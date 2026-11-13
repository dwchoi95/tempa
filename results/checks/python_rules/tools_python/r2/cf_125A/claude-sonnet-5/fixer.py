from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------------
# Rule 1: off-by-one rounding constant  (X + 2) // 3  ->  (X + 1) // 3
# ---------------------------------------------------------------------------

def _is_plus2_floordiv3(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    if not (isinstance(node.right, ast.Constant) and node.right.value == 2):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.BinOp) and isinstance(parent.op, ast.FloorDiv)):
        return False
    if not (isinstance(parent.right, ast.Constant) and parent.right.value == 3):
        return False
    return ctx.field(node) == "left"


def _fix_plus2_floordiv3(node, ctx):
    return [ctx.text(node.left) + " + 1"]


# ---------------------------------------------------------------------------
# Rule 2: forgotten carry when rounded inches reach 12 (should roll into feet)
# Rewritten generically at the final print(...) statement, whatever shape it
# takes (two plain args, .format(), f-string, or str(...)+..+str(...)).
# ---------------------------------------------------------------------------

def _get_print_call(node):
    if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call):
        call = node.value
        if isinstance(call.func, ast.Name) and call.func.id == "print":
            return call
    return None


def _collect_str_calls(n, out):
    if isinstance(n, ast.BinOp):
        _collect_str_calls(n.left, out)
        _collect_str_calls(n.right, out)
    elif isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "str" and len(n.args) == 1:
        out.append(n.args[0])


def _extract_feet_inch_exprs(call):
    non_str_args = [a for a in call.args
                     if not (isinstance(a, ast.Constant) and isinstance(a.value, str))]
    if len(non_str_args) == 2:
        return non_str_args[0], non_str_args[1]

    if len(call.args) == 1:
        arg = call.args[0]

        if isinstance(arg, ast.Call) and isinstance(arg.func, ast.Attribute) and arg.func.attr == "format":
            fargs = arg.args
            if len(fargs) == 2:
                return fargs[0], fargs[1]

        if isinstance(arg, ast.JoinedStr):
            vals = [v.value for v in arg.values if isinstance(v, ast.FormattedValue)]
            if len(vals) == 2:
                return vals[0], vals[1]

        if isinstance(arg, ast.BinOp):
            calls = []
            _collect_str_calls(arg, calls)
            if len(calls) == 2:
                return calls[0], calls[1]

    return None


def _is_fixable_print(node, ctx):
    call = _get_print_call(node)
    if call is None:
        return False
    return _extract_feet_inch_exprs(call) is not None


def _fix_carry_before_print(node, ctx):
    call = node.value
    pair = _extract_feet_inch_exprs(call)
    if pair is None:
        return []
    feet_e, inch_e = pair
    feet_txt = ctx.text(feet_e)
    inch_txt = ctx.text(inch_e)
    snippet = (
        "_feet = " + feet_txt + "\n"
        "_inch = " + inch_txt + "\n"
        "if _inch == 12:\n"
        "    _feet += 1\n"
        "    _inch = 0\n"
        "print(_feet, _inch)"
    )
    return [snippet]


# ---------------------------------------------------------------------------
# Rule 3: typo'd modulus constant (e.g. % 26 instead of % 36) used alongside
# a genuine // 36 elsewhere in the same program.
# ---------------------------------------------------------------------------

def _is_cm_mod26(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mod)):
        return False
    if not (isinstance(node.right, ast.Constant) and node.right.value == 26):
        return False
    for n in ast.walk(ctx.tree):
        if (isinstance(n, ast.BinOp) and isinstance(n.op, ast.FloorDiv)
                and isinstance(n.right, ast.Constant) and n.right.value == 36):
            return True
    return False


def _fix_cm_mod26(node, ctx):
    return [ctx.text(node.left) + " % 36"]


# ---------------------------------------------------------------------------
# Rule 4: inside a branch that tests `X % 3 == 2`, adding the remainder
# itself (which is always 2) instead of the constant 1.
# ---------------------------------------------------------------------------

def _find_enclosing_if(node, ctx):
    cur = ctx.parent(node)
    while cur is not None and not isinstance(cur, ast.If):
        cur = ctx.parent(cur)
    return cur


def _is_add_remainder_instead_of_one(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    right = node.right
    if not (isinstance(right, ast.BinOp) and isinstance(right.op, ast.Mod)):
        return False
    if not (isinstance(right.right, ast.Constant) and right.right.value == 3):
        return False
    enclosing_if = _find_enclosing_if(node, ctx)
    if enclosing_if is None:
        return False
    test = enclosing_if.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], ast.Eq)):
        return False
    if not (isinstance(test.left, ast.BinOp) and isinstance(test.left.op, ast.Mod)
            and isinstance(test.left.right, ast.Constant) and test.left.right.value == 3):
        return False
    cmp_val = test.comparators[0]
    return isinstance(cmp_val, ast.Constant) and cmp_val.value == 2


def _fix_add_remainder_instead_of_one(node, ctx):
    return [ctx.text(node.left) + " + 1"]


# ---------------------------------------------------------------------------
# Rule 5: result of floor-division/modulo stays a float (because the input
# was divided in place with `/=` earlier) and gets stringified without an
# int() cast, producing "1.0" instead of "1".
# ---------------------------------------------------------------------------

def _is_str_of_float_div(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "str"):
        return False
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    if not (isinstance(arg, ast.BinOp) and isinstance(arg.op, (ast.FloorDiv, ast.Mod))):
        return False
    names = {n.id for n in ast.walk(arg) if isinstance(n, ast.Name)}
    if not names:
        return False
    for n in ast.walk(ctx.tree):
        if (isinstance(n, ast.AugAssign) and isinstance(n.op, ast.Div)
                and isinstance(n.target, ast.Name) and n.target.id in names):
            return True
        if isinstance(n, ast.Assign) and isinstance(n.value, ast.BinOp) and isinstance(n.value.op, ast.Div):
            for t in n.targets:
                if isinstance(t, ast.Name) and t.id in names:
                    return True
    return False


def _fix_str_of_float_div(node, ctx):
    return ["str(int(" + ctx.text(node.args[0]) + "))"]


# ---------------------------------------------------------------------------
# Rule 6: a helper function compares its own name to a literal instead of
# comparing its parameter (copy/paste slip: `if funcname == 1` inside
# `def funcname(param):`).
# ---------------------------------------------------------------------------

def _find_enclosing_function(node, ctx):
    cur = ctx.parent(node)
    while cur is not None and not isinstance(cur, ast.FunctionDef):
        cur = ctx.parent(cur)
    return cur


def _is_funcname_self_compare(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    if not isinstance(node.left, ast.Name):
        return False
    func = _find_enclosing_function(node, ctx)
    if func is None or node.left.id != func.name:
        return False
    return len(func.args.args) == 1


def _fix_funcname_self_compare(node, ctx):
    func = _find_enclosing_function(node, ctx)
    param_name = func.args.args[0].arg
    return [param_name + " <= 1"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="round_up_offset_plus2_should_be_plus1",
                match=_is_plus2_floordiv3,
                replace=_fix_plus2_floordiv3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_carry_into_feet_at_12_inches",
                match=_is_fixable_print,
                replace=_fix_carry_before_print,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="typo_modulus_26_should_be_36",
                match=_is_cm_mod26,
                replace=_fix_cm_mod26,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="adds_remainder_instead_of_one_in_round_up_branch",
                match=_is_add_remainder_instead_of_one,
                replace=_fix_add_remainder_instead_of_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_int_cast_on_float_division_result",
                match=_is_str_of_float_div,
                replace=_fix_str_of_float_div,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="helper_compares_its_own_name_instead_of_parameter",
                match=_is_funcname_self_compare,
                replace=_fix_funcname_self_compare,
                symptoms=("wrong",),
            ),
        ]