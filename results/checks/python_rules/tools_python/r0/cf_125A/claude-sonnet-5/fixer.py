from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _is_const(node, value=None):
    if not isinstance(node, ast.Constant):
        return False
    if value is None:
        return True
    return node.value == value


def _get_block(node, ctx):
    cur = node
    while True:
        parent = ctx.parent(cur)
        if parent is None:
            return None, None
        for field in ('body', 'orelse', 'finalbody'):
            lst = getattr(parent, field, None)
            if isinstance(lst, list) and cur in lst:
                return parent, lst
        cur = parent


def _is_one(e):
    return isinstance(e, ast.Constant) and e.value == 1


def _increment_target(stmt):
    if (isinstance(stmt, ast.AugAssign) and isinstance(stmt.op, ast.Add)
            and isinstance(stmt.target, ast.Name) and _is_one(stmt.value)):
        return stmt.target.id
    if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)):
        name = stmt.targets[0].id
        val = stmt.value
        if isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add):
            if isinstance(val.left, ast.Name) and val.left.id == name and _is_one(val.right):
                return name
            if isinstance(val.right, ast.Name) and val.right.id == name and _is_one(val.left):
                return name
    return None


def _branch_diff_target(node):
    if not node.orelse or len(node.body) != 1 or len(node.orelse) != 1:
        return None
    b, e = node.body[0], node.orelse[0]
    if not (isinstance(b, ast.Assign) and isinstance(e, ast.Assign)):
        return None
    if len(b.targets) != 1 or len(e.targets) != 1:
        return None
    if not (isinstance(b.targets[0], ast.Name) and isinstance(e.targets[0], ast.Name)):
        return None
    if b.targets[0].id != e.targets[0].id:
        return None
    name = b.targets[0].id

    def diff_by_one(v1, v2):
        if isinstance(v2, ast.BinOp) and isinstance(v2.op, ast.Add):
            try:
                if ast.dump(v2.left) == ast.dump(v1) and _is_one(v2.right):
                    return True
                if ast.dump(v2.right) == ast.dump(v1) and _is_one(v2.left):
                    return True
            except Exception:
                return False
        return False

    if diff_by_one(b.value, e.value) or diff_by_one(e.value, b.value):
        return name
    return None


def _get_cond_target(node):
    if not isinstance(node, ast.If):
        return None
    if len(node.body) == 1:
        t = _increment_target(node.body[0])
        if t:
            return t
    return _branch_diff_target(node)


def _test_ok(node):
    test = node.test
    if isinstance(test, ast.Compare) and len(test.ops) == 1:
        comp = test.comparators[0]
        if (isinstance(comp, ast.Constant) and comp.value in (1, 2)
                and isinstance(test.ops[0], (ast.Eq, ast.GtE, ast.Gt, ast.NotEq))):
            return True
    return False


def _find_feet_var(stmts):
    feet = None
    for s in stmts:
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
            val = s.value
            if (isinstance(val, ast.BinOp) and isinstance(val.op, ast.FloorDiv)
                    and isinstance(val.right, ast.Constant) and val.right.value in (12, 36)):
                feet = s.targets[0].id
    return feet


# ---------------------------------------------------------------------------
# Rule 1a: print(feet, ..., inches) missing carry from rounding
# ---------------------------------------------------------------------------

def _is_print_pair(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'print'):
        return False
    if len(node.args) < 2:
        return False
    first, last = node.args[0], node.args[-1]
    if isinstance(first, ast.Constant) and isinstance(first.value, str):
        return False
    if isinstance(last, ast.Constant) and isinstance(last.value, str):
        return False
    if isinstance(first, ast.Starred) or isinstance(last, ast.Starred):
        return False
    return True


def _fix_print_pair(node, ctx):
    first = ctx.text(node.args[0])
    last = ctx.text(node.args[-1])
    mid = [ctx.text(a) for a in node.args[1:-1]]
    new_first = f"({first}) + ({last}) // 12"
    new_last = f"({last}) % 12"
    new_args = [new_first] + mid + [new_last]
    kwtext = ""
    if node.keywords:
        parts = []
        for kw in node.keywords:
            if kw.arg is None:
                parts.append("**" + ctx.text(kw.value))
            else:
                parts.append(f"{kw.arg}={ctx.text(kw.value)}")
        kwtext = ", " + ", ".join(parts)
    return [f"print({', '.join(new_args)}{kwtext})"]


# ---------------------------------------------------------------------------
# Rule 1b: "{} {}".format(feet, inches) missing carry from rounding
# ---------------------------------------------------------------------------

def _is_format_pair(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'format' and len(node.args) == 2
            and not any(isinstance(a, ast.Starred) for a in node.args))


def _fix_format_pair(node, ctx):
    base = ctx.text(node.func.value)
    first = ctx.text(node.args[0])
    last = ctx.text(node.args[1])
    return [f'{base}.format(({first}) + ({last}) // 12, ({last}) % 12)']


# ---------------------------------------------------------------------------
# Rule 2: n//3 + n%3  used as "round up" instead of n//3 + 1
# ---------------------------------------------------------------------------

def _is_floordiv3(e):
    return (isinstance(e, ast.BinOp) and isinstance(e.op, ast.FloorDiv)
            and isinstance(e.right, ast.Constant) and e.right.value == 3)


def _is_mod3(e):
    return (isinstance(e, ast.BinOp) and isinstance(e.op, ast.Mod)
            and isinstance(e.right, ast.Constant) and e.right.value == 3)


def _is_wrong_increment(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    left, right = node.left, node.right
    if _is_floordiv3(left) and _is_mod3(right):
        try:
            return ast.dump(left.left) == ast.dump(right.left)
        except Exception:
            return False
    return False


def _fix_wrong_increment(node, ctx):
    return [ctx.text(node.left) + " + 1"]


# ---------------------------------------------------------------------------
# Rule 3: (x + 2) // 3  should be (x + 1) // 3
# ---------------------------------------------------------------------------

def _is_round_const2(node, ctx):
    if not _is_const(node, 2):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.BinOp) and isinstance(parent.op, ast.Add)):
        return False
    if parent.right is not node:
        return False
    gp = ctx.parent(parent)
    if not (isinstance(gp, ast.BinOp) and isinstance(gp.op, ast.FloorDiv)):
        return False
    if gp.left is not parent:
        return False
    if not (isinstance(gp.right, ast.Constant) and gp.right.value == 3):
        return False
    return True


def _fix_round_const2(node, ctx):
    return ["1"]


# ---------------------------------------------------------------------------
# Rule 4: rounding adjustment applied before splitting into feet/inches,
# so the carry when inches reaches 12 is lost -> insert a carry check.
# ---------------------------------------------------------------------------

def _is_rounding_if(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if not _test_ok(node):
        return False
    target = _get_cond_target(node)
    if target is None:
        return False
    block, lst = _get_block(node, ctx)
    if block is None:
        return False
    if node not in lst:
        return False
    idx = lst.index(node)
    feet_var = _find_feet_var(lst[:idx])
    return feet_var is not None


def _fix_rounding_if(node, ctx):
    target = _get_cond_target(node)
    block, lst = _get_block(node, ctx)
    if block is None or node not in lst:
        return []
    idx = lst.index(node)
    feet_var = _find_feet_var(lst[:idx])
    if feet_var is None or target is None:
        return []
    orig = ctx.text(node)
    carry = f"if {target} == 12:\n    {feet_var} += 1\n    {target} = 0"
    return [orig + "\n" + carry]


# ---------------------------------------------------------------------------
# Rule 5: comparing the function's own name instead of its parameter
# ---------------------------------------------------------------------------

def _enclosing_function(node, ctx):
    cur = node
    while True:
        parent = ctx.parent(cur)
        if parent is None:
            return None
        if isinstance(parent, ast.FunctionDef):
            return parent
        cur = parent


def _is_self_ref_compare(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.left, ast.Name)):
        return False
    if not (isinstance(node.ops[0], ast.Eq) and len(node.comparators) == 1
            and isinstance(node.comparators[0], ast.Constant)
            and node.comparators[0].value == 1):
        return False
    fn = _enclosing_function(node, ctx)
    if fn is None:
        return False
    if node.left.id != fn.name:
        return False
    if len(fn.args.args) != 1:
        return False
    return True


def _fix_self_ref_compare(node, ctx):
    fn = _enclosing_function(node, ctx)
    param = fn.args.args[0].arg
    return [f"{param} <= 1"]


# ---------------------------------------------------------------------------
# Rule 6: true-division leaves a float; str() of a later //,% is not cast
# back to int, so the output prints "x.0" instead of "x".
# ---------------------------------------------------------------------------

def _contains_true_div_assign(ctx, name):
    for n in ast.walk(ctx.tree):
        if (isinstance(n, ast.AugAssign) and isinstance(n.op, ast.Div)
                and isinstance(n.target, ast.Name) and n.target.id == name):
            return True
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if (isinstance(t, ast.Name) and t.id == name
                        and isinstance(n.value, ast.BinOp) and isinstance(n.value.op, ast.Div)):
                    return True
    return False


def _is_float_str_arg(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'str' and len(node.args) == 1):
        return False
    arg = node.args[0]
    if not (isinstance(arg, ast.BinOp) and isinstance(arg.op, (ast.FloorDiv, ast.Mod))):
        return False
    base = arg.left
    if not isinstance(base, ast.Name):
        return False
    return _contains_true_div_assign(ctx, base.id)


def _fix_float_str_arg(node, ctx):
    arg = node.args[0]
    return [f"str(int({ctx.text(arg)}))"]


# ---------------------------------------------------------------------------
# Rule 7: math.ceil used for "round to nearest" instead of round()
# ---------------------------------------------------------------------------

def _is_ceil_call(node, ctx):
    if not isinstance(node, ast.Call) or len(node.args) != 1:
        return False
    f = node.func
    if isinstance(f, ast.Attribute) and f.attr == 'ceil':
        return True
    if isinstance(f, ast.Name) and f.id == 'ceil':
        return True
    return False


def _fix_ceil_call(node, ctx):
    return [f"round({ctx.text(node.args[0])})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="print_pair_missing_carry", match=_is_print_pair,
                    replace=_fix_print_pair, symptoms=("wrong",)),
            Rewrite(name="format_pair_missing_carry", match=_is_format_pair,
                    replace=_fix_format_pair, symptoms=("wrong",)),
            Rewrite(name="round_up_adds_remainder_instead_of_one",
                    match=_is_wrong_increment, replace=_fix_wrong_increment,
                    symptoms=("wrong",)),
            Rewrite(name="round_constant_two_should_be_one",
                    match=_is_round_const2, replace=_fix_round_const2,
                    symptoms=("wrong",)),
            Rewrite(name="rounding_if_missing_carry_insert",
                    match=_is_rounding_if, replace=_fix_rounding_if,
                    symptoms=("wrong",)),
            Rewrite(name="self_referential_compare_in_helper",
                    match=_is_self_ref_compare, replace=_fix_self_ref_compare,
                    symptoms=("wrong",)),
            Rewrite(name="float_division_leaks_into_str",
                    match=_is_float_str_arg, replace=_fix_float_str_arg,
                    symptoms=("wrong",)),
            Rewrite(name="ceil_used_instead_of_round",
                    match=_is_ceil_call, replace=_fix_ceil_call,
                    symptoms=("wrong",)),
        ]