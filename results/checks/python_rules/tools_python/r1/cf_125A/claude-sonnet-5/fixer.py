from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _const_val(n):
    return n.value if isinstance(n, ast.Constant) else None


def _collect_name_groups(tree):
    groups = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            names = [a.id for a in node.args if isinstance(a, ast.Name)]
            if len(names) >= 2:
                groups.append(names)
        if isinstance(node, ast.JoinedStr):
            names = []
            for v in node.values:
                if isinstance(v, ast.FormattedValue) and isinstance(v.value, ast.Name):
                    names.append(v.value.id)
            if len(names) >= 2:
                groups.append(names)
    return groups


def _find_feet_var(tree, inchvar):
    try:
        for names in _collect_name_groups(tree):
            if inchvar in names:
                for nm in names:
                    if nm != inchvar:
                        return nm
    except Exception:
        return None
    return None


def _mentions_36(expr):
    for n in ast.walk(expr):
        if isinstance(n, ast.Constant) and n.value == 36:
            return True
    return False


# ---------------------------------------------------------------------------
# Rule 1: carry-over-12 bug hidden inside an If that bumps an "inches" value
# by one when a remainder rounds up (the classic "feet computed first, inch
# rounding can overflow past 11" misconception).
# ---------------------------------------------------------------------------

def _find_inc_var(node):
    if not isinstance(node, ast.If):
        return None
    body = node.body
    orelse = node.orelse
    empty_else = (len(orelse) == 0) or (len(orelse) == 1 and isinstance(orelse[0], ast.Pass))
    if empty_else:
        if len(body) != 1:
            return None
        s = body[0]
        if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name) and isinstance(s.op, ast.Add) \
                and isinstance(s.value, ast.Constant) and s.value.value == 1:
            return s.target.id
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name):
            tgt = s.targets[0]
            v = s.value
            if isinstance(v, ast.BinOp) and isinstance(v.op, ast.Add) and isinstance(v.left, ast.Name) \
                    and v.left.id == tgt.id and isinstance(v.right, ast.Constant) and v.right.value == 1:
                return tgt.id
        return None
    if len(body) == 1 and len(orelse) == 1:
        b, o = body[0], orelse[0]
        if isinstance(b, ast.Assign) and isinstance(o, ast.Assign) and len(b.targets) == 1 and len(o.targets) == 1 \
                and isinstance(b.targets[0], ast.Name) and isinstance(o.targets[0], ast.Name) \
                and b.targets[0].id == o.targets[0].id:
            var = b.targets[0].id

            def is_plus1(big, small):
                return isinstance(big, ast.BinOp) and isinstance(big.op, ast.Add) \
                    and isinstance(big.right, ast.Constant) and big.right.value == 1 \
                    and ast.dump(big.left) == ast.dump(small)

            if is_plus1(o.value, b.value) or is_plus1(b.value, o.value):
                return var
    return None


def _is_carry_if(node, ctx):
    try:
        var = _find_inc_var(node)
        if var is None:
            return False
        return _find_feet_var(ctx.tree, var) is not None
    except Exception:
        return False


def _fix_carry_if(node, ctx):
    try:
        var = _find_inc_var(node)
        feetvar = _find_feet_var(ctx.tree, var)
        if var is None or feetvar is None:
            return []
        orig = ctx.text(node)
        norm = "if {v} == 12:\n    {f} += 1\n    {v} = 0".format(v=var, f=feetvar)
        return [orig + "\n" + norm]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 2: same carry-overflow bug, but the rounded inch value is produced by
# a plain assignment (round(...), int(... + 0.5), or (x + 1) // 3) rather
# than guarded by an If.
# ---------------------------------------------------------------------------

def _is_round_shaped(val):
    if isinstance(val, ast.Call) and isinstance(val.func, ast.Name) and val.func.id == 'round':
        return True
    if isinstance(val, ast.Call) and isinstance(val.func, ast.Name) and val.func.id == 'int' \
            and len(val.args) == 1:
        a = val.args[0]
        if isinstance(a, ast.BinOp) and isinstance(a.op, ast.Add) and isinstance(a.right, ast.Constant) \
                and a.right.value == 0.5:
            return True
    if isinstance(val, ast.BinOp) and isinstance(val.op, ast.FloorDiv) and isinstance(val.right, ast.Constant) \
            and val.right.value == 3 and isinstance(val.left, ast.BinOp) and isinstance(val.left.op, ast.Add) \
            and isinstance(val.left.right, ast.Constant) and val.left.right.value == 1:
        return True
    return False


def _is_rounding_assign(node, ctx):
    try:
        if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
            return False
        val = node.value
        if _mentions_36(val):
            return False
        if not _is_round_shaped(val):
            return False
        var = node.targets[0].id
        return _find_feet_var(ctx.tree, var) is not None
    except Exception:
        return False


def _fix_rounding_assign(node, ctx):
    try:
        var = node.targets[0].id
        feetvar = _find_feet_var(ctx.tree, var)
        if feetvar is None:
            return []
        orig = ctx.text(node)
        norm = "if {v} == 12:\n    {f} += 1\n    {v} = 0".format(v=var, f=feetvar)
        return [orig + "\n" + norm]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 3: feet computed with a spurious "round to nearest" (+0.5) when it
# should be a plain floor division by 36.
# ---------------------------------------------------------------------------

def _is_feet_rounded_div36(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'int'
            and len(node.args) == 1 and isinstance(node.args[0], ast.BinOp) and isinstance(node.args[0].op, ast.Add)
            and isinstance(node.args[0].right, ast.Constant) and node.args[0].right.value == 0.5
            and isinstance(node.args[0].left, ast.BinOp) and isinstance(node.args[0].left.op, ast.Div)
            and isinstance(node.args[0].left.right, ast.Constant) and node.args[0].left.right.value == 36)


def _fix_feet_rounded_div36(node, ctx):
    try:
        inner = ctx.text(node.args[0].left)
        return ["int(" + inner + ")"]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 4: rounding adjustment adds the remainder itself instead of 1.
# ---------------------------------------------------------------------------

def _is_add_full_remainder(node, ctx):
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)
            and isinstance(node.left, ast.BinOp) and isinstance(node.left.op, ast.FloorDiv)
            and isinstance(node.right, ast.BinOp) and isinstance(node.right.op, ast.Mod)
            and isinstance(node.left.right, ast.Constant) and node.left.right.value == 3
            and isinstance(node.right.right, ast.Constant) and node.right.right.value == 3
            and ast.dump(node.left.left) == ast.dump(node.right.left))


def _fix_add_full_remainder(node, ctx):
    try:
        return [ctx.text(node.left) + " + 1"]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 5: (x + 2) // 3  should be (x + 1) // 3  (rounding threshold off by one)
# ---------------------------------------------------------------------------

def _is_plus2_div3(node, ctx):
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.FloorDiv)
            and isinstance(node.right, ast.Constant) and node.right.value == 3
            and isinstance(node.left, ast.BinOp) and isinstance(node.left.op, ast.Add)
            and isinstance(node.left.right, ast.Constant) and node.left.right.value == 2)


def _fix_plus2_div3(node, ctx):
    try:
        base = ctx.text(node.left.left)
        return ["(" + base + " + 1) // 3"]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 6: typo'd modulus constant that should be 36 (feet-block size), found
# right after a "// 36" feet computation on the same base variable.
# ---------------------------------------------------------------------------

def _is_wrong_mod_36(node, ctx):
    try:
        var = None
        c = None
        if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Mod) and isinstance(node.target, ast.Name):
            var = node.target.id
            c = node.value
        elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name) \
                and isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Mod) \
                and isinstance(node.value.left, ast.Name) and node.value.left.id == node.targets[0].id:
            var = node.targets[0].id
            c = node.value.right
        else:
            return False
        if not (isinstance(c, ast.Constant) and isinstance(c.value, int) and c.value != 36):
            return False
        parent = ctx.parent(node)
        body = getattr(parent, 'body', None)
        if not body:
            return False
        found = False
        for s in body:
            if s is node:
                break
            if isinstance(s, ast.Assign) and len(s.targets) == 1:
                v = s.value
                if isinstance(v, ast.BinOp) and isinstance(v.op, ast.FloorDiv) and isinstance(v.left, ast.Name) \
                        and v.left.id == var and isinstance(v.right, ast.Constant) and v.right.value == 36:
                    found = True
        return found
    except Exception:
        return False


def _fix_wrong_mod_36(node, ctx):
    try:
        if isinstance(node, ast.AugAssign):
            return [node.target.id + " %= 36"]
        var = node.targets[0].id
        return [var + " = " + ctx.text(node.value.left) + " % 36"]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 7: str(expr) around an int-valued expression left as a float because
# of earlier "/=" division; wrap in int() (a safe no-op when already int).
# ---------------------------------------------------------------------------

def _is_str_of_div(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'str'
            and len(node.args) == 1
            and isinstance(node.args[0], ast.BinOp) and isinstance(node.args[0].op, (ast.FloorDiv, ast.Mod))
            and not (isinstance(node.args[0].left, ast.Call) and isinstance(node.args[0].left.func, ast.Name)
                     and node.args[0].left.func.id == 'int'))


def _fix_str_of_div(node, ctx):
    try:
        inner = ctx.text(node.args[0])
        return ["str(int(" + inner + "))"]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 8: double-counting bug -- feet computed directly as base // 36 *and*
# inches computed directly as round(base / 3) (or base // 3) on the SAME
# base, instead of subtracting the feet portion first.
# ---------------------------------------------------------------------------

def _directly_divides_base(expr, base):
    e = expr
    if isinstance(e, ast.Call) and isinstance(e.func, ast.Name) and e.func.id == 'round' and len(e.args) == 1:
        e = e.args[0]
    if isinstance(e, ast.BinOp) and isinstance(e.op, (ast.Div, ast.FloorDiv)) \
            and isinstance(e.right, ast.Constant) and e.right.value == 3 \
            and isinstance(e.left, ast.Name) and e.left.id == base:
        return True
    return False


def _find_base_for_feet36(varname, ctx):
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and n.targets[0].id == varname:
            v = n.value
            if isinstance(v, ast.BinOp) and isinstance(v.op, ast.FloorDiv) and isinstance(v.right, ast.Constant) \
                    and v.right.value == 36 and isinstance(v.left, ast.Name):
                return v.left.id
    return None


def _var_is_round_total(varname, base, ctx):
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) \
                and n.targets[0].id == varname:
            if _directly_divides_base(n.value, base):
                return True
    return False


def _is_double_count_print(node, ctx):
    try:
        if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'print'):
            return False
        if len(node.args) != 2:
            return False
        feetarg, incharg = node.args
        if not (isinstance(feetarg, ast.Name) and isinstance(incharg, ast.Name)):
            return False
        base = _find_base_for_feet36(feetarg.id, ctx)
        if base is None:
            return False
        return _var_is_round_total(incharg.id, base, ctx)
    except Exception:
        return False


def _fix_double_count_print(node, ctx):
    try:
        incharg = node.args[1]
        return ["print(" + incharg.id + " // 12, " + incharg.id + " % 12)"]
    except Exception:
        return []


# ---------------------------------------------------------------------------
# Rule 9: a helper function mistakenly compares its own name (the function
# object) to a constant instead of comparing its parameter.
# ---------------------------------------------------------------------------

def _enclosing_function(node, ctx):
    p = ctx.parent(node)
    while p is not None and not isinstance(p, ast.FunctionDef):
        p = ctx.parent(p)
    return p


def _is_self_name_compare(node, ctx):
    try:
        if not (isinstance(node, ast.Compare) and isinstance(node.left, ast.Name)):
            return False
        func = _enclosing_function(node, ctx)
        if func is None or not func.args.args:
            return False
        return node.left.id == func.name
    except Exception:
        return False


def _fix_self_name_compare(node, ctx):
    try:
        func = _enclosing_function(node, ctx)
        param = func.args.args[0].arg
        return [param + " <= 1"]
    except Exception:
        return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="carry_over_12_in_if", match=_is_carry_if, replace=_fix_carry_if,
                    symptoms=("wrong",)),
            Rewrite(name="carry_over_12_in_assign", match=_is_rounding_assign, replace=_fix_rounding_assign,
                    symptoms=("wrong",)),
            Rewrite(name="feet_should_floor_not_round", match=_is_feet_rounded_div36,
                    replace=_fix_feet_rounded_div36, symptoms=("wrong",)),
            Rewrite(name="round_adjustment_adds_remainder", match=_is_add_full_remainder,
                    replace=_fix_add_full_remainder, symptoms=("wrong",)),
            Rewrite(name="round_threshold_plus2_should_be_plus1", match=_is_plus2_div3,
                    replace=_fix_plus2_div3, symptoms=("wrong",)),
            Rewrite(name="typo_modulus_should_be_36", match=_is_wrong_mod_36,
                    replace=_fix_wrong_mod_36, symptoms=("wrong",)),
            Rewrite(name="str_wrap_int_cast", match=_is_str_of_div,
                    replace=_fix_str_of_div, symptoms=("wrong",)),
            Rewrite(name="double_counted_feet_and_inches", match=_is_double_count_print,
                    replace=_fix_double_count_print, symptoms=("wrong",)),
            Rewrite(name="self_referential_compare", match=_is_self_name_compare,
                    replace=_fix_self_name_compare, symptoms=("wrong",)),
        ]