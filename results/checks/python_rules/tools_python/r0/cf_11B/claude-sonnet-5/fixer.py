from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------
# Helper predicates
# ---------------------------------------------------------------------

def _is_true_const(node):
    if isinstance(node, ast.Constant):
        return node.value is True
    nc = getattr(ast, "NameConstant", None)
    if nc is not None and isinstance(node, nc):
        return node.value is True
    return False


def _is_call_named(node, name):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == name)


# ---------------------------------------------------------------------
# Rule 1: `int(input())` not wrapped in abs()
# ---------------------------------------------------------------------

def _is_bare_int_input(node, ctx):
    if not _is_call_named(node, "int"):
        return False
    if len(node.args) != 1:
        return False
    if not _is_call_named(node.args[0], "input"):
        return False
    parent = ctx.parent(node)
    if _is_call_named(parent, "abs"):
        return False
    return True


def _wrap_abs(node, ctx):
    return ["abs(" + ctx.text(node) + ")"]


# ---------------------------------------------------------------------
# Rule 2: `x = map(int, input())` style misread of a single integer
# ---------------------------------------------------------------------

def _is_map_int_input(node, ctx):
    if not _is_call_named(node, "map"):
        return False
    if len(node.args) != 2:
        return False
    a0, a1 = node.args
    if not (isinstance(a0, ast.Name) and a0.id == "int"):
        return False
    if not _is_call_named(a1, "input"):
        return False
    return True


def _fix_map_int_input(node, ctx):
    return ["abs(int(input()))"]


# ---------------------------------------------------------------------
# Rule 3: `print(x)` where `x` only ever held the mis-parsed `map(...)`
# object -> replace with the full jump-counting computation.
# ---------------------------------------------------------------------

def _is_print_of_mapped_var(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    call = node.value
    if not _is_call_named(call, "print"):
        return False
    if len(call.args) != 1 or not isinstance(call.args[0], ast.Name):
        return False
    var = call.args[0].id
    for stmt in ast.walk(ctx.tree):
        if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)
                and stmt.targets[0].id == var):
            if _is_map_int_input(stmt.value, ctx):
                return True
    return False


def _fix_print_of_mapped_var(node, ctx):
    var = node.value.args[0].id
    text = (
        "jumps = 0\n"
        "pos = 0\n"
        "while pos < abs({v}) or (pos - abs({v})) % 2 != 0:\n"
        "    jumps += 1\n"
        "    pos += jumps\n"
        "print(jumps)"
    ).format(v=var)
    return [text]


# ---------------------------------------------------------------------
# Rule 4: greedy sign-choosing loop `while pos != x: ...` that tries to
# add/subtract the next jump instead of using the parity test.
# ---------------------------------------------------------------------

def _assigned_names(node):
    names = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.Assign):
            for t in sub.targets:
                if isinstance(t, ast.Name):
                    names.add(t.id)
        elif isinstance(sub, ast.AugAssign) and isinstance(sub.target, ast.Name):
            names.add(sub.target.id)
    return names


def _mismatch_while(node):
    if not isinstance(node, ast.While):
        return None
    test = node.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], ast.NotEq)):
        return None
    left, right = test.left, test.comparators[0]
    if not (isinstance(left, ast.Name) and isinstance(right, ast.Name)):
        return None
    names = _assigned_names(node)
    if left.id in names and right.id not in names:
        return left.id, right.id
    if right.id in names and left.id not in names:
        return right.id, left.id
    return None


def _find_counter_name(node, pos_name):
    for sub in ast.walk(node):
        if (isinstance(sub, ast.AugAssign) and isinstance(sub.target, ast.Name)
                and sub.target.id != pos_name and isinstance(sub.op, ast.Add)
                and isinstance(sub.value, ast.Constant) and sub.value.value == 1):
            return sub.target.id
        if (isinstance(sub, ast.Assign) and len(sub.targets) == 1
                and isinstance(sub.targets[0], ast.Name)
                and sub.targets[0].id != pos_name):
            v = sub.value
            if (isinstance(v, ast.BinOp) and isinstance(v.op, ast.Add)
                    and isinstance(v.left, ast.Name)
                    and v.left.id == sub.targets[0].id
                    and isinstance(v.right, ast.Constant) and v.right.value == 1):
                return sub.targets[0].id
    return None


def _is_sign_choice_while(node, ctx):
    info = _mismatch_while(node)
    if info is None:
        return False
    pos_name, _x_name = info
    counter = _find_counter_name(node, pos_name)
    return counter is not None


def _fix_sign_choice_while(node, ctx):
    pos_name, x_name = _mismatch_while(node)
    counter = _find_counter_name(node, pos_name)
    text = (
        "{p} = 0\n"
        "while {p} < abs({x}) or ({p}-abs({x})) % 2 != 0:\n"
        "    {c} += 1\n"
        "    {p} += {c}"
    ).format(p=pos_name, x=x_name, c=counter)
    return [text]


# ---------------------------------------------------------------------
# Rule 5: triangular-number-formula loop `while True: ... (n*n+n)/2 ...`
# that tries to shortcut the computation analytically instead of
# simulating jumps.
# ---------------------------------------------------------------------

def _find_triangular_binop(node):
    for sub in ast.walk(node):
        if isinstance(sub, ast.BinOp) and isinstance(sub.op, ast.Div):
            rt = sub.right
            if isinstance(rt, ast.Constant) and rt.value == 2:
                left = sub.left
                if isinstance(left, (ast.BinOp,)):
                    return sub
    return None


def _find_compare_other_side(while_node, tri_node):
    for sub in ast.walk(while_node):
        if isinstance(sub, ast.Compare) and len(sub.comparators) == 1:
            if sub.left is tri_node:
                return sub.comparators[0]
            if sub.comparators[0] is tri_node:
                return sub.left
    return None


def _is_triangular_while(node, ctx):
    if not isinstance(node, ast.While):
        return False
    if not _is_true_const(node.test):
        return False
    tri = _find_triangular_binop(node)
    if tri is None:
        return False
    other = _find_compare_other_side(node, tri)
    return other is not None


def _fix_triangular_while(node, ctx):
    tri = _find_triangular_binop(node)
    other = _find_compare_other_side(node, tri)
    vx = ctx.text(other)
    text = (
        "jumps = 0\n"
        "pos = 0\n"
        "while pos < abs({v}) or (pos - abs({v})) % 2 != 0:\n"
        "    jumps += 1\n"
        "    pos += jumps\n"
        "print(jumps)"
    ).format(v=vx)
    return [text]


# ---------------------------------------------------------------------

class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="wrap_int_input_in_abs",
                match=_is_bare_int_input,
                replace=_wrap_abs,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="map_int_input_should_be_single_int",
                match=_is_map_int_input,
                replace=_fix_map_int_input,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="print_mapped_var_needs_jump_loop",
                match=_is_print_of_mapped_var,
                replace=_fix_print_of_mapped_var,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="greedy_sign_choice_loop_to_parity_loop",
                match=_is_sign_choice_while,
                replace=_fix_sign_choice_while,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="triangular_formula_loop_to_parity_loop",
                match=_is_triangular_while,
                replace=_fix_triangular_while,
                symptoms=("wrong", "timeout"),
            ),
        ]