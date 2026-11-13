from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _augassign_inc_by_one(stmt):
    return (isinstance(stmt, ast.AugAssign) and isinstance(stmt.op, ast.Add)
            and isinstance(stmt.target, ast.Name)
            and isinstance(stmt.value, ast.Constant) and stmt.value.value == 1)


def _get_counter_and_pos(node):
    counter = None
    for stmt in node.body:
        if _augassign_inc_by_one(stmt):
            counter = stmt.target.id
    pos_name = None
    for stmt in node.body:
        if isinstance(stmt, ast.If):
            body_targets = [s.target.id for s in stmt.body
                             if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name)]
            else_targets = [s.target.id for s in stmt.orelse
                             if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name)]
            common = set(body_targets) & set(else_targets)
            if common:
                pos_name = common.pop()
    return counter, pos_name


def _is_sign_based_while(node, ctx):
    if not isinstance(node, ast.While):
        return False
    test = node.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], ast.NotEq)):
        return False
    left, right = test.left, test.comparators[0]
    if not (isinstance(left, ast.Name) and isinstance(right, ast.Name)):
        return False
    counter, pos_name = _get_counter_and_pos(node)
    if counter is None or pos_name is None:
        return False
    return pos_name in (left.id, right.id)


def _fix_sign_based_while(node, ctx):
    left, right = node.test.left, node.test.comparators[0]
    counter, pos_name = _get_counter_and_pos(node)
    x_name = right.id if left.id == pos_name else left.id
    text = (
        f"while {pos_name} < abs({x_name}) or ({pos_name}-abs({x_name})) % 2 != 0:\n"
        f"    {counter} += 1\n"
        f"    {pos_name} += {counter}"
    )
    return [text]


def _is_map_single_int(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)):
        return False
    v = node.value
    if not (isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id == 'map'):
        return False
    if len(v.args) != 2:
        return False
    a0, a1 = v.args
    if not (isinstance(a0, ast.Name) and a0.id == 'int'):
        return False
    if not (isinstance(a1, ast.Call) and isinstance(a1.func, ast.Name) and a1.func.id == 'input'):
        return False
    return True


def _fix_map_single_int(node, ctx):
    target = ctx.text(node.targets[0])
    text = (
        f"{target} = abs(int(input()))\n"
        "jumps = 0\n"
        "pos = 0\n"
        f"while pos < {target} or (pos-{target}) % 2 != 0:\n"
        "    jumps += 1\n"
        "    pos += jumps"
    )
    return [text]


def _find_parity_while_counter(tree):
    for sub in ast.walk(tree):
        if isinstance(sub, ast.While):
            test_src = ""
            try:
                test_src = ast.dump(sub.test)
            except Exception:
                test_src = ""
            if '2' in test_src and ('NotEq' in test_src or 'Mod' in test_src):
                for stmt in sub.body:
                    if _augassign_inc_by_one(stmt):
                        return stmt.target.id
    return None


def _is_wrong_print_var(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'print' and len(node.args) == 1
            and isinstance(node.args[0], ast.Name)):
        return False
    printed = node.args[0].id
    counter = _find_parity_while_counter(ctx.tree)
    if counter is None:
        return False
    return counter != printed


def _fix_wrong_print_var(node, ctx):
    counter = _find_parity_while_counter(ctx.tree)
    if counter is None:
        return []
    return [f"print({counter})"]


def _find_input_var(tree):
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            v = node.value
            if isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id == 'int' and len(v.args) == 1:
                arg = v.args[0]
                if isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name) and arg.func.id == 'input':
                    return node.targets[0].id
    return None


def _find_triangular_counter(node):
    for sub in ast.walk(node):
        if _augassign_inc_by_one(sub):
            return sub.target.id
    return None


def _is_triangular_while(node, ctx):
    if not isinstance(node, ast.While):
        return False
    test = node.test
    if not (isinstance(test, ast.Constant) and test.value is True):
        return False
    var = _find_triangular_counter(node)
    if var is None:
        return False
    src = ctx.text(node).replace(" ", "")
    pattern1 = f"{var}*{var}"
    pattern2 = f"{var}*({var}"
    return pattern1 in src or pattern2 in src


def _fix_triangular_while(node, ctx):
    xvar = _find_input_var(ctx.tree)
    if xvar is None:
        return []
    text = (
        "jumps = 0\n"
        "pos = 0\n"
        f"while pos < abs({xvar}) or (pos-abs({xvar})) % 2 != 0:\n"
        "    jumps += 1\n"
        "    pos += jumps\n"
        "print(jumps)"
    )
    return [text]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="sign_based_walk_should_be_parity_check",
                match=_is_sign_based_while,
                replace=_fix_sign_based_while,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="map_single_int_misuse",
                match=_is_map_single_int,
                replace=_fix_map_single_int,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="print_wrong_variable_instead_of_counter",
                match=_is_wrong_print_var,
                replace=_fix_wrong_print_var,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="triangular_number_formula_instead_of_simulation",
                match=_is_triangular_while,
                replace=_fix_triangular_while,
                symptoms=("wrong",),
            ),
        ]