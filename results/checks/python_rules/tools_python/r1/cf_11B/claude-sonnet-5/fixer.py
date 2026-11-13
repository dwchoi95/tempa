from src.core.repair import Rule
import ast

from src.core.rewrite import Rewrite


def _is_plain_int_input(node, ctx):
    """Call int(input()) not yet wrapped in abs()."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "int"):
        return False
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    if not (isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name)
            and arg.func.id == "input"):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name) and parent.func.id == "abs":
        return False
    return True


def _wrap_abs(node, ctx):
    return ["abs(" + ctx.text(node) + ")"]


def _find_zero_init(name, tree):
    for n in ast.walk(tree):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name) and n.targets[0].id == name
                and isinstance(n.value, ast.Constant) and n.value.value == 0):
            return True
    return False


def _is_overshoot_while(node, ctx):
    """while pos != x: n += 1; (add or subtract n from pos based on overshoot)."""
    if not isinstance(node, ast.While):
        return False
    t = node.test
    if not (isinstance(t, ast.Compare) and len(t.ops) == 1 and isinstance(t.ops[0], ast.NotEq)):
        return False
    if not (isinstance(t.left, ast.Name) and isinstance(t.comparators[0], ast.Name)):
        return False
    if not node.body:
        return False
    first = node.body[0]
    if not (isinstance(first, ast.AugAssign) and isinstance(first.op, ast.Add)
            and isinstance(first.target, ast.Name)
            and isinstance(first.value, ast.Constant) and first.value.value == 1):
        return False
    return True


def _overshoot_replace(node, ctx):
    t = node.test
    left_name = t.left.id
    right_name = t.comparators[0].id
    tree = ctx.tree
    left_zero = _find_zero_init(left_name, tree)
    right_zero = _find_zero_init(right_name, tree)
    if left_zero and not right_zero:
        pos, targ = left_name, right_name
    elif right_zero and not left_zero:
        pos, targ = right_name, left_name
    else:
        pos, targ = left_name, right_name
    counter = node.body[0].target.id
    text = (f"while {pos} < {targ} or ({pos}-{targ}) % 2 != 0:\n"
            f"    {counter} += 1\n"
            f"    {pos} += {counter}")
    return [text]


def _is_map_input_assign(node, ctx):
    """x = map(int, input()) (or similar) used as the whole input-reading step."""
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)):
        return False
    v = node.value
    return isinstance(v, ast.Call) and isinstance(v.func, ast.Name) and v.func.id == "map"


def _map_input_replace(node, ctx):
    text = ("x = abs(int(input()))\n"
            "jumps = 0\n"
            "pos = 0\n"
            "while pos < x or (pos-x) % 2 != 0:\n"
            "    jumps += 1\n"
            "    pos += jumps")
    return [text]


def _is_map_bound_print(node, ctx):
    """print(x) where x was bound via the map(...) input misparse."""
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "print" and len(node.args) == 1
            and isinstance(node.args[0], ast.Name)):
        return False
    name = node.args[0].id
    for n in ast.walk(ctx.tree):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name) and n.targets[0].id == name
                and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name)
                and n.value.func.id == "map"):
            return True
    return False


def _map_print_replace(node, ctx):
    return ["print(jumps)"]


def _is_triangular_term(node):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)):
        return False
    left, right = node.left, node.right
    if not (isinstance(right, ast.Constant) and right.value in (2, 2.0)):
        return False
    if not (isinstance(left, ast.BinOp) and isinstance(left.op, ast.Add)):
        return False

    def is_square(e, name):
        return (isinstance(e, ast.BinOp) and isinstance(e.op, ast.Mult)
                and isinstance(e.left, ast.Name) and isinstance(e.right, ast.Name)
                and e.left.id == e.right.id == name)

    a, b = left.left, left.right
    if isinstance(b, ast.Name) and is_square(a, b.id):
        return True
    if isinstance(a, ast.Name) and is_square(b, a.id):
        return True
    return False


def _find_zero_compare_name(node):
    for n in ast.walk(node):
        if isinstance(n, ast.Compare) and len(n.ops) == 1 and isinstance(n.ops[0], ast.Eq):
            left, right = n.left, n.comparators[0]
            if isinstance(left, ast.Name) and isinstance(right, ast.Constant) and right.value == 0:
                return left.id
            if isinstance(right, ast.Name) and isinstance(left, ast.Constant) and left.value == 0:
                return right.id
    return None


def _is_triangular_while(node, ctx):
    """while True: search minimal n with triangular number n*(n+1)/2 >= target."""
    if not isinstance(node, ast.While):
        return False
    if not (isinstance(node.test, ast.Constant) and node.test.value is True):
        return False
    if not any(_is_triangular_term(n) for n in ast.walk(node)):
        return False
    return _find_zero_compare_name(node) is not None


def _triangular_replace(node, ctx):
    target = _find_zero_compare_name(node)
    text = (f"x = abs({target})\n"
            "jumps = 0\n"
            "pos = 0\n"
            "while pos < x or (pos-x) % 2 != 0:\n"
            "    jumps += 1\n"
            "    pos += jumps\n"
            "print(jumps)")
    return [text]


def _is_strict_lt(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Lt))


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="wrap_input_with_abs", match=_is_plain_int_input,
                    replace=_wrap_abs, symptoms=("wrong",)),

            Rewrite(name="overshoot_correction_loop_to_parity_loop",
                    match=_is_overshoot_while, replace=_overshoot_replace,
                    symptoms=("wrong", "timeout")),

            Rewrite(name="map_input_misparse_to_parity_loop",
                    match=_is_map_input_assign, replace=_map_input_replace,
                    symptoms=("wrong", "err:TypeError")),

            Rewrite(name="map_bound_print_to_jumps",
                    match=_is_map_bound_print, replace=_map_print_replace,
                    symptoms=("wrong", "err:TypeError")),

            Rewrite(name="triangular_search_to_parity_loop",
                    match=_is_triangular_while, replace=_triangular_replace,
                    symptoms=("wrong", "timeout")),

            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt,
                    replace=_to_lte, symptoms=("wrong",)),
        ]