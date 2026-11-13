from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_digr_like(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Mult)
    )


def _fix_digr_call(node, ctx):
    return [f"digr({ctx.text(node.args[0].left)})*digr({ctx.text(node.args[0].right)})"]


def _is_bad_root_bound(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 9
    )


def _fix_root_bound(node, ctx):
    return [f"{ctx.text(node.left)}<10"]


def _is_input_in_root_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"d", "root", "digr"}
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
        and len(node.args[0].args) == 0
    )


def _fix_input_in_root_call(node, ctx):
    return [f"{node.func.id}(int(input()))"]


def _is_print_root_of_input(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Call)
        and isinstance(node.value.args[0].func, ast.Name)
        and node.value.args[0].func.id in {"d", "root", "digr"}
    )


def _fix_print_root_of_input(node, ctx):
    return ["n = int(input())\nq, r = divmod(n, 9)\nd = [q] + [q + 1] * r + [q] * (8 - r)\nres = 0\nfor i in range(9):\n    for j in range(9):\n        res += d[i] * d[j] * d[(i * j) % 9]\nfor i in range(1, n + 1):\n    res -= n // i\nprint(res)"]


def _is_mod9_wrong(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 10
    )


def _fix_mod9(node, ctx):
    return [f"{ctx.text(node.left)} % 9"]


def _is_range_start1_to_n_plus_1(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
        and isinstance(node.args[1], ast.BinOp)
        and isinstance(node.args[1].op, ast.Add)
        and isinstance(node.args[1].left, ast.Name)
        and node.args[1].left.id == "n"
        and isinstance(node.args[1].right, ast.Constant)
        and node.args[1].right.value == 1
    )


def _fix_range_start1_to_n_plus_1(node, ctx):
    return [f"range(1, {ctx.text(node.args[1].left)})"]


def _is_nested_range_inclusive(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Name)
        and isinstance(node.args[1], ast.Name)
        and node.args[0].id == node.args[1].id
    )


def _fix_nested_range_inclusive(node, ctx):
    return [f"range({ctx.text(node.args[0])}, {ctx.text(node.args[1])} + 1)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="multiply_digital_roots_then_recurse",
                match=_is_digr_like,
                replace=_fix_digr_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="digital_root_bound_should_be_ten",
                match=_is_bad_root_bound,
                replace=_fix_root_bound,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="input_needs_int_in_root_call",
                match=_is_input_in_root_call,
                replace=_fix_input_in_root_call,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="print_root_of_input_should_be_full_solution",
                match=_is_print_root_of_input,
                replace=_fix_print_root_of_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_modulus_for_nine_based_formula",
                match=_is_mod9_wrong,
                replace=_fix_mod9,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_end_should_be_exclusive_n",
                match=_is_range_start1_to_n_plus_1,
                replace=_fix_range_start1_to_n_plus_1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="inclusive_nested_range_needs_plus_one",
                match=_is_nested_range_inclusive,
                replace=_fix_nested_range_inclusive,
                symptoms=("wrong",),
            ),
        ]