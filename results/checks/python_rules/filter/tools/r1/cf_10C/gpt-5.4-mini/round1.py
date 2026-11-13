from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_without_int(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _wrap_int(node, ctx):
    return [f"int({ctx.text(node)})"]


def _is_len_str_loop_cond(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.left.args[0], ast.Call)
        and isinstance(node.left.args[0].func, ast.Name)
        and node.left.args[0].func.id == "str"
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _len_str_eq_one(node, ctx):
    return [f"{ctx.text(node.left)} == {ctx.text(node.comparators[0])}"]


def _is_range_inclusive_loop(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and len(node.keywords) == 0
        and isinstance(node.args[1], ast.Name)
        and node.args[1].id in {"n", "N"}
    )


def _range_stop_plus_one(node, ctx):
    return [f"range({ctx.text(node.args[0])}, {ctx.text(node.args[1])} + 1)"]


def _is_self_mul(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mult)
        and isinstance(node.left, ast.Name)
        and isinstance(node.right, ast.Name)
        and node.left.id == node.right.id
    )


def _to_pow_two(node, ctx):
    return [f"{ctx.text(node.left)} ** 2"]


def _is_strict_lt(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Lt)
    )


def _to_lte(node, ctx):
    return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]


def _is_return_input(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Call) and _is_input_without_int(node.value, ctx)


def _return_int_input(node, ctx):
    return ["return int(input())"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="input_needs_int", match=_is_input_without_int, replace=_wrap_int, symptoms=("wrong",)),
            Rewrite(name="len_str_loop_should_stop_at_one", match=_is_len_str_loop_cond, replace=_len_str_eq_one, symptoms=("wrong",)),
            Rewrite(name="range_upper_bound_inclusive", match=_is_range_inclusive_loop, replace=_range_stop_plus_one, symptoms=("wrong",)),
            Rewrite(name="self_multiplication_should_be_square", match=_is_self_mul, replace=_to_pow_two, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt, replace=_to_lte, symptoms=("wrong",)),
            Rewrite(name="return_input_needs_int", match=_is_return_input, replace=_return_int_input, symptoms=("wrong",)),
        ]