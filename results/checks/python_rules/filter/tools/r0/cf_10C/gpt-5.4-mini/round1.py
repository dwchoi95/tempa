from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and len(node.args) == 0
        and len(node.keywords) == 0
    )


def _is_int_call_on_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and _is_input_call(node.args[0], ctx)
        and len(node.keywords) == 0
    )


def _replace_input_with_int_input(node, ctx):
    return ["int(input())"]


def _is_digitroot_recursive_sum(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"digr", "root", "d"}
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Mult)
    )


def _replace_recursive_digitroot_call(node, ctx):
    arg = node.args[0]
    return [f"{ctx.text(node.func)}({ctx.text(arg.left)}) * {ctx.text(arg.right)}"]


def _is_nested_range_inclusive(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value in (0, 1)
        and isinstance(node.args[1], ast.Name)
    )


def _fix_range_upper_bound(node, ctx):
    return [f"range({ctx.text(node.args[0])}, {ctx.text(node.args[1])} + 1)"]


def _is_compare_lt_to_self_mult(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Lt)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.BinOp)
        and isinstance(node.comparators[0].op, ast.Mult)
    )


def _fix_compare_to_le(node, ctx):
    return [f"{ctx.text(node.left)} <= {ctx.text(node.comparators[0])}"]


def _is_input_used_as_number(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"d", "root"}
        and len(node.args) == 1
        and _is_input_call(node.args[0], ctx)
    )


def _wrap_input_with_int(node, ctx):
    return [f"{ctx.text(node.func)}(int(input()))"]


def _is_return_zero(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value == 0


def _remove_wrong_return(node, ctx):
    return [""]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="input_needs_int_conversion",
                match=_is_int_call_on_input,
                replace=_replace_input_with_int_input,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="digit_root_should_not_recurse_on_product_structure",
                match=_is_digitroot_recursive_sum,
                replace=_replace_recursive_digitroot_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="inclusive_range_upper_bound",
                match=_is_nested_range_inclusive,
                replace=_fix_range_upper_bound,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_lt_to_le_for_exact_counts",
                match=_is_compare_lt_to_self_mult,
                replace=_fix_compare_to_le,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrap_input_when_passing_to_numeric_function",
                match=_is_input_used_as_number,
                replace=_wrap_input_with_int,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="remove_dead_return_zero",
                match=_is_return_zero,
                replace=_remove_wrong_return,
                symptoms=("wrong",),
            ),
        ]