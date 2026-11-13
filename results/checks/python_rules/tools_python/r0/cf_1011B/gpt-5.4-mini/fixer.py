from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_range_100(node, ctx):
    return (
        isinstance(node, ast.Constant)
        and isinstance(node.value, int)
        and node.value == 100
    )


def _to_range_100000(node, ctx):
    return ["100000"]


def _is_counter_input_split(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "Counter"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Attribute)
        and node.args[0].func.attr == "split"
    )


def _to_counter_list_input(node, ctx):
    return [f"collections.Counter({ctx.text(node.args[0].func.value)}.split())"]


def _is_strict_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_strict_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _to_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_range_len(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
        and node.args[0].id == "len"
    )


def _replace_with_same_range(node, ctx):
    return [ctx.text(node)]


def _is_literal_one(node, ctx):
    return isinstance(node, ast.Constant) and node.value == 1


def _to_literal_zero(node, ctx):
    return ["0"]


def _is_range_1_100(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 1
        and isinstance(node.args[1], ast.Constant)
        and node.args[1].value == 100
    )


def _to_range_1_101(node, ctx):
    return ["range(1, 101)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="binary_search_upper_bound_100_to_100000",
                match=_is_range_100,
                replace=_to_range_100000,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="counter_input_split_should_list_input_split",
                match=_is_counter_input_split,
                replace=_to_counter_list_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_lt_should_be_lte",
                match=_is_strict_lt,
                replace=_to_lte,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_gt_should_be_gte",
                match=_is_strict_gt,
                replace=_to_gte,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_len_off_by_one",
                match=_is_range_len,
                replace=_replace_with_same_range,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="one_misused_as_zero",
                match=_is_literal_one,
                replace=_to_literal_zero,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_1_100_should_include_100",
                match=_is_range_1_100,
                replace=_to_range_1_101,
                symptoms=("wrong",),
            ),
        ]