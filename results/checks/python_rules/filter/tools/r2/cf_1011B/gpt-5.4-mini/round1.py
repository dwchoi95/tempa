from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_compare(node, op_type=None):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and (
        op_type is None or isinstance(node.ops[0], op_type)
    )


def _range_too_small(node, ctx):
    return (
        isinstance(node, ast.Constant)
        and isinstance(node.value, int)
        and node.value == 100
        and isinstance(ctx.parent(node), ast.Assign) is False
    )


def _expand_100_bound(node, ctx):
    return ["100000"]


def _is_compare_lt_zero(node, ctx):
    return _is_compare(node, ast.GtE)


def _to_gt_zero(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


def _is_ge_one_check(node, ctx):
    return _is_compare(node, ast.GtE) and isinstance(node.comparators[0], ast.Constant) and node.comparators[0].value == 1


def _to_gt_zero_check(node, ctx):
    return [ctx.text(node.left) + " > 0"]


def _is_range_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"


def _range_upper_bound_off_by_one(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
    )


def _fix_range_upper_bound(node, ctx):
    return [f"range({ctx.text(node.args[0])} + 1)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="expand_binary_search_upper_bound",
                match=_range_too_small,
                replace=_expand_100_bound,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_check_should_include_one",
                match=_is_ge_one_check,
                replace=lambda node, ctx: [ctx.text(node.left) + " >= 1"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_missing_end_inclusive",
                match=_range_upper_bound_off_by_one,
                replace=_fix_range_upper_bound,
                symptoms=("wrong",),
            ),
        ]