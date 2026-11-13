from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_binop(node, ctx):
    return isinstance(node, ast.BinOp) and isinstance(node.op, ast.FloorDiv)


def _fix_div_one(node, ctx):
    return [ctx.text(node.left) + " // (" + ctx.text(node.right) + " - 1)"]


def _is_range_100(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 100
    )


def _range_100001(node, ctx):
    return ["range(100000, 0, -1)"]


def _is_range_100_start(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 100
        and isinstance(ctx.parent(node), ast.For)
        and ctx.field(node) == "iter"
    )


def _range_100_to_101(node, ctx):
    return ["range(100, 0, -1)"]


def _is_compare_gt_eq(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)


def _gt_eq_to_gt(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


def _is_compare_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _lt_to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_name_prev_days(node, ctx):
    return isinstance(node, ast.Name) and node.id == "prev_days"


def _prev_days_to_min_days(node, ctx):
    return ["min_days"]


def _is_name_food(node, ctx):
    return isinstance(node, ast.Name) and node.id == "food"


def _food_to_foodz(node, ctx):
    return ["foodz"]


def _is_assign_r_100(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "r"
        and isinstance(node.value, ast.Constant)
        and node.value.value == 100
    )


def _r_100_to_100000(node, ctx):
    return [ctx.text(node.targets[0]) + " = 100000"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="floor_divisor_should_use_minus_one",
                match=_is_binop,
                replace=_fix_div_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_upper_bound_too_small",
                match=_is_range_100,
                replace=_range_100001,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="range_bound_in_search_loop",
                match=_is_range_100_start,
                replace=_range_100_to_101,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="greater_equal_should_be_greater",
                match=_is_compare_gt_eq,
                replace=_gt_eq_to_gt,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_lt_should_be_lte",
                match=_is_compare_lt,
                replace=_lt_to_lte,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_prev_days_variable",
                match=_is_name_prev_days,
                replace=_prev_days_to_min_days,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_food_sequence_variable",
                match=_is_name_food,
                replace=_food_to_foodz,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="binary_search_upper_bound_too_small",
                match=_is_assign_r_100,
                replace=_r_100_to_100000,
                symptoms=("wrong", "timeout"),
            ),
        ]