from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bound_100(node, ctx):
    return isinstance(node, ast.Constant) and node.value == 100


def _to_big_bound(node, ctx):
    return ["100000"]


def _is_food_indexing(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.value, ast.Name)
        and node.value.id == "food"
        and isinstance(node.slice, ast.Name)
        and node.slice.id == "i"
    )


def _fix_food_indexing(node, ctx):
    return [ctx.text(node.value) + "[j]"]


def _is_zero_range(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value == 0
    )


def _to_full_range(node, ctx):
    return ["range(1, len(food))"]


def _is_prev_days_initialization(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "prev_days"
    )


def _fix_prev_days_initialization(node, ctx):
    return ["prev_days = food[0] // n"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="binary_search_upper_bound_too_small",
                match=_is_bound_100,
                replace=_to_big_bound,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="preserve_food_indexing",
                match=_is_food_indexing,
                replace=_fix_food_indexing,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="iterate_all_food_types_instead_of_starting_at_zero",
                match=_is_zero_range,
                replace=_to_full_range,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="divide_by_participants_for_initial_days",
                match=_is_prev_days_initialization,
                replace=_fix_prev_days_initialization,
                symptoms=("wrong",),
            ),
        ]