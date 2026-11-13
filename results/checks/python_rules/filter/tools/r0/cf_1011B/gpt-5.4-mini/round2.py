from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_zero_literal(node, ctx):
    return isinstance(node, ast.Constant) and node.value == 0


def _zero_to_one(node, ctx):
    return ["1"]


def _is_bad_floor_division_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.FloorDiv)
        and any(isinstance(c, ast.Name) and c.id == "n" for c in node.comparators)
    )


def _floor_div_check_to_div(node, ctx):
    return [ctx.text(node.left.left) + " / " + ctx.text(node.left.right) + " >= " + ctx.text(node.comparators[0])]


def _is_range_without_inclusive_bound(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[1], ast.Constant)
        and node.args[1].value == 100
    )


def _range_to_inclusive(node, ctx):
    return ["range(" + ctx.text(node.args[0]) + ", 101)"]


def _is_len_food_bound(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[1], ast.Call)
        and isinstance(node.args[1].func, ast.Name)
        and node.args[1].func.id == "len"
    )


def _len_bound_plus_one(node, ctx):
    return ["range(" + ctx.text(node.args[0]) + ", " + ctx.text(node.args[1]) + " + 1)"]


def _is_prev_days_assignment(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "prev_days"
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.FloorDiv)
    )


def _prev_days_ceiling_fix(node, ctx):
    return [ctx.text(node.targets[0]) + " = (" + ctx.text(node.value.left) + " + " + ctx.text(node.value.right) + " - 1) // " + ctx.text(node.value.right)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="zero_bound_should_be_one",
                match=_is_zero_literal,
                replace=_zero_to_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="floor_division_in_feasibility_check",
                match=_is_bad_floor_division_check,
                replace=_floor_div_check_to_div,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_upper_bound_100_should_be_101",
                match=_is_range_without_inclusive_bound,
                replace=_range_to_inclusive,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_bound_should_be_inclusive",
                match=_is_len_food_bound,
                replace=_len_bound_plus_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="days_should_use_ceiling_division",
                match=_is_prev_days_assignment,
                replace=_prev_days_ceiling_fix,
                symptoms=("wrong",),
            ),
        ]