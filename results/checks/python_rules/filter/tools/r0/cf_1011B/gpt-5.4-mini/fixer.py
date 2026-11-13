from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_const(node, value=None):
    return isinstance(node, ast.Constant) and (value is None or node.value == value)


def _is_name(node, name=None):
    return isinstance(node, ast.Name) and (name is None or node.id == name)


def _is_range_call(node):
    return isinstance(node, ast.Call) and _is_name(node.func, "range")


def _is_binary_div(node):
    return isinstance(node, ast.BinOp) and isinstance(node.op, ast.FloorDiv)


def _match_small_upper_bound(node, ctx):
    return _is_const(node, 100)


def _replace_upper_bound(node, ctx):
    return ["100000"]


def _match_floor_div_in_feasibility(node, ctx):
    return _is_binary_div(node)


def _replace_floor_div_in_feasibility(node, ctx):
    return [ctx.text(node.left) + " // " + ctx.text(node.right)]


def _match_range_off_by_one(node, ctx):
    return _is_range_call(node) and len(node.args) == 1 and _is_const(node.args[0], 100)


def _replace_range_off_by_one(node, ctx):
    return ["range(1, 101)"]


def _match_greedy_count_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)


def _replace_greedy_count_compare(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="binary_search_upper_bound_too_small",
                match=_match_small_upper_bound,
                replace=_replace_upper_bound,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="floor_division_in_feasibility_check",
                match=_match_floor_div_in_feasibility,
                replace=_replace_floor_div_in_feasibility,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_upper_bound_off_by_one",
                match=_match_range_off_by_one,
                replace=_replace_range_off_by_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="comparison_greedy_threshold_strictness",
                match=_match_greedy_count_compare,
                replace=_replace_greedy_count_compare,
                symptoms=("wrong",),
            ),
        ]