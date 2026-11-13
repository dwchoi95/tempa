from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_bool_const(node):
    return isinstance(node, ast.Constant) and isinstance(node.value, bool)


def _is_none_return(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _fix_return_false(node, ctx):
    return ["return False"]


def _fix_return_true(node, ctx):
    return ["return True"]


def _replace_name_with(node, ctx, new_name):
    return [new_name]


def _is_unique_day_compare_with_day(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (_is_name(node.left, "day") and ctx.text(node.comparators[0]) in {"day", "date"})
            or (_is_name(node.comparators[0], "day") and ctx.text(node.left) in {"day", "date"})
        )
    )


def _flip_count_compare_to_eq1(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1):
        return False
    op = node.ops[0]
    if isinstance(op, (ast.LtE, ast.Gt, ast.NotEq)):
        left = ctx.text(node.left)
        right = ctx.text(node.comparators[0])
        if left in {"count", "counter", "num", "result", "days", "months", "total", "unique_day_counter",
                    "count_day", "count_month", "appearance", "freq", "checker", "value", "x", "i", "j"}:
            return right == "1"
    return False


def _replace_compare_eq1(node, ctx):
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    return [f"{left} == {right}"]


def _is_contains_returning_direct_bool(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"x", "y", "tf"}


def _replace_with_false(node, ctx):
    return ["return False"]


def _is_wrong_month_index(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and ctx.text(node.slice) == "1"
        and isinstance(ctx.parent(node), ast.Compare)
        and "month" in ctx.text(ctx.parent(node))
    )


def _fix_month_index(node, ctx):
    return [ctx.text(node.value) + "[0]"]


class Fixer:
    def rules(self):
        return [
            Rewrite("replace_return_none_with_false", _is_none_return, _fix_return_false, symptoms=("wrong",)),
            Rewrite("compare_to_true_when_boolean_needed", lambda n, c: _is_bool_const(n) and n.value is True, _fix_return_true, symptoms=("wrong",)),
            Rewrite("day_param_name_mismatch", _is_unique_day_compare_with_day, lambda n, c: [ctx.text(n.left) + " == " + ctx.text(n.comparators[0])], symptoms=("wrong",)),
            Rewrite("flip_count_bound_to_eq1", _flip_count_compare_to_eq1, _replace_compare_eq1, symptoms=("wrong",)),
            Rewrite("wrong_month_index", _is_wrong_month_index, _fix_month_index, symptoms=("wrong",)),
        ]