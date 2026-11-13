from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_function_named(name):
    def _match(node, ctx):
        return isinstance(node, ast.FunctionDef) and node.name == name
    return _match


def _is_day_compare_to_wrong_name(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Name)
        and ctx.text(node.left) in {"date", "day"}
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Name)
        and ctx.text(node.comparators[0]) != ctx.text(node.left)
    )


def _replace_compare_with_left_name(node, ctx):
    return [f"{ctx.text(node.left)} == {ctx.text(node.comparators[0])}"]


def _is_month_compare_to_wrong_name(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Name)
        and ctx.text(node.left) == "month"
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Name)
        and ctx.text(node.comparators[0]) not in {"month"}
    )


def _replace_month_compare(node, ctx):
    return [f"{ctx.text(node.left)} == {ctx.text(node.comparators[0])}"]


def _is_unique_day_bad_return(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Compare)
        and len(node.value.ops) == 1
        and isinstance(node.value.ops[0], (ast.LtE, ast.GtE))
    )


def _replace_unique_day_return(node, ctx):
    left = ctx.text(node.value.left)
    right = ctx.text(node.value.comparators[0])
    op = "==" if isinstance(node.value.ops[0], (ast.LtE, ast.GtE)) else ctx.text(node.value.ops[0])
    return [f"return {left} {op} {right}"]


def _is_contains_returning_boolexpr(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value).strip() in {"True", "False"} and isinstance(ctx.parent(node), ast.FunctionDef)


def _replace_contains_with_loop(node, ctx):
    return []


def _is_compare_to_wrong_index(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.value, ast.Name)
        and ctx.text(node.value) in {"possible_birthdays", "possible_birthday"}
        and isinstance(node.slice, ast.Constant)
        and node.slice.value in (1, 2)
    )


def _fix_possible_birthdays_index(node, ctx):
    if isinstance(node.slice, ast.Constant) and node.slice.value == 2:
        return [f"{ctx.text(node.value)}[0]"]
    return [ctx.text(node)]


def _is_wrong_bool_constant(node, ctx):
    return isinstance(node, ast.NameConstant) and node.value is True and ctx.text(node) == "true"


def _fix_true_constant(node, ctx):
    return ["True"]


def _is_contains_wrong_name_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and ctx.text(node.func) in {"unique_date", "unique_months"}


def _fix_unique_date_call(node, ctx):
    return [ctx.text(node).replace("unique_date", "unique_day").replace("unique_months", "unique_month")]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="compare_day_name_to_parameter",
                match=_is_day_compare_to_wrong_name,
                replace=_replace_compare_with_left_name,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_month_name_to_parameter",
                match=_is_month_compare_to_wrong_name,
                replace=_replace_month_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_day_bad_threshold_return",
                match=_is_unique_day_bad_return,
                replace=_replace_unique_day_return,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_wrong_call_name",
                match=_is_contains_wrong_name_call,
                replace=_fix_unique_date_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_positional_index_for_month",
                match=_is_compare_to_wrong_index,
                replace=_fix_possible_birthdays_index,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="lowercase_true_literal",
                match=_is_wrong_bool_constant,
                replace=_fix_true_constant,
                symptoms=("wrong",),
            ),
        ]