from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_compare(node, op_type):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], op_type)


def _is_name(node, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_constant_bool(node, value):
    return isinstance(node, ast.Constant) and node.value is value


def _is_return_name(node, name):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == name


def _is_return_call(node, func_name):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == func_name
    )


def _replace_return_expr(expr_text, replacement):
    return [replacement]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="compare_to_wrong_variable_in_unique_day",
                match=lambda node, ctx: _is_compare(node, ast.Eq)
                and _is_name(node.left, "day")
                and len(node.comparators) == 1
                and isinstance(node.comparators[0], ast.Name)
                and node.comparators[0].id in {"days", "day"},
                replace=lambda node, ctx: [ctx.text(node.left) + " == " + ctx.text(node.comparators[0]).replace("days", "birthday[1]").replace("day", "birthday[1]")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_to_wrong_variable_in_unique_month",
                match=lambda node, ctx: _is_compare(node, ast.Eq)
                and _is_name(node.left, "month")
                and len(node.comparators) == 1
                and isinstance(node.comparators[0], ast.Name)
                and node.comparators[0].id in {"days", "day"},
                replace=lambda node, ctx: [ctx.text(node.left) + " == birthday[0]"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_day_wrong_counter_variable",
                match=lambda node, ctx: _is_name(node, "days"),
                replace=lambda node, ctx: ["count"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_month_wrong_counter_variable",
                match=lambda node, ctx: _is_name(node, "months"),
                replace=lambda node, ctx: ["count"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_day_misspelled_true",
                match=lambda node, ctx: _is_name(node, "true"),
                replace=lambda node, ctx: ["True"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_day_misspelled_false",
                match=lambda node, ctx: _is_name(node, "flase"),
                replace=lambda node, ctx: ["False"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_day_misspelled_false_lower",
                match=lambda node, ctx: _is_name(node, "false"),
                replace=lambda node, ctx: ["False"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="strict_greater_than_one_should_be_equal_one",
                match=lambda node, ctx: _is_compare(node, ast.Gt),
                replace=lambda node, ctx: [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="nonunique_returns_true_instead_of_false",
                match=lambda node, ctx: isinstance(node, ast.Return)
                and isinstance(node.value, ast.Compare)
                and len(node.value.ops) == 1
                and isinstance(node.value.ops[0], ast.Gt)
                and ctx.text(node.value.left).strip() in {"counter", "count", "result", "num", "x", "i", "total", "unique"},
                replace=lambda node, ctx: [f"return {ctx.text(node.value.left)} == {ctx.text(node.value.comparators[0])}"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_constant_true_for_contains_should_loop_over_month",
                match=lambda node, ctx: _is_return_name(node, "True")
                and isinstance(ctx.parent(node), ast.If),
                replace=lambda node, ctx: [ctx.text(node)],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="delete_bare_return_in_contains",
                match=lambda node, ctx: isinstance(node, ast.Return) and node.value is None,
                replace=lambda node, ctx: ["return False"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_return_true_on_any_match",
                match=lambda node, ctx: isinstance(node, ast.Return)
                and isinstance(node.value, ast.Name)
                and node.value.id == "True",
                replace=lambda node, ctx: ["return True"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_return_false_on_empty_loop",
                match=lambda node, ctx: isinstance(node, ast.Return) and node.value is None,
                replace=lambda node, ctx: ["return False"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_use_month_filtered_days",
                match=lambda node, ctx: isinstance(node, ast.Return)
                and isinstance(node.value, ast.Call)
                and isinstance(node.value.func, ast.Name)
                and node.value.func.id in {"unique_date", "unique_day"},
                replace=lambda node, ctx: [ctx.text(node)],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_unique_date_with_unique_day",
                match=lambda node, ctx: isinstance(node, ast.Name) and node.id == "unique_date",
                replace=lambda node, ctx: ["unique_day"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_off_by_one_leq",
                match=lambda node, ctx: isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], ast.LtE),
                replace=lambda node, ctx: [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])],
                symptoms=("wrong",),
            ),
        ]