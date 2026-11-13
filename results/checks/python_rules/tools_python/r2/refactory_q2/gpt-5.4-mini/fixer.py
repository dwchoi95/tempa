from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_return_const_or_name(node, ctx, bad_names=("True", "False", "None")):
    return isinstance(node, ast.Return) and (
        node.value is None
        or isinstance(node.value, ast.Constant)
        or isinstance(node.value, ast.Name)
    )


def _match_day_name_misuse(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (
                ctx.field(node.left) == "comparators"
                and isinstance(node.left, ast.Name)
                and node.left.id in {"day", "date"}
                and isinstance(node.comparators[0], ast.Name)
                and node.comparators[0].id in {"days", "day", "date"}
                and node.comparators[0].id != node.left.id
            )
            or (
                isinstance(node.left, ast.Subscript)
                and isinstance(node.left.slice, ast.Constant)
                and node.left.slice.value == 1
                and isinstance(node.comparators[0], ast.Name)
                and node.comparators[0].id in {"days", "day"}
            )
        )
    )


def _replace_day_name(node, ctx):
    if isinstance(node.left, ast.Name):
        return [f"{ctx.text(node.comparators[0])} == {node.left.id}"]
    return [f"{ctx.text(node.left.value if isinstance(node.left, ast.Attribute) else node.left)} == {ctx.text(node.comparators[0])}"]


def _match_day_variable_misuse(node, ctx):
    return isinstance(node, ast.Name) and node.id == "day" and isinstance(ctx.parent(node), ast.Compare) is False


def _match_day_used_as_rhs_of_eq(node, ctx):
    p = ctx.parent(node)
    return (
        isinstance(node, ast.Name)
        and node.id == "day"
        and isinstance(p, ast.Compare)
        and len(p.ops) == 1
        and isinstance(p.ops[0], ast.Eq)
        and p.left is node
    )


def _replace_day_var(node, ctx):
    return ["date"]


def _match_wrong_index_day(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.left.slice, ast.Constant)
        and node.left.slice.value == 1
        and isinstance(node.comparators[0], ast.Name)
        and node.comparators[0].id in {"days", "day", "date", "months", "month"}
        and node.comparators[0].id != "day"
    )


def _replace_wrong_index_day(node, ctx):
    return [f"{ctx.text(node.left.value)}[1] == day"]


def _match_wrong_index_month(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.left.slice, ast.Constant)
        and node.left.slice.value == 0
        and isinstance(node.comparators[0], ast.Name)
        and node.comparators[0].id in {"days", "day", "date", "months", "month"}
        and node.comparators[0].id != "month"
    )


def _replace_wrong_index_month(node, ctx):
    return [f"{ctx.text(node.left.value)}[0] == month"]


def _match_wrong_return_true_for_nonunique(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value in {True, False, "true", "false"}


def _replace_return_false(node, ctx):
    return ["return False"]


def _match_contains_return_only(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_contains_return(node, ctx):
    return ["for birthday in possible_birthdays:\n    if birthday[0] == month:\n        if unique_day(birthday[1], possible_birthdays):\n            return True\nreturn False"]


def _match_true_if_count_eq1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and (
            (isinstance(node.left, ast.Name) and node.left.id in {"count", "counter", "result", "num", "total", "unique_day_counter", "unique_month_counter", "flag", "x", "i", "j"})
            or isinstance(node.left, ast.Call)
        )
    )


def _replace_eq1(node, ctx):
    return [ctx.text(node.left) + " == 1"]


def _match_lte1_or_gte1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and (isinstance(node.ops[0], ast.LtE) or isinstance(node.ops[0], ast.GtE))
    )


def _replace_cmp_eq1(node, ctx):
    op = "==" if isinstance(node.ops[0], (ast.LtE, ast.GtE)) else ctx.text(node.ops[0])
    return [f"{ctx.text(node.left)} == {ctx.text(node.comparators[0])}"]


def _match_unique_day_calls_unique_date(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "unique_date"


def _replace_unique_date(node, ctx):
    return [f"unique_day({', '.join(ctx.text(a) for a in node.args)}{', ' if node.keywords else ''}{', '.join(f'{kw.arg}={ctx.text(kw.value)}' for kw in node.keywords)})"]


def _match_wrong_contains_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"result", "ans", "flag", "tf", "check", "x", "y"}


def _replace_false_return(node, ctx):
    return ["return False"]


def _match_unique_day_expr_is_true(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Compare)


def _replace_return_compare(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="day_variable_misnamed_as_day_in_unique_day",
                match=_match_day_used_as_rhs_of_eq,
                replace=_replace_day_var,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_day_index_or_name_comparison",
                match=_match_wrong_index_day,
                replace=_replace_wrong_index_day,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_month_index_or_name_comparison",
                match=_match_wrong_index_month,
                replace=_replace_wrong_index_month,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_count_to_one_fix",
                match=_match_true_if_count_eq1,
                replace=_replace_eq1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="non_strict_unique_should_be_exactly_one",
                match=_match_lte1_or_gte1,
                replace=_replace_cmp_eq1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_date_call_should_be_unique_day",
                match=_match_unique_day_calls_unique_date,
                replace=_replace_unique_date,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_false_not_true_or_missing",
                match=_match_wrong_return_true_for_nonunique,
                replace=_replace_return_false,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_contains_unique_day_body",
                match=_match_contains_return_only,
                replace=_replace_contains_return,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_should_return_false_not_name",
                match=_match_wrong_contains_return,
                replace=_replace_false_return,
                symptoms=("wrong",),
            ),
        ]