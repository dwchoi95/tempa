from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_str_constant(node, value):
    return isinstance(node, ast.Constant) and node.value == value


def _is_bool_constant(node, value):
    return isinstance(node, ast.Constant) and node.value is value


def _day_param_misused_in_month_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.left.slice, ast.Constant)
        and node.left.slice.value == 0
        and _is_name(node.comparators[0], "month")
    )


def _fix_day_month_compare(node, ctx):
    return [ctx.text(node.left.value) + "[0] == month"]


def _month_param_misused_in_day_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.left.slice, ast.Constant)
        and node.left.slice.value == 1
        and _is_name(node.comparators[0], "day")
    )


def _fix_month_day_compare(node, ctx):
    return [ctx.text(node.left.value) + "[1] == day"]


def _count_compare_to_le(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and _is_name(node.left, "count")
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_count_eq_one(node, ctx):
    return ["count == 1"]


def _count_compare_to_ge(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and _is_name(node.left, "count")
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_count_eq_one_from_ge(node, ctx):
    return ["count == 1"]


def _unique_day_returns_not_unique(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.NotEq)
        and _is_name(node.left, "count")
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_unique_day_return(node, ctx):
    return ["count == 1"]


def _truthy_name_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"true", "false", "True", "False"}


def _fix_truthy_return(node, ctx):
    if isinstance(node.value, ast.Name) and node.value.id in {"true", "True"}:
        return ["return True"]
    if isinstance(node.value, ast.Name) and node.value.id in {"false", "False"}:
        return ["return False"]
    return []


def _contains_return_bool_name(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id in {"unique_day", "unique_month"}


def _fix_contains_return(node, ctx):
    return ["return False"]


def _contains_unique_day_return_self(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node).strip() == "return"


def _fix_contains_unique_day_return(node, ctx):
    return ["for birthday in possible_birthdays:\n    if birthday[0] == month:\n        if unique_day(birthday[1], possible_birthdays):\n            return True\nreturn False"]


def _wrong_subscript_in_unique_month(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.left.slice, ast.Constant)
        and node.left.slice.value == 1
    )


def _fix_unique_month_subscript(node, ctx):
    return [ctx.text(node.left.value) + "[0] == month"]


def _wrong_subscript_in_unique_day(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Subscript)
        and isinstance(node.left.slice, ast.Constant)
        and node.left.slice.value == 0
    )


def _fix_unique_day_subscript(node, ctx):
    return [ctx.text(node.left.value) + "[1] == day"]


def _bad_unique_day_call_arg(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "unique_day"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Subscript)
        and isinstance(node.args[0].slice, ast.Constant)
        and node.args[0].slice.value == 0
    )


def _fix_bad_unique_day_call_arg(node, ctx):
    return [ctx.text(node.func) + "(" + ctx.text(node.args[0].value) + "[1], " + ctx.text(node.args[1]) + ")"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="month_compare_uses_day_field", match=_day_param_misused_in_month_compare, replace=_fix_day_month_compare, symptoms=("wrong",)),
            Rewrite(name="day_compare_uses_month_field", match=_month_param_misused_in_day_compare, replace=_fix_month_day_compare, symptoms=("wrong",)),
            Rewrite(name="count_le_one_should_eq_one", match=_count_compare_to_le, replace=_fix_count_eq_one, symptoms=("wrong",)),
            Rewrite(name="count_ge_one_should_eq_one", match=_count_compare_to_ge, replace=_fix_count_eq_one_from_ge, symptoms=("wrong",)),
            Rewrite(name="unique_day_must_require_exactly_one", match=_unique_day_returns_not_unique, replace=_fix_unique_day_return, symptoms=("wrong",)),
            Rewrite(name="lowercase_bool_return", match=_truthy_name_return, replace=_fix_truthy_return, symptoms=("err:NameError", "wrong")),
            Rewrite(name="contains_unique_day_missing_body", match=_contains_unique_day_return_self, replace=_fix_contains_unique_day_return, symptoms=("wrong",)),
            Rewrite(name="unique_month_uses_day_subscript", match=_wrong_subscript_in_unique_month, replace=_fix_unique_month_subscript, symptoms=("wrong",)),
            Rewrite(name="unique_day_uses_month_subscript", match=_wrong_subscript_in_unique_day, replace=_fix_unique_day_subscript, symptoms=("wrong",)),
            Rewrite(name="contains_unique_day_calls_unique_day_with_month_field", match=_bad_unique_day_call_arg, replace=_fix_bad_unique_day_call_arg, symptoms=("wrong",)),
        ]