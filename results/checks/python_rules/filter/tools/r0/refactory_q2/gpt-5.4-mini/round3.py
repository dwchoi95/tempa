from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_func_named(name):
    def _match(node, ctx):
        return isinstance(node, ast.FunctionDef) and node.name == name
    return _match


def _arg_name(func_node, idx):
    return func_node.args.args[idx].arg


def _is_name(node, value):
    return isinstance(node, ast.Name) and node.id == value


def _is_compare_eq(node):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)


def _replace_name(old, new):
    def _replace(node, ctx):
        return [new]
    return _replace


def _unique_day_misnamed_var(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and ctx.text(node.left) == "day"
        and ctx.text(node.comparators[0]) in {"day", "days"}
    )


def _fix_unique_day_compare(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


def _unique_month_misnamed_var(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and ctx.text(node.left) == "month"
        and ctx.text(node.comparators[0]) in {"days", "day"}
    )


def _fix_unique_month_compare(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


def _contains_unique_day_return_bug(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value) in {"", "None"} if getattr(node, "value", None) is not None else False


def _contains_unique_day_return_fix(node, ctx):
    return ["False"]


def _contains_unique_day_return_true(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value) in {"True", "unique_day(birthday[1], possible_birthdays)", "unique_day(birthday[1],possible_birthdays)", "unique_day(i[1],possible_birthdays)", "unique_day(i[1], possible_birthdays)"}


def _contains_unique_day_return_true_fix(node, ctx):
    return ["False"]


def _contains_unique_day_wrong_return_only(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value).strip() == "True"


def _contains_unique_day_wrong_return_only_fix(node, ctx):
    return ["False"]


def _contains_unique_day_bad_month_test(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and ctx.text(node.left) in {"month", "possible_birthdays[i][0]"}
        and ctx.text(node.comparators[0]) in {"days", "day"}
    )


def _contains_unique_day_bad_month_test_fix(node, ctx):
    return [ctx.text(node.left).replace("day", "month").replace("days", "month") + " == " + ctx.text(node.comparators[0]).replace("days", "month").replace("day", "month")]


def _contains_unique_day_first_stmt_return(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value).strip() in {"True", "False"} and isinstance(ctx.parent(node), ast.FunctionDef)


def _contains_unique_day_nonlocal_false(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value).strip() == "False"


def _contains_unique_day_nonlocal_false_fix(node, ctx):
    return ["False"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="unique_day_compare_use_parameter",
                match=_unique_day_misnamed_var,
                replace=_fix_unique_day_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_month_compare_use_parameter",
                match=_unique_month_misnamed_var,
                replace=_fix_unique_month_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_return_false_not_true",
                match=lambda node, ctx: isinstance(node, ast.Return)
                and ctx.text(node.value).strip() == "True"
                and isinstance(ctx.parent(node), ast.FunctionDef)
                and ctx.parent(node).name == "contains_unique_day",
                replace=lambda node, ctx: ["False"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_missing_return_false",
                match=lambda node, ctx: isinstance(node, ast.Return)
                and getattr(node, "value", None) is None
                and isinstance(ctx.parent(node), ast.FunctionDef)
                and ctx.parent(node).name == "contains_unique_day",
                replace=lambda node, ctx: ["return False"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_bad_month_argument",
                match=lambda node, ctx: isinstance(node, ast.Call)
                and ctx.text(node.func) == "unique_day"
                and len(node.args) == 1
                and ctx.text(node.args[0]) in {"x", "day"}
                and isinstance(ctx.parent(node), ast.Return)
                and isinstance(ctx.parent(ctx.parent(node)), ast.FunctionDef)
                and ctx.parent(ctx.parent(node)).name == "contains_unique_day",
                replace=lambda node, ctx: [f"unique_day({ctx.text(node.args[0])}, possible_birthdays)"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_month_filter_compare",
                match=lambda node, ctx: isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], ast.Eq)
                and ctx.text(node.left) in {"i[0]", "birthday[0]", "birthmonth[0]"}
                and ctx.text(node.comparators[0]) in {"month", "months"},
                replace=lambda node, ctx: [f"{ctx.text(node.left)} == month"],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_wrong_month_index",
                match=lambda node, ctx: isinstance(node, ast.Subscript)
                and ctx.text(node) in {"possible_birthdays[i][1]", "possible_birthdays[i][2]"}
                and isinstance(ctx.parent(node), ast.Compare),
                replace=lambda node, ctx: [ctx.text(node).replace("[1]", "[0]").replace("[2]", "[0]")],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_day_use_equals_not_less_equal",
                match=lambda node, ctx: isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], ast.LtE),
                replace=lambda node, ctx: [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_month_use_equals_not_less_equal",
                match=lambda node, ctx: isinstance(node, ast.Compare)
                and len(node.ops) == 1
                and isinstance(node.ops[0], ast.LtE),
                replace=lambda node, ctx: [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_return_any_match",
                match=lambda node, ctx: isinstance(node, ast.Return)
                and ctx.text(node.value).strip() in {"True", "False"}
                and isinstance(ctx.parent(node), ast.FunctionDef)
                and ctx.parent(node).name == "contains_unique_day",
                replace=lambda node, ctx: ["False"],
                symptoms=("wrong",),
            ),
        ]