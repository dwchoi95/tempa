from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_unique_day_bug(node, ctx):
    return (
        isinstance(node, ast.FunctionDef)
        and node.name == "unique_day"
        and len(node.args.args) >= 1
        and isinstance(node.args.args[0], ast.arg)
        and node.args.args[0].arg in {"date", "day"}
    )


def _fix_unique_day_params(node, ctx):
    if not node.args.args:
        return []
    first = node.args.args[0]
    if first.arg == "date":
        args = [ctx.text(a) for a in node.args.args]
        args[0] = "day"
        header = f"def unique_day({', '.join(args)}):"
        return [header]
    return []


def _is_unique_month_bug(node, ctx):
    return (
        isinstance(node, ast.FunctionDef)
        and node.name == "unique_month"
        and len(node.args.args) >= 1
        and isinstance(node.args.args[0], ast.arg)
        and node.args.args[0].arg in {"day", "date"}
    )


def _fix_unique_month_params(node, ctx):
    if not node.args.args:
        return []
    first = node.args.args[0]
    if first.arg != "month":
        args = [ctx.text(a) for a in node.args.args]
        args[0] = "month"
        header = f"def unique_month({', '.join(args)}):"
        return [header]
    return []


def _is_contains_unique_day_missing_or_wrong(node, ctx):
    return (
        isinstance(node, ast.FunctionDef)
        and node.name == "contains_unique_day"
        and (
            len(node.body) == 1
            and isinstance(node.body[0], (ast.Return, ast.Pass))
            or len(node.body) >= 1
        )
    )


def _fix_contains_unique_day(node, ctx):
    return ["""def contains_unique_day(month, possible_birthdays):
    for birthday in possible_birthdays:
        if birthday[0] == month:
            if unique_day(birthday[1], possible_birthdays):
                return True
    return False"""]


def _is_compare_len_gt_one(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Gt)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _replace_gt_one_with_eq_one(node, ctx):
    return [f"{ctx.text(node.left)} == 1"]


def _is_compare_len_ge_two(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _replace_ge_two_with_eq_one(node, ctx):
    return [f"{ctx.text(node.left)} == 1"]


def _is_false_literal(node, ctx):
    return isinstance(node, ast.Constant) and node.value is False


def _replace_false_with_true(node, ctx):
    return ["True"]


def _is_true_literal(node, ctx):
    return isinstance(node, ast.Constant) and node.value is True


def _replace_true_with_false(node, ctx):
    return ["False"]


def _is_name_day_in_month(node, ctx):
    return isinstance(node, ast.Name) and node.id in {"days", "day", "count", "result"} and isinstance(
        ctx.parent(node), ast.Compare
    )


def _is_bad_return_name(node, ctx):
    return isinstance(node, ast.Name) and node.id in {"true", "false", "Flase"}


def _fix_bad_return_name(node, ctx):
    return ["True" if node.id.lower() == "true" else "False"]


def _is_wrong_unique_day_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"unique_date"}
        and len(node.args) == 1
    )


def _fix_unique_date_call(node, ctx):
    return [f"unique_day({', '.join(ctx.text(a) for a in node.args)})"]


def _is_return_none_or_pass(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _fix_return_none(node, ctx):
    return [""]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="unique_day_param_name",
                match=_is_unique_day_bug,
                replace=_fix_unique_day_params,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_month_param_name",
                match=_is_unique_month_bug,
                replace=_fix_unique_month_params,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="contains_unique_day_stub",
                match=_is_contains_unique_day_missing_or_wrong,
                replace=_fix_contains_unique_day,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="gt_one_should_eq_one",
                match=_is_compare_len_gt_one,
                replace=_replace_gt_one_with_eq_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="ge_two_should_eq_one",
                match=_is_compare_len_ge_two,
                replace=_replace_ge_two_with_eq_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="false_literal",
                match=_is_false_literal,
                replace=_replace_false_with_true,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="true_literal",
                match=_is_true_literal,
                replace=_replace_true_with_false,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="bad_return_name",
                match=_is_bad_return_name,
                replace=_fix_bad_return_name,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="unique_date_call",
                match=_is_wrong_unique_day_call,
                replace=_fix_unique_date_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="remove_empty_return",
                match=_is_return_none_or_pass,
                replace=_fix_return_none,
                symptoms=("wrong",),
            ),
        ]