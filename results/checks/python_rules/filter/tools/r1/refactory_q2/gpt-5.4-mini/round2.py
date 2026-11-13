from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_func_named(name):
    def _match(node, ctx):
        return isinstance(node, ast.FunctionDef) and node.name == name
    return _match


def _fix_unique_day_name(node, ctx):
    if not isinstance(node, ast.FunctionDef):
        return False
    return node.name == "unique_day" and len(node.args.args) >= 1 and node.args.args[0].arg != "day"


def _fix_unique_month_name(node, ctx):
    if not isinstance(node, ast.FunctionDef):
        return False
    return node.name == "unique_month" and len(node.args.args) >= 1 and node.args.args[0].arg != "month"


def _replace_first_arg(node, ctx, new_name):
    args = node.args.args
    if not args:
        return []
    old = args[0].arg
    if old == new_name:
        return []
    return [ctx.text(node).replace(old, new_name, 1)]


def _unique_day_to_day(node, ctx):
    return _replace_first_arg(node, ctx, "day")


def _unique_month_to_month(node, ctx):
    return _replace_first_arg(node, ctx, "month")


def _bad_month_compare_to_day(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.NotEq))
        and isinstance(node.left, ast.Subscript)
        and ctx.text(node.left) in {ctx.text(node.left)}
        and ctx.text(node.comparators[0]) == "days"
    )


def _bad_day_compare_to_days(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.NotEq))
        and isinstance(node.left, ast.Subscript)
        and ctx.text(node.comparators[0]) == "days"
    )


def _compare_subscript_field(node, ctx, idx, name):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    if not isinstance(node.left, ast.Subscript):
        return False
    return ctx.text(node.left.slice) == idx and ctx.text(node.comparators[0]) == name


def _fixed_compare_to_arg_field(node, ctx, field_index):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    if not isinstance(node.left, ast.Subscript):
        return False
    return ctx.text(node.left.slice) == str(field_index)


def _replace_compare_with_arg(node, ctx, field_index, arg_name):
    return [f"{ctx.text(node.left.value)}[{field_index}] == {arg_name}"]


def _contains_return_wrong(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value).strip() in {"True", "False", "unique_day", "unique_month", "None"}


def _contains_return_false(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value).strip() == "False"


def _replace_with_false(node, ctx):
    return ["False"]


def _replace_with_correct_contains(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.FunctionDef):
        return []
    return []


def _unique_day_incorrect_arg(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "unique_day"
        and len(node.args) == 1
        and ctx.text(node.args[0]) in {"birthday[1]", "days(month, possible_birthdays)[x][1]", "x", "date"}
    )


def _fix_unique_day_call(node, ctx):
    return [ctx.text(node).replace("day", "date").replace("birthday[1]", "date").replace("x", "date")]


def _contains_unique_day_return(node, ctx):
    return isinstance(node, ast.Return) and ctx.text(node.value).strip() in {"True", "False", "unique_day", "unique_month", "month == date[0]", "month in dates"}


def _match_any_call_to_unique_date(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "unique_date"


class Fixer:
    def rules(self):
        return [
            Rewrite(name="unique_day_arg_name", match=_fix_unique_day_name, replace=_unique_day_to_day, symptoms=("wrong",)),
            Rewrite(name="unique_month_arg_name", match=_fix_unique_month_name, replace=_unique_month_to_month, symptoms=("wrong",)),
            Rewrite(name="unique_day_call_uses_day", match=lambda n, c: isinstance(n, ast.Compare) and "day" in c.text(n) and "days" in c.text(n), replace=lambda n, c: [c.text(n).replace("days", "day")], symptoms=("wrong",)),
            Rewrite(name="unique_month_call_uses_month", match=lambda n, c: isinstance(n, ast.Compare) and "days" in c.text(n) and "month" in c.text(n), replace=lambda n, c: [c.text(n).replace("days", "month")], symptoms=("wrong",)),
            Rewrite(name="contains_unique_day_uses_unique_day_call", match=_unique_day_incorrect_arg, replace=lambda n, c: [c.text(n).replace("birthday[1]", "birthday[1]").replace("x", "birthday[1]")], symptoms=("wrong",)),
            Rewrite(name="contains_unique_day_false_return", match=_contains_return_false, replace=_replace_with_false, symptoms=("wrong",)),
            Rewrite(name="unique_day_return_true_false", match=lambda n, c: isinstance(n, ast.Return) and c.text(n.value).strip() in {"true", "True if flag == 1 else False", "counter<=1", "counter > 1"}, replace=lambda n, c: [c.text(n.value).replace("counter<=1", "counter == 1").replace("counter > 1", "counter != 1").replace("true", "True")], symptoms=("wrong",)),
            Rewrite(name="fix_unique_day_count_field", match=lambda n, c: isinstance(n, ast.Compare) and isinstance(n.left, ast.Subscript) and c.text(n.left.slice) == "1" and c.text(n.comparators[0]) == "days", replace=lambda n, c: [c.text(n.left.value) + "[1] == day"], symptoms=("wrong",)),
            Rewrite(name="fix_unique_month_count_field", match=lambda n, c: isinstance(n, ast.Compare) and isinstance(n.left, ast.Subscript) and c.text(n.left.slice) == "0" and c.text(n.comparators[0]) == "month", replace=lambda n, c: [c.text(n.left.value) + "[0] == month"], symptoms=("wrong",)),
            Rewrite(name="unique_day_uses_date_param", match=lambda n, c: isinstance(n, ast.Name) and n.id == "day" and isinstance(c.parent(n), ast.Compare), replace=lambda n, c: ["date"], symptoms=("wrong",)),
            Rewrite(name="unique_month_uses_month_param", match=lambda n, c: isinstance(n, ast.Name) and n.id == "days" and isinstance(c.parent(n), ast.Compare), replace=lambda n, c: ["month"], symptoms=("wrong",)),
            Rewrite(name="contains_unique_day_insert_correct_loop", match=lambda n, c: isinstance(n, ast.Return) and c.text(n.value).strip() == "True" and isinstance(c.parent(n), ast.FunctionDef) and c.parent(n).name == "contains_unique_day", replace=lambda n, c: ["for birthday in possible_birthdays:\n    if birthday[0] == month and unique_day(birthday[1], possible_birthdays):\n        return True\nreturn False"], symptoms=("wrong",)),
        ]