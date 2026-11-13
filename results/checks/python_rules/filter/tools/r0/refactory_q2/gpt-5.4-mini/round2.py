from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_call_to(node, fname):
    return isinstance(node, ast.Call) and _is_name(node.func, fname)


def _has_unique_day_bug(node, ctx):
    if not isinstance(node, ast.FunctionDef) or node.name != "unique_day":
        return False
    for n in ast.walk(node):
        if isinstance(n, ast.Compare) and isinstance(n.left, ast.Name) and n.left.id == "date":
            if len(n.ops) == 1 and isinstance(n.ops[0], ast.Eq):
                if len(n.comparators) == 1 and _is_name(n.comparators[0], "day"):
                    return False
        if isinstance(n, ast.Name) and n.id == "day":
            return True
    return False


def _fix_unique_day_use_date(node, ctx):
    return [ctx.text(node).replace("day", "date")]


def _fix_unique_month_use_month(node, ctx):
    return [ctx.text(node).replace("day", "month")]


def _contains_unique_day_generic(node, ctx):
    return isinstance(node, ast.FunctionDef) and node.name == "contains_unique_day"


def _replace_contains_unique_day(node, ctx):
    return [
        "def contains_unique_day(month, possible_birthdays):\n"
        "    for birthday in possible_birthdays:\n"
        "        if birthday[0] == month:\n"
        "            if unique_day(birthday[1], possible_birthdays):\n"
        "                return True\n"
        "    return False"
    ]


def _contains_unique_day_return(node, ctx):
    return isinstance(node, ast.Return) and ctx.parent(node) is not None and isinstance(ctx.parent(node), ast.FunctionDef) and ctx.parent(node).name == "contains_unique_day"


def _replace_return_false(node, ctx):
    return ["return False"]


def _false_name(node, ctx):
    return _is_name(node, "false") or _is_name(node, "true")


def _replace_bool_name(node, ctx):
    return ["False" if ctx.text(node).lower() == "false" else "True"]


def _unique_day_compare_wrong_name(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq) and _is_name(node.comparators[0], "day") and "birthday[1]" in ctx.text(node)


def _unique_month_compare_wrong_name(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq) and _is_name(node.comparators[0], "month") and "birthday[0]" in ctx.text(node)


class Fixer:
    def rules(self):
        return [
            Rewrite(name="unique_day_param_name", match=_has_unique_day_bug, replace=_fix_unique_day_use_date, symptoms=("wrong",)),
            Rewrite(name="unique_month_param_name", match=lambda n, c: isinstance(n, ast.FunctionDef) and n.name == "unique_month", replace=_fix_unique_month_use_month, symptoms=("wrong",)),
            Rewrite(name="contains_unique_day_canonical", match=_contains_unique_day_generic, replace=_replace_contains_unique_day, symptoms=("wrong",)),
            Rewrite(name="contains_unique_day_return", match=_contains_unique_day_return, replace=_replace_return_false, symptoms=("wrong",)),
            Rewrite(name="lowercase_bool_name", match=_false_name, replace=_replace_bool_name, symptoms=("err:NameError", "wrong")),
            Rewrite(name="unique_day_compare_misnamed_var", match=_unique_day_compare_wrong_name, replace=lambda n, c: [ctx.text(n).replace("day", "date")], symptoms=("wrong",)),
            Rewrite(name="unique_month_compare_misnamed_var", match=_unique_month_compare_wrong_name, replace=lambda n, c: [ctx.text(n).replace("day", "month")], symptoms=("wrong",)),
        ]