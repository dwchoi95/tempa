from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_func(node, name):
    return isinstance(node, ast.FunctionDef) and node.name == name


def _is_name(node, s):
    return isinstance(node, ast.Name) and node.id == s


def _is_const(node, v):
    return isinstance(node, ast.Constant) and node.value == v


def _first_arg_name(func):
    return func.args.args[0].arg if func.args.args else None


def _second_arg_name(func):
    return func.args.args[1].arg if len(func.args.args) > 1 else None


def _body_has_return_true(func):
    return any(isinstance(s, ast.Return) and _is_const(s.value, True) for s in func.body)


def _body_has_return_false(func):
    return any(isinstance(s, ast.Return) and _is_const(s.value, False) for s in func.body)


class Fixer:
    def rules(self):
        rules = []

        def match_day_name(node, ctx):
            return isinstance(node, ast.Name) and node.id == "day"

        def repl_day_name(node, ctx):
            return [ctx.text(node)]

        rules.append(Rewrite(
            name="day_name_in_unique_day",
            match=match_day_name,
            replace=repl_day_name,
            symptoms=("wrong", "err:NameError"),
        ))

        def match_month_name(node, ctx):
            return isinstance(node, ast.Name) and node.id == "days"

        def repl_month_name(node, ctx):
            return [ctx.text(node)]

        rules.append(Rewrite(
            name="days_name_in_unique_month",
            match=match_month_name,
            replace=repl_month_name,
            symptoms=("wrong", "err:NameError"),
        ))

        def match_counter_name(node, ctx):
            return isinstance(node, ast.Name) and node.id in {"count", "days", "months"} and isinstance(ctx.parent(node), ast.Assign)

        def repl_counter_name(node, ctx):
            return [ctx.text(node)]

        rules.append(Rewrite(
            name="counter_assignment_name_preserve",
            match=match_counter_name,
            replace=repl_counter_name,
            symptoms=("wrong",),
        ))

        def match_le(node, ctx):
            return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE)

        def repl_le(node, ctx):
            return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]

        rules.append(Rewrite(
            name="lte_should_be_eq",
            match=match_le,
            replace=repl_le,
            symptoms=("wrong",),
        ))

        def match_unique_count_return(node, ctx):
            return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)

        def repl_unique_count_return(node, ctx):
            return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]

        rules.append(Rewrite(
            name="gt_should_be_eq",
            match=match_unique_count_return,
            replace=repl_unique_count_return,
            symptoms=("wrong",),
        ))

        def match_bare_return(node, ctx):
            return isinstance(node, ast.Return) and node.value is None and isinstance(ctx.parent(node), ast.FunctionDef)

        def repl_bare_return(node, ctx):
            func = ctx.parent(node)
            if _is_func(func, "contains_unique_day"):
                return [
                    "for " + (_first_arg_name(func) or "x") + " in possible_birthdays:\n"
                    "    if " + (_first_arg_name(func) or "x") + " == " + (_first_arg_name(func) or "x") + "[0]:\n"
                    "        if unique_day(" + (_first_arg_name(func) or "x") + "[1], possible_birthdays):\n"
                    "            return True\n"
                    "return False"
                ]
            return []

        rules.append(Rewrite(
            name="fill_missing_contains_unique_day",
            match=match_bare_return,
            replace=repl_bare_return,
            symptoms=("wrong",),
        ))

        def match_true_false_return(node, ctx):
            return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value in {True, False}

        def repl_true_false_return(node, ctx):
            return [ctx.text(node)]

        rules.append(Rewrite(
            name="preserve_boolean_return",
            match=match_true_false_return,
            replace=repl_true_false_return,
            symptoms=("wrong",),
        ))

        def match_wrong_arg_unique_day(node, ctx):
            return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "unique_day" and len(node.args) == 1

        def repl_wrong_arg_unique_day(node, ctx):
            return [ctx.text(node.func) + "(" + ctx.text(node.args[0]) + ", possible_birthdays)"]

        rules.append(Rewrite(
            name="unique_day_call_uses_existing_arg",
            match=match_wrong_arg_unique_day,
            replace=repl_wrong_arg_unique_day,
            symptoms=("wrong",),
        ))

        def match_wrong_arg_unique_month(node, ctx):
            return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "unique_month" and len(node.args) == 1

        def repl_wrong_arg_unique_month(node, ctx):
            return [ctx.text(node.func) + "(" + ctx.text(node.args[0]) + ", possible_birthdays)"]

        rules.append(Rewrite(
            name="unique_month_call_uses_existing_arg",
            match=match_wrong_arg_unique_month,
            replace=repl_wrong_arg_unique_month,
            symptoms=("wrong",),
        ))

        def match_count_comp(node, ctx):
            return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)

        def repl_count_comp(node, ctx):
            return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]

        rules.append(Rewrite(
            name="lt_should_be_eq_for_uniqueness",
            match=match_count_comp,
            replace=repl_count_comp,
            symptoms=("wrong",),
        ))

        return rules