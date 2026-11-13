from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, name):
    return isinstance(node, ast.Name) and node.id == name


def _is_const_str(node, value):
    return isinstance(node, ast.Constant) and node.value == value


def _is_compare_len_le_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and isinstance(node.left, ast.Name)
        and node.left.id in {"count", "counter", "result", "num", "total", "days", "months", "days_in_month"}
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_len_le_1(node, ctx):
    left = ctx.text(node.left)
    right = ctx.text(node.comparators[0])
    return [left + " == " + right]


def _is_compare_count_gt_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Gt)
        and isinstance(node.left, ast.Name)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_gt_1_to_eq_1(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


def _is_compare_count_ge_2(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _fix_ge_2_to_eq_1(node, ctx):
    return [ctx.text(node.left) + " == 1"]


def _is_compare_count_lt_eq_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_lte_1_to_eq_1(node, ctx):
    return [ctx.text(node.left) + " == 1"]


def _is_true_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value is True


def _fix_true_return(node, ctx):
    return ["return False"]


def _is_false_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value is False


def _fix_false_return(node, ctx):
    return ["return True"]


def _is_bad_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _fix_return_false(node, ctx):
    return ["return False"]


def _is_call_name(node, name):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == name


def _fix_unique_date_to_unique_day(node, ctx):
    return ["unique_day(" + ", ".join(ctx.text(a) for a in node.args) + ")"]


def _match_unique_date_call(node, ctx):
    return _is_call_name(node, "unique_date")


def _match_day_var_vs_date_param(node, ctx):
    return isinstance(node, ast.Name) and node.id == "day"


def _fix_day_to_date(node, ctx):
    return ["date"]


def _match_date_var_vs_day_param(node, ctx):
    return isinstance(node, ast.Name) and node.id == "date"


def _fix_date_to_day(node, ctx):
    return ["day"]


def _match_false_literal(node, ctx):
    return isinstance(node, ast.Constant) and node.value is False


def _fix_false_to_true(node, ctx):
    return ["True"]


def _match_true_literal(node, ctx):
    return isinstance(node, ast.Constant) and node.value is True


def _fix_true_to_false(node, ctx):
    return ["False"]


def _match_wrong_month_index(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.slice, ast.Constant)
        and node.slice.value == 1
        and isinstance(node.value, ast.Name)
    )


def _fix_month_index(node, ctx):
    return [ctx.text(node.value) + "[0]"]


def _match_wrong_day_index(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.slice, ast.Constant)
        and node.slice.value == 0
        and isinstance(node.value, ast.Name)
    )


def _fix_day_index(node, ctx):
    return [ctx.text(node.value) + "[1]"]


def _match_count_lt_2(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Lt)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _fix_lt_2_to_eq_1(node, ctx):
    return [ctx.text(node.left) + " == 1"]


def _match_count_lte_1(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.LtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 1
    )


def _fix_count_lte_1_to_eq_1(node, ctx):
    return [ctx.text(node.left) + " == 1"]


class Fixer:
    def rules(self):
        return [
            Rewrite("count_leq_one_to_eq_one", _is_compare_len_le_1, _fix_len_le_1, ("wrong",)),
            Rewrite("count_gt_one_to_eq_one", _is_compare_count_gt_1, _fix_gt_1_to_eq_1, ("wrong",)),
            Rewrite("count_ge_two_to_eq_one", _is_compare_count_ge_2, _fix_ge_2_to_eq_1, ("wrong",)),
            Rewrite("count_lte_one_to_eq_one", _is_compare_count_lt_eq_1, _fix_lte_1_to_eq_1, ("wrong",)),
            Rewrite("true_return_to_false", _is_true_return, _fix_true_return, ("wrong",)),
            Rewrite("false_return_to_true", _is_false_return, _fix_false_return, ("wrong",)),
            Rewrite("return_none_to_false", _is_bad_return_none, _fix_return_false, ("wrong",)),
            Rewrite("unique_date_call_to_unique_day", _match_unique_date_call, _fix_unique_date_to_unique_day, ("wrong",)),
            Rewrite("day_name_to_date", _match_day_var_vs_date_param, _fix_day_to_date, ("wrong",)),
            Rewrite("date_name_to_day", _match_date_var_vs_day_param, _fix_date_to_day, ("wrong",)),
            Rewrite("false_literal_to_true", _match_false_literal, _fix_false_to_true, ("wrong",)),
            Rewrite("true_literal_to_false", _match_true_literal, _fix_true_to_false, ("wrong",)),
            Rewrite("wrong_month_index_to_zero", _match_wrong_month_index, _fix_month_index, ("wrong",)),
            Rewrite("wrong_day_index_to_one", _match_wrong_day_index, _fix_day_index, ("wrong",)),
            Rewrite("count_lt_two_to_eq_one", _match_count_lt_2, _fix_lt_2_to_eq_1, ("wrong",)),
            Rewrite("count_lte_one_to_eq_one_2", _match_count_lte_1, _fix_count_lte_1_to_eq_1, ("wrong",)),
        ]