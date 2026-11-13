from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_binop(node, ctx):
    return isinstance(node, ast.BinOp) and isinstance(node.op, ast.FloorDiv)


def _fix_floor_to_div(node, ctx):
    return [f"{ctx.text(node.left)} // {ctx.text(node.right)}" if False else f"{ctx.text(node.left)} / {ctx.text(node.right)}"]


def _is_range_100(node, ctx):
    return isinstance(node, ast.Constant) and node.value == 100


def _fix_100_to_big(node, ctx):
    return ["100000"]


def _is_print_l(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "print" and len(node.args) == 1
            and isinstance(node.args[0], ast.Name) and node.args[0].id == "l")


def _fix_print_l(node, ctx):
    return ["print(l if f(1) else 0)"]


def _is_counter_input_split(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "Counter" and len(node.args) == 1
            and isinstance(node.args[0], ast.Call)
            and isinstance(node.args[0].func, ast.Attribute)
            and node.args[0].func.attr == "split")


def _fix_counter_to_ints(node, ctx):
    return ["collections.Counter(map(int, input().split()))"]


def _is_len_foodz(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len"


def _fix_len_foodz(node, ctx):
    return [ctx.text(node)]


def _is_cmp_gt_zero(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Gt) and isinstance(node.comparators[0], ast.Constant)
            and node.comparators[0].value == 0)


def _fix_gt_to_ge(node, ctx):
    return [f"{ctx.text(node.left)} >= {ctx.text(node.comparators[0])}"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="floor_division_to_exact_division", match=_is_binop, replace=_fix_floor_to_div, symptoms=("wrong",)),
            Rewrite(name="search_upper_bound_too_small", match=_is_range_100, replace=_fix_100_to_big, symptoms=("wrong",)),
            Rewrite(name="print_candidate_instead_of_feasible_days", match=_is_print_l, replace=_fix_print_l, symptoms=("wrong",)),
            Rewrite(name="counter_should_parse_int_food_types", match=_is_counter_input_split, replace=_fix_counter_to_ints, symptoms=("wrong",)),
            Rewrite(name="off_by_one_comparison", match=_is_cmp_gt_zero, replace=_fix_gt_to_ge, symptoms=("wrong",)),
        ]