from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_binop_with_floor_div(node, ctx):
    return isinstance(node, ast.BinOp) and isinstance(node.op, ast.FloorDiv)


def _fix_floor_div_to_plus(node, ctx):
    return [ctx.text(node.left) + " + " + ctx.text(node.right)]


def _is_counter_input_split(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "Counter"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Attribute)
        and node.args[0].func.attr == "split"
    )


def _fix_counter_to_ints(node, ctx):
    inner = ctx.text(node.args[0].args[0]) if node.args and node.args[0].args else ""
    return [f"collections.Counter(map(int, {inner}.split()))"]


def _is_sorted_items_reverse(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "sorted"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Attribute)
        and node.args[0].func.attr == "items"
    )


def _fix_sorted_items_keep_counts(node, ctx):
    return [ctx.text(node.args[0].func.value) + ".values()"]


def _is_len_of_foodz(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "len"


def _fix_len_foodz_to_100(node, ctx):
    return ["100"]


def _is_assign_food_list(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id == "food"
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Mult)
    )


def _fix_food_list_init(node, ctx):
    return ["food = [0] * 100"]


def _is_range_len_food(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "len"
    )


def _fix_range_to_hundred(node, ctx):
    return ["range(100)"]


def _is_print_prev_days(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "print"


def _fix_print_answer(node, ctx):
    return ["print(ans)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="floor_divisor_used_as_addition_index_count",
                match=_is_binop_with_floor_div,
                replace=_fix_floor_div_to_plus,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="counter_should_parse_ints",
                match=_is_counter_input_split,
                replace=_fix_counter_to_ints,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="sorted_items_should_use_counts_values",
                match=_is_sorted_items_reverse,
                replace=_fix_sorted_items_keep_counts,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="len_of_foodz_should_be_full_type_range",
                match=_is_len_of_food_list if False else _is_len_of_foodz,
                replace=_fix_len_foodz_to_100,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="food_list_should_have_hundred_slots",
                match=_is_assign_food_list,
                replace=_fix_food_list_init,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="range_over_len_food_should_be_100",
                match=_is_range_len_food,
                replace=_fix_range_to_hundred,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_wrong_variable",
                match=_is_print_prev_days,
                replace=_fix_print_answer,
                symptoms=("wrong",),
            ),
        ]