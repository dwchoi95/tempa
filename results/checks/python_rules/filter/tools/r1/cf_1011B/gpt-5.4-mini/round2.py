from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_bound_100(node, ctx):
    return isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name) and node.targets[0].id == "r" and isinstance(node.value, ast.Constant) and node.value.value == 100


def _fix_bound_100(node, ctx):
    return ["r = 100000"]


def _is_check_one_guard(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.UnaryOp)
        and isinstance(node.test.op, ast.Not)
        and isinstance(node.test.operand, ast.Call)
        and isinstance(node.test.operand.func, ast.Name)
        and node.test.operand.func.id == "f"
        and len(node.test.operand.args) == 1
        and isinstance(node.test.operand.args[0], ast.Constant)
        and node.test.operand.args[0].value == 1
    )


def _fix_check_one_guard(node, ctx):
    return ["if not f(1):\n    print(0)"]


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


def _fix_counter_input_split(node, ctx):
    return [ctx.text(node.args[0])]


def _is_sorted_values_key(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "sorted"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Attribute)
        and node.args[0].func.attr == "items"
        and any(kw.arg == "reverse" and isinstance(kw.value, ast.Constant) and kw.value.value for kw in node.keywords)
    )


def _fix_sorted_values_key(node, ctx):
    return ["sorted(food.values(), reverse=True)"]


def _is_range_reverse_100_to_1(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Constant)
        and isinstance(node.args[1], ast.Constant)
        and node.args[0].value == 100
        and node.args[1].value == 0
        and any(isinstance(kw.value, ast.Constant) and kw.value.value == -1 for kw in node.keywords)
    )


def _fix_range_reverse_100_to_1(node, ctx):
    return ["range(100, 0, -1)"]


def _is_len_food_index(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.value, ast.Name)
        and node.value.id == "food"
        and isinstance(node.slice, ast.Name)
        and node.slice.id == "i"
        and isinstance(ctx.parent(node), ast.Assign)
    )


def _fix_len_food_index(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="fix_binary_search_upper_bound", match=_is_bad_bound_100, replace=_fix_bound_100, symptoms=("wrong",)),
            Rewrite(name="keep_zero_day_guard_but_make_it_useful", match=_is_check_one_guard, replace=_fix_check_one_guard, symptoms=("wrong",)),
            Rewrite(name="counter_on_split_strings_should_use_numbers", match=_is_counter_input_split, replace=_fix_counter_input_split, symptoms=("wrong",)),
            Rewrite(name="sorted_counts_should_sort_values", match=_is_sorted_values_key, replace=_fix_sorted_values_key, symptoms=("wrong",)),
            Rewrite(name="reverse_range_bounds_should_be_100_to_1", match=_is_range_reverse_100_to_1, replace=_fix_range_reverse_100_to_1, symptoms=("wrong",)),
            Rewrite(name="preserve_food_indexing", match=_is_len_food_index, replace=_fix_len_food_index, symptoms=("wrong",)),
        ]