from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_int(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
    )


def _match_add_one_to_input(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and ((isinstance(node.left, ast.Call) and _is_input_int(node.left) and isinstance(node.right, ast.Constant) and node.right.value == 2)
             or (isinstance(node.right, ast.Call) and _is_input_int(node.right) and isinstance(node.left, ast.Constant) and node.left.value == 2))
    )


def _replace_add_one_to_input(node, ctx):
    if isinstance(node.left, ast.Call):
        return [ctx.text(node.left) + " + 1"]
    return ["1 + " + ctx.text(node.right)]


def _match_rounding_add_two(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 2
    )


def _replace_rounding_add_two(node, ctx):
    return [ctx.text(node.left) + " + 1"]


def _match_floor_div_36_then_mod_36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_floor_div_36_then_mod_36(node, ctx):
    return [ctx.text(node.left) + " // 3"]


def _match_mod_36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_mod_36(node, ctx):
    return [ctx.text(node.left) + " % 3"]


def _match_round_over_three(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
    )


def _replace_round_over_three(node, ctx):
    arg = node.args[0]
    return ["(" + ctx.text(arg.left) + " + 1) // " + ctx.text(arg.right)]


def _match_ceil_over_three(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute) is False
        and isinstance(node.func, ast.Name)
        and node.func.id == "ceil"
        and len(node.args) == 1
    )


def _replace_ceil_over_three(node, ctx):
    if isinstance(node.args[0], ast.BinOp) and isinstance(node.args[0].op, ast.Div):
        arg = node.args[0]
        return ["(" + ctx.text(arg.left) + " + 1) // " + ctx.text(arg.right)]
    return []


def _match_wrong_print_tuple(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "print"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
    )


def _replace_wrong_print_tuple(node, ctx):
    return []


def _match_compare_ge_2(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _replace_compare_ge_2(node, ctx):
    return [ctx.text(node.left) + " == 2"]


def _match_mod3_ge_2(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and len(node.comparators) == 1
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Mod)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 3
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _replace_mod3_ge_2(node, ctx):
    return [ctx.text(node.left) + " == 2"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="add_one_not_two_after_input", match=_match_add_one_to_input, replace=_replace_add_one_to_input, symptoms=("wrong",)),
            Rewrite(name="rounding_bias_add_one", match=_match_rounding_add_two, replace=_replace_rounding_add_two, symptoms=("wrong",)),
            Rewrite(name="feet_division_should_use_inches", match=_match_floor_div_36_then_mod_36, replace=_replace_floor_div_36_then_mod_36, symptoms=("wrong",)),
            Rewrite(name="centimeters_mod_should_be_three", match=_match_mod_36, replace=_replace_mod_36, symptoms=("wrong",)),
            Rewrite(name="round_division_to_floor_plus_one", match=_match_round_over_three, replace=_replace_round_over_three, symptoms=("wrong",)),
            Rewrite(name="ceil_over_three_to_rounding", match=_match_ceil_over_three, replace=_replace_ceil_over_three, symptoms=("wrong",)),
            Rewrite(name="compare_ge_two_to_eq_two", match=_match_compare_ge_2, replace=_replace_compare_ge_2, symptoms=("wrong",)),
            Rewrite(name="mod3_ge_two_to_eq_two", match=_match_mod3_ge_2, replace=_replace_mod3_ge_2, symptoms=("wrong",)),
        ]