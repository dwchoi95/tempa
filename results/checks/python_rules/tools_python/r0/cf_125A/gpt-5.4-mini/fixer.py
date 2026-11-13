from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_int_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
    )


def _is_round_call(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "round"


def _match_plus_two_div3(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 3
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
    )


def _replace_plus_two_div3(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _match_round_div3(node, ctx):
    return _is_round_call(node, ctx) and len(node.args) == 1 and isinstance(node.args[0], ast.BinOp)


def _replace_round_div3(node, ctx):
    arg = node.args[0]
    if isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Div) and isinstance(arg.right, ast.Constant) and arg.right.value == 3:
        return [f"({ctx.text(arg.left)} + 1) // 3"]
    return []


def _match_round_left_over_div3(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 3
    )


def _replace_round_left_over_div3(node, ctx):
    arg = node.args[0]
    return [f"({ctx.text(arg.left)} + 1) // 3"]


def _match_floordiv36_then_mod36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_floordiv36_then_mod36(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.BinOp) and isinstance(parent.op, ast.Mod):
        return [f"({ctx.text(node.left)} // 3)"]
    return [ctx.text(node)]


def _match_mod36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_mod36(node, ctx):
    return [f"({ctx.text(node.left)} % 3)"]


def _match_compare_eq2(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _replace_compare_eq2(node, ctx):
    return [f"{ctx.text(node.left)} >= 2"]


def _match_compare_ge18(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.GtE)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 18
    )


def _replace_compare_ge18(node, ctx):
    return [f"{ctx.text(node.left)} >= 18"]


def _match_div36_input_plus1(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
    )


def _replace_div36_input_plus1(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 36"]


def _match_float_input(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float" and len(node.args) == 1


def _replace_float_input(node, ctx):
    return [f"int({ctx.text(node.args[0])})"]


def _match_print_float_div(node, ctx):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "print"


def _replace_print_float_div(node, ctx):
    return []


def _match_round_modf_like(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
    )


def _replace_round_modf_like(node, ctx):
    arg = node.args[0]
    if isinstance(arg.right, ast.Constant) and arg.right.value == 3:
        return [f"({ctx.text(arg.left)} + 1) // 3"]
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="round_up_2_over_3_to_1_over_3", match=_match_plus_two_div3, replace=_replace_plus_two_div3, symptoms=("wrong",)),
            Rewrite(name="round_div3_to_add_one", match=_match_round_div3, replace=_replace_round_div3, symptoms=("wrong",)),
            Rewrite(name="round_call_div3_to_integer_round_up", match=_match_round_left_over_div3, replace=_replace_round_left_over_div3, symptoms=("wrong",)),
            Rewrite(name="use_inches_before_feet_not_feet_before_inches", match=_match_floordiv36_then_mod36, replace=_replace_floordiv36_then_mod36, symptoms=("wrong",)),
            Rewrite(name="replace_mod36_with_mod3", match=_match_mod36, replace=_replace_mod36, symptoms=("wrong",)),
            Rewrite(name="eq_2_should_be_ge_2", match=_match_compare_eq2, replace=_replace_compare_eq2, symptoms=("wrong",)),
            Rewrite(name="ge_18_is_not_the_rounding_threshold_here", match=_match_compare_ge18, replace=_replace_compare_ge18, symptoms=("wrong",)),
            Rewrite(name="fix_plus_two_over_36_to_plus_one_over_36", match=_match_div36_input_plus1, replace=_replace_div36_input_plus1, symptoms=("wrong",)),
            Rewrite(name="input_should_be_integer_not_float", match=_match_float_input, replace=_replace_float_input, symptoms=("wrong", "err:ValueError")),
        ]