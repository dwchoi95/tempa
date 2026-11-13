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


def _match_round_rem(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
    )


def _replace_round_rem(node, ctx):
    return [f"{ctx.text(node.args[0].left)} // {ctx.text(node.args[0].right)}"]


def _match_wrong_add2_before_div3(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and ctx.text(node.left).strip().startswith("(")
        and ctx.text(node.right) == "3"
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
    )


def _replace_wrong_add2_before_div3(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _match_mod36_over_3_round(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and isinstance(node.args[0].left, ast.BinOp)
        and isinstance(node.args[0].left.op, ast.BinOp)
    )


def _replace_mod36_over_3_round(node, ctx):
    inner = node.args[0].args[0]
    return [f"({ctx.text(inner.left)} + 1) // 36"]


def _match_feet_from_cm36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and ctx.text(node.right) == "36"
    )


def _replace_feet_from_cm36(node, ctx):
    return [f"({ctx.text(node.left)} + 1) // 36"]


def _match_float_to_int_round(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
    )


def _replace_float_to_int_round(node, ctx):
    return [f"round({ctx.text(node.args[0].left)} / {ctx.text(node.args[0].right)})"]


def _match_print_two_vars(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "print"
        and len(node.args) == 2
    )


def _replace_print_two_vars(node, ctx):
    return [f"print({ctx.text(node.args[0])}, {ctx.text(node.args[1])})"]


def _match_mod3_eq_2(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 2
    )


def _replace_mod3_eq_2(node, ctx):
    return [f"{ctx.text(node.left)} >= 2"]


def _match_bare_round_div3(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and ctx.text(node.args[0].right) == "3"
    )


def _replace_bare_round_div3(node, ctx):
    return [f"({ctx.text(node.args[0].left)} + 1) // 3"]


class Fixer:
    def rules(self):
        return [
            Rewrite("round_division_to_floor_after_bias", _match_round_rem, _replace_round_rem, symptoms=("wrong",)),
            Rewrite("add_two_before_div3_off_by_one", _match_wrong_add2_before_div3, _replace_wrong_add2_before_div3, symptoms=("wrong",)),
            Rewrite("round_nested_quotient_to_biased_ceil36", _match_mod36_over_3_round, _replace_mod36_over_3_round, symptoms=("wrong",)),
            Rewrite("feet_should_be_from_inches_not_cm", _match_feet_from_cm36, _replace_feet_from_cm36, symptoms=("wrong",)),
            Rewrite("use_round_instead_of_int_for_quotient", _match_float_to_int_round, _replace_float_to_int_round, symptoms=("wrong",)),
            Rewrite("print_two_args_with_commas", _match_print_two_vars, _replace_print_two_vars, symptoms=("wrong",)),
            Rewrite("rem_eq_two_should_trigger_round_up", _match_mod3_eq_2, _replace_mod3_eq_2, symptoms=("wrong",)),
            Rewrite("round_div3_should_bias_up_on_two", _match_bare_round_div3, _replace_bare_round_div3, symptoms=("wrong",)),
        ]