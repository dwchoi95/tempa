from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_print_two_args_commas(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 2
    )


def _fix_print_two_args_commas(node, ctx):
    return [f"print({ctx.text(node.value.args[0])}, {ctx.text(node.value.args[1])})"]


def _is_round_division_to_inches(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"round", "ceil"}
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
    )


def _fix_round_division_to_inches(node, ctx):
    left = ctx.text(node.args[0].left)
    right = ctx.text(node.args[0].right)
    return [f"(({left}) + 1) // ({right})"]


def _is_floor36_then_mod3(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.FloorDiv)
        and ctx.text(node.value.right) == "36"
    )


def _fix_floor36_then_mod3(node, ctx):
    return [f"{ctx.text(node.targets[0])} = {ctx.text(node.value.left)} // 3"]


def _is_mod36(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Mod)
        and ctx.text(node.value.right) == "36"
    )


def _fix_mod36(node, ctx):
    return [f"{ctx.text(node.targets[0])} = {ctx.text(node.value.left)} % 3"]


def _is_add1_to_input_before_div(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and ctx.text(node.left.right) == "2"
        and ctx.text(node.right) == "3"
    )


def _fix_add1_to_input_before_div(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _is_n_over36_plus_fmod3(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.FloorDiv)
        and ctx.text(node.left.right) == "36"
        and isinstance(node.right, ast.BinOp)
        and isinstance(node.right.op, ast.Div)
    )


def _fix_n_over36_plus_fmod3(node, ctx):
    return [f"(({ctx.text(node.left.left)}) + 1) // 36"]


def _is_print_float_sum(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.BinOp)
        and isinstance(node.value.args[0].op, ast.Add)
    )


def _fix_print_float_sum(node, ctx):
    return [f"print({ctx.text(node.value.args[0].left)}, {ctx.text(node.value.args[0].right)})"]


def _is_wrong_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _fix_wrong_return_none(node, ctx):
    return ["return 0"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="print_two_args_with_commas",
                match=_is_print_two_args_commas,
                replace=_fix_print_two_args_commas,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_division_to_inches",
                match=_is_round_division_to_inches,
                replace=_fix_round_division_to_inches,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_inch_conversion_before_feet",
                match=_is_floor36_then_mod3,
                replace=_fix_floor36_then_mod3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_remainder_modulus",
                match=_is_mod36,
                replace=_fix_mod36,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="add_one_before_rounding_div3",
                match=_is_add1_to_input_before_div,
                replace=_fix_add1_to_input_before_div,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="add_one_to_full_inches_total",
                match=_is_n_over36_plus_fmod3,
                replace=_fix_n_over36_plus_fmod3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_two_values_instead_of_sum",
                match=_is_print_float_sum,
                replace=_fix_print_float_sum,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="non_void_return_placeholder",
                match=_is_wrong_return_none,
                replace=_fix_wrong_return_none,
                symptoms=("wrong",),
            ),
        ]