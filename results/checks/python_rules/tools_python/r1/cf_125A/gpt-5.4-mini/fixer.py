from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "input"


def _is_int_input(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and _is_input_call(node.args[0])
    )


def _match_add2_over3(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
        and isinstance(node.right, ast.Constant)
        and node.right.value == 3
        and _is_int_input(node.left.left)
    )


def _replace_add2_over3(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _match_add1_over3(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 1
        and isinstance(node.right, ast.Constant)
        and node.right.value == 3
        and _is_int_input(node.left.left)
    )


def _replace_add1_over3(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _match_div36_then_ceil3(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "ceil"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 3
    )


def _replace_div36_then_ceil3(node, ctx):
    return [f"round({ctx.text(node.args[0].left)}/3)"]


def _match_round_div3_to_round_div3(node, ctx):
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


def _replace_round_div3_to_round_div3(node, ctx):
    return [ctx.text(node)]


def _match_floor36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_floor36(node, ctx):
    return [f"({ctx.text(node.left)} // 3) // 12"]


def _match_mod36(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 36
    )


def _replace_mod36(node, ctx):
    return [f"({ctx.text(node.left)} // 3) % 12"]


def _match_add1_input(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 1
        and _is_int_input(node.left)
    )


def _replace_add1_input(node, ctx):
    return [f"({ctx.text(node.left)} + 2)"]


def _match_div3_then_div12(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.right, ast.Constant)
        and node.right.value == 12
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.FloorDiv)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 3
    )


def _replace_div3_then_div12(node, ctx):
    return [f"{ctx.text(node.left.left)} // 36"]


def _match_print_single(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
    )


def _replace_print_single(node, ctx):
    a = ctx.text(node.value.args[0])
    return [f"print({a} // 12, {a} % 12)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="add_two_before_div3_should_be_add_one",
                match=_match_add2_over3,
                replace=_replace_add2_over3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="add_one_before_div3_kept",
                match=_match_add1_over3,
                replace=_replace_add1_over3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="ceil_div3_on_remainder_should_round",
                match=_match_div36_then_ceil3,
                replace=_replace_div36_then_ceil3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_div3_is_intended",
                match=_match_round_div3_to_round_div3,
                replace=_replace_round_div3_to_round_div3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="divide_by_36_should_be_divide_by_3_then_12",
                match=_match_floor36,
                replace=_replace_floor36,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="mod_36_should_be_mod_12_after_inches",
                match=_match_mod36,
                replace=_replace_mod36,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="add_one_to_input_is_round_up_by_two",
                match=_match_add1_input,
                replace=_replace_add1_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="nested_division_36_simplification",
                match=_match_div3_then_div12,
                replace=_replace_div3_then_div12,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_single_value_should_print_feet_and_inches",
                match=_match_print_single,
                replace=_replace_print_single,
                symptoms=("wrong",),
            ),
        ]