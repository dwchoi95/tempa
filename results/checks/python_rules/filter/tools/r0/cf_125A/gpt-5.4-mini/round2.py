from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_print_two_args(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "print"
        and len(node.args) == 2
        and not node.keywords
    )


def _fix_print_two_args(node, ctx):
    return [f"print({ctx.text(node.args[0])}, {ctx.text(node.args[1])})"]


def _is_round_inch_from_cm(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.left, ast.Call)
        and isinstance(node.left.left.func, ast.Name)
        and node.left.left.func.id == "int"
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
        and isinstance(node.right, ast.Constant)
        and node.right.value == 3
    )


def _fix_round_inch_from_cm(node, ctx):
    return [f"({ctx.text(node.left.left.args[0])} + 1) // 3"]


def _is_round_div3_by_2(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.FloorDiv)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 3
        and isinstance(node.right, ast.Constant)
        and node.right.value == 6
    )


def _fix_round_div3_by_2(node, ctx):
    return [f"{ctx.text(node.left.left)} // 36"]


def _is_round_div3_plus2(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.right, ast.Constant)
        and node.left.right.value == 2
        and isinstance(node.right, ast.Constant)
        and node.right.value == 3
    )


def _fix_round_div3_plus2(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _is_wrong_ceil_div3(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "ceil"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
    )


def _fix_wrong_ceil_div3(node, ctx):
    expr = node.args[0]
    return [f"round({ctx.text(expr.left)}/{ctx.text(expr.right)})"]


def _is_wrong_round_div3(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
    )


def _fix_wrong_round_div3(node, ctx):
    expr = node.args[0]
    return [f"round({ctx.text(expr.left)}/{ctx.text(expr.right)})"]


def _is_bad_print_expr(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.BinOp)
        and isinstance(node.value.args[0].op, ast.Add)
    )


def _fix_bad_print_expr(node, ctx):
    return [f"print({ctx.text(node.value.args[0].left)}, {ctx.text(node.value.args[0].right)})"]


def _is_bad_output_join(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "print"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Add)
        and any(isinstance(x, ast.Call) and isinstance(x.func, ast.Name) and x.func.id in {"str", "int"} for x in ast.walk(node.args[0]))
    )


def _fix_bad_output_join(node, ctx):
    return [f"print({ctx.text(node.args[0].left)}, {ctx.text(node.args[0].right)})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="print_two_args_with_commas",
                match=_is_print_two_args,
                replace=_fix_print_two_args,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="add_one_for_rounding_cm_to_inches",
                match=_is_round_inch_from_cm,
                replace=_fix_round_inch_from_cm,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_ceil_offset_for_feet",
                match=_is_round_div3_by_2,
                replace=_fix_round_div3_by_2,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_plus_two_rounding",
                match=_is_round_div3_plus2,
                replace=_fix_round_div3_plus2,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="ceil_should_be_round_for_inches",
                match=_is_wrong_ceil_div3,
                replace=_fix_wrong_ceil_div3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_division_to_inches",
                match=_is_wrong_round_div3,
                replace=_fix_wrong_round_div3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_sum_should_be_two_values",
                match=_is_bad_print_expr,
                replace=_fix_bad_print_expr,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="bad_output_concat_to_print_args",
                match=_is_bad_output_join,
                replace=_fix_bad_output_join,
                symptoms=("wrong",),
            ),
        ]