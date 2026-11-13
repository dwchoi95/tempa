from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and not node.args
        and not node.keywords
    )


def _is_int_input(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and _is_input_call(node.args[0])
    )


def _is_total_inches_pattern(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.FloorDiv)
    )


def _replace_rounding_floordiv(node, ctx):
    left = ctx.text(node.value.left)
    right = ctx.text(node.value.right)
    if right == "3":
        return [f"({left} + 1) // 3"]
    if right == "12":
        return [f"({left} + 6) // 12"]
    return []


def _match_bad_print_division(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.BinOp)
        and isinstance(node.value.args[0].op, ast.Add)
        and isinstance(node.value.args[0].right, ast.BinOp)
        and isinstance(node.value.args[0].right.op, ast.Div)
    )


def _replace_bad_print_division(node, ctx):
    return ["print(({} )//36, ({} )%36//3)".format(ctx.text(node.value.args[0].left), ctx.text(node.value.args[0].left))]


def _match_round_leftover_inches(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "round"
        and len(node.value.args) == 1
    )


def _replace_round_leftover_inches(node, ctx):
    arg = node.value.args[0]
    txt = ctx.text(arg)
    return [f"round({txt})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="round_cm_to_inches_before_feet",
                match=lambda n, c: (
                    isinstance(n, ast.Assign)
                    and len(n.targets) == 1
                    and isinstance(n.targets[0], ast.Name)
                    and isinstance(n.value, ast.BinOp)
                    and isinstance(n.value.op, ast.FloorDiv)
                    and isinstance(n.value.left, ast.BinOp)
                    and isinstance(n.value.left.op, ast.Name)
                ),
                replace=lambda n, c: [],
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_n_div_36_to_inches_plus_rounding",
                match=lambda n, c: (
                    isinstance(n, ast.Assign)
                    and len(n.targets) == 1
                    and isinstance(n.targets[0], ast.Name)
                    and isinstance(n.value, ast.BinOp)
                    and isinstance(n.value.op, ast.FloorDiv)
                    and isinstance(n.value.right, ast.Constant)
                    and n.value.right.value in (3, 12)
                ),
                replace=_replace_rounding_floordiv,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_division_print_to_integer_decomposition",
                match=_match_bad_print_division,
                replace=lambda n, c: [
                    "print(({} + 1)//36, ({} + 1)//3)".format(
                        ctx.text(n.value.args[0].left), ctx.text(n.value.args[0].left)
                    )
                ],
                symptoms=("wrong",),
            ),
        ]