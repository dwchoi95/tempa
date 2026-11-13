from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_stmt(node):
    return isinstance(node, ast.stmt)


def _is_expr(node):
    return isinstance(node, ast.expr)


def _const_int(node, value=None):
    if not isinstance(node, ast.Constant) or not isinstance(node.value, int):
        return False
    return value is None or node.value == value


def _input_int(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
    )


def _is_div(node, left_name=None, right_const=None):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.FloorDiv)
        and isinstance(node.left, ast.Name)
        and (left_name is None or node.left.id == left_name)
        and _const_int(node.right, right_const)
    )


def _is_mod(node, left_name=None, right_const=None):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.left, ast.Name)
        and (left_name is None or node.left.id == left_name)
        and _const_int(node.right, right_const)
    )


def _replace_input_int(node, ctx):
    return ["int(input())"]


def _replace_div36_to_div3(node, ctx):
    return [f"{ctx.text(node.left)} // 3"]


def _replace_div36_to_inches_plus_rounding(node, ctx):
    return [f"{ctx.text(node.left)} // 3"]


def _replace_round_division_print_to_integer_decomposition(node, ctx):
    return [f"round({ctx.text(node.args[0].args[0].left)}/3)"]


def _replace_plus2_to_plus1(node, ctx):
    return [f"{ctx.text(node.left)} + 1"]


def _replace_plus6_to_plus1(node, ctx):
    return [f"{ctx.text(node.left)} + 1"]


def _replace_floor36_to_floor3(node, ctx):
    return [f"{ctx.text(node.left)} // 3"]


def _replace_mod36_to_mod3(node, ctx):
    return [f"{ctx.text(node.left)} % 3"]


def _replace_round_to_divmod_style(node, ctx):
    return [f"{ctx.text(node.left)} // 3"]


def _replace_float_round_inches(node, ctx):
    return [f"int({ctx.text(node.left)} / 3 + 0.5)"]


def _replace_float_round_feet(node, ctx):
    return [f"int({ctx.text(node.left)} / 36 + 0.5)"]


def _replace_ceil_div3(node, ctx):
    return [f"int({ctx.text(node.left)} // 3)"]


def _replace_wrong_mod26(node, ctx):
    return [f"{ctx.text(node.left)} % 36"]


def _replace_compare_ge_18(node, ctx):
    return [f"{ctx.text(node.left)} >= 2"]


def _replace_compare_ge_2(node, ctx):
    return [f"{ctx.text(node.left)} == 2"]


def _replace_print_one_arg_to_two(node, ctx):
    return [f"print({ctx.text(node.args[0])} // 12, {ctx.text(node.args[0])} % 12)"]


def _replace_print_float_expr(node, ctx):
    return [f"print({ctx.text(node.values[0].left)}//36, int(({ctx.text(node.values[0].values[0].left)}%36)/3))"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="input_int_call_identity",
                match=lambda n, c: _input_int(n),
                replace=_replace_input_int,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="div36_used_for_inches_should_be_div3",
                match=lambda n, c: _is_div(n, right_const=36),
                replace=_replace_div36_to_div3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="mod36_used_for_inches_should_be_mod3",
                match=lambda n, c: _is_mod(n, right_const=36),
                replace=_replace_mod36_to_mod3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="off_by_one_add_two_should_add_one",
                match=lambda n, c: isinstance(n, ast.BinOp)
                and isinstance(n.op, ast.Add)
                and _const_int(n.right, 2),
                replace=_replace_plus2_to_plus1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="off_by_one_add_six_should_add_one",
                match=lambda n, c: isinstance(n, ast.BinOp)
                and isinstance(n.op, ast.Add)
                and _const_int(n.right, 6),
                replace=_replace_plus6_to_plus1,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="float_rounded_inches_should_use_div3",
                match=lambda n, c: isinstance(n, ast.BinOp)
                and isinstance(n.op, ast.Div)
                and _const_int(n.right, 3),
                replace=_replace_float_round_inches,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="float_rounded_feet_should_use_div36",
                match=lambda n, c: isinstance(n, ast.BinOp)
                and isinstance(n.op, ast.Div)
                and _const_int(n.right, 36),
                replace=_replace_float_round_feet,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="ceil_on_inches_should_be_floor",
                match=lambda n, c: isinstance(n, ast.Call)
                and isinstance(n.func, ast.Name)
                and n.func.id in {"ceil", "ceiling"}
                and len(n.args) == 1,
                replace=_replace_ceil_div3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_mod26_should_be_mod36",
                match=lambda n, c: _const_int(n, 26),
                replace=_replace_wrong_mod26,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_ge_18_should_be_compare_remainder_2",
                match=lambda n, c: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], ast.GtE)
                and _const_int(n.comparators[0], 18),
                replace=_replace_compare_ge_18,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="compare_ge_2_should_be_eq_2",
                match=lambda n, c: isinstance(n, ast.Compare)
                and len(n.ops) == 1
                and isinstance(n.ops[0], ast.GtE)
                and _const_int(n.comparators[0], 2),
                replace=_replace_compare_ge_2,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_single_quantity_should_split_into_feet_and_inches",
                match=lambda n, c: isinstance(n, ast.Expr)
                and isinstance(n.value, ast.Call)
                and isinstance(n.value.func, ast.Name)
                and n.value.func.id == "print"
                and len(n.value.args) == 1
                and isinstance(n.value.args[0], ast.BinOp)
                and isinstance(n.value.args[0].op, ast.Add),
                replace=lambda n, c: [f"print({ctx.text(n.value.args[0].left)}//12, {ctx.text(n.value.args[0].left)}%12)"],
                symptoms=("wrong",),
            ),
        ]