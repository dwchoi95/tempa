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


def _is_round_div(node, denom):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "round"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Div)
        and ctx_text_denominator(node.args[0], denom)
    )


def ctx_text_denominator(binop, denom):
    return isinstance(binop.right, ast.Constant) and binop.right.value == denom


def _is_mod(node, value):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Mod)
        and isinstance(node.right, ast.Constant)
        and node.right.value == value
    )


def _is_div(node, value):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Div)
        and isinstance(node.right, ast.Constant)
        and node.right.value == value
    )


def _const_int(node, value):
    return isinstance(node, ast.Constant) and node.value == value


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="round_cm_to_inches_then_split_feet",
                match=self._match_round_inches_then_feet,
                replace=self._replace_round_inches_then_feet,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="divide_by_36_should_divide_by_3",
                match=self._match_div36_to_div3,
                replace=self._replace_div36_to_div3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="off_by_one_round_up_two_centimeters",
                match=self._match_add2_before_div3,
                replace=self._replace_add1_before_div3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_remainder_half_up",
                match=self._match_round_remainder_half_up,
                replace=self._replace_round_remainder_half_up,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="feet_from_inches_then_remainder",
                match=self._match_feet_from_inches,
                replace=self._replace_feet_from_inches,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="ceil_integer_result_to_int",
                match=self._match_ceil_print_float,
                replace=self._replace_ceil_print_float,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_compare_two_not_one",
                match=self._match_eq_one_in_rounding,
                replace=self._replace_eq_one_in_rounding,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="add_missing_foot_carry",
                match=self._match_missing_carry,
                replace=self._replace_missing_carry,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="use_round_before_split",
                match=self._match_simple_round_inches,
                replace=self._replace_simple_round_inches,
                symptoms=("wrong",),
            ),
        ]

    def _match_round_inches_then_feet(self, node, ctx):
        return (
            isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and isinstance(node.value, ast.BinOp)
            and isinstance(node.value.op, ast.FloorDiv)
            and _is_int_input(node.value.left)
            and _const_int(node.value.right, 36)
        )

    def _replace_round_inches_then_feet(self, node, ctx):
        return [f"{ctx.text(node.targets[0])} = {ctx.text(node.value.left)} // 3"]

    def _match_div36_to_div3(self, node, ctx):
        return (
            isinstance(node, ast.BinOp)
            and isinstance(node.op, ast.FloorDiv)
            and _is_int_input(node.left)
            and _const_int(node.right, 36)
        )

    def _replace_div36_to_div3(self, node, ctx):
        return [f"{ctx.text(node.left)} // 3"]

    def _match_add2_before_div3(self, node, ctx):
        return (
            isinstance(node, ast.BinOp)
            and isinstance(node.op, ast.FloorDiv)
            and isinstance(node.left, ast.BinOp)
            and isinstance(node.left.op, ast.BinOp.__mro__[0])
        )

    def _replace_add1_before_div3(self, node, ctx):
        if (
            isinstance(node.left, ast.BinOp)
            and isinstance(node.left.op, ast.Add)
            and _const_int(node.left.right, 2)
            and _const_int(node.right, 3)
        ):
            return [f"({ctx.text(node.left.left)} + 1) // 3"]
        return []

    def _match_round_remainder_half_up(self, node, ctx):
        return (
            isinstance(node, ast.BinOp)
            and isinstance(node.op, ast.FloorDiv)
            and isinstance(node.left, ast.BinOp)
            and isinstance(node.left.op, ast.Add)
            and _const_int(node.left.right, 1)
            and _const_int(node.right, 3)
        )

    def _replace_round_remainder_half_up(self, node, ctx):
        return [f"({ctx.text(node.left.left)} + 2) // 3"]

    def _match_feet_from_inches(self, node, ctx):
        return (
            isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and isinstance(node.value, ast.BinOp)
            and isinstance(node.value.op, ast.FloorDiv)
            and _is_int_input(node.value.left)
            and _const_int(node.value.right, 36)
        )

    def _replace_feet_from_inches(self, node, ctx):
        return [f"{ctx.text(node.targets[0])} = ({ctx.text(node.value.left)} // 3) // 12"]

    def _match_ceil_print_float(self, node, ctx):
        return (
            isinstance(node, ast.Call)
            and isinstance(node.func, ast.Name)
            and node.func.id == "print"
            and len(node.args) == 1
            and isinstance(node.args[0], ast.BinOp)
            and isinstance(node.args[0].op, ast.Div)
        )

    def _replace_ceil_print_float(self, node, ctx):
        return []

    def _match_eq_one_in_rounding(self, node, ctx):
        return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq) and _const_int(node.comparators[0], 1)

    def _replace_eq_one_in_rounding(self, node, ctx):
        return [f"{ctx.text(node.left)} <= 1"]

    def _match_missing_carry(self, node, ctx):
        return (
            isinstance(node, ast.If)
            and isinstance(node.test, ast.Compare)
            and len(node.test.ops) == 1
            and isinstance(node.test.ops[0], ast.Eq)
            and _const_int(node.test.comparators[0], 12)
        )

    def _replace_missing_carry(self, node, ctx):
        return [
            f"{ctx.text(node)}\nif {ctx.text(node.test.left)} == 12:\n    {ctx.text(node.body[0].targets[0])} += 1\n    {ctx.text(node.body[0].targets[0])} = 0"
        ]

    def _match_simple_round_inches(self, node, ctx):
        return (
            isinstance(node, ast.Assign)
            and len(node.targets) == 1
            and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name)
            and node.value.func.id == "round"
            and len(node.value.args) == 1
        )

    def _replace_simple_round_inches(self, node, ctx):
        return [ctx.text(node)]