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


def _match_add_one_before_div36(node, ctx):
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


def _replace_add_one_before_div36(node, ctx):
    return [f"({ctx.text(node.left.left)} + 1) // 3"]


def _match_add_one_before_div36_stmt(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value, ast.FloorDiv)
        and isinstance(node.value.left, ast.BinOp)
        and isinstance(node.value.left.op, ast.Add)
        and isinstance(node.value.left.right, ast.Constant)
        and node.value.left.right.value == 2
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 3
    )


def _replace_add_one_before_div36_stmt(node, ctx):
    return [f"{ctx.text(node.targets[0])} = ({ctx.text(node.value.left.left)} + 1) // 3"]


def _match_round_div3_to_round_div3_then_split(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.FloorDiv)
        and isinstance(node.value.left, ast.BinOp)
        and isinstance(node.value.left.op, ast.Add)
        and isinstance(node.value.left.right, ast.Constant)
        and node.value.left.right.value == 1
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 3
    )


def _replace_round_div3_to_round_div3_then_split(node, ctx):
    return [f"{ctx.text(node.targets[0])} = {ctx.text(node.value.left.left)} // 3"]


def _match_bad_feet_first(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.FloorDiv)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 36
    )


def _replace_bad_feet_first(node, ctx):
    return [f"{ctx.text(node.targets[0])} = {ctx.text(node.value.left)} // 3"]


def _match_bad_remainder36_to_mod3(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Mod)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 36
    )


def _replace_bad_remainder36_to_mod3(node, ctx):
    return [f"{ctx.text(node.targets[0])} = {ctx.text(node.value.left)} % 3"]


def _match_round_leftover_inches(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "round"
    )


def _replace_round_leftover_inches(node, ctx):
    return [f"{ctx.text(node.targets[0])} = ({ctx.text(node.value.args[0].left)} + 1) // 3"]


def _match_round_overall_inches(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "round"
        and len(node.value.args) == 1
    )


def _replace_round_overall_inches(node, ctx):
    return [f"{ctx.text(node.targets[0])} = round({ctx.text(node.value.args[0])})"]


def _match_print_single_value(node, ctx):
    return isinstance(node, ast.Print) if hasattr(ast, "Print") else False


def _match_bad_print_expr(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
    )


def _replace_bad_print_expr(node, ctx):
    return [f"print({ctx.text(node.value.args[0])}, 0)"]


def _match_bad_input_prompt(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Constant)
    )


def _replace_bad_input_prompt(node, ctx):
    return ["input()"]


def _match_increment_if_2(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.Eq)
        and isinstance(node.test.comparators[0], ast.Constant)
        and node.test.comparators[0].value == 2
    )


def _replace_increment_if_2(node, ctx):
    return [ctx.text(node).replace("== 2", ">= 2")]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="add_one_before_div3",
                match=_match_add_one_before_div36,
                replace=_replace_add_one_before_div36,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="add_one_before_div3_stmt",
                match=_match_add_one_before_div36_stmt,
                replace=_replace_add_one_before_div36_stmt,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_div3_then_split",
                match=_match_round_div3_to_round_div3_then_split,
                replace=_replace_round_div3_to_round_div3_then_split,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="feet_should_use_div3_not_div36",
                match=_match_bad_feet_first,
                replace=_replace_bad_feet_first,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="remainder_should_be_mod3_not_mod36",
                match=_match_bad_remainder36_to_mod3,
                replace=_replace_bad_remainder36_to_mod3,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_leftover_inches",
                match=_match_round_leftover_inches,
                replace=_replace_round_leftover_inches,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="round_overall_inches",
                match=_match_round_overall_inches,
                replace=_replace_round_overall_inches,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="remove_input_prompt",
                match=_match_bad_input_prompt,
                replace=_replace_bad_input_prompt,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_increment_threshold",
                match=_match_increment_if_2,
                replace=_replace_increment_if_2,
                symptoms=("wrong",),
            ),
        ]