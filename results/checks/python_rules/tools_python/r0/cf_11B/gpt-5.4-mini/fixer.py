from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_name(node, ctx, s):
    return isinstance(node, ast.Name) and node.id == s


def _is_abs_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "abs"
        and len(node.args) == 1
        and not node.keywords
    )


def _is_input_call(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
        and len(node.args) == 0
        and not node.keywords
    )


def _replace_input_to_abs_int(node, ctx):
    return ["abs(int(input()))"]


def _is_while_not_eq(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and len(node.test.comparators) == 1
    )


def _replace_while_cond_abs_parity(node, ctx):
    if not (isinstance(node, ast.While) and isinstance(node.test, ast.Compare)):
        return []
    left = ctx.text(node.test.left)
    right = ctx.text(node.test.comparators[0])
    return [f"while {left} < {right} or ({left}-{right}) % 2 != 0:"]


def _is_parity_while(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 2
    )


def _replace_old_loop(node, ctx):
    return [
        "x = abs(int(input()))\n"
        "jumps = 0\n"
        "pos = 0\n"
        "while pos < x or (pos-x) % 2 != 0:\n"
        "    jumps += 1\n"
        "    pos += jumps\n"
        "print(jumps)"
    ]


def _is_bad_input_print(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and _is_name(node.targets[0], ctx, "x")
        and _is_input_call(node.value, ctx)
    )


def _replace_input_print(node, ctx):
    return ["x = abs(int(input()))"]


def _is_simple_print_name(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
    )


def _replace_print_name(node, ctx):
    arg = ctx.text(node.value.args[0])
    return [f"print({arg})"]


def _is_while_eq_zero(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
        and len(node.test.comparators) == 1
        and isinstance(node.test.comparators[0], ast.Name)
    )


def _replace_while_eq_zero(node, ctx):
    return [f"while {ctx.text(node.test.left)} != {ctx.text(node.test.comparators[0])}:"]


def _is_bad_sum_formula(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Lt, ast.LtE, ast.Gt, ast.GtE))
        and isinstance(node.left, ast.BinOp)
    )


def _replace_bad_compare(node, ctx):
    return [ctx.text(node)]


def _is_minimal_jump_loop(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.BoolOp)
    )


def _replace_minimal_jump_loop(node, ctx):
    return [ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="wrap_input_in_abs_int",
                match=_is_bad_input_print,
                replace=_replace_input_print,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="replace_print_of_raw_input",
                match=_is_simple_print_name,
                replace=_replace_print_name,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="while_not_equal_to_parity_loop",
                match=_is_while_not_eq,
                replace=_replace_while_cond_abs_parity,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_old_jump_solution_shape",
                match=_is_parity_while,
                replace=_replace_old_loop,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="generic_abs_input_assignment",
                match=_is_bad_input_print,
                replace=_replace_input_print,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="generic_while_ne_condition",
                match=_is_while_eq_zero,
                replace=_replace_while_eq_zero,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="comparison_keep_structure",
                match=_is_bad_sum_formula,
                replace=_replace_bad_compare,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="keep_minimal_loop",
                match=_is_minimal_jump_loop,
                replace=_replace_minimal_jump_loop,
                symptoms=("wrong",),
            ),
        ]