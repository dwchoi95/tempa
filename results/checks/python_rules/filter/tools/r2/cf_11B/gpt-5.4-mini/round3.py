from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_input_to_map(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "map"
        and len(node.args) == 2
        and isinstance(node.args[0], ast.Name)
        and node.args[0].id == "int"
        and isinstance(node.args[1], ast.Call)
        and isinstance(node.args[1].func, ast.Name)
        and node.args[1].func.id == "input"
        and not node.args[1].args
        and not node.args[1].keywords
    )


def _fix_input_to_abs_int(node, ctx):
    return ["abs(int(input()))"]


def _is_bad_print_var(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "print"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
        and node.args[0].id in {"x", "n", "count", "a"}
    )


def _fix_print_var(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.Expr) and ctx.field(node) == "value":
        return []
    return [ctx.text(node)]


def _is_while_not_eq(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
    )


def _fix_while_condition(node, ctx):
    t = node.test
    return [f"while {ctx.text(t.left)} < {ctx.text(t.comparators[0])} or ({ctx.text(t.left)}-{ctx.text(t.comparators[0])}) % 2 != 0:"]


def _is_eq_one_step_condition(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and any(isinstance(op, ast.BinOp) for op in [node.left] + list(node.comparators))
    )


def _fix_eq_to_lt(node, ctx):
    return [f"{ctx.text(node.left)} < {ctx.text(node.comparators[0])}"]


def _is_bad_pos_update(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.Lt)
        and any(
            isinstance(stmt, ast.Assign)
            and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)
            and stmt.targets[0].id == "pos"
            for stmt in node.body + node.orelse
        )
    )


def _fix_pos_update(node, ctx):
    return [f"{ctx.text(node.test.left)} += {ctx.text(node.test.comparators[0])}"]


def _is_bad_triangular_formula(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Div)
        and isinstance(node.left, ast.BinOp)
        and isinstance(node.left.op, ast.Add)
        and isinstance(node.left.left, ast.BinOp)
        and isinstance(node.left.left.op, ast.Mult)
        and isinstance(node.left.left.left, ast.Name)
        and node.left.left.left.id == "n"
    )


def _fix_triangular_formula(node, ctx):
    return ["(n * (n + 1)) // 2"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="input_map_should_be_abs_int_input",
                match=_is_bad_input_to_map,
                replace=_fix_input_to_abs_int,
                symptoms=("err:TypeError", "wrong"),
            ),
            Rewrite(
                name="print_variable_as_result",
                match=_is_bad_print_var,
                replace=_fix_print_var,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="while_not_equal_should_use_parity_progression",
                match=_is_while_not_eq,
                replace=_fix_while_condition,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="equality_stop_condition_should_be_strict_progress",
                match=_is_eq_one_step_condition,
                replace=_fix_eq_to_lt,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="pos_update_should_accumulate_jump",
                match=_is_bad_pos_update,
                replace=_fix_pos_update,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="triangular_number_should_use_integer_division",
                match=_is_bad_triangular_formula,
                replace=_fix_triangular_formula,
                symptoms=("wrong",),
            ),
        ]