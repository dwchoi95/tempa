from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_input_call(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "input"
    )


def _is_int_input(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "int"
        and len(node.args) == 1
        and _is_input_call(node.args[0])
    )


def _match_bare_input_assigned_to_x(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
        return False
    return (
        node.targets[0].id == "x"
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
    )


def _replace_bare_input_assigned_to_x(node, ctx):
    return ["x = abs(int(input()))"]


def _match_int_input_no_abs(node, ctx):
    return _is_int_input(node, ctx) and not (
        isinstance(node.parent, ast.Call)
        and isinstance(node.parent.func, ast.Name)
        and node.parent.func.id == "abs"
    )


def _replace_int_input_no_abs(node, ctx):
    return ["abs(" + ctx.text(node) + ")"]


def _match_while_eq_zero_count(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
        and isinstance(node.test.comparators[0], ast.Name)
    )


def _replace_while_eq_zero_count(node, ctx):
    test = ctx.text(node.test)
    body = "\n".join(ctx.text(s) for s in node.body)
    return [f"while {test} or ({ctx.text(node.test.left)}-{ctx.text(node.test.comparators[0])}) % 2 != 0:\n{body}"]


def _match_while_pos_not_x(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
        and isinstance(node.test.comparators[0], ast.Name)
        and node.test.left.id in {"pos", "s"}
        and node.test.comparators[0].id in {"x"}
    )


def _replace_while_pos_not_x(node, ctx):
    left = ctx.text(node.test.left)
    right = ctx.text(node.test.comparators[0])
    body = "\n".join(ctx.text(s) for s in node.body)
    return [f"while {left} < {right} or ({left}-{right}) % 2 != 0:\n{body}"]


def _match_add_step_to_pos(node, ctx):
    return (
        isinstance(node, ast.AugAssign)
        and isinstance(node.op, ast.Add)
        and isinstance(node.target, ast.Name)
        and node.target.id in {"pos", "s", "pos1"}
    )


def _replace_add_step_to_pos(node, ctx):
    return [ctx.text(node)]


def _match_wrong_input_print(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id == "x"
        and any(
            isinstance(n, ast.Assign)
            and any(isinstance(t, ast.Name) and t.id == "x" for t in n.targets)
            and _is_input_call(n.value)
            for n in ast.walk(ctx.tree)
        )
    )


def _replace_wrong_input_print(node, ctx):
    return ["x = abs(int(input()))", "jumps = 0", "pos = 0", "while pos < x or (pos-x) % 2 != 0:\n    jumps += 1\n    pos += jumps", "print(jumps)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="map_input_to_abs_int_input",
                match=_match_bare_input_assigned_to_x,
                replace=_replace_bare_input_assigned_to_x,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="wrap_int_input_with_abs",
                match=_match_int_input_no_abs,
                replace=_replace_int_input_no_abs,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="while_not_equal_needs_parity_condition",
                match=_match_while_eq_zero_count,
                replace=_replace_while_eq_zero_count,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="while_target_not_reached_needs_parity_condition",
                match=_match_while_pos_not_x,
                replace=_replace_while_pos_not_x,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="accumulate_by_jump_size",
                match=_match_add_step_to_pos,
                replace=_replace_add_step_to_pos,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_input_variable_instead_of_solution",
                match=_match_wrong_input_print,
                replace=_replace_wrong_input_print,
                symptoms=("wrong", "err:TypeError"),
            ),
        ]