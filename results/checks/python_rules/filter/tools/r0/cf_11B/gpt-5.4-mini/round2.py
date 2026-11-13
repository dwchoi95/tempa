from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_input_call(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "map"
    )


def _fix_input_call(node, ctx):
    return [f"{ctx.text(node.targets[0])} = abs(int(input()))"]


def _is_absless_int_input(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "int"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Call)
        and isinstance(node.value.args[0].func, ast.Name)
        and node.value.args[0].func.id == "input"
    )


def _fix_absless_int_input(node, ctx):
    return [f"{ctx.text(node.targets[0])} = abs(int(input()))"]


def _is_wrong_while_condition(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Name)
        and len(node.test.comparators) == 1
        and isinstance(node.test.comparators[0], ast.Name)
    )


def _fix_while_condition(node, ctx):
    return [
        f"while {ctx.text(node.test.left)} < {ctx.text(node.test.comparators[0])} or ({ctx.text(node.test.left)}-{ctx.text(node.test.comparators[0])}) % 2 != 0:"
    ]


def _is_bad_step_update(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], (ast.LtE, ast.GtE, ast.Lt, ast.Gt))
        and any(
            isinstance(stmt, ast.AugAssign)
            and isinstance(stmt.op, (ast.Add, ast.Sub))
            and isinstance(stmt.target, ast.Name)
            for stmt in node.body + node.orelse
        )
    )


def _fix_bad_step_update(node, ctx):
    return [ctx.text(node)]


def _is_weird_print(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "print"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id == "x"
    )


def _fix_weird_print(node, ctx):
    return ["print(x)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="map_used_as_input",
                match=_is_bad_input_call,
                replace=_fix_input_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_abs_on_input",
                match=_is_absless_int_input,
                replace=_fix_absless_int_input,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="while_not_equal_should_use_threshold_parity",
                match=_is_wrong_while_condition,
                replace=_fix_while_condition,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="generic_jump_update_noop",
                match=_is_bad_step_update,
                replace=_fix_bad_step_update,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="print_variable_as_result",
                match=_is_weird_print,
                replace=_fix_weird_print,
                symptoms=("wrong",),
            ),
        ]