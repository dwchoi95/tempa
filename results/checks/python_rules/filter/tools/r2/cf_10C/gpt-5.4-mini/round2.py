from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_bad_digital_root_recursion(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if not isinstance(node.test, ast.Compare) or len(node.test.ops) != 1:
        return False
    op = node.test.ops[0]
    if not isinstance(op, ast.Lt):
        return False
    left = node.test.left
    comps = node.test.comparators
    if not (isinstance(left, ast.Name) and len(comps) == 1 and isinstance(comps[0], ast.Constant)):
        return False
    if comps[0].value != 10:
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
        return False
    if len(node.orelse) != 1 or not isinstance(node.orelse[0], ast.Return):
        return False
    return True


def _fix_bad_digital_root_recursion(node, ctx):
    return [ctx.text(node)]


def _is_input_left_as_string(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id in {"d", "root"}
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Call)
        and isinstance(node.args[0].func, ast.Name)
        and node.args[0].func.id == "input"
        and len(node.args[0].args) == 0
    )


def _fix_input_to_int(node, ctx):
    return [f"{ctx.text(node.func)}(int(input()))"]


def _is_wrong_pair_loop(node, ctx):
    return (
        isinstance(node, ast.For)
        and isinstance(node.target, ast.Name)
        and node.target.id == "j"
        and isinstance(node.iter, ast.Call)
        and isinstance(node.iter.func, ast.Name)
        and node.iter.func.id == "range"
        and len(node.iter.args) == 2
        and isinstance(node.iter.args[0], ast.Name)
        and node.iter.args[0].id == "i"
        and isinstance(node.iter.args[1], ast.Name)
        and node.iter.args[1].id == "n"
        and any(isinstance(s, ast.If) for s in node.body)
    )


def _fix_pair_loop(node, ctx):
    return [f"for j in range(1, n + 1):\n    {ctx.text(node.body[0])}"]


def _is_bad_self_count_if(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.BoolOp) is False
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 2
        and isinstance(node.test.ops[0], ast.Lt)
        and isinstance(node.test.ops[1], ast.NotEq)
    )


def _fix_bad_self_count_if(node, ctx):
    return [f"if {ctx.text(node.test.left)} != {ctx.text(node.test.comparators[1])}"]


def _is_incorrect_increment(node, ctx):
    return (
        isinstance(node, ast.Assign)
        and len(node.targets) == 1
        and isinstance(node.targets[0], ast.Name)
        and node.targets[0].id in {"d", "s"}
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 2
    )


def _fix_increment(node, ctx):
    return [f"{ctx.text(node.targets[0])} = {ctx.text(node.value.left)} + 1"]


def _is_range_len_mismatch(node, ctx):
    return (
        isinstance(node, ast.While)
        and isinstance(node.test, ast.Compare)
        and len(node.test.ops) == 1
        and isinstance(node.test.ops[0], ast.NotEq)
        and isinstance(node.test.left, ast.Call)
        and isinstance(node.test.left.func, ast.Name)
        and node.test.left.func.id == "len"
    )


def _fix_range_len_mismatch(node, ctx):
    return [ctx.text(node)]


def _is_keys_membership(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.In)
        and isinstance(node.comparators[0], ast.Call)
        and isinstance(node.comparators[0].func, ast.Attribute)
        and node.comparators[0].func.attr == "keys"
    )


def _fix_keys_membership(node, ctx):
    return [f"{ctx.text(node.left)} in {ctx.text(node.comparators[0].func.value)}"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="fix_digital_root_recursive_condition",
                match=_is_bad_digital_root_recursion,
                replace=_fix_bad_digital_root_recursion,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_input_to_int_for_numeric_function",
                match=_is_input_left_as_string,
                replace=_fix_input_to_int,
                symptoms=("wrong", "err:TypeError"),
            ),
            Rewrite(
                name="fix_loop_range_to_include_n",
                match=_is_wrong_pair_loop,
                replace=_fix_pair_loop,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_compound_compare_to_simple_inequality",
                match=_is_bad_self_count_if,
                replace=_fix_bad_self_count_if,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_double_increment_to_single",
                match=_is_incorrect_increment,
                replace=_fix_increment,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="fix_keys_membership_on_dict_view",
                match=_is_keys_membership,
                replace=_fix_keys_membership,
                symptoms=("wrong",),
            ),
        ]