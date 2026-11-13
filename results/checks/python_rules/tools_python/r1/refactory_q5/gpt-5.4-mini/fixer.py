from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_len_cmp(node, ctx, op_type):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], op_type)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.comparators[0], ast.Name)
        and ctx.text(node.left.args[0]) == ctx.text(node.comparators[0])
    )


def _fix_len_lt_to_eq(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


def _fix_len_le_to_lt(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


def _is_return_slice_off_by_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.Slice)
        and node.value.slice.lower is None
        and node.value.slice.step is None
        and isinstance(node.value.slice.upper, ast.BinOp)
        and isinstance(node.value.slice.upper.op, ast.Add)
        and isinstance(node.value.slice.upper.right, ast.Constant)
        and node.value.slice.upper.right.value == 1
    )


def _fix_return_slice_off_by_one(node, ctx):
    v = node.value
    upper = v.slice.upper
    left = ctx.text(upper.left)
    return [f"return {ctx.text(v.value)}[:{left}]"]


def _is_return_wrong_constant_5(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.Subscript)
        and isinstance(node.value.slice, ast.Constant)
        and node.value.slice.value == 5
    )


def _fix_return_slice_k(node, ctx):
    return [f"return {ctx.text(node.value.value)}[:k]"]


def _is_append_remove_result(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Call)
        and isinstance(node.value.args[0].func, ast.Attribute)
        and node.value.args[0].func.attr == "remove"
    )


def _fix_append_remove_result(node, ctx):
    app = node.value
    removed = app.args[0]
    target = ctx.text(app.func.value)
    arg = ctx.text(removed.args[0])
    return [f"{target}.append({arg})\n{ctx.text(removed.func.value)}.remove({arg})"]


def _is_append_max_then_remove_max(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Call)
        and isinstance(node.value.args[0].func, ast.Name)
        and node.value.args[0].func.id == "max"
    )


def _fix_append_max_then_remove_max(node, ctx):
    return [ctx.text(node.value)]


def _is_return_lst_when_should_be_empty(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "lst"


def _fix_return_empty_list(node, ctx):
    return ["return []"]


def _is_wrong_list_append_name(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Attribute)
        and node.value.func.attr == "append"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
        and node.value.args[0].id in {"lst", "numbers", "element", "elements", "oldest", "i"}
    )


def _fix_append_max_name(node, ctx):
    return [ctx.text(node)]


def _is_missing_counter_increment(node, ctx):
    return (
        isinstance(node, ast.While)
        and any(
            isinstance(s, ast.Expr)
            and isinstance(s.value, ast.Call)
            and isinstance(s.value.func, ast.Attribute)
            and s.value.func.attr == "append"
            for s in node.body
        )
        and not any(
            isinstance(s, ast.AugAssign)
            and isinstance(s.op, ast.Add)
            and isinstance(s.target, ast.Name)
            and s.target.id in {"counter", "count", "n"}
            for s in node.body
        )
    )


def _fix_add_counter_increment(node, ctx):
    for s in node.body:
        if isinstance(s, ast.Expr):
            return [ctx.text(s) + "\ncounter += 1"]
    return []


def _is_wrong_pop_max_index(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "pop"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
        and node.args[0].id in {"largest", "biggest", "maxi", "maximum"}
    )


def _fix_pop_biggest(node, ctx):
    return [f"{ctx.text(node.func.value)}.pop({ctx.text(node.func.value)}.index(max({ctx.text(node.func.value)})))"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="len_k_loop_off_by_one",
                match=lambda n, c: _is_len_cmp(n, c, ast.LtE),
                replace=_fix_len_le_to_lt,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="len_k_loop_needs_equality",
                match=lambda n, c: _is_len_cmp(n, c, ast.Lt),
                replace=_fix_len_lt_to_eq,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_slice_off_by_one",
                match=_is_return_slice_off_by_one,
                replace=_fix_return_slice_off_by_one,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_slice_should_use_k",
                match=_is_return_wrong_constant_5,
                replace=_fix_return_slice_k,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_remove_result_confusion",
                match=_is_append_remove_result,
                replace=_fix_append_remove_result,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="append_max_then_remove_max",
                match=_is_append_max_then_remove_max,
                replace=_fix_append_max_then_remove_max,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="return_lst_instead_of_empty",
                match=_is_return_lst_when_should_be_empty,
                replace=_fix_return_empty_list,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="wrong_value_appended_in_topk_loop",
                match=_is_wrong_list_append_name,
                replace=_fix_append_max_name,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="missing_counter_increment",
                match=_is_missing_counter_increment,
                replace=_fix_add_counter_increment,
                symptoms=("wrong", "timeout"),
            ),
            Rewrite(
                name="pop_should_use_index_of_max",
                match=_is_wrong_pop_max_index,
                replace=_fix_pop_biggest,
                symptoms=("wrong",),
            ),
        ]