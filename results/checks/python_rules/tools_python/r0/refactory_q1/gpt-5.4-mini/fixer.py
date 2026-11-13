from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_none_return(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Constant) and node.value.value is None


def _replace_none_with_zero(node, ctx):
    return ["return 0"]


def _is_empty_tuple_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.Is))
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Tuple)
        and len(node.comparators[0].elts) == 0
    )


def _is_empty_list_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], (ast.Eq, ast.Is))
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.List)
        and len(node.comparators[0].elts) == 0
    )


def _replace_empty_seq_checks(node, ctx):
    left = ctx.text(node.left)
    return [f"not {left}"]


def _is_len_call_cmp(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and len(node.comparators) == 1
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.left.args[0], ast.Name)
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 0
    )


def _replace_len_cmp_to_zero(node, ctx):
    return [f"len({ctx.text(node.left.args[0])}) == 0"]


def _is_strict_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_strict_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _to_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_gt_zero(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Gt)
        and len(node.comparators) == 1
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 0
    )


def _to_ge_zero(node, ctx):
    return [ctx.text(node.left) + " >= 0"]


def _is_return_i_plus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.left, ast.Name)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _replace_return_i_plus_one(node, ctx):
    return ["return len(seq)"]


def _is_return_i_minus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Sub)
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _replace_return_i_minus_one(node, ctx):
    return ["return i"]


def _is_return_len_minus_one(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Sub)
        and isinstance(node.value.left, ast.Call)
        and isinstance(node.value.left.func, ast.Name)
        and node.value.left.func.id == "len"
        and len(node.value.left.args) == 1
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _replace_return_len_minus_one(node, ctx):
    return [f"return len({ctx.text(node.value.left.args[0])})"]


def _is_return_none_stmt(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_bare_return_with_zero(node, ctx):
    return ["return 0"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="return_none_in_search", match=_is_none_return, replace=_replace_none_with_zero, symptoms=("wrong",)),
            Rewrite(name="empty_tuple_check_to_not_seq", match=_is_empty_tuple_check, replace=_replace_empty_seq_checks, symptoms=("wrong",)),
            Rewrite(name="empty_list_check_to_not_seq", match=_is_empty_list_check, replace=_replace_empty_seq_checks, symptoms=("wrong",)),
            Rewrite(name="len_eq_zero_check", match=_is_len_call_cmp, replace=_replace_len_cmp_to_zero, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt, replace=_to_lte, symptoms=("wrong",)),
            Rewrite(name="strict_gt_should_be_gte", match=_is_strict_gt, replace=_to_gte, symptoms=("wrong",)),
            Rewrite(name="gt_zero_should_be_ge_zero", match=_is_gt_zero, replace=_to_ge_zero, symptoms=("wrong",)),
            Rewrite(name="off_by_one_return_i_plus_one", match=_is_return_i_plus_one, replace=_replace_return_i_plus_one, symptoms=("wrong",)),
            Rewrite(name="off_by_one_return_i_minus_one", match=_is_return_i_minus_one, replace=_replace_return_i_minus_one, symptoms=("wrong",)),
            Rewrite(name="len_minus_one_return", match=_is_return_len_minus_one, replace=_replace_return_len_minus_one, symptoms=("wrong",)),
            Rewrite(name="bare_return_to_zero", match=_is_return_none_stmt, replace=_replace_bare_return_with_zero, symptoms=("wrong",)),
        ]