from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_seq_param(node, ctx):
    return isinstance(node, ast.Name) and node.id == "seq"


def _is_empty_seq_check(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 2
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.ops[1], ast.Eq)
        and ((isinstance(node.left, ast.Name) and node.left.id == "seq") or True)
    )


def _is_len_seq_zero(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 1
        and isinstance(node.ops[0], ast.Eq)
        and isinstance(node.left, ast.Call)
        and isinstance(node.left.func, ast.Name)
        and node.left.func.id == "len"
        and len(node.left.args) == 1
        and isinstance(node.left.args[0], ast.Name)
        and node.left.args[0].id == "seq"
        and isinstance(node.comparators[0], ast.Constant)
        and node.comparators[0].value == 0
    )


def _replace_empty_check(node, ctx):
    return ["len(seq) == 0"]


def _replace_return_none_zero(node, ctx):
    return ["0"]


def _is_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is not None and isinstance(node.value, ast.Constant) and node.value.value is None


def _is_return_len_seq_plus1(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.left, ast.Call)
        and isinstance(node.value.left.func, ast.Name)
        and node.value.left.func.id == "len"
    )


def _replace_return_len_seq(node, ctx):
    return ["return len(seq)"]


def _is_return_bare(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_return_zero_stmt(node, ctx):
    return ["return 0"]


def _is_strict_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_lte_return_zero_if_empty(node, ctx):
    return (
        isinstance(node, ast.If)
        and isinstance(node.test, ast.Compare)
        and isinstance(node.test.left, ast.Name)
        and node.test.left.id == "seq"
    )


def _replace_return_zero_stmt(node, ctx):
    return ["return 0"]


def _is_wrong_return_i_plus1(node, ctx):
    return (
        isinstance(node, ast.Return)
        and isinstance(node.value, ast.BinOp)
        and isinstance(node.value.op, ast.Add)
        and isinstance(node.value.left, ast.Name)
        and node.value.left.id == "i"
        and isinstance(node.value.right, ast.Constant)
        and node.value.right.value == 1
    )


def _replace_return_len(node, ctx):
    return ["return len(seq)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_seq_check_as_len_zero", match=_is_len_seq_zero, replace=_replace_empty_check, symptoms=("wrong",)),
            Rewrite(name="return_none_to_zero", match=_is_return_none, replace=_replace_return_none_zero, symptoms=("wrong",)),
            Rewrite(name="bare_return_to_zero", match=_is_return_bare, replace=_replace_return_zero_stmt, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt, replace=_to_lte, symptoms=("wrong",)),
            Rewrite(name="return_len_seq_plus_one_to_len_seq", match=_is_return_len_seq_plus1, replace=_replace_return_len, symptoms=("wrong",)),
        ]