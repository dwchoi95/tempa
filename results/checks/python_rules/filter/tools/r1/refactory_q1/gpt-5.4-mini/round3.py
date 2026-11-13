from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_search_call_context(node, ctx):
    return isinstance(ctx.parent(node), ast.FunctionDef) and ctx.parent(node).name == "search"


def _is_len_seq(node):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "len"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.Name)
        and node.args[0].id == "seq"
    )


def _is_empty_seq_check(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1 or len(node.comparators) != 1:
        return False
    left = node.left
    right = node.comparators[0]
    op = node.ops[0]
    return (
        isinstance(op, (ast.Eq, ast.NotEq))
        and (
            (_is_len_seq(left) and isinstance(right, ast.Constant) and right.value == 0)
            or (_is_len_seq(right) and isinstance(left, ast.Constant) and left.value == 0)
            or (isinstance(left, ast.Name) and left.id == "seq" and isinstance(right, (ast.Tuple, ast.List)) and len(right.elts) == 0)
            or (isinstance(right, ast.Name) and right.id == "seq" and isinstance(left, (ast.Tuple, ast.List)) and len(left.elts) == 0)
        )
    )


def _replace_empty_return_zero(node, ctx):
    return ["return 0"]


def _match_bad_newseq_len(node, ctx):
    return isinstance(node, ast.Compare) and ctx.text(node).replace(" ", "") == "newseq[-1]<x"


def _replace_newseq_len(node, ctx):
    return ["seq[-1] < x"]


def _match_empty_seq_incorrect(node, ctx):
    return _is_empty_seq_check(node, ctx)


def _replace_empty_seq_incorrect(node, ctx):
    txt = ctx.text(node)
    if "return None" in ctx.text(ctx.parent(node)) or "return False" in ctx.text(ctx.parent(node)):
        return ["len(seq) == 0"]
    return ["len(seq) == 0"]


def _match_return_len_plus_one(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Add)


def _replace_return_len_plus_one(node, ctx):
    return ["return len(seq)"]


def _match_strict_lt_in_search(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _match_redundant_return_inside_loop(node, ctx):
    return isinstance(node, ast.Return) and isinstance(ctx.parent(node), ast.If)


def _replace_redundant_return_inside_loop(node, ctx):
    parent = ctx.parent(node)
    if isinstance(parent, ast.If) and len(parent.body) == 1 and parent.body[0] is node:
        return ["break"]
    return []


def _match_bare_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_bare_return_none(node, ctx):
    return ["return len(seq)"]


def _match_break_return_i(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "i"


def _replace_break_return_i(node, ctx):
    return ["return len(seq)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_sequence_should_return_zero", match=_match_empty_seq_incorrect,
                    replace=_replace_empty_seq_incorrect, symptoms=("wrong",)),
            Rewrite(name="newseq_last_check_should_use_seq", match=_match_bad_newseq_len,
                    replace=_replace_newseq_len, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_match_strict_lt_in_search,
                    replace=_replace_lte, symptoms=("wrong",)),
            Rewrite(name="bare_return_none_should_return_len", match=_match_bare_return_none,
                    replace=_replace_bare_return_none, symptoms=("wrong",)),
            Rewrite(name="return_i_after_loop_should_be_len", match=_match_break_return_i,
                    replace=_replace_break_return_i, symptoms=("wrong",)),
            Rewrite(name="len_plus_one_should_be_len", match=_match_return_len_plus_one,
                    replace=_replace_return_len_plus_one, symptoms=("wrong",)),
            Rewrite(name="return_inside_if_in_loop_should_break", match=_match_redundant_return_inside_loop,
                    replace=_replace_redundant_return_inside_loop, symptoms=("wrong",)),
        ]