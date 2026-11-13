from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_empty_check(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    if len(node.ops) != 1 or len(node.comparators) != 1:
        return False
    left = node.left
    comp = node.comparators[0]
    if isinstance(node.ops[0], (ast.Eq, ast.Is)):
        return (
            (isinstance(left, ast.Name) and left.id == "seq"
             and isinstance(comp, (ast.Tuple, ast.List)) and len(comp.elts) == 0)
            or (isinstance(comp, ast.Name) and comp.id == "seq"
                and isinstance(left, (ast.Tuple, ast.List)) and len(left.elts) == 0)
        )
    if isinstance(node.ops[0], ast.NotEq):
        return False
    return False


def _fix_empty_check(node, ctx):
    return ["len(seq) == 0"]


def _is_strict_lt_on_search_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _fix_lt_to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_gte_when_should_be_gt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)


def _fix_gte_to_gt(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


def _is_gt_when_should_be_gte(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _fix_gt_to_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_lt_when_should_be_le(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _fix_lt_to_le(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_gt_when_should_be_lt(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _fix_gt_to_lt(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


def _is_break_instead_of_return(node, ctx):
    return isinstance(node, ast.Break)


def _fix_break_to_return_i(node, ctx):
    parent = ctx.parent(node)
    grand = ctx.parent(parent) if parent is not None else None
    if isinstance(grand, ast.For) and isinstance(parent, ast.If):
        return ["return i"]
    return []


def _is_return_none(node, ctx):
    return isinstance(node, ast.Constant) and node.value is None


def _fix_none_to_zero(node, ctx):
    return ["0"]


def _is_return_i_plus_1(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Add)


def _fix_i_plus_1_to_len(node, ctx):
    txt = ctx.text(node.value)
    if "i + 1" in txt or "i+1" in txt:
        return ["len(seq)"]
    return []


def _is_wrong_range_len_minus1(node, ctx):
    return (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and node.func.id == "range"
        and len(node.args) == 1
        and isinstance(node.args[0], ast.BinOp)
        and isinstance(node.args[0].op, ast.Sub)
        and isinstance(node.args[0].right, ast.Constant)
        and node.args[0].right.value == 1
    )


def _fix_range_minus1(node, ctx):
    return ["range(len(seq))"]


def _is_index_minus1(node, ctx):
    return isinstance(node, ast.BinOp) and isinstance(node.op, ast.Sub) and isinstance(node.right, ast.Constant) and node.right.value == 1


def _fix_index_minus1(node, ctx):
    return [ctx.text(node.left)]


def _is_count_add_count(node, ctx):
    return (
        isinstance(node, ast.AugAssign)
        and isinstance(node.target, ast.Name)
        and node.target.id in {"count", "counter", "position", "result", "value"}
        and isinstance(node.op, ast.Add)
        and isinstance(node.value, ast.Name)
        and node.value.id == node.target.id
    )


def _fix_add_self_to_one(node, ctx):
    return [f"{ctx.text(node.target)} += 1"]


def _is_return_len_plus1(node, ctx):
    return isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp) and isinstance(node.value.op, ast.Add)


def _fix_len_plus1_to_len(node, ctx):
    txt = ctx.text(node.value)
    if "len(seq) + 1" in txt or "len(seq)+1" in txt:
        return ["len(seq)"]
    if "i + 1" in txt or "i+1" in txt:
        return ["len(seq)"]
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_sequence_returns_zero", match=_is_empty_check, replace=_fix_empty_check, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt_on_search_compare, replace=_fix_lt_to_lte, symptoms=("wrong",)),
            Rewrite(name="gte_should_be_gt", match=_is_gte_when_should_be_gt, replace=_fix_gte_to_gt, symptoms=("wrong",)),
            Rewrite(name="gt_should_be_gte", match=_is_gt_when_should_be_gte, replace=_fix_gt_to_gte, symptoms=("wrong",)),
            Rewrite(name="off_by_one_range_bound", match=_is_wrong_range_len_minus1, replace=_fix_range_minus1, symptoms=("wrong",)),
            Rewrite(name="return_none_to_zero", match=_is_return_none, replace=_fix_none_to_zero, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="break_to_return_i", match=_is_break_instead_of_return, replace=_fix_break_to_return_i, symptoms=("wrong",)),
            Rewrite(name="return_i_plus_one_to_len", match=_is_return_i_plus_1, replace=_fix_i_plus_1_to_len, symptoms=("wrong",)),
            Rewrite(name="off_by_one_index", match=_is_index_minus1, replace=_fix_index_minus1, symptoms=("wrong",)),
            Rewrite(name="double_increment_to_one", match=_is_count_add_count, replace=_fix_add_self_to_one, symptoms=("timeout", "wrong")),
            Rewrite(name="len_plus_one_to_len", match=_is_return_len_plus1, replace=_fix_len_plus1_to_len, symptoms=("wrong",)),
        ]