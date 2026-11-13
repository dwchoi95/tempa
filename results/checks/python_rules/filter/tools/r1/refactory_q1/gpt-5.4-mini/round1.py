from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_empty_seq_check(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    if len(node.ops) != 1 or len(node.comparators) != 1:
        return False
    left = node.left
    comp = node.comparators[0]
    if not (isinstance(left, ast.Name) and left.id == "seq"):
        return False
    if not isinstance(comp, (ast.Tuple, ast.List)):
        return len(comp.elts) == 0
    return False


def _replace_empty_seq_with_zero(node, ctx):
    return ["0"]


def _is_strict_lt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)


def _replace_lt_with_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_strict_gt_compare(node, ctx):
    return isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)


def _replace_gt_with_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_return_len_minus_one(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp)
            and isinstance(node.value.op, ast.Sub)
            and isinstance(node.value.left, ast.Call)
            and isinstance(node.value.left.func, ast.Name)
            and node.value.left.func.id == "len"
            and isinstance(node.value.right, ast.Constant)
            and node.value.right.value == 1)


def _replace_len_minus_one_with_len(node, ctx):
    return [ctx.text(node.value.left) + ""]


def _is_return_i_plus_one(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.BinOp)
            and isinstance(node.value.op, ast.Add)
            and isinstance(node.value.right, ast.Constant)
            and node.value.right.value == 1)


def _replace_i_plus_one_with_i(node, ctx):
    return [ctx.text(node.value.left)]


def _is_range_len_minus_one(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"
            and len(node.args) == 1 and isinstance(node.args[0], ast.BinOp)
            and isinstance(node.args[0].op, ast.Sub)
            and isinstance(node.args[0].right, ast.Constant)
            and node.args[0].right.value == 1)


def _replace_range_len_minus_one(node, ctx):
    return ["range(" + ctx.text(node.args[0].left) + ")"]


def _is_range_len_plus_one(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"
            and len(node.args) == 1 and isinstance(node.args[0], ast.BinOp)
            and isinstance(node.args[0].op, ast.Add)
            and isinstance(node.args[0].right, ast.Constant)
            and node.args[0].right.value == 1)


def _replace_range_len_plus_one(node, ctx):
    return ["range(" + ctx.text(node.args[0].left) + ")"]


def _is_append_x_return_none(node, ctx):
    return isinstance(node, ast.Expr) and isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Attribute) \
        and node.value.func.attr == "append"


def _replace_append_expr(node, ctx):
    return [""]


def _is_bare_return_none(node, ctx):
    return isinstance(node, ast.Return) and node.value is None


def _replace_return_none(node, ctx):
    return []


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_sequence_should_return_zero", match=_is_empty_seq_check,
                    replace=_replace_empty_seq_with_zero, symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte", match=_is_strict_lt_compare,
                    replace=_replace_lt_with_lte, symptoms=("wrong",)),
            Rewrite(name="strict_gt_should_be_gte", match=_is_strict_gt_compare,
                    replace=_replace_gt_with_gte, symptoms=("wrong",)),
            Rewrite(name="len_minus_one_to_len", match=_is_return_len_minus_one,
                    replace=_replace_len_minus_one_with_len, symptoms=("wrong",)),
            Rewrite(name="off_by_one_return_i_plus_one", match=_is_return_i_plus_one,
                    replace=_replace_i_plus_one_with_i, symptoms=("wrong",)),
            Rewrite(name="range_len_minus_one_to_len", match=_is_range_len_minus_one,
                    replace=_replace_range_len_minus_one, symptoms=("wrong",)),
            Rewrite(name="range_len_plus_one_to_len", match=_is_range_len_plus_one,
                    replace=_replace_range_len_plus_one, symptoms=("wrong",)),
            Rewrite(name="delete_unneeded_append_expression", match=_is_append_x_return_none,
                    replace=_replace_append_expr, symptoms=("wrong",)),
            Rewrite(name="bare_return_none_removed", match=_is_bare_return_none,
                    replace=_replace_return_none, symptoms=("wrong",)),
        ]