from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _looks_empty_check(text):
    t = text.replace(" ", "")
    if "()" in t or "[]" in t:
        return True
    if "len(" in t and ("==0" in t or "<1" in t):
        return True
    if t.startswith("not"):
        return True
    return False


def _is_docstring_expr(node):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str))


# --- Rule 1: empty-sequence branch returns the wrong sentinel instead of 0 ---
def _match_empty_return(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If):
        return False
    if ctx.field(node) != "body":
        return False
    if node not in parent.body:
        return False
    if not _looks_empty_check(ctx.text(parent.test)):
        return False
    val_text = ctx.text(node.value).strip()
    if val_text == "0":
        return False
    return True


def _fix_empty_return(node, ctx):
    return ["return 0"]


# --- Rule 2: `seq == () or []` style check missing the second `seq ==` ---
def _match_or_missing_compare(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or)):
        return False
    if len(node.values) != 2:
        return False
    a, b = node.values
    if not (isinstance(a, ast.Compare) and len(a.ops) == 1 and isinstance(a.ops[0], ast.Eq)):
        return False
    if isinstance(b, ast.Compare):
        return False
    return True


def _fix_or_missing_compare(node, ctx):
    a, b = node.values
    left_text = ctx.text(a.left)
    return [ctx.text(a) + " or " + left_text + " == " + ctx.text(b)]


# --- Rule 3: if/return pair attached inside the loop body instead of for/else ---
def _for_premature_shape(node):
    body = node.body
    if len(body) == 1:
        s = body[0]
        if (isinstance(s, ast.If) and len(s.body) == 1 and isinstance(s.body[0], ast.Return)
                and len(s.orelse) == 1 and isinstance(s.orelse[0], ast.Return)):
            return "B"
    if len(body) == 2:
        s0, s1 = body
        if (isinstance(s0, ast.If) and not s0.orelse and len(s0.body) == 1
                and isinstance(s0.body[0], ast.Return) and isinstance(s1, ast.Return)):
            return "A"
    return None


def _match_for_premature(node, ctx):
    if not isinstance(node, ast.For):
        return False
    return _for_premature_shape(node) is not None


def _fix_for_premature(node, ctx):
    shape = _for_premature_shape(node)
    target = ctx.text(node.target)
    iter_ = ctx.text(node.iter)
    body = node.body
    if shape == "B":
        if_stmt = body[0]
        if_ret = ctx.text(if_stmt.body[0])
        else_ret = ctx.text(if_stmt.orelse[0])
    else:
        if_stmt, other = body
        if_ret = ctx.text(if_stmt.body[0])
        else_ret = ctx.text(other)
    test = ctx.text(if_stmt.test)
    new_text = ("for " + target + " in " + iter_ + ":\n"
                "    if " + test + ":\n"
                "        " + if_ret + "\n"
                "else:\n"
                "    " + else_ret)
    return [new_text]


# --- Rule 4: a dead trailing docstring where a fallback return belongs ---
def _match_trailing_docstring(node, ctx):
    if not _is_docstring_expr(node):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    body = parent.body
    if not body or body[-1] is not node or len(body) < 2:
        return False
    prev = body[-2]
    if isinstance(prev, ast.Return):
        return False
    return True


def _fix_trailing_docstring(node, ctx):
    return ["return len(seq)"]


# --- Rule 5: a `for` loop is the last statement with no fallback return ---
def _match_missing_return_after_for(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if node.orelse:
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    body = parent.body
    if not body or body[-1] is not node:
        return False
    return True


def _fix_missing_return_after_for(node, ctx):
    return [ctx.text(node) + "\nreturn len(seq)"]


# --- Rule 6: off-by-one `range(len(seq) +/- 1)` ---
def _match_range_offby1(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "range" and len(node.args) == 1):
        return False
    arg = node.args[0]
    if not (isinstance(arg, ast.BinOp) and isinstance(arg.op, (ast.Add, ast.Sub))):
        return False
    if not (isinstance(arg.right, ast.Constant) and arg.right.value == 1):
        return False
    if isinstance(arg.left, ast.Call) and isinstance(arg.left.func, ast.Name) and arg.left.func.id == "len":
        return True
    if isinstance(arg.left, ast.Name):
        return True
    return False


def _fix_range_offby1(node, ctx):
    arg = node.args[0]
    return ["range(" + ctx.text(arg.left) + ")"]


# --- Rule 7: `x >= upper_bound` should be `x > upper_bound` before returning len(seq) ---
def _match_overreach_gte(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If) or ctx.field(node) != "test":
        return False
    for s in parent.body:
        if isinstance(s, ast.Return) and s.value is not None and "len(" in ctx.text(s.value):
            return True
    return False


def _fix_overreach_gte(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


# --- Rule 8: `x < elem` should be `x <= elem` (strict boundary on the search value) ---
def _match_strict_lt_x(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Lt)
            and isinstance(node.left, ast.Name) and node.left.id == "x")


def _fix_strict_lt_x(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


# --- Rule 9: `v += v` instead of `v += 1` ---
def _match_self_aug_add(node, ctx):
    return (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)
            and isinstance(node.target, ast.Name) and isinstance(node.value, ast.Name)
            and node.target.id == node.value.id)


def _fix_self_aug_add(node, ctx):
    return [ctx.text(node.target) + " += 1"]


# --- Rule 10: `elem > x` counting comparison backwards (should be `x > elem`) ---
def _match_elem_gt_x(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Gt)):
        return False
    if not (isinstance(node.comparators[0], ast.Name) and node.comparators[0].id == "x"):
        return False
    if isinstance(node.left, ast.Name) and node.left.id == "x":
        return False
    return True


def _fix_elem_gt_x(node, ctx):
    return [ctx.text(node.comparators[0]) + " > " + ctx.text(node.left)]


# --- Rule 11: bare `sorted(seq)` statement whose result is discarded ---
def _match_bare_sorted(node, ctx):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    call = node.value
    if not (isinstance(call.func, ast.Name) and call.func.id == "sorted"):
        return False
    if not call.args:
        return False
    return True


def _fix_bare_sorted(node, ctx):
    call = node.value
    target_text = ctx.text(call.args[0])
    return [target_text + " = " + ctx.text(call)]


# --- Rule 12: empty-check branch sets a variable instead of returning early ---
def _match_empty_assign(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If):
        return False
    if ctx.field(node) != "body" or len(parent.body) != 1:
        return False
    if not _looks_empty_check(ctx.text(parent.test)):
        return False
    return True


def _fix_empty_assign(node, ctx):
    return ["return 0"]


# --- Rule 13: `seq == ()` (or `seq == []`) alone misses the other empty form ---
def _match_tuple_or_list_only_check(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    if not (isinstance(node.left, ast.Name) and node.left.id == "seq"):
        return False
    comp = node.comparators[0]
    is_empty_tuple = isinstance(comp, ast.Tuple) and len(comp.elts) == 0
    is_empty_list = isinstance(comp, ast.List) and len(comp.elts) == 0
    if not (is_empty_tuple or is_empty_list):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and ctx.field(node) == "test"):
        return False
    return True


def _fix_tuple_or_list_only_check(node, ctx):
    return ["len(seq) == 0"]


# --- Rule 14: first statement indexes seq without any emptiness guard ---
def _match_missing_leading_guard(node, ctx):
    if not isinstance(node, ast.If):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    body = parent.body
    idx = 0
    if body and _is_docstring_expr(body[0]):
        idx = 1
    if idx >= len(body) or body[idx] is not node:
        return False
    test_text = ctx.text(node.test)
    if _looks_empty_check(test_text):
        return False
    t = test_text.replace(" ", "")
    if "seq[0]" in t or "seq[-1]" in t or "seq[len(seq)" in t:
        return True
    return False


def _fix_missing_leading_guard(node, ctx):
    return ["if len(seq) == 0:\n    return 0\n" + ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="empty_check_should_return_zero", match=_match_empty_return,
                    replace=_fix_empty_return, symptoms=("wrong",)),
            Rewrite(name="or_missing_second_compare", match=_match_or_missing_compare,
                    replace=_fix_or_missing_compare, symptoms=("wrong",)),
            Rewrite(name="for_if_premature_return_to_for_else", match=_match_for_premature,
                    replace=_fix_for_premature, symptoms=("wrong",)),
            Rewrite(name="trailing_docstring_should_be_fallback_return", match=_match_trailing_docstring,
                    replace=_fix_trailing_docstring, symptoms=("wrong",)),
            Rewrite(name="missing_return_after_for", match=_match_missing_return_after_for,
                    replace=_fix_missing_return_after_for, symptoms=("wrong",)),
            Rewrite(name="range_len_offby1", match=_match_range_offby1,
                    replace=_fix_range_offby1, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="overreach_gte_should_be_gt", match=_match_overreach_gte,
                    replace=_fix_overreach_gte, symptoms=("wrong",)),
            Rewrite(name="strict_lt_on_x_should_be_lte", match=_match_strict_lt_x,
                    replace=_fix_strict_lt_x, symptoms=("wrong",)),
            Rewrite(name="self_aug_add_should_increment", match=_match_self_aug_add,
                    replace=_fix_self_aug_add, symptoms=("wrong", "timeout")),
            Rewrite(name="elem_gt_x_counting_direction_flip", match=_match_elem_gt_x,
                    replace=_fix_elem_gt_x, symptoms=("wrong",)),
            Rewrite(name="bare_sorted_result_discarded", match=_match_bare_sorted,
                    replace=_fix_bare_sorted, symptoms=("wrong",)),
            Rewrite(name="empty_check_assign_should_return", match=_match_empty_assign,
                    replace=_fix_empty_assign, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="tuple_or_list_only_empty_check", match=_match_tuple_or_list_only_check,
                    replace=_fix_tuple_or_list_only_check, symptoms=("wrong",)),
            Rewrite(name="missing_leading_empty_guard", match=_match_missing_leading_guard,
                    replace=_fix_missing_leading_guard, symptoms=("wrong", "err:IndexError")),
        ]