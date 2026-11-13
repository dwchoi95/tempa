from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _ancestors(node, ctx):
    cur = node
    while True:
        p = ctx.parent(cur)
        if p is None:
            return
        yield p
        cur = p


def _enclosing_for(node, ctx):
    for p in _ancestors(node, ctx):
        if isinstance(p, ast.For):
            return p
        if isinstance(p, (ast.FunctionDef, ast.Module)):
            return None
    return None


def _enclosing_while(node, ctx):
    for p in _ancestors(node, ctx):
        if isinstance(p, ast.While):
            return p
        if isinstance(p, (ast.FunctionDef, ast.Module)):
            return None
    return None


# ---------------------------------------------------------------------------
# R1: comparing a string-iteration variable / subscript to an int literal
# 4 or 7 instead of the string literal '4' / '7'.
# ---------------------------------------------------------------------------
def _is_digit_literal_mismatch(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], (ast.Eq, ast.NotEq)):
        return False
    left, right = node.left, node.comparators[0]

    def is_int47(x):
        return isinstance(x, ast.Constant) and x.value in (4, 7) and not isinstance(x.value, bool)

    if is_int47(right):
        other = left
    elif is_int47(left):
        other = right
    else:
        return False

    if isinstance(other, ast.Subscript):
        return True
    if isinstance(other, ast.Name):
        f = _enclosing_for(node, ctx)
        if f is not None and isinstance(f.target, ast.Name) and f.target.id == other.id:
            it = f.iter
            if isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == "range":
                return False
            return True
    return False


def _fix_digit_literal_mismatch(node, ctx):
    left, right = node.left, node.comparators[0]
    opstr = " == " if isinstance(node.ops[0], ast.Eq) else " != "

    def is_int47(x):
        return isinstance(x, ast.Constant) and x.value in (4, 7) and not isinstance(x.value, bool)

    if is_int47(right):
        return [f"{ctx.text(left)}{opstr}'{right.value}'"]
    else:
        return [f"'{left.value}'{opstr}{ctx.text(right)}"]


# ---------------------------------------------------------------------------
# R2: "count =+ 1" typo instead of "count += 1"
# ---------------------------------------------------------------------------
def _is_assign_plus_typo(node, ctx):
    if not isinstance(node, ast.Assign) or len(node.targets) != 1:
        return False
    tgt = node.targets[0]
    if not isinstance(tgt, ast.Name):
        return False
    val = node.value
    return (isinstance(val, ast.UnaryOp) and isinstance(val.op, ast.UAdd)
            and isinstance(val.operand, ast.Constant) and val.operand.value == 1)


def _fix_assign_plus_typo(node, ctx):
    return [f"{ctx.text(node.targets[0])} += 1"]


# ---------------------------------------------------------------------------
# R3: comparing a count to len(...) instead of to 4 or 7
# ---------------------------------------------------------------------------
def _is_len_call(x):
    return isinstance(x, ast.Call) and isinstance(x.func, ast.Name) and x.func.id == "len"


def _is_count_eq_len(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.Eq):
        return False
    left, right = node.left, node.comparators[0]
    return _is_len_call(left) or _is_len_call(right)


def _fix_count_eq_len(node, ctx):
    left, right = node.left, node.comparators[0]
    if _is_len_call(left) and _is_len_call(right):
        count_expr = ctx.text(right)
    elif _is_len_call(left):
        count_expr = ctx.text(right)
    else:
        count_expr = ctx.text(left)
    return [f"{count_expr} == 4 or {count_expr} == 7"]


# ---------------------------------------------------------------------------
# R4: comparing to int(X) where X is a digit-string, should compare to len(X)
# ---------------------------------------------------------------------------
def _is_int_should_be_len(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.Eq):
        return False
    right = node.comparators[0]
    return (isinstance(right, ast.Call) and isinstance(right.func, ast.Name)
            and right.func.id == "int" and len(right.args) == 1)


def _fix_int_should_be_len(node, ctx):
    right = node.comparators[0]
    arg_text = ctx.text(right.args[0])
    return [f"{ctx.text(node.left)} == len({arg_text})"]


# ---------------------------------------------------------------------------
# R5: X.isdigit() used instead of X in '47'
# ---------------------------------------------------------------------------
def _is_isdigit_call(node, ctx):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "isdigit" and len(node.args) == 0)


def _fix_isdigit_call(node, ctx):
    return [f"{ctx.text(node.func.value)} in '47'"]


# ---------------------------------------------------------------------------
# R6: for loop body unconditionally increments a counter (counts length,
# not lucky digits). Wrap the increment in `if <loopvar> in '47':`.
# ---------------------------------------------------------------------------
def _is_naive_count_for(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if not isinstance(node.target, ast.Name):
        return False
    body = node.body
    if len(body) != 1:
        return False
    stmt = body[0]
    if not isinstance(stmt, ast.Assign) or len(stmt.targets) != 1:
        return False
    tgt = stmt.targets[0]
    if not isinstance(tgt, ast.Name):
        return False
    val = stmt.value
    if not (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)):
        return False
    return (isinstance(val.left, ast.Name) and val.left.id == tgt.id
            and isinstance(val.right, ast.Constant) and val.right.value == 1)


def _fix_naive_count_for(node, ctx):
    var_name = ctx.text(node.target)
    iter_text = ctx.text(node.iter)
    body_text = ctx.text(node.body[0])
    return [f"for {var_name} in {iter_text}:\n    if {var_name} in '47':\n        {body_text}"]


# ---------------------------------------------------------------------------
# R7: a while-digit-extraction loop compares the dividend variable itself
# to 4/7 instead of the freshly extracted digit variable.
# ---------------------------------------------------------------------------
def _find_digit_var(while_node, base_name):
    for stmt in while_node.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 and isinstance(stmt.targets[0], ast.Name):
            val = stmt.value
            if (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Mod)
                    and isinstance(val.left, ast.Name) and val.left.id == base_name
                    and stmt.targets[0].id != base_name):
                return stmt.targets[0].id
    return None


def _is_wrong_while_digit_var(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.Eq):
        return False
    left, right = node.left, node.comparators[0]
    if not (isinstance(right, ast.Constant) and right.value in (4, 7)):
        return False
    if not isinstance(left, ast.Name):
        return False
    w = _enclosing_while(node, ctx)
    if w is None:
        return False
    test_names = {n.id for n in ast.walk(w.test) if isinstance(n, ast.Name)}
    if left.id not in test_names:
        return False
    return _find_digit_var(w, left.id) is not None


def _fix_wrong_while_digit_var(node, ctx):
    w = _enclosing_while(node, ctx)
    digit_var = _find_digit_var(w, node.left.id)
    return [f"{digit_var} == {ctx.text(node.comparators[0])}"]


# ---------------------------------------------------------------------------
# R8: output case mistakes ("Yes"/"yes" -> "YES", "No"/"no" -> "NO")
# ---------------------------------------------------------------------------
def _is_bad_case_yes(node, ctx):
    return (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and node.value.lower() == "yes" and node.value != "YES")


def _fix_bad_case_yes(node, ctx):
    return ['"YES"']


def _is_bad_case_no(node, ctx):
    return (isinstance(node, ast.Constant) and isinstance(node.value, str)
            and node.value.lower() == "no" and node.value != "NO")


def _fix_bad_case_no(node, ctx):
    return ['"NO"']


# ---------------------------------------------------------------------------
# R9/R10: stray debug prints right after reading input, or trailing after
# the decision.
# ---------------------------------------------------------------------------
def _is_print_stmt(node):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name) and node.value.func.id == "print")


def _contains_input_call(val):
    for n in ast.walk(val):
        if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "input":
            return True
    return False


def _get_block_and_index(node, ctx):
    p = ctx.parent(node)
    if p is None or not hasattr(p, "body"):
        return None, None
    body = getattr(p, "body")
    if node not in body:
        return None, None
    return body, body.index(node)


def _is_debug_print_after_input(node, ctx):
    if not _is_print_stmt(node):
        return False
    if len(node.value.args) != 1 or not isinstance(node.value.args[0], ast.Name):
        return False
    body, idx = _get_block_and_index(node, ctx)
    if body is None or idx == 0:
        return False
    prev = body[idx - 1]
    if not (isinstance(prev, ast.Assign) and len(prev.targets) == 1
            and isinstance(prev.targets[0], ast.Name)):
        return False
    if prev.targets[0].id != node.value.args[0].id:
        return False
    return _contains_input_call(prev.value)


def _delete_stmt(node, ctx):
    return [""]


def _is_trailing_debug_print(node, ctx):
    if not _is_print_stmt(node):
        return False
    if len(node.value.args) != 1 or not isinstance(node.value.args[0], ast.Name):
        return False
    body, idx = _get_block_and_index(node, ctx)
    if body is None:
        return False
    if idx != len(body) - 1 or idx == 0:
        return False
    prev = body[idx - 1]
    return isinstance(prev, ast.If)


# ---------------------------------------------------------------------------
# R11: a duplicated .count("4") where a second count should use "7"
# ---------------------------------------------------------------------------
def _is_second_count4(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == "count"):
        return False
    if len(node.args) != 1 or not (isinstance(node.args[0], ast.Constant) and node.args[0].value == "4"):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Assign):
        return False
    body, idx = _get_block_and_index(parent, ctx)
    if body is None or idx == 0:
        return False
    prev = body[idx - 1]
    if not isinstance(prev, ast.Assign):
        return False
    pv = prev.value
    if not (isinstance(pv, ast.Call) and isinstance(pv.func, ast.Attribute) and pv.func.attr == "count"):
        return False
    if not (len(pv.args) == 1 and isinstance(pv.args[0], ast.Constant) and pv.args[0].value == "4"):
        return False
    return True


def _fix_second_count4(node, ctx):
    return [f"{ctx.text(node.func)}('7')"]


# ---------------------------------------------------------------------------
# R12: (count - len(x)) == 0  should be  count == 4 or count == 7
# ---------------------------------------------------------------------------
def _is_sub_len_eq_zero(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.Eq):
        return False
    left, right = node.left, node.comparators[0]
    if not (isinstance(right, ast.Constant) and right.value == 0):
        return False
    if not (isinstance(left, ast.BinOp) and isinstance(left.op, ast.Sub)):
        return False
    return _is_len_call(left.right)


def _fix_sub_len_eq_zero(node, ctx):
    sumexpr = ctx.text(node.left.left)
    return [f"{sumexpr} == 4 or {sumexpr} == 7"]


# ---------------------------------------------------------------------------
# R13: range(..., X-1) off-by-one, should be range(..., X)
# ---------------------------------------------------------------------------
def _is_range_len_minus1(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"):
        return False
    if len(node.args) == 1:
        arg = node.args[0]
    elif len(node.args) == 2:
        arg = node.args[1]
    else:
        return False
    return (isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Sub)
            and isinstance(arg.right, ast.Constant) and arg.right.value == 1)


def _fix_range_len_minus1(node, ctx):
    args = node.args
    if len(args) == 1:
        return [f"range({ctx.text(args[0].left)})"]
    else:
        return [f"range({ctx.text(args[0])}, {ctx.text(args[1].left)})"]


# ---------------------------------------------------------------------------
# R14: X % 4 == 0 or X % 7 == 0 should be X == 4 or X == 7
# ---------------------------------------------------------------------------
def _is_mod0(v, n):
    return (isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq)
            and isinstance(v.left, ast.BinOp) and isinstance(v.left.op, ast.Mod)
            and isinstance(v.left.right, ast.Constant) and v.left.right.value == n
            and isinstance(v.comparators[0], ast.Constant) and v.comparators[0].value == 0)


def _is_mod_check(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or) and len(node.values) == 2):
        return False
    v1, v2 = node.values
    if _is_mod0(v1, 4) and _is_mod0(v2, 7) and ctx.text(v1.left.left) == ctx.text(v2.left.left):
        return True
    if _is_mod0(v1, 7) and _is_mod0(v2, 4) and ctx.text(v1.left.left) == ctx.text(v2.left.left):
        return True
    return False


def _fix_mod_check(node, ctx):
    base = ctx.text(node.values[0].left.left)
    return [f"{base} == 4 or {base} == 7"]


# ---------------------------------------------------------------------------
# R15: tautological "X != 4 or X != 7" should be "X != 4 and X != 7"
# ---------------------------------------------------------------------------
def _is_ne(v, n):
    return (isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.NotEq)
            and isinstance(v.comparators[0], ast.Constant) and v.comparators[0].value == n)


def _is_tautological_or_noteq(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or) and len(node.values) == 2):
        return False
    v1, v2 = node.values
    if _is_ne(v1, 4) and _is_ne(v2, 7) and ctx.text(v1.left) == ctx.text(v2.left):
        return True
    if _is_ne(v1, 7) and _is_ne(v2, 4) and ctx.text(v1.left) == ctx.text(v2.left):
        return True
    return False


def _fix_tautological_or_noteq(node, ctx):
    texts = [ctx.text(v) for v in node.values]
    return [" and ".join(texts)]


# ---------------------------------------------------------------------------
# R16: bare literal in boolean condition, e.g. "x == 4 or 7"
# ---------------------------------------------------------------------------
def _is_bare_literal_or(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or) and len(node.values) == 2):
        return False
    v1, v2 = node.values

    def is_plain_int(x):
        return isinstance(x, ast.Constant) and isinstance(x.value, int) and not isinstance(x.value, bool)

    if isinstance(v1, ast.Compare) and len(v1.ops) == 1 and is_plain_int(v2):
        return True
    if isinstance(v2, ast.Compare) and len(v2.ops) == 1 and is_plain_int(v1):
        return True
    return False


def _fix_bare_literal_or(node, ctx):
    v1, v2 = node.values
    if isinstance(v1, ast.Compare):
        comp, lit = v1, v2
    else:
        comp, lit = v2, v1
    left_text = ctx.text(comp.left)
    op_text = " == " if isinstance(comp.ops[0], ast.Eq) else " != "
    return [f"{ctx.text(comp)} or {left_text}{op_text}{ctx.text(lit)}"]


# ---------------------------------------------------------------------------
# R17: n == (4 or 7)  should be  n == 4 or n == 7
# ---------------------------------------------------------------------------
def _is_eq_to_or_literal(node, ctx):
    if not isinstance(node, ast.Compare) or len(node.ops) != 1:
        return False
    if not isinstance(node.ops[0], ast.Eq):
        return False
    right = node.comparators[0]
    if isinstance(right, ast.BoolOp) and isinstance(right.op, ast.Or) and len(right.values) == 2:
        v1, v2 = right.values
        return all(isinstance(v, ast.Constant) and v.value in (4, 7) for v in (v1, v2))
    return False


def _fix_eq_to_or_literal(node, ctx):
    left_text = ctx.text(node.left)
    right = node.comparators[0]
    parts = [f"{left_text} == {ctx.text(v)}" for v in right.values]
    return [" or ".join(parts)]


# ---------------------------------------------------------------------------
# R18: inverted membership test before an increment:
# "if X not in [...]: S += 1" should drop the negation.
# ---------------------------------------------------------------------------
def _is_inverted_count_if(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if len(node.body) != 1:
        return False
    stmt = node.body[0]
    is_incr = isinstance(stmt, ast.AugAssign) and isinstance(stmt.op, ast.Add)
    if not is_incr:
        return False
    test = node.test
    return isinstance(test, ast.Compare) and len(test.ops) == 1 and isinstance(test.ops[0], ast.NotIn)


def _fix_inverted_count_if(node, ctx):
    test = node.test
    left_text = ctx.text(test.left)
    comp_text = ctx.text(test.comparators[0])
    body_text = ctx.text(node.body[0])
    return [f"if {left_text} in {comp_text}:\n    {body_text}"]


# ---------------------------------------------------------------------------
# R19: float division by 10 instead of floor division (digit stripping)
# ---------------------------------------------------------------------------
def _is_float_div_by_10(node, ctx):
    return (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div)
            and isinstance(node.right, ast.Constant) and node.right.value == 10)


def _fix_float_div_by_10(node, ctx):
    return [f"{ctx.text(node.left)} // {ctx.text(node.right)}"]


# ---------------------------------------------------------------------------
# R20: redundant subscript using a stale counter instead of the loop var
# ---------------------------------------------------------------------------
def _is_redundant_subscript_in_for(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    val = node.value
    if not isinstance(val, ast.Name):
        return False
    p = ctx.parent(node)
    while p is not None and not isinstance(p, ast.For):
        if isinstance(p, (ast.FunctionDef, ast.Module)):
            return False
        p = ctx.parent(p)
    if p is None:
        return False
    if not (isinstance(p.iter, ast.Name) and p.iter.id == val.id and isinstance(p.target, ast.Name)):
        return False
    if isinstance(node.slice, ast.Name) and node.slice.id == p.target.id:
        return False
    return True


def _fix_redundant_subscript_in_for(node, ctx):
    p = ctx.parent(node)
    while not isinstance(p, ast.For):
        p = ctx.parent(p)
    return [ctx.text(p.target)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="digit_literal_mismatch", match=_is_digit_literal_mismatch,
                    replace=_fix_digit_literal_mismatch, symptoms=("wrong",)),
            Rewrite(name="assign_plus_typo", match=_is_assign_plus_typo,
                    replace=_fix_assign_plus_typo, symptoms=("wrong",)),
            Rewrite(name="count_eq_len_misconception", match=_is_count_eq_len,
                    replace=_fix_count_eq_len, symptoms=("wrong",)),
            Rewrite(name="int_should_be_len", match=_is_int_should_be_len,
                    replace=_fix_int_should_be_len, symptoms=("wrong",)),
            Rewrite(name="isdigit_should_be_in_47", match=_is_isdigit_call,
                    replace=_fix_isdigit_call, symptoms=("wrong",)),
            Rewrite(name="naive_count_for_wraps_if", match=_is_naive_count_for,
                    replace=_fix_naive_count_for, symptoms=("wrong",)),
            Rewrite(name="wrong_while_digit_var", match=_is_wrong_while_digit_var,
                    replace=_fix_wrong_while_digit_var, symptoms=("wrong",)),
            Rewrite(name="bad_case_yes", match=_is_bad_case_yes,
                    replace=_fix_bad_case_yes, symptoms=("wrong",)),
            Rewrite(name="bad_case_no", match=_is_bad_case_no,
                    replace=_fix_bad_case_no, symptoms=("wrong",)),
            Rewrite(name="debug_print_after_input", match=_is_debug_print_after_input,
                    replace=_delete_stmt, symptoms=("wrong",)),
            Rewrite(name="trailing_debug_print", match=_is_trailing_debug_print,
                    replace=_delete_stmt, symptoms=("wrong",)),
            Rewrite(name="duplicate_count4_should_be_7", match=_is_second_count4,
                    replace=_fix_second_count4, symptoms=("wrong",)),
            Rewrite(name="sub_len_eq_zero", match=_is_sub_len_eq_zero,
                    replace=_fix_sub_len_eq_zero, symptoms=("wrong",)),
            Rewrite(name="range_off_by_one_len_minus1", match=_is_range_len_minus1,
                    replace=_fix_range_len_minus1, symptoms=("wrong",)),
            Rewrite(name="mod_check_should_be_eq", match=_is_mod_check,
                    replace=_fix_mod_check, symptoms=("wrong",)),
            Rewrite(name="tautological_or_noteq", match=_is_tautological_or_noteq,
                    replace=_fix_tautological_or_noteq, symptoms=("wrong",)),
            Rewrite(name="bare_literal_or", match=_is_bare_literal_or,
                    replace=_fix_bare_literal_or, symptoms=("wrong",)),
            Rewrite(name="eq_to_or_literal", match=_is_eq_to_or_literal,
                    replace=_fix_eq_to_or_literal, symptoms=("wrong",)),
            Rewrite(name="inverted_count_if", match=_is_inverted_count_if,
                    replace=_fix_inverted_count_if, symptoms=("wrong",)),
            Rewrite(name="float_div_by_10", match=_is_float_div_by_10,
                    replace=_fix_float_div_by_10, symptoms=("wrong", "timeout")),
            Rewrite(name="redundant_subscript_in_for", match=_is_redundant_subscript_in_for,
                    replace=_fix_redundant_subscript_in_for, symptoms=("wrong",)),
        ]