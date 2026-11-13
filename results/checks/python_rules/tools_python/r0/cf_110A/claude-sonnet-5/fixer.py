from src.core.repair import Rule
import ast

from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _is_int_const(n, values):
    return isinstance(n, ast.Constant) and isinstance(n.value, int) and n.value in values


def _find_ancestor(node, ctx, kinds, limit=60):
    cur = node
    for _ in range(limit):
        cur = ctx.parent(cur)
        if cur is None:
            return None
        if isinstance(cur, kinds):
            return cur
    return None


# ---------------------------------------------------------------------------
# 1. Comparing a per-character loop variable to an int literal 4/7 instead
#    of the string '4'/'7'.
# ---------------------------------------------------------------------------

def _is_char_loopvar_int_eq(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)):
        return False
    comp = node.comparators[0]
    if not _is_int_const(comp, (4, 7)):
        return False
    left = node.left
    if not isinstance(left, (ast.Name, ast.Subscript)):
        return False
    loop = _find_ancestor(node, ctx, (ast.For,))
    if loop is None:
        return False
    if isinstance(left, ast.Name):
        tgt = loop.target
        return isinstance(tgt, ast.Name) and tgt.id == left.id
    return True  # subscript access inside a for-loop: almost certainly char access


def _fix_char_loopvar_int_eq(node, ctx):
    comp = node.comparators[0]
    s = "'4'" if comp.value == 4 else "'7'"
    return [ctx.text(node.left) + " == " + s]


# ---------------------------------------------------------------------------
# 2. Wrong output literal spellings ("Yes"/"yes"/"si"/"No"/"no") instead of
#    the required "YES"/"NO".
# ---------------------------------------------------------------------------

_YES_WORDS = {"yes", "si"}
_NO_WORDS = {"no"}


def _is_yesno_const(node, ctx):
    if not (isinstance(node, ast.Constant) and isinstance(node.value, str)):
        return False
    v = node.value
    if v.lower() in _YES_WORDS and v != "YES":
        return True
    if v.lower() in _NO_WORDS and v != "NO":
        return True
    return False


def _fix_yesno_const(node, ctx):
    if node.value.lower() in _YES_WORDS:
        return ['"YES"']
    return ['"NO"']


# ---------------------------------------------------------------------------
# 3. `x == (4 or 7)` always evaluates the parenthesised `or` to its first
#    truthy operand; expand into two comparisons.
# ---------------------------------------------------------------------------

def _is_compare_to_boolop(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)
            and isinstance(node.comparators[0], ast.BoolOp)
            and isinstance(node.comparators[0].op, ast.Or))


def _fix_compare_to_boolop(node, ctx):
    left_text = ctx.text(node.left)
    parts = [left_text + " == " + ctx.text(v) for v in node.comparators[0].values]
    return [" or ".join(parts)]


# ---------------------------------------------------------------------------
# 4. `cond == 4 or 7` (bare literal in a boolean chain) -- the bare literal
#    needs to become another comparison against the same left-hand value.
# ---------------------------------------------------------------------------

def _sibling_eq_compare(parent, node):
    for v in parent.values:
        if v is not node and isinstance(v, ast.Compare) and len(v.ops) == 1 \
                and isinstance(v.ops[0], ast.Eq):
            return v
    return None


def _is_bare_const_in_boolop(node, ctx):
    if not _is_int_const(node, (4, 7)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.BoolOp):
        return False
    if node not in parent.values:
        return False
    return _sibling_eq_compare(parent, node) is not None


def _fix_bare_const_in_boolop(node, ctx):
    parent = ctx.parent(node)
    sib = _sibling_eq_compare(parent, node)
    if sib is None:
        return []
    left_text = ctx.text(sib.left)
    return [left_text + " == " + ctx.text(node)]


# ---------------------------------------------------------------------------
# 5. Using `count % 4 == 0 or count % 7 == 0` instead of
#    `count == 4 or count == 7`.
# ---------------------------------------------------------------------------

def _mod_zero(v, n):
    return (isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq)
            and isinstance(v.left, ast.BinOp) and isinstance(v.left.op, ast.Mod)
            and isinstance(v.left.right, ast.Constant) and v.left.right.value == n
            and isinstance(v.comparators[0], ast.Constant) and v.comparators[0].value == 0)


def _is_mod_check_boolop(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or)
            and len(node.values) == 2):
        return False
    v1, v2 = node.values
    if _mod_zero(v1, 4) and _mod_zero(v2, 7):
        return ctx.text(v1.left.left) == ctx.text(v2.left.left)
    if _mod_zero(v1, 7) and _mod_zero(v2, 4):
        return ctx.text(v1.left.left) == ctx.text(v2.left.left)
    return False


def _fix_mod_check_boolop(node, ctx):
    x = ctx.text(node.values[0].left.left)
    return [x + " == 4 or " + x + " == 7"]


# ---------------------------------------------------------------------------
# 6. `count =+ 1` (typo for `count += 1`).
# ---------------------------------------------------------------------------

def _is_assign_unary_plus(node, ctx):
    return (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)
            and isinstance(node.value, ast.UnaryOp) and isinstance(node.value.op, ast.UAdd))


def _fix_assign_unary_plus(node, ctx):
    name = ctx.text(node.targets[0])
    operand = ctx.text(node.value.operand)
    return [name + " += " + operand]


# ---------------------------------------------------------------------------
# 7. Inside a digit-extraction while loop, comparing the whole shrinking
#    number instead of the freshly extracted digit.
# ---------------------------------------------------------------------------

def _digit_extractor(stmt, xname):
    if not (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)):
        return None
    tgt = stmt.targets[0].id
    val = stmt.value
    if tgt == xname:
        return None
    if (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Mod)
            and isinstance(val.left, ast.Name) and val.left.id == xname
            and isinstance(val.right, ast.Constant) and val.right.value == 10):
        return tgt
    return None


def _is_digit_misuse_compare(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)):
        return False
    if not isinstance(node.left, ast.Name):
        return False
    if not _is_int_const(node.comparators[0], (4, 7)):
        return False
    loop = _find_ancestor(node, ctx, (ast.While,))
    if loop is None:
        return False
    xname = node.left.id
    for stmt in ast.walk(loop):
        if _digit_extractor(stmt, xname):
            return True
    return False


def _fix_digit_misuse_compare(node, ctx):
    loop = _find_ancestor(node, ctx, (ast.While,))
    xname = node.left.id
    for stmt in ast.walk(loop):
        d = _digit_extractor(stmt, xname)
        if d:
            return [d + " == " + ctx.text(node.comparators[0])]
    return []


# ---------------------------------------------------------------------------
# 8. `counter == len(something)` instead of `counter == 4 or counter == 7`
#    (checking "all digits lucky" instead of "lucky digit count is lucky").
# ---------------------------------------------------------------------------

def _is_len_call(n):
    return isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "len"


def _is_count_eq_len(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)):
        return False
    left, right = node.left, node.comparators[0]
    if isinstance(left, ast.Name) and _is_len_call(right):
        return True
    if isinstance(right, ast.Name) and _is_len_call(left):
        return True
    return False


def _fix_count_eq_len(node, ctx):
    left, right = node.left, node.comparators[0]
    if isinstance(left, ast.Name) and _is_len_call(right):
        v = ctx.text(left)
    else:
        v = ctx.text(right)
    return [v + " == 4 or " + v + " == 7"]


# ---------------------------------------------------------------------------
# 9. `len(x) == 4` / `len(x) == 7` used as the whole check (checking string
#    length instead of counting lucky digits).
# ---------------------------------------------------------------------------

def _is_len_eq_47(node, ctx):
    if not _is_len_call(node):
        return False
    if len(node.args) != 1:
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Compare) and len(parent.ops) == 1
            and isinstance(parent.ops[0], ast.Eq)):
        return False
    if parent.left is not node:
        return False
    return _is_int_const(parent.comparators[0], (4, 7))


def _fix_len_eq_47(node, ctx):
    x = ctx.text(node.args[0])
    return ["(" + x + ".count('4') + " + x + ".count('7'))"]


# ---------------------------------------------------------------------------
# 10. Counting '4' twice instead of counting '4' and '7'.
# ---------------------------------------------------------------------------

def _is_count4_call(n):
    return (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
            and n.func.attr == "count" and len(n.args) == 1
            and isinstance(n.args[0], ast.Constant) and n.args[0].value == "4")


def _is_dup_count4(node, ctx):
    if not _is_count4_call(node):
        return False
    assign = ctx.parent(node)
    if not isinstance(assign, ast.Assign):
        return False
    holder = ctx.parent(assign)
    if holder is None or not hasattr(holder, "body"):
        return False
    body = holder.body
    try:
        idx = body.index(assign)
    except ValueError:
        return False
    if idx == 0:
        return False
    prev = body[idx - 1]
    if not isinstance(prev, ast.Assign):
        return False
    if not _is_count4_call(prev.value):
        return False
    return ctx.text(prev.value.func.value) == ctx.text(node.func.value)


def _fix_dup_count4(node, ctx):
    return [ctx.text(node.func.value) + '.count("7")']


# ---------------------------------------------------------------------------
# 11. `for ... : if lucky: count += 1  else: break` -- the else/break
#    terminates counting early; it should simply not exist.
# ---------------------------------------------------------------------------

def _is_if_else_break(node, ctx):
    return (isinstance(node, ast.If) and len(node.orelse) == 1
            and isinstance(node.orelse[0], ast.Break)
            and _find_ancestor(node, ctx, (ast.For, ast.While)) is not None)


def _fix_if_else_break(node, ctx):
    test_text = ctx.text(node.test)
    body_lines = [ctx.text(s) for s in node.body]
    joined = "\n    ".join(body_lines)
    return ["if " + test_text + ":\n    " + joined]


# ---------------------------------------------------------------------------
# 12. `if x == 4: ... elif x == 4: ...` (duplicated condition instead of
#    checking the other lucky value, 7).
# ---------------------------------------------------------------------------

def _is_dup_elif_test(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Eq)):
        return False
    if not _is_int_const(node.comparators[0], (4, 7)):
        return False
    parent_if = ctx.parent(node)
    if not (isinstance(parent_if, ast.If) and parent_if.test is node):
        return False
    grandparent = ctx.parent(parent_if)
    if not isinstance(grandparent, ast.If):
        return False
    if len(grandparent.orelse) != 1 or grandparent.orelse[0] is not parent_if:
        return False
    return ctx.text(grandparent.test) == ctx.text(node)


def _fix_dup_elif_test(node, ctx):
    other = 7 if node.comparators[0].value == 4 else 4
    return [ctx.text(node.left) + " == " + str(other)]


# ---------------------------------------------------------------------------
# 13. `is` used instead of `==` for literal comparison.
# ---------------------------------------------------------------------------

def _is_is_literal(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Is))


def _fix_is_literal(node, ctx):
    return [ctx.text(node.left) + " == " + ctx.text(node.comparators[0])]


# ---------------------------------------------------------------------------
# 14. Off-by-one `range(x - 1)` / `range(0, x - 1)` that drops the last
#    character.
# ---------------------------------------------------------------------------

def _is_range_off_by_one(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "range"):
        return False
    args = node.args
    if len(args) == 1:
        upper = args[0]
    elif len(args) == 2:
        upper = args[1]
    else:
        return False
    return (isinstance(upper, ast.BinOp) and isinstance(upper.op, ast.Sub)
            and isinstance(upper.right, ast.Constant) and upper.right.value == 1)


def _fix_range_off_by_one(node, ctx):
    args = node.args
    if len(args) == 1:
        new_upper = ctx.text(args[0].left)
        return ["range(" + new_upper + ")"]
    new_upper = ctx.text(args[1].left)
    return ["range(" + ctx.text(args[0]) + ", " + new_upper + ")"]


# ---------------------------------------------------------------------------

class Fixer:
    def rules(self):
        return [
            Rewrite(name="char_loopvar_int_literal_to_str",
                    match=_is_char_loopvar_int_eq,
                    replace=_fix_char_loopvar_int_eq,
                    symptoms=("wrong",)),

            Rewrite(name="yes_no_output_casing",
                    match=_is_yesno_const,
                    replace=_fix_yesno_const,
                    symptoms=("wrong",)),

            Rewrite(name="compare_to_parenthesised_or",
                    match=_is_compare_to_boolop,
                    replace=_fix_compare_to_boolop,
                    symptoms=("wrong",)),

            Rewrite(name="bare_const_in_boolop",
                    match=_is_bare_const_in_boolop,
                    replace=_fix_bare_const_in_boolop,
                    symptoms=("wrong",)),

            Rewrite(name="mod_check_instead_of_equality",
                    match=_is_mod_check_boolop,
                    replace=_fix_mod_check_boolop,
                    symptoms=("wrong",)),

            Rewrite(name="assign_unary_plus_instead_of_augassign",
                    match=_is_assign_unary_plus,
                    replace=_fix_assign_unary_plus,
                    symptoms=("wrong",)),

            Rewrite(name="digit_misuse_full_number_instead_of_digit",
                    match=_is_digit_misuse_compare,
                    replace=_fix_digit_misuse_compare,
                    symptoms=("wrong",)),

            Rewrite(name="count_eq_len_instead_of_47",
                    match=_is_count_eq_len,
                    replace=_fix_count_eq_len,
                    symptoms=("wrong",)),

            Rewrite(name="len_eq_47_should_count_lucky_digits",
                    match=_is_len_eq_47,
                    replace=_fix_len_eq_47,
                    symptoms=("wrong",)),

            Rewrite(name="duplicate_count4_should_be_count7",
                    match=_is_dup_count4,
                    replace=_fix_dup_count4,
                    symptoms=("wrong",)),

            Rewrite(name="if_else_break_removes_counter",
                    match=_is_if_else_break,
                    replace=_fix_if_else_break,
                    symptoms=("wrong",)),

            Rewrite(name="duplicate_elif_test_flip_literal",
                    match=_is_dup_elif_test,
                    replace=_fix_dup_elif_test,
                    symptoms=("wrong",)),

            Rewrite(name="is_comparison_to_eq",
                    match=_is_is_literal,
                    replace=_fix_is_literal,
                    symptoms=("wrong", "err:SyntaxWarning")),

            Rewrite(name="range_off_by_one",
                    match=_is_range_off_by_one,
                    replace=_fix_range_off_by_one,
                    symptoms=("wrong",)),
        ]