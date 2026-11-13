from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _unwrap_slice(s):
    if isinstance(s, ast.Index):
        return s.value
    return s


def _find_enclosing_for(node, ctx):
    cur = node
    while True:
        p = ctx.parent(cur)
        if p is None:
            return None
        if isinstance(p, ast.For):
            return p
        cur = p


# ---------------------------------------------------------------------
# 1. `count =+ 1` typo (Assign with unary + instead of AugAssign +=)
# ---------------------------------------------------------------------
def _is_uadd_typo(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1):
        return False
    if not isinstance(node.targets[0], ast.Name):
        return False
    val = node.value
    return isinstance(val, ast.UnaryOp) and isinstance(val.op, ast.UAdd)


def _fix_uadd_typo(node, ctx):
    name = ctx.text(node.targets[0])
    operand = ctx.text(node.value.operand)
    return [f"{name} += {operand}"]


# ---------------------------------------------------------------------
# 2. `.isdigit()` used instead of checking for '4'/'7'
# ---------------------------------------------------------------------
def _is_isdigit_misuse(node, ctx):
    return (isinstance(node, ast.Call) and len(node.args) == 0
            and isinstance(node.func, ast.Attribute) and node.func.attr == "isdigit")


def _fix_isdigit_misuse(node, ctx):
    base = ctx.text(node.func.value)
    return [f"({base} == '4' or {base} == '7')"]


# ---------------------------------------------------------------------
# 3. Indexing the iterable with a stale index variable instead of the
#    loop variable itself (e.g. `for i in n: ... n[f] ...` where f never
#    changes).
# ---------------------------------------------------------------------
def _is_stale_index_subscript(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    if not isinstance(node.value, ast.Name):
        return False
    for_node = _find_enclosing_for(node, ctx)
    if for_node is None:
        return False
    if not isinstance(for_node.target, ast.Name):
        return False
    if not isinstance(for_node.iter, ast.Name):
        return False
    if for_node.iter.id != node.value.id:
        return False
    if for_node.target.id == node.value.id:
        return False
    sl = _unwrap_slice(node.slice)
    if isinstance(sl, ast.Name) and sl.id == for_node.target.id:
        return False
    if not isinstance(sl, ast.Name):
        return False
    return True


def _fix_stale_index_subscript(node, ctx):
    for_node = _find_enclosing_for(node, ctx)
    return [for_node.target.id]


# ---------------------------------------------------------------------
# 4. `int(x / 10)` loses precision for huge ints; should be `x // 10`.
# ---------------------------------------------------------------------
def _is_int_div10(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "int"):
        return False
    if len(node.args) != 1:
        return False
    arg = node.args[0]
    if not (isinstance(arg, ast.BinOp) and isinstance(arg.op, ast.Div)):
        return False
    right = arg.right
    return isinstance(right, ast.Constant) and right.value == 10


def _fix_int_div10(node, ctx):
    arg = node.args[0]
    return [f"{ctx.text(arg.left)} // 10"]


# ---------------------------------------------------------------------
# 5. `count == len(x)` (or `len(x) == count`) should be `count == 4 or
#    count == 7`.
# ---------------------------------------------------------------------
def _is_len_call(n):
    return isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "len"


def _is_count_eq_len(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    left, right = node.left, node.comparators[0]
    if _is_len_call(right) and not _is_len_call(left):
        return True
    if _is_len_call(left) and not _is_len_call(right):
        return True
    return False


def _fix_count_eq_len(node, ctx):
    left, right = node.left, node.comparators[0]
    var = ctx.text(left) if _is_len_call(right) else ctx.text(right)
    return [f"{var} == 4 or {var} == 7"]


# ---------------------------------------------------------------------
# 6. `len(a) == len(b)` should check the filtered-count side against 4/7.
# ---------------------------------------------------------------------
def _is_len_eq_len(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    return _is_len_call(node.left) and _is_len_call(node.comparators[0])


def _fix_len_eq_len(node, ctx):
    right = node.comparators[0]
    text = ctx.text(right)
    return [f"{text} == 4 or {text} == 7"]


# ---------------------------------------------------------------------
# 7. `X == A or B` (missing repeated comparison) -> `X == A or X == B`.
#    Also handles `X != A or B`.
# ---------------------------------------------------------------------
def _is_or_bare_literal(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or) and len(node.values) == 2):
        return False
    first, second = node.values
    if not (isinstance(first, ast.Compare) and len(first.ops) == 1):
        return False
    if not isinstance(first.ops[0], (ast.Eq, ast.NotEq)):
        return False
    return isinstance(second, ast.Constant)


def _fix_or_bare_literal(node, ctx):
    first, second = node.values
    left_text = ctx.text(first.left)
    op_text = "==" if isinstance(first.ops[0], ast.Eq) else "!="
    return [f"{left_text} {op_text} {ctx.text(first.comparators[0])} or {left_text} {op_text} {ctx.text(second)}"]


# ---------------------------------------------------------------------
# 8. Comparing a character (loop variable over a string) to an int
#    literal 4/7 instead of the string '4'/'7'.
# ---------------------------------------------------------------------
def _is_digit_compare_int(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    right = node.comparators[0]
    if not (isinstance(right, ast.Constant) and type(right.value) is int and right.value in (4, 7)):
        return False
    left = node.left
    for_node = _find_enclosing_for(node, ctx)
    if for_node is None or not isinstance(for_node.target, ast.Name):
        return False
    if isinstance(left, ast.Name) and for_node.target.id == left.id:
        return True
    if isinstance(left, ast.Subscript):
        sl = _unwrap_slice(left.slice)
        if isinstance(sl, ast.Name) and for_node.target.id == sl.id:
            return True
    return False


def _fix_digit_compare_int(node, ctx):
    right = node.comparators[0]
    return [f"{ctx.text(node.left)} == '{right.value}'"]


# ---------------------------------------------------------------------
# 9. Stray debug print() statements that leak extra output lines.
# ---------------------------------------------------------------------
_YESNO_WORDS = ("yes", "no", "si", "YES", "NO")


def _is_debug_print(node, ctx):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    call = node.value
    if not (isinstance(call.func, ast.Name) and call.func.id == "print"):
        return False
    text = ctx.text(call)
    for w in _YESNO_WORDS:
        if w in text:
            return False
    return True


def _fix_debug_print(node, ctx):
    return [""]


# ---------------------------------------------------------------------
# 10. Wrong-case / wrong-language YES/NO literal.
# ---------------------------------------------------------------------
_CASE_MAP = {"yes": "YES", "no": "NO", "si": "YES"}


def _is_wrong_case_yesno(node, ctx):
    if not (isinstance(node, ast.Constant) and isinstance(node.value, str)):
        return False
    key = node.value.strip().lower()
    if key not in _CASE_MAP:
        return False
    return node.value != _CASE_MAP[key]


def _fix_wrong_case_yesno(node, ctx):
    key = node.value.strip().lower()
    return [repr(_CASE_MAP[key])]


# ---------------------------------------------------------------------
# 11. De Morgan slip: `X != A or X != B` is always true; should be `and`.
# ---------------------------------------------------------------------
def _is_bad_demorgan(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or) and len(node.values) == 2):
        return False
    a, b = node.values

    def is_ne(x):
        return isinstance(x, ast.Compare) and len(x.ops) == 1 and isinstance(x.ops[0], ast.NotEq)

    if not (is_ne(a) and is_ne(b)):
        return False
    return ctx.text(a.left) == ctx.text(b.left)


def _fix_bad_demorgan(node, ctx):
    a, b = node.values
    return [ctx.text(a) + " and " + ctx.text(b)]


# ---------------------------------------------------------------------
# 12. `x == (4 or 7)` always reduces to `x == 4`; expand to full check.
# ---------------------------------------------------------------------
def _is_eq_or_literal_tuple(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    right = node.comparators[0]
    if not (isinstance(right, ast.BoolOp) and isinstance(right.op, ast.Or)):
        return False
    return all(isinstance(v, ast.Constant) for v in right.values)


def _fix_eq_or_literal_tuple(node, ctx):
    right = node.comparators[0]
    left_text = ctx.text(node.left)
    parts = [f"{left_text} == {ctx.text(v)}" for v in right.values]
    return [" or ".join(parts)]


# ---------------------------------------------------------------------
# 13. `x not in ["4", "7"]` used while counting lucky digits (should be
#     `in`, the student inverted the membership test).
# ---------------------------------------------------------------------
def _is_not_in_47_list(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.NotIn)):
        return False
    comp = node.comparators[0]
    if not isinstance(comp, (ast.List, ast.Tuple, ast.Set)):
        return False
    vals = comp.elts
    if len(vals) != 2:
        return False
    return all(isinstance(v, ast.Constant) and v.value in ("4", "7") for v in vals)


def _fix_not_in_47_list(node, ctx):
    return [ctx.text(node.left) + " in " + ctx.text(node.comparators[0])]


# ---------------------------------------------------------------------
# 14. Final if/else whose branches print something other than a plain
#     YES/NO literal (e.g. an f-string message) -> normalize to YES/NO.
# ---------------------------------------------------------------------
def _complex_message(call):
    if len(call.args) != 1:
        return True
    return not isinstance(call.args[0], ast.Constant)


def _get_print_call(stmt):
    if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Name) and stmt.value.func.id == "print"):
        return stmt.value
    return None


def _is_nonstandard_yesno_if(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if len(node.body) != 1 or len(node.orelse) != 1:
        return False
    c1 = _get_print_call(node.body[0])
    c2 = _get_print_call(node.orelse[0])
    if c1 is None or c2 is None:
        return False
    return _complex_message(c1) or _complex_message(c2)


def _fix_nonstandard_yesno_if(node, ctx):
    test_text = ctx.text(node.test)
    return [f"if {test_text}:\n    print(\"YES\")\nelse:\n    print(\"NO\")"]


# ---------------------------------------------------------------------
# 15. Off-by-one `range(..., s - 1)` misses the last character.
# ---------------------------------------------------------------------
def _is_range_off_by_one(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "range"):
        return False
    if len(node.args) not in (1, 2):
        return False
    last = node.args[-1]
    return (isinstance(last, ast.BinOp) and isinstance(last.op, ast.Sub)
            and isinstance(last.right, ast.Constant) and last.right.value == 1)


def _fix_range_off_by_one(node, ctx):
    args = list(node.args)
    last = args[-1]
    args[-1] = last.left
    args_text = ", ".join(ctx.text(a) for a in args)
    return [f"range({args_text})"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="uadd_typo_should_be_augassign", match=_is_uadd_typo,
                    replace=_fix_uadd_typo, symptoms=("wrong",)),
            Rewrite(name="isdigit_misuse_for_lucky_check", match=_is_isdigit_misuse,
                    replace=_fix_isdigit_misuse, symptoms=("wrong",)),
            Rewrite(name="stale_index_subscript", match=_is_stale_index_subscript,
                    replace=_fix_stale_index_subscript, symptoms=("wrong", "timeout")),
            Rewrite(name="int_div10_should_be_floordiv", match=_is_int_div10,
                    replace=_fix_int_div10, symptoms=("wrong",)),
            Rewrite(name="count_eq_len_should_be_lucky_check", match=_is_count_eq_len,
                    replace=_fix_count_eq_len, symptoms=("wrong",)),
            Rewrite(name="len_eq_len_should_be_lucky_check", match=_is_len_eq_len,
                    replace=_fix_len_eq_len, symptoms=("wrong",)),
            Rewrite(name="or_bare_literal_missing_comparison", match=_is_or_bare_literal,
                    replace=_fix_or_bare_literal, symptoms=("wrong",)),
            Rewrite(name="digit_compare_int_should_be_str", match=_is_digit_compare_int,
                    replace=_fix_digit_compare_int, symptoms=("wrong",)),
            Rewrite(name="remove_stray_debug_print", match=_is_debug_print,
                    replace=_fix_debug_print, symptoms=("wrong",)),
            Rewrite(name="wrong_case_or_language_yesno", match=_is_wrong_case_yesno,
                    replace=_fix_wrong_case_yesno, symptoms=("wrong",)),
            Rewrite(name="bad_demorgan_or_should_be_and", match=_is_bad_demorgan,
                    replace=_fix_bad_demorgan, symptoms=("wrong",)),
            Rewrite(name="eq_or_literal_tuple_always_true", match=_is_eq_or_literal_tuple,
                    replace=_fix_eq_or_literal_tuple, symptoms=("wrong",)),
            Rewrite(name="not_in_47_list_inverted", match=_is_not_in_47_list,
                    replace=_fix_not_in_47_list, symptoms=("wrong",)),
            Rewrite(name="nonstandard_yesno_message", match=_is_nonstandard_yesno_if,
                    replace=_fix_nonstandard_yesno_if, symptoms=("wrong",)),
            Rewrite(name="range_off_by_one", match=_is_range_off_by_one,
                    replace=_fix_range_off_by_one, symptoms=("wrong",)),
        ]