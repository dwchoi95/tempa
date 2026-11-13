from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


NOARG_STR_METHODS = {
    'isupper', 'islower', 'istitle', 'isalpha',
    'upper', 'lower', 'capitalize', 'title', 'swapcase',
}


def _is_call_attr(node, name):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == name and not node.args and not node.keywords)


def _find_isupper_base(node):
    for v in ast.walk(node):
        if (isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute)
                and v.func.attr == 'isupper' and not v.args and not v.keywords):
            return v.func.value
    return None


# ---------------------------------------------------------------------------
# 1. .capitalize() is never the right transform for this task; .swapcase() is.
def _is_capitalize_call(node, ctx):
    return _is_call_attr(node, 'capitalize')


def _capitalize_to_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


# ---------------------------------------------------------------------------
# 2. .title() suffers from the same misconception as .capitalize().
def _is_title_call(node, ctx):
    return _is_call_attr(node, 'title')


def _title_to_swapcase(node, ctx):
    return [ctx.text(node.func.value) + ".swapcase()"]


# ---------------------------------------------------------------------------
# 3. "uppercase" is not a real str method (typo for "upper").
def _is_uppercase_typo(node, ctx):
    return isinstance(node, ast.Attribute) and node.attr == 'uppercase'


def _fix_uppercase_typo(node, ctx):
    return [ctx.text(node.value) + ".upper"]


# ---------------------------------------------------------------------------
# 4. A no-arg string-test method referenced without being called:
#    `x.isupper` used as a (always-truthy) value instead of `x.isupper()`.
def _is_bare_noarg_method(node, ctx):
    if not isinstance(node, ast.Attribute):
        return False
    if node.attr not in NOARG_STR_METHODS:
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        return False
    return True


def _add_call_parens(node, ctx):
    return [ctx.text(node) + "()"]


# ---------------------------------------------------------------------------
# 5. `word[1:].islower()` is (almost) always meant to be `.isupper()`
#    when checking "all letters except the first are uppercase".
def _is_islower_on_slice(node, ctx):
    if not _is_call_attr(node, 'islower'):
        return False
    base = node.func.value
    return isinstance(base, ast.Subscript) and isinstance(base.slice, ast.Slice)


def _islower_slice_to_isupper(node, ctx):
    return [ctx.text(node.func.value) + ".isupper()"]


# ---------------------------------------------------------------------------
# 6. `X.isupper() and Y.islower()` has the two checks the wrong way
#    round; the caps-lock rule needs "first lower AND rest upper".
def _is_isupper_and_islower(node, ctx):
    if not isinstance(node, ast.BoolOp) or not isinstance(node.op, ast.And):
        return False
    if len(node.values) != 2:
        return False
    a, b = node.values
    return _is_call_attr(a, 'isupper') and _is_call_attr(b, 'islower')


def _swap_isupper_islower(node, ctx):
    a, b = node.values
    a_base = ctx.text(a.func.value)
    b_base = ctx.text(b.func.value)
    return [a_base + ".islower() and " + b_base + ".isupper()"]


# ---------------------------------------------------------------------------
# 7. `.upper()`/`.lower()` called and the resulting (always truthy,
#    non-empty) string used directly as a boolean test, instead of
#    calling `.isupper()`/`.islower()`.
def _is_case_call_in_bool_context(node, ctx):
    if not (_is_call_attr(node, 'upper') or _is_call_attr(node, 'lower')):
        return False
    parent = ctx.parent(node)
    if parent is None:
        return False
    field = ctx.field(node)
    if isinstance(parent, (ast.If, ast.While)) and field == 'test':
        return True
    if isinstance(parent, ast.BoolOp) and field == 'values':
        return True
    if isinstance(parent, ast.UnaryOp) and isinstance(parent.op, ast.Not) and field == 'operand':
        return True
    return False


def _case_call_to_isX(node, ctx):
    name = 'isupper' if node.func.attr == 'upper' else 'islower'
    return [ctx.text(node.func.value) + "." + name + "()"]


# ---------------------------------------------------------------------------
# 8. `X[0].upper() + X[1:].lower()` is the long-hand (and subtly
#    wrong-in-general) way of writing `X.swapcase()`.
def _is_call_attr_on_subscript(node, attr):
    return _is_call_attr(node, attr) and isinstance(node.func.value, ast.Subscript)


def _is_concat_upper0_lower_rest(node, ctx):
    if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Add):
        return False
    left, right = node.left, node.right
    if not _is_call_attr_on_subscript(left, 'upper'):
        return False
    if not _is_call_attr_on_subscript(right, 'lower'):
        return False
    lbase = left.func.value.value
    rbase = right.func.value.value
    return ctx.text(lbase) == ctx.text(rbase)


def _concat_to_swapcase(node, ctx):
    base = ctx.text(node.left.func.value.value)
    return [base + ".swapcase()"]


# ---------------------------------------------------------------------------
# 9. `word[1:-1]` instead of `word[1:]` drops the last character by
#    mistake when checking/transforming "all but the first letter".
def _is_slice_1_to_neg1(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    sl = node.slice
    if not isinstance(sl, ast.Slice):
        return False
    if sl.lower is None or sl.upper is None or sl.step is not None:
        return False
    if not (isinstance(sl.lower, ast.Constant) and sl.lower.value == 1):
        return False
    upper = sl.upper
    return (isinstance(upper, ast.UnaryOp) and isinstance(upper.op, ast.USub)
            and isinstance(upper.operand, ast.Constant) and upper.operand.value == 1)


def _fix_slice_1_to_neg1(node, ctx):
    return [ctx.text(node.value) + "[1:]"]


# ---------------------------------------------------------------------------
# 10. The condition handles "all upper" / "first lower, rest upper" but
#     forgets the single-character special case entirely.
def _missing_len1_case(node, ctx):
    if not isinstance(node, ast.BoolOp) or not isinstance(node.op, ast.Or):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If) or parent.test is not node:
        return False
    text = ctx.text(node)
    if "len(" in text:
        return False
    if "isupper" not in text:
        return False
    return _find_isupper_base(node) is not None


def _add_len1_prefix(node, ctx):
    base = _find_isupper_base(node)
    if base is None:
        return []
    return ["len(" + ctx.text(base) + ") == 1 or " + ctx.text(node)]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="capitalize_should_be_swapcase",
                    match=_is_capitalize_call, replace=_capitalize_to_swapcase,
                    symptoms=("wrong",)),

            Rewrite(name="title_should_be_swapcase",
                    match=_is_title_call, replace=_title_to_swapcase,
                    symptoms=("wrong",)),

            Rewrite(name="uppercase_typo",
                    match=_is_uppercase_typo, replace=_fix_uppercase_typo,
                    symptoms=("err:AttributeError", "wrong")),

            Rewrite(name="missing_call_parens",
                    match=_is_bare_noarg_method, replace=_add_call_parens,
                    symptoms=("wrong",)),

            Rewrite(name="islower_slice_should_be_isupper",
                    match=_is_islower_on_slice, replace=_islower_slice_to_isupper,
                    symptoms=("wrong",)),

            Rewrite(name="swapped_isupper_islower_and",
                    match=_is_isupper_and_islower, replace=_swap_isupper_islower,
                    symptoms=("wrong",)),

            Rewrite(name="case_call_used_as_bool_should_be_isX",
                    match=_is_case_call_in_bool_context, replace=_case_call_to_isX,
                    symptoms=("wrong",)),

            Rewrite(name="concat_upper0_lower_rest_should_be_swapcase",
                    match=_is_concat_upper0_lower_rest, replace=_concat_to_swapcase,
                    symptoms=("wrong",)),

            Rewrite(name="slice_1_to_neg1_drops_last_char",
                    match=_is_slice_1_to_neg1, replace=_fix_slice_1_to_neg1,
                    symptoms=("wrong",)),

            Rewrite(name="condition_missing_single_char_case",
                    match=_missing_len1_case, replace=_add_len1_prefix,
                    symptoms=("wrong", "err:IndexError")),
        ]