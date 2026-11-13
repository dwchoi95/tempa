from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


STRING_METHODS = {
    "isupper", "islower", "isalpha", "isdigit", "isalnum",
    "upper", "lower", "capitalize", "title", "swapcase",
}


def _const_eq(node, value):
    if node is None:
        return False
    if isinstance(node, ast.Constant):
        return node.value == value
    # fallback for very old ast shapes
    if hasattr(node, "n"):
        return node.n == value
    return False


def _is_rest_subscript(sub):
    """Matches X[1:], X[1::], X[1:len(X)] -- the 'rest of the word' slice."""
    if not isinstance(sub, ast.Subscript):
        return False
    s = sub.slice
    if hasattr(ast, "Index") and isinstance(s, ast.Index):
        s = s.value
    if not isinstance(s, ast.Slice):
        return False
    if not _const_eq(s.lower, 1):
        return False
    if s.upper is None:
        return True
    if isinstance(s.upper, ast.Call) and isinstance(s.upper.func, ast.Name) and s.upper.func.id == "len":
        return True
    return False


def _find_base_var(node):
    for n in ast.walk(node):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr in ("isupper", "islower", "upper", "lower")):
            base = n.func.value
            while isinstance(base, ast.Subscript):
                base = base.value
            if isinstance(base, ast.Name):
                return base.id
    return None


def _in_bool_context(node, ctx):
    parent = ctx.parent(node)
    if parent is None:
        return False
    if isinstance(parent, ast.BoolOp) and node in parent.values:
        return True
    if isinstance(parent, ast.UnaryOp) and isinstance(parent.op, ast.Not) and parent.operand is node:
        return True
    if isinstance(parent, (ast.If, ast.While)) and parent.test is node:
        return True
    if isinstance(parent, ast.IfExp) and parent.test is node:
        return True
    return False


# ---------------------------------------------------------------------------
# Rule 1: `.upper()`/`.lower()` used as a boolean test instead of
# `.isupper()`/`.islower()`.
# ---------------------------------------------------------------------------
def _is_upper_lower_call_bool(node, ctx):
    if not (isinstance(node, ast.Call) and not node.args and not node.keywords):
        return False
    if not (isinstance(node.func, ast.Attribute) and node.func.attr in ("upper", "lower")):
        return False
    return _in_bool_context(node, ctx)


def _replace_upper_lower_call_bool(node, ctx):
    newattr = "isupper" if node.func.attr == "upper" else "islower"
    base_text = ctx.text(node.func.value)
    return [f"{base_text}.{newattr}()"]


# ---------------------------------------------------------------------------
# Rule 2: bare method reference (missing parentheses), e.g. `x[1:].isupper`
# used directly as a truthy condition.
# ---------------------------------------------------------------------------
def _is_bare_predicate_attr(node, ctx):
    if not isinstance(node, ast.Attribute):
        return False
    if node.attr not in STRING_METHODS:
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        return False
    if isinstance(parent, ast.Attribute):
        return False
    return True


def _add_call_parens(node, ctx):
    return [ctx.text(node) + "()"]


# ---------------------------------------------------------------------------
# Rule 3: `.capitalize()`/`.title()` used as the "fix the case" action,
# where only `.swapcase()` is ever correct for this task.
# ---------------------------------------------------------------------------
def _is_capitalize_or_title_call(node, ctx):
    return (isinstance(node, ast.Call) and not node.args and not node.keywords
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in ("capitalize", "title"))


def _replace_capitalize_title(node, ctx):
    base_text = ctx.text(node.func.value)
    return [f"{base_text}.swapcase()"]


# ---------------------------------------------------------------------------
# Rule 4: an `or`-condition deciding whether to swap case, missing the
# `len(word) == 1` disjunct needed for single-letter inputs.
# ---------------------------------------------------------------------------
def _match_missing_len1(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or)):
        return False
    if ctx.field(node) != "test":
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If):
        return False
    compact = ctx.text(node).replace(" ", "")
    if "==1" in compact:
        return False
    return _find_base_var(node) is not None


def _replace_missing_len1(node, ctx):
    var = _find_base_var(node)
    return [ctx.text(node) + f" or len({var}) == 1"]


# ---------------------------------------------------------------------------
# Rule 5: `X[0].upper() + X[1:].lower()` used as the "swap" operation --
# only correct for one of the two trigger conditions; `.swapcase()` is
# correct for both.
# ---------------------------------------------------------------------------
def _is_first_upper_rest_lower(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    left, right = node.left, node.right
    if not (isinstance(left, ast.Call) and not left.args and not left.keywords
            and isinstance(left.func, ast.Attribute) and left.func.attr == "upper"):
        return False
    if not (isinstance(right, ast.Call) and not right.args and not right.keywords
            and isinstance(right.func, ast.Attribute) and right.func.attr == "lower"):
        return False
    lbase, rbase = left.func.value, right.func.value
    if not (isinstance(lbase, ast.Subscript) and isinstance(rbase, ast.Subscript)):
        return False
    lroot, rroot = lbase.value, rbase.value
    return (isinstance(lroot, ast.Name) and isinstance(rroot, ast.Name)
            and lroot.id == rroot.id)


def _replace_first_upper_rest_lower(node, ctx):
    root = node.left.func.value.value.id
    return [f"{root}.swapcase()"]


# ---------------------------------------------------------------------------
# Rule 6: `X[1:].isupper()` used as the (sole or partial) trigger condition.
# This fails for single-character words (empty slice -> isupper() is False).
# Rewriting to `X[1:].upper() == X[1:]` keeps the same meaning for non-empty
# slices while also being True (correctly) for the empty-slice case.
# ---------------------------------------------------------------------------
def _match_rest_isupper(node, ctx):
    return (isinstance(node, ast.Call) and not node.args and not node.keywords
            and isinstance(node.func, ast.Attribute) and node.func.attr == "isupper"
            and _is_rest_subscript(node.func.value))


def _replace_rest_isupper(node, ctx):
    base_text = ctx.text(node.func.value)
    return [f"{base_text}.upper() == {base_text}"]


# ---------------------------------------------------------------------------
# Rule 7: `X[1:].islower()` where `.isupper()` was meant -- this task never
# needs to check whether the "rest" of the word is lowercase.
# ---------------------------------------------------------------------------
def _match_rest_islower(node, ctx):
    return (isinstance(node, ast.Call) and not node.args and not node.keywords
            and isinstance(node.func, ast.Attribute) and node.func.attr == "islower"
            and _is_rest_subscript(node.func.value))


def _replace_rest_islower(node, ctx):
    base_text = ctx.text(node.func.value)
    return [f"{base_text}.isupper()"]


# ---------------------------------------------------------------------------
# Rule 8: a method call that "looks like" a mutation but strings are
# immutable, e.g. `x.capitalize()` as a bare statement with the result
# discarded.
# ---------------------------------------------------------------------------
def _is_bare_mutation_call(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and not node.value.args and not node.value.keywords
            and isinstance(node.value.func, ast.Attribute)
            and node.value.func.attr in ("swapcase", "capitalize", "title", "upper", "lower")
            and isinstance(node.value.func.value, ast.Name))


def _replace_bare_mutation(node, ctx):
    name = node.value.func.value.id
    return [f"{name} = {ctx.text(node.value)}"]


# ---------------------------------------------------------------------------
# Generic cheap slip: strict comparison that should be non-strict.
# ---------------------------------------------------------------------------
def _is_strict_lt(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Lt))


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="upper_lower_as_bool_to_is_check",
                    match=_is_upper_lower_call_bool,
                    replace=_replace_upper_lower_call_bool,
                    symptoms=("wrong",)),
            Rewrite(name="bare_predicate_missing_call",
                    match=_is_bare_predicate_attr,
                    replace=_add_call_parens,
                    symptoms=("wrong", "err:AttributeError")),
            Rewrite(name="capitalize_title_should_be_swapcase",
                    match=_is_capitalize_or_title_call,
                    replace=_replace_capitalize_title,
                    symptoms=("wrong",)),
            Rewrite(name="missing_len1_disjunct",
                    match=_match_missing_len1,
                    replace=_replace_missing_len1,
                    symptoms=("wrong",)),
            Rewrite(name="first_upper_rest_lower_should_be_swapcase",
                    match=_is_first_upper_rest_lower,
                    replace=_replace_first_upper_rest_lower,
                    symptoms=("wrong",)),
            Rewrite(name="rest_isupper_to_equality_form",
                    match=_match_rest_isupper,
                    replace=_replace_rest_isupper,
                    symptoms=("wrong",)),
            Rewrite(name="rest_islower_should_be_isupper",
                    match=_match_rest_islower,
                    replace=_replace_rest_islower,
                    symptoms=("wrong",)),
            Rewrite(name="bare_mutation_call_needs_assignment",
                    match=_is_bare_mutation_call,
                    replace=_replace_bare_mutation,
                    symptoms=("wrong",)),
            Rewrite(name="strict_lt_should_be_lte",
                    match=_is_strict_lt,
                    replace=_to_lte,
                    symptoms=("wrong",)),
        ]