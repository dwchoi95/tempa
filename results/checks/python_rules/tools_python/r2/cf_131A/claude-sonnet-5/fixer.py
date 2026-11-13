from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _is_zero_arg_call(node, attr):
    return (isinstance(node, ast.Call)
            and isinstance(node.func, ast.Attribute)
            and node.func.attr == attr
            and not node.args and not node.keywords)


def _in_bool_context(node, ctx):
    parent = ctx.parent(node)
    if parent is None:
        return False
    if isinstance(parent, (ast.If, ast.While)):
        try:
            return ctx.field(node) == 'test'
        except Exception:
            return parent.test is node
    if isinstance(parent, ast.BoolOp):
        return node in parent.values
    if isinstance(parent, ast.UnaryOp) and isinstance(parent.op, ast.Not):
        return parent.operand is node
    return False


# --- Rule 1: .capitalize() -> .swapcase() --------------------------------

def _match_capitalize(node, ctx):
    return _is_zero_arg_call(node, 'capitalize')


def _replace_capitalize(node, ctx):
    base = ctx.text(node.func.value)
    return [base + ".swapcase()"]


# --- Rule 2: .title() -> .swapcase() --------------------------------------

def _match_title(node, ctx):
    return _is_zero_arg_call(node, 'title')


def _replace_title(node, ctx):
    base = ctx.text(node.func.value)
    return [base + ".swapcase()"]


# --- Rule 3: bare isupper/islower/istitle attribute missing call parens ---

def _match_bare_is_check(node, ctx):
    if not isinstance(node, ast.Attribute):
        return False
    if node.attr not in ("isupper", "islower", "istitle"):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        return False
    return True


def _replace_bare_is_check(node, ctx):
    return [ctx.text(node) + "()"]


# --- Rule 4: .upper()/.lower() used as a boolean test -> .isupper() -------

def _match_case_call_bool(node, ctx):
    if not isinstance(node, ast.Call):
        return False
    if not isinstance(node.func, ast.Attribute):
        return False
    if node.func.attr not in ("upper", "lower"):
        return False
    if node.args or node.keywords:
        return False
    return _in_bool_context(node, ctx)


def _replace_case_call_bool(node, ctx):
    base = ctx.text(node.func.value)
    return [base + ".isupper()"]


# --- Rule 5: bare .upper/.lower attribute used as boolean test -----------

def _match_case_bare_bool(node, ctx):
    if not isinstance(node, ast.Attribute):
        return False
    if node.attr not in ("upper", "lower"):
        return False
    parent = ctx.parent(node)
    if isinstance(parent, ast.Call) and parent.func is node:
        return False
    return _in_bool_context(node, ctx)


def _replace_case_bare_bool(node, ctx):
    base = ctx.text(node.value)
    return [base + ".isupper()"]


# --- Rule 6: X.isupper() -> (X.upper() == X), fixes the empty-slice case --

def _match_isupper_call(node, ctx):
    return _is_zero_arg_call(node, 'isupper')


def _replace_isupper_call(node, ctx):
    base = ctx.text(node.func.value)
    return [f"({base}.upper() == {base})"]


# --- Rule 7: non-existent .uppercase()/.lowercase() typo methods ---------

def _match_bad_case_typo(node, ctx):
    return (_is_zero_arg_call(node, 'uppercase')
            or _is_zero_arg_call(node, 'lowercase'))


def _replace_bad_case_typo(node, ctx):
    base = ctx.text(node.func.value)
    newattr = "upper" if node.func.attr == "uppercase" else "lower"
    return [base + "." + newattr + "()"]


class Fixer:
    def rules(self):
        return [
            Rewrite(
                name="capitalize_should_be_swapcase",
                match=_match_capitalize,
                replace=_replace_capitalize,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="title_should_be_swapcase",
                match=_match_title,
                replace=_replace_title,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="bare_is_check_missing_call",
                match=_match_bare_is_check,
                replace=_replace_bare_is_check,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="bool_case_call_should_be_isupper",
                match=_match_case_call_bool,
                replace=_replace_case_call_bool,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="bool_case_bare_should_be_isupper_call",
                match=_match_case_bare_bool,
                replace=_replace_case_bare_bool,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="isupper_call_to_upper_equality",
                match=_match_isupper_call,
                replace=_replace_isupper_call,
                symptoms=("wrong",),
            ),
            Rewrite(
                name="uppercase_lowercase_typo",
                match=_match_bad_case_typo,
                replace=_replace_bad_case_typo,
                symptoms=("wrong", "err:AttributeError"),
            ),
        ]