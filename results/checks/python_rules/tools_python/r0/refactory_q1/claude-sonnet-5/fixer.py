from src.core.repair import Rule
"""
Repair rules for the "Sequential Search" assignment.

Each Rewrite below targets one narrow, local misconception seen across many
buggy submissions (empty-sequence handling, strict/non-strict comparison
confusion, off-by-one additions/subtractions, misattached if/else, forward
references to not-yet-defined variables, etc).  Rules are intentionally small
and composable: the harness searches over repeated applications, so several
small edits chain together to fix a single submission.
"""

import ast
import builtins as _builtins_mod

from src.core.rewrite import Rewrite

_BUILTIN_NAMES = set(dir(_builtins_mod))


# --------------------------------------------------------------------------
# helpers
# --------------------------------------------------------------------------

def _enclosing_func(node, ctx):
    n = node
    while True:
        p = ctx.parent(n)
        if p is None:
            return None
        if isinstance(p, ast.FunctionDef):
            return p
        n = p


def _const_val(n):
    if isinstance(n, ast.Constant):
        return n.value
    if hasattr(ast, "Num") and isinstance(n, ast.Num):
        return n.n
    return None


def _slice_text(ctx, node):
    sl = node.slice
    if hasattr(ast, "Index") and isinstance(sl, ast.Index):
        sl = sl.value
    return ctx.text(sl)


def _looks_like_empty_check(text):
    t = text.replace(" ", "")
    keys = ["==[]", "==()", "len(seq)==0", "notseq", "ifseq:", "lenseq)==0"]
    return any(k in t for k in keys)


def _second_param_name(func, default="seq"):
    if func is not None and len(func.args.args) >= 2:
        return func.args.args[1].arg
    return default


# --------------------------------------------------------------------------
# 1. empty-sequence guard missing
# --------------------------------------------------------------------------

def _first_real_stmt(func):
    body = func.body
    idx = 0
    if body and isinstance(body[0], ast.Expr) and isinstance(
        body[0].value, (ast.Constant, getattr(ast, "Str", ast.Constant))
    ):
        idx = 1
    return body[idx] if idx < len(body) else None


def _needs_empty_guard(node, ctx):
    func = _enclosing_func(node, ctx)
    if func is None or func.name != "search":
        return False
    target = _first_real_stmt(func)
    if target is not node:
        return False
    full_text = ctx.text(func)
    if _looks_like_empty_check(full_text):
        return False
    return True


def _add_empty_guard(node, ctx):
    return ["if not seq:\n    return 0\n" + ctx.text(node)]


# --------------------------------------------------------------------------
# 2. forward reference to a variable defined later via `X = list(seq)`
# --------------------------------------------------------------------------

def _is_forward_ref_name(node, ctx):
    if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
        return False
    func = _enclosing_func(node, ctx)
    if func is None:
        return False
    node_line = getattr(node, "lineno", None)
    if node_line is None:
        return False
    for stmt in ast.walk(func):
        if (
            isinstance(stmt, ast.Assign)
            and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)
            and stmt.targets[0].id == node.id
            and stmt.lineno > node_line
        ):
            val = stmt.value
            if (
                isinstance(val, ast.Call)
                and isinstance(val.func, ast.Name)
                and val.func.id == "list"
                and len(val.args) == 1
            ):
                return True
    return False


def _fix_forward_ref_name(node, ctx):
    func = _enclosing_func(node, ctx)
    for stmt in ast.walk(func):
        if (
            isinstance(stmt, ast.Assign)
            and len(stmt.targets) == 1
            and isinstance(stmt.targets[0], ast.Name)
            and stmt.targets[0].id == node.id
            and stmt.lineno > node.lineno
        ):
            val = stmt.value
            if (
                isinstance(val, ast.Call)
                and isinstance(val.func, ast.Name)
                and val.func.id == "list"
                and len(val.args) == 1
            ):
                return [ctx.text(val.args[0])]
    return []


# --------------------------------------------------------------------------
# 3. comparison strictness / direction toggles involving `x`
# --------------------------------------------------------------------------

_CMP_SYMS = [
    (ast.Lt, "<"),
    (ast.LtE, "<="),
    (ast.Gt, ">"),
    (ast.GtE, ">="),
]


def _involves_x(node, ctx):
    try:
        lt = ctx.text(node.left).strip()
        rt = ctx.text(node.comparators[0]).strip()
    except Exception:
        return False
    return lt == "x" or rt == "x"


def _make_cmp_toggle(from_cls, to_symbol):
    def match(node, ctx):
        return (
            isinstance(node, ast.Compare)
            and len(node.ops) == 1
            and isinstance(node.ops[0], from_cls)
            and _involves_x(node, ctx)
        )

    def replace(node, ctx):
        return [ctx.text(node.left) + " " + to_symbol + " " + ctx.text(node.comparators[0])]

    return match, replace


# --------------------------------------------------------------------------
# 4. elem <= x <= elem + 1  ->  x <= elem
# --------------------------------------------------------------------------

def _is_elem_window_compare(node, ctx):
    return (
        isinstance(node, ast.Compare)
        and len(node.ops) == 2
        and isinstance(node.ops[0], (ast.Lt, ast.LtE))
        and isinstance(node.ops[1], (ast.Lt, ast.LtE))
        and isinstance(node.comparators[1], ast.BinOp)
        and isinstance(node.comparators[1].op, ast.Add)
    )


def _fix_elem_window_compare(node, ctx):
    return [ctx.text(node.comparators[0]) + " <= " + ctx.text(node.left)]


# --------------------------------------------------------------------------
# 5. dangling loop missing trailing `return len(seq)`
# --------------------------------------------------------------------------

def _is_dangling_loop(node, ctx):
    if not isinstance(node, (ast.For, ast.While)):
        return False
    func = _enclosing_func(node, ctx)
    if func is None or func.name != "search":
        return False
    return func.body and func.body[-1] is node


def _append_return_len(node, ctx):
    return [ctx.text(node) + "\nreturn len(seq)"]


# --------------------------------------------------------------------------
# 6. off-by-one add/sub constant 1 (generic removal)
# --------------------------------------------------------------------------

def _is_plus_one(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Add)
        and _const_val(node.right) == 1
    )


def _fix_remove_plus_one(node, ctx):
    return [ctx.text(node.left)]


def _is_minus_one(node, ctx):
    return (
        isinstance(node, ast.BinOp)
        and isinstance(node.op, ast.Sub)
        and _const_val(node.right) == 1
    )


def _fix_remove_minus_one(node, ctx):
    return [ctx.text(node.left)]


# --------------------------------------------------------------------------
# 7. call instead of subscript:  seq(i)  ->  seq[i]
# --------------------------------------------------------------------------

def _is_call_should_be_subscript(node, ctx):
    if not (
        isinstance(node, ast.Call)
        and isinstance(node.func, ast.Name)
        and len(node.args) == 1
        and not node.keywords
    ):
        return False
    func = _enclosing_func(node, ctx)
    second = _second_param_name(func, default=None)
    return second is not None and node.func.id == second


def _fix_call_should_be_subscript(node, ctx):
    return [ctx.text(node.func) + "[" + ctx.text(node.args[0]) + "]"]


# --------------------------------------------------------------------------
# 8. attribute subscript misuse:  seq.index[i]  ->  seq.index(i)
# --------------------------------------------------------------------------

def _is_attr_index_subscript(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.value, ast.Attribute)
        and node.value.attr == "index"
    )


def _fix_attr_index_subscript(node, ctx):
    return [ctx.text(node.value) + "(" + _slice_text(ctx, node) + ")"]


# --------------------------------------------------------------------------
# 9. malformed range/len loop headers
# --------------------------------------------------------------------------

def _is_bad_range_len(node, ctx):
    if not isinstance(node, ast.Call):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.For) and parent.iter is node):
        return False
    if isinstance(node.func, ast.Name) and node.func.id == "len" and len(node.args) == 1:
        return True
    if isinstance(node.func, ast.Name) and node.func.id == "range" and len(node.args) == 1:
        inner = node.args[0]
        if not (isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name) and inner.func.id == "len"):
            return True
    return False


def _fix_bad_range_len(node, ctx):
    if isinstance(node.func, ast.Name) and node.func.id == "len":
        inner = node.args[0]
        if (
            isinstance(inner, ast.Call)
            and isinstance(inner.func, ast.Name)
            and inner.func.id == "range"
            and len(inner.args) == 1
        ):
            return ["range(len(" + ctx.text(inner.args[0]) + "))"]
        return ["range(len(" + ctx.text(inner) + "))"]
    if isinstance(node.func, ast.Name) and node.func.id == "range":
        inner = node.args[0]
        return ["range(len(" + ctx.text(inner) + "))"]
    return []


# --------------------------------------------------------------------------
# 10. `len` mistakenly used as a sequence name for subscripting
# --------------------------------------------------------------------------

def _is_len_as_name_subscript(node, ctx):
    return (
        isinstance(node, ast.Subscript)
        and isinstance(node.value, ast.Name)
        and node.value.id == "len"
    )


def _fix_len_as_name_subscript(node, ctx):
    func = _enclosing_func(node, ctx)
    second = _second_param_name(func)
    return [second + "[" + _slice_text(ctx, node) + "]"]


# --------------------------------------------------------------------------
# 11. `X == 0` typo for assignment `X = 0`
# --------------------------------------------------------------------------

def _is_eq_as_assign(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    val = node.value
    return (
        isinstance(val, ast.Compare)
        and len(val.ops) == 1
        and isinstance(val.ops[0], ast.Eq)
        and isinstance(val.left, ast.Name)
    )


def _fix_eq_as_assign(node, ctx):
    val = node.value
    return [ctx.text(val.left) + " = " + ctx.text(val.comparators[0])]


# --------------------------------------------------------------------------
# 12. bare `sorted(seq)` call whose result is discarded
# --------------------------------------------------------------------------

def _is_bare_sorted_call(node, ctx):
    return (
        isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and isinstance(node.value.func, ast.Name)
        and node.value.func.id == "sorted"
        and len(node.value.args) == 1
        and isinstance(node.value.args[0], ast.Name)
    )


def _fix_bare_sorted_call(node, ctx):
    name = node.value.args[0].id
    return [name + " = " + ctx.text(node.value)]


# --------------------------------------------------------------------------
# 13. `X == [] or ()`-style always-true literal disjunction
# --------------------------------------------------------------------------

def _is_or_literal_truthy(node, ctx):
    if not (isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or)):
        return False
    return any(isinstance(v, (ast.List, ast.Tuple)) and not v.elts for v in node.values)


def _fix_or_literal_truthy(node, ctx):
    left_name = None
    for v in node.values:
        if isinstance(v, ast.Compare):
            left_name = v.left
            break
    parts = []
    for v in node.values:
        if isinstance(v, (ast.List, ast.Tuple)) and not v.elts:
            if left_name is None:
                return []
            parts.append(ctx.text(left_name) + " == " + ctx.text(v))
        else:
            parts.append(ctx.text(v))
    if len(parts) < 2:
        return []
    return [" or ".join(parts)]


# --------------------------------------------------------------------------
# 14. list(seq).index(max(seq)) missing the trailing +1
# --------------------------------------------------------------------------

def _is_index_max_call(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and node.func.attr == "index"):
        return False
    if not node.args:
        return False
    arg = node.args[0]
    if not (isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name) and arg.func.id == "max"):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.Return) and parent.value is node


def _fix_index_max_call(node, ctx):
    return [ctx.text(node) + " + 1"]


# --------------------------------------------------------------------------
# 15. bare `return` inside a loop meant to be `break`
# --------------------------------------------------------------------------

def _is_bare_return_in_loop(node, ctx):
    if not (isinstance(node, ast.Return) and node.value is None):
        return False
    p = ctx.parent(node)
    while p is not None and not isinstance(p, ast.FunctionDef):
        if isinstance(p, (ast.For, ast.While)):
            return True
        p = ctx.parent(p)
    return False


def _fix_bare_return_in_loop(node, ctx):
    return ["break"]


# --------------------------------------------------------------------------
# 16. `return x` where the loop index was meant
# --------------------------------------------------------------------------

def _is_return_x_should_be_index(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name) and node.value.id == "x"):
        return False
    func = _enclosing_func(node, ctx)
    if func is None or not func.args.args or func.args.args[0].arg != "x":
        return False
    n = node
    while True:
        p = ctx.parent(n)
        if p is None or isinstance(p, ast.FunctionDef):
            return False
        if isinstance(p, ast.For):
            return True
        n = p


def _fix_return_x_should_be_index(node, ctx):
    n = node
    while True:
        p = ctx.parent(n)
        if isinstance(p, ast.For):
            tgt = p.target
            if isinstance(tgt, ast.Name):
                return [tgt.id]
            if isinstance(tgt, ast.Tuple) and tgt.elts and isinstance(tgt.elts[0], ast.Name):
                return [tgt.elts[0].id]
            return []
        n = p


# --------------------------------------------------------------------------
# 17. `return seq` where `return 0` was meant
# --------------------------------------------------------------------------

def _is_return_seq_should_be_zero(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = _enclosing_func(node, ctx)
    if func is None or len(func.args.args) < 2:
        return False
    return node.value.id == func.args.args[1].arg


def _fix_return_seq_should_be_zero(node, ctx):
    return ["return 0"]


# --------------------------------------------------------------------------
# 18. `position += position` instead of `position += 1`
# --------------------------------------------------------------------------

def _is_self_doubling_augassign(node, ctx):
    return (
        isinstance(node, ast.AugAssign)
        and isinstance(node.op, ast.Add)
        and isinstance(node.target, ast.Name)
        and isinstance(node.value, ast.Name)
        and node.target.id == node.value.id
    )


def _fix_self_doubling_augassign(node, ctx):
    return [ctx.text(node.target) + " += 1"]


# --------------------------------------------------------------------------
# 19. while-loop counter used before being initialised
# --------------------------------------------------------------------------

def _is_uninitialized_while_var(node, ctx):
    if not isinstance(node, ast.While):
        return False
    func = _enclosing_func(node, ctx)
    if func is None or not func.body or func.body[0] is not node:
        return False
    param_names = {a.arg for a in func.args.args}
    for n in ast.walk(node.test):
        if isinstance(n, ast.Name) and n.id not in param_names:
            for s in ast.walk(node):
                if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name) and s.target.id == n.id:
                    return True
    return False


def _fix_uninitialized_while_var(node, ctx):
    func = _enclosing_func(node, ctx)
    param_names = {a.arg for a in func.args.args}
    for n in ast.walk(node.test):
        if isinstance(n, ast.Name) and n.id not in param_names:
            for s in ast.walk(node):
                if isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name) and s.target.id == n.id:
                    return [n.id + " = 0\n" + ctx.text(node)]
    return []


# --------------------------------------------------------------------------
# 20. first-statement empty-guard assigns instead of returning
# --------------------------------------------------------------------------

def _is_empty_branch_assign(node, ctx):
    if not isinstance(node, ast.Assign):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If):
        return False
    if len(parent.body) != 1 or parent.body[0] is not node:
        return False
    func = _enclosing_func(node, ctx)
    if func is None or not func.body or func.body[0] is not parent:
        return False
    return _looks_like_empty_check(ctx.text(parent.test))


def _fix_empty_branch_assign(node, ctx):
    return ["return 0"]


# --------------------------------------------------------------------------
# 21. misattached if/else: `if c: return i` / `else: return len(seq)`
#     where `else` should belong to the enclosing `for`, not the `if`.
# --------------------------------------------------------------------------

def _is_misattached_if_else(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if node.orelse:
        return False
    if len(node.body) != 1:
        return False
    inner = node.body[0]
    if not isinstance(inner, ast.If):
        return False
    if len(inner.orelse) != 1 or not isinstance(inner.orelse[0], ast.Return):
        return False
    return True


def _fix_misattached_if_else(node, ctx):
    inner = node.body[0]
    lines = []
    lines.append("for " + ctx.text(node.target) + " in " + ctx.text(node.iter) + ":")
    lines.append("    if " + ctx.text(inner.test) + ":")
    for s in inner.body:
        lines.append("        " + ctx.text(s))
    lines.append("else:")
    for s in inner.orelse:
        lines.append("    " + ctx.text(s))
    return ["\n".join(lines)]


# --------------------------------------------------------------------------
# 22. undefined name used where the sequence parameter was meant
# --------------------------------------------------------------------------

def _is_undefined_name(node, ctx):
    if not isinstance(node, ast.Name) or not isinstance(node.ctx, ast.Load):
        return False
    if node.id in _BUILTIN_NAMES:
        return False
    func = _enclosing_func(node, ctx)
    if func is None or len(func.args.args) < 2:
        return False
    if node.id in {a.arg for a in func.args.args}:
        return False
    assigned = set()
    for n in ast.walk(func):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name):
                    assigned.add(t.id)
        if isinstance(n, ast.For):
            for t in ast.walk(n.target):
                if isinstance(t, ast.Name):
                    assigned.add(t.id)
    if node.id in assigned:
        return False
    return True


def _fix_undefined_name(node, ctx):
    func = _enclosing_func(node, ctx)
    return [func.args.args[1].arg]


# --------------------------------------------------------------------------
# Fixer
# --------------------------------------------------------------------------

class Fixer:
    def rules(self):
        rules = [
            Rewrite(name="empty_guard_missing", match=_needs_empty_guard,
                    replace=_add_empty_guard, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="forward_ref_var", match=_is_forward_ref_name,
                    replace=_fix_forward_ref_name, symptoms=("wrong", "err:NameError")),
            Rewrite(name="elem_window_compare", match=_is_elem_window_compare,
                    replace=_fix_elem_window_compare, symptoms=("wrong",)),
            Rewrite(name="dangling_loop_missing_return", match=_is_dangling_loop,
                    replace=_append_return_len, symptoms=("wrong",)),
            Rewrite(name="remove_plus_one", match=_is_plus_one,
                    replace=_fix_remove_plus_one, symptoms=("wrong",)),
            Rewrite(name="remove_minus_one", match=_is_minus_one,
                    replace=_fix_remove_minus_one, symptoms=("wrong",)),
            Rewrite(name="call_should_be_subscript", match=_is_call_should_be_subscript,
                    replace=_fix_call_should_be_subscript, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="attr_index_subscript_misuse", match=_is_attr_index_subscript,
                    replace=_fix_attr_index_subscript, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="bad_range_len_header", match=_is_bad_range_len,
                    replace=_fix_bad_range_len, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="len_used_as_seq_name", match=_is_len_as_name_subscript,
                    replace=_fix_len_as_name_subscript, symptoms=("wrong", "err:TypeError")),
            Rewrite(name="eq_should_be_assign", match=_is_eq_as_assign,
                    replace=_fix_eq_as_assign, symptoms=("wrong", "err:NameError")),
            Rewrite(name="bare_sorted_discarded", match=_is_bare_sorted_call,
                    replace=_fix_bare_sorted_call, symptoms=("wrong",)),
            Rewrite(name="or_literal_always_true", match=_is_or_literal_truthy,
                    replace=_fix_or_literal_truthy, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="index_max_missing_plus_one", match=_is_index_max_call,
                    replace=_fix_index_max_call, symptoms=("wrong",)),
            Rewrite(name="bare_return_should_be_break", match=_is_bare_return_in_loop,
                    replace=_fix_bare_return_in_loop, symptoms=("wrong",)),
            Rewrite(name="return_x_should_be_index", match=_is_return_x_should_be_index,
                    replace=_fix_return_x_should_be_index, symptoms=("wrong",)),
            Rewrite(name="return_seq_should_be_zero", match=_is_return_seq_should_be_zero,
                    replace=_fix_return_seq_should_be_zero, symptoms=("wrong",)),
            Rewrite(name="self_doubling_augassign", match=_is_self_doubling_augassign,
                    replace=_fix_self_doubling_augassign, symptoms=("wrong", "timeout")),
            Rewrite(name="uninitialized_while_counter", match=_is_uninitialized_while_var,
                    replace=_fix_uninitialized_while_var, symptoms=("wrong", "err:NameError")),
            Rewrite(name="empty_branch_should_return", match=_is_empty_branch_assign,
                    replace=_fix_empty_branch_assign, symptoms=("wrong", "err:IndexError")),
            Rewrite(name="misattached_if_else_in_for", match=_is_misattached_if_else,
                    replace=_fix_misattached_if_else, symptoms=("wrong",)),
            Rewrite(name="undefined_name_to_param", match=_is_undefined_name,
                    replace=_fix_undefined_name, symptoms=("wrong", "err:NameError")),
        ]

        for from_cls, from_sym in _CMP_SYMS:
            for to_cls, to_sym in _CMP_SYMS:
                if from_cls is to_cls:
                    continue
                match, replace = _make_cmp_toggle(from_cls, to_sym)
                rules.append(
                    Rewrite(
                        name="cmp_toggle_%s_to_%s" % (from_sym, to_sym),
                        match=match,
                        replace=replace,
                        symptoms=("wrong",),
                    )
                )

        return rules