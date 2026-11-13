from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------------
# Generic helpers
# ---------------------------------------------------------------------------

DOMAIN_WORDS = {"day", "date", "month"}


def _enclosing_function(node, ctx):
    cur = node
    while cur is not None:
        cur = ctx.parent(cur)
        if isinstance(cur, ast.FunctionDef):
            return cur
    return None


def _target_names(t):
    names = set()
    if isinstance(t, ast.Name):
        names.add(t.id)
    elif isinstance(t, (ast.Tuple, ast.List)):
        for e in t.elts:
            names |= _target_names(e)
    return names


def _bound_names(func):
    names = set(a.arg for a in func.args.args)
    for n in ast.walk(func):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                names |= _target_names(t)
        elif isinstance(n, ast.AugAssign):
            names |= _target_names(n.target)
        elif isinstance(n, ast.For):
            names |= _target_names(n.target)
        elif isinstance(n, ast.comprehension):
            names |= _target_names(n.target)
        elif isinstance(n, ast.FunctionDef) and n is not func:
            names.add(n.name)
    return names


def _is_bool_const(node, val):
    return isinstance(node, ast.Constant) and node.value is val


def _const_index(node):
    if not isinstance(node, ast.Subscript):
        return None
    s = node.slice
    if isinstance(s, ast.Constant):
        return s.value
    if hasattr(ast, "Index") and isinstance(s, getattr(ast, "Index")):
        v = s.value
        if isinstance(v, ast.Constant):
            return v.value
    return None


# ---------------------------------------------------------------------------
# Rule: undefined domain-word name should be the function's own parameter
# ---------------------------------------------------------------------------

def _is_undefined_domain_name(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
        return False
    if node.id not in DOMAIN_WORDS:
        return False
    func = _enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    if not func.args.args:
        return False
    param_name = func.args.args[0].arg
    if node.id == param_name:
        return False
    bound = _bound_names(func)
    if node.id in bound:
        return False
    return True


def _fix_undefined_domain_name(node, ctx):
    func = _enclosing_function(node, ctx)
    return [func.args.args[0].arg]


# ---------------------------------------------------------------------------
# Rule: rename an unused parameter to the domain word actually used in body
# ---------------------------------------------------------------------------

def _candidate_domain_rename(func, param_name):
    loads = set()
    for n in ast.walk(func):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
            loads.add(n.id)
    if param_name in loads:
        return None
    bound = _bound_names(func) - {param_name}
    candidates = [w for w in DOMAIN_WORDS if w in loads and w not in bound and w != param_name]
    if len(candidates) == 1:
        return candidates[0]
    return None


def _is_unused_param_with_domain_typo(node, ctx):
    if not isinstance(node, ast.arg):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.arguments):
        return False
    func = ctx.parent(parent)
    if not isinstance(func, ast.FunctionDef):
        return False
    if func.name not in ("unique_day", "unique_month"):
        return False
    if not func.args.args or func.args.args[0] is not node:
        return False
    return _candidate_domain_rename(func, node.arg) is not None


def _fix_unused_param_rename(node, ctx):
    parent = ctx.parent(node)
    func = ctx.parent(parent)
    return [_candidate_domain_rename(func, node.arg)]


# ---------------------------------------------------------------------------
# Rule: "possible_birthday" typo for "possible_birthdays"
# ---------------------------------------------------------------------------

def _is_possible_birthday_typo(node, ctx):
    return isinstance(node, ast.Name) and node.id == "possible_birthday"


def _fix_possible_birthday_typo(node, ctx):
    return ["possible_birthdays"]


# ---------------------------------------------------------------------------
# Rule: tuple accumulation missing the trailing comma: x = x + i  ->  x + (i,)
# ---------------------------------------------------------------------------

def _enclosing_for(node, ctx):
    cur = node
    while cur is not None:
        cur = ctx.parent(cur)
        if isinstance(cur, ast.For):
            return cur
        if isinstance(cur, ast.FunctionDef):
            return None
    return None


def _is_tuple_append_missing_comma(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    if not (isinstance(node.left, ast.Name) and isinstance(node.right, ast.Name)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Assign):
        return False
    if len(parent.targets) != 1 or not isinstance(parent.targets[0], ast.Name):
        return False
    if parent.targets[0].id != node.left.id:
        return False
    forloop = _enclosing_for(node, ctx)
    if forloop is None or not isinstance(forloop.target, ast.Name):
        return False
    return forloop.target.id == node.right.id


def _fix_tuple_append_missing_comma(node, ctx):
    return [ctx.text(node.left) + " + (" + ctx.text(node.right) + ",)"]


# ---------------------------------------------------------------------------
# Rule: wrong tuple index (0 vs 1) when comparing against day/month parameter
# ---------------------------------------------------------------------------

def _wrong_index_cmp(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    if not func.args.args:
        return False
    param_name = func.args.args[0].arg
    expected = 1 if func.name == "unique_day" else 0
    wrong = 0 if expected == 1 else 1
    left, right = node.left, node.comparators[0]

    def is_param(n):
        return isinstance(n, ast.Name) and n.id == param_name

    def is_wrong_sub(n):
        return isinstance(n, ast.Subscript) and _const_index(n) == wrong

    return (is_param(left) and is_wrong_sub(right)) or (is_param(right) and is_wrong_sub(left))


def _fix_wrong_index_cmp(node, ctx):
    func = _enclosing_function(node, ctx)
    expected = 1 if func.name == "unique_day" else 0
    left, right = node.left, node.comparators[0]
    if isinstance(left, ast.Subscript):
        new_left = ctx.text(left.value) + "[" + str(expected) + "]"
        return [new_left + " == " + ctx.text(right)]
    new_right = ctx.text(right.value) + "[" + str(expected) + "]"
    return [ctx.text(left) + " == " + new_right]


# ---------------------------------------------------------------------------
# Rule: calling unique_day with the month index (0) instead of the day index (1)
# ---------------------------------------------------------------------------

def _is_wrong_unique_day_call_arg(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "unique_day"):
        return False
    if not node.args:
        return False
    return _const_index(node.args[0]) == 0


def _fix_wrong_unique_day_call_arg(node, ctx):
    arg0 = node.args[0]
    new_arg0 = ctx.text(arg0.value) + "[1]"
    rest = [ctx.text(a) for a in node.args[1:]]
    all_args = [new_arg0] + rest
    kwargs = [ctx.text(k.value) if k.arg is None else (k.arg + "=" + ctx.text(k.value)) for k in node.keywords]
    return [ctx.text(node.func) + "(" + ", ".join(all_args + kwargs) + ")"]


# ---------------------------------------------------------------------------
# Rule: "unique_date" typo for "unique_day"
# ---------------------------------------------------------------------------

def _is_unique_date_typo(node, ctx):
    if not (isinstance(node, ast.Name) and node.id == "unique_date"):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.Call) and parent.func is node


def _fix_unique_date_typo(node, ctx):
    return ["unique_day"]


# ---------------------------------------------------------------------------
# Rule: contains_unique_day returns False on the very first non-matching item
# (if unique_day(...): return True  else: return False) inside a for loop
# ---------------------------------------------------------------------------

def _is_premature_false_return_loop(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if len(node.body) != 1:
        return False
    stmt = node.body[0]
    if not isinstance(stmt, ast.If):
        return False
    if len(stmt.body) != 1 or not isinstance(stmt.body[0], ast.Return):
        return False
    if len(stmt.orelse) != 1 or not isinstance(stmt.orelse[0], ast.Return):
        return False
    if not (_is_bool_const(stmt.body[0].value, True) and _is_bool_const(stmt.orelse[0].value, False)):
        return False
    func = _enclosing_function(node, ctx)
    return func is not None and func.name == "contains_unique_day"


def _fix_premature_false_return_loop(node, ctx):
    stmt = node.body[0]
    text = (
        "for " + ctx.text(node.target) + " in " + ctx.text(node.iter) + ":\n"
        "    if " + ctx.text(stmt.test) + ":\n"
        "        return True\n"
        "return False"
    )
    return [text]


# ---------------------------------------------------------------------------
# Rule: contains_unique_day directly returns unique_day(...) on first match
# ---------------------------------------------------------------------------

def _is_direct_return_call_for(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if len(node.body) != 1:
        return False
    stmt = node.body[0]
    if not isinstance(stmt, ast.If) or len(stmt.body) != 1 or stmt.orelse:
        return False
    inner = stmt.body[0]
    if not isinstance(inner, ast.Return) or inner.value is None:
        return False
    if not (isinstance(inner.value, ast.Call) and isinstance(inner.value.func, ast.Name)
            and inner.value.func.id == "unique_day"):
        return False
    func = _enclosing_function(node, ctx)
    return func is not None and func.name == "contains_unique_day"


def _fix_direct_return_call_for(node, ctx):
    stmt = node.body[0]
    inner = stmt.body[0]
    text = (
        "for " + ctx.text(node.target) + " in " + ctx.text(node.iter) + ":\n"
        "    if " + ctx.text(stmt.test) + ":\n"
        "        if " + ctx.text(inner.value) + ":\n"
        "            return True\n"
        "return False"
    )
    return [text]


# ---------------------------------------------------------------------------
# Rule: for-loop that only ever returns True is the last statement, with no
# trailing "return False" to cover the not-found case
# ---------------------------------------------------------------------------

def _is_for_missing_trailing_return(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if len(node.body) != 1:
        return False
    stmt = node.body[0]
    if not isinstance(stmt, ast.If):
        return False
    if stmt.orelse:
        if not (len(stmt.orelse) == 1 and isinstance(stmt.orelse[0], ast.Continue)):
            return False
    if len(stmt.body) != 1 or not isinstance(stmt.body[0], ast.Return):
        return False
    if not _is_bool_const(stmt.body[0].value, True):
        return False
    func = _enclosing_function(node, ctx)
    if func is None or func.name != "contains_unique_day":
        return False
    return bool(func.body) and func.body[-1] is node


def _fix_for_missing_trailing_return(node, ctx):
    return [ctx.text(node) + "\nreturn False"]


# ---------------------------------------------------------------------------
# Rule: unique_day/unique_month ends in "if cond: return True" with no else
# ---------------------------------------------------------------------------

def _is_if_missing_else_return_false(node, ctx):
    if not isinstance(node, ast.If) or node.orelse:
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
        return False
    if not _is_bool_const(node.body[0].value, True):
        return False
    func = _enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    return bool(func.body) and func.body[-1] is node


def _fix_if_missing_else_return_false(node, ctx):
    return ["if " + ctx.text(node.test) + ":\n    return True\nelse:\n    return False"]


# ---------------------------------------------------------------------------
# Rule: counting function returns a mis-thresholded comparison directly
# ---------------------------------------------------------------------------

def _is_bad_count_return(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    v = node.value
    if not (isinstance(v, ast.Compare) and len(v.ops) == 1 and len(v.comparators) == 1):
        return False
    if not isinstance(v.ops[0], (ast.Gt, ast.GtE, ast.Lt, ast.LtE)):
        return False
    if not isinstance(v.left, ast.Name):
        return False
    if not (isinstance(v.comparators[0], ast.Constant) and isinstance(v.comparators[0].value, int)
            and not isinstance(v.comparators[0].value, bool)):
        return False
    func = _enclosing_function(node, ctx)
    return func is not None and func.name in ("unique_day", "unique_month")


def _fix_bad_count_return(node, ctx):
    v = node.value
    return ["return " + ctx.text(v.left) + " == 1"]


# ---------------------------------------------------------------------------
# Rule: counting function uses an "if count <op> n: return B1 [else: return B2]"
# threshold check instead of comparing to exactly one occurrence
# ---------------------------------------------------------------------------

def _is_bad_count_if(node, ctx):
    if not isinstance(node, ast.If):
        return False
    test = node.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1 and len(test.comparators) == 1):
        return False
    if not isinstance(test.ops[0], (ast.Gt, ast.GtE, ast.Lt, ast.LtE)):
        return False
    if not isinstance(test.left, ast.Name):
        return False
    comp = test.comparators[0]
    if not (isinstance(comp, ast.Constant) and isinstance(comp.value, int) and not isinstance(comp.value, bool)):
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
        return False
    bv = node.body[0].value
    if not (isinstance(bv, ast.Constant) and isinstance(bv.value, bool)):
        return False
    if node.orelse:
        if len(node.orelse) != 1 or not isinstance(node.orelse[0], ast.Return):
            return False
        ov = node.orelse[0].value
        if not (isinstance(ov, ast.Constant) and isinstance(ov.value, bool)):
            return False
    func = _enclosing_function(node, ctx)
    return func is not None and func.name in ("unique_day", "unique_month")


def _fix_bad_count_if(node, ctx):
    var = ctx.text(node.test.left)
    return ["if " + var + " == 1:\n    return True\nelse:\n    return False"]


# ---------------------------------------------------------------------------
# Rule: lowercase "true"/"false" NameError typo
# ---------------------------------------------------------------------------

def _is_lowercase_bool(node, ctx):
    return isinstance(node, ast.Name) and node.id in ("true", "false") and isinstance(node.ctx, ast.Load)


def _fix_lowercase_bool(node, ctx):
    return ["True" if node.id == "true" else "False"]


# ---------------------------------------------------------------------------
# Rule: empty tuple used as an accumulator later called with .append(...)
# ---------------------------------------------------------------------------

def _is_empty_tuple_should_be_list(node, ctx):
    if not (isinstance(node, ast.Tuple) and not node.elts):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Assign) and len(parent.targets) == 1
            and isinstance(parent.targets[0], ast.Name)):
        return False
    name = parent.targets[0].id
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    for n in ast.walk(func):
        if isinstance(n, ast.Attribute) and n.attr == "append" \
                and isinstance(n.value, ast.Name) and n.value.id == name:
            return True
    return False


def _fix_empty_tuple_should_be_list(node, ctx):
    return ["[]"]


# ---------------------------------------------------------------------------
# Rule: AugAssign on a counter that was never initialised in the function
# ---------------------------------------------------------------------------

def _is_augassign_missing_init(node, ctx):
    if not isinstance(node, ast.For):
        return False
    aug_targets = set()
    for n in ast.walk(node):
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name):
            aug_targets.add(n.target.id)
    if not aug_targets:
        return False
    func = _enclosing_function(node, ctx)
    if func is None or node not in func.body:
        return False
    idx = func.body.index(node)
    assigned_before = set()
    for stmt in func.body[:idx]:
        for n in ast.walk(stmt):
            if isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Name):
                        assigned_before.add(t.id)
    missing = [v for v in aug_targets if v not in assigned_before]
    return len(missing) == 1


def _fix_augassign_missing_init(node, ctx):
    aug_targets = set()
    for n in ast.walk(node):
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name):
            aug_targets.add(n.target.id)
    func = _enclosing_function(node, ctx)
    idx = func.body.index(node)
    assigned_before = set()
    for stmt in func.body[:idx]:
        for n in ast.walk(stmt):
            if isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Name):
                        assigned_before.add(t.id)
    missing = [v for v in aug_targets if v not in assigned_before][0]
    return [missing + " = 0\n" + ctx.text(node)]


# ---------------------------------------------------------------------------
# Generic off-by-one: `i <= len(seq)` should be `i < len(seq)`
# ---------------------------------------------------------------------------

def _is_off_by_one_le_len(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.LtE)
            and isinstance(node.comparators[0], ast.Call)
            and isinstance(node.comparators[0].func, ast.Name)
            and node.comparators[0].func.id == "len")


def _fix_off_by_one_le_len(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


# ---------------------------------------------------------------------------
# Generic: strict comparison relaxed to non-strict
# ---------------------------------------------------------------------------

def _is_strict_lt(node, ctx):
    return (isinstance(node, ast.Compare) and len(node.ops) == 1
            and isinstance(node.ops[0], ast.Lt))


def _to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


# ---------------------------------------------------------------------------

class Fixer:
    def rules(self):
        return [
            Rewrite(name="undefined_domain_name_use_param",
                    match=_is_undefined_domain_name,
                    replace=_fix_undefined_domain_name,
                    symptoms=("err:NameError", "wrong")),
            Rewrite(name="unused_param_rename_to_domain_word",
                    match=_is_unused_param_with_domain_typo,
                    replace=_fix_unused_param_rename,
                    symptoms=("err:NameError", "wrong")),
            Rewrite(name="possible_birthday_typo",
                    match=_is_possible_birthday_typo,
                    replace=_fix_possible_birthday_typo,
                    symptoms=("err:NameError",)),
            Rewrite(name="tuple_append_missing_comma",
                    match=_is_tuple_append_missing_comma,
                    replace=_fix_tuple_append_missing_comma,
                    symptoms=("wrong", "err:TypeError")),
            Rewrite(name="wrong_subscript_index_in_count_fn",
                    match=_wrong_index_cmp,
                    replace=_fix_wrong_index_cmp,
                    symptoms=("wrong",)),
            Rewrite(name="wrong_arg_index_in_unique_day_call",
                    match=_is_wrong_unique_day_call_arg,
                    replace=_fix_wrong_unique_day_call_arg,
                    symptoms=("wrong",)),
            Rewrite(name="unique_date_typo",
                    match=_is_unique_date_typo,
                    replace=_fix_unique_date_typo,
                    symptoms=("err:NameError",)),
            Rewrite(name="loop_early_false_return",
                    match=_is_premature_false_return_loop,
                    replace=_fix_premature_false_return_loop,
                    symptoms=("wrong",)),
            Rewrite(name="direct_return_call_in_loop",
                    match=_is_direct_return_call_for,
                    replace=_fix_direct_return_call_for,
                    symptoms=("wrong",)),
            Rewrite(name="for_missing_trailing_return",
                    match=_is_for_missing_trailing_return,
                    replace=_fix_for_missing_trailing_return,
                    symptoms=("wrong",)),
            Rewrite(name="if_missing_else_return_false",
                    match=_is_if_missing_else_return_false,
                    replace=_fix_if_missing_else_return_false,
                    symptoms=("wrong",)),
            Rewrite(name="bad_count_return",
                    match=_is_bad_count_return,
                    replace=_fix_bad_count_return,
                    symptoms=("wrong",)),
            Rewrite(name="bad_count_if",
                    match=_is_bad_count_if,
                    replace=_fix_bad_count_if,
                    symptoms=("wrong",)),
            Rewrite(name="lowercase_bool_typo",
                    match=_is_lowercase_bool,
                    replace=_fix_lowercase_bool,
                    symptoms=("err:NameError",)),
            Rewrite(name="empty_tuple_should_be_list",
                    match=_is_empty_tuple_should_be_list,
                    replace=_fix_empty_tuple_should_be_list,
                    symptoms=("err:AttributeError",)),
            Rewrite(name="augassign_missing_init",
                    match=_is_augassign_missing_init,
                    replace=_fix_augassign_missing_init,
                    symptoms=("err:UnboundLocalError", "err:NameError")),
            Rewrite(name="off_by_one_le_len",
                    match=_is_off_by_one_le_len,
                    replace=_fix_off_by_one_le_len,
                    symptoms=("err:IndexError", "wrong")),
            Rewrite(name="strict_lt_should_be_lte",
                    match=_is_strict_lt,
                    replace=_to_lte,
                    symptoms=("wrong",)),
        ]