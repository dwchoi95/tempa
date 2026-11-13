from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


def _enclosing_function(node, ctx):
    p = ctx.parent(node)
    while p is not None and not isinstance(p, ast.FunctionDef):
        p = ctx.parent(p)
    return p


def _collect_defined_names(func):
    names = set()
    for n in ast.walk(func):
        if isinstance(n, ast.arg):
            names.add(n.arg)
        elif isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name):
                    names.add(t.id)
        elif isinstance(n, ast.AugAssign):
            if isinstance(n.target, ast.Name):
                names.add(n.target.id)
        elif isinstance(n, ast.For):
            if isinstance(n.target, ast.Name):
                names.add(n.target.id)
        elif isinstance(n, ast.FunctionDef):
            names.add(n.name)
    return names


def _module_function_names(ctx):
    names = set()
    for n in ast.walk(ctx.tree):
        if isinstance(n, ast.FunctionDef):
            names.add(n.name)
    return names


def _slice_value(sl):
    if isinstance(sl, ast.Index):
        return sl.value
    return sl


# ---------------------------------------------------------------------
# 1. Stub `contains_unique_day` (body is just `return`/`pass`/docstring).
# ---------------------------------------------------------------------

def _is_stub_tail(func, stmt):
    if func.body[-1] is not stmt:
        return False
    if not (isinstance(stmt, ast.Return) and stmt.value is None) and not isinstance(stmt, ast.Pass):
        return False
    for s in func.body[:-1]:
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str):
            continue
        return False
    return True


def _is_stub_contains_unique_day(node, ctx):
    if not (isinstance(node, ast.Return) or isinstance(node, ast.Pass)):
        return False
    func = ctx.parent(node)
    if not isinstance(func, ast.FunctionDef) or func.name != "contains_unique_day":
        return False
    return _is_stub_tail(func, node)


def _fix_stub_contains_unique_day(node, ctx):
    func = ctx.parent(node)
    args = [a.arg for a in func.args.args]
    month_param = args[0] if len(args) > 0 else "month"
    bdays_param = args[1] if len(args) > 1 else "possible_birthdays"
    text = (
        "for birthday in " + bdays_param + ":\n"
        "    if birthday[0] == " + month_param + ":\n"
        "        if unique_day(birthday[1], " + bdays_param + "):\n"
        "            return True\n"
        "return False"
    )
    return [text]


# ---------------------------------------------------------------------
# 2. Stub `unique_day` / `unique_month`.
# ---------------------------------------------------------------------

def _is_stub_unique_day_or_month(node, ctx):
    if not (isinstance(node, ast.Return) or isinstance(node, ast.Pass)):
        return False
    func = ctx.parent(node)
    if not isinstance(func, ast.FunctionDef) or func.name not in ("unique_day", "unique_month"):
        return False
    return _is_stub_tail(func, node)


def _fix_stub_unique_day_or_month(node, ctx):
    func = ctx.parent(node)
    args = [a.arg for a in func.args.args]
    key_param = args[0] if len(args) > 0 else "day"
    bdays_param = args[1] if len(args) > 1 else "possible_birthdays"
    idx = "1" if func.name == "unique_day" else "0"
    text = (
        "count = 0\n"
        "for birthday in " + bdays_param + ":\n"
        "    if birthday[" + idx + "] == " + key_param + ":\n"
        "        count += 1\n"
        "return count == 1"
    )
    return [text]


# ---------------------------------------------------------------------
# 3. Undefined name used in a Compare inside unique_day/unique_month,
#    should instead refer to the function's first parameter.
# ---------------------------------------------------------------------

def _is_undefined_name_in_compare(node, ctx):
    if not isinstance(node, ast.Name):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Compare):
        return False
    func = _enclosing_function(node, ctx)
    if func is None or func.name not in ("unique_day", "unique_month"):
        return False
    if not func.args.args:
        return False
    param_name = func.args.args[0].arg
    if node.id == param_name:
        return False
    defined = _collect_defined_names(func)
    defined |= _module_function_names(ctx)
    if node.id in defined:
        return False
    return True


def _fix_undefined_name_in_compare(node, ctx):
    func = _enclosing_function(node, ctx)
    param_name = func.args.args[0].arg
    return [param_name]


# ---------------------------------------------------------------------
# 4. Comparator uses the zero-initialised counter variable instead of
#    the actual search parameter.
# ---------------------------------------------------------------------

def _find_counter_name(func):
    for n in ast.walk(func):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name):
            if isinstance(n.value, ast.Constant) and n.value.value == 0 and not isinstance(n.value.value, bool):
                cand = n.targets[0].id
                for n2 in ast.walk(func):
                    if isinstance(n2, ast.Compare) and isinstance(n2.left, ast.Name) and n2.left.id == cand:
                        if len(n2.ops) == 1 and isinstance(n2.ops[0], ast.Eq):
                            c = n2.comparators[0]
                            if isinstance(c, ast.Constant) and c.value == 1 and not isinstance(c.value, bool):
                                return cand
    return None


def _is_counter_compare_should_use_param(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    if len(node.ops) != 1 or not isinstance(node.ops[0], ast.Eq):
        return False
    comparator = node.comparators[0]
    if not isinstance(comparator, ast.Name):
        return False
    func = _enclosing_function(node, ctx)
    if func is None or not func.args.args:
        return False
    param_name = func.args.args[0].arg
    if comparator.id == param_name:
        return False
    counter_name = _find_counter_name(func)
    return counter_name is not None and comparator.id == counter_name


def _fix_counter_compare_should_use_param(node, ctx):
    func = _enclosing_function(node, ctx)
    param_name = func.args.args[0].arg
    return [ctx.text(node.left) + " == " + param_name]


# ---------------------------------------------------------------------
# 5. `X = X + 1` where X is otherwise undefined: should increment the
#    real zero-initialised counter instead.
# ---------------------------------------------------------------------

def _is_broken_increment(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
        return False
    target = node.targets[0]
    val = node.value
    if not (isinstance(val, ast.BinOp) and isinstance(val.op, ast.Add)):
        return False
    if not (isinstance(val.left, ast.Name) and val.left.id == target.id):
        return False
    if not (isinstance(val.right, ast.Constant) and val.right.value == 1 and not isinstance(val.right.value, bool)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    assigned_elsewhere = False
    for n in ast.walk(func):
        if n is node:
            continue
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name) and t.id == target.id:
                    assigned_elsewhere = True
        if isinstance(n, ast.For) and isinstance(n.target, ast.Name) and n.target.id == target.id:
            assigned_elsewhere = True
        if isinstance(n, ast.arg) and n.arg == target.id:
            assigned_elsewhere = True
    if assigned_elsewhere:
        return False
    counter_name = _find_counter_name(func)
    return counter_name is not None and counter_name != target.id


def _fix_broken_increment(node, ctx):
    func = _enclosing_function(node, ctx)
    counter_name = _find_counter_name(func)
    return [counter_name + " = " + counter_name + " + 1"]


# ---------------------------------------------------------------------
# 6. Counter used via AugAssign but never initialised: insert `x = 0`.
# ---------------------------------------------------------------------

def _is_missing_counter_init(node, ctx):
    if not isinstance(node, ast.For):
        return False
    func = ctx.parent(node)
    if not isinstance(func, ast.FunctionDef):
        return False
    if func.name not in ("unique_day", "unique_month"):
        return False
    counter = None
    for n in ast.walk(node):
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and isinstance(n.op, ast.Add):
            counter = n.target.id
    if counter is None:
        return False
    if node not in func.body:
        return False
    idx = func.body.index(node)
    for stmt in func.body[:idx]:
        if isinstance(stmt, ast.Assign):
            for t in stmt.targets:
                if isinstance(t, ast.Name) and t.id == counter:
                    return False
    return True


def _fix_missing_counter_init(node, ctx):
    counter = None
    for n in ast.walk(node):
        if isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and isinstance(n.op, ast.Add):
            counter = n.target.id
    return [counter + " = 0", ctx.text(node)]


# ---------------------------------------------------------------------
# 7. `return counter >= 2` / `return counter > 1` / `return counter <= 1`
#    used as the direct truth value, should be `== 1`.
# ---------------------------------------------------------------------

def _is_bad_threshold_return(node, ctx):
    if not isinstance(node, ast.Compare):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Return):
        return False
    if len(node.ops) != 1 or not isinstance(node.left, ast.Name):
        return False
    op = node.ops[0]
    comp = node.comparators[0]
    if not isinstance(comp, ast.Constant) or isinstance(comp.value, bool) or not isinstance(comp.value, int):
        return False
    if isinstance(op, ast.GtE) and comp.value == 2:
        return True
    if isinstance(op, ast.Gt) and comp.value == 1:
        return True
    if isinstance(op, ast.LtE) and comp.value == 1:
        return True
    return False


def _fix_bad_threshold_return(node, ctx):
    return [ctx.text(node.left) + " == 1"]


# ---------------------------------------------------------------------
# 8. Tuple accumulator used with `.append` -> should be a list.
# ---------------------------------------------------------------------

def _is_tuple_with_append(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)):
        return False
    if not (isinstance(node.value, ast.Tuple) and len(node.value.elts) == 0):
        return False
    name = node.targets[0].id
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    for n in ast.walk(func):
        if isinstance(n, ast.Attribute) and n.attr == "append":
            if isinstance(n.value, ast.Name) and n.value.id == name:
                return True
    return False


def _fix_tuple_with_append(node, ctx):
    return [ctx.text(node.targets[0]) + " = []"]


# ---------------------------------------------------------------------
# 9. Tuple concatenation missing the one-tuple wrapping comma.
# ---------------------------------------------------------------------

def _is_tuple_concat_missing_comma(node, ctx):
    if not isinstance(node, ast.BinOp) or not isinstance(node.op, ast.Add):
        return False
    if not isinstance(node.left, ast.Name):
        return False
    right = node.right
    if isinstance(right, ast.Tuple):
        return False
    if isinstance(right, ast.Constant) and isinstance(right.value, (int, float)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Assign) and len(parent.targets) == 1
            and isinstance(parent.targets[0], ast.Name) and parent.targets[0].id == node.left.id):
        return False
    name = node.left.id
    func = _enclosing_function(parent, ctx)
    if func is None:
        return False
    init_found = False
    for n in ast.walk(func):
        if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) and n.targets[0].id == name:
            if isinstance(n.value, ast.Tuple) and len(n.value.elts) == 0:
                init_found = True
    return init_found


def _fix_tuple_concat_missing_comma(node, ctx):
    return [ctx.text(node.left) + " + (" + ctx.text(node.right) + ",)"]


# ---------------------------------------------------------------------
# 10. Call to the undefined helper `unique_date` -> `unique_day`.
# ---------------------------------------------------------------------

def _is_undefined_unique_date_call(node, ctx):
    if not isinstance(node, ast.Name) or node.id != "unique_date":
        return False
    names = _module_function_names(ctx)
    return "unique_date" not in names


def _fix_undefined_unique_date_call(node, ctx):
    return ["unique_day"]


# ---------------------------------------------------------------------
# 11. `if cond: return True else: return False` nested inside a loop:
#     the `else` branch causes a premature wrong exit.
# ---------------------------------------------------------------------

def _is_premature_else_return_false(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if len(node.orelse) != 1:
        return False
    else_stmt = node.orelse[0]
    if not (isinstance(else_stmt, ast.Return) and isinstance(else_stmt.value, ast.Constant) and else_stmt.value.value is False):
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
        return False
    p = ctx.parent(node)
    found_loop = False
    while p is not None and not isinstance(p, ast.FunctionDef):
        if isinstance(p, (ast.For, ast.While)):
            found_loop = True
            break
        p = ctx.parent(p)
    return found_loop


def _fix_premature_else_return_false(node, ctx):
    return ["if " + ctx.text(node.test) + ":\n    " + ctx.text(node.body[0])]


# ---------------------------------------------------------------------
# 12. A loop (or lone `if`) is the last statement of the function and
#     contains a `return True` but no fallback `return False`.
# ---------------------------------------------------------------------

def _is_loop_missing_trailing_false(node, ctx):
    if not isinstance(node, (ast.For, ast.While)):
        return False
    func = ctx.parent(node)
    if not isinstance(func, ast.FunctionDef):
        return False
    if func.body[-1] is not node:
        return False
    for n in ast.walk(node):
        if isinstance(n, ast.Return) and isinstance(n.value, ast.Constant) and n.value.value is True:
            return True
    return False


def _fix_loop_missing_trailing_false(node, ctx):
    return [ctx.text(node), "return False"]


def _is_if_missing_trailing_false(node, ctx):
    if not isinstance(node, ast.If):
        return False
    if node.orelse:
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
        return False
    func = ctx.parent(node)
    if not isinstance(func, ast.FunctionDef):
        return False
    if func.body[-1] is not node:
        return False
    return True


def _fix_if_missing_trailing_false(node, ctx):
    return [ctx.text(node), "return False"]


# ---------------------------------------------------------------------
# 13. Tuple-index confusion: `x[1]` vs `x[0]` when compared against a
#     variable literally named day/date/month.
# ---------------------------------------------------------------------

def _is_wrong_index_for_month_or_day(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.Compare) or len(parent.ops) != 1 or not isinstance(parent.ops[0], ast.Eq):
        return False
    if parent.left is node:
        other = parent.comparators[0] if parent.comparators else None
    elif parent.comparators and parent.comparators[0] is node:
        other = parent.left
    else:
        return False
    if not isinstance(other, ast.Name):
        return False
    if other.id in ("day", "date"):
        expected = 1
    elif other.id == "month":
        expected = 0
    else:
        return False
    idx = _slice_value(node.slice)
    if not isinstance(idx, ast.Constant) or idx.value not in (0, 1):
        return False
    return idx.value != expected


def _fix_wrong_index_for_month_or_day(node, ctx):
    parent = ctx.parent(node)
    if parent.left is node:
        other = parent.comparators[0]
    else:
        other = parent.left
    expected = 1 if other.id in ("day", "date") else 0
    return [ctx.text(node.value) + "[" + str(expected) + "]"]


# ---------------------------------------------------------------------
# 14. Lowercase `true`/`false` typos, and `Flase`.
# ---------------------------------------------------------------------

def _is_lowercase_bool_typo(node, ctx):
    return isinstance(node, ast.Name) and node.id in ("true", "false")


def _fix_lowercase_bool_typo(node, ctx):
    return ["True" if node.id == "true" else "False"]


def _is_flase_typo(node, ctx):
    return isinstance(node, ast.Name) and node.id == "Flase"


def _fix_flase_typo(node, ctx):
    return ["False"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="stub_contains_unique_day",
                    match=_is_stub_contains_unique_day,
                    replace=_fix_stub_contains_unique_day,
                    symptoms=("wrong", "err:NameError", "err:TypeError")),

            Rewrite(name="stub_unique_day_or_month",
                    match=_is_stub_unique_day_or_month,
                    replace=_fix_stub_unique_day_or_month,
                    symptoms=("wrong", "err:NameError", "err:TypeError")),

            Rewrite(name="undefined_name_in_compare_use_param",
                    match=_is_undefined_name_in_compare,
                    replace=_fix_undefined_name_in_compare,
                    symptoms=("err:NameError", "wrong")),

            Rewrite(name="counter_compare_should_use_param",
                    match=_is_counter_compare_should_use_param,
                    replace=_fix_counter_compare_should_use_param,
                    symptoms=("wrong",)),

            Rewrite(name="broken_increment_use_counter",
                    match=_is_broken_increment,
                    replace=_fix_broken_increment,
                    symptoms=("err:NameError", "wrong")),

            Rewrite(name="missing_counter_init",
                    match=_is_missing_counter_init,
                    replace=_fix_missing_counter_init,
                    symptoms=("err:NameError", "err:UnboundLocalError", "wrong")),

            Rewrite(name="bad_threshold_return",
                    match=_is_bad_threshold_return,
                    replace=_fix_bad_threshold_return,
                    symptoms=("wrong",)),

            Rewrite(name="tuple_append_should_be_list",
                    match=_is_tuple_with_append,
                    replace=_fix_tuple_with_append,
                    symptoms=("err:AttributeError",)),

            Rewrite(name="tuple_concat_missing_comma",
                    match=_is_tuple_concat_missing_comma,
                    replace=_fix_tuple_concat_missing_comma,
                    symptoms=("wrong", "err:TypeError")),

            Rewrite(name="call_to_undefined_unique_date",
                    match=_is_undefined_unique_date_call,
                    replace=_fix_undefined_unique_date_call,
                    symptoms=("err:NameError",)),

            Rewrite(name="premature_else_return_false",
                    match=_is_premature_else_return_false,
                    replace=_fix_premature_else_return_false,
                    symptoms=("wrong",)),

            Rewrite(name="loop_missing_trailing_false",
                    match=_is_loop_missing_trailing_false,
                    replace=_fix_loop_missing_trailing_false,
                    symptoms=("wrong",)),

            Rewrite(name="if_missing_trailing_false",
                    match=_is_if_missing_trailing_false,
                    replace=_fix_if_missing_trailing_false,
                    symptoms=("wrong",)),

            Rewrite(name="wrong_tuple_index_for_month_or_day",
                    match=_is_wrong_index_for_month_or_day,
                    replace=_fix_wrong_index_for_month_or_day,
                    symptoms=("wrong",)),

            Rewrite(name="lowercase_bool_typo",
                    match=_is_lowercase_bool_typo,
                    replace=_fix_lowercase_bool_typo,
                    symptoms=("err:NameError",)),

            Rewrite(name="flase_typo",
                    match=_is_flase_typo,
                    replace=_fix_flase_typo,
                    symptoms=("err:NameError",)),
        ]