from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------- generic helpers ----------

def _enclosing_funcdef(node, ctx):
    cur = ctx.parent(node)
    while cur is not None and not isinstance(cur, ast.FunctionDef):
        cur = ctx.parent(cur)
    return cur


def _ancestor_for(node, ctx):
    cur = ctx.parent(node)
    while cur is not None and not isinstance(cur, ast.FunctionDef):
        if isinstance(cur, ast.For) and isinstance(cur.target, ast.Name):
            return cur
        cur = ctx.parent(cur)
    return None


def _containing_stmt(node, ctx):
    cur = node
    while True:
        parent = ctx.parent(cur)
        if parent is None:
            return None, None
        field = ctx.field(cur)
        container = getattr(parent, field, None) if field else None
        if isinstance(container, list) and cur in container:
            return cur, parent
        cur = parent


def _find_preceding_for(node, ctx):
    stmt, block_parent = _containing_stmt(node, ctx)
    if stmt is None:
        return None
    field = ctx.field(stmt)
    body = getattr(block_parent, field)
    try:
        idx = body.index(stmt)
    except ValueError:
        return None
    for s in reversed(body[:idx]):
        if isinstance(s, ast.For) and isinstance(s.target, ast.Name):
            return s
    return None


def _find_loop_tracker(for_node, loop_var_id):
    for n in ast.walk(for_node):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)
                and isinstance(n.value, ast.Name)
                and n.value.id == loop_var_id
                and n.targets[0].id != loop_var_id):
            return n.targets[0].id
    return None


def _assigned_names(func):
    names = set()
    for n in ast.walk(func):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                if isinstance(t, ast.Name):
                    names.add(t.id)
        if isinstance(n, ast.For) and isinstance(n.target, ast.Name):
            names.add(n.target.id)
        if isinstance(n, ast.arg):
            names.add(n.arg)
    return names


def _find_init_list_vars(func):
    names = []
    for n in ast.walk(func):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)
                and isinstance(n.value, (ast.List, ast.Tuple))
                and len(n.value.elts) == 0):
            names.append(n.targets[0].id)
    return names


def _find_accumulator(func):
    counts = {}
    for n in ast.walk(func):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr == 'append' and isinstance(n.func.value, ast.Name)):
            counts[n.func.value.id] = counts.get(n.func.value.id, 0) + 1
        if (isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name)
                and isinstance(n.op, ast.Add)):
            counts[n.target.id] = counts.get(n.target.id, 0) + 1
    if not counts:
        return None
    return max(counts, key=lambda k: counts[k])


_MUTATORS = {'reverse', 'sort', 'clear'}


# ---------- Rule: swapped tracker assignment (x = tracker instead of tracker = x) ----------

def _is_swapped_tracker_assign(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)):
        return False
    if not isinstance(node.value, ast.Name):
        return False
    forn = _ancestor_for(node, ctx)
    if forn is None:
        return False
    loop_var = forn.target.id
    target_id = node.targets[0].id
    value_id = node.value.id
    if target_id != loop_var or value_id == loop_var:
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.If)


def _fix_swapped_tracker_assign(node, ctx):
    return [ctx.text(node.value) + " = " + ctx.text(node.targets[0])]


# ---------- Rule: tracker updated with an undefined/wrong name instead of loop var ----------

def _is_bad_tracker_update_value(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)):
        return False
    if not isinstance(node.value, ast.Name):
        return False
    forn = _ancestor_for(node, ctx)
    if forn is None:
        return False
    loop_var = forn.target.id
    target_id = node.targets[0].id
    value_id = node.value.id
    if target_id == loop_var or value_id == loop_var:
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If):
        return False
    func = _enclosing_funcdef(node, ctx)
    if func is None:
        return False
    assigned = _assigned_names(func)
    return value_id not in assigned


def _fix_bad_tracker_update_value(node, ctx):
    forn = _ancestor_for(node, ctx)
    return [ctx.text(node.targets[0]) + " = " + forn.target.id]


# ---------- Rule: remove/append called with stale loop var instead of tracker ----------

def _is_call_using_loopvar_instead_of_tracker(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)):
        return False
    if node.func.attr not in {'remove', 'append'}:
        return False
    if len(node.args) != 1 or not isinstance(node.args[0], ast.Name):
        return False
    forn = _find_preceding_for(node, ctx)
    if forn is None:
        return False
    loop_var = forn.target.id
    if node.args[0].id != loop_var:
        return False
    tracker = _find_loop_tracker(forn, loop_var)
    return tracker is not None and tracker != loop_var


def _fix_call_using_loopvar(node, ctx):
    forn = _find_preceding_for(node, ctx)
    loop_var = forn.target.id
    tracker = _find_loop_tracker(forn, loop_var)
    return [ctx.text(node.func) + "(" + tracker + ")"]


# ---------- Rule: flip direction of an age comparison ----------

_FLIP_SYM = {ast.Lt: '>', ast.Gt: '<', ast.LtE: '>=', ast.GtE: '<='}


def _is_flippable_age_compare(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1):
        return False
    if type(node.ops[0]) not in _FLIP_SYM:
        return False
    def _is_agey(n):
        return isinstance(n, (ast.Subscript, ast.Name))
    return _is_agey(node.left) and _is_agey(node.comparators[0])


def _flip_age_compare(node, ctx):
    sym = _FLIP_SYM[type(node.ops[0])]
    return [ctx.text(node.left) + " " + sym + " " + ctx.text(node.comparators[0])]


# ---------- Rule: bare mutator attribute used as statement, missing call ----------

def _is_bare_mutator_attr_stmt(node, ctx):
    if not (isinstance(node, ast.Attribute) and node.attr in _MUTATORS):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.Expr)


def _fix_bare_mutator_attr_stmt(node, ctx):
    return [ctx.text(node) + "()"]


# ---------- Rule: return of a bare mutator attribute (no call) ----------

def _is_return_bare_mutator(node, ctx):
    return (isinstance(node, ast.Return) and isinstance(node.value, ast.Attribute)
            and node.value.attr in _MUTATORS)


def _fix_return_bare_mutator(node, ctx):
    call_text = ctx.text(node.value) + "()"
    base_text = ctx.text(node.value.value)
    return [call_text + "\nreturn " + base_text]


# ---------- Rule: return of a mutator call result (which is None) ----------

def _is_return_call_mutator(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    v = node.value
    return (isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute)
            and v.func.attr in _MUTATORS and len(v.args) == 0 and len(v.keywords) == 0)


def _fix_return_call_mutator(node, ctx):
    call_text = ctx.text(node.value)
    base_text = ctx.text(node.value.func.value)
    return [call_text + "\nreturn " + base_text]


# ---------- Rule: subscript used instead of call e.g. lst.pop[i] ----------

def _is_subscript_call_typo(node, ctx):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
            and node.value.attr in {'pop', 'remove', 'append', 'insert'})


def _fix_subscript_call_typo(node, ctx):
    return [ctx.text(node.value) + "(" + ctx.text(node.slice) + ")"]


# ---------- Rule: += name should be += (name,) when it is the just-removed item ----------

def _is_bare_name_augassign_add(node, ctx):
    if not (isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Add)):
        return False
    if not isinstance(node.value, ast.Name):
        return False
    stmt, block_parent = _containing_stmt(node, ctx)
    if stmt is None:
        return False
    field = ctx.field(stmt)
    siblings = getattr(block_parent, field)
    for s in siblings:
        if isinstance(s, ast.Expr) and isinstance(s.value, ast.Call):
            c = s.value
            if (isinstance(c.func, ast.Attribute) and c.func.attr == 'remove'
                    and len(c.args) == 1 and isinstance(c.args[0], ast.Name)
                    and c.args[0].id == node.value.id):
                return True
    return False


def _fix_bare_name_augassign_add(node, ctx):
    return [ctx.text(node.target) + " += (" + ctx.text(node.value) + ",)"]


# ---------- Rule: x = x.append(y) should be x = x + [y] ----------

def _is_reassign_append_result(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1
            and isinstance(node.targets[0], ast.Name)):
        return False
    v = node.value
    if not (isinstance(v, ast.Call) and isinstance(v.func, ast.Attribute)
            and v.func.attr == 'append' and isinstance(v.func.value, ast.Name)):
        return False
    if v.func.value.id != node.targets[0].id or len(v.args) != 1:
        return False
    return True


def _fix_reassign_append_result(node, ctx):
    target = ctx.text(node.targets[0])
    arg = ctx.text(node.value.args[0])
    return [target + " = " + target + " + [" + arg + "]"]


# ---------- Rule: max()/min() without key, comparing raw tuples ----------

def _is_max_min_missing_key(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id in {'max', 'min'}):
        return False
    if len(node.args) != 1:
        return False
    for kw in node.keywords:
        if kw.arg == 'key':
            return False
    return True


def _fix_max_min_missing_key(node, ctx):
    fname = node.func.id
    arg_text = ctx.text(node.args[0])
    return [fname + "(" + arg_text + ", key=lambda p: p[1])"]


# ---------- Rule: stray bare-name statement at module level ----------

def _is_stray_module_name_stmt(node, ctx):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Name)):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.Module)


def _fix_stray_module_name_stmt(node, ctx):
    return [""]


# ---------- Rule: function ends without return (pass/print), has an accumulator ----------

def _is_print_call_stmt(node):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name) and node.value.func.id == 'print')


def _is_missing_return_last_stmt(node, ctx):
    if not (isinstance(node, ast.Pass) or _is_print_call_stmt(node)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if ctx.field(node) != 'body' or not parent.body or parent.body[-1] is not node:
        return False
    for n in ast.walk(parent):
        if isinstance(n, ast.Return):
            return False
    return _find_accumulator(parent) is not None


def _fix_missing_return_last_stmt(node, ctx):
    parent = ctx.parent(node)
    acc = _find_accumulator(parent)
    if acc is None:
        return []
    return ["return " + acc]


# ---------- Rule: function has no return at all; loop is last statement ----------

def _is_func_missing_return_after_loop(node, ctx):
    if not isinstance(node, (ast.While, ast.For)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if not parent.body or parent.body[-1] is not node:
        return False
    for n in ast.walk(parent):
        if isinstance(n, ast.Return):
            return False
    return _find_accumulator(parent) is not None


def _fix_func_missing_return_after_loop(node, ctx):
    func = ctx.parent(node)
    acc = _find_accumulator(func)
    if acc is None:
        return []
    return [ctx.text(node) + "\nreturn " + acc]


# ---------- Rule: missing recursive-call return ----------

def _is_missing_return_on_recursive_call(node, ctx):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name)):
        return False
    func = _enclosing_funcdef(node, ctx)
    if func is None or node.value.func.id != func.name:
        return False
    if not func.body or func.body[-1] is not node:
        return False
    for n in ast.walk(func):
        if isinstance(n, ast.Return):
            return False
    return True


def _fix_missing_return_on_recursive_call(node, ctx):
    return ["return " + ctx.text(node.value)]


# ---------- Rule: accumulator used via .append()/return but never initialised ----------

def _is_loop_missing_accum_init(node, ctx):
    if not isinstance(node, (ast.While, ast.For)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    names = set()
    for n in ast.walk(node):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr == 'append' and isinstance(n.func.value, ast.Name)):
            names.add(n.func.value.id)
    if not names:
        return False
    assigned = _assigned_names(parent)
    missing = names - assigned
    return len(missing) == 1


def _fix_loop_missing_accum_init(node, ctx):
    names = set()
    for n in ast.walk(node):
        if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                and n.func.attr == 'append' and isinstance(n.func.value, ast.Name)):
            names.add(n.func.value.id)
    func = ctx.parent(node)
    assigned = _assigned_names(func)
    missing = names - assigned
    if len(missing) != 1:
        return []
    name = missing.pop()
    return [name + " = []\n" + ctx.text(node)]


# ---------- Rule: .append() target is an undefined name, one empty-list var exists ----------

def _is_undefined_append_target(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'append'):
        return False
    if not isinstance(node.func.value, ast.Name):
        return False
    func = _enclosing_funcdef(node, ctx)
    if func is None:
        return False
    assigned = _assigned_names(func)
    name = node.func.value.id
    if name in assigned:
        return False
    inits = _find_init_list_vars(func)
    cands = [n for n in inits if n != name]
    return len(cands) == 1


def _fix_undefined_append_target(node, ctx):
    func = _enclosing_funcdef(node, ctx)
    inits = _find_init_list_vars(func)
    name = node.func.value.id
    cands = [n for n in inits if n != name]
    if len(cands) != 1:
        return []
    args_text = ", ".join(ctx.text(a) for a in node.args)
    return [cands[0] + ".append(" + args_text + ")"]


# ---------- Rule: return of an undefined name, one empty-list var exists ----------

def _is_undefined_return_name(node, ctx):
    if not (isinstance(node, ast.Return) and isinstance(node.value, ast.Name)):
        return False
    func = _enclosing_funcdef(node, ctx)
    if func is None:
        return False
    assigned = _assigned_names(func)
    name = node.value.id
    if name in assigned:
        return False
    inits = _find_init_list_vars(func)
    cands = [n for n in inits if n != name]
    return len(cands) == 1


def _fix_undefined_return_name(node, ctx):
    func = _enclosing_funcdef(node, ctx)
    inits = _find_init_list_vars(func)
    name = node.value.id
    cands = [n for n in inits if n != name]
    if len(cands) != 1:
        return []
    return ["return " + cands[0]]


# ---------- Rule: range(1, len(lst)+1) off-by-one ----------

def _is_range_len_plus_one(node, ctx):
    if not (isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add)):
        return False
    if not (isinstance(node.right, ast.Constant) and node.right.value == 1):
        return False
    if not (isinstance(node.left, ast.Call) and isinstance(node.left.func, ast.Name)
            and node.left.func.id == 'len'):
        return False
    parent = ctx.parent(node)
    return (isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name)
            and parent.func.id == 'range')


def _fix_range_len_plus_one(node, ctx):
    return [ctx.text(node.left)]


# ---------- Rule: bare .pop() (no args) inside a merge-style `while a and b:` loop ----------

def _is_pop_no_args_in_merge(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
            and node.func.attr == 'pop' and len(node.args) == 0):
        return False
    cur = node
    whilen = None
    while cur is not None:
        cur = ctx.parent(cur)
        if isinstance(cur, ast.While):
            whilen = cur
            break
        if isinstance(cur, ast.FunctionDef) or cur is None:
            break
    if whilen is None:
        return False
    test = whilen.test
    return isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And)


def _fix_pop_no_args_in_merge(node, ctx):
    return [ctx.text(node.func) + "(0)"]


class Fixer:
    def rules(self):
        return [
            Rewrite(name="swapped_tracker_assign",
                    match=_is_swapped_tracker_assign,
                    replace=_fix_swapped_tracker_assign,
                    symptoms=("wrong",)),
            Rewrite(name="bad_tracker_update_value",
                    match=_is_bad_tracker_update_value,
                    replace=_fix_bad_tracker_update_value,
                    symptoms=("wrong", "err:NameError")),
            Rewrite(name="call_uses_loopvar_not_tracker",
                    match=_is_call_using_loopvar_instead_of_tracker,
                    replace=_fix_call_using_loopvar,
                    symptoms=("wrong",)),
            Rewrite(name="flip_age_compare_direction",
                    match=_is_flippable_age_compare,
                    replace=_flip_age_compare,
                    symptoms=("wrong",)),
            Rewrite(name="bare_mutator_attr_missing_call",
                    match=_is_bare_mutator_attr_stmt,
                    replace=_fix_bare_mutator_attr_stmt,
                    symptoms=("wrong", "err:AttributeError")),
            Rewrite(name="return_bare_mutator_attr",
                    match=_is_return_bare_mutator,
                    replace=_fix_return_bare_mutator,
                    symptoms=("wrong",)),
            Rewrite(name="return_mutator_call_result",
                    match=_is_return_call_mutator,
                    replace=_fix_return_call_mutator,
                    symptoms=("wrong",)),
            Rewrite(name="subscript_instead_of_call",
                    match=_is_subscript_call_typo,
                    replace=_fix_subscript_call_typo,
                    symptoms=("err:TypeError", "wrong")),
            Rewrite(name="augassign_should_wrap_tuple",
                    match=_is_bare_name_augassign_add,
                    replace=_fix_bare_name_augassign_add,
                    symptoms=("wrong",)),
            Rewrite(name="reassign_via_append_result",
                    match=_is_reassign_append_result,
                    replace=_fix_reassign_append_result,
                    symptoms=("wrong", "err:AttributeError")),
            Rewrite(name="max_min_missing_key",
                    match=_is_max_min_missing_key,
                    replace=_fix_max_min_missing_key,
                    symptoms=("wrong",)),
            Rewrite(name="stray_module_level_name",
                    match=_is_stray_module_name_stmt,
                    replace=_fix_stray_module_name_stmt,
                    symptoms=("err:NameError",)),
            Rewrite(name="missing_return_last_stmt",
                    match=_is_missing_return_last_stmt,
                    replace=_fix_missing_return_last_stmt,
                    symptoms=("wrong",)),
            Rewrite(name="missing_return_after_loop",
                    match=_is_func_missing_return_after_loop,
                    replace=_fix_func_missing_return_after_loop,
                    symptoms=("wrong",)),
            Rewrite(name="missing_return_on_recursive_call",
                    match=_is_missing_return_on_recursive_call,
                    replace=_fix_missing_return_on_recursive_call,
                    symptoms=("wrong",)),
            Rewrite(name="loop_missing_accumulator_init",
                    match=_is_loop_missing_accum_init,
                    replace=_fix_loop_missing_accum_init,
                    symptoms=("err:NameError", "wrong")),
            Rewrite(name="undefined_append_target",
                    match=_is_undefined_append_target,
                    replace=_fix_undefined_append_target,
                    symptoms=("err:NameError", "wrong")),
            Rewrite(name="undefined_return_name",
                    match=_is_undefined_return_name,
                    replace=_fix_undefined_return_name,
                    symptoms=("err:NameError", "wrong")),
            Rewrite(name="range_len_plus_one",
                    match=_is_range_len_plus_one,
                    replace=_fix_range_len_plus_one,
                    symptoms=("err:IndexError", "wrong")),
            Rewrite(name="pop_no_args_in_merge_loop",
                    match=_is_pop_no_args_in_merge,
                    replace=_fix_pop_no_args_in_merge,
                    symptoms=("wrong",)),
        ]