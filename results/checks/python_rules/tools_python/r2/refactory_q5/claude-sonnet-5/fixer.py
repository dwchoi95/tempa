from src.core.repair import Rule
import ast
import difflib

from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _safe(fn):
    def wrapped(node, ctx):
        try:
            return fn(node, ctx)
        except Exception:
            return False
    return wrapped


def _safe_replace(fn):
    def wrapped(node, ctx):
        try:
            return fn(node, ctx)
        except Exception:
            return []
    return wrapped


def _enclosing_function(node, ctx):
    cur = node
    while cur is not None:
        cur = ctx.parent(cur)
        if isinstance(cur, ast.FunctionDef):
            return cur
    return None


def _collect_assigned_names(func):
    names = set()
    for n in ast.walk(func):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            names.add(n.id)
        if isinstance(n, ast.arg):
            names.add(n.arg)
    names.add(func.name)
    return names


def _find_list_accumulator(func):
    for n in ast.walk(func):
        if (isinstance(n, ast.Assign) and len(n.targets) == 1
                and isinstance(n.targets[0], ast.Name)
                and isinstance(n.value, ast.List) and len(n.value.elts) == 0):
            return n.targets[0].id
    return None


def _param_names(func):
    return {a.arg for a in func.args.args}


def _param_k_name(func):
    args = func.args.args
    if len(args) >= 2:
        return args[1].arg
    return 'k'


def _candidate_name(node, func, ctx):
    parent = ctx.parent(node)
    if (isinstance(parent, ast.Attribute) or isinstance(parent, ast.Return)
            or isinstance(parent, ast.Subscript)):
        acc = _find_list_accumulator(func)
        if acc and acc != node.id:
            return acc
    assigned = _collect_assigned_names(func)
    params = _param_names(func)
    candidates = sorted(assigned - {func.name} - params)
    close = difflib.get_close_matches(node.id, candidates, n=1, cutoff=0.6)
    if close:
        return close[0]
    return None


def _stmt_block_and_index(node, ctx):
    parent = ctx.parent(node)
    body = getattr(parent, 'body', None)
    if body is None or node not in body:
        return None, None
    return body, body.index(node)


# ---------------------------------------------------------------------------
# Rule: swap order of remove(X) then append(X) -> append(X) then remove(X)
# ---------------------------------------------------------------------------

def _is_remove_before_append(node, ctx):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    call = node.value
    if not (isinstance(call.func, ast.Attribute) and call.func.attr == 'remove'):
        return False
    body, idx = _stmt_block_and_index(node, ctx)
    if body is None or idx + 1 >= len(body):
        return False
    nxt = body[idx + 1]
    if not (isinstance(nxt, ast.Expr) and isinstance(nxt.value, ast.Call)):
        return False
    ncall = nxt.value
    if not (isinstance(ncall.func, ast.Attribute) and ncall.func.attr == 'append'):
        return False
    if len(call.args) != 1 or len(ncall.args) != 1:
        return False
    return ctx.text(call.args[0]) == ctx.text(ncall.args[0])


def _fix_remove_before_append(node, ctx):
    body, idx = _stmt_block_and_index(node, ctx)
    nxt = body[idx + 1]
    return [ctx.text(nxt)]


def _is_append_after_remove(node, ctx):
    if not (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)):
        return False
    call = node.value
    if not (isinstance(call.func, ast.Attribute) and call.func.attr == 'append'):
        return False
    body, idx = _stmt_block_and_index(node, ctx)
    if body is None or idx == 0:
        return False
    prev = body[idx - 1]
    if not (isinstance(prev, ast.Expr) and isinstance(prev.value, ast.Call)):
        return False
    pcall = prev.value
    if not (isinstance(pcall.func, ast.Attribute) and pcall.func.attr == 'remove'):
        return False
    if len(call.args) != 1 or len(pcall.args) != 1:
        return False
    return ctx.text(call.args[0]) == ctx.text(pcall.args[0])


def _fix_append_after_remove(node, ctx):
    body, idx = _stmt_block_and_index(node, ctx)
    prev = body[idx - 1]
    return [ctx.text(prev)]


# ---------------------------------------------------------------------------
# Rule: wrong variable assigned inside max-tracking if-body
# ---------------------------------------------------------------------------

def _is_misassigned_track(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1):
        return False
    target = node.targets[0]
    value = node.value
    if not (isinstance(target, ast.Name) and isinstance(value, ast.Name)):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If):
        return False
    if not parent.body or parent.body[0] is not node:
        return False
    test = parent.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], (ast.Gt, ast.Lt))):
        return False
    left, comp = test.left, test.comparators[0]
    if not (isinstance(left, ast.Name) and isinstance(comp, ast.Name)):
        return False
    names = {left.id, comp.id}
    if target.id in names:
        return False
    if value.id not in names:
        return False
    correct = names - {value.id}
    return len(correct) == 1


def _fix_misassigned_track(node, ctx):
    parent = ctx.parent(node)
    test = parent.test
    names = {test.left.id, test.comparators[0].id}
    correct = list(names - {node.value.id})[0]
    return [correct + " = " + ctx.text(node.value)]


# ---------------------------------------------------------------------------
# Rule: undefined / typo'd accumulator name
# ---------------------------------------------------------------------------

def _is_undefined_accumulator_name(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
        return False
    func = _enclosing_function(node, ctx)
    if func is None:
        return False
    assigned = _collect_assigned_names(func)
    if node.id in assigned:
        return False
    parent = ctx.parent(node)
    valid_ctx = False
    if isinstance(parent, ast.Attribute) and parent.attr in ('append', 'remove') and parent.value is node:
        valid_ctx = True
    elif isinstance(parent, ast.Return) and parent.value is node:
        valid_ctx = True
    elif isinstance(parent, ast.Subscript) and parent.value is node:
        gp = ctx.parent(parent)
        if isinstance(gp, ast.Return) and gp.value is parent:
            valid_ctx = True
    elif (isinstance(parent, ast.Call) and isinstance(parent.func, ast.Name)
          and parent.func.id == func.name and node in parent.args):
        valid_ctx = True
    if not valid_ctx:
        return False
    return _candidate_name(node, func, ctx) is not None


def _fix_undefined_accumulator_name(node, ctx):
    func = _enclosing_function(node, ctx)
    cand = _candidate_name(node, func, ctx)
    return [cand] if cand else []


# ---------------------------------------------------------------------------
# Rule: appending the whole list instead of the just-computed maximum
# ---------------------------------------------------------------------------

def _is_append_whole_list(node, ctx):
    if not isinstance(node, ast.Name):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Call) and isinstance(parent.func, ast.Attribute)
            and parent.func.attr == 'append'):
        return False
    if len(parent.args) != 1 or parent.args[0] is not node:
        return False
    stmt = ctx.parent(parent)
    if not isinstance(stmt, ast.Expr):
        return False
    body, idx = _stmt_block_and_index(stmt, ctx)
    if body is None or idx == 0:
        return False
    prev = body[idx - 1]
    if not (isinstance(prev, ast.Assign) and len(prev.targets) == 1
            and isinstance(prev.targets[0], ast.Name)):
        return False
    val = prev.value
    if not (isinstance(val, ast.Call) and isinstance(val.func, ast.Name) and val.func.id == 'max'):
        return False
    if len(val.args) != 1:
        return False
    return ctx.text(val.args[0]) == ctx.text(node)


def _fix_append_whole_list(node, ctx):
    stmt = ctx.parent(ctx.parent(node))
    body, idx = _stmt_block_and_index(stmt, ctx)
    prev = body[idx - 1]
    return [prev.targets[0].id]


# ---------------------------------------------------------------------------
# Rule: pop(max(lst)) should index first
# ---------------------------------------------------------------------------

def _is_pop_value_as_index(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == 'max'):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Call) and isinstance(parent.func, ast.Attribute)
            and parent.func.attr == 'pop'):
        return False
    if len(parent.args) != 1 or parent.args[0] is not node:
        return False
    if len(node.args) != 1:
        return False
    return ctx.text(parent.func.value) == ctx.text(node.args[0])


def _fix_pop_value_as_index(node, ctx):
    lst_text = ctx.text(node.args[0])
    return ["{0}.index(max({0}))".format(lst_text)]


# ---------------------------------------------------------------------------
# Rule: len(acc) <= k   -->   len(acc) < k
# ---------------------------------------------------------------------------

def _is_len_lte_k(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE)):
        return False
    left = node.left
    if not (isinstance(left, ast.Call) and isinstance(left.func, ast.Name) and left.func.id == 'len'):
        return False
    return isinstance(node.comparators[0], ast.Name)


def _fix_lte_to_lt(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


# ---------------------------------------------------------------------------
# Rule: counter <= k (counter initialised to 0)  -->  counter < k
# ---------------------------------------------------------------------------

def _is_counter_lte_k_zero(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.LtE)):
        return False
    left, right = node.left, node.comparators[0]
    if not (isinstance(left, ast.Name) and isinstance(right, ast.Name)):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.While) and parent.test is node):
        return False
    body, idx = _stmt_block_and_index(parent, ctx)
    if body is None:
        return False
    for i in range(idx - 1, -1, -1):
        st = body[i]
        if (isinstance(st, ast.Assign) and len(st.targets) == 1
                and isinstance(st.targets[0], ast.Name) and st.targets[0].id == left.id):
            return isinstance(st.value, ast.Constant) and st.value.value == 0
    return False


# ---------------------------------------------------------------------------
# Rule: while k >= 0  -->  while k > 0
# ---------------------------------------------------------------------------

def _is_gte_zero_while(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.GtE)):
        return False
    right = node.comparators[0]
    if not (isinstance(right, ast.Constant) and right.value == 0):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.While) and parent.test is node


def _fix_gte_to_gt(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


# ---------------------------------------------------------------------------
# Rule: slice upper bound off-by-one / hard-coded, should be k
# ---------------------------------------------------------------------------

def _is_bad_slice_upper(node, ctx):
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.Slice) and parent.upper is node):
        return False
    if isinstance(node, ast.Constant) and isinstance(node.value, int) and not isinstance(node.value, bool):
        func = _enclosing_function(node, ctx)
        return func is not None
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub)):
        l, r = node.left, node.right
        if isinstance(l, ast.Name) and isinstance(r, ast.Constant) and r.value == 1:
            return True
        if isinstance(r, ast.Name) and isinstance(l, ast.Constant) and l.value == 1:
            return True
    return False


def _fix_bad_slice_upper(node, ctx):
    if isinstance(node, ast.Constant):
        func = _enclosing_function(node, ctx)
        kname = _param_k_name(func) if func else 'k'
        return [kname]
    if isinstance(node, ast.BinOp):
        if isinstance(node.left, ast.Name):
            return [ctx.text(node.left)]
        if isinstance(node.right, ast.Name):
            return [ctx.text(node.right)]
    return []


# ---------------------------------------------------------------------------
# Rule: fake swap (a = b; b = a) should become a tuple swap
# ---------------------------------------------------------------------------

def _cross_match(a_target, a_value, b_target, b_value, ctx):
    return (ctx.text(a_target) == ctx.text(b_value)
            and ctx.text(b_target) == ctx.text(a_value))


def _is_fake_swap_first(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1):
        return False
    body, idx = _stmt_block_and_index(node, ctx)
    if body is None or idx + 1 >= len(body):
        return False
    nxt = body[idx + 1]
    if not (isinstance(nxt, ast.Assign) and len(nxt.targets) == 1):
        return False
    return _cross_match(node.targets[0], node.value, nxt.targets[0], nxt.value, ctx)


def _fix_fake_swap_first(node, ctx):
    body, idx = _stmt_block_and_index(node, ctx)
    nxt = body[idx + 1]
    t0, v0 = ctx.text(node.targets[0]), ctx.text(node.value)
    t1, v1 = ctx.text(nxt.targets[0]), ctx.text(nxt.value)
    return ["{}, {} = {}, {}".format(t0, t1, v0, v1)]


def _is_fake_swap_second(node, ctx):
    if not (isinstance(node, ast.Assign) and len(node.targets) == 1):
        return False
    body, idx = _stmt_block_and_index(node, ctx)
    if body is None or idx == 0:
        return False
    prev = body[idx - 1]
    if not (isinstance(prev, ast.Assign) and len(prev.targets) == 1):
        return False
    return _cross_match(prev.targets[0], prev.value, node.targets[0], node.value, ctx)


def _fix_fake_swap_second(node, ctx):
    return [""]


# ---------------------------------------------------------------------------
# Rule: subscript-call typo e.g. r.append[x] -> r.append(x)
# ---------------------------------------------------------------------------

def _is_bracket_call(node, ctx):
    if not isinstance(node, ast.Subscript):
        return False
    val = node.value
    return isinstance(val, ast.Attribute) and val.attr in ('append', 'remove', 'pop')


def _fix_bracket_call(node, ctx):
    idx_text = ctx.text(node.slice)
    return [ctx.text(node.value) + "(" + idx_text + ")"]


# ---------------------------------------------------------------------------
# Rule: comparing loop index directly to max(lst) instead of lst[index]
# ---------------------------------------------------------------------------

def _is_missing_index_compare(node, ctx):
    if not (isinstance(node, ast.Compare) and len(node.ops) == 1 and isinstance(node.ops[0], ast.Eq)):
        return False
    left, right = node.left, node.comparators[0]
    if not isinstance(left, ast.Name):
        return False
    if not (isinstance(right, ast.Call) and isinstance(right.func, ast.Name) and right.func.id == 'max'):
        return False
    cur = node
    forloop = None
    while cur is not None:
        cur = ctx.parent(cur)
        if isinstance(cur, ast.For):
            forloop = cur
            break
    if forloop is None:
        return False
    if not (isinstance(forloop.target, ast.Name) and forloop.target.id == left.id):
        return False
    it = forloop.iter
    if not (isinstance(it, ast.Call) and isinstance(it.func, ast.Name) and it.func.id == 'range'):
        return False
    if len(it.args) != 1:
        return False
    arg = it.args[0]
    return isinstance(arg, ast.Call) and isinstance(arg.func, ast.Name) and arg.func.id == 'len'


def _fix_missing_index_compare(node, ctx):
    cur = node
    forloop = None
    while cur is not None:
        cur = ctx.parent(cur)
        if isinstance(cur, ast.For):
            forloop = cur
            break
    lst_text = ctx.text(forloop.iter.args[0].args[0])
    idx_text = ctx.text(node.left)
    return ["{}[{}] == {}".format(lst_text, idx_text, ctx.text(node.comparators[0]))]


# ---------------------------------------------------------------------------
# Rule: extend `if lst == []: return []` to also cover k == 0
# ---------------------------------------------------------------------------

def _is_emptylist_guard_test(node, ctx):
    if isinstance(node, ast.BoolOp):
        return False
    parent = ctx.parent(node)
    if not (isinstance(parent, ast.If) and parent.test is node):
        return False
    if len(parent.body) != 1 or not isinstance(parent.body[0], ast.Return):
        return False
    ret_val = parent.body[0].value
    if not (isinstance(ret_val, ast.List) and len(ret_val.elts) == 0):
        return False
    func = _enclosing_function(node, ctx)
    return func is not None


def _fix_add_k_zero(node, ctx):
    func = _enclosing_function(node, ctx)
    kname = _param_k_name(func) if func else 'k'
    return [ctx.text(node) + " or {} == 0".format(kname)]


# ---------------------------------------------------------------------------
# Rule: `if k == 0: return <wrong>` -> `return []`
# ---------------------------------------------------------------------------

def _is_wrong_k_zero_return(node, ctx):
    if not isinstance(node, ast.Return):
        return False
    parent = ctx.parent(node)
    if not isinstance(parent, ast.If):
        return False
    test = parent.test
    is_k_zero = (isinstance(test, ast.Compare) and len(test.ops) == 1
                 and isinstance(test.ops[0], ast.Eq)
                 and isinstance(test.left, ast.Name)
                 and isinstance(test.comparators[0], ast.Constant)
                 and test.comparators[0].value == 0)
    if not is_k_zero:
        return False
    val = node.value
    if isinstance(val, ast.List) and len(val.elts) == 0:
        return False
    return True


def _fix_wrong_k_zero_return(node, ctx):
    return ["return []"]


# ---------------------------------------------------------------------------
# Rule: insert a missing k == 0 guard at the top of the function
# ---------------------------------------------------------------------------

def _has_k_zero_check(func, kname):
    for n in ast.walk(func):
        if isinstance(n, ast.Compare) and len(n.ops) == 1:
            op = n.ops[0]
            if isinstance(op, (ast.Eq, ast.LtE, ast.Lt)):
                left, right = n.left, n.comparators[0]
                names, consts = [], []
                for x in (left, right):
                    if isinstance(x, ast.Name):
                        names.append(x.id)
                    if isinstance(x, ast.Constant):
                        consts.append(x.value)
                if kname in names and 0 in consts:
                    return True
    return False


def _is_first_stmt_needing_k_guard(node, ctx):
    parent = ctx.parent(node)
    if not isinstance(parent, ast.FunctionDef):
        return False
    if not parent.body or parent.body[0] is not node:
        return False
    if isinstance(node, ast.Return):
        return False
    kname = _param_k_name(parent)
    if kname not in _param_names(parent):
        return False
    if _has_k_zero_check(parent, kname):
        return False
    return True


def _fix_insert_k_zero_guard(node, ctx):
    func = ctx.parent(node)
    kname = _param_k_name(func)
    return ["if {0} == 0:\n    return []\n".format(kname) + ctx.text(node)]


# ---------------------------------------------------------------------------
# Fixer
# ---------------------------------------------------------------------------

class Fixer:
    def rules(self):
        return [
            Rewrite(name="swap_remove_before_append_1",
                    match=_safe(_is_remove_before_append),
                    replace=_safe_replace(_fix_remove_before_append),
                    symptoms=("wrong",)),
            Rewrite(name="swap_remove_before_append_2",
                    match=_safe(_is_append_after_remove),
                    replace=_safe_replace(_fix_append_after_remove),
                    symptoms=("wrong",)),
            Rewrite(name="misassigned_track_var",
                    match=_safe(_is_misassigned_track),
                    replace=_safe_replace(_fix_misassigned_track),
                    symptoms=("wrong", "err:NameError")),
            Rewrite(name="undefined_accumulator_name",
                    match=_safe(_is_undefined_accumulator_name),
                    replace=_safe_replace(_fix_undefined_accumulator_name),
                    symptoms=("err:NameError", "wrong")),
            Rewrite(name="append_whole_list_instead_of_value",
                    match=_safe(_is_append_whole_list),
                    replace=_safe_replace(_fix_append_whole_list),
                    symptoms=("wrong",)),
            Rewrite(name="pop_value_as_index",
                    match=_safe(_is_pop_value_as_index),
                    replace=_safe_replace(_fix_pop_value_as_index),
                    symptoms=("wrong", "err:TypeError", "err:ValueError")),
            Rewrite(name="len_lte_k_to_lt",
                    match=_safe(_is_len_lte_k),
                    replace=_safe_replace(_fix_lte_to_lt),
                    symptoms=("wrong", "err:IndexError", "timeout")),
            Rewrite(name="counter_lte_k_zero_init_to_lt",
                    match=_safe(_is_counter_lte_k_zero),
                    replace=_safe_replace(_fix_lte_to_lt),
                    symptoms=("wrong", "err:IndexError")),
            Rewrite(name="while_gte_zero_to_gt",
                    match=_safe(_is_gte_zero_while),
                    replace=_safe_replace(_fix_gte_to_gt),
                    symptoms=("wrong", "err:IndexError", "err:ValueError")),
            Rewrite(name="slice_bound_should_be_k",
                    match=_safe(_is_bad_slice_upper),
                    replace=_safe_replace(_fix_bad_slice_upper),
                    symptoms=("wrong",)),
            Rewrite(name="fake_swap_to_tuple_swap_1",
                    match=_safe(_is_fake_swap_first),
                    replace=_safe_replace(_fix_fake_swap_first),
                    symptoms=("wrong",)),
            Rewrite(name="fake_swap_to_tuple_swap_2",
                    match=_safe(_is_fake_swap_second),
                    replace=_safe_replace(_fix_fake_swap_second),
                    symptoms=("wrong",)),
            Rewrite(name="subscript_call_typo",
                    match=_safe(_is_bracket_call),
                    replace=_safe_replace(_fix_bracket_call),
                    symptoms=("err:TypeError", "wrong")),
            Rewrite(name="missing_index_in_compare",
                    match=_safe(_is_missing_index_compare),
                    replace=_safe_replace(_fix_missing_index_compare),
                    symptoms=("wrong", "timeout")),
            Rewrite(name="add_k_zero_to_emptylist_guard",
                    match=_safe(_is_emptylist_guard_test),
                    replace=_safe_replace(_fix_add_k_zero),
                    symptoms=("wrong",)),
            Rewrite(name="fix_wrong_k_zero_return_value",
                    match=_safe(_is_wrong_k_zero_return),
                    replace=_safe_replace(_fix_wrong_k_zero_return),
                    symptoms=("wrong",)),
            Rewrite(name="insert_missing_k_zero_guard",
                    match=_safe(_is_first_stmt_needing_k_guard),
                    replace=_safe_replace(_fix_insert_k_zero_guard),
                    symptoms=("wrong",)),
        ]