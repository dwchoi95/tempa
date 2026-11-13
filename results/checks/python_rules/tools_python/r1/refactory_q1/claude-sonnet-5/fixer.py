from src.core.repair import Rule
import ast
from src.core.rewrite import Rewrite


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

_BUILTINS = {"len", "range", "enumerate", "list", "tuple", "max", "min",
             "sorted", "int", "str", "set", "dict", "True", "False", "None"}


def _find_func(node, ctx):
    n = node
    while n is not None and not isinstance(n, ast.FunctionDef):
        n = ctx.parent(n)
    return n


def _seq_param(func):
    if func is not None and len(func.args.args) >= 2:
        return func.args.args[1].arg
    return "seq"


def _get_enclosing_block(node, ctx):
    parent = ctx.parent(node)
    if parent is None:
        return None
    for attr in ("body", "orelse", "finalbody"):
        lst = getattr(parent, attr, None)
        if isinstance(lst, list) and node in lst:
            return lst
    return None


def _collect_assigned_names(func):
    names = {a.arg for a in func.args.args}
    for n in ast.walk(func):
        if isinstance(n, ast.Assign):
            for t in n.targets:
                for nm in ast.walk(t):
                    if isinstance(nm, ast.Name):
                        names.add(nm.id)
        elif isinstance(n, ast.AugAssign):
            for nm in ast.walk(n.target):
                if isinstance(nm, ast.Name):
                    names.add(nm.id)
        elif isinstance(n, ast.For):
            for nm in ast.walk(n.target):
                if isinstance(nm, ast.Name):
                    names.add(nm.id)
    return names


def _one_edit_away(a, b):
    if a == b or len(a) < 2 or len(b) < 2:
        return False
    if abs(len(a) - len(b)) > 1:
        return False
    if len(a) == len(b):
        return sum(1 for x, y in zip(a, b) if x != y) == 1
    longer, shorter = (a, b) if len(a) > len(b) else (b, a)
    for i in range(len(longer)):
        if longer[:i] + longer[i + 1:] == shorter:
            return True
    return False


def _unwrap_elifs(if_node):
    chain = [if_node]
    cur = if_node
    while len(cur.orelse) == 1 and isinstance(cur.orelse[0], ast.If):
        cur = cur.orelse[0]
        chain.append(cur)
    return chain, cur


# ---------------------------------------------------------------------------
# rule: use before definition of a `X = list(seq)` style copy variable
# ---------------------------------------------------------------------------

def _is_use_before_list_copy(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
        return False
    func = _find_func(node, ctx)
    if func is None:
        return False
    for stmt in ast.walk(func):
        if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)
                and stmt.targets[0].id == node.id
                and isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Name)
                and stmt.value.func.id == "list"
                and len(stmt.value.args) == 1):
            if (node.lineno, node.col_offset) < (stmt.lineno, stmt.col_offset):
                return True
    return False


def _fix_use_before_list_copy(node, ctx):
    func = _find_func(node, ctx)
    for stmt in ast.walk(func):
        if (isinstance(stmt, ast.Assign) and len(stmt.targets) == 1
                and isinstance(stmt.targets[0], ast.Name)
                and stmt.targets[0].id == node.id
                and isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Name)
                and stmt.value.func.id == "list"
                and len(stmt.value.args) == 1):
            return [ctx.text(stmt.value.args[0])]
    return []


# ---------------------------------------------------------------------------
# rule: for loop whose body is [If(no else, single return), Return(...)]
# the trailing Return executes on the very first iteration -> move it out
# ---------------------------------------------------------------------------

def _is_for_body_extra_return(node, ctx):
    if not isinstance(node, ast.For):
        return False
    body = node.body
    if len(body) != 2:
        return False
    first, second = body
    if not isinstance(first, ast.If) or first.orelse:
        return False
    if not isinstance(second, ast.Return):
        return False
    if len(first.body) != 1:
        return False
    if "\n" in ctx.text(first.body[0]) or "\n" in ctx.text(second):
        return False
    return True


def _fix_for_body_extra_return(node, ctx):
    if_node = node.body[0]
    header = "for " + ctx.text(node.target) + " in " + ctx.text(node.iter) + ":"
    inner_if = "    if " + ctx.text(if_node.test) + ":"
    inner_ret = "        " + ctx.text(if_node.body[0])
    tail_ret = ctx.text(node.body[1])
    return [header + "\n" + inner_if + "\n" + inner_ret + "\n" + tail_ret]


# ---------------------------------------------------------------------------
# rule: for loop whose single body statement is an if/elif chain ending in
# an "else: return ..." -- the else fires on the first mismatching element.
# ---------------------------------------------------------------------------

def _is_for_if_else_premature_return(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.If):
        return False
    chain, leaf = _unwrap_elifs(node.body[0])
    for n in chain:
        if len(n.body) != 1:
            return False
        if "\n" in ctx.text(n.body[0]):
            return False
    if len(leaf.orelse) != 1 or not isinstance(leaf.orelse[0], ast.Return):
        return False
    if "\n" in ctx.text(leaf.orelse[0]):
        return False
    return True


def _fix_for_if_else_premature_return(node, ctx):
    chain, leaf = _unwrap_elifs(node.body[0])
    ret_text = ctx.text(leaf.orelse[0])
    lines = ["for " + ctx.text(node.target) + " in " + ctx.text(node.iter) + ":"]
    first = True
    for n in chain:
        kw = "if" if first else "elif"
        lines.append("    " + kw + " " + ctx.text(n.test) + ":")
        lines.append("        " + ctx.text(n.body[0]))
        first = False
    lines.append(ret_text)
    return ["\n".join(lines)]


# ---------------------------------------------------------------------------
# rule: a for/while loop is the last meaningful statement of its block and
# nothing after it returns a value -> add the missing fall-through return.
# ---------------------------------------------------------------------------

def _is_loop_missing_trailing_return(node, ctx):
    if not isinstance(node, (ast.For, ast.While)):
        return False
    block = _get_enclosing_block(node, ctx)
    if block is None:
        return False
    idx = block.index(node)
    for stmt in block[idx + 1:]:
        if isinstance(stmt, ast.Return) and stmt.value is not None:
            return False
        if isinstance(stmt, ast.Expr):
            continue
        return False
    return True


def _fix_loop_missing_trailing_return(node, ctx):
    func = _find_func(node, ctx)
    seq_param = _seq_param(func)
    return [ctx.text(node) + "\nreturn len(" + seq_param + ")"]


# ---------------------------------------------------------------------------
# rule: bare `return` inside a for-loop that is immediately followed by a
# sibling `return <value>` -- the bare return should just break the loop.
# ---------------------------------------------------------------------------

def _is_bare_return_should_break(node, ctx):
    if not isinstance(node, ast.Return) or node.value is not None:
        return False
    n = node
    for_node = None
    while n is not None:
        par = ctx.parent(n)
        if isinstance(par, ast.For):
            for_node = par
            break
        n = par
    if for_node is None:
        return False
    block = _get_enclosing_block(for_node, ctx)
    if block is None:
        return False
    idx = block.index(for_node)
    if idx + 1 >= len(block):
        return False
    nxt = block[idx + 1]
    return isinstance(nxt, ast.Return) and nxt.value is not None


def _fix_bare_return_should_break(node, ctx):
    return ["break"]


# ---------------------------------------------------------------------------
# rule: trailing `return <loopvar>` / `return <loopvar>+1` after a loop that
# used that name as its index -- should be `return len(seq)`.
# ---------------------------------------------------------------------------

def _is_bad_trailing_return_loopvar(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    val = node.value
    name_id = None
    if isinstance(val, ast.Name):
        name_id = val.id
    elif isinstance(val, ast.BinOp) and isinstance(val.left, ast.Name):
        name_id = val.left.id
    if name_id is None:
        return False
    block = _get_enclosing_block(node, ctx)
    if block is None:
        return False
    idx = block.index(node)
    if idx == 0:
        return False
    prev = block[idx - 1]
    if not isinstance(prev, (ast.For, ast.While)):
        return False
    tgt = getattr(prev, "target", None)
    matched = False
    if isinstance(tgt, ast.Name) and tgt.id == name_id:
        matched = True
    elif isinstance(tgt, ast.Tuple):
        matched = any(isinstance(e, ast.Name) and e.id == name_id for e in tgt.elts)
    return matched


def _fix_bad_trailing_return_loopvar(node, ctx):
    func = _find_func(node, ctx)
    return ["return len(" + _seq_param(func) + ")"]


# ---------------------------------------------------------------------------
# rule: `return X - 1` -> `return X`  (common off-by-one on the final answer)
# ---------------------------------------------------------------------------

def _is_decrement_return(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    v = node.value
    return (isinstance(v, ast.BinOp) and isinstance(v.op, ast.Sub)
            and isinstance(v.right, ast.Constant) and v.right.value == 1)


def _fix_decrement_return(node, ctx):
    return ["return " + ctx.text(node.value.left)]


# ---------------------------------------------------------------------------
# rule: `return len(seq) + 1` -> `return len(seq)`
# ---------------------------------------------------------------------------

def _is_increment_len_return(node, ctx):
    if not isinstance(node, ast.Return) or node.value is None:
        return False
    v = node.value
    return (isinstance(v, ast.BinOp) and isinstance(v.op, ast.Add)
            and isinstance(v.right, ast.Constant) and v.right.value == 1
            and isinstance(v.left, ast.Call) and isinstance(v.left.func, ast.Name)
            and v.left.func.id == "len")


def _fix_increment_len_return(node, ctx):
    return ["return " + ctx.text(node.value.left)]


# ---------------------------------------------------------------------------
# rule: `count==0` as a bare expression statement -- should be an assignment
# ---------------------------------------------------------------------------

def _is_double_eq_typo(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    v = node.value
    return (isinstance(v, ast.Compare) and len(v.ops) == 1
            and isinstance(v.ops[0], ast.Eq) and isinstance(v.left, ast.Name))


def _fix_double_eq_typo(node, ctx):
    v = node.value
    return [ctx.text(v.left) + " = " + ctx.text(v.comparators[0])]


# ---------------------------------------------------------------------------
# rule: `sorted(seq)` called and its result discarded
# ---------------------------------------------------------------------------

def _is_discarded_sorted_call(node, ctx):
    return (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name) and node.value.func.id == "sorted")


def _fix_discarded_sorted_call(node, ctx):
    arg_text = ctx.text(node.value.args[0])
    return [arg_text + " = " + ctx.text(node.value)]


# ---------------------------------------------------------------------------
# rule: last statement of the function is a bare expression that should be
# a return (e.g. `seq.index(x)` with no `return`)
# ---------------------------------------------------------------------------

def _is_trailing_expr_should_be_return(node, ctx):
    if not isinstance(node, ast.Expr):
        return False
    func = _find_func(node, ctx)
    if func is None or ctx.parent(node) is not func:
        return False
    body = func.body
    if not body or body[-1] is not node:
        return False
    return isinstance(node.value, (ast.Call, ast.Name, ast.Subscript, ast.BinOp))


def _fix_trailing_expr_should_be_return(node, ctx):
    return ["return " + ctx.text(node.value)]


# ---------------------------------------------------------------------------
# rules: broken range() expressions used as for-loop iterables
# ---------------------------------------------------------------------------

def _is_range_of_seq(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "range"):
        return False
    if len(node.args) != 1:
        return False
    func = _find_func(node, ctx)
    return isinstance(node.args[0], ast.Name) and node.args[0].id == _seq_param(func)


def _fix_range_of_seq(node, ctx):
    return ["range(len(" + ctx.text(node.args[0]) + "))"]


def _is_bare_len_as_for_iter(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "len"):
        return False
    parent = ctx.parent(node)
    return isinstance(parent, ast.For) and parent.iter is node


def _fix_bare_len_as_for_iter(node, ctx):
    return ["range(" + ctx.text(node) + ")"]


def _is_len_range_seq(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "len"):
        return False
    if len(node.args) != 1:
        return False
    inner = node.args[0]
    return (isinstance(inner, ast.Call) and isinstance(inner.func, ast.Name)
            and inner.func.id == "range" and len(inner.args) == 1)


def _fix_len_range_seq(node, ctx):
    inner_arg = node.args[0].args[0]
    return ["range(len(" + ctx.text(inner_arg) + "))"]


def _is_range_len_minus_one(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == "range" and len(node.args) == 1):
        return False
    a = node.args[0]
    return (isinstance(a, ast.BinOp) and isinstance(a.op, ast.Sub)
            and isinstance(a.left, ast.Call) and isinstance(a.left.func, ast.Name)
            and a.left.func.id == "len")


def _fix_range_len_minus_one(node, ctx):
    return ["range(" + ctx.text(node.args[0].left) + ")"]


# ---------------------------------------------------------------------------
# rule: `for i, x in enumerate(seq)` (or bare `seq`) shadows the parameter x
# ---------------------------------------------------------------------------

def _is_enumerate_shadow_param(node, ctx):
    if not isinstance(node, ast.For):
        return False
    if not (isinstance(node.target, ast.Tuple) and len(node.target.elts) == 2):
        return False
    idx_var, elem_var = node.target.elts
    if not (isinstance(idx_var, ast.Name) and isinstance(elem_var, ast.Name)):
        return False
    func = _find_func(node, ctx)
    if func is None or not func.args.args:
        return False
    first_param = func.args.args[0].arg
    if elem_var.id != first_param:
        return False
    it = node.iter
    seq_param = _seq_param(func)
    if isinstance(it, ast.Name) and it.id == seq_param:
        return True
    if (isinstance(it, ast.Call) and isinstance(it.func, ast.Name)
            and it.func.id == "enumerate" and len(it.args) == 1):
        return True
    return False


def _fix_enumerate_shadow_param(node, ctx):
    idx_var = node.target.elts[0]
    func = _find_func(node, ctx)
    first_param = func.args.args[0].arg
    seq_param = _seq_param(func)
    it = node.iter
    if isinstance(it, ast.Name):
        iter_text = "enumerate(" + ctx.text(it) + ")"
    else:
        iter_text = ctx.text(it)
    return [
        "for " + idx_var.id + ", elem in " + iter_text + ":\n"
        "    if " + first_param + " <= elem:\n"
        "        return " + idx_var.id
    ]


# ---------------------------------------------------------------------------
# rule: undefined while-loop counter used as a subscript index and bumped
# inside the loop -- needs an initialisation before the loop.
# ---------------------------------------------------------------------------

def _find_index_name(test):
    for n in ast.walk(test):
        if isinstance(n, ast.Subscript) and isinstance(n.slice, ast.Name):
            return n.slice.id
    return None


def _is_while_missing_counter_init(node, ctx):
    if not isinstance(node, ast.While):
        return False
    func = _find_func(node, ctx)
    if func is None or ctx.parent(node) is not func:
        return False
    body = func.body
    if not body or body[0] is not node:
        return False
    idx_name = _find_index_name(node.test)
    if idx_name is None:
        return False
    if idx_name in {a.arg for a in func.args.args}:
        return False
    incremented = any(isinstance(s, ast.AugAssign) and isinstance(s.target, ast.Name)
                       and s.target.id == idx_name for s in ast.walk(node))
    return incremented


def _fix_while_missing_counter_init(node, ctx):
    idx_name = _find_index_name(node.test)
    return [idx_name + " = 0\n" + ctx.text(node)]


# ---------------------------------------------------------------------------
# rule: `seq(i)` used instead of `seq[i]`
# ---------------------------------------------------------------------------

def _is_call_should_be_subscript(node, ctx):
    if not (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)):
        return False
    func = _find_func(node, ctx)
    if func is None:
        return False
    if node.func.id != _seq_param(func):
        return False
    return len(node.args) == 1 and not node.keywords


def _fix_call_should_be_subscript(node, ctx):
    return [ctx.text(node.func) + "[" + ctx.text(node.args[0]) + "]"]


# ---------------------------------------------------------------------------
# rule: `seq.index[i]` used instead of `seq.index(i)`
# ---------------------------------------------------------------------------

def _is_index_subscript_should_be_call(node, ctx):
    return (isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute)
            and node.value.attr == "index")


def _fix_index_subscript_should_be_call(node, ctx):
    return [ctx.text(node.value) + "(" + ctx.text(node.slice) + ")"]


# ---------------------------------------------------------------------------
# rule: one-character typo for an existing parameter name (NameError)
# ---------------------------------------------------------------------------

def _is_typo_name(node, ctx):
    if not (isinstance(node, ast.Name) and isinstance(node.ctx, ast.Load)):
        return False
    if node.id in _BUILTINS or len(node.id) < 2:
        return False
    func = _find_func(node, ctx)
    if func is None:
        return False
    if node.id in _collect_assigned_names(func):
        return False
    for p in func.args.args:
        if _one_edit_away(p.arg, node.id):
            return True
    return False


def _fix_typo_name(node, ctx):
    func = _find_func(node, ctx)
    for p in func.args.args:
        if _one_edit_away(p.arg, node.id):
            return [p.arg]
    return []


# ---------------------------------------------------------------------------
# rule: `if seq[i] < x: return x` inside a search-style for loop -- the
# comparison direction and the returned value are both wrong.
# ---------------------------------------------------------------------------

def _is_lt_return_x(node, ctx):
    if not isinstance(node, ast.If) or node.orelse:
        return False
    if len(node.body) != 1 or not isinstance(node.body[0], ast.Return):
        return False
    ret = node.body[0]
    if ret.value is None or not isinstance(ret.value, ast.Name):
        return False
    test = node.test
    if not (isinstance(test, ast.Compare) and len(test.ops) == 1
            and isinstance(test.ops[0], ast.Lt)):
        return False
    left = test.left
    comp = test.comparators[0]
    if not isinstance(comp, ast.Name) or not isinstance(left, ast.Subscript):
        return False
    return ret.value.id == comp.id


def _fix_lt_return_x(node, ctx):
    left = node.test.left
    comp_name = ctx.text(node.test.comparators[0])
    idx_text = ctx.text(left.slice)
    return ["if " + ctx.text(left) + " >= " + comp_name + ":\n    return " + idx_text]


# ---------------------------------------------------------------------------
# generic comparison-strictness flips
# ---------------------------------------------------------------------------

def _simple_compare(node):
    return isinstance(node, ast.Compare) and len(node.ops) == 1


def _is_strict_lt(node, ctx):
    return _simple_compare(node) and isinstance(node.ops[0], ast.Lt)


def _fix_lt_to_lte(node, ctx):
    return [ctx.text(node.left) + " <= " + ctx.text(node.comparators[0])]


def _is_lte(node, ctx):
    return _simple_compare(node) and isinstance(node.ops[0], ast.LtE)


def _fix_lte_to_lt(node, ctx):
    return [ctx.text(node.left) + " < " + ctx.text(node.comparators[0])]


def _is_gt(node, ctx):
    return _simple_compare(node) and isinstance(node.ops[0], ast.Gt)


def _fix_gt_to_gte(node, ctx):
    return [ctx.text(node.left) + " >= " + ctx.text(node.comparators[0])]


def _is_gte(node, ctx):
    return _simple_compare(node) and isinstance(node.ops[0], ast.GtE)


def _fix_gte_to_gt(node, ctx):
    return [ctx.text(node.left) + " > " + ctx.text(node.comparators[0])]


# ---------------------------------------------------------------------------

class Fixer:
    def rules(self):
        return [
            Rewrite(name="use_before_list_copy",
                    match=_is_use_before_list_copy,
                    replace=_fix_use_before_list_copy,
                    symptoms=("err:NameError", "wrong")),

            Rewrite(name="for_body_extra_return",
                    match=_is_for_body_extra_return,
                    replace=_fix_for_body_extra_return,
                    symptoms=("wrong",)),

            Rewrite(name="for_if_else_premature_return",
                    match=_is_for_if_else_premature_return,
                    replace=_fix_for_if_else_premature_return,
                    symptoms=("wrong",)),

            Rewrite(name="loop_missing_trailing_return",
                    match=_is_loop_missing_trailing_return,
                    replace=_fix_loop_missing_trailing_return,
                    symptoms=("wrong", "err:TypeError")),

            Rewrite(name="bare_return_should_break",
                    match=_is_bare_return_should_break,
                    replace=_fix_bare_return_should_break,
                    symptoms=("wrong",)),

            Rewrite(name="bad_trailing_return_loopvar",
                    match=_is_bad_trailing_return_loopvar,
                    replace=_fix_bad_trailing_return_loopvar,
                    symptoms=("wrong",)),

            Rewrite(name="decrement_return_off_by_one",
                    match=_is_decrement_return,
                    replace=_fix_decrement_return,
                    symptoms=("wrong",)),

            Rewrite(name="increment_len_return_off_by_one",
                    match=_is_increment_len_return,
                    replace=_fix_increment_len_return,
                    symptoms=("wrong",)),

            Rewrite(name="double_eq_typo",
                    match=_is_double_eq_typo,
                    replace=_fix_double_eq_typo,
                    symptoms=("err:NameError", "wrong")),

            Rewrite(name="discarded_sorted_call",
                    match=_is_discarded_sorted_call,
                    replace=_fix_discarded_sorted_call,
                    symptoms=("wrong",)),

            Rewrite(name="trailing_expr_should_be_return",
                    match=_is_trailing_expr_should_be_return,
                    replace=_fix_trailing_expr_should_be_return,
                    symptoms=("wrong",)),

            Rewrite(name="range_of_seq",
                    match=_is_range_of_seq,
                    replace=_fix_range_of_seq,
                    symptoms=("err:TypeError",)),

            Rewrite(name="bare_len_as_for_iter",
                    match=_is_bare_len_as_for_iter,
                    replace=_fix_bare_len_as_for_iter,
                    symptoms=("err:TypeError",)),

            Rewrite(name="len_range_seq",
                    match=_is_len_range_seq,
                    replace=_fix_len_range_seq,
                    symptoms=("err:TypeError",)),

            Rewrite(name="range_len_minus_one",
                    match=_is_range_len_minus_one,
                    replace=_fix_range_len_minus_one,
                    symptoms=("wrong", "err:IndexError")),

            Rewrite(name="enumerate_shadow_param",
                    match=_is_enumerate_shadow_param,
                    replace=_fix_enumerate_shadow_param,
                    symptoms=("wrong",)),

            Rewrite(name="while_missing_counter_init",
                    match=_is_while_missing_counter_init,
                    replace=_fix_while_missing_counter_init,
                    symptoms=("err:NameError", "err:UnboundLocalError")),

            Rewrite(name="call_should_be_subscript",
                    match=_is_call_should_be_subscript,
                    replace=_fix_call_should_be_subscript,
                    symptoms=("err:TypeError",)),

            Rewrite(name="index_subscript_should_be_call",
                    match=_is_index_subscript_should_be_call,
                    replace=_fix_index_subscript_should_be_call,
                    symptoms=("err:TypeError",)),

            Rewrite(name="typo_parameter_name",
                    match=_is_typo_name,
                    replace=_fix_typo_name,
                    symptoms=("err:NameError",)),

            Rewrite(name="lt_return_x_instead_of_index",
                    match=_is_lt_return_x,
                    replace=_fix_lt_return_x,
                    symptoms=("wrong",)),

            Rewrite(name="strict_lt_should_be_lte",
                    match=_is_strict_lt,
                    replace=_fix_lt_to_lte,
                    symptoms=("wrong",)),

            Rewrite(name="lte_should_be_lt",
                    match=_is_lte,
                    replace=_fix_lte_to_lt,
                    symptoms=("wrong",)),

            Rewrite(name="gt_should_be_gte",
                    match=_is_gt,
                    replace=_fix_gt_to_gte,
                    symptoms=("wrong",)),

            Rewrite(name="gte_should_be_gt",
                    match=_is_gte,
                    replace=_fix_gte_to_gt,
                    symptoms=("wrong",)),
        ]