/-
Surf, the surface language of Lemma A.3: the Python that the buggy programs
of Section 6 and the repairs use, node for node as CPython's `ast` gives it, and
its static analysis, defined directly from the language reference and not through
the translation: own body, bind, G, N, classification, kind, and the occurrences
of names. A comprehension is a nested function scope whose first iterable the
scope around it evaluates; a walrus target in a comprehension is bound in the
nearest enclosing scope that is not a comprehension and declared `nonlocal` or
`global` in the comprehension (PEP 572); a private name in a class is mangled
(CPython's `_Py_Mangle`). Everything is computable.
-/
import PyCore.Syntax
import Common.Interp

namespace Surf
open PyCore (Name Label Fact Cls Kind)

/-- A parameter's kind: positional-only, positional-or-keyword, `*args`,
keyword-only, `**kwargs`. -/
inductive PKind where
  | posonly | pos | vararg | kwonly | kwarg
  deriving DecidableEq, Repr

/-- A comprehension's form. -/
inductive CompKind where
  | list | set | dict | gen
  deriving DecidableEq, Repr

mutual
/-- Expressions, as `ast.expr`. A target (of an assignment, `for`, `del`, a
generator) is an expression in store context, as in `ast`. -/
inductive Expr where
  | const (l : Label) (c : String)
  | name (l : Label) (x : Name)
  | bin (l : Label) (op : String) (a b : Expr)
  | unary (l : Label) (op : String) (a : Expr)
  /-- `and` / `or` over two or more operands. -/
  | boolop (l : Label) (op : String) (es : List Expr)
  /-- `a op₁ e₁ op₂ e₂ …`; the operands after the first are `es`. -/
  | compare (l : Label) (a : Expr) (ops : List String) (es : List Expr)
  | ifexp (l : Label) (c a b : Expr)
  /-- Positional arguments (`star` for `*e`) and keyword arguments. -/
  | call (l : Label) (f : Expr) (args : List Expr) (kws : List Kw)
  | attr (l : Label) (e : Expr) (a : Name)
  | sub (l : Label) (e i : Expr)
  | slice (l : Label) (lo hi st : Option Expr)
  | star (l : Label) (e : Expr)
  | list (l : Label) (es : List Expr)
  | tuple (l : Label) (es : List Expr)
  | set (l : Label) (es : List Expr)
  | dict (l : Label) (kvs : List DItem)
  | lam (l : Label) (ps : List Param) (b : Expr)
  /-- A comprehension: its element (key and value for a dictionary) and generators. -/
  | comp (l : Label) (k : CompKind) (es : List Expr) (gs : List Gen)
  | walrus (l : Label) (x : Name) (e : Expr)
  | yield (l : Label) (e : Option Expr)
  | yieldFrom (l : Label) (e : Expr)
  /-- An f-string: its constant parts and formatted values. -/
  | fstr (l : Label) (parts : List Expr)
  | fmt (l : Label) (e : Expr) (conv : Int) (spec : Option Expr)
/-- A keyword argument `x=e`, or `**e` (`x = none`). -/
inductive Kw where
  | mk (l : Label) (x : Option Name) (e : Expr)
/-- A dictionary item `k: v`, or `**v` (`k = none`). -/
inductive DItem where
  | mk (k : Option Expr) (v : Expr)
/-- A parameter, with its kind, default and annotation. -/
inductive Param where
  | mk (l : Label) (x : Name) (k : PKind) (dflt ann : Option Expr)
/-- A generator `for t in i if c …` of a comprehension. -/
inductive Gen where
  | mk (l : Label) (t i : Expr) (ifs : List Expr)
end

/-- `import name as asname` or `from m import name as asname`. -/
structure Alias where
  l : Label
  name : Name
  asname : Option Name

mutual
/-- Statements, as `ast.stmt`. Left out, as the paper excludes them: `with`,
`finally`, `match`, `async`, `try`/`except*`, type parameters. -/
inductive Stmt where
  | expr (l : Label) (e : Expr)
  /-- `t₁ = t₂ = … = e` -/
  | assign (l : Label) (ts : List Expr) (e : Expr)
  | augassign (l : Label) (t : Expr) (op : String) (e : Expr)
  | annassign (l : Label) (t ann : Expr) (v : Option Expr)
  | del (l : Label) (ts : List Expr)
  | ite (l : Label) (c : Expr) (t u : List Stmt)
  /-- `while c: b else: u` -/
  | while (l : Label) (c : Expr) (b u : List Stmt)
  /-- `for t in it: b else: u` -/
  | for (l : Label) (t it : Expr) (b u : List Stmt)
  | brk (l : Label)
  | cont (l : Label)
  | pass (l : Label)
  | ret (l : Label) (e : Option Expr)
  /-- `@ds def f(ps) -> r: b` -/
  | defn (l : Label) (f : Name) (ps : List Param) (b : List Stmt) (ds : List Expr) (r : Option Expr)
  /-- `@ds class x(bs, ks): b` -/
  | cls (l : Label) (x : Name) (bs : List Expr) (ks : List Kw) (b : List Stmt) (ds : List Expr)
  | glob (l : Label) (xs : List Name)
  | nonloc (l : Label) (xs : List Name)
  /-- `try: b except …: … else: u` -/
  | tryE (l : Label) (b : List Stmt) (hs : List Handler) (u : List Stmt)
  /-- `raise e from c` -/
  | raise (l : Label) (e c : Option Expr)
  | imp (l : Label) (al : List Alias)
  | impFrom (l : Label) (m : Option Name) (al : List Alias) (lvl : Nat)
  | assert (l : Label) (t : Expr) (msg : Option Expr)
/-- `except ty as x: b` (`ty = none` for a bare `except`). -/
inductive Handler where
  | mk (l : Label) (ty : Option Expr) (x : Option Name) (b : List Stmt)
end

def Expr.label : Expr → Label
  | .const l .. | .name l .. | .bin l .. | .unary l .. | .boolop l .. | .compare l .. | .ifexp l ..
  | .call l .. | .attr l .. | .sub l .. | .slice l .. | .star l .. | .list l .. | .tuple l ..
  | .set l .. | .dict l .. | .lam l .. | .comp l .. | .walrus l .. | .yield l .. | .yieldFrom l ..
  | .fstr l .. | .fmt l .. => l

def Stmt.label : Stmt → Label
  | .expr l .. | .assign l .. | .augassign l .. | .annassign l .. | .del l .. | .ite l ..
  | .while l .. | .for l .. | .brk l | .cont l | .pass l | .ret l .. | .defn l .. | .cls l ..
  | .glob l .. | .nonloc l .. | .tryE l .. | .raise l .. | .imp l .. | .impFrom l .. | .assert l .. => l

def Param.label : Param → Label | .mk l .. => l
def Param.name : Param → Name | .mk _ x .. => x
def Handler.ty : Handler → Option Expr | .mk _ ty _ _ => ty

/-- The name an import binds: `asname`, else the first component of the module. -/
def Alias.bound (a : Alias) : Name := a.asname.getD ((a.name.splitOn ".").headD a.name)

/-- The aliases that bind a name (`from m import *` binds none statically). -/
def bindingAliases (al : List Alias) : List Alias := al.filter (·.name != "*")

/-! ## Scopes and mangling -/

/-- A scope other than the module: a function (`def`), a lambda, a class body,
or a comprehension, with the label of the node that introduces it. The module is
the empty chain. -/
inductive Scope where
  | fn (l : Label) (f : Name) (ps : List Param) (b : List Stmt)
  | lam (l : Label) (ps : List Param) (b : Expr)
  | cl (l : Label) (x : Name) (b : List Stmt)
  | comp (l : Label) (k : CompKind) (es : List Expr) (gs : List Gen)

def Scope.label : Scope → Label
  | .fn l .. | .lam l .. | .cl l .. | .comp l .. => l

def Scope.isComp : Scope → Bool
  | .comp .. => true
  | _ => false

/-- The class whose name mangles private names: the innermost class of the chain
(functions and comprehensions nested in a class keep it). -/
def priv : List Scope → Option Name
  | [] => none
  | .cl _ x _ :: _ => some x
  | _ :: C => priv C

/-- CPython's `_Py_Mangle`: in class `_C`, `__x` is `_C__x`, unless it ends in
`__` or holds a dot, or the class name is all underscores. -/
def mangle (c : Option Name) (x : Name) : Name :=
  match c with
  | none => x
  | some c =>
    let c := (c.dropWhile (· == '_')).toString
    if x.startsWith "__" && !x.endsWith "__" && !x.contains '.' && !c.isEmpty then "_" ++ c ++ x
    else x

/-! ## The own body O(S) -/

section
variable (p : Option Name)

mutual
/-- What an expression adds to the own body of the scope evaluating it; `st` holds
in store context, where a name is bound. A lambda adds its defaults; a
comprehension its first iterable and the walrus targets of its body, its nested
comprehensions' included (PEP 572: they bind in the scope around); the rest of
each is a scope of its own. -/
def factsE (st : Bool) : Expr → List Fact
  | .const .. => []
  | .name _ x => if st then [.bind (mangle p x)] else []
  | .bin _ _ a b | .sub _ a b => factsE false a ++ factsE false b
  | .unary _ _ a | .attr _ a _ => factsE false a
  | .star _ a => factsE st a
  | .list _ es | .tuple _ es => factsEs st es
  | .boolop _ _ es | .set _ es | .fstr _ es => factsEs false es
  | .compare _ a _ es => factsE false a ++ factsEs false es
  | .ifexp _ c a b => factsE false c ++ factsE false a ++ factsE false b
  | .call _ f args kws => factsE false f ++ factsEs false args ++ factsKs kws
  | .slice _ a b c => factsO a ++ factsO b ++ factsO c
  | .dict _ kvs => factsDs kvs
  | .lam _ ps _ => factsPs ps
  | .comp _ _ es gs => factsG1 gs ++ (factsGs true gs ++ factsEs false es).filter Fact.isWal
  | .walrus _ x e => .wal (mangle p x) :: factsE false e
  | .yield _ e => .yld :: factsO e
  | .yieldFrom _ e => .yld :: factsE false e
  | .fmt _ e _ s => factsE false e ++ factsO s
def factsO : Option Expr → List Fact
  | none => []
  | some e => factsE false e
def factsEs (st : Bool) : List Expr → List Fact
  | [] => []
  | e :: es => factsE st e ++ factsEs st es
def factsKs : List Kw → List Fact
  | [] => []
  | .mk _ _ e :: ks => factsE false e ++ factsKs ks
def factsDs : List DItem → List Fact
  | [] => []
  | .mk k v :: kvs => factsO k ++ factsE false v ++ factsDs kvs
def factsPs : List Param → List Fact
  | [] => []
  | .mk _ _ _ d a :: ps => factsO d ++ factsO a ++ factsPs ps
def factsG1 : List Gen → List Fact
  | [] => []
  | .mk _ _ i _ :: _ => factsE false i
/-- A comprehension's generators in its own scope: targets bound, conditions, and
the iterables after the first. -/
def factsGs (first : Bool) : List Gen → List Fact
  | [] => []
  | .mk _ t i ifs :: gs =>
    (if first then [] else factsE false i) ++ factsE true t ++ factsEs false ifs ++ factsGs false gs
end

end

section
variable (p : Option Name)

def paramBinds (ps : List Param) : List Fact := ps.map fun q => .bind (mangle p q.name)

mutual
/-- The own body of a statement: what it binds, declares, or yields in its scope
(no comprehension, so the walrus targets of its comprehensions are bound here). -/
def factsS : Stmt → List Fact
  | .expr _ e => factsE p false e
  | .assign _ ts e => factsE p false e ++ factsEs p true ts
  | .augassign _ t _ e => factsE p true t ++ factsE p false e
  | .annassign _ t a v => factsE p true t ++ factsE p false a ++ factsO p v
  | .del _ ts => factsEs p true ts
  | .ite _ c t u => factsE p false c ++ factsB t ++ factsB u
  | .while _ c b u => factsE p false c ++ factsB b ++ factsB u
  | .for _ t it b u => factsE p true t ++ factsE p false it ++ factsB b ++ factsB u
  | .brk _ | .cont _ | .pass _ => []
  | .ret _ e => factsO p e
  | .defn _ f ps _ ds r =>
    factsPs p ps ++ factsEs p false ds ++ factsO p r ++ [.bind (mangle p f)]
  | .cls _ x bs ks _ ds =>
    factsEs p false bs ++ factsKs p ks ++ factsEs p false ds ++ [.bind (mangle p x)]
  | .glob _ xs => xs.map fun x => .glob (mangle p x)
  | .nonloc _ xs => xs.map fun x => .nonloc (mangle p x)
  | .tryE _ b hs u => factsB b ++ factsHs hs ++ factsB u
  | .raise _ e c => factsO p e ++ factsO p c
  | .imp _ al | .impFrom _ _ al _ => (bindingAliases al).map fun a => .bind (mangle p a.bound)
  | .assert _ t m => factsE p false t ++ factsO p m
def factsHs : List Handler → List Fact
  | [] => []
  | .mk _ ty x b :: hs =>
    factsO p ty ++ (x.map fun x => Fact.bind (mangle p x)).toList ++ factsB b ++ factsHs hs
def factsB : List Stmt → List Fact
  | [] => []
  | s :: ss => factsS s ++ factsB ss
end

end

/-- O(S) of a scope in the chain `C`: its parameters, the own body, and, for a
class, `__module__` and `__qualname__` (as in PyCore); for a comprehension, its
targets and own body (whose walrus targets are `wal` facts), and for a generator
expression, the `yield` of its element. -/
def Scope.facts (C : List Scope) (S : Scope) : List Fact :=
  let p := priv (S :: C)
  match S with
  | .fn _ _ ps b => paramBinds p ps ++ factsB p b
  | .lam _ ps b => paramBinds p ps ++ factsE p false b
  | .cl _ _ b => .bind "__module__" :: .bind "__qualname__" :: factsB p b
  | .comp _ k es gs => (if k = .gen then [.yld] else []) ++ factsGs p true gs ++ factsEs p false es

/-- `bind(S)`; a walrus target binds in a scope that is no comprehension. -/
def Scope.binds (C : List Scope) (S : Scope) (x : Name) : Bool :=
  (S.facts C).contains (.bind x) || (!S.isComp && (S.facts C).contains (.wal x))
/-- A walrus target of a comprehension's own body. -/
def Scope.walrus (C : List Scope) (S : Scope) (x : Name) : Bool :=
  S.isComp && (S.facts C).contains (.wal x)
def Scope.declG (C : List Scope) (S : Scope) (x : Name) : Bool := (S.facts C).contains (.glob x)
def Scope.declN (C : List Scope) (S : Scope) (x : Name) : Bool := (S.facts C).contains (.nonloc x)

/-- A function scope is a generator if O(S) yields. -/
def Scope.kind (C : List Scope) (S : Scope) : Kind :=
  match S with
  | .cl .. => .plain
  | _ => if (S.facts C).contains .yld then .gen else .plain

/-! ## Classification -/

/-- Whether a comprehension's walrus target `x` is global: the nearest enclosing
scope that is no comprehension is the module or declares `x` global (CPython's
`symtable_extend_namedexpr_scope`). -/
def walGlobal : List Scope → Name → Bool
  | [], _ => true
  | S :: C, x => if S.isComp then walGlobal C x else S.declG C x

/-- The nearest enclosing function scope (a `def`, lambda, or comprehension; a
class body is none) that binds or declares `x`; a comprehension's walrus target is
free (or global) in it. -/
def enclosing : List Scope → Name → Cls
  | [], _ => .glob
  | .cl .. :: C, x => enclosing C x
  | S :: C, x =>
    if S.declG C x then .glob
    else if S.walrus C x then (if walGlobal C x then .glob else .free)
    else if S.declN C x || S.binds C x then .free else enclosing C x

/-- `cls_S(x)` for the scope at the head of the chain; the empty chain is the module. -/
def clsOf : List Scope → Name → Cls
  | [], _ => .glob
  | S :: C, x =>
    if S.declG C x then .glob else if S.declN C x then .free
    else if S.walrus C x then (if walGlobal C x then .glob else .free)
    else if S.binds C x then .loc
    else enclosing C x

/-! ## Occurrences and functions -/

/-- An occurrence of a (mangled) name at a node, in the scope at the head of a
chain, or a function scope (`def`, lambda, comprehension) with its chain. -/
inductive Item where
  | occ (l : Label) (x : Name) (C : List Scope)
  | fn (l : Label) (C : List Scope) (S : Scope)

def paramOccs (C : List Scope) (ps : List Param) : List Item :=
  ps.map fun q => .occ q.label (mangle (priv C) q.name) C

mutual
/-- The occurrences: names read or written, walrus targets, parameters; a
function's defaults and annotations and a comprehension's first iterable in the
scope around it. -/
def itemsE (C : List Scope) : Expr → List Item
  | .const .. => []
  | .name l x => [.occ l (mangle (priv C) x) C]
  | .bin _ _ a b | .sub _ a b => itemsE C a ++ itemsE C b
  | .unary _ _ a | .attr _ a _ | .star _ a | .yieldFrom _ a => itemsE C a
  | .boolop _ _ es | .set _ es | .fstr _ es | .list _ es | .tuple _ es => itemsEs C es
  | .compare _ a _ es => itemsE C a ++ itemsEs C es
  | .ifexp _ c a b => itemsE C c ++ itemsE C a ++ itemsE C b
  | .call _ f args kws => itemsE C f ++ itemsEs C args ++ itemsKs C kws
  | .slice _ a b c => itemsO C a ++ itemsO C b ++ itemsO C c
  | .dict _ kvs => itemsDs C kvs
  | .lam l ps b =>
    itemsPs C ps ++ .fn l C (.lam l ps b) :: paramOccs (.lam l ps b :: C) ps ++
      itemsE (.lam l ps b :: C) b
  | .comp l k es gs =>
    itemsG1 C gs ++ .fn l C (.comp l k es gs) ::
      itemsGs (.comp l k es gs :: C) true gs ++ itemsEs (.comp l k es gs :: C) es
  | .walrus l x e => .occ l (mangle (priv C) x) C :: itemsE C e
  | .yield _ e => itemsO C e
  | .fmt _ e _ s => itemsE C e ++ itemsO C s
def itemsO (C : List Scope) : Option Expr → List Item
  | none => []
  | some e => itemsE C e
def itemsEs (C : List Scope) : List Expr → List Item
  | [] => []
  | e :: es => itemsE C e ++ itemsEs C es
def itemsKs (C : List Scope) : List Kw → List Item
  | [] => []
  | .mk _ _ e :: ks => itemsE C e ++ itemsKs C ks
def itemsDs (C : List Scope) : List DItem → List Item
  | [] => []
  | .mk k v :: kvs => itemsO C k ++ itemsE C v ++ itemsDs C kvs
def itemsPs (C : List Scope) : List Param → List Item
  | [] => []
  | .mk _ _ _ d a :: ps => itemsO C d ++ itemsO C a ++ itemsPs C ps
def itemsG1 (C : List Scope) : List Gen → List Item
  | [] => []
  | .mk _ _ i _ :: _ => itemsE C i
def itemsGs (C : List Scope) (first : Bool) : List Gen → List Item
  | [] => []
  | .mk _ t i ifs :: gs =>
    (if first then [] else itemsE C i) ++ itemsE C t ++ itemsEs C ifs ++ itemsGs C false gs
end

mutual
/-- A statement's items. A class node is an occurrence of `__name__`, `__module__`
and `__qualname__` in its body (as in PyCore). -/
def itemsS (C : List Scope) (s : Stmt) : List Item := match s with
  | .expr _ e => itemsE C e
  | .assign _ ts e => itemsE C e ++ itemsEs C ts
  | .augassign _ t _ e => itemsE C t ++ itemsE C e
  | .annassign _ t a v => itemsE C t ++ itemsE C a ++ itemsO C v
  | .del _ ts => itemsEs C ts
  | .ite _ c t u => itemsE C c ++ itemsB C t ++ itemsB C u
  | .while _ c b u => itemsE C c ++ itemsB C b ++ itemsB C u
  | .for _ t it b u => itemsE C t ++ itemsE C it ++ itemsB C b ++ itemsB C u
  | .brk _ | .cont _ | .pass _ => []
  | .ret _ e => itemsO C e
  | .defn l f ps b ds r =>
    itemsPs C ps ++ itemsEs C ds ++ itemsO C r ++
      .occ l (mangle (priv C) f) C :: .fn l C (.fn l f ps b) ::
      paramOccs (.fn l f ps b :: C) ps ++ itemsB (.fn l f ps b :: C) b
  | .cls l x bs ks b ds =>
    itemsEs C bs ++ itemsKs C ks ++ itemsEs C ds ++ .occ l (mangle (priv C) x) C ::
      (PyCore.classImplicit.map fun y => .occ l y (.cl l x b :: C)) ++ itemsB (.cl l x b :: C) b
  | .glob l xs | .nonloc l xs => xs.map fun x => .occ l (mangle (priv C) x) C
  | .tryE _ b hs u => itemsB C b ++ itemsHs C hs ++ itemsB C u
  | .raise _ e c => itemsO C e ++ itemsO C c
  | .imp _ al | .impFrom _ _ al _ =>
    (bindingAliases al).map fun a => .occ a.l (mangle (priv C) a.bound) C
  | .assert _ t m => itemsE C t ++ itemsO C m
def itemsHs (C : List Scope) : List Handler → List Item
  | [] => []
  | .mk l ty x b :: hs =>
    itemsO C ty ++ (x.map fun x => Item.occ l (mangle (priv C) x) C).toList ++ itemsB C b ++
      itemsHs C hs
def itemsB (C : List Scope) : List Stmt → List Item
  | [] => []
  | s :: ss => itemsS C s ++ itemsB C ss
end

/-! ## Shared by the semantics and the translation -/

def unstar : Expr → Expr
  | .star _ e => e
  | e => e

def isStar : Expr → Bool
  | .star .. => true
  | _ => false

/-- A constant after CPython's AST optimizer: a constant, a sign of one, or a tuple of them. -/
def isConstE : Expr → Bool
  | .const .. => true
  | .unary _ op (.const ..) => op == "USub" || op == "UAdd" || op == "Invert"
  | .tuple _ es => es.attach.all fun ⟨e, _⟩ => isConstE e
  | _ => false

/-- The positions of a starred target: before it, whether there is one, after it. -/
def splitStar (ts : List Expr) : Nat × Bool × Nat :=
  match ts.findIdx? isStar with
  | some i => (i, true, ts.length - i - 1)
  | none => (ts.length, false, 0)

def PKind.pk : PKind → Py.PK
  | .posonly => .posonly | .pos => .pos | .vararg => .vararg | .kwonly => .kwonly | .kwarg => .kwarg

def Param.kind : Param → PKind | .mk _ _ k _ _ => k
def Param.dflt : Param → Option Expr | .mk _ _ _ d _ => d
def Param.ann : Param → Option Expr | .mk _ _ _ _ a => a

/-- The annotations a `def` evaluates, in CPython's order: the positional-or-keyword
parameters, the positional-only ones, `*args`, the keyword-only ones, `**kwargs`,
the return annotation. -/
def annOrder (ps : List Param) (r : Option Expr) : List (Option Expr) :=
  let of (k : PKind) := (ps.filter (Param.kind · == k)).filterMap Param.ann
  (of .pos ++ of .posonly ++ of .vararg ++ of .kwonly ++ of .kwarg ++ r.toList).map some

/-- A scope's name in a qualified name; list, set and dictionary comprehensions
are inlined (PEP 709) and have none. -/
def Scope.qualPart : Scope → Option String
  | .fn _ f _ _ => some f
  | .lam .. => some "<lambda>"
  | .cl _ x _ => some x
  | .comp _ .gen .. => some "<genexpr>"
  | .comp .. => none

/-- CPython's `__qualname__` of a scope named `n` in the chain `C`: `n` at module
level or when the scope around declares it `global`, else the qualified name of
the scope around and `n`, joined by `.<locals>.` after a function and `.` after
a class. -/
def qualIn : List Scope → Name → String
  | [], n => n
  | P :: C, n => match Scope.qualPart P with
    | none => qualIn C n
    | some pn =>
      if P.declG C (mangle (priv (P :: C)) n) then n
      else qualIn C pn ++ (match P with | .cl .. => "." | _ => ".<locals>.") ++ n

/-- Whether a name a comprehension reads is a local of the function around it, through
list, set and dictionary comprehensions only: CPython 3.13 inlines those into the
scope around (PEP 709), so an unset such name raises `UnboundLocalError` there, while
through a generator expression or a lambda it is a free variable (`NameError`). -/
def inlinedLocal (ch : List Scope) (x : Name) : Bool :=
  match ch with
  | .comp _ k _ _ :: C => k != .gen && go C
  | _ => false
where
  go : List Scope → Bool
    | .comp _ k _ _ :: C => k != .gen && go C
    | (S@(.fn ..)) :: C | (S@(.lam ..)) :: C => clsOf (S :: C) x == .loc
    | _ => false

end Surf
