/-
PyCore syntax, the static analysis (own body, bind, G, N, classification, kind),
edits as subtree replacement at sites, and the footprint F(p, q) of
Definition 4. Everything here is computable.
-/
namespace PyCore

abbrev Name := String
/-- A node's position. The theorem holds for any labelling; with distinct labels
(e.g. source positions), a set of labels is a set of nodes. -/
abbrev Label := Nat

mutual
inductive Expr where
  | const (l : Label) (c : String)
  /-- A read of `x`. `k`, if given, overrides the class of the exception every
  failing lookup raises (the translation may tag a read so); without it the
  class follows the lookup: `UnboundLocalError` for an unset local cell,
  `NameError` otherwise. -/
  | name (l : Label) (x : Name) (k : Option String)
  | bin (l : Label) (op : String) (a b : Expr)
  | call (l : Label) (f a : Expr)
  /-- `lambda x: b`, a function whose body is a block (an expression body `e` is
  `[return e]`); with `comp`, a comprehension's function `λ° x. b`, whose walrus
  targets bind in the scope around it. -/
  | lam (l : Label) (comp : Bool) (x : Name) (b : List Stmt)
  | walrus (l : Label) (x : Name) (e : Expr)
  | yield (l : Label) (e : Expr)
  /-- `a if c else b` -/
  | cond (l : Label) (c a b : Expr)
  /-- `a and b` (`isAnd`) or `a or b`, short-circuit. -/
  | bool (l : Label) (isAnd : Bool) (a b : Expr)
  /-- `yield from e`, delegating through `next` only. -/
  | yieldFrom (l : Label) (e : Expr)
inductive Stmt where
  | assign (l : Label) (x : Name) (e : Expr)
  | del (l : Label) (x : Name)
  | expr (l : Label) (e : Expr)
  | ite (l : Label) (c : Expr) (t u : List Stmt)
  /-- `while c: b else: u` -/
  | while (l : Label) (c : Expr) (b u : List Stmt)
  | ret (l : Label) (e : Expr)
  /-- `def f(x): b` -/
  | defn (l : Label) (f x : Name) (b : List Stmt)
  /-- `class x: b`; `q` is its qualified name (`f.<locals>.C`), which CPython's
  compiler computes from the functions and classes around it. -/
  | cls (l : Label) (x : Name) (q : String) (b : List Stmt)
  | glob (l : Label) (x : Name)
  | nonloc (l : Label) (x : Name)
  /-- `try: b except h₁ as x₁: hb₁ … else: u` -/
  | tryE (l : Label) (b : List Stmt) (hs : List Handler) (u : List Stmt)
  | raise (l : Label) (e : Expr)
  | print (l : Label) (e : Expr)
  | brk (l : Label)
  | cont (l : Label)
/-- A handler clause `except h as x: hb`, labelled `lh`. -/
inductive Handler where
  | mk (lh : Label) (h : Expr) (x : Name) (hb : List Stmt)
end

instance : Inhabited Expr := ⟨.const 0 ""⟩
instance : Inhabited Stmt := ⟨.brk 0⟩

def Expr.label : Expr → Label
  | .const l _ | .name l _ _ | .bin l _ _ _ | .call l _ _ | .lam l _ _ _ | .walrus l _ _
  | .yield l _ | .cond l _ _ _ | .bool l _ _ _ | .yieldFrom l _ => l

def Stmt.label : Stmt → Label
  | .assign l _ _ | .del l _ | .expr l _ | .ite l _ _ _ | .while l _ _ _ | .ret l _
  | .defn l _ _ _ | .cls l _ _ _ | .glob l _ | .nonloc l _ | .tryE l _ _ _
  | .raise l _ | .print l _ | .brk l | .cont l => l

/-- A scope other than the module: a function (`def` or lambda) or a class body,
with the label of the node that introduces it. The module is the empty chain. -/
inductive Scope where
  | fn (l : Label) (comp : Bool) (x : Name) (b : List Stmt)
  | cl (l : Label) (ss : List Stmt)
  deriving Inhabited

/-! ## The own body O(S) -/

/-- What the own body of a scope says about a name: it binds it, binds it by a
walrus (`wal`), declares it `global` or `nonlocal`, or (`yld`) the body yields. -/
inductive Fact where
  | bind (x : Name) | wal (x : Name) | glob (x : Name) | nonloc (x : Name) | yld
  deriving DecidableEq, Repr

def Fact.isWal : Fact → Bool
  | .wal _ => true
  | _ => false

mutual
/-- A comprehension's function adds the walrus targets of its own body (its own
nested comprehensions' included) to the scope around it. -/
def factsE : Expr → List Fact
  | .const _ _ | .name _ _ _ | .lam _ false _ _ => []
  | .lam _ true _ b => (factsB b).filter Fact.isWal
  | .bin _ _ a b | .call _ a b | .bool _ _ a b => factsE a ++ factsE b
  | .walrus _ x e => .wal x :: factsE e
  | .yield _ e | .yieldFrom _ e => .yld :: factsE e
  | .cond _ c a b => factsE c ++ factsE a ++ factsE b
def factsS : Stmt → List Fact
  | .assign _ x e => .bind x :: factsE e
  | .del _ x => [.bind x]
  | .expr _ e | .ret _ e | .raise _ e | .print _ e => factsE e
  | .ite _ c t u => factsE c ++ factsB t ++ factsB u
  | .while _ c b u => factsE c ++ factsB b ++ factsB u
  | .defn _ f _ _ => [.bind f]
  | .cls _ x _ _ => [.bind x]
  | .glob _ x => [.glob x]
  | .nonloc _ x => [.nonloc x]
  | .tryE _ b hs u => factsB b ++ factsHs hs ++ factsB u
  | .brk _ | .cont _ => []
def factsHs : List Handler → List Fact
  | [] => []
  | .mk _ h x hb :: hs => factsE h ++ .bind x :: factsB hb ++ factsHs hs
def factsB : List Stmt → List Fact
  | [] => []
  | s :: ss => factsS s ++ factsB ss
end

/-- The facts of O(S), with the parameter bound. -/
def Scope.facts : Scope → List Fact
  | .fn _ _ x ss => .bind x :: factsB ss
  | .cl _ ss => .bind "__module__" :: .bind "__qualname__" :: factsB ss

def Scope.isComp : Scope → Bool
  | .fn _ c _ _ => c
  | .cl _ _ => false

/-- `bind(S)`: what `S` binds; a walrus target binds in a scope that is no
comprehension. -/
def Scope.binds (S : Scope) (x : Name) : Bool :=
  S.facts.contains (.bind x) || (!S.isComp && S.facts.contains (.wal x))
def Scope.declG (S : Scope) (x : Name) : Bool := S.facts.contains (.glob x)
def Scope.declN (S : Scope) (x : Name) : Bool := S.facts.contains (.nonloc x)
/-- A walrus target of a comprehension's own body. -/
def Scope.walrus (S : Scope) (x : Name) : Bool := S.isComp && S.facts.contains (.wal x)

inductive Kind where
  | plain | gen
  deriving DecidableEq, Repr

/-- generator if O(S) yields, else plain. -/
def Scope.kind : Scope → Kind
  | S@(.fn _ _ _ _) => if S.facts.contains .yld then .gen else .plain
  | .cl _ _ => .plain

/-! ## Classification -/

inductive Cls where
  | loc | free | glob
  deriving DecidableEq, Repr

/-- Whether a comprehension's walrus target `x` is global: the nearest enclosing
scope that is no comprehension is the module or declares `x` global. -/
def walGlobal : List Scope → Name → Bool
  | [], _ => true
  | S :: C, x => if S.isComp then walGlobal C x else S.declG x

/-- The classification by the nearest enclosing function scope that binds or
declares `x`; a class body is no function scope. -/
def enclosing : List Scope → Name → Cls
  | [], _ => .glob
  | .cl _ _ :: C, x => enclosing C x
  | S@(.fn _ _ _ _) :: C, x =>
    if S.declG x then .glob
    else if S.walrus x then (if walGlobal C x then .glob else .free)
    else if S.declN x || S.binds x then .free else enclosing C x

/-- `cls_S(x)` for the scope at the head of the chain (innermost first);
the empty chain is the module. A comprehension's walrus target is free in it (or
global, by `walGlobal`). -/
def clsOf : List Scope → Name → Cls
  | [], _ => .glob
  | S :: C, x =>
    if S.declG x then .glob else if S.declN x then .free
    else if S.walrus x then (if walGlobal C x then .glob else .free)
    else if S.binds x then .loc
    else enclosing C x

/-! ## Edits

An edit replaces subtrees of `p` at sites: an expression by an expression, a
statement of a block by a list of statements (a deletion, a replacement, or an
insertion `[t, s]` / `[s, t]` at the statement `s` it precedes or follows as the
last of its block), and a handler clause by another (labelled as the one it
replaces). `q` is the result. -/
structure Edit where
  e : Label → Option Expr := fun _ => none
  s : Label → Option (List Stmt) := fun _ => none
  h : Label → Option Handler := fun _ => none

def Edit.none : Edit := {}

section
variable (R : Edit)

mutual
def editE : Expr → Expr
  | .const l c => (R.e l).getD (.const l c)
  | .name l x k => (R.e l).getD (.name l x k)
  | .bin l op a b => (R.e l).getD (.bin l op (editE a) (editE b))
  | .call l a b => (R.e l).getD (.call l (editE a) (editE b))
  | .lam l k x b => (R.e l).getD (.lam l k x (editB b))
  | .walrus l x e => (R.e l).getD (.walrus l x (editE e))
  | .yield l e => (R.e l).getD (.yield l (editE e))
  | .yieldFrom l e => (R.e l).getD (.yieldFrom l (editE e))
  | .cond l c a b => (R.e l).getD (.cond l (editE c) (editE a) (editE b))
  | .bool l o a b => (R.e l).getD (.bool l o (editE a) (editE b))
def editS : Stmt → List Stmt
  | .assign l x e => (R.s l).getD [.assign l x (editE e)]
  | .del l x => (R.s l).getD [.del l x]
  | .expr l e => (R.s l).getD [.expr l (editE e)]
  | .ite l c t u => (R.s l).getD [.ite l (editE c) (editB t) (editB u)]
  | .while l c b u => (R.s l).getD [.while l (editE c) (editB b) (editB u)]
  | .ret l e => (R.s l).getD [.ret l (editE e)]
  | .defn l f x b => (R.s l).getD [.defn l f x (editB b)]
  | .cls l x q b => (R.s l).getD [.cls l x q (editB b)]
  | .glob l x => (R.s l).getD [.glob l x]
  | .nonloc l x => (R.s l).getD [.nonloc l x]
  | .tryE l b hs u => (R.s l).getD [.tryE l (editB b) (editHs hs) (editB u)]
  | .raise l e => (R.s l).getD [.raise l (editE e)]
  | .print l e => (R.s l).getD [.print l (editE e)]
  | .brk l => (R.s l).getD [.brk l]
  | .cont l => (R.s l).getD [.cont l]
def editHs : List Handler → List Handler
  | [] => []
  | .mk lh h x hb :: hs => (R.h lh).getD (.mk lh (editE h) x (editB hb)) :: editHs hs
def editB : List Stmt → List Stmt
  | [] => []
  | s :: ss => editS s ++ editB ss
end

/-- The scope of `q` that corresponds to a scope of `p` outside the sites. -/
def editSc : Scope → Scope
  | .fn l k x b => .fn l k x (editB R b)
  | .cl l ss => .cl l (editB R ss)

/-- `x` is classified alike in `p` and `q` in the scope at the head of the chain
and in every scope enclosing it. -/
def alike : List Scope → Name → Bool
  | [], _ => true
  | S :: C, x => clsOf (S :: C) x == clsOf ((S :: C).map (editSc R)) x && alike C x

end

/-- What a class body does before its code, at the class node, in its own scope:
`__module__ = __name__`, then `__qualname__ = 'C'`. These names are bound by every
class body (CPython's compiler emits the stores; a `global` or `nonlocal`
declaration in the body redirects them). -/
def classImplicit : List Name := ["__name__", "__module__", "__qualname__"]

/-! ## Occurrences and functions -/

/-- An item of a program: an occurrence of a name at a node, in the scope at the
head of a chain, or a function scope introduced at a node. -/
inductive Item where
  | occ (l : Label) (x : Name) (C : List Scope)
  | fn (l : Label) (S : Scope)

section
variable (R : Edit)

mutual
/-- The items of the nodes outside the sites of `R` (all of them for `Edit.none`). -/
def itemsE (C : List Scope) : Expr → List Item
  | .const _ _ => []
  | .name l x _ => if (R.e l).isSome then [] else [.occ l x C]
  | .bin l _ a b | .call l a b | .bool l _ a b =>
    if (R.e l).isSome then [] else itemsE C a ++ itemsE C b
  | .lam l k x b =>
    if (R.e l).isSome then [] else
    .fn l (.fn l k x b) :: .occ l x (.fn l k x b :: C) :: itemsB (.fn l k x b :: C) b
  | .walrus l x e => if (R.e l).isSome then [] else .occ l x C :: itemsE C e
  | .yield l e | .yieldFrom l e => if (R.e l).isSome then [] else itemsE C e
  | .cond l c a b => if (R.e l).isSome then [] else itemsE C c ++ itemsE C a ++ itemsE C b
def itemsS (C : List Scope) : Stmt → List Item
  | .assign l x e => if (R.s l).isSome then [] else .occ l x C :: itemsE C e
  | .del l x | .glob l x | .nonloc l x => if (R.s l).isSome then [] else [.occ l x C]
  | .expr l e | .ret l e | .raise l e | .print l e =>
    if (R.s l).isSome then [] else itemsE C e
  | .ite l c t u => if (R.s l).isSome then [] else itemsE C c ++ itemsB C t ++ itemsB C u
  | .while l c b u => if (R.s l).isSome then [] else itemsE C c ++ itemsB C b ++ itemsB C u
  | .defn l f x b =>
    if (R.s l).isSome then [] else
    .occ l f C :: .fn l (.fn l false x b) :: .occ l x (.fn l false x b :: C) ::
      itemsB (.fn l false x b :: C) b
  | .cls l x _ b =>
    if (R.s l).isSome then [] else
    .occ l x C :: (classImplicit.map fun y => .occ l y (.cl l b :: C)) ++ itemsB (.cl l b :: C) b
  | .tryE l b hs u => if (R.s l).isSome then [] else itemsB C b ++ itemsHs C hs ++ itemsB C u
  | .brk _ | .cont _ => []
def itemsHs (C : List Scope) : List Handler → List Item
  | [] => []
  | .mk lh h x hb :: hs =>
    (if (R.h lh).isSome then [] else itemsE C h ++ .occ lh x C :: itemsB C hb) ++ itemsHs C hs
def itemsB (C : List Scope) : List Stmt → List Item
  | [] => []
  | s :: ss => itemsS C s ++ itemsB C ss
end

mutual
/-- Every label of a list of nodes. -/
def labelsE : Expr → List Label
  | .const l _ | .name l _ _ => [l]
  | .bin l _ a b | .call l a b | .bool l _ a b => l :: labelsE a ++ labelsE b
  | .lam l _ _ b => l :: labelsB b
  | .walrus l _ b | .yield l b | .yieldFrom l b => l :: labelsE b
  | .cond l c a b => l :: labelsE c ++ labelsE a ++ labelsE b
def labelsS : Stmt → List Label
  | .assign l _ e | .expr l e | .ret l e | .raise l e | .print l e => l :: labelsE e
  | .del l _ | .glob l _ | .nonloc l _ | .brk l | .cont l => [l]
  | .ite l c t u | .while l c t u => l :: labelsE c ++ labelsB t ++ labelsB u
  | .defn l _ _ b | .cls l _ _ b => l :: labelsB b
  | .tryE l b hs u => l :: labelsB b ++ labelsHs hs ++ labelsB u
def labelsHs : List Handler → List Label
  | [] => []
  | .mk lh h _ hb :: hs => lh :: labelsE h ++ labelsB hb ++ labelsHs hs
def labelsB : List Stmt → List Label
  | [] => []
  | s :: ss => labelsS s ++ labelsB ss
end

mutual
/-- Part (1): the nodes of the replaced subtrees. -/
def part1E : Expr → List Label
  | e@(.const l _) | e@(.name l _ _) => if (R.e l).isSome then labelsE e else []
  | e@(.bin l _ a b) | e@(.call l a b) | e@(.bool l _ a b) =>
    if (R.e l).isSome then labelsE e else part1E a ++ part1E b
  | e@(.lam l _ _ b) => if (R.e l).isSome then labelsE e else part1B b
  | e@(.walrus l _ b) | e@(.yield l b) | e@(.yieldFrom l b) =>
    if (R.e l).isSome then labelsE e else part1E b
  | e@(.cond l c a b) =>
    if (R.e l).isSome then labelsE e else part1E c ++ part1E a ++ part1E b
def part1S : Stmt → List Label
  | s@(.assign l _ e) | s@(.expr l e) | s@(.ret l e) | s@(.raise l e) | s@(.print l e) =>
    if (R.s l).isSome then labelsS s else part1E e
  | s@(.del l _) | s@(.glob l _) | s@(.nonloc l _) | s@(.brk l) | s@(.cont l) =>
    if (R.s l).isSome then labelsS s else []
  | s@(.ite l c t u) | s@(.while l c t u) =>
    if (R.s l).isSome then labelsS s else part1E c ++ part1B t ++ part1B u
  | s@(.defn l _ _ b) | s@(.cls l _ _ b) => if (R.s l).isSome then labelsS s else part1B b
  | s@(.tryE l b hs u) =>
    if (R.s l).isSome then labelsS s else part1B b ++ part1Hs hs ++ part1B u
def part1Hs : List Handler → List Label
  | [] => []
  | .mk lh h x hb :: hs =>
    (if (R.h lh).isSome then labelsHs [.mk lh h x hb] else part1E h ++ part1B hb) ++ part1Hs hs
def part1B : List Stmt → List Label
  | [] => []
  | s :: ss => part1S s ++ part1B ss
end

mutual
/-- The roots of the replaced subtrees: the sites themselves. -/
def rootsE : Expr → List Label
  | (.const l _) | (.name l _ _) => if (R.e l).isSome then [l] else []
  | (.bin l _ a b) | (.call l a b) | (.bool l _ a b) =>
    if (R.e l).isSome then [l] else rootsE a ++ rootsE b
  | (.lam l _ _ b) => if (R.e l).isSome then [l] else rootsB b
  | (.walrus l _ b) | (.yield l b) | (.yieldFrom l b) => if (R.e l).isSome then [l] else rootsE b
  | (.cond l c a b) => if (R.e l).isSome then [l] else rootsE c ++ rootsE a ++ rootsE b
def rootsS : Stmt → List Label
  | (.assign l _ e) | (.expr l e) | (.ret l e) | (.raise l e) | (.print l e) =>
    if (R.s l).isSome then [l] else rootsE e
  | (.del l _) | (.glob l _) | (.nonloc l _) | (.brk l) | (.cont l) =>
    if (R.s l).isSome then [l] else []
  | (.ite l c t u) | (.while l c t u) =>
    if (R.s l).isSome then [l] else rootsE c ++ rootsB t ++ rootsB u
  | (.defn l _ _ b) | (.cls l _ _ b) => if (R.s l).isSome then [l] else rootsB b
  | (.tryE l b hs u) => if (R.s l).isSome then [l] else rootsB b ++ rootsHs hs ++ rootsB u
def rootsHs : List Handler → List Label
  | [] => []
  | .mk lh h _ hb :: hs =>
    (if (R.h lh).isSome then [lh] else rootsE h ++ rootsB hb) ++ rootsHs hs
def rootsB : List Stmt → List Label
  | [] => []
  | s :: ss => rootsS s ++ rootsB ss
end

/-- Part (2): occurrences, outside the sites, of a name classified differently in
`q` in their scope or a scope enclosing it. -/
def part2 (p : List Stmt) : List Label :=
  (itemsB R [] p).filterMap fun
    | .occ l x C => if alike R C x then none else some l
    | .fn _ _ => none

/-- The functions of both programs whose kind differs. -/
def kindChanges (p : List Stmt) : List Label :=
  (itemsB R [] p).filterMap fun
    | .fn l S => if S.kind == (editSc R S).kind then none else some l
    | .occ _ _ _ => none

def Item.label : Item → Label
  | .occ l _ _ | .fn l _ => l

/-- An item part (2) or (3) of the footprint flags. -/
def Item.bad (R : Edit) : Item → Bool
  | .occ _ x C => !alike R C x
  | .fn _ S => S.kind != (editSc R S).kind

/-- The flagged items' nodes: occurrences classified differently, and
functions whose kind changes. -/
def flagged (p : List Stmt) : List Label :=
  (itemsB R [] p).filterMap fun i => if i.bad R then some i.label else none

/-- The footprint: `none` stands for all of `p` (part (3) fires). -/
def footprint? (p : List Stmt) : Option (List Label) :=
  if kindChanges R p = [] then some (part1B R p ++ part2 R p) else none

/-- Membership in F(p, q): part (3) makes it every node of `p`. -/
def inFootprint (p : List Stmt) (l : Label) : Prop :=
  match footprint? R p with
  | some L => l ∈ L
  | none => l ∈ labelsB p

end

end PyCore
