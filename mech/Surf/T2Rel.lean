/-
(T2), the relation: a Surf.Sem configuration of `p` and a PyCore configuration of ⌊p⌋.

* values: the same `Py.Val` on both sides;
* the interpreter state, the object counter `next`, the result: equal; objects at the same
  address (an interpretation may branch on addresses);
* cells and the module dictionary: equal at every name with no leading dot; names with a dot
  are the translation's fresh names (no Python identifier has one);
* frames: the same id, kind and closure environment (on names with no dot), PyCore's chain the
  image of Surf's (`trChain`), both classifications cached as `clsOf` of the chain, a class
  namespace equal to PyCore's without the dotted names, and the code related by `CR` (the
  control) and `KRel` (the continuation): each Surf continuation item is paired with the PyCore
  items the translated code has pushed for it at that point;
* objects at each address: a Surf function object with a PyCore closure of the translated scope,
  a generator with a generator whose suspended frame is related (or, before its first resumption
  or inside a `yield from`, in one of the `Special` states).

What the relation needs beyond equal values and equal code:

* Fresh-name contents. PyCore keeps in fresh names what Surf keeps in its continuation (a `for`
  loop's iterator and flag, an assignment's value while the targets' parts are evaluated, an
  augmented target's parts, a comprehension's accumulator, a comparison's middle operand, …).
  `KRel` reads them through `Cx.rd` (the frame's reading of a name, `rdOf`) and `Cx.own` (the
  frame's own cell, `ownOf`, for `$set`/`$get`).
* Label budgets. A fresh name `.tag l` is written only by the code made for the node `l`. `KRel`
  is indexed by a set `U` of labels: every code piece that may run above the continuation has
  its labels in `U`, and the items reading a fresh name of the node `l` sit below a level whose
  `U` excludes `l` (`Rm U l`). So a write by the running code never changes what an item below
  reads (`KRel.ext`, `T2Cases.lean`).
* History. `Cx.H` holds the Surf nodes touched before; an item whose PyCore code evaluates nodes
  made for a node touched earlier (a loop's nodes at each iteration, a comparison's middle
  operand read back) records that node in `H` (`T2Sim.Seen`).
* Frame ids: PyCore's own cells are addressed by frame id, so the ids of live frames are
  distinct and below `next` (`Ids`).

`KRel` is split by construct: the homomorphic items (`CoreK`) and one family per file of cases
(`CallK`, `ClsK`, `CompK`, `LoopK`, `AsgK`, `AccK`, `MiscK`), so that the case lemmas of one file
analyse only their own family.
-/
import Surf.Semantics
import Surf.Canon
import Surf.T2Sim
import PyCore.Relation

namespace Surf.T2
open PyCore (Name Label)
open Py (Val Gadget)

/-! ## Names with a dot -/

def Dot (x : Name) : Prop := x.toList.head? = some '.'

instance (x : Name) : Decidable (Dot x) := inferInstanceAs (Decidable (_ = _))

theorem dot_fresh (t : String) (l : Label) : Dot (fresh t l) := fresh_dot ⟨t, l, rfl⟩

theorem not_fresh {x : Name} (h : ¬ Dot x) : ¬ IsFresh x := fun hf => h (fresh_dot hf)

theorem startsWith_dot (x : Name) : x.startsWith "." = true ↔ Dot x := by
  rw [String.startsWith_string_iff]
  simp only [Dot]
  constructor
  · rintro ⟨t, ht⟩
    rw [← ht]; rfl
  · intro h
    cases hx : x.toList with
    | nil => simp [hx] at h
    | cons c cs =>
      simp [hx] at h; subst h
      exact ⟨cs, by simp⟩

/-- A fresh name's tag ends in no digit (the translation's tags are letters), so that `fresh tag l`
determines `l` (`fresh_lab`). -/
def tagOk (tag : String) : Bool := !(tag.toList.getLast?.any Char.isDigit)

theorem takeWhile_app {p : Char → Bool} : ∀ {A B : List Char}, (∀ c ∈ A, p c = true) →
    (∀ c, B.head? = some c → p c = false) → List.takeWhile p (A ++ B) = A
  | [], [], _, _ => rfl
  | [], b :: B, _, hb => by simp [hb b rfl]
  | a :: A, B, ha, hb => by
    have ih := takeWhile_app (A := A) (B := B) (fun c hc => ha c (List.mem_cons_of_mem _ hc)) hb
    simp [ha a List.mem_cons_self, ih]

theorem fresh_lab {tag tag' : String} {l l' : Label} (h1 : tagOk tag = true) (h2 : tagOk tag' = true)
    (h : fresh tag l = fresh tag' l') : l = l' := by
  have key : ∀ (t : String) (n : Nat), tagOk t = true →
      List.takeWhile Char.isDigit (fresh t n).toList.reverse = (Nat.toDigits 10 n).reverse := by
    intro t n ht
    simp only [fresh, String.toList_append, Nat.toString_eq_ofList_toDigits]
    simp only [List.reverse_append, String.toList_ofList]
    apply takeWhile_app
    · intro c hc
      exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) (List.mem_reverse.1 hc)
    · intro c hc
      cases ht' : t.toList.reverse with
      | nil => simp [ht'] at hc; subst hc; decide
      | cons d ds =>
        rw [ht'] at hc; simp at hc; subst hc
        have : t.toList.getLast? = some d := by
          rw [List.getLast?_eq_head?_reverse, ht']; rfl
        simpa [tagOk, this] using ht
  have := key tag l h1
  rw [h, key tag' l' h2] at this
  have := congrArg List.reverse this
  simp only [List.reverse_reverse] at this
  rw [← Nat.ofDigitChars_ten_toDigits (n := l), ← this, Nat.ofDigitChars_ten_toDigits]

theorem fresh_ne {tag tag' : String} {l l' : Label} (h1 : tagOk tag = true) (h2 : tagOk tag' = true)
    (h : l ≠ l') : fresh tag l ≠ fresh tag' l' := fun e => h (fresh_lab h1 h2 e)

/-! ## Well-formed syntax

The shape conditions every Python AST meets. `okName`: an identifier, an operator's class name or a
module path holds no `:` or `,`, is neither empty nor `*`, and does not start with `=` (the
translation writes names into the constants `$op:…`, `$annot:…` and the markers `$kw:…`,
`$param:<kind><=?><name>`, which split at `:` and `,` and read a leading `=` as a default). A constant is a literal's text, which
never starts with `$` (the core's own constants do). A Boolean operation has two operands or more;
a comparison as many operators as operands after the first, and one at least; a comprehension a
generator at least, one element (two for a dictionary), clause targets that are targets (`tgtOk`), and
no `yield` in its own scope (CPython rejects `yield` in a comprehension but in its first iterable); a starred expression stands only where a display, a call or a target unpacks
it; an annotated assignment's target is a name, an attribute or a subscript; `raise from c` has
an exception; `from m import *` imports nothing else, and `import` imports no `*`; a handler with no
class has no name; an annotated name is an identifier; no `del` target is starred (CPython: "cannot
delete starred"). -/

def okName (s : String) : Bool := !(s.contains ':') && !(s.contains ',') && s != "*" && s != "" &&
  !(s.startsWith "=")

/-- A module path or an alias's name: no `:` or `,`. -/
def okPath (s : String) : Bool := !(s.contains ':') && !(s.contains ',')

mutual
/-- An assignment target as Python's grammar has it: a name, attribute, subscript, or a tuple or list of
targets (one of them possibly starred). -/
def tgtOk : Expr → Bool
  | .name .. | .attr .. | .sub .. => true
  | .tuple _ ts | .list _ ts => tgtsOk ts
  | _ => false
def tgtsOk : List Expr → Bool
  | [] => true
  | .star _ t :: ts => tgtOk t && tgtsOk ts
  | t :: ts => tgtOk t && tgtsOk ts
end

mutual
/-- A `del` target with no starred part. -/
def delOk : Expr → Bool
  | .tuple _ ts | .list _ ts => delOks ts
  | .star .. => false
  | _ => true
def delOks : List Expr → Bool
  | [] => true
  | t :: ts => delOk t && delOks ts
end

mutual
def okE : Expr → Bool
  | .const _ k => !k.startsWith "$"
  | .name .. => true
  | .bin _ op a b => okName op && okE a && okE b
  | .sub _ a b => okE a && okE b
  | .unary _ op a => okName op && okE a
  | .attr _ a x => okName x && okE a
  | .yieldFrom _ a => okE a
  | .boolop _ _ es => decide (2 ≤ es.length) && okEs es
  | .compare _ a ops es => okE a && okEs es && decide (ops.length = es.length) && !es.isEmpty &&
      ops.all okName
  | .ifexp _ c a b => okE c && okE a && okE b
  | .call _ f args kws => okE f && okAs args && okKs kws
  | .slice _ a b c => okO a && okO b && okO c
  | .star .. => false
  | .list _ es | .tuple _ es | .set _ es => okAs es
  | .dict _ kvs => okDs kvs
  | .lam _ ps b => okPs ps && okE b
  | .comp _ k es gs => okEs es && okGs gs && !gs.isEmpty &&
      decide (es.length = if k = .dict then 2 else 1) &&
      !((factsGs none true gs ++ factsEs none false es).contains .yld)
  | .walrus _ _ e => okE e
  | .yield _ e => okO e
  | .fstr _ es => okEs es
  | .fmt _ e _ s => okE e && okO s
def okO : Option Expr → Bool
  | none => true
  | some e => okE e
def okEs : List Expr → Bool
  | [] => true
  | e :: es => okE e && okEs es
/-- Elements of a display, arguments of a call, targets of an unpacking: `*e` allowed. -/
def okAs : List Expr → Bool
  | [] => true
  | .star _ e :: es => okE e && okAs es
  | e :: es => okE e && okAs es
def okKs : List Kw → Bool
  | [] => true
  | .mk _ x e :: ks => (x.all okName) && okE e && okKs ks
def okDs : List DItem → Bool
  | [] => true
  | .mk k v :: kvs => okO k && okE v && okDs kvs
def okPs : List Param → Bool
  | [] => true
  | .mk _ x _ d a :: ps => okName x && okO d && okO a && okPs ps
def okGs : List Gen → Bool
  | [] => true
  | .mk _ t i ifs :: gs => okE t && tgtOk t && okE i && okEs ifs && okGs gs
end

def okAl (a : Alias) : Bool := okPath a.name && a.asname.all okName

mutual
def okS : Stmt → Bool
  | .expr _ e => okE e
  | .assign _ ts e => okAs ts && ts.all tgtOk && okE e
  | .augassign _ t op e => okName op && okE t && okE e
  | .annassign _ t a v =>
    (match t with | .name _ y => okName y | .attr .. | .sub .. => true | _ => false) && okE t && okE a && okO v
  | .del _ ts => okAs ts && delOks ts
  | .ite _ c t u | .while _ c t u => okE c && okB t && okB u
  | .for _ t it b u => okE t && tgtOk t && okE it && okB b && okB u
  | .brk _ | .cont _ | .pass _ => true
  | .glob _ xs | .nonloc _ xs => xs.all okName
  | .imp _ al => al.all okAl && al.all (·.name != "*")
  | .impFrom _ m al _ => m.all okPath && al.all okAl &&
      (al.all (·.name != "*") || al.length == 1)
  | .ret _ e => okO e
  | .defn _ f ps b ds r => okName f && okPs ps && okB b && okEs ds && okO r
  | .cls _ x bs ks b ds => okName x && okAs bs && okKs ks && okB b && okEs ds
  | .tryE _ b hs u => okB b && okHs hs && okB u
  | .raise _ e c => (e.isSome || c.isNone) && okO e && okO c
  | .assert _ t m => okE t && okO m
def okHs : List Handler → Bool
  | [] => true
  | .mk _ ty x b :: hs => okO ty && x.all okName && (ty.isSome || x.isNone) && okB b && okHs hs
def okB : List Stmt → Bool
  | [] => true
  | s :: ss => okS s && okB ss
end

/-! ## Nodes touched when an expression is entered

`touchB p`: the pairs `(l, e)` such that the Surf node `l` counts as touched when the expression
`e` is evaluated: a keyword argument's node when its value is evaluated, a comprehension clause's
node when its iterable is evaluated (the implementation's line trace maps both to the line of
their value). -/

mutual
def touchE : Expr → List (Label × Expr)
  | .const .. | .name .. => []
  | .bin _ _ a b | .sub _ a b => touchE a ++ touchE b
  | .unary _ _ a | .attr _ a _ | .walrus _ _ a | .yieldFrom _ a => touchE a
  -- a starred item's node, when its operand is evaluated (its marker is the star node's)
  | .star l a => (l, a) :: touchE a
  | .boolop _ _ es | .list _ es | .tuple _ es | .set _ es | .fstr _ es => touchEs es
  | .compare _ a _ es => touchE a ++ touchEs es
  | .ifexp _ c a b => touchE c ++ touchE a ++ touchE b
  | .call _ f as ks => touchE f ++ touchEs as ++ touchKs ks
  | .slice _ a b c => touchO a ++ touchO b ++ touchO c
  | .dict _ kvs => touchDs kvs
  | .lam _ ps b => touchPs ps ++ touchE b
  | .comp _ _ es gs => touchEs es ++ touchGs gs
  | .yield _ e => touchO e
  | .fmt _ e _ s => touchE e ++ touchO s
def touchO : Option Expr → List (Label × Expr)
  | none => []
  | some e => touchE e
def touchEs : List Expr → List (Label × Expr)
  | [] => []
  | e :: es => touchE e ++ touchEs es
def touchKs : List Kw → List (Label × Expr)
  | [] => []
  | .mk l _ e :: ks => (l, e) :: touchE e ++ touchKs ks
def touchDs : List DItem → List (Label × Expr)
  | [] => []
  | .mk k v :: kvs => touchO k ++ touchE v ++ touchDs kvs
def touchPs : List Param → List (Label × Expr)
  | [] => []
  | .mk _ _ _ d a :: ps => touchO d ++ touchO a ++ touchPs ps
def touchGs : List Gen → List (Label × Expr)
  | [] => []
  | .mk l t i ifs :: gs => (l, i) :: touchE t ++ touchE i ++ touchEs ifs ++ touchGs gs
end

mutual
def touchS : Stmt → List (Label × Expr)
  | .expr _ e | .ret _ (some e) => touchE e
  | .assign _ ts e => touchEs ts ++ touchE e
  | .augassign _ t _ e => touchE t ++ touchE e
  | .annassign _ t a v => touchE t ++ touchE a ++ touchO v
  | .del _ ts => touchEs ts
  | .ite _ c t u | .while _ c t u => touchE c ++ touchB t ++ touchB u
  | .for _ t it b u => touchE t ++ touchE it ++ touchB b ++ touchB u
  | .defn _ _ ps b ds r => touchPs ps ++ touchB b ++ touchEs ds ++ touchO r
  | .cls _ _ bs ks b ds => touchEs bs ++ touchKs ks ++ touchB b ++ touchEs ds
  | .tryE _ b hs u => touchB b ++ touchHs hs ++ touchB u
  | .raise _ e c => touchO e ++ touchO c
  | .assert _ t m => touchE t ++ touchO m
  | _ => []
def touchHs : List Handler → List (Label × Expr)
  | [] => []
  | .mk _ ty _ b :: hs => touchO ty ++ touchB b ++ touchHs hs
def touchB : List Stmt → List (Label × Expr)
  | [] => []
  | s :: ss => touchS s ++ touchB ss
end

/-- A comprehension clause's node. -/
def _root_.Surf.Gen.label : Gen → Label | .mk l .. => l

/-! ## Code pieces of `p` -/

def SubL {α} (A B : List α) : Prop := ∀ x ∈ A, x ∈ B

/-- The PyCore items of ⌊p⌋. -/
abbrev PI (p : List Stmt) : List PyCore.Item := PyCore.itemsB R0 [] (tr p)

/-- All labels. -/
def UAll : Label → Prop := fun _ => True

/-- The label budget `U` without `l`. -/
def Rm (U : Label → Prop) (l : Label) : Label → Prop := fun l' => U l' ∧ l' ≠ l

structure GoodE (p : List Stmt) (C : List Scope) (U : Label → Prop) (e : Expr) : Prop where
  s : SubL (itemsE C e) (itemsB [] p)
  t : SubL (PyCore.itemsE R0 (trChain C) (trE C e)) (PI p)
  ok : okE e = true
  u : ∀ l ∈ labelsE e, U l
  /-- the class name that mangles the chain's private names is an identifier (no `:`) -/
  pv : ∀ c, priv C = some c → okName c = true
  /-- distinct labels (`WF.nodup`) -/
  nd : (labelsE e).Nodup
  /-- the nodes touched when its parts are entered (a keyword's, a starred item's, a clause's) are `p`'s -/
  tch : SubL (touchE e) (touchB p)

structure GoodB (p : List Stmt) (C : List Scope) (U : Label → Prop) (ss : List Stmt) : Prop where
  s : SubL (itemsB C ss) (itemsB [] p)
  t : SubL (PyCore.itemsB R0 (trChain C) (trB C ss)) (PI p)
  ok : okB ss = true
  u : ∀ l ∈ labelsB ss, U l
  /-- (for a block with code) the mangling class name is an identifier -/
  pv : ss ≠ [] → ∀ c, priv C = some c → okName c = true
  nd : (labelsB ss).Nodup
  tch : SubL (touchB ss) (touchB p)

structure GoodHs (p : List Stmt) (C : List Scope) (U : Label → Prop) (hs : List Handler) : Prop where
  s : SubL (itemsHs C hs) (itemsB [] p)
  t : SubL (PyCore.itemsHs R0 (trChain C) (trHs C hs)) (PI p)
  ok : okHs hs = true
  u : ∀ l ∈ labelsHs hs, U l
  /-- (for handlers) the mangling class name is an identifier -/
  pv : hs ≠ [] → ∀ c, priv C = some c → okName c = true
  nd : (labelsHs hs).Nodup
  tch : SubL (touchHs hs) (touchB p)

def GoodEs (p : List Stmt) (C : List Scope) (U : Label → Prop) (es : List Expr) : Prop :=
  ∀ e ∈ es, GoodE p C U e

def GoodO (p : List Stmt) (C : List Scope) (U : Label → Prop) : Option Expr → Prop
  | none => True
  | some e => GoodE p C U e

/-- A comprehension clause in the comprehension's own scope: its target and conditions. -/
def GoodGT (p : List Stmt) (C : List Scope) (U : Label → Prop) : Gen → Prop
  | .mk l t _ ifs => U l ∧ GoodE p C U t ∧ GoodEs p C U ifs ∧
      SubL (PyCore.itemsB R0 (trChain C) (trT C (forSrc l) t (trE C t))) (PI p)

/-- A clause's target and conditions (its node aside), and the items of the target's store. -/
def GoodGP (p : List Stmt) (C : List Scope) (U : Label → Prop) : Gen → Prop
  | .mk l t _ ifs => GoodE p C U t ∧ GoodEs p C U ifs ∧
      SubL (PyCore.itemsB R0 (trChain C) (trT C (forSrc l) t (trE C t))) (PI p)

/-- Clauses after the first, all their parts in the comprehension's own scope. -/
def GoodGs (p : List Stmt) (C : List Scope) (U : Label → Prop) (gs : List Gen) : Prop :=
  ∀ g ∈ gs, GoodGT p C U g ∧ match g with | .mk _ _ i _ => GoodE p C U i

/-- A fresh name the translated code binds in the scope at the head of the chain: global at the
module, local in every other scope, so that a store and a read of it go to one dotted place. -/
def FOk (C : List Scope) (x : Name) : Prop :=
  PyCore.clsOf (trChain C) x = match C with | [] => .glob | _ => .loc

/-- The fresh names `.tag l` of the tags `tags`, all bound in the scope at the head of `C`. -/
def FOks (C : List Scope) (l : Label) (tags : List String) : Prop := ∀ tag ∈ tags, FOk C (fresh tag l)

/-- The fresh names of comprehension clauses after the first: iterator, flag, item, `StopIteration`. -/
def GsFOk (C : List Scope) (gs : List Gen) : Prop := ∀ g ∈ gs, FOks C g.label ["j", "g", "v", "s"]

/-- A handler's name: Surf's (raw, as in `Kont.catchS`) and PyCore's (mangled, or the fresh
`.e lh` of a handler node `lh` in the budget `U` when the handler names none). -/
def XOk (C : List Scope) (U : Label → Prop) (x : Option Name) (x' : Name) : Prop :=
  (∃ y, x = some y ∧ x' = mangle (priv C) y ∧ ¬ Dot x') ∨
    (x = none ∧ (∃ lh, x' = fresh "e" lh ∧ U lh) ∧ FOk C x')

/-- A running handler's name: Surf's (mangled) and PyCore's. -/
def HOk (C : List Scope) (U : Label → Prop) (x : Option Name) (x' : Name) : Prop :=
  (x = some x' ∧ ¬ Dot x') ∨ (x = none ∧ (∃ lh, x' = fresh "e" lh ∧ U lh) ∧ FOk C x')

/-- The head of the chain is no comprehension (`break`, `continue` and statements run only there). -/
def NoCompH : List Scope → Prop
  | S :: _ => S.isComp = false
  | [] => True

/-! ## The parts an `evs` item evaluates (as `Sem.evalStep`/`Sem.execStep` list them) -/

/-- A call's function, positional arguments (stars unwrapped) and keyword values. -/
def partsCall (g : Expr) (args : List Expr) (kws : List Kw) : List (Option Expr) :=
  some g :: (args.map fun a => some (unstar a)) ++ kws.map fun | .mk _ _ v => some v
/-- A `def`'s decorators, defaults and annotations (CPython's order). -/
def partsDef (ds : List Expr) (ps : List Param) (r : Option Expr) : List (Option Expr) :=
  ds.map some ++ (ps.filterMap Param.dflt).map some ++ annOrder ps r
/-- A lambda's defaults. -/
def partsLam (ps : List Param) : List (Option Expr) := ps.filterMap Param.dflt |>.map some
/-- A list, tuple or set display's items (stars unwrapped). -/
def partsDisp (es : List Expr) : List (Option Expr) := es.map fun a => some (unstar a)
/-- A class statement's decorators, bases (stars unwrapped) and keyword values. -/
def partsCls (ds bs : List Expr) (kws : List Kw) : List (Option Expr) :=
  ds.map some ++ bs.map (fun a => some (unstar a)) ++ kws.map fun | .mk _ _ v => some v

/-! ## PyCore code the relation names -/

section
variable {σ : Type}

/-- PyCore's continuation while an argument record is evaluated: the values `done` so far, the
expressions after the current one, then `K'` (the call of the record's operation, …). -/
def recK (done : List Val) (rest : List PE) (K' : List (PyCore.Kont σ)) : List (PyCore.Kont σ) :=
  .binR "," (.data "$args" done) :: rest.map (.binL ",") ++ K'

/-- The handler of a `for` loop's `StopIteration`. -/
def stopH (l : Label) : PyCore.Handler :=
  .mk (sub l 19) (.const (sub l 20) "$stop") (fresh "s" l)
    [.assign (sub l 21) (fresh "g" l) (.const (sub l 22) "$false")]

/-- The `try` of one iteration of the loop `l` over the iterator in `iv`, its `else` block `b`
(the target's store and the body). -/
def tryS (l : Label) (iv : Name) (b : PS) : PyCore.Stmt :=
  .tryE (sub l 14)
    [.assign (sub l 15) (fresh "v" l) (.call (sub l 16) (.const (sub l 17) "$next") (.name (sub l 18) iv none))]
    [stopH l] b

/-- The `while` of the loop `l` (`forLoop`), as the continuation item of its body. -/
def loopK (l : Label) (iv : Name) (b u : PS) : PyCore.Kont σ :=
  .loop (.name (sub l 13) (fresh "g" l) none) [tryS l iv b] u

/-- The loop `l` awaits its iterator's next item. -/
def nextK (l : Label) (iv : Name) (b u : PS) (K' : List (PyCore.Kont σ)) : List (PyCore.Kont σ) :=
  .assign (fresh "v" l) :: .seq [] :: .tryE [stopH l] b :: .seq [] :: loopK l iv b u :: K'

/-- The `$get` of a comparison's (node `l`) middle operand (node `lb`). -/
def getE (l lb : Label) : PE := gad l 4 (.get (fresh "c" lb)) []

/-- The rest of a comparison chain (node `l`) after the operand `lb`. -/
def cmpRest (C : List Scope) (l lb : Label) (ops : List String) (es : List Expr) : PE :=
  cmpChain l (sub l 1) (getE l lb) (cmpOps ops (trLs C es))

/-- The `format` of an f-string's value, its spec next if any. -/
def fmtRest (C : List Scope) (spec : Option Expr) (K' : List (PyCore.Kont σ)) : List (PyCore.Kont σ) :=
  match spec with
  | some s => recK [] [trE C s] (.callA (.op .format) :: K')
  | none => recK [] [] (.callA (.op .format) :: K')

/-- An `assert`'s failure branch. -/
def assertRaise (C : List Scope) (l : Label) (m : Option Expr) : PyCore.Stmt :=
  .expr (sub l 1) (gad l 2 (.raiseK "AssertionError") (match m with | some m => [trE C m] | none => []))

/-- The binding of one alias of `import`. -/
def impS (C : List Scope) (a : Alias) : PyCore.Stmt :=
  if a.name == "*" then stuckAt (sub a.l 0)
  else .assign (sub a.l 0) (mangle (priv C) a.bound)
    (cc a.l 1 s!"$op:import:{a.name}:{if a.asname.isSome then 1 else 0}" [])

/-- The binding of one alias of `from m import …` (the module in `.m l`). -/
def fromS (C : List Scope) (l : Label) (a : Alias) : PyCore.Stmt :=
  if a.name == "*" then
    .expr (sub a.l 0) (gad a.l 1 .starstore [cc a.l 2 "$op:importStar" [nm a.l 3 (fresh "m" l)]])
  else .assign (sub a.l 0) (mangle (priv C) a.bound)
    (cc a.l 1 ("$op:importFrom:" ++ a.name) [nm a.l 3 (fresh "m" l)])

/-- The statements of an augmented assignment (node `l`, target node `lt`) after the target's
parts: the update, then the write (`wrN`/`wrA`/`wrI`). -/
def augUpd (C : List Scope) (l : Label) (op : String) (e : Expr) : PyCore.Stmt :=
  .assign (sub l 1) (fresh "v" l) (.bin (sub l 2) (op ++ "=") (nm l 3 (fresh "g" l)) (trE C e))
def wrN (l lt : Label) (y : Name) : PyCore.Stmt := .assign (sub lt 2) y (nm lt 3 (fresh "v" l))
def getA (l lt : Label) (a : Name) : PyCore.Stmt :=
  .assign (sub lt 5) (fresh "g" l) (cc lt 6 ("$op:getattr:" ++ a) [nm lt 7 (fresh "o" l)])
def wrA (l lt : Label) (a : Name) : PyCore.Stmt :=
  .expr (sub lt 2) (cc lt 9 ("$op:setattr:" ++ a) [nm lt 10 (fresh "o" l), nm lt 11 (fresh "v" l)])
def keyS (C : List Scope) (l lt : Label) (i : Expr) : PyCore.Stmt := .assign (sub lt 5) (fresh "k" l) (trE C i)
def getI (l lt : Label) : PyCore.Stmt :=
  .assign (sub lt 6) (fresh "g" l) (cc lt 7 "$op:getitem" [nm lt 8 (fresh "o" l), nm lt 9 (fresh "k" l)])
def wrI (l lt : Label) : PyCore.Stmt :=
  .expr (sub lt 2) (cc lt 10 "$op:setitem" [nm lt 11 (fresh "o" l), nm lt 12 (fresh "k" l), nm lt 13 (fresh "v" l)])

/-- The `return` of a list, set or dictionary comprehension's accumulator. -/
def retAcc (l : Label) : PyCore.Stmt := .ret (sub l 7) (nm l 6 (fresh "acc" l))

/-- A comprehension clause's (node `lg`) body: its conditions around the clauses after it. -/
def genBody (C : List Scope) (l : Label) (k : CompKind) (es : List Expr) (lg : Label) (ifs : List Expr)
    (rest : List Gen) : PS :=
  ifsNest lg (trEs C ifs) (trGs C (fresh "i" l) false rest (compElt l k (trEs C es)))

/-- A clause's loop body: the target's store, then `genBody`. -/
def genLoop (C : List Scope) (l : Label) (k : CompKind) (es : List Expr) (g : Gen) (rest : List Gen) : PS :=
  match g with
  | .mk lg t _ ifs => trT C (forSrc lg) t (trE C t) ++ genBody C l k es lg ifs rest

def seqs (n : Nat) : List (PyCore.Kont σ) := List.replicate n (.seq [])

/-- A blk's end as PyCore may have it below a block's next statements. -/
def BlkTail (pre : List (PyCore.Kont σ)) : Prop :=
  pre = [] ∨ pre = [.tryE [] []] ∨ pre = [.seq [], .tryE [] []]

end

/-! ## Values read from fresh names -/

/-- The Surf address `o` holds an object, and no comprehension's function object (a function object
there is a `def`'s or a lambda's; a generator there leaves both runs stuck at `enterK`). -/
def NoCompObj {σ} (objs : Std.HashMap Nat (Sem.Obj σ)) (o : Nat) : Prop :=
  (objs[o]?).isSome ∧ ∀ S C cl κ kd dflt, objs[o]? = some (Sem.Obj.clo S C cl κ kd dflt) → S.isComp = false

/-- Every `enterK` item of a continuation (a `**` parameter's dictionary awaited) names an address with
no comprehension's function object. -/
def EnterOk {σ} (objs : Std.HashMap Nat (Sem.Obj σ)) (K : List (Sem.Kont σ)) : Prop :=
  ∀ o b kx, Sem.Kont.enterK o b kx ∈ K → NoCompObj objs o

/-- Every pending `enterK` of the frames `st` and of the suspended generators in `O` names an address of
`O` with no comprehension's function object. -/
def EnterInv {σ} (O : Std.HashMap Nat (Sem.Obj σ)) (st : List (Sem.Frame σ)) : Prop :=
  (∀ g ∈ st, EnterOk O g.kont) ∧ ∀ (o : Nat) (g : Sem.Frame σ), O[o]? = some (Sem.Obj.gen (.susp g)) → EnterOk O g.kont

/-- The `enterK` items of `k` are among those of `K`. -/
def EnterSub {σ} (k K : List (Sem.Kont σ)) : Prop :=
  ∀ o b kx, Sem.Kont.enterK o b kx ∈ k → Sem.Kont.enterK o b kx ∈ K

/-- The PyCore frame's reading of a name (by its classification), and its own cell. -/
abbrev pObj {σ} (t : PyCore.Config σ) (o : Nat) : Option (PyCore.Obj σ) := t.objs[o]?
abbrev pCell {σ} (t : PyCore.Config σ) (a : PyCore.Addr) : Option Val := t.cells[a]?
abbrev pGlob {σ} (t : PyCore.Config σ) (x : Name) : Option Val := t.glob x
abbrev sObj {σ} (s : Sem.Config σ) (o : Nat) : Option (Sem.Obj σ) := s.objs[o]?
abbrev sCell {σ} (s : Sem.Config σ) (a : Sem.Addr) : Option Val := s.cells[a]?
abbrev sGlob {σ} (s : Sem.Config σ) (x : Name) : Option Val := s.glob[x]?

/-- A frame's reading of a name by its classification, the module dictionary and cells given. The
translation binds a fresh name in the scope that uses it, so a frame reads its fresh names in its
own cells or namespace, and only the module frame in the module dictionary; a fresh name classified
global in any other frame, or free, reads nothing (so that the module frame's writes of its fresh
names leave other frames' readings alone). -/
def rdAt {σ} (gl : Name → Option Val) (cs : Std.HashMap PyCore.Addr Val) (f' : PyCore.Frame σ) (x : Name) :
    Option Val :=
  match f'.cls x with
  | .glob => match f'.kind with
    | .mod => gl x
    | _ => none
  | .loc => match f'.kind with
    | .cls => f'.ns.lookup x
    | _ => cs[(f'.id, x)]?
  | .free => none

/-- A frame's own cell of a name. -/
def ownAt {σ} (cs : Std.HashMap PyCore.Addr Val) (f' : PyCore.Frame σ) (x : Name) : Option Val := cs[(f'.id, x)]?

abbrev rdOf {σ} (t : PyCore.Config σ) (f' : PyCore.Frame σ) : Name → Option Val := rdAt t.glob t.cells f'
abbrev ownOf {σ} (t : PyCore.Config σ) (f' : PyCore.Frame σ) : Name → Option Val := ownAt t.cells f'

/-- What the continuation relation of a frame reads: the program, the frame's chain, its reading
of fresh names and its own cells, and the Surf nodes touched before. -/
structure Cx where
  p : List Stmt
  C : List Scope
  rd : Name → Option Val
  own : Name → Option Val
  H : Label → Prop

/-- A PyCore expression made for the target `lt` that evaluates, with no other effect, to the value
`v` kept in a fresh name of a node outside `U` (the source of a target's store). -/
inductive SrcR (x : Cx) (U : Label → Prop) (lt : Label) : PE → Val → Prop
  | name {k tag l v} : k < 64 → tagOk tag = true → ¬ U l → x.rd (fresh tag l) = some v →
      SrcR x U lt (.name (sub lt k) (fresh tag l) none) v
  /-- an unpacked item: the item `i` of the tuple kept in `.u l` -/
  | item {l i ws w} : ¬ U l → x.rd (fresh "u" l) = some (.tuple ws) → ws[i]? = some w →
      SrcR x U lt (itemSrc l i lt) w

/-- A `yield from`'s delegate: Surf's subiterator and PyCore's `Deleg`. -/
def DelegR (sub : Val) (d : PyCore.Deleg) : Prop :=
  (∃ o, sub = .gen o ∧ d = .gen o) ∨ ((∀ o, sub ≠ .gen o) ∧ d = .it sub)

/-- The targets `ts` still to delete (Surf flattens a tuple target, PyCore nests its block). -/
inductive DelSeg {σ} (C : List Scope) : List Expr → List (PyCore.Kont σ) → List (PyCore.Kont σ) → Prop
  | base {ts K'} : DelSeg C ts (.seq (trDs C ts) :: K') K'
  | nest {es ts K1 K'} : DelSeg C ts K1 K' → DelSeg C (es ++ ts) (.seq (trDs C es) :: .tryE [] [] :: K1) K'

/-- An augmented target's parts as PyCore keeps them, and its write. -/
def AugT (x : Cx) (l lt : Label) : Sem.ATgt → PyCore.Stmt → Prop
  | .name y, w => ¬ Dot y ∧ w = wrN l lt y
  | .attr ob a, w => x.rd (fresh "o" l) = some ob ∧ ':' ∉ a.toList ∧ w = wrA l lt a
  | .item ob i, w => x.rd (fresh "o" l) = some ob ∧ x.rd (fresh "k" l) = some i ∧ w = wrI l lt

/-- A part of a slice or an f-string (node `l`): an expression and its translation, or `None`
(the core's, at a node made for `l`). -/
def PartR (x : Cx) (U : Label → Prop) (l : Label) : Option Expr → PE → Prop
  | some e, pe => GoodE x.p x.C U e ∧ pe = trE x.C e
  | none, pe => ∃ k, k < 64 ∧ pe = .const (sub l k) "$none"

def PartsR (x : Cx) (U : Label → Prop) (l : Label) : List (Option Expr) → List PE → Prop
  | [], [] => True
  | a :: rest, pe :: ps => PartR x U l a pe ∧ PartsR x U l rest ps
  | _, _ => False

mutual
/-- The nodes a set item's constness marker reads (the item, and through a sign or a tuple, its parts). -/
def constNodes : Expr → List Label
  | .unary l _ a => l :: constNodes a
  | .tuple l es => l :: constNodesL es
  | e => [Sem.Expr.lbl e]
def constNodesL : List Expr → List Label
  | [] => []
  | e :: es => constNodes e ++ constNodesL es
end

/-- The nodes a set item's marker reads: a starred item's star node, else its constness nodes. -/
def setOwners : Expr → List Label
  | .star l _ => [l]
  | e => constNodes e

/-- The nodes of an unpacking's targets (the owners of its markers, read when the store starts). -/
def tgtKids : Expr → List Label
  | .tuple _ ts | .list _ ts => ts.map Sem.Expr.lbl
  | _ => []

def _root_.Surf.Kw.lbl : Kw → Label | .mk l _ _ => l

section
variable {σ : Type}

/-- A `def`'s function (node `l`), the last item of its `$def` record. -/
def defFn (C : List Scope) (l : Label) (g : Name) (ps : List Param) (b : List Stmt) : PE :=
  .lam (sub l 1) false (fresh "a" l) (paramBind (.fn l g ps b :: C) ps ++ trB (.fn l g ps b :: C) b)

/-- A lambda's function (node `l`). -/
def lamFn (C : List Scope) (l : Label) (ps : List Param) (b : Expr) : PE :=
  .lam (sub l 1) false (fresh "a" l) (paramBind (.lam l ps b :: C) ps ++ [.ret (sub l 2) (trE (.lam l ps b :: C) b)])

/-- A lambda's annotations, in a branch that never runs. -/
def lamDead (C : List Scope) (l : Label) (ps : List Param) : PE :=
  .cond (sub l 3) (.const (sub l 3) "$false") (recR (sub l 3) (trAnns C ps)) (.const (sub l 3) "$none")

/-- An annotated assignment's (node `l`, target `t`, annotation `A`) annotation: at module or class
level its value into `.n l` and the target's key store, in a function a branch that never runs. -/
def annS (C : List Scope) (l : Label) (t A : Expr) : PS :=
  if isTop C then .assign (sub l 6) (fresh "n" l) (trE C A) :: annT C l t else [dead (sub l 6) [.expr (sub l 8) (trE C A)]]

/-- A class statement's (node `l`) class, after its arguments' `$cls`. -/
def clsS (C : List Scope) (l : Label) (x : Name) (b : List Stmt) : PyCore.Stmt :=
  .cls (sub l 1) (mangle (priv C) x) (qualIn C x) (setupS l :: trB (.cl l x b :: C) b)

end

/-! ## Continuations

Surf's continuation items and the PyCore items the translated code has pushed for them. The
`Bool` index says whether the top item awaits a value (`true`) or not (`false`: the end of a
statement, or a class body's namespace); the label set is the budget of the code that may run above. -/

section
variable {σ : Type}

/-- What an annotated assignment's annotation code needs: its node's fresh `.n l` written there (at
module or class level, where it is bound), the annotation, the target's shape and labels, and for a
name target a mangled name the gadget `$annot:ŷ` keeps whole. -/
def AnnOk (x : Cx) (U : Label → Prop) (l : Label) (t A : Expr) : Prop :=
  U l ∧ (isTop x.C = true → FOk x.C (fresh "n" l)) ∧ GoodE x.p x.C U A ∧ okE t = true ∧
    (∀ l' ∈ labelsE t, U l') ∧ (∀ lt y, t = .name lt y → ':' ∉ (mangle (priv x.C) y).toList)

/-- What the item of a later clause (`cIter`) needs of the clauses after the current one, at the
budget of the items below. -/
def NextOk (p : List Stmt) (C : List Scope) (U : Label → Prop) (es : List Expr) : List Gen → Prop
  | [] => True
  | g :: rest => U g.label ∧ GoodGP p C (Rm U g.label) g ∧ GoodGs p C (Rm U g.label) rest ∧
      GoodEs p C (Rm U g.label) es ∧ NextOk p C (Rm U g.label) es rest

mutual
inductive KRel (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  | nil {U} : KRel x U false [] []
  | core {U i K K'} : CoreK x U i K K' → KRel x U i K K'
  | call {U i K K'} : CallK x U i K K' → KRel x U i K K'
  | cls {U i K K'} : ClsK x U i K K' → KRel x U i K K'
  | comp {U i K K'} : CompK x U i K K' → KRel x U i K K'
  | loop {U i K K'} : LoopK x U i K K' → KRel x U i K K'
  | asg {U i K K'} : AsgK x U i K K' → KRel x U i K K'
  | acc {U i K K'} : AccK x U i K K' → KRel x U i K K'
  | misc {U i K K'} : MiscK x U i K K' → KRel x U i K K'

/-- The items of the constructs the translation maps to PyCore's own (`T2Cases.lean`). -/
inductive CoreK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  | exprS {U K K'} : KRel x U false K K' → CoreK x U true (.exprS :: K) (.exprS :: K')
  | binL {U K K' op b} : op ≠ "," → GoodE x.p x.C U b → KRel x U true K K' →
      CoreK x U true (.binL op b :: K) (.binL op (trE x.C b) :: K')
  | binR {U K K' op v} : op ≠ "," → KRel x U true K K' → CoreK x U true (.binR op v :: K) (.binR op v :: K')
  /-- the rest of a block; PyCore may first end a `blk` (`pre`) -/
  | seq {U K K' ss pre} : (ss ≠ [] → NoCompH x.C) → BlkTail pre → GoodB x.p x.C U ss → KRel x U false K K' →
      CoreK x U false (.seq ss :: K) (pre ++ .seq (trB x.C ss) :: K')
  /-- the bottom of a lambda's frame: PyCore's `ret` statement was the last of a block -/
  | seqNil {U} : CoreK x U false [] [.seq []]
  | ifS {U K K' t u} : NoCompH x.C → GoodB x.p x.C U t → GoodB x.p x.C U u → KRel x U false K K' →
      CoreK x U true (.ifS t u :: K) (.ifS (trB x.C t) (trB x.C u) :: K')
  | ifST {U K K' t u} : NoCompH x.C → GoodB x.p x.C U t → GoodB x.p x.C U u → KRel x U false K K' →
      CoreK x U true (.ifST t u :: K) (.ifT (trB x.C t) (trB x.C u) :: K')
  | whileS {U K K' c b u} : NoCompH x.C → GoodE x.p x.C U c → GoodB x.p x.C U b → GoodB x.p x.C U u → KRel x U false K K' →
      CoreK x U true (.whileS c b u :: K) (.whileS (trE x.C c) (trB x.C b) (trB x.C u) :: K')
  | whileT {U K K' c b u} : NoCompH x.C → GoodE x.p x.C U c → GoodB x.p x.C U b → GoodB x.p x.C U u → KRel x U false K K' →
      CoreK x U true (.whileT c b u :: K) (.whileT (trE x.C c) (trB x.C b) (trB x.C u) :: K')
  | loop {U K K' c b u} : NoCompH x.C → GoodE x.p x.C U c → GoodB x.p x.C U b → GoodB x.p x.C U u → KRel x U false K K' →
      CoreK x U false (.loop c b u :: K) (.loop (trE x.C c) (trB x.C b) (trB x.C u) :: K')
  | retS {U K K'} : KRel x U false K K' → CoreK x U true (.retS :: K) (.retS :: K')
  | tryE {U K K' hs u} : NoCompH x.C → GoodHs x.p x.C U hs → GoodB x.p x.C U u → KRel x U false K K' →
      CoreK x U false (.tryE hs u :: K) (.tryE (trHs x.C hs) (trB x.C u) :: K')
  | catchS {U K K' ex y y' hb hs u} : NoCompH x.C → GoodB x.p x.C U hb → GoodHs x.p x.C U hs → GoodB x.p x.C U u →
      XOk x.C U y y' → KRel x U false K K' →
      CoreK x U true (.catchS ex y hb hs u :: K) (.catchS ex y' (trB x.C hb) (trHs x.C hs) (trB x.C u) :: K')
  | catchT {U K K' ex y y' hb hs u} : NoCompH x.C → GoodB x.p x.C U hb → GoodHs x.p x.C U hs → GoodB x.p x.C U u →
      XOk x.C U y y' → KRel x U false K K' →
      CoreK x U true (.catchT ex y hb hs u :: K) (.catchT ex y' (trB x.C hb) (trHs x.C hs) (trB x.C u) :: K')
  | handler {U K K' y y' ex} : NoCompH x.C → HOk x.C U y y' → KRel x U false K K' →
      CoreK x U false (.handler y ex :: K) (.handler y' ex :: K')
  | ifK {U K K' a b} : GoodE x.p x.C U a → GoodE x.p x.C U b → KRel x U true K K' →
      CoreK x U true (.ifK a b :: K) (.condK (trE x.C a) (trE x.C b) :: K')
  | ifT {U K K' a b} : GoodE x.p x.C U a → GoodE x.p x.C U b → KRel x U true K K' →
      CoreK x U true (.ifT a b :: K) (.condT (trE x.C a) (trE x.C b) :: K')
  /-- the operands after the first of a Boolean operation (node `l`, whose nodes PyCore's chain has) -/
  | boolK {U K K' l o e rest} : x.H l → GoodEs x.p x.C U (e :: rest) → KRel x U true K K' →
      CoreK x U true (.boolK o (e :: rest) :: K)
        (.boolK o (boolChainIn l o (trEs x.C (e :: rest))) :: K')
  | boolT {U K K' l o v e rest} : x.H l → GoodEs x.p x.C U (e :: rest) → KRel x U true K K' →
      CoreK x U true (.boolT o v (e :: rest) :: K)
        (.boolT o v (boolChainIn l o (trEs x.C (e :: rest))) :: K')
  /-- the last operand of a Boolean operation: PyCore evaluates it in place -/
  | boolNil {U K K' o} : KRel x U true K K' → CoreK x U true (.boolK o [] :: K) K'
  | walrusK {U K K' y} : ¬ Dot y → KRel x U true K K' → CoreK x U true (.walrusK y :: K) (.walrus y :: K')
  | yieldK {U K K'} : KRel x U true K K' → CoreK x U true (.yieldK :: K) (.yieldS :: K')
  | native {U K K' k} : KRel x U true K K' → CoreK x U true (.native k :: K) (.native k :: K')
  /-- the store of a `def`'s function object, a class, an imported module or name -/
  | assignN {U K K' y} : ¬ Dot y → KRel x U false K K' → CoreK x U true (.assignN y :: K) (.assign y :: K')
  | decos {U K K' ds} : KRel x U true K K' → CoreK x U true (.decos ds :: K) (.decos ds :: K')

/-- Calls, `def`, lambdas, parameters, decorators (`T2Call.lean`), with the argument records of a
call, `def` and lambda (`evs` with `Then.call`, `.defn`, `.lam`). -/
inductive CallK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  | argStar {U K K' g kws kwvals} : KRel x U true K K' →
      CallK x U true (.argStar (.call g) kws kwvals :: K) (.argStar (.call g) kws kwvals :: K')
  | argKw {U K K' g args} : KRel x U true K K' →
      CallK x U true (.argKw (.call g) args :: K) (.argKw (.call g) args :: K')
  /-- the `**` parameter's dictionary is made, then the function `o` is entered -/
  | enterK {U K K' o bound kx} : KRel x U true K K' →
      CallK x U true (.enterK o bound kx :: K) (.enterK o bound kx :: K')
  /-- the function and arguments of a call (node `l`) still to evaluate (`rest`, PyCore's `ps`), the
  values so far `acc`; PyCore's record ends with the arguments' markers, whose nodes (the arguments',
  a starred one's star node, the keywords') are touched up to the current item -/
  | evsCall {U K K' l f args kws rest acc ps} : GoodE x.p x.C U (.call l f args kws) →
      acc.length < (partsCall f args kws).length → rest = (partsCall f args kws).drop (acc.length + 1) →
      (∀ a ∈ args.take acc.length, x.H (Sem.Expr.lbl a)) → (∀ k ∈ kws.take (acc.length - args.length), x.H k.lbl) →
      PartsR x U l rest ps → KRel x U true K K' →
      CallK x U true (.evs rest acc (.call args.length (args.map isStar) (kws.map fun | .mk _ x _ => x)) :: K)
        (recK acc.reverse (ps ++ args.map starMark ++ kws.map kwMark) (.callA (.prim Gadget.call.name) :: K'))
  /-- the decorators, defaults and annotations of `def g` (node `l`) still to evaluate; PyCore's record
  ends with the parameters' markers and the function, then the store of `g` -/
  | evsDefn {U K K' l g ps b ds r rest acc pes} : x.H l → GoodB x.p x.C U [.defn l g ps b ds r] →
      ¬ Dot (mangle (priv x.C) g) → acc.length < (partsDef ds ps r).length →
      rest = (partsDef ds ps r).drop (acc.length + 1) → PartsR x U l rest pes → KRel x U false K K' →
      CallK x U true (.evs rest acc (.defn l g ps b ds.length (ps.filterMap Param.dflt).length) :: K)
        (recK acc.reverse (pes ++ ps.map (paramMark (.fn l g ps b :: x.C)) ++ [defFn x.C l g ps b])
          (.callA (.prim (Gadget.defn ds.length ps.length).name) :: .assign (mangle (priv x.C) g) :: K'))
  /-- the defaults of a lambda (node `l`) still to evaluate; PyCore's record ends with its annotations in a
  branch that never runs, the parameters' markers and the function -/
  | evsLam {U K K' l ps b rest acc pes} : x.H l → GoodE x.p x.C U (.lam l ps b) →
      acc.length < (partsLam ps).length → rest = (partsLam ps).drop (acc.length + 1) → PartsR x U l rest pes →
      KRel x U true K K' →
      CallK x U true (.evs rest acc (.lam l ps b) :: K)
        (recK acc.reverse (pes ++ lamDead x.C l ps :: ps.map (paramMark (.lam l ps b :: x.C)) ++ [lamFn x.C l ps b])
          (.callA (.prim (Gadget.defn 0 ps.length).name) :: K'))

/-- Class statements and bodies (`T2Class.lean`), with the argument records of a class statement. -/
inductive ClsK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  /-- the body runs; its namespace makes the class, stored next (index `false`: it awaits no value) -/
  | clsEnd {U K K' y q bs kws ds} : ¬ Dot y → KRel x U false K K' →
      ClsK x U false (.clsEnd y q bs kws ds :: K) (.clsEnd y q bs kws ds :: .assign y :: K')
  /-- `SETUP_ANNOTATIONS` of a module or class body: the new dictionary awaited -/
  | setAnn {U K K'} : KRel x U false K K' →
      ClsK x U true (.setAnn :: K) (recK [] [] (.callA (.prim Gadget.setup.name) :: .exprS :: K'))
  /-- the decorators, bases and keyword values of a class statement (node `l`) still to evaluate;
  PyCore's record ends with the bases' and keywords' markers (touched up to the current item), its
  `$cls` keeps the arguments for the class that follows -/
  | evsCls {U K K' l y bs kws b ds ss rest acc ps} : x.H l → GoodB x.p x.C U [.cls l y bs kws b ds] →
      ¬ Dot (mangle (priv x.C) y) →
      acc.length < (partsCls ds bs kws).length → rest = (partsCls ds bs kws).drop (acc.length + 1) →
      (∀ a ∈ bs.take (acc.length + 1 - ds.length), x.H (Sem.Expr.lbl a)) →
      (∀ k ∈ kws.take (acc.length + 1 - ds.length - bs.length), x.H k.lbl) →
      PartsR x U l rest ps → (ss ≠ [] → NoCompH x.C) → GoodB x.p x.C U ss → KRel x U false K K' →
      ClsK x U true (.evs rest acc (.cls l y b ds.length (bs.map isStar) (kws.map fun | .mk _ x _ => x)) :: .seq ss :: K)
        (recK acc.reverse (ps ++ bs.map starMark ++ kws.map kwMark)
          (.callA (.prim (Gadget.cls ds.length).name) :: .exprS :: .seq [clsS x.C l y b] :: .tryE [] [] ::
            .seq (trB x.C ss) :: K'))
  /-- a class statement's starred bases expanded (PyCore: by its `$cls`) -/
  | argStarC {U K K' l y bs kws0 b ds ss dv kws kwvals} : x.H l → GoodB x.p x.C U [.cls l y bs kws0 b ds] →
      ¬ Dot (mangle (priv x.C) y) → (ss ≠ [] → NoCompH x.C) → GoodB x.p x.C U ss → KRel x U false K K' →
      ClsK x U true (.argStar (.cls l y b dv) kws kwvals :: .seq ss :: K)
        (.argStar (.cls dv) kws kwvals :: .exprS :: .seq [clsS x.C l y b] :: .tryE [] [] :: .seq (trB x.C ss) :: K')
  /-- a class statement's `**` keywords expanded -/
  | argKwC {U K K' l y bs kws0 b ds ss dv args} : x.H l → GoodB x.p x.C U [.cls l y bs kws0 b ds] →
      ¬ Dot (mangle (priv x.C) y) → (ss ≠ [] → NoCompH x.C) → GoodB x.p x.C U ss → KRel x U false K K' →
      ClsK x U true (.argKw (.cls l y b dv) args :: .seq ss :: K)
        (.argKw (.cls dv) args :: .exprS :: .seq [clsS x.C l y b] :: .tryE [] [] :: .seq (trB x.C ss) :: K')

/-- Comprehensions (`T2Comp.lean`). In the comprehension's frame (chain `.comp l k es gs :: _`),
a clause `g` (node `lg`) loops over the iterator in `iv` (the parameter `.i l` for the first
clause, `.j lg` for the others); the items of list, set and dictionary comprehensions read the
accumulator in `.acc l`. `n`, `m`: the `seq []` items PyCore's nested blocks leave. -/
inductive CompK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  /-- the first iterable is evaluated around the comprehension's function `fo` -/
  | compIt {U K K' o} : KRel x U true K K' →
      CompK x U true (.compIt (.fn o) :: K) (recK [] [] (.callA (.op .iter) :: .callA (.fn o) :: K'))
  | compCall {U K K' o} : KRel x U true K K' → CompK x U true (.compCall (.fn o) :: K) (.callA (.fn o) :: K')
  /-- the bottom of a list, set or dictionary comprehension's frame: the accumulator is made -/
  | compStart {U l ci it g rest gs C0} : x.C = .comp l ci.k ci.es gs :: C0 → ci.k ≠ .gen → ci.acc = .none →
      x.H l → U l → x.own (fresh "i" l) = some it → x.rd (fresh "i" l) = some it →
      FOk x.C (fresh "acc" l) → FOks x.C g.label ["g", "v", "s"] → GsFOk x.C rest →
      GoodGT x.p x.C (Rm U l) g → GoodGs x.p x.C (Rm U l) rest → GoodEs x.p x.C (Rm U l) ci.es →
      g.label ≠ l → GoodGP x.p x.C (Rm (Rm U l) g.label) g → GoodGs x.p x.C (Rm (Rm U l) g.label) rest →
      GoodEs x.p x.C (Rm (Rm U l) g.label) ci.es → NextOk x.p x.C (Rm (Rm U l) g.label) ci.es rest →
      CompK x (Rm U l) true [.compStart ci it g rest]
        [.assign (fresh "acc" l), .seq (trGs x.C (fresh "i" l) true (g :: rest) (compElt l ci.k (trEs x.C ci.es))
          ++ [retAcc l])]
  /-- the bottom: the accumulator is returned when the loops end -/
  | cAcc {U l k es gs C0 acc} : x.C = .comp l k es gs :: C0 → x.rd (fresh "acc" l) = some acc →
      CompK x (Rm U l) false [.cAcc acc] [.seq [retAcc l]]
  /-- the clause `g` awaits its iterator's next item -/
  | cNext {U K K' l ci it g rest gs C0 iv n} : x.C = .comp l ci.k ci.es gs :: C0 → ¬ U l →
      (iv = fresh "i" l ∨ iv = fresh "j" g.label) → x.rd iv = some it →
      x.rd (fresh "g" g.label) = some (.bool true) → (ci.k ≠ .gen → x.rd (fresh "acc" l) = some ci.acc) →
      x.H g.label → FOks x.C g.label ["g", "v", "s"] → GsFOk x.C rest →
      U g.label → GoodGP x.p x.C (Rm U g.label) g → GoodGs x.p x.C (Rm U g.label) rest →
      GoodEs x.p x.C (Rm U g.label) ci.es → NextOk x.p x.C (Rm U g.label) ci.es rest → KRel x U false K K' →
      CompK x (Rm U g.label) true (.cNext ci it g rest :: K)
        (nextK g.label iv (genLoop x.C l ci.k ci.es g rest) [] (seqs n ++ K'))
  /-- the loop of the clause `g` runs its body -/
  | cLoop {U K K' l ci it g rest gs C0 iv n0 n} : x.C = .comp l ci.k ci.es gs :: C0 → ¬ U l →
      (iv = fresh "i" l ∨ iv = fresh "j" g.label) → x.rd iv = some it →
      x.rd (fresh "g" g.label) = some (.bool true) → (ci.k ≠ .gen → x.rd (fresh "acc" l) = some ci.acc) →
      x.H g.label → FOks x.C g.label ["g", "v", "s"] → GsFOk x.C rest →
      U g.label → GoodGP x.p x.C (Rm U g.label) g → GoodGs x.p x.C (Rm U g.label) rest →
      GoodEs x.p x.C (Rm U g.label) ci.es → NextOk x.p x.C (Rm U g.label) ci.es rest → KRel x U false K K' →
      CompK x (Rm U g.label) false (.cLoop ci it g rest :: K)
        (seqs n0 ++ loopK g.label iv (genLoop x.C l ci.k ci.es g rest) [] :: seqs n ++ K')
  /-- the target of `g` is stored: its conditions next -/
  | cConds {U K K' l lg ci ifs rest gs C0} : x.C = .comp l ci.k ci.es gs :: C0 → ¬ U l → x.H lg →
      (ci.k ≠ .gen → x.rd (fresh "acc" l) = some ci.acc) → GsFOk x.C rest → GoodEs x.p x.C U ifs → GoodGs x.p x.C U rest →
      GoodEs x.p x.C U ci.es → NextOk x.p x.C U ci.es rest → KRel x U false K K' →
      CompK x U false (.cConds ci ifs rest :: K) (.seq (genBody x.C l ci.k ci.es lg ifs rest) :: K')
  | cCond {U K K' l lg ci ifs rest gs C0 j} : x.C = .comp l ci.k ci.es gs :: C0 → ¬ U l → x.H lg →
      (ci.k ≠ .gen → x.rd (fresh "acc" l) = some ci.acc) → GsFOk x.C rest → GoodEs x.p x.C U ifs → GoodGs x.p x.C U rest →
      GoodEs x.p x.C U ci.es → NextOk x.p x.C U ci.es rest → KRel x U false K K' →
      CompK x U true (.cCond ci ifs rest :: K) (.ifS (genBody x.C l ci.k ci.es lg ifs rest) [] :: seqs (j + 1) ++ K')
  | cCondT {U K K' l lg ci ifs rest gs C0 j} : x.C = .comp l ci.k ci.es gs :: C0 → ¬ U l → x.H lg →
      (ci.k ≠ .gen → x.rd (fresh "acc" l) = some ci.acc) → GsFOk x.C rest → GoodEs x.p x.C U ifs → GoodGs x.p x.C U rest →
      GoodEs x.p x.C U ci.es → NextOk x.p x.C U ci.es rest → KRel x U false K K' →
      CompK x U true (.cCondT ci ifs rest :: K) (.ifT (genBody x.C l ci.k ci.es lg ifs rest) [] :: seqs (j + 1) ++ K')
  /-- the iterable of a later clause `g` is evaluated, then its `iter` -/
  | cIter {U K K' l ci rest gs C0 m} {g : Gen} : x.C = .comp l ci.k ci.es gs :: C0 → ¬ U l →
      (ci.k ≠ .gen → x.rd (fresh "acc" l) = some ci.acc) → x.H g.label → U g.label →
      FOks x.C g.label ["j", "g", "v", "s"] → GsFOk x.C rest → GoodGP x.p x.C (Rm U g.label) g → GoodGs x.p x.C (Rm U g.label) rest →
      GoodEs x.p x.C (Rm U g.label) ci.es → NextOk x.p x.C (Rm U g.label) ci.es rest → KRel x U false K K' →
      CompK x U true (.cIter ci g rest :: K)
        (recK [] [] (.callA (.op .iter) :: .assign (fresh "j" g.label) ::
          .seq (forLoop g.label (fresh "j" g.label) (trT x.C (forSrc g.label) (match g with | .mk _ t _ _ => t) (trE x.C (match g with | .mk _ t _ _ => t)))
            (genBody x.C l ci.k ci.es g.label (match g with | .mk _ _ _ ifs => ifs) rest) []) :: seqs m ++ K'))
  | cIt {U K K' l ci rest gs C0 m} {g : Gen} : x.C = .comp l ci.k ci.es gs :: C0 → ¬ U l →
      (ci.k ≠ .gen → x.rd (fresh "acc" l) = some ci.acc) → x.H g.label → U g.label →
      FOks x.C g.label ["j", "g", "v", "s"] → GsFOk x.C rest → GoodGP x.p x.C (Rm U g.label) g → GoodGs x.p x.C (Rm U g.label) rest →
      GoodEs x.p x.C (Rm U g.label) ci.es → NextOk x.p x.C (Rm U g.label) ci.es rest → KRel x U false K K' →
      CompK x U true (.cIt ci g rest :: K)
        (.assign (fresh "j" g.label) ::
          .seq (forLoop g.label (fresh "j" g.label) (trT x.C (forSrc g.label) (match g with | .mk _ t _ _ => t) (trE x.C (match g with | .mk _ t _ _ => t)))
            (genBody x.C l ci.k ci.es g.label (match g with | .mk _ _ _ ifs => ifs) rest) []) :: seqs m ++ K')
  /-- the element statement after `accum` or a generator expression's `yield`, which PyCore runs in `m`
  blocks Surf has not -/
  | cExpr {U K K' m} : KRel x U false K K' → CompK x U true (.exprS :: K) (.exprS :: seqs m ++ K')
  /-- a list or set comprehension's element, added to the accumulator -/
  | cElt {U K K' k acc m} : KRel x U false K K' →
      CompK x U true (.cElt k acc :: K) (recK [acc] [] (.callA (.op (.accum k)) :: .exprS :: seqs (m + 1) ++ K'))
  | cKey {U K K' acc v m} : GoodE x.p x.C U v → KRel x U false K K' →
      CompK x U true (.cKey acc v :: K)
        (recK [acc] [trE x.C v] (.callA (.op (.accum .dict)) :: .exprS :: seqs (m + 1) ++ K'))
  | cVal {U K K' acc kv m} : KRel x U false K K' →
      CompK x U true (.cVal acc kv :: K)
        (recK [acc, kv] [] (.callA (.op (.accum .dict)) :: .exprS :: seqs (m + 1) ++ K'))

/-- `for` statements (`T2Loop.lean`), the statement at node `l`, the rest of its block `ss` below:
the iterator in `.i l`, the flag `.g l`, the item `.v l`; PyCore runs the loop in the statement's block. -/
inductive LoopK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  | forIt {U K K' l t b u ss} : NoCompH x.C → x.H l → U l → FOks x.C l ["i", "g", "v", "s"] →
      GoodE x.p x.C (Rm U l) t → tgtOk t = true →
      SubL (PyCore.itemsB R0 (trChain x.C) (trT x.C (forSrc l) t (trE x.C t))) (PI x.p) → GoodB x.p x.C (Rm U l) b → GoodB x.p x.C U u → GoodB x.p x.C U ss →
      KRel x U false K K' →
      LoopK x U true (.forIt t b u :: .seq ss :: K)
        (recK [] [] (.callA (.op .iter) :: .assign (fresh "i" l) ::
          .seq (forLoop l (fresh "i" l) (trT x.C (forSrc l) t (trE x.C t)) (trB x.C b) (trB x.C u)) :: .tryE [] [] ::
          .seq (trB x.C ss) :: K'))
  | forStart {U K K' l t b u ss} : NoCompH x.C → x.H l → U l → FOks x.C l ["i", "g", "v", "s"] →
      GoodE x.p x.C (Rm U l) t → tgtOk t = true →
      SubL (PyCore.itemsB R0 (trChain x.C) (trT x.C (forSrc l) t (trE x.C t))) (PI x.p) → GoodB x.p x.C (Rm U l) b → GoodB x.p x.C U u → GoodB x.p x.C U ss →
      KRel x U false K K' →
      LoopK x U true (.forStart t b u :: .seq ss :: K)
        (.assign (fresh "i" l) ::
          .seq (forLoop l (fresh "i" l) (trT x.C (forSrc l) t (trE x.C t)) (trB x.C b) (trB x.C u)) :: .tryE [] [] ::
          .seq (trB x.C ss) :: K')
  /-- `next` of the iterator runs; PyCore's `while` body is inside the loop, the loop inside the
  statement's block -/
  | forNext {U K K' l t it b u ss} : NoCompH x.C → x.H l → U l → x.rd (fresh "i" l) = some it →
      x.rd (fresh "g" l) = some (.bool true) → FOks x.C l ["g", "v", "s"] → GoodE x.p x.C (Rm U l) t → tgtOk t = true →
      SubL (PyCore.itemsB R0 (trChain x.C) (trT x.C (forSrc l) t (trE x.C t))) (PI x.p) →
      GoodB x.p x.C (Rm U l) b → GoodB x.p x.C U u → GoodB x.p x.C U ss → KRel x U false K K' →
      LoopK x (Rm U l) true (.forNext t it b u :: .seq ss :: K)
        (nextK l (fresh "i" l) (trT x.C (forSrc l) t (trE x.C t) ++ trB x.C b) (trB x.C u)
          (.seq [] :: .tryE [] [] :: .seq (trB x.C ss) :: K'))
  /-- the target is stored, the body runs (PyCore: in the `try`'s `else` block) -/
  | forLoop {U K K' l t it b u ss} : NoCompH x.C → x.H l → U l → x.rd (fresh "i" l) = some it →
      x.rd (fresh "g" l) = some (.bool true) → FOks x.C l ["g", "v", "s"] → GoodE x.p x.C (Rm U l) t → tgtOk t = true →
      SubL (PyCore.itemsB R0 (trChain x.C) (trT x.C (forSrc l) t (trE x.C t))) (PI x.p) →
      GoodB x.p x.C (Rm U l) b → GoodB x.p x.C U u → GoodB x.p x.C U ss → KRel x U false K K' →
      LoopK x (Rm U l) false (.forLoop t it b u :: .seq ss :: K)
        (.seq [] :: loopK l (fresh "i" l) (trT x.C (forSrc l) t (trE x.C t) ++ trB x.C b) (trB x.C u) :: .seq [] ::
          .tryE [] [] :: .seq (trB x.C ss) :: K')

/-- Assignments with a fresh source, unpacking, augmented and annotated assignments, `del`
(`T2Assign.lean`). -/
inductive AsgK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  /-- `ts = e` (node `l`): the value awaited, to be kept in `.t l` -/
  | assignK {U K K' l ts} : U l → FOk x.C (fresh "t" l) → GoodEs x.p x.C (Rm U l) ts →
      SubL (PyCore.itemsB R0 (trChain x.C) (trTs x.C (nameSrc "t" l) ts)) (PI x.p) → KRel x U false K K' →
      AsgK x U true (.assignK ts :: K)
        (.assign (fresh "t" l) :: .seq (trTs x.C (nameSrc "t" l) ts) :: .tryE [] [] :: K')
  /-- the targets still to store, the value in `.t l` -/
  | stManyT {U K K' l ts v} : x.rd (fresh "t" l) = some v → GoodEs x.p x.C (Rm U l) ts →
      SubL (PyCore.itemsB R0 (trChain x.C) (trTs x.C (nameSrc "t" l) ts)) (PI x.p) → KRel x U false K K' →
      AsgK x (Rm U l) false (.stMany (ts.map (·, v)) :: K) (.seq (trTs x.C (nameSrc "t" l) ts) :: .tryE [] [] :: K')
  /-- an attribute target `o.a` (node `lt`): the object awaited, the source read next -/
  | stAttr {U K K' lt a v src} : x.H lt → SrcR x U lt src v → KRel x U false K K' →
      AsgK x U true (.stAttr a v :: K) (recK [] [src] (.callA (.op (.setattr a)) :: .exprS :: K'))
  | stSubL {U K K' lt i v src} : x.H lt → GoodE x.p x.C U i → SrcR x U lt src v → KRel x U false K K' →
      AsgK x U true (.stSubL i v :: K) (recK [] [trE x.C i, src] (.callA (.op .setitem) :: .exprS :: K'))
  | stSubR {U K K' lt o v src} : x.H lt → SrcR x U lt src v → KRel x U false K K' →
      AsgK x U true (.stSubR o v :: K) (recK [o] [src] (.callA (.op .setitem) :: .exprS :: K'))
  /-- a tuple or list target (node `lt`): the unpacking awaited, its items to be kept in `.u lt` -/
  | stUnpack {U K K' lt ts} : x.H lt → U lt → FOk x.C (fresh "u" lt) → GoodEs x.p x.C (Rm U lt) (ts.map unstar) →
      SubL (PyCore.itemsB R0 (trChain x.C) (trItems x.C lt 0 ts)) (PI x.p) → KRel x U false K K' →
      AsgK x U true (.stUnpack (ts.map unstar) :: K)
        (.unpackK ts.length :: .assign (fresh "u" lt) :: .seq (trItems x.C lt 0 ts) :: .tryE [] [] :: K')
  /-- the targets from the `i`-th of an unpacking still to store, the items in `.u lt` -/
  | stManyU {U K K' lt} {ts : List Expr} {ws : List Val} {i : Nat} : x.rd (fresh "u" lt) = some (.tuple ws) → ws.length = ts.length →
      GoodEs x.p x.C (Rm U lt) (ts.map unstar) →
      SubL (PyCore.itemsB R0 (trChain x.C) (trItems x.C lt 0 ts)) (PI x.p) → KRel x U false K K' →
      AsgK x (Rm U lt) false (.stMany (((ts.drop i).map unstar).zip (ws.drop i)) :: K)
        (.seq (trItems x.C lt i (ts.drop i)) :: .tryE [] [] :: K')
  /-- `y op= e` (node `l`, target `lt`): the old value awaited, kept in `.g l` -/
  | augN {U K K' l lt y op e} : x.H l → x.H lt → U l → FOks x.C l ["g", "v"] → ¬ Dot y → GoodE x.p x.C (Rm U l) e →
      KRel x U false K K' →
      AsgK x U true (.augN y op e :: K)
        (.assign (fresh "g" l) :: .seq [augUpd x.C l op e, wrN l lt y] :: .tryE [] [] :: K')
  | augAttr {U K K' l lt a op e} : x.H l → x.H lt → U l → FOks x.C l ["o", "g", "v"] → ':' ∉ a.toList →
      GoodE x.p x.C (Rm U l) e → KRel x U false K K' →
      AsgK x U true (.augAttr a op e :: K)
        (.assign (fresh "o" l) :: .seq [getA l lt a, augUpd x.C l op e, wrA l lt a] :: .tryE [] [] :: K')
  | augAttrV {U K K' l lt ob a op e} : x.H l → x.H lt → U l → x.rd (fresh "o" l) = some ob → FOks x.C l ["g", "v"] →
      ':' ∉ a.toList → GoodE x.p x.C (Rm U l) e → KRel x U false K K' →
      AsgK x (Rm U l) true (.augAttrV ob a op e :: K)
        (.assign (fresh "g" l) :: .seq [augUpd x.C l op e, wrA l lt a] :: .tryE [] [] :: K')
  | augSubL {U K K' l lt i op e} : x.H l → x.H lt → U l → FOks x.C l ["o", "k", "g", "v"] → GoodE x.p x.C (Rm U l) i →
      GoodE x.p x.C (Rm U l) e → KRel x U false K K' →
      AsgK x U true (.augSubL i op e :: K)
        (.assign (fresh "o" l) :: .seq [keyS x.C l lt i, getI l lt, augUpd x.C l op e, wrI l lt] :: .tryE [] [] :: K')
  | augSubI {U K K' l lt ob op e} : x.H l → x.H lt → U l → x.rd (fresh "o" l) = some ob → FOks x.C l ["k", "g", "v"] →
      GoodE x.p x.C (Rm U l) e → KRel x U false K K' →
      AsgK x (Rm U l) true (.augSubI ob op e :: K)
        (.assign (fresh "k" l) :: .seq [getI l lt, augUpd x.C l op e, wrI l lt] :: .tryE [] [] :: K')
  | augSubV {U K K' l lt ob iv op e} : x.H l → x.H lt → U l → x.rd (fresh "o" l) = some ob →
      x.rd (fresh "k" l) = some iv → FOks x.C l ["g", "v"] → GoodE x.p x.C (Rm U l) e → KRel x U false K K' →
      AsgK x (Rm U l) true (.augSubV ob iv op e :: K)
        (.assign (fresh "g" l) :: .seq [augUpd x.C l op e, wrI l lt] :: .tryE [] [] :: K')
  /-- the value of `e` awaited, then the in-place operator -/
  | augR {U K K' l lt op old t w} : x.H l → x.H lt → U l → FOk x.C (fresh "v" l) → AugT x l lt t w →
      KRel x U false K K' →
      AsgK x (Rm U l) true (.augR op old t :: K)
        (.binR (op ++ "=") old :: .assign (fresh "v" l) :: .seq [w] :: .tryE [] [] :: K')
  | augW {U K K' l lt t w} : x.H l → x.H lt → U l → FOk x.C (fresh "v" l) → AugT x l lt t w → KRel x U false K K' →
      AsgK x (Rm U l) true (.augW t :: K) (.assign (fresh "v" l) :: .seq [w] :: .tryE [] [] :: K')
  /-- `t: A = e` (node `l`): the value awaited, kept in `.t l`; the store and the annotation next -/
  | annK {U K K' l t A a} : x.H l → U l → FOk x.C (fresh "t" l) → GoodE x.p x.C (Rm U l) t →
      ((∃ lt y, t = .name lt y) ∨ (∃ lt o a, t = .attr lt o a) ∨ (∃ lt o i, t = .sub lt o i)) →
      a = (if isTop x.C then some A else none) → AnnOk x U l t A → KRel x U false K K' →
      AsgK x U true (.annK t a :: K)
        (.assign (fresh "t" l) :: .seq (trT x.C (nameSrc "t" l) t (trE x.C t) ++ annS x.C l t A) :: .tryE [] [] ::
          K')
  /-- the target stored (or a bare target's parts evaluated): the annotation next (a bare target's
  binding after it, in a branch that never runs) -/
  | annA {U K K' l t A a tail} : x.H l → x.H (Sem.Expr.lbl t) → a = (if isTop x.C then some A else none) →
      AnnOk x U l t A → (tail = [] ∨ tail = [dead (sub l 9) (annBind x.C t)]) → KRel x U false K K' →
      AsgK x (Rm U l) false (.annA t a :: K) (.seq (annS x.C l t A ++ tail) :: .tryE [] [] :: K')
  /-- a name target's annotation value awaited, kept in `.n l`, then its key's store -/
  | annV {U K K' l lt y A tail} : x.H l → x.H lt → isTop x.C = true → AnnOk x U l (.name lt y) A →
      (tail = [] ∨ tail = [dead (sub l 9) (annBind x.C (.name lt y))]) → KRel x U false K K' →
      AsgK x U true (.annV (mangle (priv x.C) y) :: K)
        (.assign (fresh "n" l) :: .seq (annT x.C l (.name lt y) ++ tail) :: .tryE [] [] :: K')
  /-- another target's annotation value awaited, then dropped -/
  | annE {U K K' l t A tail} : x.H l → x.H (Sem.Expr.lbl t) → isTop x.C = true → (∀ lt y, t ≠ .name lt y) →
      AnnOk x U l t A → (tail = [] ∨ tail = [dead (sub l 9) (annBind x.C t)]) → KRel x U false K K' →
      AsgK x U true (.exprS :: K) (.assign (fresh "n" l) :: .seq (annT x.C l t ++ tail) :: .tryE [] [] :: K')
  /-- the end of an augmented or annotated assignment's block (node `l`) after its last operation (a
  `setattr`, `setitem` or `$annot`): PyCore's statement, then the rest of the block -/
  | exprBlk {U K K' tail} : (tail = [] ∨ ∃ l t, x.H l ∧ tail = [dead (sub l 9) (annBind x.C t)]) →
      KRel x U false K K' → AsgK x U true (.exprS :: K) (.exprS :: .seq tail :: .tryE [] [] :: K')
  /-- a bare attribute target's object, evaluated and dropped -/
  | evsDrop1 {U K K'} : KRel x U false K K' → AsgK x U true (.evs [] [] .drop :: K) (.exprS :: K')
  /-- a bare subscript target's parts (node `lt`), evaluated and dropped -/
  | evsDropR {U K K' lt rest acc ps} : x.H lt → PartsR x U lt rest ps → KRel x U false K K' →
      AsgK x U true (.evs rest acc .drop :: K) (recK acc.reverse ps (.exprS :: K'))
  /-- `del ts`: the targets still to delete -/
  | delMany {U K K' ts Kp} : GoodEs x.p x.C U ts → delOks ts = true → DelSeg x.C ts Kp (.tryE [] [] :: K') →
      KRel x U false K K' →
      AsgK x U false (.delMany ts :: K) Kp
  | delAttr {U K K' a} : KRel x U false K K' →
      AsgK x U true (.delAttr a :: K) (recK [] [] (.callA (.op (.delattr a)) :: .exprS :: K'))
  | delSubL {U K K' i} : GoodE x.p x.C U i → KRel x U false K K' →
      AsgK x U true (.delSubL i :: K) (recK [] [trE x.C i] (.callA (.op .delitem) :: .exprS :: K'))
  | delSubR {U K K' o} : KRel x U false K K' →
      AsgK x U true (.delSubR o :: K) (recK [o] [] (.callA (.op .delitem) :: .exprS :: K'))

/-- Attributes, subscripts, unary operators, formatted values, displays, slices and f-strings (`evs`
with `Then.op`) (`T2Access.lean`). -/
inductive AccK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  | unK {U K K' op} : KRel x U true K K' →
      AccK x U true (.unK op :: K) (recK [] [] (.callA (.op (.unop op)) :: K'))
  | attrK {U K K' a} : KRel x U true K K' →
      AccK x U true (.attrK a :: K) (recK [] [] (.callA (.op (.getattr a)) :: K'))
  | subL {U K K' i} : GoodE x.p x.C U i → KRel x U true K K' →
      AccK x U true (.subL i :: K) (recK [] [trE x.C i] (.callA (.op .getitem) :: K'))
  | subR {U K K' o} : KRel x U true K K' →
      AccK x U true (.subR o :: K) (recK [o] [] (.callA (.op .getitem) :: K'))
  | fmtV {U K K' c spec} : GoodO x.p x.C U spec → KRel x U true K K' →
      AccK x U true (.fmtV c spec :: K)
        (if c = -1 then fmtRest x.C spec K' else recK [] [] (.callA (.op (.convert c)) :: fmtRest x.C spec K'))
  | fmtC {U K K' spec} : GoodO x.p x.C U spec → KRel x U true K K' →
      AccK x U true (.fmtC spec :: K) (fmtRest x.C spec K')
  | fmtS {U K K' v} : KRel x U true K K' →
      AccK x U true (.fmtS v :: K) (recK [v] [] (.callA (.op .format) :: K'))
  /-- the parts `rest` of a slice or an f-string (node `l`) still to evaluate, the values `acc` so far
  (reversed), then the operation `o` -/
  | evsOp {U K K' l rest ps acc o} : x.H l → PartsR x U l rest ps → KRel x U true K K' →
      AccK x U true (.evs rest acc (.op o) :: K) (recK acc.reverse ps (.callA (.op o) :: K'))
  /-- the items of a list display (node `l`) still to evaluate; PyCore's record ends with their markers,
  whose nodes are touched up to the current item -/
  | evsList {U K K' l es rest acc ps} : GoodE x.p x.C U (.list l es) →
      acc.length < (partsDisp es).length → rest = (partsDisp es).drop (acc.length + 1) →
      (∀ e ∈ es.take (acc.length + 1), x.H (Sem.Expr.lbl e)) → PartsR x U l rest ps → KRel x U true K K' →
      AccK x U true (.evs rest acc (.op (.display (.list (es.map isStar)))) :: K)
        (recK acc.reverse (ps ++ es.map starMark) (.callA (.prim (Gadget.display "list").name) :: K'))
  | evsTuple {U K K' l es rest acc ps} : GoodE x.p x.C U (.tuple l es) →
      acc.length < (partsDisp es).length → rest = (partsDisp es).drop (acc.length + 1) →
      (∀ e ∈ es.take (acc.length + 1), x.H (Sem.Expr.lbl e)) → PartsR x U l rest ps → KRel x U true K K' →
      AccK x U true (.evs rest acc (.op (.display (.tuple (es.map isStar)))) :: K)
        (recK acc.reverse (ps ++ es.map starMark) (.callA (.prim (Gadget.display "tuple").name) :: K'))
  /-- a set display: the items' markers read their constness nodes, touched when the item is entered -/
  | evsSet {U K K' l es rest acc ps} : GoodE x.p x.C U (.set l es) →
      acc.length < (partsDisp es).length → rest = (partsDisp es).drop (acc.length + 1) →
      (∀ e ∈ es.take (acc.length + 1), ∀ c ∈ setOwners e, x.H c) → PartsR x U l rest ps → KRel x U true K K' →
      AccK x U true (.evs rest acc (.op (.display (if es.length > 2 && es.all isConstE then Py.Disp.constSet
          else Py.Disp.set (es.map isStar)))) :: K)
        (recK acc.reverse (ps ++ es.map (constMark 57)) (.callA (.prim (Gadget.display "set").name) :: K'))

/-- Chained comparisons, `assert`, `raise`, imports, `yield from` (`T2Misc.lean`). -/
inductive MiscK (x : Cx) : (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop
  /-- a single comparison: PyCore's own binary operator -/
  | cmpL1 {U K K' o e} : GoodE x.p x.C U e → o ≠ "," → KRel x U true K K' →
      MiscK x U true (.cmpL [o] [e] :: K) (.binL o (trE x.C e) :: K')
  /-- the first operand of a chain (node `l`, whose nodes PyCore's chain has); the middle operand `e`
  is kept in `.c e.label` -/
  | cmpLm {U K K' l o o' ops e e' es} : x.H l → GoodEs x.p x.C U (e :: e' :: es) → ops.length = es.length →
      (∀ q ∈ o :: o' :: ops, q ≠ ",") → (labelsEs (e :: e' :: es)).Nodup → KRel x U true K K' →
      MiscK x U true (.cmpL (o :: o' :: ops) (e :: e' :: es) :: K)
        (.binL o (gad l 3 (.set (fresh "c" e.label)) [trE x.C e]) ::
          .boolK true (cmpRest x.C l e.label (o' :: ops) (e' :: es)) :: K')
  | cmpR1 {U K K' a o} : o ≠ "," → KRel x U true K K' → MiscK x U true (.cmpR a o [] [] :: K) (.binR o a :: K')
  /-- a middle operand (node `lb`) is evaluated, into `$set` -/
  | cmpRm {U K K' l a o ops es lb} : x.H l → U lb → GoodEs x.p x.C (Rm U lb) es → ops.length = es.length →
      ops ≠ [] → (∀ q ∈ o :: ops, q ≠ ",") → (labelsEs es).Nodup → KRel x U true K K' →
      MiscK x U true (.cmpR a o ops es :: K)
        (recK [] [] (.callA (.prim (Gadget.set (fresh "c" lb)).name) :: .binR o a ::
          .boolK true (cmpRest x.C l lb ops es) :: K'))
  /-- the last comparison's result -/
  | cmpONil {U K K' b es} : KRel x U true K K' → MiscK x U true (.cmpO b [] es :: K) K'
  | cmpO {U K K' l b ops es lb} : x.H l → x.own (fresh "c" lb) = some b → GoodEs x.p x.C (Rm U lb) es →
      ops.length = es.length → ops ≠ [] → (∀ q ∈ ops, q ≠ ",") → (labelsEs es).Nodup → KRel x U true K K' →
      MiscK x (Rm U lb) true (.cmpO b ops es :: K) (.boolK true (cmpRest x.C l lb ops es) :: K')
  | cmpT {U K K' l r b ops es lb} : x.H l → x.own (fresh "c" lb) = some b → GoodEs x.p x.C (Rm U lb) es →
      ops.length = es.length → ops ≠ [] → (∀ q ∈ ops, q ≠ ",") → (labelsEs es).Nodup → KRel x U true K K' →
      MiscK x (Rm U lb) true (.cmpT r b ops es :: K) (.boolT true r (cmpRest x.C l lb ops es) :: K')
  /-- `assert t, m` (node `l`) -/
  | assertK {U K K' l m} : x.H l → GoodO x.p x.C U m → KRel x U false K K' →
      MiscK x U true (.assertK m :: K) (.ifS [] [assertRaise x.C l m] :: K')
  | assertT {U K K' l m} : x.H l → GoodO x.p x.C U m → KRel x U false K K' →
      MiscK x U true (.assertT m :: K) (.ifT [] [assertRaise x.C l m] :: K')
  | assertM {U K K'} : KRel x U false K K' →
      MiscK x U true (.assertM :: K)
        (recK [] [] (.callA (.prim (Gadget.raiseK "AssertionError").name) :: .exprS :: .seq [] :: K'))
  /-- `raise e`: its value, then the exception made of it -/
  | evsRaise {U K K'} : KRel x U false K K' → MiscK x U true (.evs [] [] (.raise false) :: K) (.raiseS :: K')
  | raiseCn {U K K'} : KRel x U false K K' → MiscK x U true (.raiseC none :: K) (.raiseE :: K')
  /-- `raise e from c` -/
  | evsRaiseFrom {U K K' c} : GoodE x.p x.C U c → KRel x U false K K' →
      MiscK x U true (.evs [some c] [] (.raise true) :: K)
        (recK [] [trE x.C c] (.callA (.prim Gadget.raiseFrom.name) :: .exprS :: K'))
  | evsRaiseFrom2 {U K K' v} : KRel x U false K K' →
      MiscK x U true (.evs [] [v] (.raise true) :: K)
        (recK [v] [] (.callA (.prim Gadget.raiseFrom.name) :: .exprS :: K'))
  | raiseCs {U K K' cv} : KRel x U false K K' →
      MiscK x U true (.raiseC (some cv) :: K) (.raiseC cv :: .exprS :: K')
  | raiseW {U K K' e} : KRel x U false K K' → MiscK x U true (.raiseW e :: K) (.raiseW e :: .exprS :: K')
  /-- `import a₁, …`: the module of an alias awaited, the aliases `al` after it -/
  | impMany {U K K' l y} {al : List Alias} : ¬ Dot y → (∀ a ∈ al, okAl a = true) →
      (∀ a ∈ al, ¬ Dot (mangle (priv x.C) a.bound)) → KRel x U false K K' →
      MiscK x U true (.assignN y :: .seq (al.map fun a => .imp l [a]) :: K)
        (.assign y :: .seq (al.map (impS x.C)) :: .tryE [] [] :: K')
  /-- `from m import …` (node `l`): the module awaited, kept in `.m l` -/
  | impMod {U K K' l al} : U l → FOk x.C (fresh "m" l) → (∀ a ∈ al, okAl a = true) →
      (∀ a ∈ al, a.name ≠ "*" → ¬ Dot (mangle (priv x.C) a.bound)) → KRel x U false K K' →
      MiscK x U true (.impMod al :: K) (.assign (fresh "m" l) :: .seq (al.map (fromS x.C l)) :: .tryE [] [] :: K')
  | impNext {U K K' l m al} : x.rd (fresh "m" l) = some m → (∀ a ∈ al, okAl a = true) →
      (∀ a ∈ al, a.name ≠ "*" → ¬ Dot (mangle (priv x.C) a.bound)) → KRel x U false K K' →
      MiscK x (Rm U l) false (.impNext m al :: K) (.seq (al.map (fromS x.C l)) :: .tryE [] [] :: K')
  | starStore {U K K'} : KRel x U false K K' →
      MiscK x U true (.starStore :: K) (recK [] [] (.callA (.prim Gadget.starstore.name) :: .exprS :: K'))
  /-- `yield from`: the operand, its iterator, the delegate's next item -/
  | yfK {U K K'} : KRel x U true K K' → MiscK x U true (.yfK :: K) (.yfStart :: K')
  | yfIt {U K K'} : KRel x U true K K' → MiscK x U true (.yfIt :: K) (.yfIt :: K')
  | yfN {U K K' sb d} : DelegR sb d → KRel x U true K K' → MiscK x U true (.yfN sb :: K) (.yfGot d :: K')
end

/-! ## Controls -/

/-- Surf's control and PyCore's, with the index of the continuation they run on and the label
budget of the code they run. -/
inductive CR (p : List Stmt) (C : List Scope) (U : Label → Prop) : Bool → Sem.Ctrl σ → PyCore.Ctrl σ → Prop
  | ev {e} : GoodE p C U e → CR p C U true (.ev e) (.ev (trE C e))
  | val {v} : CR p C U true (.val v) (.val v)
  | exec {ss} : GoodB p C U ss → (ss ≠ [] → NoCompH C) → CR p C U false (.exec ss) (.exec (trB C ss))
  | raise {i v} : CR p C U i (.raise v) (.raise v)
  | retv {i v} : CR p C U i (.retv v) (.retv v)
  | brk : NoCompH C → CR p C U false .brk .brk
  | cont : NoCompH C → CR p C U false .cont .cont
  | wait {i} : CR p C U i .wait .wait
  | op {o vs} : CR p C U true (.op o vs) (.op o vs)
  | kapp {k r} : CR p C U true (.kapp k r) (.kapp k r)
  | call {g args kws} : CR p C U true (.call g args kws) (.call g args kws)
  | ns {i ns} : CR p C U i (.ns ns) (.ns ns)

/-- Suspended generator frames before their first resumption, or inside a `yield from`: PyCore
has steps to make before the frames correspond (the resumption lemmas take them): a generator
expression's loops' start, a generator function's or lambda's parameters' bindings, or a `yield from`
that has yielded its delegate's item. -/
inductive Special (x : Cx) : Sem.Ctrl σ → List (Sem.Kont σ) → PyCore.Ctrl σ → List (PyCore.Kont σ) → Prop
  /-- a generator expression's frame (chain `.comp l .gen es (g :: rest) :: _`), not yet run -/
  | genComp {l es g rest C0 it} : x.C = .comp l .gen es (g :: rest) :: C0 → x.H l →
      g.label ≠ l → GoodGP x.p x.C (Rm (Rm UAll l) g.label) g → GoodGs x.p x.C (Rm (Rm UAll l) g.label) rest →
      GoodEs x.p x.C (Rm (Rm UAll l) g.label) es → NextOk x.p x.C (Rm (Rm UAll l) g.label) es rest →
      x.rd (fresh "i" l) = some it → x.own (fresh "i" l) = some it →
      FOks x.C g.label ["g", "v", "s"] → GsFOk x.C rest → GoodGT x.p x.C UAll g → GoodGs x.p x.C UAll rest → GoodEs x.p x.C UAll es →
      Special x (.call .next [it] []) [.cNext ⟨.gen, es, .none⟩ it g rest]
        (.exec (trGs x.C (fresh "i" l) true (g :: rest) (compElt l .gen (trEs x.C es)))) []
  /-- a generator function's frame (chain `.fn l g ps b :: _`), not yet run: PyCore's body starts with the
  parameters' bindings, in branches that never run -/
  | genFn {l g ps b C0} : x.C = .fn l g ps b :: C0 → (∀ q ∈ ps, x.H q.label) → GoodB x.p x.C UAll b →
      Special x (.exec b) [] (.exec (paramBind x.C ps ++ trB x.C b)) []
  /-- a generator lambda's frame, not yet run -/
  | genLam {l ps b C0} : x.C = .lam l ps b :: C0 → (∀ q ∈ ps, x.H q.label) → GoodE x.p x.C UAll b →
      Special x (.ev b) [.retS] (.exec (paramBind x.C ps ++ [.ret (sub l 2) (trE x.C b)])) []
  /-- inside a `yield from`, after its delegate's item was yielded -/
  | yf {U K K' sb d} : DelegR sb d → KRel x U true K K' → Special x (.val .none) (.yfR sb :: K) (.yfStep d) K'

end

/-! ## Frames, objects, configurations -/

def fk : Sem.FKind → PyCore.FKind
  | .mod => .mod
  | .fn => .fn
  | .gen o => .gen o
  | .cls => .cls

/-- The kind of a frame and the scope at the head of its chain. -/
def KC : Sem.FKind → List Scope → Prop
  | .mod, [] => True
  | .cls, .cl .. :: _ => True
  | .fn, .fn .. :: _ | .fn, .lam .. :: _ | .fn, .comp .. :: _ => True
  | .gen _, .fn .. :: _ | .gen _, .lam .. :: _ | .gen _, .comp .. :: _ => True
  | _, _ => False

/-- PyCore's kind of each comprehension's function in a chain is the comprehension's: a generator
for a generator expression (PEP 709 inlines the others, `inlinedLocal`); each class's name is a
program's name (`okName`: no `:`, which mangled names in core constants need). -/
def KOk : List Scope → Prop
  | [] => True
  | S :: C => (match S with
      | .comp _ k _ _ => (trScope C S).kind = (if k = .gen then .gen else .plain)
      | .cl _ x _ => okName x = true
      | _ => True) ∧ KOk C

variable {σ : Type}

/-- The static part of the frame relation: everything but the code. -/
structure FRel0 (f : Sem.Frame σ) (f' : PyCore.Frame σ) : Prop where
  id : f'.id = f.id
  chain : f'.chain = trChain f.chain
  cls : f.cls = clsOf f.chain
  pcls : f'.cls = PyCore.clsOf f'.chain
  kind : f'.kind = fk f.kind
  kc : KC f.kind f.chain
  κ : ∀ x, ¬ Dot x → f'.κ x = f.κ x
  /-- a closure environment holds cells of the same name -/
  κa : ∀ x a, f.κ x = some a → a.2 = x
  ns : PyCore.dropReserved f'.ns = f.ns
  kok : KOk f.chain

/-- The context of a frame's continuation relation. -/
abbrev cx (p : List Stmt) (H : Label → Prop) (rd own : Name → Option Val) (f : Sem.Frame σ) : Cx :=
  ⟨p, f.chain, rd, own, H⟩

structure FRel (p : List Stmt) (H : Label → Prop) (rd own : Name → Option Val) (f : Sem.Frame σ)
    (f' : PyCore.Frame σ) : Prop extends FRel0 f f' where
  /-- the frame's scope node was touched -/
  hl : ∀ S C, f.chain = S :: C → H S.label
  code : ∃ U i, CR p f.chain U i f.ctrl f'.ctrl ∧ KRel (cx p H rd own f) U i f.kont f'.kont

/-- Generators. -/
inductive GRel (p : List Stmt) (H : Label → Prop) (gl : Name → Option Val) (cs : Std.HashMap PyCore.Addr Val) :
    Sem.GSt σ → PyCore.GSt σ → Prop
  | susp {f f'} : FRel p H (rdAt gl cs f') (ownAt cs f') f f' → GRel p H gl cs (.susp f) (.susp f')
  | special {f f'} : FRel0 f f' → (∀ S C, f.chain = S :: C → H S.label) →
      Special (cx p H (rdAt gl cs f') (ownAt cs f') f) f.ctrl f.kont f'.ctrl f'.kont → GRel p H gl cs (.susp f) (.susp f')
  | running : GRel p H gl cs .running .running
  | done : GRel p H gl cs .done .done

/-- A function object's signature and defaults as PyCore's closure holds them: none for a
comprehension's function (called on its iterator); for a `def` or lambda, the parameters (mangled
in its own scope) and the defaults. -/
def SigR (S : Scope) (C : List Scope) (dflt : List (Option Val)) : Option PyCore.Sig → Prop
  | none => S.isComp = true
  | some (sig, d) => d = dflt ∧ match S with
    | .fn _ _ ps _ | .lam _ ps _ => sig = ps.map fun q => (mangle (priv (S :: C)) q.name, q.kind.pk)
    | _ => False

/-- The code of a scope is code of `p`. -/
def GoodSc (p : List Stmt) (C : List Scope) : Scope → Prop
  | S@(.fn _ _ _ b) => GoodB p (S :: C) UAll b
  | S@(.lam _ _ b) => GoodE p (S :: C) UAll b
  | S@(.comp l k es gs) => GoodE p C UAll (.comp l k es gs) ∧ GoodEs p (S :: C) UAll es ∧ (match gs with
      | g :: rest => GoodGT p (S :: C) UAll g ∧ GoodGs p (S :: C) UAll rest
      | [] => False)
  | .cl .. => True

/-- The parameters of a scope. -/
def _root_.Surf.Scope.params : Scope → List Param
  | .fn _ _ ps _ | .lam _ ps _ => ps
  | _ => []

/-- A function object and a closure of its translated scope. -/
inductive ORel (p : List Stmt) (H : Label → Prop) (gl : Name → Option Val) (cs : Std.HashMap PyCore.Addr Val) :
    Sem.Obj σ → PyCore.Obj σ → Prop
  | clo {S C cl cl' κ κ' kd dflt sg} : cl = clsOf (S :: C) → cl' = PyCore.clsOf (trChain (S :: C)) →
      kd = S.kind C → (∀ x, ¬ Dot x → κ' x = κ x) → (∀ x a, κ x = some a → a.2 = x) →
      SigR S C dflt sg → H S.label → (∀ q ∈ S.params, H q.label) → GoodSc p C S → KOk (S :: C) →
      ORel p H gl cs (.clo S C cl κ kd dflt) (.clo (trScope C S) (trChain C) cl' κ' sg)
  | gen {g g'} : GRel p H gl cs g g' → ORel p H gl cs (.gen g) (.gen g')

/-- PyCore's frame ids: distinct on the stack, below `next`; a suspended generator's frame has the
generator's address, which no frame on the stack has. -/
structure Ids (t : PyCore.Config σ) : Prop where
  nodup : (t.stack.map (·.id)).Nodup
  lt : ∀ g ∈ t.stack, g.id < t.next
  obj : ∀ o b, pObj t o = some b → o < t.next
  susp : ∀ o g, pObj t o = some (.gen (.susp g)) → g.id = o ∧ ∀ h ∈ t.stack, h.id ≠ o
  gk : ∀ g ∈ t.stack, ∀ o, g.kind = .gen o → g.id = o
  /-- the module frame has id 0 (so it is the only one on the stack) -/
  m0 : ∀ g ∈ t.stack, g.kind = .mod → g.id = 0
  /-- a suspended generator's frame is a generator frame -/
  sk : ∀ o g, pObj t o = some (.gen (.susp g)) → g.kind = .gen o

structure CRel (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) : Prop where
  stack : PyCore.All2 (fun f f' => FRel p H (rdOf t f') (ownOf t f') f f') s.stack t.stack
  objs : ∀ o, PyCore.OptRel (ORel p H t.glob t.cells) (sObj s o) (pObj t o)
  cells : ∀ a : Sem.Addr, ¬ Dot a.2 → pCell t a = sCell s a
  glob : ∀ x, ¬ Dot x → pGlob t x = sGlob s x
  out : t.out = []
  next : t.next = s.next
  res : t.res = s.res
  st : t.st = s.st
  /-- every frame below the top waits for its callee -/
  wait : ∀ g ∈ s.stack.tail, g.ctrl = .wait
  ids : Ids t
  /-- every pending `enterK` (of a frame or of a suspended generator) names an allocated address with no
  comprehension's function object (Surf and PyCore would enter it differently) -/
  enter : EnterInv s.objs s.stack

/-- The initial configurations: Surf's module frame starts with `SETUP_ANNOTATIONS`'s dictionary,
PyCore's with the statement `setupS 0`. -/
def InitRel (p : List Stmt) (s : Sem.Config σ) (t : PyCore.Config σ) : Prop :=
  ∃ (σ0 : Std.HashMap Name Val) (s0 : σ), s = Sem.init p σ0 s0 ∧ t = PyCore.init (tr p) (fun x => σ0[x]?) s0

/-- A call PyCore holds as the value and the call of `g` (a loop's `next`, a function object on one
argument, such as a comprehension's on its iterator), Surf at the call: related as the call (`CRel` with
PyCore's call control). -/
def PendRel (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) : Prop :=
  ∃ (f : Sem.Frame σ) (fs : List (Sem.Frame σ)) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (g v : Val)
    (K' : List (PyCore.Kont σ)), s.stack = f :: fs ∧ t.stack = f' :: fs' ∧ f.ctrl = .call g [v] [] ∧
    -- PyCore holds the value and the call of `g` (a loop's `next`, a comprehension's function)
    ((f'.ctrl = .val v ∧ f'.kont = .callA g :: K' ∧
      (g = .next ∨ ∃ o, g = .fn o) ∧
      CRel p H s { t with stack := { f' with ctrl := .call g [v] [], kont := K' } :: fs' }) ∨
    -- or `yield from` asks its suspended delegate generator `o` for the next item
    (∃ o g0, g = .next ∧ v = .gen o ∧ f'.ctrl = .yfStep (.gen o) ∧ f'.kont = K' ∧
      pObj t o = some (.gen (.susp g0)) ∧
      CRel p H s { t with stack := { f' with ctrl := .call .next [.gen o] [], kont := .yfGot (.gen o) :: K' } :: fs' }))

def CRelI (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) : Prop :=
  CRel p H s t ∨ InitRel p s t ∨ PendRel p H s t

/-- The conditions on `p` (each holds for every Python program): distinct labels (positions), all
of them positive (the exporter labels nodes from 1; the module's `SETUP_ANNOTATIONS` uses labels
below 64), no name with a dot (no Python identifier has one), augmented targets that are names,
attributes or subscripts (Python's grammar), and the shape conditions `okB` of Python's ASTs. -/
structure WF (p : List Stmt) : Prop where
  nodup : (labelsB p).Nodup
  pos : ∀ l ∈ labelsB p, 0 < l
  nodot : NoDot p
  reg : regB {} [] p = true
  ok : okB p = true

/-- The context of a step: configurations related but for the top frames' code. -/
structure At0 (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) (f : Sem.Frame σ)
    (fs : List (Sem.Frame σ)) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) : Prop where
  hs : s.stack = f :: fs
  ht : t.stack = f' :: fs'
  hf : FRel0 f f'
  hl : ∀ S C, f.chain = S :: C → H S.label
  hfs : PyCore.All2 (fun f f' => FRel p H (rdOf t f') (ownOf t f') f f') fs fs'
  objs : ∀ o, PyCore.OptRel (ORel p H t.glob t.cells) (sObj s o) (pObj t o)
  cells : ∀ a : Sem.Addr, ¬ Dot a.2 → pCell t a = sCell s a
  glob : ∀ x, ¬ Dot x → pGlob t x = sGlob s x
  out : t.out = []
  next : t.next = s.next
  res : t.res = s.res
  st : t.st = s.st
  wait : ∀ g ∈ fs, g.ctrl = .wait
  ids : Ids t
  enter : EnterInv s.objs (f :: fs)

/-- The context of a case: related configurations whose top frames are `f` and `f'`. -/
structure At (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) (f : Sem.Frame σ)
    (fs : List (Sem.Frame σ)) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) : Prop where
  r : CRel p H s t
  hs : s.stack = f :: fs
  ht : t.stack = f' :: fs'
  hf : FRel p H (rdOf t f') (ownOf t f') f f'

/-- The context of the top frame's continuation relation. -/
abbrev At.x {p H s t f fs f' fs'} (_ : @At σ p H s t f fs f' fs') : Cx := cx p H (rdOf t f') (ownOf t f') f

/-! ## Outcomes, reach, the measure, the simulation step -/

/-- Corresponding outcomes: the same output (PyCore's output list stays empty: output is the
interpretation's), state, exception or value, and module dictionaries equal on every name with
no dot. -/
def OCorr : Sem.Outcome σ → PyCore.Outcome σ → Prop
  | .normal st g, .normal out g' st' => out = [] ∧ st' = st ∧ ∀ x, ¬ Dot x → g' x = g[x]?
  | .exc v st, .exc v' out st' => v' = v ∧ out = [] ∧ st' = st
  | .stuck st, .stuck out st' => out = [] ∧ st' = st
  | _, _ => False

/-- What the top frame touches besides `Sem.focus`: the target a store (`Ctrl.store`) or a `del`
(`Kont.delMany`) evaluates; a `def`'s or lambda's parameters when its function object is made;
a keyword argument's or comprehension clause's node when its value or iterable is evaluated
(`touchB`), and a clause's node at each `next` of its iterator and when its iterable is entered (each
of these follows, in a run, the evaluation of that iterable, so a run from the start touches the same
nodes); an import alias when it is bound. -/
def TouchF (p : List Stmt) (f : Sem.Frame σ) (l : Label) : Prop :=
  match f.ctrl, f.kont with
  | .store t _, _ => Sem.Expr.lbl t = l ∨ l ∈ tgtKids t
  | .exec (.augassign _ t _ _ :: _), _ => Sem.Expr.lbl t = l
  | .exec (.annassign _ t _ none :: _), _ => Sem.Expr.lbl t = l
  | .exec [], .delMany (t :: _) :: _ => Sem.Expr.lbl t = l
  | .val _, .evsEnd (.defn _ _ ps _ _ _) :: _ => ∃ q ∈ ps, q.label = l
  | .val _, .evsEnd (.lam _ ps _) :: _ => ∃ q ∈ ps, q.label = l
  | .ev e, .evs _ _ (.op (.display (.set _))) :: _ => (l, e) ∈ touchB p ∨ l ∈ constNodes e
  | .ev e, .evs _ _ (.op (.display .constSet)) :: _ => (l, e) ∈ touchB p ∨ l ∈ constNodes e
  | .ev e, _ => (l, e) ∈ touchB p
  | .exec (.imp _ [a] :: _), _ => a.l = l
  | .exec [], .impNext _ (a :: _) :: _ => a.l = l
  | .call _ _ _, .cNext _ _ g _ :: _ => g.label = l
  | .exec [], .cConds _ [] (g :: _) :: _ => g.label = l
  | _, _ => False

/-- The Surf nodes a configuration touches. -/
def Touch (p : List Stmt) (c : Sem.Config σ) (l : Label) : Prop :=
  Sem.focus c = some l ∨ match c.stack with
    | f :: _ => TouchF p f l
    | [] => False

/-- The Surf run from `c` touches no node of `F`. -/
def NoReachT (p : List Stmt) (I : Py.Interp σ) (F : Label → Prop) (c : Sem.Config σ) : Prop :=
  ∀ n l, Touch p (Sem.run I n c) l → ¬ F l

/-- PyCore's focus, but for the module's `SETUP_ANNOTATIONS` (labels below 64, made for no Surf
node). -/
def pfocus (t : PyCore.Config σ) : Option Label :=
  match PyCore.focus t with
  | some x => if 64 ≤ x then some x else none
  | none => none

/-- The measure of stuttering: the lengths of the top frames' continuations, a `yield from`'s
`yfStep` counted as the item `yfGot` it pushes. -/
def μ (s : Sem.Config σ) (t : PyCore.Config σ) : Nat :=
  (match s.stack with | f :: _ => f.kont.length | [] => 0) +
  (match t.stack with
    | f :: _ => f.kont.length + (match f.ctrl with | .yfStep _ => 1 | _ => 0)
    | [] => 0)

def Fin (s : Sem.Config σ) (t : PyCore.Config σ) : Prop := OCorr (Sem.outcome s) (PyCore.outcome t)

/-- One simulation step of (T2), `H` the Surf nodes touched before. -/
abbrev Goal (I : Py.Interp σ) (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) : Prop :=
  SimStep (Sem.step I) (PyCore.step I) (CRelI p) Fin μ (Touch p) pfocus H s t

/-- A simulation step in which PyCore's run moves (or both end): the conclusion of the call lemmas, which
`callA_sim` turns into a step from PyCore's configuration before the call (a loop's `next`). -/
abbrev GoalB (I : Py.Interp σ) (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) : Prop :=
  SimStepB (Sem.step I) (PyCore.step I) (CRelI p) Fin μ (Touch p) pfocus H s t

/-- The continuation is at a bare `except` (a handler with no class). -/
def BareAt (x : Cx) (U : Label → Prop) (i : Bool) (K : List (Sem.Kont σ)) (K' : List (PyCore.Kont σ)) : Prop :=
  ∃ lh y hb hs u K0 K0', K = .tryE (.mk lh none y hb :: hs) u :: K0 ∧
    K' = .tryE (trHs x.C (.mk lh none y hb :: hs)) (trB x.C u) :: K0' ∧ GoodHs x.p x.C U (.mk lh none y hb :: hs) ∧
    GoodB x.p x.C U u ∧ KRel x U false K0 K0'

/-- The hypotheses of an `ev e` case. -/
abbrev EvCase (I : Py.Interp σ) (p : List Stmt) (e : Expr) : Prop :=
  ∀ {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {U : Label → Prop} (A : At p H s t f fs f' fs'),
    WF p → f.ctrl = .ev e → f'.ctrl = .ev (trE f.chain e) →
    GoodE p f.chain U e → KRel A.x U true f.kont f'.kont → Goal I p H s t

/-- The hypotheses of an `exec (st :: ss)` case. -/
abbrev ExecCase (I : Py.Interp σ) (p : List Stmt) (st : Stmt) : Prop :=
  ∀ {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {U : Label → Prop} {ss : List Stmt}
    (A : At p H s t f fs f' fs'), WF p → f.ctrl = .exec (st :: ss) → f'.ctrl = .exec (trB f.chain (st :: ss)) →
    GoodB p f.chain U (st :: ss) → (st :: ss ≠ [] → NoCompH f.chain) → KRel A.x U false f.kont f'.kont →
    Goal I p H s t

/-- The hypotheses of a case on the continuation's top item (the family `Fam`): the controls
`c`, `c'` with the index `i`. -/
abbrev KCase (I : Py.Interp σ) (p : List Stmt) (i : Bool)
    (Fam : Cx → (Label → Prop) → Bool → List (Sem.Kont σ) → List (PyCore.Kont σ) → Prop)
    (Ctl : Bool → List Scope → (Label → Prop) → Sem.Ctrl σ → PyCore.Ctrl σ → Prop) : Prop :=
  ∀ {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {U : Label → Prop} (A : At p H s t f fs f' fs'),
    WF p → Ctl i f.chain U f.ctrl f'.ctrl → Fam A.x U i f.kont f'.kont → Goal I p H s t

/-- A value reaches the continuation. -/
def CVal (_ : Bool) (_ : List Scope) (_ : Label → Prop) (c : Sem.Ctrl σ) (c' : PyCore.Ctrl σ) : Prop :=
  ∃ v, c = .val v ∧ c' = .val v

/-- A statement or block ended. -/
def CDone (_ : Bool) (_ : List Scope) (_ : Label → Prop) (c : Sem.Ctrl σ) (c' : PyCore.Ctrl σ) : Prop :=
  c = .exec [] ∧ c' = .exec []

/-- A signal passes the continuation (of index `i`): an exception, a return, and `break`, `continue`,
which reach only continuations awaiting no value (`CR.brk`, `CR.cont`). -/
def CSig (i : Bool) (C : List Scope) (_ : Label → Prop) (c : Sem.Ctrl σ) (c' : PyCore.Ctrl σ) : Prop :=
  (∃ v, c = .raise v ∧ c' = .raise v) ∨ (∃ v, c = .retv v ∧ c' = .retv v) ∨
  (i = false ∧ NoCompH C ∧ c = .brk ∧ c' = .brk) ∨ (i = false ∧ NoCompH C ∧ c = .cont ∧ c' = .cont)

/-- A class body's namespace reaches the continuation. -/
def CNs (_ : Bool) (_ : List Scope) (_ : Label → Prop) (c : Sem.Ctrl σ) (c' : PyCore.Ctrl σ) : Prop :=
  ∃ ns, c = .ns ns ∧ c' = .ns ns

theorem run_eq (I : Py.Interp σ) : ∀ n (c : Sem.Config σ), Sem.run I n c = runF (Sem.step I) n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [Sem.run, runF]
    cases Sem.step I c <;> simp [run_eq I n]

theorem prun_eq (I : Py.Interp σ) : ∀ n (c : PyCore.Config σ), PyCore.run I n c = runF (PyCore.step I) n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [PyCore.run, runF]
    cases PyCore.step I c <;> simp [prun_eq I n]

end Surf.T2
