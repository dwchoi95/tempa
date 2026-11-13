/-
The translation ⌊·⌋ of Lemma A.3, from Surf to PyCore, computable.

It is a homomorphism on control flow: conditional and Boolean expressions, `while`
with `else`, `break`, `continue`, and `try` with several handlers and `else` are
PyCore's own. It keeps every scope: a `def`, a lambda, and a comprehension become a
PyCore lambda (whose body is a block) in place, a class a class.

A translated program asks the interpretation for exactly what the Surf program asks
(Surf/Semantics.lean), in the same order, and allocates the same objects in the same
order: every operation is a call of a constant `$op:…` on an argument record (`$args`
extended by `,`), and what Surf's core does itself is a call of a core gadget
(`Py.Gadget`).

Locality. Everything the translation takes from a Surf node lives in PyCore nodes made
for that node (labelled `sub l k`), and what a parent's gadget needs to know about a
child at run time (starred or not, a keyword's name, constness, a parameter's name,
kind and default) is the child's own marker node (`Py.isMarker`), which the gadget
reads when it runs: a parent's nodes depend only on the parent's own fields. A
subterm of what CPython rejects is kept in a branch that never runs (`if $false:`).

Every Surf statement becomes one PyCore statement (several are grouped in a `try`
with no handler and no `else`, which runs them in order and passes everything); every
module and class body starts with `SETUP_ANNOTATIONS`, every function body with a
branch that never runs and binds each parameter. The root of the translation of the
Surf node labelled `l` is labelled `sub l 0`, every other node made for it `sub l k`
(`k < 64`: `k < 46` for its own nodes, `k ≥ 46` for those made for it in its parent's
place: 50 a set item's part's constness marker, 54 the dead branch and 55 the stop of a
target CPython rejects, 56 a parameter's marker, 57 an item's or argument's marker, 58 an
annotation's store, 59 and 61 an unpacked item, 60 a bare annotated target's binding, 62 a
bare annotated target's parts, 63 a target's source), and a fresh name made for it
is `.tag l`; the module's `SETUP_ANNOTATIONS` is labelled below 64, which no Surf node's
translation uses (the exporter labels Surf nodes from 1).
-/
import Surf.Syntax

namespace Surf
open PyCore (Name Label)
open Py (Gadget)

abbrev PS := List PyCore.Stmt
abbrev PE := PyCore.Expr

/-- The `k`-th node the translation makes for the Surf node labelled `l`. -/
def sub (l : Label) (k : Nat) : Label := 64 * l + k

/-- A fresh name for the Surf node labelled `l`. -/
def fresh (tag : String) (l : Label) : Name := "." ++ tag ++ toString l

def IsFresh (x : Name) : Prop := ∃ tag l, x = fresh tag l

/-- The argument record of `es`, labelled `r`: `$args` extended by each. -/
def recR (r : Label) (es : List PE) : PE :=
  es.foldl (fun acc e => .bin r "," acc e) (.const r "$args")

/-- A call, labelled `r`, of the core constant `g` (an operation `$op:…` or a gadget's name)
on the record of `es`. -/
def ccR (r : Label) (g : String) (es : List PE) : PE := .call r (.const r g) (recR r es)

def cc (l : Label) (k : Nat) (g : String) (es : List PE) : PE := ccR (sub l k) g es

def gad (l : Label) (k : Nat) (g : Gadget) (es : List PE) : PE := cc l k g.name es

/-- A read of a fresh name. -/
def nm (l : Label) (k : Nat) (x : Name) : PE := .name (sub l k) x none

/-- Several statements as one: a `try` with no handler and no `else`. -/
def blk (l : Label) (ss : PS) : PyCore.Stmt := .tryE (sub l 0) ss [] []

/-- A statement that cannot step, labelled `r`, for what CPython's compiler rejects. -/
def stuckAt (r : Label) : PyCore.Stmt := .expr r (ccR r Gadget.stuck.name [])

/-- A branch that never runs, labelled `r`. -/
def dead (r : Label) (ss : PS) : PyCore.Stmt := .ite r (.const r "$false") ss []

/-- The source of a store that never runs. -/
def deadSrc (lt : Label) : PE := .const (sub lt 63) "$none"

/-- The scope at the head of the chain runs as a module or class body. -/
def isTop : List Scope → Bool
  | [] | .cl .. :: _ => true
  | _ => false

/-- A parameter's marker, its name mangled in its function's chain `C`. -/
def paramMark (C : List Scope) (q : Param) : PE :=
  .const (sub q.label 56) (Py.paramMarker (mangle (priv C) q.name) q.kind.pk q.dflt.isSome)

/-- The start of a function body (in its own chain `C`): for each parameter, a branch
that never runs and binds it, labelled by the parameter. -/
def paramBind (C : List Scope) (ps : List Param) : PS :=
  ps.map fun q => dead (sub q.label 2)
    [.assign (sub q.label 0) (mangle (priv C) q.name) (.const (sub q.label 1) "$none")]

/-- `SETUP_ANNOTATIONS`, for the module (`l = 0`) or the class node `l`. -/
def setupS (l : Label) : PyCore.Stmt := .expr (sub l 4) (gad l 5 .setup [cc l 6 "$op:display:dict:" []])

/-- An item's or a positional argument's marker: starred or not. -/
def starMark : Expr → PE
  | .star l _ => .const (sub l 57) "$star"
  | e => .const (sub e.label 57) "$pos"

/-- A keyword argument's marker. -/
def kwMark : Kw → PE
  | .mk l x _ => .const (sub l 57) (Py.kwMarker x)

mutual
/-- A set item's marker: starred, or its constness (CPython folds a constant, a sign of one,
and a tuple of constants), computed by the core from the item's parts' markers. -/
def constMark (k : Nat) : Expr → PE
  | .const l _ => .const (sub l k) "$c0"
  | .unary l op a => ccR (sub l k) (Gadget.cunary op).name [constMark 50 a]
  | .tuple l es => ccR (sub l k) Gadget.ctuple.name (constMarks es)
  | .star l _ => .const (sub l k) "$star"
  | e => .const (sub e.label k) "$nc"
/-- The markers of a set item's parts (`k = 50`, apart from their own item markers, 57). -/
def constMarks : List Expr → List PE
  | [] => []
  | e :: es => constMark 50 e :: constMarks es
end

/-- The item `i` of the unpacked tuple `.u l`, as the source of the element target `lt`. -/
def itemSrc (l : Label) (i : Nat) (lt : Label) : PE :=
  ccR (sub lt 59) (Gadget.item i).name [.name (sub lt 61) (fresh "u" l) none]

/-- The inner `and`s (`or`s) of `a and b and c …`, the parent's nodes. -/
def boolChainIn (l : Label) (o : Bool) : List PE → PE
  | [] => gad l 1 .stuck []
  | [a] => a
  | a :: b :: rest => .bool (sub l 1) o a (boolChainIn l o (b :: rest))

/-- `a and b and c` as `a and (b and c)`. -/
def boolChain (l : Label) (o : Bool) : List PE → PE
  | [] => gad l 0 .stuck []
  | [a] => a
  | a :: b :: rest => .bool (sub l 0) o a (boolChainIn l o (b :: rest))

/-- `a op₁ b op₂ c …` as `a op₁ b and b op₂ c …`, each middle operand `b` (labelled `lb`)
evaluated once and kept in the frame's own cell `.c lb`; the nodes are the parent's
(`r` the root). -/
def cmpChain (l : Label) (r : Label) (left : PE) : List (String × Label × PE) → PE
  | [] => ccR r Gadget.stuck.name [left]
  | [(op, _, b)] => .bin r op left b
  | (op, lb, b) :: rest =>
    .bool r true (.bin (sub l 2) op left (gad l 3 (.set (fresh "c" lb)) [b]))
      (cmpChain l (sub l 1) (gad l 4 (.get (fresh "c" lb)) []) rest)

/-- The operators of a chained comparison with its operands (`?` where missing). -/
def cmpOps : List String → List (Label × PE) → List (String × Label × PE)
  | _, [] => []
  | ops, (lb, b) :: rest => (ops.headD "?", lb, b) :: cmpOps ops.tail rest

/-- `if c₁ if c₂ …: body` of the generator `lg` as nested `if`s. -/
def ifsNest (lg : Label) : List PE → PS → PS
  | [], body => body
  | c :: cs, body => [.ite (sub lg 3) c (ifsNest lg cs body) []]

/-- `for t in i` over the iterator in `iv`: `next` alone under the handler, the
target stored after it (`store`), then `body`; `.g` turns false when the iterator
is exhausted, so the loop's `else` runs then and not after a `break`. -/
def forLoop (l : Label) (iv : Name) (store body u : PS) : PS :=
  [.assign (sub l 10) (fresh "g" l) (.const (sub l 11) "$true"),
   .while (sub l 12) (.name (sub l 13) (fresh "g" l) none)
     [.tryE (sub l 14)
       [.assign (sub l 15) (fresh "v" l)
         (.call (sub l 16) (.const (sub l 17) "$next") (.name (sub l 18) iv none))]
       [.mk (sub l 19) (.const (sub l 20) "$stop") (fresh "s" l)
         [.assign (sub l 21) (fresh "g" l) (.const (sub l 22) "$false")]]
       (store ++ body)] u]

/-- The value a target labelled `lt` receives in a `for` loop over `l`. -/
def forSrc (l : Label) (lt : Label) : PE := .name (sub lt 63) (fresh "v" l) none

/-- The value a target labelled `lt` receives from the fresh name `.tag l`. -/
def nameSrc (tag : String) (l : Label) (lt : Label) : PE := .name (sub lt 63) (fresh tag l) none

def accName : CompKind → String
  | .set => "set" | .dict => "dict" | _ => "list"

/-- A comprehension's element (its values `es` translated): yielded by a generator
expression, else added to the accumulator `.acc`. -/
def compElt (l : Label) (k : CompKind) (es : List PE) : PS :=
  let acc := fresh "acc" l
  match k, es with
  | .gen, [e] => [.expr (sub l 9) (.yield (sub l 10) e)]
  | .list, [e] => [.expr (sub l 9) (cc l 10 "$op:accum:list" [nm l 8 acc, e])]
  | .set, [e] => [.expr (sub l 9) (cc l 10 "$op:accum:set" [nm l 8 acc, e])]
  | .dict, [kk, v] => [.expr (sub l 9) (cc l 10 "$op:accum:dict" [nm l 8 acc, kk, v])]
  | _, es => [stuckAt (sub l 9), dead (sub l 11) (es.map (.expr (sub l 11)))]

/-- A comprehension's body around its loops: for a list, set or dictionary
comprehension, the accumulator made first and returned last. -/
def compWrap (l : Label) (k : CompKind) (loops : PS) : PS :=
  if k = .gen then loops
  else .assign (sub l 4) (fresh "acc" l) (cc l 5 ("$op:display:" ++ accName k ++ ":") []) :: loops ++
    [.ret (sub l 7) (nm l 6 (fresh "acc" l))]

/-- The store of `x: A` at module or class level, the annotation's value in `.n l`: for a
name, into `__annotations__`; otherwise it is dropped (a statement that does nothing, so
that every target has its node here). Nodes made for the target. -/
def annT (C : List Scope) (l : Label) (t : Expr) : PS :=
  match t with
  | .name lt x =>
    [.expr (sub lt 58) (ccR (sub lt 58) (Gadget.annot (mangle (priv C) x)).name [nm l 7 (fresh "n" l)])]
  | t => [.expr (sub t.label 58) (.const (sub t.label 58) "$none")]

/-- A bare annotated name is bound (in the statement's branch that never runs; any other
target leaves a statement that does nothing); nodes made for the target. -/
def annBind (C : List Scope) : Expr → PS
  | .name lt x => [.assign (sub lt 60) (mangle (priv C) x) (.const (sub lt 60) "$none")]
  | t => [.expr (sub t.label 60) (.const (sub t.label 60) "$none")]

mutual
/-- An expression's value. -/
def trE (C : List Scope) : Expr → PE
  | .const l c => .const (sub l 0) c
  | .name l x => .name (sub l 0) (mangle (priv C) x) none
  | .bin l op a b => .bin (sub l 0) op (trE C a) (trE C b)
  | .unary l op a => cc l 0 ("$op:unop:" ++ op) [trE C a]
  | .boolop l op es => boolChain l (op == "And") (trEs C es)
  | .compare l a ops es => cmpChain l (sub l 0) (trE C a) (cmpOps ops (trLs C es))
  | .ifexp l c a b => .cond (sub l 0) (trE C c) (trE C a) (trE C b)
  | .call l f args kws =>
    gad l 0 .call (trE C f :: trA C args ++ trKs C kws ++ args.map starMark ++ kws.map kwMark)
  | .attr l e a => cc l 0 ("$op:getattr:" ++ mangle (priv C) a) [trE C e]
  | .sub l e i => cc l 0 "$op:getitem" [trE C e, trE C i]
  | .slice l a b c => cc l 0 "$op:display:slice" [trO C l 1 a, trO C l 2 b, trO C l 3 c]
  | .star l e => .cond (sub l 0) (.const (sub l 1) "$false") (trE C e) (gad l 2 .stuck [])
  | .list l es => gad l 0 (.display "list") (trA C es ++ es.map starMark)
  | .tuple l es => gad l 0 (.display "tuple") (trA C es ++ es.map starMark)
  | .set l es => gad l 0 (.display "set") (trA C es ++ es.map (constMark 57))
  | .dict l kvs =>
    cc l 0 ("$op:display:dict:" ++ Py.starsStr (kvs.map fun | .mk k _ => k.isNone)) (trKVs C kvs)
  | .lam l ps b =>
    gad l 0 (.defn 0 ps.length) (trDfs C ps ++
      [.cond (sub l 3) (.const (sub l 3) "$false") (recR (sub l 3) (trAnns C ps)) (.const (sub l 3) "$none")] ++
      ps.map (paramMark (.lam l ps b :: C)) ++
      [.lam (sub l 1) false (fresh "a" l)
        (paramBind (.lam l ps b :: C) ps ++ [.ret (sub l 2) (trE (.lam l ps b :: C) b)])])
  | .comp l k es gs =>
    if gs.isEmpty then
      .cond (sub l 0) (.const (sub l 11) "$false")
        (.call (sub l 12) (.lam (sub l 1) true (fresh "i" l) (compWrap l k
            (trGs (.comp l k es gs :: C) (fresh "i" l) true gs (compElt l k (trEs (.comp l k es gs :: C) es)))))
          (.const (sub l 13) "$none"))
        (gad l 14 .stuck [])
    else
      .call (sub l 0) (.lam (sub l 1) true (fresh "i" l) (compWrap l k
          (trGs (.comp l k es gs :: C) (fresh "i" l) true gs (compElt l k (trEs (.comp l k es gs :: C) es)))))
        (cc l 3 "$op:iter" [trG1 C gs])
  | .walrus l x e => .walrus (sub l 0) (mangle (priv C) x) (trE C e)
  | .yield l e => .yield (sub l 0) (trO C l 1 e)
  | .yieldFrom l e => .yieldFrom (sub l 0) (trE C e)
  | .fstr l es => cc l 0 "$op:display:fstr" (trEs C es)
  | .fmt l e conv s =>
    let v := if conv == -1 then trE C e else cc l 1 ("$op:convert:" ++ toString conv) [trE C e]
    cc l 0 "$op:format" (match s with
      | some s => [v, trE C s]
      | none => [v])
/-- An optional expression, `None` (the core's) if absent, labelled `sub l k`. -/
def trO (C : List Scope) (l : Label) (k : Nat) : Option Expr → PE
  | none => .const (sub l k) "$none"
  | some e => trE C e
def trEs (C : List Scope) : List Expr → List PE
  | [] => []
  | e :: es => trE C e :: trEs C es
/-- The items of a display or the positional arguments of a call: a starred one gives its
operand (the display or call expands it; its marker says so). -/
def trA (C : List Scope) : List Expr → List PE
  | [] => []
  | .star _ e :: es => trE C e :: trA C es
  | e :: es => trE C e :: trA C es
/-- The values of keyword arguments. -/
def trKs (C : List Scope) : List Kw → List PE
  | [] => []
  | .mk _ _ e :: ks => trE C e :: trKs C ks
/-- Loads, each with its node's label. -/
def trLs (C : List Scope) : List Expr → List (Label × PE)
  | [] => []
  | e :: es => (e.label, trE C e) :: trLs C es
/-- A dictionary display's keys and values, in order (`**m` gives `m` alone). -/
def trKVs (C : List Scope) : List DItem → List PE
  | [] => []
  | .mk (some k) v :: kvs => trE C k :: trE C v :: trKVs C kvs
  | .mk none v :: kvs => trE C v :: trKVs C kvs
/-- The defaults, which the scope around a function evaluates. -/
def trDfs (C : List Scope) : List Param → List PE
  | [] => []
  | .mk _ _ _ (some d) _ :: ps => trE C d :: trDfs C ps
  | .mk _ _ _ none _ :: ps => trDfs C ps
/-- The annotations of the parameters of kind `k`, in order. -/
def trAnnK (C : List Scope) (k : PKind) : List Param → List PE
  | [] => []
  | .mk _ _ k' _ (some a) :: ps => if k' = k then trE C a :: trAnnK C k ps else trAnnK C k ps
  | .mk _ _ _ _ none :: ps => trAnnK C k ps
/-- All the parameters' annotations, in order (a lambda's, which CPython's parser rejects,
go in a branch that never runs). -/
def trAnns (C : List Scope) : List Param → List PE
  | [] => []
  | .mk _ _ _ _ (some a) :: ps => trE C a :: trAnns C ps
  | .mk _ _ _ _ none :: ps => trAnns C ps
/-- The first iterable, which the scope around a comprehension evaluates. -/
def trG1 (C : List Scope) : List Gen → PE
  | [] => .const 0 "$none"
  | .mk _ _ i _ :: _ => trE C i
/-- A comprehension's generators as nested loops around `inner`, in its own scope;
the first draws from the parameter `it`, each later one from a fresh iterator. -/
def trGs (C : List Scope) (it : Name) (first : Bool) : List Gen → PS → PS
  | [], inner => inner
  | .mk lg t i ifs :: gs, inner =>
    let iv := if first then it else fresh "j" lg
    (if first then [] else [.assign (sub lg 0) iv (cc lg 1 "$op:iter" [trE C i])]) ++
    forLoop lg iv (trT C (forSrc lg) t (trE C t)) (ifsNest lg (trEs C ifs) (trGs C it false gs inner)) []
/-- The store of the value `src lt` into the target `t` (labelled `lt`): the source is a
node made for the target. `tE` is the target's value, kept in a branch that never runs
if it is no target. -/
def trT (C : List Scope) (src : Label → PE) (t : Expr) (tE : PE) : PS :=
  match t with
  | .name lt x => [.assign (sub lt 0) (mangle (priv C) x) (src lt)]
  | .attr lt o a => [.expr (sub lt 0) (cc lt 1 ("$op:setattr:" ++ mangle (priv C) a) [trE C o, src lt])]
  | .sub lt o i => [.expr (sub lt 0) (cc lt 1 "$op:setitem" [trE C o, trE C i, src lt])]
  | .tuple lt ts =>
    [blk lt (.assign (sub lt 1) (fresh "u" lt) (gad lt 2 .unpack (src lt :: trMarks ts)) ::
      trItems C lt 0 ts)]
  | .list lt ts =>
    [blk lt (.assign (sub lt 1) (fresh "u" lt) (gad lt 2 .unpack (src lt :: trMarks ts)) ::
      trItems C lt 0 ts)]
  | .star ls e => [stuckAt (sub ls 55), dead (sub ls 54) (trT C src e (trE C e))]
  | t => [stuckAt (sub t.label 55), dead (sub t.label 54) [.expr (sub t.label 54) tE]]
/-- The targets' markers, which give an unpacking its shape. -/
def trMarks : List Expr → List PE
  | [] => []
  | t :: ts => starMark t :: trMarks ts
def trItems (C : List Scope) (lt : Label) (i : Nat) : List Expr → PS
  | [] => []
  | .star _ t :: ts => trT C (itemSrc lt i) t (trE C t) ++ trItems C lt (i + 1) ts
  | t :: ts => trT C (itemSrc lt i) t (trE C t) ++ trItems C lt (i + 1) ts
/-- Stores of the value `src lt` into each of `ts`, in order. -/
def trTs (C : List Scope) (src : Label → PE) : List Expr → PS
  | [] => []
  | t :: ts => trT C src t (trE C t) ++ trTs C src ts
/-- `del t`; `tD` is the store into it, kept in a branch that never runs if it is no target. -/
def trD (C : List Scope) (t : Expr) (tD : PS) : PS :=
  match t with
  | .name lt x => [.del (sub lt 0) (mangle (priv C) x)]
  | .attr lt o a => [.expr (sub lt 0) (cc lt 1 ("$op:delattr:" ++ mangle (priv C) a) [trE C o])]
  | .sub lt o i => [.expr (sub lt 0) (cc lt 1 "$op:delitem" [trE C o, trE C i])]
  | .tuple lt ts => [blk lt (trDs C ts)]
  | .list lt ts => [blk lt (trDs C ts)]
  | t => [stuckAt (sub t.label 55), dead (sub t.label 54) tD]
def trDs (C : List Scope) : List Expr → PS
  | [] => []
  | t :: ts => trD C t (trT C deadSrc t (trE C t)) ++ trDs C ts
/-- An augmented assignment's reading of its target `t` (its parts into `.o l`, `.k l`, its
value into `.g l`) and its store of `.v l`; nodes made for the target. `tT` is the store
into it, kept in a branch that never runs if it is no augmented target. -/
def trAug (C : List Scope) (l : Label) (t : Expr) (tT : PS) : PS × PS :=
  match t with
  | .name lt x =>
    ([.assign (sub lt 0) (fresh "g" l) (.name (sub lt 1) (mangle (priv C) x) none)],
     [.assign (sub lt 2) (mangle (priv C) x) (nm lt 3 (fresh "v" l))])
  | .attr lt o a =>
    ([.assign (sub lt 4) (fresh "o" l) (trE C o),
      .assign (sub lt 5) (fresh "g" l)
        (cc lt 6 ("$op:getattr:" ++ mangle (priv C) a) [nm lt 7 (fresh "o" l)])],
     [.expr (sub lt 2) (cc lt 9 ("$op:setattr:" ++ mangle (priv C) a)
        [nm lt 10 (fresh "o" l), nm lt 11 (fresh "v" l)])])
  | .sub lt o i =>
    ([.assign (sub lt 4) (fresh "o" l) (trE C o),
      .assign (sub lt 5) (fresh "k" l) (trE C i),
      .assign (sub lt 6) (fresh "g" l)
        (cc lt 7 "$op:getitem" [nm lt 8 (fresh "o" l), nm lt 9 (fresh "k" l)])],
     [.expr (sub lt 2) (cc lt 10 "$op:setitem"
        [nm lt 11 (fresh "o" l), nm lt 12 (fresh "k" l), nm lt 13 (fresh "v" l)])])
  | t => ([stuckAt (sub t.label 55), dead (sub t.label 54) tT], [])
/-- A bare annotated target `t: A` (no value): an attribute's or subscript's parts are
evaluated, a name leaves a statement that does nothing; nodes made for the target. `tT` is the store into it, kept in a branch that never
runs if it is no name, attribute or subscript. -/
def annBare (C : List Scope) (t : Expr) (tT : PS) : PS :=
  match t with
  | .name lt _ => [.expr (sub lt 62) (.const (sub lt 62) "$none")]
  | .attr lt o _ => [.expr (sub lt 62) (trE C o)]
  | .sub lt o i => [.expr (sub lt 62) (recR (sub lt 62) [trE C o, trE C i])]
  | t => [stuckAt (sub t.label 55), dead (sub t.label 54) tT]
/-- One PyCore statement for each Surf statement. -/
def trS (C : List Scope) : Stmt → PyCore.Stmt
  | .expr l e => .expr (sub l 0) (trE C e)
  | .assign l ts e => blk l (.assign (sub l 1) (fresh "t" l) (trE C e) :: trTs C (nameSrc "t" l) ts)
  | .augassign l t op e =>
    let p := trAug C l t (trT C deadSrc t (trE C t))
    blk l (p.1 ++ [.assign (sub l 1) (fresh "v" l)
      (.bin (sub l 2) (op ++ "=") (nm l 3 (fresh "g" l)) (trE C e))] ++ p.2)
  | .annassign l t a v =>
    -- at module or class level the annotation's value goes into `.n l`, then the target
    -- stores its key; in a function it is not evaluated (a branch that never runs)
    let ann : PS := if isTop C then .assign (sub l 6) (fresh "n" l) (trE C a) :: annT C l t
      else [dead (sub l 6) [.expr (sub l 8) (trE C a)]]
    match v with
    | some e => blk l (.assign (sub l 1) (fresh "t" l) (trE C e) :: trT C (nameSrc "t" l) t (trE C t) ++ ann)
    | none => blk l (annBare C t (trT C deadSrc t (trE C t)) ++ ann ++ [dead (sub l 9) (annBind C t)])
  | .del l ts => blk l (trDs C ts)
  | .ite l c t u => .ite (sub l 0) (trE C c) (trB C t) (trB C u)
  | .while l c b u => .while (sub l 0) (trE C c) (trB C b) (trB C u)
  | .for l t it b u =>
    blk l (.assign (sub l 1) (fresh "i" l) (cc l 2 "$op:iter" [trE C it]) ::
      forLoop l (fresh "i" l) (trT C (forSrc l) t (trE C t)) (trB C b) (trB C u))
  | .brk l => .brk (sub l 0)
  | .cont l => .cont (sub l 0)
  | .pass l => .expr (sub l 0) (.const (sub l 1) "$none")
  | .ret l e => .ret (sub l 0) (trO C l 1 e)
  | .defn l f ps b ds r =>
    .assign (sub l 0) (mangle (priv C) f)
      (gad l 2 (.defn ds.length ps.length)
        (trEs C ds ++ trDfs C ps ++ trAnnK C .pos ps ++ trAnnK C .posonly ps ++ trAnnK C .vararg ps ++
          trAnnK C .kwonly ps ++ trAnnK C .kwarg ps ++ (match r with | some r => [trE C r] | none => []) ++
          ps.map (paramMark (.fn l f ps b :: C)) ++
          [.lam (sub l 1) false (fresh "a" l)
            (paramBind (.fn l f ps b :: C) ps ++ trB (.fn l f ps b :: C) b)]))
  | .cls l x bs ks b ds =>
    blk l [.expr (sub l 2) (gad l 3 (.cls ds.length)
             (trEs C ds ++ trA C bs ++ trKs C ks ++ bs.map starMark ++ ks.map kwMark)),
           .cls (sub l 1) (mangle (priv C) x) (qualIn C x) (setupS l :: trB (.cl l x b :: C) b)]
  | .glob l xs => blk l (xs.map fun x => .glob (sub l 1) (mangle (priv C) x))
  | .nonloc l xs => blk l (xs.map fun x => .nonloc (sub l 1) (mangle (priv C) x))
  | .tryE l b hs u => .tryE (sub l 0) (trB C b) (trHs C hs) (trB C u)
  | .raise l none none => .expr (sub l 0) (gad l 1 .reraise [])
  | .raise l (some e) none => .raise (sub l 0) (trE C e)
  | .raise l (some e) (some c) => .expr (sub l 0) (gad l 1 .raiseFrom [trE C e, trE C c])
  | .raise l none (some c) => blk l [stuckAt (sub l 1), dead (sub l 2) [.expr (sub l 2) (trE C c)]]
  | .imp l al =>
    blk l (al.map fun a =>
      if a.name == "*" then stuckAt (sub a.l 0)
      else .assign (sub a.l 0) (mangle (priv C) a.bound)
        (cc a.l 1 s!"$op:import:{a.name}:{if a.asname.isSome then 1 else 0}" []))
  | .impFrom l m al lvl =>
    if lvl > 0 then
      blk l [.expr (sub l 1) (gad l 2 (.raiseK "ImportError") []),
             dead (sub l 3) ((bindingAliases al).map fun a =>
                 .assign (sub a.l 0) (mangle (priv C) a.bound) (.const (sub a.l 1) "$none"))]
    else
      blk l (.assign (sub l 1) (fresh "m" l) (cc l 2 s!"$op:import:{m.getD ""}:1" []) ::
        al.map fun a =>
          if a.name == "*" then
            .expr (sub a.l 0) (gad a.l 1 .starstore [cc a.l 2 "$op:importStar" [nm a.l 3 (fresh "m" l)]])
          else .assign (sub a.l 0) (mangle (priv C) a.bound)
            (cc a.l 1 ("$op:importFrom:" ++ a.name) [nm a.l 3 (fresh "m" l)]))
  | .assert l t m =>
    .ite (sub l 0) (trE C t) []
      [.expr (sub l 1) (gad l 2 (.raiseK "AssertionError") (match m with | some m => [trE C m] | none => []))]
def trHs (C : List Scope) : List Handler → List PyCore.Handler
  | [] => []
  | .mk l ty x b :: hs =>
    .mk (sub l 0) (match ty with | some t => trE C t | none => .const (sub l 1) "$any")
      ((x.map (mangle (priv C))).getD (fresh "e" l)) (trB C b) :: trHs C hs
def trB (C : List Scope) : List Stmt → PS
  | [] => []
  | s :: ss => trS C s :: trB C ss
end

/-- ⌊p⌋ for a module `p`. -/
def tr (p : List Stmt) : PS := setupS 0 :: trB [] p

/-- The PyCore scope a Surf scope (in the chain `C`) becomes. -/
def trScope (C : List Scope) : Scope → PyCore.Scope
  | .fn l f ps b => .fn (sub l 1) false (fresh "a" l) (paramBind (.fn l f ps b :: C) ps ++ trB (.fn l f ps b :: C) b)
  | .lam l ps b =>
    .fn (sub l 1) false (fresh "a" l) (paramBind (.lam l ps b :: C) ps ++ [.ret (sub l 2) (trE (.lam l ps b :: C) b)])
  | .cl l x b => .cl (sub l 1) (setupS l :: trB (.cl l x b :: C) b)
  | .comp l k es gs => .fn (sub l 1) true (fresh "i" l) (compWrap l k
      (trGs (.comp l k es gs :: C) (fresh "i" l) true gs (compElt l k (trEs (.comp l k es gs :: C) es))))

def trChain : List Scope → List PyCore.Scope
  | [] => []
  | S :: C => trScope C S :: trChain C

end Surf
