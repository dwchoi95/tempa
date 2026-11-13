/-
(T1) The translation maps each scope to a scope, keeps the classification of each
occurrence of a name and the kind of each function, and adds only fresh names.

The own body of every PyCore scope of ⌊p⌋ agrees with that of its Surf scope on
every name that is not fresh (`scope_facts`), so the classifications agree on
every chain (`cls_tr`) and the kinds agree (`kind_tr`); and the occurrences and
functions of ⌊p⌋ are, up to fresh names, the images of those of `p` (`items_tr`).
What CPython's parser rejects is kept in branches that never run, which the analysis
visits like any other code, so no grammar condition is needed but one: a generator
expression has one element (CPython's `GeneratorExp` has one `elt`), else ⌊·⌋ does not
yield there (`GenOk`, for the kinds only).
-/
import Surf.Footprint

namespace Surf
open PyCore (Name Label Fact Cls Kind)

/-! ## Lemmas on PyCore's analysis -/

@[simp] theorem enone_e (l : Label) : PyCore.Edit.none.e l = none := rfl
@[simp] theorem enone_s (l : Label) : PyCore.Edit.none.s l = none := rfl
@[simp] theorem enone_h (l : Label) : PyCore.Edit.none.h l = none := rfl

@[simp] theorem dflt_mk (l x k d a) : (Param.mk l x k d a).dflt = d := rfl
@[simp] theorem ann_mk (l x k d a) : (Param.mk l x k d a).ann = a := rfl
@[simp] theorem kind_mk (l x k d a) : (Param.mk l x k d a).kind = k := rfl
@[simp] theorem label_mk (l x k d a) : (Param.mk l x k d a).label = l := rfl
@[simp] theorem name_mk (l x k d a) : (Param.mk l x k d a).name = x := rfl

section
variable {R : PyCore.Edit}

theorem pfactsB_append : ∀ a b : List PyCore.Stmt, PyCore.factsB (a ++ b) = PyCore.factsB a ++ PyCore.factsB b
  | [], _ => rfl
  | s :: a, b => by simp [PyCore.factsB, pfactsB_append a b]

theorem pitemsB_append (C) : ∀ a b : List PyCore.Stmt,
    PyCore.itemsB R C (a ++ b) = PyCore.itemsB R C a ++ PyCore.itemsB R C b
  | [], _ => rfl
  | s :: a, b => by simp [PyCore.itemsB, pitemsB_append C a b]

theorem pfactsB_map {α} (f : α → PyCore.Stmt) : ∀ xs : List α,
    PyCore.factsB (xs.map f) = xs.flatMap fun x => PyCore.factsS (f x)
  | [] => rfl
  | x :: xs => by simp [PyCore.factsB, pfactsB_map f xs]

theorem pitemsB_map {α} (C : List PyCore.Scope) (f : α → PyCore.Stmt) : ∀ xs : List α,
    PyCore.itemsB R C (xs.map f) = xs.flatMap fun x => PyCore.itemsS R C (f x)
  | [] => rfl
  | x :: xs => by simp [PyCore.itemsB, pitemsB_map C f xs]

end

theorem pfactsE_foldl (l : Label) : ∀ (es : List PyCore.Expr) (acc : PyCore.Expr),
    PyCore.factsE (es.foldl (fun acc e => .bin l "," acc e) acc) =
      PyCore.factsE acc ++ es.flatMap PyCore.factsE
  | [], _ => by simp
  | e :: es, acc => by simp [pfactsE_foldl l es, PyCore.factsE]

theorem pitemsE_foldl (C) (l : Label) : ∀ (es : List PyCore.Expr) (acc : PyCore.Expr),
    PyCore.itemsE R0 C (es.foldl (fun acc e => .bin l "," acc e) acc) =
      PyCore.itemsE R0 C acc ++ es.flatMap (PyCore.itemsE R0 C)
  | [], _ => by simp
  | e :: es, acc => by simp [pitemsE_foldl C l es, PyCore.itemsE]

@[simp] theorem pfactsE_recR (r : Label) (es : List PE) : PyCore.factsE (recR r es) = es.flatMap PyCore.factsE := by
  simp [recR, pfactsE_foldl, PyCore.factsE]
@[simp] theorem pfactsE_ccR (r : Label) (g : String) (es : List PE) :
    PyCore.factsE (ccR r g es) = es.flatMap PyCore.factsE := by
  simp [ccR, PyCore.factsE]
@[simp] theorem pfactsE_cc (l : Label) (k : Nat) (g : String) (es : List PE) :
    PyCore.factsE (cc l k g es) = es.flatMap PyCore.factsE := pfactsE_ccR ..
@[simp] theorem pfactsE_gad (l : Label) (k : Nat) (g : Py.Gadget) (es : List PE) :
    PyCore.factsE (gad l k g es) = es.flatMap PyCore.factsE := pfactsE_ccR ..
@[simp] theorem flatMap_nil_fun {α β} (xs : List α) : xs.flatMap (fun _ => ([] : List β)) = [] := by
  induction xs <;> simp_all
@[simp] theorem pitemsE_recR (C) (r : Label) (es : List PE) :
    PyCore.itemsE R0 C (recR r es) = es.flatMap (PyCore.itemsE R0 C) := by
  simp [recR, pitemsE_foldl, PyCore.itemsE]
@[simp] theorem pitemsE_ccR (C) (r : Label) (g : String) (es : List PE) :
    PyCore.itemsE R0 C (ccR r g es) = es.flatMap (PyCore.itemsE R0 C) := by
  simp [ccR, PyCore.itemsE]

/-! Markers name nothing. -/

@[simp] theorem pfactsE_starMark (e : Expr) : PyCore.factsE (starMark e) = [] := by
  cases e <;> rfl
@[simp] theorem pfactsE_kwMark (k : Kw) : PyCore.factsE (kwMark k) = [] := by
  cases k; rfl
@[simp] theorem pfactsE_paramMark (C : List Scope) (q : Param) : PyCore.factsE (paramMark C q) = [] := rfl
@[simp] theorem pitemsE_starMark (C) (e : Expr) : PyCore.itemsE R0 C (starMark e) = [] := by
  cases e <;> rfl
@[simp] theorem pitemsE_kwMark (C) (k : Kw) : PyCore.itemsE R0 C (kwMark k) = [] := by
  cases k; rfl
@[simp] theorem pitemsE_paramMark (C) (D : List Scope) (q : Param) : PyCore.itemsE R0 C (paramMark D q) = [] := rfl

mutual
theorem pfactsE_constMark (k : Nat) : ∀ e : Expr, PyCore.factsE (constMark k e) = []
  | .const .. => rfl
  | .unary _ _ a => by simp [constMark, pfactsE_constMark 50 a]
  | .tuple _ es => by simp [constMark, pfactsE_constMarks es]
  | .star .. => rfl
  | .name .. | .bin .. | .boolop .. | .compare .. | .ifexp .. | .call .. | .attr .. | .sub ..
  | .slice .. | .list .. | .set .. | .dict .. | .lam .. | .comp .. | .walrus .. | .yield ..
  | .yieldFrom .. | .fstr .. | .fmt .. => rfl
theorem pfactsE_constMarks : ∀ es : List Expr, (constMarks es).flatMap PyCore.factsE = []
  | [] => rfl
  | e :: es => by simp [constMarks, pfactsE_constMark 50 e, pfactsE_constMarks es]
end
attribute [simp] pfactsE_constMark pfactsE_constMarks

mutual
theorem pitemsE_constMark (C) (k : Nat) : ∀ e : Expr, PyCore.itemsE R0 C (constMark k e) = []
  | .const .. => rfl
  | .unary _ _ a => by simp [constMark, pitemsE_constMark C 50 a]
  | .tuple _ es => by simp [constMark, pitemsE_constMarks C es]
  | .star .. => rfl
  | .name .. | .bin .. | .boolop .. | .compare .. | .ifexp .. | .call .. | .attr .. | .sub ..
  | .slice .. | .list .. | .set .. | .dict .. | .lam .. | .comp .. | .walrus .. | .yield ..
  | .yieldFrom .. | .fstr .. | .fmt .. => rfl
theorem pitemsE_constMarks (C) : ∀ es : List Expr, (constMarks es).flatMap (PyCore.itemsE R0 C) = []
  | [] => rfl
  | e :: es => by simp [constMarks, pitemsE_constMark C 50 e, pitemsE_constMarks C es]
end
attribute [simp] pitemsE_constMark pitemsE_constMarks

@[simp] theorem pfactsE_marks (C : List Scope) (ps : List Param) :
    (ps.map (paramMark C)).flatMap PyCore.factsE = [] := by simp
@[simp] theorem pitemsE_marks (D) (C : List Scope) (ps : List Param) :
    (ps.map (paramMark C)).flatMap (PyCore.itemsE R0 D) = [] := by simp

theorem constMarks_eq : ∀ es : List Expr, constMarks es = es.map (constMark 50)
  | [] => rfl
  | e :: es => by simp [constMarks, constMarks_eq es]

theorem trMarks_eq : ∀ ts : List Expr, trMarks ts = ts.map starMark
  | [] => rfl
  | t :: ts => by simp [trMarks, trMarks_eq ts]

/-! ## Own bodies -/

/-- A fact about a name that is not fresh, or `yield`. -/
def NF : Fact → Prop
  | .bind x | .wal x | .glob x | .nonloc x => ¬ IsFresh x
  | .yld => True

/-- Two lists of facts that agree on every fact `NF` admits. -/
def FEq (A B : List Fact) : Prop := ∀ f, NF f → (f ∈ A ↔ f ∈ B)

theorem ne_fresh {f : Fact} (hf : NF f) (t : String) (l : Label) : (f = .bind (fresh t l)) = False := by
  apply propext; constructor
  · rintro rfl; exact hf ⟨t, l, rfl⟩
  · exact False.elim

theorem FEq.trans {A B D : List Fact} (h1 : FEq A B) (h2 : FEq B D) : FEq A D :=
  fun f hf => (h1 f hf).trans (h2 f hf)

theorem fresh_isFresh (t : String) (l : Label) : IsFresh (fresh t l) := ⟨t, l, rfl⟩

@[simp] theorem pfactsB_paramBind (C : List Scope) :
    ∀ ps, PyCore.factsB (paramBind C ps) = paramBinds (priv C) ps
  | [] => rfl
  | q :: ps => by
    have := pfactsB_paramBind C ps
    simp only [paramBind, paramBinds, List.map_cons, PyCore.factsB, PyCore.factsS, PyCore.factsE, dead,
      List.append_nil, List.nil_append] at *
    rw [this]; rfl

theorem pfactsE_boolChainIn (l : Label) (o : Bool) : ∀ xs : List PE,
    PyCore.factsE (boolChainIn l o xs) = xs.flatMap PyCore.factsE
  | [] => by simp [boolChainIn, gad]
  | [_] => by simp [boolChainIn]
  | a :: b :: rest => by
    have := pfactsE_boolChainIn l o (b :: rest)
    simp only [boolChainIn, PyCore.factsE, this, List.flatMap_cons]

@[simp] theorem pfactsE_boolChain (l : Label) (o : Bool) (xs : List PE) :
    PyCore.factsE (boolChain l o xs) = xs.flatMap PyCore.factsE := by
  match xs with
  | [] => simp [boolChain, gad]
  | [_] => simp [boolChain]
  | a :: b :: rest => simp only [boolChain, PyCore.factsE, pfactsE_boolChainIn, List.flatMap_cons]

theorem pfactsE_cmpChain (l : Label) : ∀ (r : Label) (left : PE) (xs : List (String × Label × PE)),
    PyCore.factsE (cmpChain l r left xs) = PyCore.factsE left ++ xs.flatMap fun x => PyCore.factsE x.2.2
  | r, left, [] => by simp [cmpChain, PyCore.factsE]
  | r, left, [(op, lb, b)] => by simp [cmpChain, PyCore.factsE]
  | r, left, (op, lb, b) :: x :: rest => by
    have ih := pfactsE_cmpChain l (sub l 1) (gad l 4 (.get (fresh "c" lb)) []) (x :: rest)
    simp only [cmpChain, pfactsE_gad, List.flatMap_nil, List.nil_append] at ih ⊢
    simp [PyCore.factsE, ih]

theorem pfactsE_cmpOps (f : PE → List Fact) : ∀ (ops : List String) (xs : List (Label × PE)),
    (cmpOps ops xs).flatMap (fun x => f x.2.2) = xs.flatMap fun x => f x.2
  | _, [] => rfl
  | ops, (lb, b) :: rest => by simp [cmpOps, pfactsE_cmpOps f ops.tail rest]

@[simp] theorem pfactsB_ifsNest (lg : Label) : ∀ (cs : List PE) (body : PS),
    PyCore.factsB (ifsNest lg cs body) = cs.flatMap PyCore.factsE ++ PyCore.factsB body
  | [], _ => rfl
  | c :: cs, body => by
    simp [ifsNest, PyCore.factsB, PyCore.factsS, pfactsB_ifsNest lg cs body]

theorem pfactsB_forLoop (l : Label) (iv : Name) (st body u : PS) : FEq (PyCore.factsB (forLoop l iv st body u))
    (PyCore.factsB st ++ PyCore.factsB body ++ PyCore.factsB u) := by
  intro f hf
  simp only [forLoop, PyCore.factsB, PyCore.factsS, PyCore.factsHs, PyCore.factsE, pfactsB_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, ne_fresh hf, List.append_nil, List.nil_append,
    false_or, or_false]

theorem pfactsB_compWrap (l : Label) (k : CompKind) (loops : PS) :
    FEq (PyCore.factsB (compWrap l k loops)) (PyCore.factsB loops) := by
  intro f hf
  unfold compWrap; split
  · rfl
  · simp [PyCore.factsB, PyCore.factsS, PyCore.factsE, pfactsB_append, ne_fresh hf, nm, cc]

theorem pfactsB_dead (r : Label) (ss : PS) : PyCore.factsB [dead r ss] = PyCore.factsB ss := by
  simp [dead, PyCore.factsB, PyCore.factsS, PyCore.factsE]

@[simp] theorem pfactsS_dead (r : Label) (ss : PS) : PyCore.factsS (dead r ss) = PyCore.factsB ss := by
  simp [dead, PyCore.factsB, PyCore.factsS, PyCore.factsE]
@[simp] theorem pfactsS_stuckAt (r : Label) : PyCore.factsS (stuckAt r) = [] := by
  simp [stuckAt, PyCore.factsS]
@[simp] theorem pfactsS_setupS (l : Label) : PyCore.factsS (setupS l) = [] := by
  simp [setupS, PyCore.factsS, gad, cc]
@[simp] theorem pfactsE_deadSrc (lt : Label) : PyCore.factsE (deadSrc lt) = [] := rfl

/-- The facts of a comprehension's element: its values', and the generator's `yield`. -/
theorem pfactsB_compElt (l : Label) (k : CompKind) (es : List PE) (f : Fact) (hf : f ≠ .yld) :
    f ∈ PyCore.factsB (compElt l k es) ↔ f ∈ es.flatMap PyCore.factsE := by
  unfold compElt; split <;>
    simp [PyCore.factsB, PyCore.factsS, PyCore.factsE, cc, nm, List.map, pfactsB_map, hf]

theorem pfactsB_compElt_yld (l : Label) (k : CompKind) (es : List PE) (hk : k = .gen) (h1 : es.length = 1) :
    Fact.yld ∈ PyCore.factsB (compElt l k es) := by
  subst hk
  match es, h1 with
  | [e], _ => simp [compElt, PyCore.factsB, PyCore.factsS, PyCore.factsE]

theorem pfactsB_compElt_ny (l : Label) (k : CompKind) (es : List PE) (hk : k ≠ .gen ∨ es.length ≠ 1) :
    Fact.yld ∈ PyCore.factsB (compElt l k es) ↔ Fact.yld ∈ es.flatMap PyCore.factsE := by
  unfold compElt; split <;> simp_all [PyCore.factsB, PyCore.factsS, PyCore.factsE, cc, nm, pfactsB_map]

@[simp] theorem pfactsB_annT (C : List Scope) (l : Label) (t : Expr) : PyCore.factsB (annT C l t) = [] := by
  cases t <;> simp [annT, PyCore.factsB, PyCore.factsS, nm, PyCore.factsE]

/-- The simplification `feq` runs: unfold the translation, the analyses, and membership. -/
macro "tr_simp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [
    trE, trO, trEs, trA, trKs, trLs, trKVs, trDfs, trAnns, trAnnK, trG1, trGs, trT, trItems, trD, trDs,
    nameSrc, itemSrc, forSrc, blk, pfactsB_annT, pfactsE_cc, pfactsE_gad, nm, setupS, flatMap_nil_fun,
    factsE, factsO, factsEs, factsKs, factsDs, factsPs, factsG1, factsGs,
    List.mem_append, List.mem_cons, List.not_mem_nil, List.flatMap_cons, List.flatMap_nil,
    List.flatMap_append, List.append_nil, List.nil_append, pfactsB_append, PyCore.factsB,
    PyCore.factsS, PyCore.factsHs, PyCore.factsE, or_false, false_or, ite_false, ite_true,
    Bool.false_eq_true, pfactsE_recR, pfactsE_ccR, pfactsE_starMark, pfactsE_kwMark, pfactsE_constMark,
    pfactsE_constMarks, pfactsE_marks, pfactsE_paramMark, pfactsB_paramBind, pfactsE_boolChain,
    pfactsE_cmpOps, pfactsB_ifsNest, pfactsB_map, pfactsS_dead, pfactsS_stuckAt, pfactsS_setupS,
    pfactsE_deadSrc, dflt_mk, ann_mk, List.flatMap_map, List.map_cons, List.map_nil, trMarks_eq, constMarks_eq] $[$loc]?)

/-- Specialize each `FEq` fact to the fact `f` at hand (`hf : NF f`), and simplify it. -/
syntax "feq_ih" (ppSpace colGt term:max)* : tactic
set_option hygiene false in
macro_rules
  | `(tactic| feq_ih) => `(tactic| skip)
  | `(tactic| feq_ih $h $hs*) =>
    `(tactic| ((have := $h f hf; (try tr_simp at this); (try simp only [ne_fresh hf, false_or, or_false] at this)); feq_ih $hs*))

set_option hygiene false in
/-- Close an `FEq` goal from `FEq` facts about its parts. -/
macro "feq" hs:(ppSpace colGt term:max)* : tactic => `(tactic|
  (intro f hf; feq_ih $hs*; tr_simp; (try simp only [ne_fresh hf, false_or, or_false, List.not_mem_nil, *]); all_goals grind))

theorem factsPs_mem (p : Option Name) (f : Fact) : ∀ ps : List Param, f ∈ factsPs p ps ↔
    f ∈ ps.flatMap (fun q => factsO p q.dflt) ∨ f ∈ ps.flatMap (fun q => factsO p q.ann)
  | [] => by simp [factsPs]
  | .mk _ _ _ d a :: ps => by
    have := factsPs_mem p f ps
    simp only [factsPs, List.mem_append, List.flatMap_cons, dflt_mk, ann_mk, this]; grind

/-- What a target stores from: a source with no facts. -/
def SrcOk (src : Label → PE) : Prop := ∀ lt, PyCore.factsE (src lt) = []

theorem srcOk_name (t : String) (l : Label) : SrcOk (nameSrc t l) := fun _ => rfl
theorem srcOk_item (l : Label) (i : Nat) : SrcOk (itemSrc l i) := fun _ => by simp [itemSrc, PyCore.factsE]
theorem srcOk_for (l : Label) : SrcOk (forSrc l) := fun _ => rfl
theorem srcOk_dead : SrcOk deadSrc := fun _ => rfl

/-- Storing into a node that is no name, star, list or tuple binds what reading it does. -/
theorem factsE_st (p : Option Name) (t : Expr) (h : ∀ lt x, t ≠ .name lt x) (h2 : ∀ lt e, t ≠ .star lt e)
    (h3 : ∀ lt es, t ≠ .list lt es) (h4 : ∀ lt es, t ≠ .tuple lt es) : factsE p true t = factsE p false t := by
  cases t <;> first | rfl | (exfalso; first | exact h _ _ rfl | exact h2 _ _ rfl | exact h3 _ _ rfl | exact h4 _ _ rfl)

theorem trA_cons (C : List Scope) (e : Expr) (es : List Expr) :
    trA C (e :: es) = trE C (unstar e) :: trA C es := by
  cases e <;> rfl

theorem trItems_cons (C : List Scope) (lt : Label) (i : Nat) (t : Expr) (ts : List Expr) :
    trItems C lt i (t :: ts) = trT C (itemSrc lt i) (unstar t) (trE C (unstar t)) ++ trItems C lt (i + 1) ts := by
  cases t <;> rfl

theorem pfactsE_unstar (C : List Scope) (e : Expr) :
    PyCore.factsE (trE C (unstar e)) = PyCore.factsE (trE C e) := by
  cases e <;> simp [unstar, trE, PyCore.factsE, gad, cc]

theorem pfactsB_unstar (C : List Scope) (src : Label → PE) (t : Expr) :
    PyCore.factsB (trT C src (unstar t) (trE C (unstar t))) = PyCore.factsB (trT C src t (trE C t)) := by
  cases t <;> simp [unstar, trT, PyCore.factsB, PyCore.factsS, PyCore.factsE, pfactsS_dead, pfactsS_stuckAt]

mutual
theorem trE_facts (C : List Scope) : ∀ e, FEq (PyCore.factsE (trE C e)) (factsE (priv C) false e)
  | .const l c => by feq
  | .name l x => by feq
  | .bin l op a b => by have h1 := trE_facts C a; have h2 := trE_facts C b; feq h1 h2
  | .unary l op a => by have h1 := trE_facts C a; feq h1
  | .boolop l op es => by have h1 := trEs_facts C es; feq h1
  | .compare l a ops es => by
    have h1 := trE_facts C a; have h2 := trLs_facts C es
    simp only [trE, pfactsE_cmpChain]; feq h1 h2
  | .ifexp l c a b => by
    have h1 := trE_facts C c; have h2 := trE_facts C a; have h3 := trE_facts C b; feq h1 h2 h3
  | .call l f args kws => by
    have h1 := trE_facts C f; have h2 := trA_facts C args; have h3 := trKs_facts C kws; feq h1 h2 h3
  | .attr l e a => by have h1 := trE_facts C e; feq h1
  | .sub l e i => by have h1 := trE_facts C e; have h2 := trE_facts C i; feq h1 h2
  | .slice l a b c => by
    have h1 := trO_facts C l 1 a; have h2 := trO_facts C l 2 b; have h3 := trO_facts C l 3 c; feq h1 h2 h3
  | .star l e => by have h1 := trE_facts C e; feq h1
  | .list l es => by have h1 := trA_facts C es; feq h1
  | .tuple l es => by have h1 := trA_facts C es; feq h1
  | .set l es => by have h1 := trA_facts C es; feq h1
  | .dict l kvs => by have h1 := trKVs_facts C kvs; feq h1
  | .lam l ps b => by
    have h1 := trDfs_facts C ps; have h2 := trAnns_facts C ps
    intro f hf; have := h1 f hf; have := h2 f hf; have := factsPs_mem (priv C) f ps
    tr_simp; (try tr_simp at *); grind
  | .comp l k es gs => by
    have h1 := trG1_facts C gs
    have h2 := trGs_facts (.comp l k es gs :: C) (fresh "i" l) true gs
      (compElt l k (trEs (.comp l k es gs :: C) es))
    have h3 := trEs_facts (.comp l k es gs :: C) es
    simp only [priv] at h2 h3
    have h4 : FEq ((PyCore.factsB (compWrap l k (trGs (.comp l k es gs :: C) (fresh "i" l) true gs
        (compElt l k (trEs (.comp l k es gs :: C) es))))).filter Fact.isWal)
        ((factsGs (priv C) true gs ++ factsEs (priv C) false es).filter Fact.isWal) := by
      intro f hf
      have e1 := pfactsB_compWrap l k (trGs (.comp l k es gs :: C) (fresh "i" l) true gs
        (compElt l k (trEs (.comp l k es gs :: C) es))) f hf
      have e2 := h2 f hf; have e3 := h3 f hf
      simp only [List.mem_filter, List.mem_append] at e1 e2 e3 ⊢
      by_cases hy : f = .yld
      · subst hy; simp [Fact.isWal]
      · have e4 := pfactsB_compElt l k (trEs (.comp l k es gs :: C) es) f hy
        grind
    simp only [trE]
    split
    · rename_i hg
      simp only [List.isEmpty_iff] at hg; subst hg
      intro f hf
      have := h4 f hf
      simp only [factsE, factsG1, factsGs, PyCore.factsE, List.nil_append, List.append_nil, gad, cc,
        pfactsE_ccR, List.flatMap_nil, List.mem_append, List.mem_filter, trGs] at this ⊢
      simpa [List.mem_filter] using this
    · intro f hf
      have := h4 f hf; have := h1 f hf
      simp only [factsE, PyCore.factsE, cc, pfactsE_ccR, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.mem_append, List.mem_filter] at *
      grind
  | .walrus l x e => by have h1 := trE_facts C e; feq h1
  | .yield l e => by have h1 := trO_facts C l 1 e; feq h1
  | .yieldFrom l e => by have h1 := trE_facts C e; feq h1
  | .fstr l es => by have h1 := trEs_facts C es; feq h1
  | .fmt l e cv sp => by
    have h1 := trE_facts C e
    cases sp with
    | none => simp only [trE]; split <;> feq h1
    | some s =>
      have h2 := trE_facts C s
      simp only [trE]; split <;> feq h1 h2
theorem trO_facts (C : List Scope) (l : Label) (k : Nat) : ∀ o,
    FEq (PyCore.factsE (trO C l k o)) (factsO (priv C) o)
  | none => by feq
  | some e => by have h1 := trE_facts C e; feq h1
theorem trEs_facts (C : List Scope) : ∀ es,
    FEq ((trEs C es).flatMap PyCore.factsE) (factsEs (priv C) false es)
  | [] => by feq
  | e :: es => by have h1 := trE_facts C e; have h2 := trEs_facts C es; feq h1 h2
theorem trA_facts (C : List Scope) : ∀ es,
    FEq ((trA C es).flatMap PyCore.factsE) (factsEs (priv C) false es)
  | [] => by feq
  | e :: es => by
    have h1 := trE_facts C e; have h2 := trA_facts C es
    rw [trA_cons]; intro f hf
    have := h1 f hf; have := h2 f hf
    simp only [List.flatMap_cons, List.mem_append, pfactsE_unstar, factsEs] at *
    grind
theorem trKs_facts (C : List Scope) : ∀ ks,
    FEq ((trKs C ks).flatMap PyCore.factsE) (factsKs (priv C) ks)
  | [] => by feq
  | .mk l x e :: ks => by have h1 := trE_facts C e; have h2 := trKs_facts C ks; feq h1 h2
theorem trLs_facts (C : List Scope) : ∀ es,
    FEq ((trLs C es).flatMap fun x => PyCore.factsE x.2) (factsEs (priv C) false es)
  | [] => by feq
  | e :: es => by have h1 := trE_facts C e; have h2 := trLs_facts C es; feq h1 h2
theorem trKVs_facts (C : List Scope) : ∀ kvs,
    FEq ((trKVs C kvs).flatMap PyCore.factsE) (factsDs (priv C) kvs)
  | [] => by feq
  | .mk (some k) v :: kvs => by
    have h1 := trE_facts C k; have h2 := trE_facts C v; have h3 := trKVs_facts C kvs; feq h1 h2 h3
  | .mk none v :: kvs => by
    have h2 := trE_facts C v; have h3 := trKVs_facts C kvs; feq h2 h3
theorem trDfs_facts (C : List Scope) : ∀ ps,
    FEq ((trDfs C ps).flatMap PyCore.factsE) (ps.flatMap fun q => factsO (priv C) q.dflt)
  | [] => by feq
  | .mk l _ _ (some d) _ :: ps => by
    have h1 := trE_facts C d; have h2 := trDfs_facts C ps; feq h1 h2
  | .mk l _ _ none _ :: ps => by have h2 := trDfs_facts C ps; feq h2
theorem trAnns_facts (C : List Scope) : ∀ ps,
    FEq ((trAnns C ps).flatMap PyCore.factsE) (ps.flatMap fun q => factsO (priv C) q.ann)
  | [] => by feq
  | .mk l _ _ _ (some a) :: ps => by
    have h1 := trE_facts C a; have h2 := trAnns_facts C ps; feq h1 h2
  | .mk l _ _ _ none :: ps => by have h2 := trAnns_facts C ps; feq h2
theorem trG1_facts (C : List Scope) : ∀ gs, FEq (PyCore.factsE (trG1 C gs)) (factsG1 (priv C) gs)
  | [] => by feq
  | .mk _ _ i _ :: _ => by have h1 := trE_facts C i; feq h1
theorem trGs_facts (C : List Scope) (it : Name) : ∀ (first : Bool) (gs : List Gen) (inner : PS),
    FEq (PyCore.factsB (trGs C it first gs inner)) (factsGs (priv C) first gs ++ PyCore.factsB inner)
  | _, [], inner => by feq
  | first, .mk lg t i ifs :: gs, inner => by
    have h1 := trE_facts C i
    have h2 := trT_facts C (forSrc lg) (srcOk_for lg) t (trE_facts C t)
    have h3 := trEs_facts C ifs
    have h4 := trGs_facts C it false gs inner
    have h5 := pfactsB_forLoop lg (if first then it else fresh "j" lg)
      (trT C (forSrc lg) t (trE C t)) (ifsNest lg (trEs C ifs) (trGs C it false gs inner)) []
    cases first <;> simp only [trGs] <;> feq h1 h2 h3 h4 h5
theorem trT_facts (C : List Scope) (src : Label → PE) (hs : SrcOk src) : ∀ t,
    FEq (PyCore.factsE (trE C t)) (factsE (priv C) false t) →
    FEq (PyCore.factsB (trT C src t (trE C t))) (factsE (priv C) true t)
  | .name lt x, _ => by have := hs lt; feq
  | .attr lt o a, _ => by have := hs lt; have h1 := trE_facts C o; feq h1
  | .sub lt o i, _ => by have := hs lt; have h1 := trE_facts C o; have h2 := trE_facts C i; feq h1 h2
  | .tuple lt ts, _ => by have := hs lt; have h1 := trItems_facts C lt 0 ts; feq h1
  | .list lt ts, _ => by have := hs lt; have h1 := trItems_facts C lt 0 ts; feq h1
  | .star ls e, _ => by have h1 := trT_facts C src hs e (trE_facts C e); feq h1
  | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1 | .ifexp .., h1
  | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1 | .comp .., h1
  | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    simp only [trT]; intro f hf; have := h1 f hf
    simp only [PyCore.factsB, PyCore.factsS, pfactsS_stuckAt, pfactsS_dead, List.nil_append,
      List.append_nil] at this ⊢
    simpa [factsE] using this
theorem trItems_facts (C : List Scope) (lt : Label) : ∀ (i : Nat) (ts : List Expr),
    FEq (PyCore.factsB (trItems C lt i ts)) (factsEs (priv C) true ts)
  | _, [] => by feq
  | i, t :: ts => by
    have h1 := trT_facts C (itemSrc lt i) (srcOk_item lt i) t (trE_facts C t)
    have h2 := trItems_facts C lt (i + 1) ts
    rw [trItems_cons]; intro f hf
    have := h1 f hf; have := h2 f hf
    simp only [pfactsB_append, List.mem_append, pfactsB_unstar, factsEs] at *
    grind
end

mutual
theorem trD_facts (C : List Scope) : ∀ t, FEq (PyCore.factsE (trE C t)) (factsE (priv C) false t) →
    FEq (PyCore.factsB (trD C t (trT C deadSrc t (trE C t)))) (factsE (priv C) true t)
  | .name lt x, _ => by feq
  | .attr lt o a, _ => by have h1 := trE_facts C o; feq h1
  | .sub lt o i, _ => by have h1 := trE_facts C o; have h2 := trE_facts C i; feq h1 h2
  | .tuple lt ts, _ => by have h1 := trDs_facts C ts; feq h1
  | .list lt ts, _ => by have h1 := trDs_facts C ts; feq h1
  | .star .., h1 | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1
  | .ifexp .., h1 | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1
  | .comp .., h1 | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    have h2 := trT_facts C deadSrc srcOk_dead _ h1
    simp only [trD]; intro f hf; have := h2 f hf
    simpa [PyCore.factsB, PyCore.factsS] using this
theorem trDs_facts (C : List Scope) : ∀ ts, FEq (PyCore.factsB (trDs C ts)) (factsEs (priv C) true ts)
  | [] => by feq
  | t :: ts => by
    have h1 := trD_facts C t (trE_facts C t); have h2 := trDs_facts C ts
    simp only [trDs]; intro f hf; have := h1 f hf; have := h2 f hf
    simp only [pfactsB_append, List.mem_append, factsEs] at *; grind
end

/-- The reading and storing statements of an augmented assignment's target bind what storing
into it does. -/
theorem trAug_facts (C : List Scope) (l : Label) (t : Expr) :
    FEq (PyCore.factsB (trAug C l t (trT C deadSrc t (trE C t))).1 ++
      PyCore.factsB (trAug C l t (trT C deadSrc t (trE C t))).2) (factsE (priv C) true t) := by
  have h0 := trT_facts C deadSrc srcOk_dead t (trE_facts C t)
  cases t with
  | name lt x => simp only [trAug]; feq
  | attr lt e a => have h2 := trE_facts C e; simp only [trAug]; feq h2
  | sub lt e i => have h2 := trE_facts C e; have h3 := trE_facts C i; simp only [trAug]; feq h2 h3
  | _ => simp only [trAug]; feq h0

/-- A bare annotated target's evaluation and its binding (in a branch that never runs) bind
what storing into it does. -/
theorem annBare_facts (C : List Scope) (t : Expr) :
    FEq (PyCore.factsB (annBare C t (trT C deadSrc t (trE C t))) ++ PyCore.factsB (annBind C t))
      (factsE (priv C) true t) := by
  have h0 := trT_facts C deadSrc srcOk_dead t (trE_facts C t)
  cases t with
  | name lt x => simp only [annBare, annBind]; feq
  | attr lt e a => have h2 := trE_facts C e; simp only [annBare, annBind]; feq h2
  | sub lt e i => have h2 := trE_facts C e; have h3 := trE_facts C i; simp only [annBare, annBind]; feq h2 h3
  | _ => simp only [annBare, annBind]; feq h0

/-- A `def`'s annotations grouped by kind are all its annotations. -/
theorem trAnnK_all (C : List Scope) (x : PE) : ∀ ps, x ∈ trAnnK C .pos ps ++ trAnnK C .posonly ps ++
    trAnnK C .vararg ps ++ trAnnK C .kwonly ps ++ trAnnK C .kwarg ps ↔ x ∈ trAnns C ps
  | [] => by simp [trAnnK, trAnns]
  | .mk _ _ k _ (some a) :: ps => by
    have := trAnnK_all C x ps
    cases k <;> simp only [trAnnK, trAnns, reduceCtorEq, ite_true, ite_false, List.mem_append,
      List.mem_cons] at this ⊢ <;> grind
  | .mk _ _ _ _ none :: ps => by
    have := trAnnK_all C x ps; simpa [trAnnK, trAnns] using this

theorem flatMap_mem_iff {α β} {f : α → List β} {A B : List α} (h : ∀ x, x ∈ A ↔ x ∈ B) (y : β) :
    y ∈ A.flatMap f ↔ y ∈ B.flatMap f := by
  simp only [List.mem_flatMap]; exact ⟨fun ⟨x, h1, h2⟩ => ⟨x, (h x).1 h1, h2⟩, fun ⟨x, h1, h2⟩ => ⟨x, (h x).2 h1, h2⟩⟩

theorem alias_facts (C : List Scope) (g : Alias → PyCore.Stmt)
    (hg : ∀ a, PyCore.factsS (g a) = if a.name == "*" then [] else [.bind (mangle (priv C) a.bound)])
    (f : Fact) : ∀ al : List Alias,
    f ∈ PyCore.factsB (al.map g) ↔ f ∈ (bindingAliases al).map fun a => Fact.bind (mangle (priv C) a.bound)
  | [] => by simp [PyCore.factsB, bindingAliases]
  | a :: al => by
    have ih := alias_facts C g hg f al
    simp only [List.map_cons, PyCore.factsB, List.mem_append, ih, bindingAliases, List.filter_cons, hg] at *
    by_cases h : a.name == "*" <;> simp_all

mutual
theorem trS_facts (C : List Scope) : ∀ s, FEq (PyCore.factsS (trS C s)) (factsS (priv C) s)
  | .expr l e => by have h1 := trE_facts C e; simp only [trS, factsS]; feq h1
  | .assign l ts e => by
    have h1 := trE_facts C e
    have h2 : ∀ ts, FEq (PyCore.factsB (trTs C (nameSrc "t" l) ts)) (factsEs (priv C) true ts) := by
      intro ts; induction ts with
      | nil => simp only [trTs]; feq
      | cons t ts ih =>
        have := trT_facts C (nameSrc "t" l) (srcOk_name "t" l) t (trE_facts C t)
        simp only [trTs]; intro f hf; have := this f hf; have := ih f hf
        simp only [pfactsB_append, List.mem_append, factsEs] at *; grind
    have h3 := h2 ts
    simp only [trS, factsS]; feq h1 h3
  | .augassign l t op e => by
    have h1 := trAug_facts C l t; have h2 := trE_facts C e
    simp only [trS, factsS]; feq h1 h2
  | .annassign l t a v => by
    have h1 := trE_facts C a
    have h3 := trT_facts C (nameSrc "t" l) (srcOk_name "t" l) t (trE_facts C t)
    have h4 := annBare_facts C t
    cases v with
    | none => cases hf : isTop C <;> simp only [trS, factsS, hf] <;> feq h1 h4
    | some v =>
      have h2 := trE_facts C v
      cases hf : isTop C <;> simp only [trS, factsS, hf] <;> feq h1 h2 h3
  | .del l ts => by have h1 := trDs_facts C ts; simp only [trS, factsS]; feq h1
  | .ite l c t u => by
    have h1 := trE_facts C c; have h2 := trB_facts C t; have h3 := trB_facts C u
    simp only [trS, factsS]; feq h1 h2 h3
  | .while l c b u => by
    have h1 := trE_facts C c; have h2 := trB_facts C b; have h3 := trB_facts C u
    simp only [trS, factsS]; feq h1 h2 h3
  | .for l t it b u => by
    have h1 := trE_facts C it
    have h2 := trT_facts C (forSrc l) (srcOk_for l) t (trE_facts C t)
    have h3 := trB_facts C b; have h4 := trB_facts C u
    have h5 := pfactsB_forLoop l (fresh "i" l) (trT C (forSrc l) t (trE C t)) (trB C b) (trB C u)
    simp only [trS, factsS]; feq h1 h2 h3 h4 h5
  | .brk l | .cont l | .pass l => by simp only [trS, factsS]; feq
  | .ret l e => by have h1 := trO_facts C l 1 e; simp only [trS, factsS]; feq h1
  | .defn l f ps b ds r => by
    have h1 := trEs_facts C ds; have h2 := trDfs_facts C ps; have h3 := trAnns_facts C ps
    intro g hg
    have := h1 g hg; have := h2 g hg; have := h3 g hg; have := factsPs_mem (priv C) g ps
    have := flatMap_mem_iff (f := PyCore.factsE) (trAnnK_all C · ps) g
    cases r with
    | none => simp only [trS, factsS]; tr_simp; (try tr_simp at *); grind
    | some r => have := trE_facts C r g hg; simp only [trS, factsS]; tr_simp; (try tr_simp at *); grind
  | .cls l x bs ks b ds => by
    have h1 := trEs_facts C ds; have h2 := trA_facts C bs; have h3 := trKs_facts C ks
    simp only [trS, factsS]; feq h1 h2 h3
  | .glob l xs | .nonloc l xs => by simp only [trS, factsS]; feq
  | .tryE l b hs u => by
    have h1 := trB_facts C b; have h2 := trHs_facts C hs; have h3 := trB_facts C u
    simp only [trS, factsS]; feq h1 h2 h3
  | .raise l none none => by simp only [trS, factsS]; feq
  | .raise l (some e) none => by have h1 := trE_facts C e; simp only [trS, factsS]; feq h1
  | .raise l (some e) (some c) => by
    have h1 := trE_facts C e; have h2 := trE_facts C c; simp only [trS, factsS]; feq h1 h2
  | .raise l none (some c) => by have h2 := trE_facts C c; simp only [trS, factsS]; feq h2
  | .imp l al => by
    intro f hf
    simp only [trS, factsS, blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, List.append_nil]
    refine alias_facts C _ (fun a => ?_) f al
    split <;> simp_all [PyCore.factsS, stuckAt, PyCore.factsE]
  | .impFrom l m al lvl => by
    intro f hf
    simp only [trS, factsS]
    split
    · simp only [blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, pfactsB_map, PyCore.factsE,
        pfactsE_gad, List.flatMap_nil, List.nil_append, List.append_nil, pfactsS_dead, List.mem_flatMap,
        List.mem_map, List.mem_singleton]
      constructor <;> rintro ⟨a, h1, h2⟩ <;> exact ⟨a, h1, h2.symm⟩
    · simp only [blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, List.append_nil, PyCore.factsE,
        List.mem_cons, ne_fresh hf, false_or, pfactsE_cc, List.flatMap_nil, List.mem_append,
        List.not_mem_nil]
      refine alias_facts C _ (fun a => ?_) f al
      split <;> simp_all [PyCore.factsS, PyCore.factsE, nm]
  | .assert l t m => by
    have h1 := trE_facts C t
    cases m with
    | none => simp only [trS, factsS]; feq h1
    | some m => have h2 := trE_facts C m; simp only [trS, factsS]; feq h1 h2
theorem trHs_facts (C : List Scope) : ∀ hs, FEq (PyCore.factsHs (trHs C hs)) (factsHs (priv C) hs)
  | [] => by simp only [trHs, factsHs]; feq
  | .mk l ty x b :: hs => by
    have h2 := trB_facts C b; have h3 := trHs_facts C hs
    cases ty with
    | none =>
      cases x <;> simp only [trHs, factsHs, Option.map, Option.getD, Option.toList, factsO] <;> feq h2 h3
    | some t =>
      have h1 := trE_facts C t
      cases x <;> simp only [trHs, factsHs, Option.map, Option.getD, Option.toList, factsO] <;> feq h1 h2 h3
theorem trB_facts (C : List Scope) : ∀ ss, FEq (PyCore.factsB (trB C ss)) (factsB (priv C) ss)
  | [] => by simp only [trB, factsB]; feq
  | s :: ss => by
    have h1 := trS_facts C s; have h2 := trB_facts C ss
    simp only [trB, factsB]; feq h1 h2
end

theorem trEs_length (C : List Scope) : ∀ es, (trEs C es).length = es.length
  | [] => rfl
  | e :: es => by simp [trEs, trEs_length C es]

/-- A generator expression has one element (CPython's `GeneratorExp` has one `elt`). -/
def Scope.genOk : Scope → Bool
  | .comp _ .gen es _ => es.length == 1
  | _ => true

/-- The own body of each scope of ⌊p⌋ is that of its Surf scope, up to fresh names; on
`yield`, for a generator expression with one element. -/
theorem scope_facts_gen (C : List Scope) : ∀ S f, NF f → (f = .yld → S.genOk = true) →
    (f ∈ (trScope C S).facts ↔ f ∈ S.facts C)
  | .fn l f ps b, g, hg, _ => by
    have h1 := trB_facts (.fn l f ps b :: C) b
    simp only [trScope, PyCore.Scope.facts, Scope.facts]
    revert g; feq h1
  | .lam l ps b, g, hg, _ => by
    have h1 := trE_facts (.lam l ps b :: C) b
    simp only [trScope, PyCore.Scope.facts, Scope.facts]
    revert g; feq h1
  | .cl l x b, g, hg, _ => by
    have h1 := trB_facts (.cl l x b :: C) b
    simp only [trScope, PyCore.Scope.facts, Scope.facts]
    revert g; feq h1
  | .comp l k es gs, f, hf, hy => by
    have h1 := trGs_facts (.comp l k es gs :: C) (fresh "i" l) true gs (compElt l k (trEs (.comp l k es gs :: C) es))
    have h2 := trEs_facts (.comp l k es gs :: C) es
    have h3 := pfactsB_compWrap l k (trGs (.comp l k es gs :: C) (fresh "i" l) true gs
      (compElt l k (trEs (.comp l k es gs :: C) es)))
    simp only [priv] at h1 h2
    simp only [trScope, PyCore.Scope.facts, Scope.facts, priv, List.mem_cons, List.mem_append]
    have e1 := h1 f hf; have e2 := h2 f hf; have e3 := h3 f hf
    simp only [List.mem_append] at e1 e3
    have hnf : f ≠ .bind (fresh "i" l) := fun h => by subst h; exact hf ⟨_, _, rfl⟩
    by_cases hyl : f = .yld
    · subst hyl
      have hg := hy rfl
      by_cases hk : k = .gen
      · subst hk
        have hl : (trEs (.comp l .gen es gs :: C) es).length = 1 := by
          simp only [Scope.genOk, beq_iff_eq] at hg
          rw [← hg]; exact trEs_length _ es
        have := pfactsB_compElt_yld l .gen _ rfl hl
        simp only [ite_true, List.mem_cons]; grind
      · have := pfactsB_compElt_ny l k (trEs (.comp l k es gs :: C) es) (.inl hk)
        simp only [hk, ite_false, List.not_mem_nil]; grind
    · have := pfactsB_compElt l k (trEs (.comp l k es gs :: C) es) f hyl
      have hk : f ∉ (if k = .gen then [Fact.yld] else []) := by split <;> simp [hyl]
      grind

theorem scope_facts (C : List Scope) (S : Scope) (hS : S.genOk = true) : FEq (trScope C S).facts (S.facts C) :=
  fun f hf => scope_facts_gen C S f hf fun _ => hS
theorem mem_iff_contains {f : Fact} {A : List Fact} : f ∈ A ↔ A.contains f = true :=
  List.contains_iff_mem.symm

theorem contains_tr {C S f} (hf : NF f) (hy : f ≠ .yld) :
    (trScope C S).facts.contains f = (S.facts C).contains f :=
  Bool.eq_iff_iff.mpr (by
    rw [← mem_iff_contains, ← mem_iff_contains]; exact scope_facts_gen C S f hf (fun h => absurd h hy))

theorem isComp_tr (C : List Scope) (S : Scope) : (trScope C S).isComp = S.isComp := by
  cases S <;> rfl

theorem binds_tr {C S x} (hx : ¬ IsFresh x) : (trScope C S).binds x = S.binds C x := by
  simp only [PyCore.Scope.binds, Scope.binds, contains_tr (f := .bind x) hx (by simp), contains_tr (f := .wal x) hx (by simp),
    isComp_tr]
theorem walrus_tr {C S x} (hx : ¬ IsFresh x) : (trScope C S).walrus x = S.walrus C x := by
  simp only [PyCore.Scope.walrus, Scope.walrus, contains_tr (f := .wal x) hx (by simp), isComp_tr]
theorem declG_tr {C S x} (hx : ¬ IsFresh x) : (trScope C S).declG x = S.declG C x := contains_tr hx (by simp)
theorem declN_tr {C S x} (hx : ¬ IsFresh x) : (trScope C S).declN x = S.declN C x := contains_tr hx (by simp)

/-- Each function of ⌊p⌋ has the kind of its Surf function (a generator expression has one
element, as CPython's parser makes it). -/
theorem kind_tr (C : List Scope) (S : Scope) (hS : S.genOk = true) : (trScope C S).kind = S.kind C := by
  have h : (trScope C S).facts.contains .yld = (S.facts C).contains .yld :=
    Bool.eq_iff_iff.mpr (by
      rw [← mem_iff_contains, ← mem_iff_contains]; exact scope_facts_gen C S .yld trivial fun _ => hS)
  cases S <;> simp only [trScope, PyCore.Scope.kind, Scope.kind] at h ⊢ <;> rw [h]

theorem walGlobal_tr {x : Name} (hx : ¬ IsFresh x) : ∀ C, PyCore.walGlobal (trChain C) x = walGlobal C x
  | [] => rfl
  | S :: C => by
    have h1 := declG_tr (C := C) (S := S) hx; have h0 := isComp_tr C S
    simp only [trChain, PyCore.walGlobal, walGlobal, h0, h1, walGlobal_tr hx C]

theorem enclosing_tr {x : Name} (hx : ¬ IsFresh x) : ∀ C, PyCore.enclosing (trChain C) x = enclosing C x
  | [] => rfl
  | S :: C => by
    have h1 := declG_tr (C := C) (S := S) hx; have h2 := declN_tr (C := C) (S := S) hx
    have h3 := binds_tr (C := C) (S := S) hx; have h4 := walrus_tr (C := C) (S := S) hx
    have ih := enclosing_tr hx C; have hw := walGlobal_tr hx C
    cases S <;> simp only [trChain, trScope] at h1 h2 h3 h4 ⊢ <;>
      simp only [PyCore.enclosing, enclosing, h1, h2, h3, h4, ih, hw]

/-- Every name that is not fresh is classified in each scope of ⌊p⌋ as in its Surf scope. -/
theorem cls_tr {x : Name} (hx : ¬ IsFresh x) : ∀ C, PyCore.clsOf (trChain C) x = clsOf C x
  | [] => rfl
  | S :: C => by
    have h1 := declG_tr (C := C) (S := S) hx; have h2 := declN_tr (C := C) (S := S) hx
    have h3 := binds_tr (C := C) (S := S) hx; have h4 := walrus_tr (C := C) (S := S) hx
    have hw := walGlobal_tr hx C
    cases S <;> simp only [trChain, trScope] at h1 h2 h3 h4 ⊢ <;>
      simp only [PyCore.clsOf, clsOf, h1, h2, h3, h4, hw, enclosing_tr hx C]



/-! ## Occurrences and functions -/

/-- A Surf item and an item of ⌊p⌋ that is its image: an occurrence of the same name
at a node made for it (`sub l k`), in the image of its chain; or a function at the
node made for it, with the image scope. -/
def Img : Item → PyCore.Item → Prop
  | .occ l x C, .occ l' x' C' => (∃ k, k < 64 ∧ l' = sub l k) ∧ x' = x ∧ C' = trChain C
  | .fn l C S, .fn l' S' => l' = sub l 1 ∧ S' = trScope C S
  | _, _ => False

/-- An occurrence of a fresh name. -/
def FreshItem : PyCore.Item → Prop
  | .occ _ x _ => IsFresh x
  | .fn .. => False

/-- The items `A` of ⌊p⌋ are, up to fresh names, the images of the items `B` of `p`. -/
structure Sim (A : List PyCore.Item) (B : List Item) : Prop where
  sound : ∀ i ∈ A, FreshItem i ∨ ∃ j ∈ B, Img j i
  complete : ∀ j ∈ B, ∃ i ∈ A, Img j i

theorem Sim.app {A A' : List PyCore.Item} {B B' : List Item} (h1 : Sim A B) (h2 : Sim A' B') :
    Sim (A ++ A') (B ++ B') := by
  constructor
  · intro i hi
    rcases List.mem_append.1 hi with h | h
    · exact (h1.sound i h).imp id fun ⟨j, hj, hij⟩ => ⟨j, List.mem_append_left _ hj, hij⟩
    · exact (h2.sound i h).imp id fun ⟨j, hj, hij⟩ => ⟨j, List.mem_append_right _ hj, hij⟩
  · intro j hj
    rcases List.mem_append.1 hj with h | h
    · obtain ⟨i, hi, hij⟩ := h1.complete j h; exact ⟨i, List.mem_append_left _ hi, hij⟩
    · obtain ⟨i, hi, hij⟩ := h2.complete j h; exact ⟨i, List.mem_append_right _ hi, hij⟩

theorem Sim.congr {A A' : List PyCore.Item} {B B' : List Item} (h : Sim A B)
    (hA : ∀ i, i ∈ A' ↔ i ∈ A) (hB : ∀ j, j ∈ B' ↔ j ∈ B) : Sim A' B' :=
  ⟨fun i hi => (h.sound i ((hA i).1 hi)).imp id fun ⟨j, hj, hij⟩ => ⟨j, (hB j).2 hj, hij⟩,
   fun j hj => let ⟨i, hi, hij⟩ := h.complete j ((hB j).1 hj); ⟨i, (hA i).2 hi, hij⟩⟩

theorem Sim.nil : Sim [] [] := ⟨by simp, by simp⟩

theorem Sim.frs {A : List PyCore.Item} (h : ∀ i ∈ A, FreshItem i) : Sim A [] :=
  ⟨fun i hi => .inl (h i hi), by simp⟩

theorem Sim.fr (lab : Label) (t : String) (l : Label) (C : List PyCore.Scope) :
    Sim [.occ lab (fresh t l) C] [] :=
  Sim.frs (by simp [FreshItem]; exact ⟨t, l, rfl⟩)

theorem Sim.oc (l k : Label) (x : Name) (C : List Scope) (hk : k < 64 := by decide) :
    Sim [.occ (sub l k) x (trChain C)] [.occ l x C] :=
  ⟨by simp [Img]; exact .inr ⟨k, hk, rfl⟩, by simp [Img]; exact ⟨k, hk, rfl⟩⟩

theorem Sim.fn1 (l : Label) (C : List Scope) (S : Scope) :
    Sim [.fn (sub l 1) (trScope C S)] [.fn l C S] := ⟨by simp [Img], by simp [Img]⟩

/-- Items of ⌊p⌋ covered by items that are already images, and fresh ones. -/
theorem Sim.cover {A A' : List PyCore.Item} {B : List Item} (h : Sim A B)
    (h1 : ∀ i ∈ A', i ∈ A ∨ FreshItem i) (h2 : ∀ i ∈ A, i ∈ A') : Sim A' B :=
  ⟨fun i hi => by
    rcases h1 i hi with h' | h'
    · exact h.sound i h'
    · exact .inl h',
   fun j hj => let ⟨i, hi, hij⟩ := h.complete j hj; ⟨i, h2 i hi, hij⟩⟩

/-- Extra items of ⌊p⌋ that are images of items already there. -/
theorem Sim.extra {A E : List PyCore.Item} {B : List Item} (h : Sim A B)
    (hE : ∀ i ∈ E, ∃ j ∈ B, Img j i) : Sim (E ++ A) B :=
  ⟨fun i hi => by
    rcases List.mem_append.1 hi with h' | h'
    · exact .inr (hE i h')
    · exact h.sound i h',
   fun j hj => let ⟨i, hi, hij⟩ := h.complete j hj; ⟨i, List.mem_append_right _ hi, hij⟩⟩


@[simp] theorem pitemsE_cc (C) (l : Label) (k : Nat) (g : String) (es : List PE) :
    PyCore.itemsE R0 C (cc l k g es) = es.flatMap (PyCore.itemsE R0 C) := pitemsE_ccR ..
@[simp] theorem pitemsE_gad (C) (l : Label) (k : Nat) (g : Py.Gadget) (es : List PE) :
    PyCore.itemsE R0 C (gad l k g es) = es.flatMap (PyCore.itemsE R0 C) := pitemsE_ccR ..
@[simp] theorem pitemsS_dead (C) (r : Label) (ss : PS) : PyCore.itemsS R0 C (dead r ss) = PyCore.itemsB R0 C ss := by
  simp [dead, PyCore.itemsS, PyCore.itemsE, PyCore.itemsB]
@[simp] theorem pitemsS_stuckAt (C) (r : Label) : PyCore.itemsS R0 C (stuckAt r) = [] := by
  simp [stuckAt, PyCore.itemsS]
@[simp] theorem pitemsS_setupS (C) (l : Label) : PyCore.itemsS R0 C (setupS l) = [] := by
  simp [setupS, PyCore.itemsS]
@[simp] theorem pitemsE_deadSrc (C) (lt : Label) : PyCore.itemsE R0 C (deadSrc lt) = [] := rfl

theorem pitemsE_boolChainIn (C) (l : Label) (o : Bool) : ∀ xs : List PE,
    PyCore.itemsE R0 C (boolChainIn l o xs) = xs.flatMap (PyCore.itemsE R0 C)
  | [] => by simp [boolChainIn]
  | [_] => by simp [boolChainIn]
  | a :: b :: rest => by
    have := pitemsE_boolChainIn C l o (b :: rest)
    simp only [boolChainIn, PyCore.itemsE, this, List.flatMap_cons, enone_e, Option.isSome_none,
      Bool.false_eq_true, ite_false]

@[simp] theorem pitemsE_boolChain (C) (l : Label) (o : Bool) (xs : List PE) :
    PyCore.itemsE R0 C (boolChain l o xs) = xs.flatMap (PyCore.itemsE R0 C) := by
  match xs with
  | [] => simp [boolChain]
  | [_] => simp [boolChain]
  | a :: b :: rest => simp only [boolChain, PyCore.itemsE, pitemsE_boolChainIn, List.flatMap_cons, enone_e,
      Option.isSome_none, Bool.false_eq_true, ite_false]

theorem pitemsE_cmpChain (C) (l : Label) : ∀ (r : Label) (left : PE) (xs : List (String × Label × PE)),
    PyCore.itemsE R0 C (cmpChain l r left xs) =
      PyCore.itemsE R0 C left ++ xs.flatMap fun x => PyCore.itemsE R0 C x.2.2
  | r, left, [] => by simp [cmpChain, PyCore.itemsE]
  | r, left, [(op, lb, b)] => by simp [cmpChain, PyCore.itemsE]
  | r, left, (op, lb, b) :: x :: rest => by
    have ih := pitemsE_cmpChain C l (sub l 1) (gad l 4 (.get (fresh "c" lb)) []) (x :: rest)
    simp only [cmpChain, pitemsE_gad, List.flatMap_nil, List.nil_append] at ih ⊢
    simp [PyCore.itemsE, ih]

theorem pitemsE_cmpOps (f : PE → List PyCore.Item) : ∀ (ops : List String) (xs : List (Label × PE)),
    (cmpOps ops xs).flatMap (fun x => f x.2.2) = xs.flatMap fun x => f x.2
  | _, [] => rfl
  | ops, (lb, b) :: rest => by simp [cmpOps, pitemsE_cmpOps f ops.tail rest]

@[simp] theorem pitemsB_ifsNest (C) (lg : Label) : ∀ (cs : List PE) (body : PS),
    PyCore.itemsB R0 C (ifsNest lg cs body) = cs.flatMap (PyCore.itemsE R0 C) ++ PyCore.itemsB R0 C body
  | [], _ => rfl
  | c :: cs, body => by
    simp [ifsNest, PyCore.itemsB, PyCore.itemsS, pitemsB_ifsNest C lg cs body]

theorem pitemsB_annT (D) (C : List Scope) (l : Label) (t : Expr) :
    ∀ i ∈ PyCore.itemsB R0 D (annT C l t), FreshItem i := by
  cases t <;> simp [annT, PyCore.itemsB, PyCore.itemsS, nm, PyCore.itemsE, FreshItem, fresh_isFresh]

theorem pitemsB_unstar (D) (C : List Scope) (src : Label → PE) (t : Expr) :
    PyCore.itemsB R0 D (trT C src (unstar t) (trE C (unstar t))) = PyCore.itemsB R0 D (trT C src t (trE C t)) := by
  cases t <;> simp [unstar, trT, PyCore.itemsB]

theorem pitemsE_unstar (D) (C : List Scope) (e : Expr) :
    PyCore.itemsE R0 D (trE C (unstar e)) = PyCore.itemsE R0 D (trE C e) := by
  cases e <;> simp [unstar, trE, PyCore.itemsE]

theorem itemsPs_mem (C : List Scope) (j : Item) : ∀ ps : List Param, j ∈ itemsPs C ps ↔
    j ∈ ps.flatMap (fun q => itemsO C q.dflt) ∨ j ∈ ps.flatMap (fun q => itemsO C q.ann)
  | [] => by simp [itemsPs]
  | .mk _ _ _ d a :: ps => by
    have := itemsPs_mem C j ps
    simp only [itemsPs, List.mem_append, List.flatMap_cons, dflt_mk, ann_mk, this]; grind

/-- What a target stores from: a source whose items are fresh. -/
def SrcIt (src : Label → PE) : Prop := ∀ lt C, ∀ i ∈ PyCore.itemsE R0 C (src lt), FreshItem i

theorem srcIt_name (t : String) (l : Label) : SrcIt (nameSrc t l) := fun _ _ i hi => by
  simp [nameSrc, PyCore.itemsE] at hi; subst hi; exact ⟨_, _, rfl⟩
theorem srcIt_item (l : Label) (i : Nat) : SrcIt (itemSrc l i) := fun _ _ j hj => by
  simp [itemSrc, PyCore.itemsE] at hj; subst hj; exact ⟨_, _, rfl⟩
theorem srcIt_for (l : Label) : SrcIt (forSrc l) := fun _ _ i hi => by
  simp [forSrc, PyCore.itemsE] at hi; subst hi; exact ⟨_, _, rfl⟩
theorem srcIt_dead : SrcIt deadSrc := fun _ _ i hi => by simp at hi

theorem SrcIt.sim {src : Label → PE} (hs : SrcIt src) (lt : Label) (C : List PyCore.Scope) :
    Sim (PyCore.itemsE R0 C (src lt)) [] := Sim.frs (hs lt C)

/-- The simplification `sim` runs on membership goals. -/
macro "tri_simp" : tactic => `(tactic| simp only [trE, trO, trEs, trA, trKs, trLs, trKVs, trDfs, trAnns,
    trG1, trGs, trT, trItems, trD, trDs, nameSrc, itemSrc, forSrc, blk, nm, setupS,
    itemsE, itemsO, itemsEs, itemsKs, itemsDs, itemsPs, itemsG1, itemsGs, trChain, trScope,
    List.mem_append, List.mem_cons, List.not_mem_nil, List.flatMap_cons, List.flatMap_nil, List.flatMap_append,
    List.append_nil, List.nil_append, pitemsB_append, pitemsB_map, PyCore.itemsB, PyCore.itemsS,
    PyCore.itemsHs, PyCore.itemsE, enone_e, enone_s, enone_h, Option.isSome_none, Bool.false_eq_true,
    ite_false, ite_true, or_false, false_or, pitemsE_recR, pitemsE_ccR, pitemsE_cc, pitemsE_gad,
    pitemsE_starMark, pitemsE_kwMark, pitemsE_constMark, pitemsE_constMarks, pitemsE_marks,
    pitemsE_paramMark, pitemsE_boolChain, pitemsE_cmpOps, pitemsB_ifsNest, pitemsS_dead, pitemsS_stuckAt,
    pitemsS_setupS, pitemsE_deadSrc, dflt_mk, ann_mk, List.flatMap_map, List.map_cons, List.map_nil,
    trMarks_eq, constMarks_eq, flatMap_nil_fun])

/-- `simcat p₁ … pₙ` appends the `Sim` facts `pᵢ`. -/
syntax "simcat" (ppSpace colGt term:max)+ : term
macro_rules
  | `(simcat $p) => `($p)
  | `(simcat $p $ps*) => `(Sim.app $p (simcat $ps*))

/-- Close a `Sim` goal from `Sim` facts about its parts, in any order. -/
macro "t1sim" ps:(ppSpace colGt term:max)+ : tactic => `(tactic|
  exact Sim.congr (simcat $ps*) (by intro i; tri_simp; all_goals grind)
    (by intro j; tri_simp; all_goals grind))

theorem sim_paramBind (C : List Scope) :
    ∀ ps, Sim (PyCore.itemsB R0 (trChain C) (paramBind C ps)) (paramOccs C ps)
  | [] => Sim.nil
  | q :: ps => by
    have ih := sim_paramBind C ps
    simp only [paramBind, paramOccs, List.map_cons] at ih ⊢
    t1sim (Sim.oc q.label 0 (mangle (priv C) q.name) C) ih

theorem sim_forLoop (D : List PyCore.Scope) (l : Label) (iv : Name) (st body u : PS) (hiv : IsFresh iv)
    {B : List Item} (h : Sim (PyCore.itemsB R0 D st ++ PyCore.itemsB R0 D body ++ PyCore.itemsB R0 D u) B) :
    Sim (PyCore.itemsB R0 D (forLoop l iv st body u)) B := by
  have hv : Sim [.occ (sub l 18) iv D] [] := Sim.frs (by simpa [FreshItem] using hiv)
  simp only [forLoop]
  t1sim h hv (Sim.fr (sub l 10) "g" l D) (Sim.fr (sub l 13) "g" l D) (Sim.fr (sub l 15) "v" l D)
    (Sim.fr (sub l 19) "s" l D) (Sim.fr (sub l 21) "g" l D)

theorem sim_compWrap (D : List PyCore.Scope) (l : Label) (k : CompKind) (loops : PS) {B : List Item}
    (h : Sim (PyCore.itemsB R0 D loops) B) : Sim (PyCore.itemsB R0 D (compWrap l k loops)) B := by
  unfold compWrap; split
  · exact h
  · t1sim h (Sim.fr (sub l 4) "acc" l D) (Sim.fr (sub l 6) "acc" l D)

theorem sim_compElt (D : List PyCore.Scope) (l : Label) (k : CompKind) (es : List PE) {B : List Item}
    (h : Sim (es.flatMap (PyCore.itemsE R0 D)) B) : Sim (PyCore.itemsB R0 D (compElt l k es)) B := by
  unfold compElt; split
  · t1sim h
  · t1sim h (Sim.fr (sub l 8) "acc" l D)
  · t1sim h (Sim.fr (sub l 8) "acc" l D)
  · t1sim h (Sim.fr (sub l 8) "acc" l D)
  · t1sim h

mutual
theorem trE_items (C : List Scope) : ∀ e, Sim (PyCore.itemsE R0 (trChain C) (trE C e)) (itemsE C e)
  | .const l c => by t1sim Sim.nil
  | .name l x => by t1sim (Sim.oc l 0 (mangle (priv C) x) C)
  | .bin l op a b => by have h1 := trE_items C a; have h2 := trE_items C b; t1sim h1 h2
  | .unary l op a => by have h1 := trE_items C a; t1sim h1
  | .boolop l op es => by have h1 := trEs_items C es; t1sim h1
  | .compare l a ops es => by
    have h1 := trE_items C a; have h2 := trLs_items C es
    simp only [trE, pitemsE_cmpChain]; t1sim h1 h2
  | .ifexp l c a b => by
    have h1 := trE_items C c; have h2 := trE_items C a; have h3 := trE_items C b; t1sim h1 h2 h3
  | .call l f args kws => by
    have h1 := trE_items C f; have h2 := trA_items C args; have h3 := trKs_items C kws; t1sim h1 h2 h3
  | .attr l e a => by have h1 := trE_items C e; t1sim h1
  | .sub l e i => by have h1 := trE_items C e; have h2 := trE_items C i; t1sim h1 h2
  | .slice l a b c => by
    have h1 := trO_items C l 1 a; have h2 := trO_items C l 2 b; have h3 := trO_items C l 3 c; t1sim h1 h2 h3
  | .star l e => by have h1 := trE_items C e; t1sim h1
  | .list l es => by have h1 := trA_items C es; t1sim h1
  | .tuple l es => by have h1 := trA_items C es; t1sim h1
  | .set l es => by have h1 := trA_items C es; t1sim h1
  | .dict l kvs => by have h1 := trKVs_items C kvs; t1sim h1
  | .lam l ps b => by
    have h1 := trPs_items C ps
    have h4 := sim_paramBind (.lam l ps b :: C) ps; have h5 := trE_items (.lam l ps b :: C) b
    t1sim h1 (Sim.fn1 l C (.lam l ps b)) (Sim.fr (sub l 1) "a" l (trChain (.lam l ps b :: C))) h4 h5
  | .comp l k es gs => by
    have h1 := trG1_items C gs
    have h3 := trEs_items (.comp l k es gs :: C) es
    have h2 := sim_compWrap (trChain (.comp l k es gs :: C)) l k _
      (trGs_items (.comp l k es gs :: C) (fresh "i" l) (fresh_isFresh "i" l) true gs _
        (sim_compElt (trChain (.comp l k es gs :: C)) l k _ h3))
    simp only [trE]
    split
    · rename_i hg
      simp only [List.isEmpty_iff] at hg; subst hg
      simp only [trChain, trScope, trGs, itemsGs, List.nil_append] at h2 ⊢
      t1sim h2 (Sim.fn1 l C (.comp l k es [])) (Sim.fr (sub l 1) "i" l (trChain (.comp l k es [] :: C)))
    · simp only [trChain, trScope] at h2 ⊢
      t1sim h1 h2 (Sim.fn1 l C (.comp l k es gs)) (Sim.fr (sub l 1) "i" l (trChain (.comp l k es gs :: C)))
  | .walrus l x e => by have h1 := trE_items C e; t1sim (Sim.oc l 0 (mangle (priv C) x) C) h1
  | .yield l e => by have h1 := trO_items C l 1 e; t1sim h1
  | .yieldFrom l e => by have h1 := trE_items C e; t1sim h1
  | .fstr l es => by have h1 := trEs_items C es; t1sim h1
  | .fmt l e cv sp => by
    have h1 := trE_items C e
    cases sp with
    | none => simp only [trE]; split <;> t1sim h1
    | some s =>
      have h2 := trE_items C s
      simp only [trE]; split <;> t1sim h1 h2
theorem trO_items (C : List Scope) (l : Label) (k : Nat) : ∀ o,
    Sim (PyCore.itemsE R0 (trChain C) (trO C l k o)) (itemsO C o)
  | none => by t1sim Sim.nil
  | some e => by have h1 := trE_items C e; t1sim h1
theorem trEs_items (C : List Scope) : ∀ es,
    Sim ((trEs C es).flatMap (PyCore.itemsE R0 (trChain C))) (itemsEs C es)
  | [] => by t1sim Sim.nil
  | e :: es => by have h1 := trE_items C e; have h2 := trEs_items C es; t1sim h1 h2
theorem trA_items (C : List Scope) : ∀ es,
    Sim ((trA C es).flatMap (PyCore.itemsE R0 (trChain C))) (itemsEs C es)
  | [] => by t1sim Sim.nil
  | e :: es => by
    have h1 := trE_items C e; have h2 := trA_items C es
    rw [trA_cons, List.flatMap_cons, pitemsE_unstar]; simp only [itemsEs]; exact Sim.app h1 h2
theorem trKs_items (C : List Scope) : ∀ ks,
    Sim ((trKs C ks).flatMap (PyCore.itemsE R0 (trChain C))) (itemsKs C ks)
  | [] => by t1sim Sim.nil
  | .mk l x e :: ks => by have h1 := trE_items C e; have h2 := trKs_items C ks; t1sim h1 h2
theorem trLs_items (C : List Scope) : ∀ es,
    Sim ((trLs C es).flatMap fun x => PyCore.itemsE R0 (trChain C) x.2) (itemsEs C es)
  | [] => by t1sim Sim.nil
  | e :: es => by have h1 := trE_items C e; have h2 := trLs_items C es; t1sim h1 h2
theorem trKVs_items (C : List Scope) : ∀ kvs,
    Sim ((trKVs C kvs).flatMap (PyCore.itemsE R0 (trChain C))) (itemsDs C kvs)
  | [] => by t1sim Sim.nil
  | .mk (some k) v :: kvs => by
    have h1 := trE_items C k; have h2 := trE_items C v; have h3 := trKVs_items C kvs; t1sim h1 h2 h3
  | .mk none v :: kvs => by have h2 := trE_items C v; have h3 := trKVs_items C kvs; t1sim h2 h3
theorem trPs_items (C : List Scope) : ∀ ps,
    Sim ((trDfs C ps).flatMap (PyCore.itemsE R0 (trChain C)) ++
      (trAnns C ps).flatMap (PyCore.itemsE R0 (trChain C))) (itemsPs C ps)
  | [] => by t1sim Sim.nil
  | .mk l x k d a :: ps => by
    have h3 := trPs_items C ps
    cases d with
    | none =>
      cases a with
      | none => t1sim h3
      | some a => have h2 := trE_items C a; t1sim h2 h3
    | some d =>
      have h1 := trE_items C d
      cases a with
      | none => t1sim h1 h3
      | some a => have h2 := trE_items C a; t1sim h1 h2 h3
theorem trG1_items (C : List Scope) : ∀ gs,
    Sim (PyCore.itemsE R0 (trChain C) (trG1 C gs)) (itemsG1 C gs)
  | [] => by t1sim Sim.nil
  | .mk _ _ i _ :: _ => by have h1 := trE_items C i; t1sim h1
theorem trGs_items (C : List Scope) (it : Name) (hit : IsFresh it) : ∀ (first : Bool) (gs : List Gen)
    (inner : PS) {B : List Item}, Sim (PyCore.itemsB R0 (trChain C) inner) B →
    Sim (PyCore.itemsB R0 (trChain C) (trGs C it first gs inner)) (itemsGs C first gs ++ B)
  | _, [], inner, B, h => by simpa [trGs, itemsGs] using h
  | first, .mk lg t i ifs :: gs, inner, B, h => by
    have h1 := trE_items C i
    have h2 := trT_items C (forSrc lg) (srcIt_for lg) t (trE_items C t)
    have h3 := trEs_items C ifs
    have h4 := trGs_items C it hit false gs inner h
    cases first
    · have h5 := sim_forLoop (trChain C) lg (fresh "j" lg) (trT C (forSrc lg) t (trE C t))
        (ifsNest lg (trEs C ifs) (trGs C it false gs inner)) [] (fresh_isFresh "j" lg)
        (B := itemsE C t ++ itemsEs C ifs ++ (itemsGs C false gs ++ B)) (by t1sim h2 h3 h4)
      simp only [trGs, itemsGs]
      t1sim h1 h5 (Sim.fr (sub lg 0) "j" lg (trChain C))
    · have h5 := sim_forLoop (trChain C) lg it (trT C (forSrc lg) t (trE C t))
        (ifsNest lg (trEs C ifs) (trGs C it false gs inner)) [] hit
        (B := itemsE C t ++ itemsEs C ifs ++ (itemsGs C false gs ++ B)) (by t1sim h2 h3 h4)
      simp only [trGs, itemsGs]
      t1sim h5
theorem trT_items (C : List Scope) (src : Label → PE) (hs : SrcIt src) : ∀ t,
    Sim (PyCore.itemsE R0 (trChain C) (trE C t)) (itemsE C t) →
    Sim (PyCore.itemsB R0 (trChain C) (trT C src t (trE C t))) (itemsE C t)
  | .name lt x, _ => by t1sim (Sim.oc lt 0 (mangle (priv C) x) C) (hs.sim lt (trChain C))
  | .attr lt o a, _ => by have h1 := trE_items C o; t1sim h1 (hs.sim lt (trChain C))
  | .sub lt o i, _ => by
    have h1 := trE_items C o; have h2 := trE_items C i; t1sim h1 h2 (hs.sim lt (trChain C))
  | .tuple lt ts, _ => by
    have h1 := trItems_items C lt 0 ts
    t1sim h1 (hs.sim lt (trChain C)) (Sim.fr (sub lt 1) "u" lt (trChain C))
  | .list lt ts, _ => by
    have h1 := trItems_items C lt 0 ts
    t1sim h1 (hs.sim lt (trChain C)) (Sim.fr (sub lt 1) "u" lt (trChain C))
  | .star ls e, _ => by have h1 := trT_items C src hs e (trE_items C e); t1sim h1
  | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1 | .ifexp .., h1
  | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1 | .comp .., h1
  | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    simp only [trT]; simpa [PyCore.itemsB, PyCore.itemsS] using h1
theorem trItems_items (C : List Scope) (lt : Label) : ∀ (i : Nat) (ts : List Expr),
    Sim (PyCore.itemsB R0 (trChain C) (trItems C lt i ts)) (itemsEs C ts)
  | _, [] => by t1sim Sim.nil
  | i, t :: ts => by
    have h1 := trT_items C (itemSrc lt i) (srcIt_item lt i) t (trE_items C t)
    have h2 := trItems_items C lt (i + 1) ts
    rw [trItems_cons, pitemsB_append, pitemsB_unstar]; simp only [itemsEs]; exact Sim.app h1 h2
end

mutual
theorem trD_items (C : List Scope) : ∀ t, Sim (PyCore.itemsE R0 (trChain C) (trE C t)) (itemsE C t) →
    Sim (PyCore.itemsB R0 (trChain C) (trD C t (trT C deadSrc t (trE C t)))) (itemsE C t)
  | .name lt x, _ => by t1sim (Sim.oc lt 0 (mangle (priv C) x) C)
  | .attr lt o a, _ => by have h1 := trE_items C o; t1sim h1
  | .sub lt o i, _ => by have h1 := trE_items C o; have h2 := trE_items C i; t1sim h1 h2
  | .tuple lt ts, _ => by have h1 := trDs_items C ts; t1sim h1
  | .list lt ts, _ => by have h1 := trDs_items C ts; t1sim h1
  | .star .., h1 | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1
  | .ifexp .., h1 | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1
  | .comp .., h1 | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    have h2 := trT_items C deadSrc srcIt_dead _ h1
    simp only [trD]; simpa [PyCore.itemsB] using h2
theorem trDs_items (C : List Scope) : ∀ ts, Sim (PyCore.itemsB R0 (trChain C) (trDs C ts)) (itemsEs C ts)
  | [] => by simp only [trDs, itemsEs, PyCore.itemsB]; exact Sim.nil
  | t :: ts => by
    have h1 := trD_items C t (trE_items C t); have h2 := trDs_items C ts
    simp only [trDs, itemsEs, pitemsB_append]; exact Sim.app h1 h2
end

theorem trAug_items (C : List Scope) (l : Label) (t : Expr) :
    Sim (PyCore.itemsB R0 (trChain C) (trAug C l t (trT C deadSrc t (trE C t))).1 ++
      PyCore.itemsB R0 (trChain C) (trAug C l t (trT C deadSrc t (trE C t))).2) (itemsE C t) := by
  have h0 := trT_items C deadSrc srcIt_dead t (trE_items C t)
  cases t with
  | name lt x =>
    simp only [trAug]
    t1sim (Sim.oc lt 1 (mangle (priv C) x) C) (Sim.oc lt 2 (mangle (priv C) x) C)
      (Sim.fr (sub lt 0) "g" l (trChain C)) (Sim.fr (sub lt 3) "v" l (trChain C))
  | attr lt e a =>
    have h2 := trE_items C e
    simp only [trAug]
    t1sim h2 (Sim.fr (sub lt 4) "o" l (trChain C)) (Sim.fr (sub lt 5) "g" l (trChain C))
      (Sim.fr (sub lt 7) "o" l (trChain C)) (Sim.fr (sub lt 10) "o" l (trChain C))
      (Sim.fr (sub lt 11) "v" l (trChain C))
  | sub lt e i =>
    have h2 := trE_items C e; have h3 := trE_items C i
    simp only [trAug]
    t1sim h2 h3 (Sim.fr (sub lt 4) "o" l (trChain C)) (Sim.fr (sub lt 5) "k" l (trChain C))
      (Sim.fr (sub lt 6) "g" l (trChain C)) (Sim.fr (sub lt 8) "o" l (trChain C))
      (Sim.fr (sub lt 9) "k" l (trChain C)) (Sim.fr (sub lt 11) "o" l (trChain C))
      (Sim.fr (sub lt 12) "k" l (trChain C)) (Sim.fr (sub lt 13) "v" l (trChain C))
  | _ => simp only [trAug]; t1sim h0

theorem annBare_items (C : List Scope) (t : Expr) :
    Sim (PyCore.itemsB R0 (trChain C) (annBare C t (trT C deadSrc t (trE C t))) ++
      PyCore.itemsB R0 (trChain C) (annBind C t)) (itemsE C t) := by
  have h0 := trT_items C deadSrc srcIt_dead t (trE_items C t)
  cases t with
  | name lt x => simp only [annBare, annBind]; t1sim (Sim.oc lt 60 (mangle (priv C) x) C)
  | attr lt e a => have h2 := trE_items C e; simp only [annBare, annBind]; t1sim h2
  | sub lt e i => have h2 := trE_items C e; have h3 := trE_items C i; simp only [annBare, annBind]; t1sim h2 h3
  | _ => simp only [annBare, annBind]; t1sim h0

theorem sim_occs (C : List Scope) (l k : Label) (hk : k < 64) (f : Name → PyCore.Stmt)
    (hf : ∀ x, PyCore.itemsS R0 (trChain C) (f x) = [.occ (sub l k) x (trChain C)]) :
    ∀ xs : List Name, Sim (PyCore.itemsB R0 (trChain C) (xs.map f)) (xs.map fun x => .occ l x C)
  | [] => Sim.nil
  | x :: xs => by
    have := sim_occs C l k hk f hf xs
    simp only [List.map_cons, PyCore.itemsB, hf]
    t1sim (Sim.oc l k x C hk) this

theorem Sim.consFresh {i : PyCore.Item} {A : List PyCore.Item} {B : List Item} (hi : FreshItem i)
    (h : Sim A B) : Sim (i :: A) B := by
  have := Sim.app (Sim.frs (A := [i]) (by simpa using hi)) h
  simpa using this

/-- The aliases of an import: one that binds a name is an occurrence at the alias's node
`sub a.l 0`; the rest is fresh. -/
theorem sim_aliases (C : List Scope) (g : Alias → PyCore.Stmt)
    (hg : ∀ a, ∀ i ∈ PyCore.itemsS R0 (trChain C) (g a), FreshItem i ∨
      ((a.name == "*") = false ∧ i = .occ (sub a.l 0) (mangle (priv C) a.bound) (trChain C)))
    (hg2 : ∀ a, (a.name == "*") = false → .occ (sub a.l 0) (mangle (priv C) a.bound) (trChain C) ∈
      PyCore.itemsS R0 (trChain C) (g a)) :
    ∀ al : List Alias, Sim (PyCore.itemsB R0 (trChain C) (al.map g))
      ((bindingAliases al).map fun a => .occ a.l (mangle (priv C) a.bound) C)
  | [] => Sim.nil
  | a :: al => by
    have ih := sim_aliases C g hg hg2 al
    simp only [List.map_cons, PyCore.itemsB, bindingAliases, List.filter_cons] at ih ⊢
    by_cases h : a.name == "*"
    · have h' : (a.name != "*") = false := by simp [bne, h]
      simp only [h', Bool.false_eq_true, ite_false]
      exact Sim.app (Sim.frs fun i hi => (hg a i hi).resolve_right (by simp [h])) ih
    · have h' : (a.name != "*") = true := by simpa [bne] using h
      have hf : (a.name == "*") = false := by simpa using h
      simp only [h', ite_true, List.map_cons]
      have h1 : Sim (PyCore.itemsS R0 (trChain C) (g a)) [.occ a.l (mangle (priv C) a.bound) C] :=
        ⟨fun i hi => (hg a i hi).imp id fun ⟨_, he⟩ =>
            ⟨_, List.mem_singleton_self _, by subst he; exact ⟨⟨0, by decide, rfl⟩, rfl, rfl⟩⟩,
         fun j hj => by
          simp only [List.mem_singleton] at hj; subst hj
          exact ⟨_, hg2 a hf, ⟨0, by decide, rfl⟩, rfl, rfl⟩⟩
      have := Sim.app h1 ih
      simpa using this

theorem sim_amap (C : List Scope) : ∀ al : List Alias,
    Sim (PyCore.itemsB R0 (trChain C) (al.map fun a =>
        .assign (sub a.l 0) (mangle (priv C) a.bound) (.const (sub a.l 1) "$none")))
      (al.map fun a => .occ a.l (mangle (priv C) a.bound) C)
  | [] => Sim.nil
  | a :: al => by
    have := sim_amap C al
    simp only [List.map_cons]
    t1sim (Sim.oc a.l 0 (mangle (priv C) a.bound) C) this

mutual
theorem trS_items (C : List Scope) : ∀ s,
    Sim (PyCore.itemsS R0 (trChain C) (trS C s)) (itemsS C s)
  | .expr l e => by have h1 := trE_items C e; simp only [trS, itemsS]; t1sim h1
  | .assign l ts e => by
    have h1 := trE_items C e
    have h2 : ∀ ts, Sim (PyCore.itemsB R0 (trChain C) (trTs C (nameSrc "t" l) ts)) (itemsEs C ts) := by
      intro ts; induction ts with
      | nil => simp only [trTs, itemsEs, PyCore.itemsB]; exact Sim.nil
      | cons t ts ih =>
        have := trT_items C (nameSrc "t" l) (srcIt_name "t" l) t (trE_items C t)
        simp only [trTs, itemsEs, pitemsB_append]; exact Sim.app this ih
    have h3 := h2 ts
    simp only [trS, itemsS]; t1sim h1 h3 (Sim.fr (sub l 1) "t" l (trChain C))
  | .augassign l t op e => by
    have h1 := trAug_items C l t; have h2 := trE_items C e
    simp only [trS, itemsS]
    t1sim h1 h2 (Sim.fr (sub l 1) "v" l (trChain C)) (Sim.fr (sub l 3) "g" l (trChain C))
  | .annassign l t a v => by
    have h1 := trE_items C a
    have h3 := trT_items C (nameSrc "t" l) (srcIt_name "t" l) t (trE_items C t)
    have h4 := annBare_items C t
    have h5 : Sim (PyCore.itemsB R0 (trChain C) (annT C l t)) [] := Sim.frs (pitemsB_annT _ C l t)
    cases v with
    | none =>
      cases hf : isTop C
      · simp only [trS, itemsS, itemsO, hf]; t1sim h1 h4
      · simp only [trS, itemsS, itemsO, hf]; t1sim h1 h4 h5 (Sim.fr (sub l 6) "n" l (trChain C))
    | some v =>
      have h2 := trE_items C v
      cases hf : isTop C
      · simp only [trS, itemsS, itemsO, hf]; t1sim h1 h2 h3 (Sim.fr (sub l 1) "t" l (trChain C))
      · simp only [trS, itemsS, itemsO, hf]
        t1sim h1 h2 h3 h5 (Sim.fr (sub l 1) "t" l (trChain C)) (Sim.fr (sub l 6) "n" l (trChain C))
  | .del l ts => by have h1 := trDs_items C ts; simp only [trS, itemsS]; t1sim h1
  | .ite l c t u => by
    have h1 := trE_items C c; have h2 := trB_items C t; have h3 := trB_items C u
    simp only [trS, itemsS]; t1sim h1 h2 h3
  | .while l c b u => by
    have h1 := trE_items C c; have h2 := trB_items C b; have h3 := trB_items C u
    simp only [trS, itemsS]; t1sim h1 h2 h3
  | .for l t it b u => by
    have h1 := trE_items C it
    have h2 := trT_items C (forSrc l) (srcIt_for l) t (trE_items C t)
    have h3 := trB_items C b; have h4 := trB_items C u
    have h5 := sim_forLoop (trChain C) l (fresh "i" l) (trT C (forSrc l) t (trE C t)) (trB C b) (trB C u)
      (fresh_isFresh "i" l) (B := itemsE C t ++ itemsB C b ++ itemsB C u) (by t1sim h2 h3 h4)
    simp only [trS, itemsS]
    t1sim h1 h5 (Sim.fr (sub l 1) "i" l (trChain C))
  | .brk l => by simp only [trS, itemsS]; t1sim Sim.nil
  | .cont l => by simp only [trS, itemsS]; t1sim Sim.nil
  | .pass l => by simp only [trS, itemsS]; t1sim Sim.nil
  | .ret l e => by have h1 := trO_items C l 1 e; simp only [trS, itemsS]; t1sim h1
  | .defn l f ps b ds r => by
    have h1 := trEs_items C ds; have h2 := trPs_items C ps
    have h4 := sim_paramBind (.fn l f ps b :: C) ps; have h5 := trB_items (.fn l f ps b :: C) b
    have hk := flatMap_mem_iff (f := PyCore.itemsE R0 (trChain C)) (trAnnK_all C · ps)
    have h3 : Sim ((trDfs C ps ++ (trAnnK C .pos ps ++ trAnnK C .posonly ps ++ trAnnK C .vararg ps ++
        trAnnK C .kwonly ps ++ trAnnK C .kwarg ps)).flatMap (PyCore.itemsE R0 (trChain C))) (itemsPs C ps) :=
      Sim.congr h2 (fun i => by have := hk i; simp only [List.flatMap_append, List.mem_append] at *; grind)
        (fun _ => Iff.rfl)
    cases r with
    | none =>
      simp only [trS, itemsS]
      refine Sim.congr (simcat h1 h3 (Sim.oc l 0 (mangle (priv C) f) C) (Sim.fn1 l C (.fn l f ps b))
        (Sim.fr (sub l 1) "a" l (trChain (.fn l f ps b :: C))) h4 h5) (fun i => ?_) (fun j => ?_) <;>
        tri_simp <;> grind
    | some r =>
      have h6 := trE_items C r
      simp only [trS, itemsS]
      refine Sim.congr (simcat h1 h3 h6 (Sim.oc l 0 (mangle (priv C) f) C) (Sim.fn1 l C (.fn l f ps b))
        (Sim.fr (sub l 1) "a" l (trChain (.fn l f ps b :: C))) h4 h5) (fun i => ?_) (fun j => ?_) <;>
        tri_simp <;> grind
  | .cls l x bs ks b ds => by
    have h1 := trEs_items C ds; have h2 := trA_items C bs
    have h3 := trKs_items C ks; have h4 := trB_items (.cl l x b :: C) b
    have h5 : Sim (PyCore.classImplicit.map fun y => .occ (sub l 1) y (trChain (.cl l x b :: C)))
        (PyCore.classImplicit.map fun y => .occ l y (.cl l x b :: C)) := by
      simp only [PyCore.classImplicit, List.map_cons, List.map_nil]
      t1sim (Sim.oc l 1 "__name__" (.cl l x b :: C)) (Sim.oc l 1 "__module__" (.cl l x b :: C))
        (Sim.oc l 1 "__qualname__" (.cl l x b :: C))
    simp only [trS, itemsS]
    simp only [trChain, trScope] at h4 h5
    t1sim h1 h2 h3 (Sim.oc l 1 (mangle (priv C) x) C) h5 h4
  | .glob l xs => by
    have := sim_occs C l 1 (by decide) (fun x => .glob (sub l 1) x) (fun _ => rfl) (xs.map (mangle (priv C)))
    simp only [List.map_map, Function.comp_def] at this
    simp only [trS, itemsS]; t1sim this
  | .nonloc l xs => by
    have := sim_occs C l 1 (by decide) (fun x => .nonloc (sub l 1) x) (fun _ => rfl) (xs.map (mangle (priv C)))
    simp only [List.map_map, Function.comp_def] at this
    simp only [trS, itemsS]; t1sim this
  | .tryE l b hs u => by
    have h1 := trB_items C b; have h2 := trHs_items C hs; have h3 := trB_items C u
    simp only [trS, itemsS]; t1sim h1 h2 h3
  | .raise l none none => by simp only [trS, itemsS, itemsO]; t1sim Sim.nil
  | .raise l (some e) none => by have h1 := trE_items C e; simp only [trS, itemsS, itemsO]; t1sim h1
  | .raise l (some e) (some c) => by
    have h1 := trE_items C e; have h2 := trE_items C c; simp only [trS, itemsS, itemsO]; t1sim h1 h2
  | .raise l none (some c) => by have h2 := trE_items C c; simp only [trS, itemsS, itemsO]; t1sim h2
  | .imp l al => by
    simp only [trS, itemsS, blk, PyCore.itemsS, PyCore.itemsHs, PyCore.itemsB, List.append_nil, enone_s,
      Option.isSome_none, Bool.false_eq_true, ite_false]
    refine sim_aliases C _ (fun a i hi => ?_) (fun a ha => ?_) al
    · split at hi <;> simp_all [PyCore.itemsS, stuckAt, PyCore.itemsE]
    · simp [ha, PyCore.itemsS]
  | .impFrom l m al lvl => by
    simp only [trS, itemsS]
    split
    · have := sim_amap C (bindingAliases al)
      t1sim this
    · simp only [blk, PyCore.itemsS, PyCore.itemsHs, PyCore.itemsB, List.append_nil, enone_s,
        Option.isSome_none, Bool.false_eq_true, ite_false, PyCore.itemsE, pitemsE_cc, List.flatMap_nil,
        List.nil_append]
      refine Sim.consFresh ⟨_, _, rfl⟩ (sim_aliases C _ (fun a i hi => ?_) (fun a ha => ?_) al)
      · split at hi
        · simp_all [PyCore.itemsS, PyCore.itemsE, nm, FreshItem, fresh_isFresh]
        · simp only [PyCore.itemsS, PyCore.itemsE, nm, pitemsE_cc, enone_s, enone_e, Option.isSome_none,
            Bool.false_eq_true, ite_false, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · rename_i hn; exact .inr ⟨by simpa using hn, rfl⟩
          · exact .inl ⟨_, _, rfl⟩
      · simp [ha, PyCore.itemsS]
  | .assert l t m => by
    have h1 := trE_items C t
    cases m with
    | none => simp only [trS, itemsS, itemsO]; t1sim h1
    | some m => have h2 := trE_items C m; simp only [trS, itemsS, itemsO]; t1sim h1 h2
theorem trHs_items (C : List Scope) : ∀ hs,
    Sim (PyCore.itemsHs R0 (trChain C) (trHs C hs)) (itemsHs C hs)
  | [] => by simp only [trHs, itemsHs]; t1sim Sim.nil
  | .mk l ty x b :: hs => by
    have h2 := trB_items C b; have h3 := trHs_items C hs
    have hx : Sim [.occ (sub l 0) ((x.map (mangle (priv C))).getD (fresh "e" l)) (trChain C)]
        (x.map fun x => Item.occ l (mangle (priv C) x) C).toList := by
      cases x with
      | none => exact Sim.fr _ "e" l _
      | some x => exact Sim.oc l 0 _ C
    cases ty with
    | none => simp only [trHs, itemsHs, itemsO]; t1sim h2 h3 hx
    | some t =>
      have h1 := trE_items C t
      simp only [trHs, itemsHs, itemsO]; t1sim h1 h2 h3 hx
theorem trB_items (C : List Scope) : ∀ ss, Sim (PyCore.itemsB R0 (trChain C) (trB C ss)) (itemsB C ss)
  | [] => by simp only [trB, itemsB]; exact Sim.nil
  | s :: ss => by
    have h1 := trS_items C s; have h2 := trB_items C ss
    simp only [trB, itemsB]; t1sim h1 h2
end
/-- The items of ⌊p⌋ are, up to fresh names, the images of those of `p`. -/
theorem items_tr (p : List Stmt) : Sim (PyCore.itemsB R0 [] (tr p)) (itemsB [] p) := by
  have := trB_items [] p
  simpa [tr, PyCore.itemsB, trChain] using this

theorem fresh_dot {x : Name} (h : IsFresh x) : x.toList.head? = some '.' := by
  obtain ⟨t, l, rfl⟩ := h; simp [fresh]

/-- No name of `p` starts with a dot, as no Python identifier, mangled or not, does
(`export_surf.py` writes identifiers only), so no name of `p` is fresh. -/
def NoDot (p : List Stmt) : Prop := ∀ l x C, Item.occ l x C ∈ itemsB [] p → x.toList.head? ≠ some '.'

def Scope.isCl : Scope → Bool
  | .cl .. => true
  | _ => false

/-- Each scope becomes a scope of the same sort (a class a class, any other a
function) at the node `sub l 1` made for it. -/
theorem trScope_sort (C : List Scope) (S : Scope) :
    (S.isCl ∧ ∃ ss, trScope C S = .cl (sub S.label 1) ss) ∨
      (S.isCl = false ∧ ∃ c x b, trScope C S = .fn (sub S.label 1) c x b) := by
  cases S <;> simp [Scope.isCl, trScope, Scope.label]

/-- Every generator expression of `p` has one element, as CPython's parser makes it
(`GeneratorExp` has one `elt`). -/
def GenOk (p : List Stmt) : Prop := ∀ l C S, Item.fn l C S ∈ itemsB [] p → S.genOk = true

/-- (T1) ⌊·⌋ maps each scope to a scope (`trScope`, `trScope_sort`), keeps the
classification of each occurrence of a name (on every chain, `cls_tr`) and the kind
of each function, and adds only fresh names: (a) every occurrence of `p` has an image
in ⌊p⌋, at a node made for it, in the image of its scope chain, classified alike;
(b) every other occurrence of ⌊p⌋ is of a fresh name; (c) every function of `p` has
its image in ⌊p⌋, of the same kind; (d) ⌊p⌋ has no other function. -/
theorem translation_keeps_scopes (p : List Stmt) (hp : NoDot p) (hg : GenOk p) :
    (∀ l x C, Item.occ l x C ∈ itemsB [] p →
      ∃ k, k < 64 ∧ PyCore.Item.occ (sub l k) x (trChain C) ∈ PyCore.itemsB R0 [] (tr p) ∧
        PyCore.clsOf (trChain C) x = clsOf C x) ∧
    (∀ l' x C', PyCore.Item.occ l' x C' ∈ PyCore.itemsB R0 [] (tr p) →
      IsFresh x ∨ ∃ l k C, k < 64 ∧ l' = sub l k ∧ C' = trChain C ∧ Item.occ l x C ∈ itemsB [] p) ∧
    (∀ l C S, Item.fn l C S ∈ itemsB [] p →
      PyCore.Item.fn (sub l 1) (trScope C S) ∈ PyCore.itemsB R0 [] (tr p) ∧
        (trScope C S).kind = S.kind C) ∧
    (∀ l' S', PyCore.Item.fn l' S' ∈ PyCore.itemsB R0 [] (tr p) →
      ∃ l C S, l' = sub l 1 ∧ S' = trScope C S ∧ Item.fn l C S ∈ itemsB [] p) := by
  have h := items_tr p
  refine ⟨fun l x C hj => ?_, fun l' x C' hi => ?_, fun l C S hj => ?_, fun l' S' hi => ?_⟩
  · obtain ⟨i, hi, hij⟩ := h.complete _ hj
    cases i with
    | occ l' x' C' =>
      obtain ⟨⟨k, hk, rfl⟩, rfl, rfl⟩ := hij
      exact ⟨k, hk, hi, cls_tr (fun hx => hp l _ C hj (fresh_dot hx)) C⟩
    | fn => exact hij.elim
  · rcases h.sound _ hi with hf | ⟨j, hj, hij⟩
    · exact .inl hf
    · cases j with
      | occ l x' C =>
        obtain ⟨⟨k, hk, rfl⟩, rfl, rfl⟩ := hij
        exact .inr ⟨l, k, C, hk, rfl, rfl, hj⟩
      | fn => exact hij.elim
  · obtain ⟨i, hi, hij⟩ := h.complete _ hj
    cases i with
    | fn l' S' => obtain ⟨rfl, rfl⟩ := hij; exact ⟨hi, kind_tr C S (hg l C S hj)⟩
    | occ => exact hij.elim
  · rcases h.sound _ hi with hf | ⟨j, hj, hij⟩
    · exact hf.elim
    · cases j with
      | fn l C S => obtain ⟨rfl, rfl⟩ := hij; exact ⟨l, C, S, rfl, rfl, hj⟩
      | occ => exact hij.elim



end Surf
