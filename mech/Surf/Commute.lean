/-
The commutation of the translation with edits, `⌊editB R p⌋ = editB (trEdit R p) ⌊p⌋`
(`tr_edit`), the syntactic core of (T3).

The local theorem (`trE_edit`, `trS_edit`, `trB_edit`, …) holds for any PyCore edit `R'`
that replaces each PyCore site of `sitesB R C ss` and is `none` at every node the
translation makes for a node outside the sites (`NB`). `trEdit R p` is such an edit when
the labels of `p` are distinct and none is 0 (the module's setup is labelled below 64).

Two conditions on the edit are needed (counterexamples in `SurfTests.lean`): a replacement
keeps the label of the expression it replaces (`KeepsLabels`; a comparison's middle operand
is kept in a cell named by its label), and each augmented assignment's target and its
replacement is a name, an attribute, or a subscript (`regB`; CPython's parser rejects the
others). The outermost `def` or class outside the sites whose qualified name changes is a
PyCore site (`qualCh`).
-/
import Surf.Footprint
import Surf.T1
import PyCore.Theorem

set_option linter.unusedSectionVars false

namespace Surf
open PyCore (Name Label)

section
variable (R : Edit)

/-! ## The labels outside the sites -/

/-- A node `l` with children's labels `rest`, cut if it is a site. -/
def ocut (site : Bool) (l : Label) (rest : List Label) : List Label := if site then [] else l :: rest

mutual
/-- The labels of the nodes outside the sites of `R`. -/
def olabelsE : Expr → List Label
  | .const l _ | .name l _ => ocut (R.e l).isSome l []
  | .bin l _ a b | .sub l a b => ocut (R.e l).isSome l (olabelsE a ++ olabelsE b)
  | .unary l _ a | .attr l a _ | .star l a | .walrus l _ a | .yieldFrom l a =>
    ocut (R.e l).isSome l (olabelsE a)
  | .boolop l _ es | .list l es | .tuple l es | .set l es | .fstr l es =>
    ocut (R.e l).isSome l (olabelsEs es)
  | .compare l a _ es => ocut (R.e l).isSome l (olabelsE a ++ olabelsEs es)
  | .ifexp l c a b => ocut (R.e l).isSome l (olabelsE c ++ olabelsE a ++ olabelsE b)
  | .call l f as ks => ocut (R.e l).isSome l (olabelsE f ++ olabelsEs as ++ olabelsKs ks)
  | .slice l a b c => ocut (R.e l).isSome l (olabelsO a ++ olabelsO b ++ olabelsO c)
  | .dict l kvs => ocut (R.e l).isSome l (olabelsDs kvs)
  | .lam l ps b => ocut (R.e l).isSome l (olabelsPs ps ++ olabelsE b)
  | .comp l _ es gs => ocut (R.e l).isSome l (olabelsEs es ++ olabelsGs gs)
  | .yield l e => ocut (R.e l).isSome l (olabelsO e)
  | .fmt l e _ s => ocut (R.e l).isSome l (olabelsE e ++ olabelsO s)
def olabelsO : Option Expr → List Label
  | none => []
  | some e => olabelsE e
def olabelsEs : List Expr → List Label
  | [] => []
  | e :: es => olabelsE e ++ olabelsEs es
def olabelsKs : List Kw → List Label
  | [] => []
  | .mk l _ e :: ks => l :: olabelsE e ++ olabelsKs ks
def olabelsDs : List DItem → List Label
  | [] => []
  | .mk k v :: kvs => olabelsO k ++ olabelsE v ++ olabelsDs kvs
def olabelsPs : List Param → List Label
  | [] => []
  | .mk l _ _ d a :: ps => l :: olabelsO d ++ olabelsO a ++ olabelsPs ps
def olabelsGs : List Gen → List Label
  | [] => []
  | .mk l t i ifs :: gs => l :: olabelsE t ++ olabelsE i ++ olabelsEs ifs ++ olabelsGs gs
end

mutual
/-- The outermost `def` and class nodes outside the sites whose qualified name changes
(`qualCh`): PyCore sites, though no Surf sites. -/
def qcS (C : List Scope) : Stmt → List Label
  | .ite l _ t u | .while l _ t u | .for l _ _ t u =>
    if (R.s l).isSome then [] else qcB C t ++ qcB C u
  | .defn l f ps b _ _ =>
    if (R.s l).isSome then [] else if qualCh R C f then [l] else qcB (.fn l f ps b :: C) b
  | .cls l x _ _ b _ =>
    if (R.s l).isSome then [] else if qualCh R C x then [l] else qcB (.cl l x b :: C) b
  | .tryE l b hs u => if (R.s l).isSome then [] else qcB C b ++ qcHs C hs ++ qcB C u
  | _ => []
def qcHs (C : List Scope) : List Handler → List Label
  | [] => []
  | .mk l _ _ b :: hs => (if (R.h l).isSome then [] else qcB C b) ++ qcHs C hs
def qcB (C : List Scope) : List Stmt → List Label
  | [] => []
  | s :: ss => qcS C s ++ qcB C ss
end

mutual
def olabelsS (C : List Scope) : Stmt → List Label
  | .expr l e => ocut (R.s l).isSome l (olabelsE R e)
  | .assign l ts e => ocut (R.s l).isSome l (olabelsEs R ts ++ olabelsE R e)
  | .augassign l t _ e => ocut (R.s l).isSome l (olabelsE R t ++ olabelsE R e)
  | .annassign l t a v => ocut (R.s l).isSome l (olabelsE R t ++ olabelsE R a ++ olabelsO R v)
  | .del l ts => ocut (R.s l).isSome l (olabelsEs R ts)
  | .ite l c t u | .while l c t u =>
    ocut (R.s l).isSome l (olabelsE R c ++ olabelsB C t ++ olabelsB C u)
  | .for l t it b u =>
    ocut (R.s l).isSome l (olabelsE R t ++ olabelsE R it ++ olabelsB C b ++ olabelsB C u)
  | .brk l | .cont l | .pass l | .glob l _ | .nonloc l _ => ocut (R.s l).isSome l []
  | .ret l e => ocut (R.s l).isSome l (olabelsO R e)
  | .defn l f ps b ds r =>
    if (R.s l).isSome then [] else
    (if qualCh R C f then [] else [l]) ++
      (olabelsPs R ps ++ olabelsB (.fn l f ps b :: C) b ++ olabelsEs R ds ++ olabelsO R r) ++
      (if qualCh R C f then qcB R (.fn l f ps b :: C) b else [])
  | .cls l x bs ks b ds =>
    if (R.s l).isSome then [] else
    (if qualCh R C x then [] else [l]) ++
      (olabelsEs R bs ++ olabelsKs R ks ++ olabelsB (.cl l x b :: C) b ++ olabelsEs R ds) ++
      (if qualCh R C x then qcB R (.cl l x b :: C) b else [])
  | .tryE l b hs u => ocut (R.s l).isSome l (olabelsB C b ++ olabelsHs C hs ++ olabelsB C u)
  | .raise l e c => ocut (R.s l).isSome l (olabelsO R e ++ olabelsO R c)
  | .imp l al | .impFrom l _ al _ => ocut (R.s l).isSome l (al.map (·.l))
  | .assert l t m => ocut (R.s l).isSome l (olabelsE R t ++ olabelsO R m)
def olabelsHs (C : List Scope) : List Handler → List Label
  | [] => []
  | .mk l ty _ b :: hs => ocut (R.h l).isSome l (olabelsO R ty ++ olabelsB C b) ++ olabelsHs C hs
def olabelsB (C : List Scope) : List Stmt → List Label
  | [] => []
  | s :: ss => olabelsS C s ++ olabelsB C ss
end

end

/-- `R'` replaces the PyCore site `x`. -/
def PSite.Agrees (R' : PyCore.Edit) : PSite → Prop
  | .e l r => R'.e l = some r
  | .s l r => R'.s l = some r
  | .h l r => R'.h l = some r

/-- `R'` is `none` at every node the translation makes for the Surf node `l`. -/
def NB (R' : PyCore.Edit) (l : Label) : Prop :=
  (∀ k, k < 64 → R'.e (sub l k) = none) ∧ (∀ k, k < 64 → R'.s (sub l k) = none) ∧
    (∀ k, k < 64 → R'.h (sub l k) = none)

theorem nb_e {R' : PyCore.Edit} {l k : Label} (h : NB R' l) (hk : k < 64) : R'.e (sub l k) = none := h.1 k hk
theorem nb_s {R' : PyCore.Edit} {l k : Label} (h : NB R' l) (hk : k < 64) : R'.s (sub l k) = none := h.2.1 k hk
theorem nb_h {R' : PyCore.Edit} {l k : Label} (h : NB R' l) (hk : k < 64) : R'.h (sub l k) = none := h.2.2 k hk

/-! ## Edits of Surf chains and of the nodes the translation makes -/

@[simp] theorem editChain_cons (R : Edit) (S : Scope) (C : List Scope) :
    editChain R (S :: C) = editSc R S :: editChain R C := rfl
@[simp] theorem editChain_nil (R : Edit) : editChain R [] = [] := rfl

@[simp] theorem priv_edit (R : Edit) : ∀ C, priv (editChain R C) = priv C
  | [] => rfl
  | S :: C => by cases S <;> simp [priv, editSc, priv_edit R C]

@[simp] theorem isTop_edit (R : Edit) (C : List Scope) : isTop (editChain R C) = isTop C := by
  cases C with
  | nil => rfl
  | cons S C => cases S <;> rfl

theorem editE_site {R : Edit} {e e' : Expr} (h : R.e e.label = some e') : editE R e = e' := by
  cases e <;> simp_all [editE, Expr.label]

theorem editE_label_none {R : Edit} {e : Expr} (h : R.e e.label = none) : (editE R e).label = e.label := by
  cases e <;> simp_all [editE, Expr.label]

theorem editE_label {R : Edit} (hk : KeepsLabels R) (e : Expr) : (editE R e).label = e.label := by
  cases h : R.e e.label with
  | none => exact editE_label_none h
  | some e' => rw [editE_site h]; exact hk _ _ h

/-- Outside the sites an expression keeps its form: whether it is starred, its marker. -/
theorem starMark_edit {R : Edit} {e : Expr} (h : R.e e.label = none) : starMark (editE R e) = starMark e := by
  cases e <;> simp_all [editE, Expr.label, starMark]

theorem unstar_editE {R : Edit} {e : Expr} (h : R.e e.label = none) :
    unstar (editE R e) = editE R (unstar e) ∨ ∃ l a, e = .star l a ∧ unstar (editE R e) = editE R a := by
  cases e <;> simp_all [editE, Expr.label, unstar]

theorem kwMarks_edit (R : Edit) : ∀ ks, (editKs R ks).map kwMark = ks.map kwMark
  | [] => rfl
  | .mk l x e :: ks => by simp [editKs, kwMark, kwMarks_edit R ks]

theorem editEs_length (R : Edit) : ∀ es, (editEs R es).length = es.length
  | [] => rfl
  | _ :: es => by simp [editEs, editEs_length R es]

theorem editPs_length (R : Edit) : ∀ ps, (editPs R ps).length = ps.length
  | [] => rfl
  | .mk .. :: ps => by simp [editPs, editPs_length R ps]

theorem editGs_isEmpty (R : Edit) (gs : List Gen) : (editGs R gs).isEmpty = gs.isEmpty := by
  cases gs with
  | nil => rfl
  | cons g gs => cases g; rfl

theorem map_editDs {β} (R : Edit) (f : DItem → β) (hf : ∀ k v, f (.mk (editO R k) (editE R v)) = f (.mk k v)) :
    ∀ kvs, (editDs R kvs).map f = kvs.map f
  | [] => rfl
  | .mk k v :: kvs => by simp [editDs, hf, map_editDs R f hf kvs]

theorem paramMark_edit (R : Edit) {C C' : List Scope} (h : priv C' = priv C) :
    ∀ ps, (editPs R ps).map (paramMark C') = ps.map (paramMark C)
  | [] => rfl
  | .mk l x k d a :: ps => by
    have ih := paramMark_edit R h ps
    cases d <;> simp [editPs, editO, paramMark, h, ih, Param.label, Param.name, Param.kind, Param.dflt]

theorem paramBind_edit (R : Edit) {C C' : List Scope} (h : priv C' = priv C) :
    ∀ ps, paramBind C' (editPs R ps) = paramBind C ps
  | [] => rfl
  | .mk l x k d a :: ps => by
    have ih := paramBind_edit R h ps
    simp only [paramBind, editPs, List.map_cons] at ih ⊢
    rw [ih]; simp [h, Param.label, Param.name]

section
variable {R' : PyCore.Edit}

theorem peditB_append : ∀ a b : List PyCore.Stmt,
    PyCore.editB R' (a ++ b) = PyCore.editB R' a ++ PyCore.editB R' b
  | [], _ => rfl
  | s :: a, b => by simp [PyCore.editB, peditB_append a b]

theorem peditB_map {α} (f : α → PyCore.Stmt) : ∀ xs : List α,
    PyCore.editB R' (xs.map f) = xs.flatMap fun x => PyCore.editS R' (f x)
  | [] => rfl
  | x :: xs => by simp [PyCore.editB, peditB_map f xs]

theorem peditE_site {e r : PE} (h : R'.e e.label = some r) : PyCore.editE R' e = r := by
  cases e <;> simp_all [PyCore.editE, PyCore.Expr.label]

theorem peditS_site {s : PyCore.Stmt} {r : PS} (h : R'.s s.label = some r) : PyCore.editS R' s = r := by
  cases s <;> simp_all [PyCore.editS, PyCore.Stmt.label]

theorem peditE_foldl {r : Label} (hn : R'.e r = none) : ∀ (es : List PE) (acc : PE),
    PyCore.editE R' (es.foldl (fun acc e => .bin r "," acc e) acc) =
      (es.map (PyCore.editE R')).foldl (fun acc e => .bin r "," acc e) (PyCore.editE R' acc)
  | [], _ => rfl
  | e :: es, acc => by simp [peditE_foldl hn es, PyCore.editE, hn]

theorem peditE_recR {r : Label} (hn : R'.e r = none) (es : List PE) :
    PyCore.editE R' (recR r es) = recR r (es.map (PyCore.editE R')) := by
  simp [recR, peditE_foldl hn, PyCore.editE, hn]

theorem peditE_ccR {r : Label} (hn : R'.e r = none) (g : String) (es : List PE) :
    PyCore.editE R' (ccR r g es) = ccR r g (es.map (PyCore.editE R')) := by
  simp [ccR, PyCore.editE, hn, peditE_recR hn]

theorem peditE_ccR_sub {l : Label} (h : NB R' l) : ∀ k, k < 64 → ∀ (g : String) (es : List PE),
    PyCore.editE R' (ccR (sub l k) g es) = ccR (sub l k) g (es.map (PyCore.editE R')) :=
  fun k hk g es => peditE_ccR (h.1 k hk) g es
theorem peditE_recR_sub {l : Label} (h : NB R' l) : ∀ k, k < 64 → ∀ (es : List PE),
    PyCore.editE R' (recR (sub l k) es) = recR (sub l k) (es.map (PyCore.editE R')) :=
  fun k hk es => peditE_recR (h.1 k hk) es
theorem peditE_cc {l : Label} (h : NB R' l) : ∀ k, k < 64 → ∀ (g : String) (es : List PE),
    PyCore.editE R' (cc l k g es) = cc l k g (es.map (PyCore.editE R')) :=
  fun k hk g es => peditE_ccR (h.1 k hk) g es
theorem peditE_gad {l : Label} (h : NB R' l) : ∀ k, k < 64 → ∀ (g : Py.Gadget) (es : List PE),
    PyCore.editE R' (gad l k g es) = gad l k g (es.map (PyCore.editE R')) :=
  fun k hk g es => peditE_ccR (h.1 k hk) _ es

/-- A node made for `l` with no site under it is fixed. -/
theorem peditE_starMark {e : Expr} (h : NB R' e.label) : PyCore.editE R' (starMark e) = starMark e := by
  cases e <;> simp only [Expr.label] at h <;> simp [starMark, Expr.label, PyCore.editE, nb_e h (by omega : 57 < 64)]
theorem peditE_kwMark {k : Kw} (h : NB R' (match k with | .mk l _ _ => l)) :
    PyCore.editE R' (kwMark k) = kwMark k := by
  cases k; simp_all [kwMark, PyCore.editE, nb_e h (by omega : 57 < 64)]
theorem peditE_paramMark {q : Param} (C : List Scope) (h : NB R' q.label) :
    PyCore.editE R' (paramMark C q) = paramMark C q := by
  simp [paramMark, PyCore.editE, nb_e h (by omega : 56 < 64)]

theorem peditB_fix {α} (f : α → PyCore.Stmt) : ∀ xs : List α, (∀ x ∈ xs, PyCore.editS R' (f x) = [f x]) →
    PyCore.editB R' (xs.map f) = xs.map f
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.map_cons, PyCore.editB, h x (by simp), peditB_fix f xs (fun y hy => h y (by simp [hy]))]
    rfl

theorem peditB_paramBind (C : List Scope) (ps : List Param) (h : ∀ q ∈ ps, NB R' q.label) :
    PyCore.editB R' (paramBind C ps) = paramBind C ps :=
  peditB_fix _ ps fun q hq => by
    have hq := h q hq
    simp (disch := omega) [PyCore.editB, PyCore.editS, PyCore.editE, dead, hq.1, hq.2.1]

theorem peditE_boolChainIn {l : Label} (hl : NB R' l) (o : Bool) : ∀ xs : List PE,
    PyCore.editE R' (boolChainIn l o xs) = boolChainIn l o (xs.map (PyCore.editE R'))
  | [] => by simp [boolChainIn, peditE_gad hl 1 (by omega)]
  | [_] => by simp [boolChainIn]
  | a :: b :: rest => by
    have ih := peditE_boolChainIn hl o (b :: rest)
    simp only [List.map_cons] at ih
    simp [boolChainIn, PyCore.editE, nb_e hl (by omega : 1 < 64), ih]

theorem peditE_boolChain {l : Label} (hl : NB R' l) (o : Bool) (xs : List PE) :
    PyCore.editE R' (boolChain l o xs) = boolChain l o (xs.map (PyCore.editE R')) := by
  match xs with
  | [] => simp [boolChain, peditE_gad hl 0 (by omega)]
  | [_] => simp [boolChain]
  | a :: b :: rest =>
    have := peditE_boolChainIn hl o (b :: rest)
    simp only [List.map_cons] at this
    simp [boolChain, PyCore.editE, nb_e hl (by omega : 0 < 64), this]

theorem peditE_cmpChain {l : Label} (hl : NB R' l) : ∀ (r : Label) (left : PE) (xs : List (String × Label × PE)),
    R'.e r = none → PyCore.editE R' (cmpChain l r left xs) =
      cmpChain l r (PyCore.editE R' left) (xs.map fun x => (x.1, x.2.1, PyCore.editE R' x.2.2))
  | r, left, [], hr => by simp [cmpChain, peditE_ccR hr]
  | r, left, [(op, _, b)], hr => by simp [cmpChain, PyCore.editE, hr]
  | r, left, (op, lb, b) :: x :: rest, hr => by
    have ih := peditE_cmpChain hl (sub l 1) (gad l 4 (.get (fresh "c" lb)) []) (x :: rest)
      (hl.1 1 (by omega))
    simp only [List.map_cons] at ih
    simp [cmpChain, PyCore.editE, hr, nb_e hl (by omega : 2 < 64), peditE_gad hl 3 (by omega),
      peditE_gad hl 4 (by omega), ih]

theorem cmpOps_map (F : PE → PE) : ∀ (ops : List String) (xs : List (Label × PE)),
    cmpOps ops (xs.map fun x => (x.1, F x.2)) = (cmpOps ops xs).map fun y => (y.1, y.2.1, F y.2.2)
  | _, [] => rfl
  | ops, (lb, b) :: rest => by simp [cmpOps, cmpOps_map F ops.tail rest]

theorem peditB_ifsNest {lg : Label} (hl : NB R' lg) : ∀ (cs : List PE) (body : PS),
    PyCore.editB R' (ifsNest lg cs body) = ifsNest lg (cs.map (PyCore.editE R')) (PyCore.editB R' body)
  | [], _ => rfl
  | c :: cs, body => by
    simp [ifsNest, PyCore.editB, PyCore.editS, nb_s hl (by omega : 3 < 64), peditB_ifsNest hl cs body]

theorem peditB_forLoop {l : Label} (hl : NB R' l) (iv : Name) (st body u : PS) :
    PyCore.editB R' (forLoop l iv st body u) =
      forLoop l iv (PyCore.editB R' st) (PyCore.editB R' body) (PyCore.editB R' u) := by
  simp (disch := omega) [forLoop, PyCore.editB, PyCore.editS, PyCore.editE, PyCore.editHs, hl.1, hl.2.1,
    hl.2.2, peditB_append]

theorem peditB_compElt {l : Label} (hl : NB R' l) (k : CompKind) (es : List PE) :
    PyCore.editB R' (compElt l k es) = compElt l k (es.map (PyCore.editE R')) := by
  have h9 := hl.2.1 9 (by omega); have h11 := hl.2.1 11 (by omega)
  have e9 := hl.1 9 (by omega); have e10 := hl.1 10 (by omega); have e11 := hl.1 11 (by omega)
  have hd : ∀ xs : List PE, PyCore.editB R' (xs.map (PyCore.Stmt.expr (sub l 11))) =
      (xs.map (PyCore.editE R')).map (PyCore.Stmt.expr (sub l 11)) := by
    intro xs; induction xs <;> simp_all [PyCore.editB, PyCore.editS]
  cases k <;> rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp (disch := omega) [compElt, PyCore.editB, PyCore.editS, PyCore.editE, stuckAt, dead, nm, cc,
      peditE_ccR, hl.1, hl.2.1, hd]

theorem peditB_compWrap {l : Label} (hl : NB R' l) (k : CompKind) (loops : PS) :
    PyCore.editB R' (compWrap l k loops) = compWrap l k (PyCore.editB R' loops) := by
  unfold compWrap; split
  · rfl
  · simp (disch := omega) [PyCore.editB, PyCore.editS, PyCore.editE, hl.1, hl.2.1, cc,
      peditE_ccR (hl.1 5 (by omega)), nm, peditB_append]

/-- A statement list replaced as the PyCore sites `stmtSites` say. -/
theorem peditB_stmtSites {ss r : PS} (h : ∀ x ∈ stmtSites ss r, x.Agrees R') (hne : ss ≠ []) :
    PyCore.editB R' ss = r := by
  match ss, hne with
  | s :: rest, _ =>
    simp only [stmtSites, List.forall_mem_cons, List.forall_mem_map, PSite.Agrees] at h
    have hrest : ∀ rest : PS, (∀ x ∈ rest, R'.s x.label = some []) → PyCore.editB R' rest = [] := by
      intro rest hr; induction rest with
      | nil => rfl
      | cons s' rest ih =>
        simp only [List.forall_mem_cons] at hr
        simp [PyCore.editB, peditS_site hr.1, ih hr.2]
    simp [PyCore.editB, peditS_site h.1, hrest rest h.2]

end

theorem mem_olabelsPs (R : Edit) {q : Param} : ∀ {ps : List Param}, q ∈ ps → q.label ∈ olabelsPs R ps
  | .mk .. :: ps, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [olabelsPs, Param.label]
    · simp [olabelsPs, mem_olabelsPs R h]

theorem starMark_label (e : Expr) : (starMark e).label = sub e.label 57 := by
  cases e <;> rfl

theorem trT_ne (C : List Scope) (src : Label → PE) (t : Expr) (tE : PE) : trT C src t tE ≠ [] := by
  cases t <;> simp [trT]

theorem trD_ne (C : List Scope) (t : Expr) (tD : PS) : trD C t tD ≠ [] := by
  cases t <;> simp [trD]

/-- A source of a store that is no site where its target is none. -/
def SrcFix (R' : PyCore.Edit) (src : Label → PE) : Prop := ∀ lt, NB R' lt → PyCore.editE R' (src lt) = src lt

theorem srcFix_name {R' : PyCore.Edit} (t : String) (l : Label) : SrcFix R' (nameSrc t l) :=
  fun _ h => by simp [nameSrc, PyCore.editE, h.1 63 (by omega)]
theorem srcFix_item {R' : PyCore.Edit} (l : Label) (i : Nat) : SrcFix R' (itemSrc l i) :=
  fun _ h => by simp [itemSrc, PyCore.editE, peditE_ccR (h.1 59 (by omega)), h.1 61 (by omega)]
theorem srcFix_for {R' : PyCore.Edit} (l : Label) : SrcFix R' (forSrc l) :=
  fun _ h => by simp [forSrc, PyCore.editE, h.1 63 (by omega)]
theorem srcFix_dead {R' : PyCore.Edit} : SrcFix R' deadSrc :=
  fun _ h => by simp [deadSrc, PyCore.editE, h.1 63 (by omega)]

section
variable {R : Edit} {R' : PyCore.Edit}

theorem site_edit {C : List Scope} {e e' : Expr} (hR : R.e e.label = some e')
    (hs : (siteE R C e e').Agrees R') : PyCore.editE R' (trE C e) = trE (editChain R C) (editE R e) := by
  rw [editE_site hR]; exact peditE_site hs

/-- A starred operand's translation, from the star's (no site). -/
theorem unstar_edit {C : List Scope} {e : Expr} (hR : R.e e.label = none) (hl : NB R' e.label)
    (ih : PyCore.editE R' (trE C e) = trE (editChain R C) (editE R e)) :
    PyCore.editE R' (trE C (unstar e)) = trE (editChain R C) (unstar (editE R e)) := by
  cases e <;> simp only [Expr.label] at hR hl <;> simp only [unstar, editE, hR, Option.getD_none] at ih ⊢ <;>
    try exact ih
  simp [trE, PyCore.editE, hl.1 0 (by omega), hl.1 1 (by omega), peditE_gad hl 2 (by omega)] at ih
  exact ih

theorem unstarT_edit {C : List Scope} {src : Label → PE} {t : Expr} (hR : R.e t.label = none) (hl : NB R' t.label)
    (ih : PyCore.editB R' (trT C src t (trE C t)) = trT (editChain R C) src (editE R t) (trE (editChain R C) (editE R t))) :
    PyCore.editB R' (trT C src (unstar t) (trE C (unstar t))) =
      trT (editChain R C) src (unstar (editE R t)) (trE (editChain R C) (unstar (editE R t))) := by
  cases t <;> simp only [Expr.label] at hR hl <;> simp only [unstar, editE, hR, Option.getD_none] at ih ⊢ <;>
    try exact ih
  simp [trT, PyCore.editB, stuckAt, dead, PyCore.editS, PyCore.editE, hl.1 54 (by omega), hl.1 55 (by omega),
    hl.2.1 54 (by omega), hl.2.1 55 (by omega), peditE_ccR (hl.1 55 (by omega))] at ih
  exact ih

theorem constMark_label (k : Nat) (e : Expr) : (constMark k e).label = sub e.label k := by
  cases e <;> rfl

/-- Outside the sites a set item's constness keeps its form. -/
theorem constMark_edit_none {R : Edit} {k : Nat} {e : Expr} (h : R.e e.label = none) :
    constMark k (editE R e) = constMark k e ∨ (∃ l op a, e = .unary l op a) ∨ (∃ l es, e = .tuple l es) := by
  cases e <;> simp_all [editE, Expr.label, constMark]

mutual
/-- A set item's constness marker, from the marker sites of its parts. -/
theorem cm_edit (k : Nat) (hk64 : k < 64) : ∀ e, R.e e.label = none → NB R' e.label →
    (∀ x ∈ cmSites R e, x.Agrees R') → (∀ l ∈ olabelsE R e, NB R' l) →
    PyCore.editE R' (constMark k e) = constMark k (editE R e)
  | .unary l op a, hR, hl, hs, ho => by
    simp only [Expr.label] at hR hl
    have ha : PyCore.editE R' (constMark 50 a) = constMark 50 (editE R a) := by
      cases ha : R.e a.label with
      | some a' =>
        simp only [cmSites, ha, List.forall_mem_cons, List.forall_mem_nil, PSite.Agrees] at hs
        rw [editE_site ha]; exact peditE_site (by rw [constMark_label]; exact hs.1)
      | none =>
        simp only [cmSites, ha] at hs
        exact cm_edit 50 (by omega) a ha (ho _ (by cases a <;> simp_all [olabelsE, ocut, Expr.label])) hs
          (fun y hy => ho y (by simp [olabelsE, ocut, hR, hy]))
    simp [constMark, editE, hR, peditE_ccR (hl.1 k hk64), ha]
  | .tuple l es, hR, hl, hs, ho => by
    simp only [Expr.label] at hR hl
    simp only [cmSites] at hs
    have h := cmL_edit es hs (fun y hy => ho y (by simp [olabelsE, ocut, hR, hy]))
    simp [constMark, editE, hR, peditE_ccR (hl.1 k hk64), h]
  | .const l c, hR, hl, _, _ | .name l c, hR, hl, _, _ | .bin l c _ _, hR, hl, _, _
  | .boolop l c _, hR, hl, _, _ | .compare l _ c _, hR, hl, _, _ | .ifexp l c _ _, hR, hl, _, _
  | .call l c _ _, hR, hl, _, _ | .attr l c _, hR, hl, _, _ | .sub l c _, hR, hl, _, _
  | .slice l c _ _, hR, hl, _, _ | .star l c, hR, hl, _, _ | .list l c, hR, hl, _, _
  | .set l c, hR, hl, _, _ | .dict l c, hR, hl, _, _ | .lam l c _, hR, hl, _, _
  | .comp l _ c _, hR, hl, _, _ | .walrus l _ c, hR, hl, _, _ | .yield l c, hR, hl, _, _
  | .yieldFrom l c, hR, hl, _, _ | .fstr l c, hR, hl, _, _ | .fmt l c _ _, hR, hl, _, _ => by
    simp only [Expr.label] at hR hl
    simp [constMark, editE, hR, PyCore.editE, hl.1 k hk64, Expr.label]
theorem cmL_edit : ∀ es, (∀ x ∈ cmSitesL R es, x.Agrees R') → (∀ l ∈ olabelsEs R es, NB R' l) →
    (constMarks es).map (PyCore.editE R') = constMarks (editEs R es)
  | [], _, _ => rfl
  | e :: es, hs, ho => by
    simp only [cmSitesL, olabelsEs, List.forall_mem_append] at hs ho
    have ih := cmL_edit es hs.2 ho.2
    have he : PyCore.editE R' (constMark 50 e) = constMark 50 (editE R e) := by
      cases he : R.e e.label with
      | some e' =>
        simp only [he, List.forall_mem_cons, List.forall_mem_nil, PSite.Agrees] at hs
        rw [editE_site he]; exact peditE_site (by rw [constMark_label]; exact hs.1.1)
      | none =>
        simp only [he] at hs
        exact cm_edit 50 (by omega) e he (ho.1 _ (by cases e <;> simp_all [olabelsE, ocut, Expr.label])) hs.1 ho.1
    simp [constMarks, editEs, ih, he]
end

variable (hk : KeepsLabels R)
include hk

set_option hygiene false in
macro "siteC" : tactic => `(tactic| exact site_edit hR (hs _ (by simp [sitesE, hR])))
set_option hygiene false in
/-- A child's sites, from its parent's (`hs`, the parent no site by `hR`). -/
macro "cmFromS" : term => `(fun x hx => hs x (by
  simp [sitesE, sitesO, sitesEs, sitesA, sitesSet, sitesKs, sitesKV, sitesDf, sitesAn, sitesG1, sitesGs, sitesT,
    sitesIt, hR, hx]))
set_option hygiene false in
/-- A child's labels outside the sites, from its parent's (`ho`). -/
macro "fromO" : term => `(fun x hx => ho x (by
  simp [olabelsE, olabelsO, olabelsEs, olabelsKs, olabelsDs, olabelsPs, olabelsGs, ocut, hR, hx]))
set_option hygiene false in
/-- The parent `l` is outside the sites. -/
macro "nbl" : tactic => `(tactic| have hl : NB R' l := ho l (by simp [olabelsE, ocut, hR]))
set_option hygiene false in
/-- Close a non-site expression from its children's commutations. -/
macro "nsC" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (disch := omega) [trE, editE, hR, Option.getD_none, PyCore.editE, hl.1, peditE_cc hl, peditE_gad hl,
    peditE_ccR_sub hl, peditE_recR_sub hl, List.map_append, List.map_cons, List.map_nil, priv_edit, $ls,*])

mutual
theorem trE_edit (C : List Scope) : ∀ e, (∀ x ∈ sitesE R C e, x.Agrees R') → (∀ l ∈ olabelsE R e, NB R' l) →
    PyCore.editE R' (trE C e) = trE (editChain R C) (editE R e)
  | .const l c, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; nsC []
  | .name l x, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; nsC []
  | .bin l op a b, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl; have ih1 := trE_edit C a cmFromS fromO; have ih2 := trE_edit C b cmFromS fromO; nsC [ih1, ih2]
  | .unary l op a, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trE_edit C a cmFromS fromO; nsC [ih1]
  | .boolop l op es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trEs_edit C es cmFromS fromO; nsC [peditE_boolChain hl, ih1]
  | .compare l a ops es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl; have ih1 := trE_edit C a cmFromS fromO; have ih2 := trLs_edit C es cmFromS fromO
      nsC [peditE_cmpChain hl (sub l 0) _ _ (hl.1 0 (by omega)), ih1, ← ih2, cmpOps_map]
  | .ifexp l c a b, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl; have ih1 := trE_edit C c cmFromS fromO; have ih2 := trE_edit C a cmFromS fromO
      have ih3 := trE_edit C b cmFromS fromO; nsC [ih1, ih2, ih3]
  | .call l f as ks, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl; have ih1 := trE_edit C f cmFromS fromO; have ih2 := trA_edit C as cmFromS fromO
      have ih3 := trKs_edit C ks cmFromS fromO; nsC [ih1, ih2.1, ih2.2, ih3.1, ih3.2, kwMarks_edit]
  | .attr l e a, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trE_edit C e cmFromS fromO; nsC [ih1]
  | .sub l e i, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl; have ih1 := trE_edit C e cmFromS fromO; have ih2 := trE_edit C i cmFromS fromO; nsC [ih1, ih2]
  | .slice l a b c, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl
      have ih1 := trO_edit C l 1 a (hl.1 1 (by omega)) cmFromS fromO
      have ih2 := trO_edit C l 2 b (hl.1 2 (by omega)) cmFromS fromO
      have ih3 := trO_edit C l 3 c (hl.1 3 (by omega)) cmFromS fromO
      nsC [ih1, ih2, ih3]
  | .star l e, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trE_edit C e cmFromS fromO; nsC [ih1]
  | .list l es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trA_edit C es cmFromS fromO; nsC [ih1.1, ih1.2]
  | .tuple l es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trA_edit C es cmFromS fromO; nsC [ih1.1, ih1.2]
  | .set l es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trSet_edit C es cmFromS fromO; nsC [ih1.1, ih1.2]
  | .dict l kvs, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl; have ih1 := trKVs_edit C kvs cmFromS fromO
      rw [editE, hR, Option.getD_none, trE, trE, map_editDs R _ (fun k v => by cases k <;> rfl)]
      nsC [ih1]
  | .lam l ps b, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl
      have ih1 := trDfs_edit C ps cmFromS fromO; have ih2 := trAnns_edit C ps cmFromS fromO
      have ih3 := trE_edit (.lam l ps b :: C) b cmFromS fromO
      simp only [editChain_cons, editSc] at ih3
      have hpb := peditB_paramBind (.lam l ps b :: C) ps
        (fun q hq => ho _ (by simp [olabelsE, ocut, hR, mem_olabelsPs R hq]))
      have hpm : ∀ q ∈ ps, PyCore.editE R' (paramMark (.lam l ps b :: C) q) = paramMark (.lam l ps b :: C) q :=
        fun q hq => peditE_paramMark _ (ho _ (by simp [olabelsE, ocut, hR, mem_olabelsPs R hq]))
      have hpm' : List.map (PyCore.editE R' ∘ paramMark (.lam l ps b :: C)) ps = ps.map (paramMark (.lam l ps b :: C)) :=
        List.map_congr_left (fun q hq => hpm q hq)
      nsC [ih1, ih2, ih3, hpb, hpm', paramBind_edit R (C := .lam l ps b :: C)
          (C' := .lam l (editPs R ps) (editE R b) :: editChain R C) (by simp [priv]),
        paramMark_edit R (C := .lam l ps b :: C) (C' := .lam l (editPs R ps) (editE R b) :: editChain R C)
          (by simp [priv]), List.map_congr_left hpm, editPs_length, PyCore.editB, PyCore.editS, hl.2.1,
        peditB_append]
  | .comp l k es gs, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl
      have ih3 := trEs_edit (.comp l k es gs :: C) es cmFromS fromO
      simp only [editChain_cons, editSc] at ih3
      have ih2 := trGs_edit (.comp l k es gs :: C) (fresh "i" l) true gs
        (compElt l k (trEs (.comp l k es gs :: C) es))
        (compElt l k (trEs (.comp l k (editEs R es) (editGs R gs) :: editChain R C) (editEs R es)))
        (by rw [peditB_compElt hl, ih3]) cmFromS fromO
      simp only [editChain_cons, editSc] at ih2
      cases gs with
      | nil => nsC [ih2, peditB_compWrap hl, PyCore.editB, PyCore.editS, hl.2.1, editGs]
      | cons g gs' =>
        obtain ⟨lg, t, i, ifs⟩ := g
        have ih1 := trE_edit C i cmFromS fromO
        nsC [ih1, ih2, peditB_compWrap hl, PyCore.editB, PyCore.editS, hl.2.1, editGs, trG1]
  | .walrus l x e, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trE_edit C e cmFromS fromO; nsC [ih1]
  | .yield l e, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trO_edit C l 1 e (hl.1 1 (by omega)) cmFromS fromO; nsC [ih1]
  | .yieldFrom l e, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trE_edit C e cmFromS fromO; nsC [ih1]
  | .fstr l es, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none => nbl; have ih1 := trEs_edit C es cmFromS fromO; nsC [ih1]
  | .fmt l e cv sp, hs, ho => by
    cases hR : R.e l with
    | some e' => siteC
    | none =>
      nbl; have ih1 := trE_edit C e cmFromS fromO
      cases sp with
      | none => simp only [trE, editE, hR, Option.getD_none, editO]; split <;> nsC [ih1]
      | some s =>
        have ih2 := trE_edit C s cmFromS fromO
        simp only [trE, editE, hR, Option.getD_none, editO]; split <;> nsC [ih1, ih2]
theorem trO_edit (C : List Scope) (l : Label) (k : Nat) : ∀ o, R'.e (sub l k) = none →
    (∀ x ∈ sitesO R C o, x.Agrees R') → (∀ l ∈ olabelsO R o, NB R' l) →
    PyCore.editE R' (trO C l k o) = trO (editChain R C) l k (editO R o)
  | none, hd, _, _ => by simp [trO, editO, PyCore.editE, hd]
  | some e, _, hs, ho => by
    simp only [sitesO, olabelsO] at hs ho
    simp only [trO, editO]; exact trE_edit C e hs ho
theorem trEs_edit (C : List Scope) : ∀ es, (∀ x ∈ sitesEs R C es, x.Agrees R') →
    (∀ l ∈ olabelsEs R es, NB R' l) →
    (trEs C es).map (PyCore.editE R') = trEs (editChain R C) (editEs R es)
  | [], _, _ => rfl
  | e :: es, hs, ho => by
    simp only [sitesEs, olabelsEs, List.forall_mem_append] at hs ho
    simp [trEs, editEs, trE_edit C e hs.1 ho.1, trEs_edit C es hs.2 ho.2]
theorem trA_edit (C : List Scope) : ∀ es, (∀ x ∈ sitesA R C es, x.Agrees R') →
    (∀ l ∈ olabelsEs R es, NB R' l) →
    (trA C es).map (PyCore.editE R') = trA (editChain R C) (editEs R es) ∧
      (es.map starMark).map (PyCore.editE R') = (editEs R es).map starMark
  | [], _, _ => ⟨rfl, rfl⟩
  | e :: es, hs, ho => by
    simp only [sitesA, olabelsEs, List.forall_mem_append] at hs ho
    obtain ⟨ih1, ih2⟩ := trA_edit C es hs.2 ho.2
    simp only [trA_cons, editEs, List.map_cons, ih1, ih2]
    cases hR : R.e e.label with
    | some e' =>
      simp only [hR, List.forall_mem_cons, List.forall_mem_nil, PSite.Agrees] at hs
      have hv := peditE_site (e := trE C (unstar e)) hs.1.1
      have hm := peditE_site (e := starMark e) (by rw [starMark_label]; exact hs.1.2.1)
      rw [editE_site hR, hv, hm]; exact ⟨rfl, rfl⟩
    | none =>
      simp only [hR] at hs
      have hl : NB R' e.label := ho.1 _ (by cases e <;> simp_all [olabelsE, ocut, Expr.label])
      have ih := trE_edit C e hs.1 ho.1
      rw [unstar_edit hR hl ih, peditE_starMark hl, starMark_edit hR]; exact ⟨rfl, rfl⟩
theorem trSet_edit (C : List Scope) : ∀ es, (∀ x ∈ sitesSet R C es, x.Agrees R') →
    (∀ l ∈ olabelsEs R es, NB R' l) →
    (trA C es).map (PyCore.editE R') = trA (editChain R C) (editEs R es) ∧
      (es.map (constMark 57)).map (PyCore.editE R') = (editEs R es).map (constMark 57)
  | [], _, _ => ⟨rfl, rfl⟩
  | e :: es, hs, ho => by
    simp only [sitesSet, olabelsEs, List.forall_mem_append] at hs ho
    obtain ⟨ih1, ih2⟩ := trSet_edit C es hs.2 ho.2
    simp only [trA_cons, editEs, List.map_cons, ih1, ih2]
    cases hR : R.e e.label with
    | some e' =>
      simp only [hR, List.forall_mem_cons, List.forall_mem_nil, PSite.Agrees] at hs
      have hv := peditE_site (e := trE C (unstar e)) hs.1.1
      have hm := peditE_site (e := constMark 57 e) (by rw [constMark_label]; exact hs.1.2.1)
      rw [editE_site hR, hv, hm]; exact ⟨rfl, rfl⟩
    | none =>
      simp only [hR, List.forall_mem_append] at hs
      have hl : NB R' e.label := ho.1 _ (by cases e <;> simp_all [olabelsE, ocut, Expr.label])
      have ih := trE_edit C e hs.1.1 ho.1
      rw [unstar_edit hR hl ih, cm_edit 57 (by omega) e hR hl hs.1.2 ho.1]; exact ⟨rfl, rfl⟩
theorem trKs_edit (C : List Scope) : ∀ ks, (∀ x ∈ sitesKs R C ks, x.Agrees R') →
    (∀ l ∈ olabelsKs R ks, NB R' l) →
    (trKs C ks).map (PyCore.editE R') = trKs (editChain R C) (editKs R ks) ∧
      (ks.map kwMark).map (PyCore.editE R') = ks.map kwMark
  | [], _, _ => ⟨rfl, rfl⟩
  | .mk l x e :: ks, hs, ho => by
    obtain ⟨ih1, ih2⟩ := trKs_edit C ks (fun y hy => hs y (by simp [sitesKs, hy]))
      (fun y hy => ho y (by simp [olabelsKs, hy]))
    have hkm := peditE_kwMark (k := .mk l x e) (ho l (by simp [olabelsKs]))
    have ih := trE_edit C e (fun y hy => hs y (by simp [sitesKs, hy])) (fun y hy => ho y (by simp [olabelsKs, hy]))
    simp [trKs, editKs, ih, ih1, ih2, hkm]
theorem trLs_edit (C : List Scope) : ∀ es, (∀ x ∈ sitesEs R C es, x.Agrees R') →
    (∀ l ∈ olabelsEs R es, NB R' l) →
    (trLs C es).map (fun x => (x.1, PyCore.editE R' x.2)) = trLs (editChain R C) (editEs R es)
  | [], _, _ => rfl
  | e :: es, hs, ho => by
    simp only [sitesEs, olabelsEs, List.forall_mem_append] at hs ho
    simp [trLs, editEs, trE_edit C e hs.1 ho.1, trLs_edit C es hs.2 ho.2, editE_label hk]
theorem trKVs_edit (C : List Scope) : ∀ kvs, (∀ x ∈ sitesKV R C kvs, x.Agrees R') →
    (∀ l ∈ olabelsDs R kvs, NB R' l) →
    (trKVs C kvs).map (PyCore.editE R') = trKVs (editChain R C) (editDs R kvs)
  | [], _, _ => rfl
  | .mk (some k) v :: kvs, hs, ho => by
    have ih1 := trE_edit C k (fun y hy => hs y (by simp [sitesKV, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsDs, olabelsO, hy]))
    have ih2 := trE_edit C v (fun y hy => hs y (by simp [sitesKV, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsDs, olabelsO, hy]))
    have ih3 := trKVs_edit C kvs (fun y hy => hs y (by simp [sitesKV, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsDs, olabelsO, hy]))
    simp [trKVs, editDs, editO, ih1, ih2, ih3]
  | .mk none v :: kvs, hs, ho => by
    have ih2 := trE_edit C v (fun y hy => hs y (by simp [sitesKV, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsDs, olabelsO, hy]))
    have ih3 := trKVs_edit C kvs (fun y hy => hs y (by simp [sitesKV, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsDs, olabelsO, hy]))
    simp [trKVs, editDs, editO, ih2, ih3]
theorem trDfs_edit (C : List Scope) : ∀ ps, (∀ x ∈ sitesDf R C ps, x.Agrees R') →
    (∀ l ∈ olabelsPs R ps, NB R' l) →
    (trDfs C ps).map (PyCore.editE R') = trDfs (editChain R C) (editPs R ps)
  | [], _, _ => rfl
  | .mk l x k (some d) a :: ps, hs, ho => by
    have ih1 := trE_edit C d (fun y hy => hs y (by simp [sitesDf, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    have ih2 := trDfs_edit C ps (fun y hy => hs y (by simp [sitesDf, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    simp [trDfs, editPs, editO, ih1, ih2]
  | .mk l x k none a :: ps, hs, ho => by
    have ih2 := trDfs_edit C ps (fun y hy => hs y (by simp [sitesDf, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    simp [trDfs, editPs, editO, ih2]
theorem trAnns_edit (C : List Scope) : ∀ ps, (∀ x ∈ sitesAn R C ps, x.Agrees R') →
    (∀ l ∈ olabelsPs R ps, NB R' l) →
    (trAnns C ps).map (PyCore.editE R') = trAnns (editChain R C) (editPs R ps)
  | [], _, _ => rfl
  | .mk l x k d (some a) :: ps, hs, ho => by
    have ih1 := trE_edit C a (fun y hy => hs y (by simp [sitesAn, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    have ih2 := trAnns_edit C ps (fun y hy => hs y (by simp [sitesAn, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    simp [trAnns, editPs, editO, ih1, ih2]
  | .mk l x k d none :: ps, hs, ho => by
    have ih2 := trAnns_edit C ps (fun y hy => hs y (by simp [sitesAn, sitesO, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    simp [trAnns, editPs, editO, ih2]
theorem trGs_edit (C : List Scope) (it : Name) : ∀ (first : Bool) (gs : List Gen) (inner inner' : PS),
    PyCore.editB R' inner = inner' → (∀ x ∈ sitesGs R C first gs, x.Agrees R') →
    (∀ l ∈ olabelsGs R gs, NB R' l) →
    PyCore.editB R' (trGs C it first gs inner) = trGs (editChain R C) it first (editGs R gs) inner'
  | _, [], inner, inner', h, _, _ => by simp [trGs, editGs, h]
  | first, .mk lg t i ifs :: gs, inner, inner', h, hs, ho => by
    have hlg : NB R' lg := ho lg (by simp [olabelsGs])
    have ho1 : ∀ y ∈ olabelsE R t, NB R' y := fun y hy => ho y (by simp [olabelsGs, hy])
    have ih1 := trT_edit C (forSrc lg) (srcFix_for lg) t (fun h' => trE_edit C t h' ho1)
      (fun y hy => hs y (by simp [sitesGs, hy])) ho1
    have ih3 := trEs_edit C ifs (fun y hy => hs y (by simp [sitesGs, hy])) (fun y hy => ho y (by simp [olabelsGs, hy]))
    have ih4 := trGs_edit C it false gs inner inner' h (fun y hy => hs y (by simp [sitesGs, hy]))
      (fun y hy => ho y (by simp [olabelsGs, hy]))
    simp only [trGs, editGs, peditB_append, peditB_forLoop hlg, peditB_ifsNest hlg, ih1, ih3, ih4]
    cases first
    · have ih2 := trE_edit C i (fun y hy => hs y (by simp [sitesGs, hy])) (fun y hy => ho y (by simp [olabelsGs, hy]))
      simp (disch := omega) [PyCore.editB, PyCore.editS, hlg.2.1, peditE_cc hlg, ih2]
    · simp [PyCore.editB]
theorem trT_edit (C : List Scope) (src : Label → PE) (hsrc : SrcFix R' src) : ∀ t,
    ((∀ x ∈ sitesE R C t, x.Agrees R') → PyCore.editE R' (trE C t) = trE (editChain R C) (editE R t)) →
    (∀ x ∈ sitesT R C src t (sitesE R C t), x.Agrees R') → (∀ l ∈ olabelsE R t, NB R' l) →
    PyCore.editB R' (trT C src t (trE C t)) = trT (editChain R C) src (editE R t) (trE (editChain R C) (editE R t))
  | t, htE, hs, ho => by
    cases hR : R.e t.label with
    | some t' =>
      unfold sitesT at hs; simp only [hR] at hs
      rw [editE_site hR]; exact peditB_stmtSites hs (trT_ne _ _ _ _)
    | none =>
      have hl : NB R' t.label := ho _ (by cases t <;> simp_all [olabelsE, ocut, Expr.label])
      cases t with
      | name lt x =>
        simp only [Expr.label] at hR hl
        simp (disch := omega) [trT, editE, hR, PyCore.editB, PyCore.editS, hl.2.1, hsrc lt hl]
      | attr lt o a =>
        simp only [Expr.label] at hR hl
        simp only [sitesT, hR, Expr.label] at hs
        have ih := trE_edit C o hs fromO
        simp (disch := omega) [trT, editE, hR, PyCore.editB, PyCore.editS, hl.2.1, peditE_cc hl, ih, hsrc lt hl]
      | sub lt o i =>
        simp only [Expr.label] at hR hl
        simp only [sitesT, hR, Expr.label, List.forall_mem_append] at hs
        have ih1 := trE_edit C o hs.1 fromO; have ih2 := trE_edit C i hs.2 fromO
        simp (disch := omega) [trT, editE, hR, PyCore.editB, PyCore.editS, hl.2.1, peditE_cc hl, ih1, ih2,
          hsrc lt hl]
      | tuple lt ts =>
        simp only [Expr.label] at hR hl
        simp only [sitesT, hR, Expr.label] at hs
        obtain ⟨ih1, ih2⟩ := trItems_edit C lt 0 ts hs fromO
        simp (disch := omega) [trT, editE, hR, blk, PyCore.editB, PyCore.editS, PyCore.editHs, hl.2.1, hl.1,
          peditE_gad hl, ih1, ih2, hsrc lt hl]
      | list lt ts =>
        simp only [Expr.label] at hR hl
        simp only [sitesT, hR, Expr.label] at hs
        obtain ⟨ih1, ih2⟩ := trItems_edit C lt 0 ts hs fromO
        simp (disch := omega) [trT, editE, hR, blk, PyCore.editB, PyCore.editS, PyCore.editHs, hl.2.1, hl.1,
          peditE_gad hl, ih1, ih2, hsrc lt hl]
      | star ls e =>
        simp only [Expr.label] at hR hl
        simp only [sitesT, hR, Expr.label] at hs
        have ih := trT_edit C src hsrc e (fun h' => trE_edit C e h' fromO) hs fromO
        simp (disch := omega) [trT, editE, hR, PyCore.editB, PyCore.editS, PyCore.editE, stuckAt, dead,
          hl.2.1, hl.1, peditE_ccR_sub hl, ih]
      | _ =>
        simp only [Expr.label] at hR hl
        simp only [sitesT, hR, Expr.label] at hs
        have ih := htE hs
        simp only [editE, hR, Option.getD_none] at ih
        simp (disch := omega) [trT, editE, hR, Expr.label, PyCore.editB, PyCore.editS, PyCore.editE, stuckAt,
          dead, hl.2.1, hl.1, peditE_ccR_sub hl, ih]
theorem trItems_edit (C : List Scope) (lt : Label) : ∀ (i : Nat) (ts : List Expr),
    (∀ x ∈ sitesIt R C lt i ts, x.Agrees R') → (∀ l ∈ olabelsEs R ts, NB R' l) →
    PyCore.editB R' (trItems C lt i ts) = trItems (editChain R C) lt i (editEs R ts) ∧
      (trMarks ts).map (PyCore.editE R') = trMarks (editEs R ts)
  | _, [], _, _ => ⟨rfl, rfl⟩
  | i, t :: ts, hs, ho => by
    simp only [sitesIt, olabelsEs, List.forall_mem_append] at hs ho
    obtain ⟨ih1, ih2⟩ := trItems_edit C lt (i + 1) ts hs.2 ho.2
    simp only [trItems_cons, editEs, trMarks_eq, List.map_cons, peditB_append] at ih1 ih2 ⊢
    rw [ih1, ih2]
    cases hR : R.e t.label with
    | some t' =>
      simp only [hR, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_nil, PSite.Agrees] at hs
      have hm := peditE_site (e := starMark t) (by rw [starMark_label]; exact hs.1.2.1)
      rw [editE_site hR, peditB_stmtSites hs.1.1 (trT_ne _ _ _ _), hm]; exact ⟨rfl, rfl⟩
    | none =>
      simp only [hR] at hs
      have hl : NB R' t.label := ho.1 _ (by cases t <;> simp_all [olabelsE, ocut, Expr.label])
      have ih := trT_edit C (itemSrc lt i) (srcFix_item lt i) t (fun h' => trE_edit C t h' ho.1) hs.1 ho.1
      rw [unstarT_edit hR hl ih, peditE_starMark hl, starMark_edit hR]; exact ⟨rfl, rfl⟩
end

mutual
theorem trD_edit (C : List Scope) : ∀ t,
    ((∀ x ∈ sitesE R C t, x.Agrees R') → PyCore.editE R' (trE C t) = trE (editChain R C) (editE R t)) →
    (∀ x ∈ sitesD R C t (sitesT R C deadSrc t (sitesE R C t)), x.Agrees R') → (∀ l ∈ olabelsE R t, NB R' l) →
    PyCore.editB R' (trD C t (trT C deadSrc t (trE C t))) =
      trD (editChain R C) (editE R t) (trT (editChain R C) deadSrc (editE R t) (trE (editChain R C) (editE R t)))
  | t, htE, hs, ho => by
    cases hR : R.e t.label with
    | some t' =>
      unfold sitesD at hs; simp only [hR] at hs
      rw [editE_site hR]; exact peditB_stmtSites hs (trD_ne _ _ _)
    | none =>
      have hl : NB R' t.label := ho _ (by cases t <;> simp_all [olabelsE, ocut, Expr.label])
      have hT : (∀ x ∈ sitesT R C deadSrc t (sitesE R C t), x.Agrees R') →
          PyCore.editB R' (trT C deadSrc t (trE C t)) =
            trT (editChain R C) deadSrc (editE R t) (trE (editChain R C) (editE R t)) :=
        fun h => trT_edit hk C deadSrc srcFix_dead t htE h ho
      cases t with
      | name lt x =>
        simp only [Expr.label] at hR hl
        simp (disch := omega) [trD, editE, hR, PyCore.editB, PyCore.editS, hl.2.1]
      | attr lt o a =>
        simp only [Expr.label] at hR hl
        unfold sitesD at hs; simp only [hR, Expr.label] at hs
        have ih := trE_edit hk C o hs fromO
        simp (disch := omega) [trD, editE, hR, PyCore.editB, PyCore.editS, hl.2.1, peditE_cc hl, ih]
      | sub lt o i =>
        simp only [Expr.label] at hR hl
        unfold sitesD at hs; simp only [hR, Expr.label, List.forall_mem_append] at hs
        have ih1 := trE_edit hk C o hs.1 fromO; have ih2 := trE_edit hk C i hs.2 fromO
        simp (disch := omega) [trD, editE, hR, PyCore.editB, PyCore.editS, hl.2.1, peditE_cc hl, ih1, ih2]
      | tuple lt ts =>
        simp only [Expr.label] at hR hl
        unfold sitesD at hs; simp only [hR, Expr.label] at hs
        have ih := trDs_edit C ts hs fromO
        simp (disch := omega) [trD, editE, hR, blk, PyCore.editB, PyCore.editS, PyCore.editHs, hl.2.1, ih]
      | list lt ts =>
        simp only [Expr.label] at hR hl
        unfold sitesD at hs; simp only [hR, Expr.label] at hs
        have ih := trDs_edit C ts hs fromO
        simp (disch := omega) [trD, editE, hR, blk, PyCore.editB, PyCore.editS, PyCore.editHs, hl.2.1, ih]
      | _ =>
        simp only [Expr.label] at hR hl
        unfold sitesD at hs; simp only [hR, Expr.label] at hs
        have ih := hT hs
        simp only [editE, hR, Option.getD_none] at ih ⊢
        simp (disch := omega) [trD, Expr.label, PyCore.editB, PyCore.editS, PyCore.editE, stuckAt, dead,
          hl.2.1, hl.1, peditE_ccR_sub hl, ih]
theorem trDs_edit (C : List Scope) : ∀ ts, (∀ x ∈ sitesDl R C ts, x.Agrees R') →
    (∀ l ∈ olabelsEs R ts, NB R' l) → PyCore.editB R' (trDs C ts) = trDs (editChain R C) (editEs R ts)
  | [], _, _ => rfl
  | t :: ts, hs, ho => by
    simp only [sitesDl, olabelsEs, List.forall_mem_append] at hs ho
    have ih1 := trD_edit C t (fun h => trE_edit hk C t h ho.1) hs.1 ho.1
    have ih2 := trDs_edit C ts hs.2 ho.2
    simp [trDs, editEs, peditB_append, ih1, ih2]
end

theorem trAug_edit (C : List Scope) (l : Label) (t : Expr) (haug : augOk R t = true)
    (hs : ∀ x ∈ sitesAug R C l t (sitesT R C deadSrc t (sitesE R C t)), x.Agrees R')
    (ho : ∀ l ∈ olabelsE R t, NB R' l) :
    PyCore.editB R' (trAug C l t (trT C deadSrc t (trE C t))).1 =
        (trAug (editChain R C) l (editE R t) (trT (editChain R C) deadSrc (editE R t)
          (trE (editChain R C) (editE R t)))).1 ∧
    PyCore.editB R' (trAug C l t (trT C deadSrc t (trE C t))).2 =
        (trAug (editChain R C) l (editE R t) (trT (editChain R C) deadSrc (editE R t)
          (trE (editChain R C) (editE R t)))).2 := by
  have hsimp : simpleT t = true := by simp only [augOk, Bool.and_eq_true] at haug; exact haug.1
  cases hR : R.e t.label with
  | some t' =>
    unfold sitesAug at hs; simp only [hR, List.forall_mem_append] at hs
    rw [editE_site hR]
    have hn1 : (trAug C l t (trT C deadSrc t (trE C t))).1 ≠ [] := by cases t <;> simp [trAug]
    have hn2 : (trAug C l t (trT C deadSrc t (trE C t))).2 ≠ [] := by
      cases t <;> simp_all [trAug, simpleT]
    exact ⟨peditB_stmtSites hs.1 hn1, peditB_stmtSites hs.2 hn2⟩
  | none =>
    have hl : NB R' t.label := ho _ (by cases t <;> simp_all [olabelsE, ocut, Expr.label])
    cases t with
    | name lt x =>
      simp only [Expr.label] at hR hl
      simp (disch := omega) [trAug, editE, hR, PyCore.editB, PyCore.editS, PyCore.editE, hl.1, hl.2.1, nm]
    | attr lt o a =>
      simp only [Expr.label] at hR hl
      unfold sitesAug at hs; simp only [hR, Expr.label] at hs
      have ih := trE_edit hk C o hs fromO
      simp (disch := omega) [trAug, editE, hR, PyCore.editB, PyCore.editS, PyCore.editE, hl.1, hl.2.1, nm,
        peditE_cc hl, ih]
    | sub lt o i =>
      simp only [Expr.label] at hR hl
      unfold sitesAug at hs; simp only [hR, Expr.label, List.forall_mem_append] at hs
      have ih1 := trE_edit hk C o hs.1 fromO; have ih2 := trE_edit hk C i hs.2 fromO
      simp (disch := omega) [trAug, editE, hR, PyCore.editB, PyCore.editS, PyCore.editE, hl.1, hl.2.1, nm,
        peditE_cc hl, ih1, ih2]
    | _ => simp [simpleT] at hsimp

omit hk in
theorem trB_append (C : List Scope) : ∀ a b : List Stmt, trB C (a ++ b) = trB C a ++ trB C b
  | [], _ => rfl
  | s :: a, b => by simp [trB, trB_append C a b]

omit hk in
theorem trS_label (C : List Scope) (s : Stmt) : (trS C s).label = sub s.label 0 := by
  cases s with
  | raise l e c => cases e <;> cases c <;> simp [trS, blk, PyCore.Stmt.label, Stmt.label]
  | impFrom l m al lv => simp only [trS]; split <;> simp [blk, PyCore.Stmt.label, Stmt.label]
  | annassign l t a v => cases v <;> simp [trS, blk, PyCore.Stmt.label, Stmt.label]
  | _ => simp [trS, blk, PyCore.Stmt.label, Stmt.label]

omit hk in
theorem editS_site {s : Stmt} {ss : List Stmt} (h : R.s s.label = some ss) : editS R s = ss := by
  cases s <;> simp_all [editS, Stmt.label]

omit hk in
theorem siteS_edit {C : List Scope} {s : Stmt} {ss : List Stmt} (hR : R.s s.label = some ss)
    (hx : (PSite.s (sub s.label 0) (trB (editChain R C) ss)).Agrees R') :
    trB (editChain R C) (editS R s) = PyCore.editS R' (trS C s) := by
  rw [editS_site hR, peditS_site (by rw [trS_label]; exact hx)]

theorem trAnnK_edit (C : List Scope) (k : PKind) : ∀ ps, (∀ x ∈ sitesAnnK R C k ps, x.Agrees R') →
    (∀ l ∈ olabelsPs R ps, NB R' l) →
    (trAnnK C k ps).map (PyCore.editE R') = trAnnK (editChain R C) k (editPs R ps)
  | [], _, _ => rfl
  | .mk l x k' d (some a) :: ps, hs, ho => by
    have ih2 := trAnnK_edit C k ps (fun y hy => hs y (by simp [sitesAnnK, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    by_cases h : k' = k
    · subst h
      have ih1 := trE_edit hk C a (fun y hy => hs y (by simp [sitesAnnK, hy]))
        (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
      simp [trAnnK, editPs, editO, ih1, ih2]
    · simp [trAnnK, editPs, editO, h, ih2]
  | .mk l x k' d none :: ps, hs, ho => by
    have ih2 := trAnnK_edit C k ps (fun y hy => hs y (by simp [sitesAnnK, hy]))
      (fun y hy => ho y (by simp [olabelsPs, olabelsO, hy]))
    simp [trAnnK, editPs, editO, ih2]


omit hk in
theorem annT_edit (C : List Scope) (l : Label) (t : Expr) (hl : NB R' l)
    (hs : ∀ x ∈ (match R.e t.label with
      | some t' => stmtSites (annT C l t) (annT (editChain R C) l t')
      | none => []), x.Agrees R')
    (ht : R.e t.label = none → NB R' t.label) :
    PyCore.editB R' (annT C l t) = annT (editChain R C) l (editE R t) := by
  cases hR : R.e t.label with
  | some t' =>
    simp only [hR] at hs; rw [editE_site hR]; exact peditB_stmtSites hs (by cases t <;> simp [annT])
  | none =>
    have h := ht hR
    cases t <;> simp only [Expr.label] at hR h <;>
      simp (disch := omega) [annT, editE, hR, PyCore.editB, PyCore.editS, PyCore.editE, Expr.label, nm,
        h.1, h.2.1, hl.1, peditE_ccR_sub h, priv_edit]

omit hk in
theorem annBind_edit (C : List Scope) (t : Expr)
    (hs : ∀ x ∈ (match R.e t.label with
      | some t' => stmtSites (annBind C t) (annBind (editChain R C) t')
      | none => []), x.Agrees R')
    (ht : R.e t.label = none → NB R' t.label) :
    PyCore.editB R' (annBind C t) = annBind (editChain R C) (editE R t) := by
  cases hR : R.e t.label with
  | some t' =>
    simp only [hR] at hs; rw [editE_site hR]; exact peditB_stmtSites hs (by cases t <;> simp [annBind])
  | none =>
    have h := ht hR
    cases t <;> simp only [Expr.label] at hR h <;>
      simp (disch := omega) [annBind, editE, hR, PyCore.editB, PyCore.editS, PyCore.editE, Expr.label,
        h.1, h.2.1, priv_edit]

theorem annBare_edit (C : List Scope) (t : Expr)
    (hs : ∀ x ∈ sitesBare R C t (sitesT R C deadSrc t (sitesE R C t)), x.Agrees R')
    (ho : ∀ l ∈ olabelsE R t, NB R' l) :
    PyCore.editB R' (annBare C t (trT C deadSrc t (trE C t))) =
      annBare (editChain R C) (editE R t) (trT (editChain R C) deadSrc (editE R t) (trE (editChain R C) (editE R t))) := by
  cases hR : R.e t.label with
  | some t' =>
    unfold sitesBare at hs; simp only [hR] at hs
    rw [editE_site hR]; exact peditB_stmtSites hs (by cases t <;> simp [annBare])
  | none =>
    have hl : NB R' t.label := ho _ (by cases t <;> simp_all [olabelsE, ocut, Expr.label])
    cases t with
    | name lt x =>
      simp only [Expr.label] at hR hl
      simp (disch := omega) [annBare, editE, hR, PyCore.editB, PyCore.editS, PyCore.editE, hl.1, hl.2.1]
    | attr lt o a =>
      simp only [Expr.label] at hR hl
      unfold sitesBare at hs; simp only [hR, Expr.label] at hs
      have ih := trE_edit hk C o hs fromO
      simp (disch := omega) [annBare, editE, hR, PyCore.editB, PyCore.editS, hl.2.1, ih]
    | sub lt o i =>
      simp only [Expr.label] at hR hl
      unfold sitesBare at hs; simp only [hR, Expr.label, List.forall_mem_append] at hs
      have ih1 := trE_edit hk C o hs.1 fromO; have ih2 := trE_edit hk C i hs.2 fromO
      simp (disch := omega) [annBare, editE, hR, PyCore.editB, PyCore.editS, hl.2.1, peditE_recR_sub hl, ih1, ih2]
    | _ =>
      simp only [Expr.label] at hR hl
      unfold sitesBare at hs; simp only [hR, Expr.label] at hs
      have ih := trT_edit hk C deadSrc srcFix_dead _ (fun h => trE_edit hk C _ h ho) hs ho
      simp only [editE, hR, Option.getD_none] at ih ⊢
      simp (disch := omega) [annBare, Expr.label, PyCore.editB, PyCore.editS, PyCore.editE, stuckAt, dead,
        hl.2.1, hl.1, peditE_ccR_sub hl, ih]

set_option hygiene false in
macro "fromSS" : term => `(fun x hx => hs x (by
  simp [sitesS, stmtSite, Stmt.label, sitesHs, sitesB, sitesAnn, sitesAnnA, sitesO, sitesEs, hR, hx]))
set_option hygiene false in
macro "fromOS" : term => `(fun x hx => ho x (by
  simp [olabelsS, olabelsE, olabelsO, olabelsEs, olabelsKs, olabelsPs, olabelsHs, olabelsB, ocut, hR, hx]))
set_option hygiene false in
macro "nblS" : tactic => `(tactic| have hl : NB R' l := ho l (by simp [olabelsS, ocut, hR]))
set_option hygiene false in
macro "siteSC" : tactic => `(tactic| exact siteS_edit hR (hs _ (by simp [sitesS, stmtSite, Stmt.label, hR])))
set_option hygiene false in
/-- The simplification that closes a non-site statement. -/
macro "stS" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (disch := omega) [editS, hR, Option.getD_none, trB, trS, blk, PyCore.editS, PyCore.editB,
    PyCore.editHs, PyCore.editE, hl.1, hl.2.1, hl.2.2, peditB_append, priv_edit, List.map_append,
    peditE_cc hl, peditE_gad hl, peditE_ccR_sub hl, peditE_recR_sub hl, $ls,*])

mutual
theorem trS_edit (C : List Scope) : ∀ s, regS R C s = true → (∀ x ∈ sitesS R C s, x.Agrees R') →
    (∀ l ∈ olabelsS R C s, NB R' l) → trB (editChain R C) (editS R s) = PyCore.editS R' (trS C s)
  | .expr l e, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none => nblS; have ih1 := trE_edit hk C e fromSS fromOS; stS [ih1]
  | .assign l ts e, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      have ih1 := trE_edit hk C e fromSS fromOS
      have h2 : ∀ ts, (∀ x ∈ sitesTs R C (nameSrc "t" l) ts, x.Agrees R') → (∀ y ∈ olabelsEs R ts, NB R' y) →
          PyCore.editB R' (trTs C (nameSrc "t" l) ts) = trTs (editChain R C) (nameSrc "t" l) (editEs R ts) := by
        intro ts; induction ts with
        | nil => intros; rfl
        | cons t ts ih =>
          intro hs' ho'
          simp only [sitesTs, olabelsEs, List.forall_mem_append] at hs' ho'
          simp [trTs, editEs, peditB_append, ih hs'.2 ho'.2,
            trT_edit hk C (nameSrc "t" l) (srcFix_name "t" l) t (fun h => trE_edit hk C t h ho'.1) hs'.1 ho'.1]
      have ih2 := h2 ts fromSS fromOS
      stS [ih1, ih2]
  | .augassign l t op e, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      have haug : augOk R t = true := by simpa [regS, hR] using hr
      have ih1 := trE_edit hk C e fromSS fromOS
      obtain ⟨ih2, ih3⟩ := trAug_edit hk C l t haug fromSS fromOS
      stS [ih1, ih2, ih3, nm]
  | .annassign l t a v, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      have hot : ∀ y ∈ olabelsE R t, NB R' y := fromOS
      have ht : R.e t.label = none → NB R' t.label := fun h =>
        hot _ (by cases t <;> simp_all [olabelsE, ocut, Expr.label])
      cases v with
      | some e =>
        have ih1 := trE_edit hk C a fromSS fromOS
        have ih2 := trE_edit hk C e fromSS fromOS
        have ih3 := trT_edit hk C (nameSrc "t" l) (srcFix_name "t" l) t (fun h => trE_edit hk C t h hot) fromSS hot
        cases hT : isTop C
        · stS [editO, ih1, ih2, ih3, hT, isTop_edit, nm, dead]
        · have hA := annT_edit C l t hl (fun x hx => hs x (by
            simp only [sitesS, stmtSite, Stmt.label, hR, sitesAnn, sitesAnnA, hT, ite_true, List.mem_append]
            grind)) ht
          stS [editO, ih1, ih2, ih3, hA, hT, isTop_edit, nm, dead]
      | none =>
        have ih1 := trE_edit hk C a fromSS fromOS
        have ih3 := annBare_edit hk C t fromSS hot
        have hB := annBind_edit C t (fun x hx => hs x (by
          simp only [sitesS, stmtSite, Stmt.label, hR, sitesAnn, sitesAnnA, List.mem_append]; grind)) ht
        cases hT : isTop C
        · stS [editO, ih1, ih3, hB, hT, isTop_edit, dead]
        · have hA := annT_edit C l t hl (fun x hx => hs x (by
            simp only [sitesS, stmtSite, Stmt.label, hR, sitesAnn, sitesAnnA, hT, ite_true, List.mem_append]
            grind)) ht
          stS [editO, ih1, ih3, hA, hB, hT, isTop_edit, dead]
  | .del l ts, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none => nblS; have ih1 := trDs_edit hk C ts fromSS fromOS; stS [ih1]
  | .ite l c t u, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
      have ih1 := trE_edit hk C c fromSS fromOS
      have ih2 := trB_edit C t hr.1 fromSS fromOS; have ih3 := trB_edit C u hr.2 fromSS fromOS
      stS [ih1, ih2, ih3]
  | .while l c b u, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
      have ih1 := trE_edit hk C c fromSS fromOS
      have ih2 := trB_edit C b hr.1 fromSS fromOS; have ih3 := trB_edit C u hr.2 fromSS fromOS
      stS [ih1, ih2, ih3]
  | .for l t it b u, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
      have ih1 := trE_edit hk C it fromSS fromOS
      have ih2 := trT_edit hk C (forSrc l) (srcFix_for l) t (fun h => trE_edit hk C t h fromOS) fromSS fromOS
      have ih3 := trB_edit C b hr.1 fromSS fromOS; have ih4 := trB_edit C u hr.2 fromSS fromOS
      stS [ih1, ih2, ih3, ih4, peditB_forLoop hl]
  | .brk l, _, hs, ho | .cont l, _, hs, ho | .pass l, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none => nblS; stS []
  | .ret l e, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none => nblS; have ih1 := trO_edit hk C l 1 e (hl.1 1 (by omega)) fromSS fromOS; stS [ih1]
  | .defn l f ps b ds r, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
    cases hq : qualCh R C f with
    | true =>
      have hx := hs (.s (sub l 0) (trB (editChain R C) (editS R (.defn l f ps b ds r))))
        (by simp [sitesS, stmtSite, Stmt.label, hR, hq])
      simp only [PSite.Agrees] at hx
      exact (peditS_site (s := trS C (.defn l f ps b ds r)) (by rw [trS_label]; exact hx)).symm
    | false =>
      simp only [sitesS, stmtSite, Stmt.label, hR, hq, Bool.false_eq_true, ite_false] at hs
      simp only [olabelsS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false, List.append_nil] at ho
      have hl : NB R' l := ho l (by simp)
      simp only [regS, hR, Option.isSome_none, Bool.false_or] at hr
      have ih1 := trEs_edit hk C ds fromSS fromOS
      have ih2 := trDfs_edit hk C ps fromSS fromOS
      have ik1 := trAnnK_edit hk C .pos ps fromSS fromOS
      have ik2 := trAnnK_edit hk C .posonly ps fromSS fromOS
      have ik3 := trAnnK_edit hk C .vararg ps fromSS fromOS
      have ik4 := trAnnK_edit hk C .kwonly ps fromSS fromOS
      have ik5 := trAnnK_edit hk C .kwarg ps fromSS fromOS
      have ih4 := trB_edit (.fn l f ps b :: C) b hr fromSS fromOS
      simp only [editChain_cons, editSc] at ih4
      have hpb := peditB_paramBind (.fn l f ps b :: C) ps
        (fun q hq => ho _ (by simp [mem_olabelsPs R hq]))
      have hpm : List.map (PyCore.editE R' ∘ paramMark (.fn l f ps b :: C)) ps = ps.map (paramMark (.fn l f ps b :: C)) :=
        List.map_congr_left (fun q hq => peditE_paramMark _ (ho _ (by simp [mem_olabelsPs R hq])))
      have hpe := paramBind_edit R (C := .fn l f ps b :: C)
          (C' := .fn l f (editPs R ps) (editB R b) :: editChain R C) (by simp [priv]) ps
      have hme := paramMark_edit R (C := .fn l f ps b :: C)
          (C' := .fn l f (editPs R ps) (editB R b) :: editChain R C) (by simp [priv]) ps
      cases r with
      | none =>
        stS [editO, ih1, ih2, ik1, ik2, ik3, ik4, ik5, ← ih4, hpb, hpm, hpe, hme, editEs_length, editPs_length]
      | some r =>
        have ih3 := trE_edit hk C r fromSS fromOS
        stS [editO, ih1, ih2, ih3, ik1, ik2, ik3, ik4, ik5, ← ih4, hpb, hpm, hpe, hme, editEs_length, editPs_length]
  | .cls l x bs ks b ds, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
    cases hq : qualCh R C x with
    | true =>
      have hx := hs (.s (sub l 0) (trB (editChain R C) (editS R (.cls l x bs ks b ds))))
        (by simp [sitesS, stmtSite, Stmt.label, hR, hq])
      simp only [PSite.Agrees] at hx
      exact (peditS_site (s := trS C (.cls l x bs ks b ds)) (by rw [trS_label]; exact hx)).symm
    | false =>
      simp only [sitesS, stmtSite, Stmt.label, hR, hq, Bool.false_eq_true, ite_false] at hs
      simp only [olabelsS, hR, hq, Option.isSome_none, Bool.false_eq_true, ite_false, List.append_nil] at ho
      have hl : NB R' l := ho l (by simp)
      have hq' : qualIn (editChain R C) x = qualIn C x := by simpa [qualCh] using hq
      simp only [regS, hR, Option.isSome_none, Bool.false_or] at hr
      have ih1 := trEs_edit hk C ds fromSS fromOS
      have ih2 := trA_edit hk C bs fromSS fromOS
      have ih3 := trKs_edit hk C ks fromSS fromOS
      have ih4 := trB_edit (.cl l x b :: C) b hr fromSS fromOS
      simp only [editChain_cons, editSc] at ih4
      stS [ih1, ih2.1, ih2.2, ih3.1, ih3.2, kwMarks_edit, ← ih4, hq', setupS, editEs_length]
  | .glob l xs, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      stS [peditB_fix (R' := R') (fun x => PyCore.Stmt.glob (sub l 1) (mangle (priv C) x)) xs
        (fun x _ => by simp (disch := omega) [PyCore.editS, hl.2.1])]
  | .nonloc l xs, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      stS [peditB_fix (R' := R') (fun x => PyCore.Stmt.nonloc (sub l 1) (mangle (priv C) x)) xs
        (fun x _ => by simp (disch := omega) [PyCore.editS, hl.2.1])]
  | .tryE l b hz u, hr, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
      have ih1 := trB_edit C b hr.1.1 fromSS fromOS; have ih2 := trHs_edit C hz hr.1.2 fromSS fromOS
      have ih3 := trB_edit C u hr.2 fromSS fromOS
      stS [ih1, ih2, ih3]
  | .raise l e c, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      cases e with
      | none =>
        cases c with
        | none => stS [editO]
        | some c => have ih2 := trE_edit hk C c fromSS fromOS; stS [editO, ih2, stuckAt, dead]
      | some e =>
        have ih1 := trE_edit hk C e fromSS fromOS
        cases c with
        | none => stS [editO, ih1]
        | some c => have ih2 := trE_edit hk C c fromSS fromOS; stS [editO, ih1, ih2]
  | .imp l al, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      have hal : ∀ a ∈ al, NB R' a.l := fun a ha => ho a.l (by
        simp only [olabelsS, ocut, hR, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_cons,
          List.mem_map]
        exact .inr ⟨a, ha, rfl⟩)
      stS []
      refine (peditB_fix _ al (fun a ha => ?_)).symm
      have h := hal a ha
      split <;> simp (disch := omega) [PyCore.editS, PyCore.editE, stuckAt, h.1, h.2.1, cc, peditE_ccR_sub h]
  | .impFrom l m al lvl, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      have hal : ∀ a ∈ al, NB R' a.l := fun a ha => ho a.l (by
        simp only [olabelsS, ocut, hR, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_cons,
          List.mem_map]
        exact .inr ⟨a, ha, rfl⟩)
      simp only [editS, hR, Option.getD_none, trB, trS]
      split
      · stS [dead]
        refine (peditB_fix _ _ (fun a ha => ?_)).symm
        have h := hal a (List.mem_filter.mp ha).1
        simp (disch := omega) [PyCore.editS, PyCore.editE, h.1, h.2.1]
      · stS []
        refine (peditB_fix _ al (fun a ha => ?_)).symm
        have h := hal a ha
        split <;> simp (disch := omega) [PyCore.editS, PyCore.editE, h.1, h.2.1, cc, gad, nm, peditE_ccR_sub h]
  | .assert l t m, _, hs, ho => by
    cases hR : R.s l with
    | some ss => siteSC
    | none =>
      nblS
      have ih1 := trE_edit hk C t fromSS fromOS
      cases m with
      | none => stS [editO, ih1]
      | some m => have ih2 := trE_edit hk C m fromSS fromOS; stS [editO, ih1, ih2]
theorem trHs_edit (C : List Scope) : ∀ hz, regHs R C hz = true → (∀ x ∈ sitesHs R C hz, x.Agrees R') →
    (∀ l ∈ olabelsHs R C hz, NB R' l) → trHs (editChain R C) (editHs R hz) = PyCore.editHs R' (trHs C hz)
  | [], _, _, _ => rfl
  | .mk l ty x b :: hz, hr, hs, ho => by
    simp only [regHs, Bool.and_eq_true] at hr
    have ih := trHs_edit C hz hr.2 (fun x hx => hs x (by simp [sitesHs, hx]))
      (fun x hx => ho x (by simp [olabelsHs, hx]))
    cases hR : R.h l with
    | some h' =>
      obtain ⟨lh, ty', x', b'⟩ := h'
      have hx : ∀ y ∈ (trHs (editChain R C) [.mk lh ty' x' b']).map (PSite.h (sub l 0)), y.Agrees R' :=
        fun y hy => hs y (by simp [sitesHs, hR, hy])
      simp only [trHs, List.map_cons, List.map_nil, List.forall_mem_cons, PSite.Agrees] at hx
      simp [editHs, hR, trHs, PyCore.editHs, hx.1, ih]
    | none =>
      have hl : NB R' l := ho l (by simp [olabelsHs, ocut, hR])
      have ih2 := trB_edit C b (by simpa [hR] using hr.1) (fun x hx => hs x (by simp [sitesHs, hR, hx]))
        (fun x hx => ho x (by simp [olabelsHs, ocut, hR, hx]))
      cases ty with
      | none => simp (disch := omega) [editHs, hR, trHs, PyCore.editHs, PyCore.editE, hl.1, hl.2.2, ih, ih2, editO]
      | some t =>
        have ih3 := trE_edit hk C t (fun x hx => hs x (by simp [sitesHs, sitesO, hR, hx]))
          (fun x hx => ho x (by simp [olabelsHs, olabelsO, ocut, hR, hx]))
        simp (disch := omega) [editHs, hR, trHs, PyCore.editHs, hl.2.2, ih, ih2, editO, ih3]
theorem trB_edit (C : List Scope) : ∀ ss, regB R C ss = true → (∀ x ∈ sitesB R C ss, x.Agrees R') →
    (∀ l ∈ olabelsB R C ss, NB R' l) → trB (editChain R C) (editB R ss) = PyCore.editB R' (trB C ss)
  | [], _, _, _ => rfl
  | s :: ss, hr, hs, ho => by
    simp only [regB, Bool.and_eq_true] at hr
    simp only [sitesB, olabelsB, List.forall_mem_append] at hs ho
    simp only [editB, trB_append, trB, PyCore.editB, trS_edit C s hr.1 hs.1 ho.1, trB_edit C ss hr.2 hs.2 ho.2]
end

end

/-! ## `trEdit` fits: the labels outside the sites and in them -/

section
variable (R : Edit)

set_option hygiene false in
/-- A count equation of `olabels`, `p1`, and `labels` at a node `l`. -/
macro "cntC" : tactic => `(tactic| (cases hR : R.e l <;>
  simp [olabelsE, olabelsO, olabelsEs, p1E, p1O, p1Es, labelsE, labelsO, labelsEs, ocut, hR,
    List.count_append, List.count_cons] <;> omega))

mutual
/-- Each label of `e` is outside its sites or in part (1), as often as it occurs. -/
theorem cntE (x : Label) : ∀ e, (olabelsE R e).count x + (p1E R e).count x = (labelsE e).count x
  | .const l _ | .name l _ => by cntC
  | .bin l _ a b | .sub l a b => by have := cntE x a; have := cntE x b; cntC
  | .unary l _ a | .attr l a _ | .star l a | .walrus l _ a | .yieldFrom l a => by have := cntE x a; cntC
  | .boolop l _ es | .list l es | .tuple l es | .set l es | .fstr l es => by have := cntEs x es; cntC
  | .compare l a _ es => by have := cntE x a; have := cntEs x es; cntC
  | .ifexp l c a b => by have := cntE x c; have := cntE x a; have := cntE x b; cntC
  | .call l f as ks => by have := cntE x f; have := cntEs x as; have := cntKs x ks; cntC
  | .slice l a b c => by have := cntO x a; have := cntO x b; have := cntO x c; cntC
  | .dict l kvs => by have := cntDs x kvs; cntC
  | .lam l ps b => by have := cntPs x ps; have := cntE x b; cntC
  | .comp l _ es gs => by have := cntEs x es; have := cntGs x gs; cntC
  | .yield l e => by have := cntO x e; cntC
  | .fmt l e _ sp => by have := cntE x e; have := cntO x sp; cntC
theorem cntO (x : Label) : ∀ o, (olabelsO R o).count x + (p1O R o).count x = (labelsO o).count x
  | none => rfl
  | some e => cntE x e
theorem cntEs (x : Label) : ∀ es, (olabelsEs R es).count x + (p1Es R es).count x = (labelsEs es).count x
  | [] => rfl
  | e :: es => by
    have := cntE x e; have := cntEs x es
    simp [olabelsEs, p1Es, labelsEs, List.count_append]; omega
theorem cntKs (x : Label) : ∀ ks, (olabelsKs R ks).count x + (p1Ks R ks).count x = (labelsKs ks).count x
  | [] => rfl
  | .mk l _ e :: ks => by
    have := cntE x e; have := cntKs x ks
    simp [olabelsKs, p1Ks, labelsKs, List.count_append, List.count_cons]; omega
theorem cntDs (x : Label) : ∀ kvs, (olabelsDs R kvs).count x + (p1Ds R kvs).count x = (labelsDs kvs).count x
  | [] => rfl
  | .mk k v :: kvs => by
    have := cntO x k; have := cntE x v; have := cntDs x kvs
    simp [olabelsDs, p1Ds, labelsDs, List.count_append]; omega
theorem cntPs (x : Label) : ∀ ps, (olabelsPs R ps).count x + (p1Ps R ps).count x = (labelsPs ps).count x
  | [] => rfl
  | .mk l _ _ d a :: ps => by
    have := cntO x d; have := cntO x a; have := cntPs x ps
    simp [olabelsPs, p1Ps, labelsPs, List.count_append, List.count_cons]; omega
theorem cntGs (x : Label) : ∀ gs, (olabelsGs R gs).count x + (p1Gs R gs).count x = (labelsGs gs).count x
  | [] => rfl
  | .mk l t i ifs :: gs => by
    have := cntE x t; have := cntE x i; have := cntEs x ifs; have := cntGs x gs
    simp [olabelsGs, p1Gs, labelsGs, List.count_append, List.count_cons]; omega
end

set_option hygiene false in
macro "cntSC" : tactic => `(tactic| (cases hR : R.s l <;>
  simp [olabelsS, olabelsO, olabelsEs, p1S, p1Site, p1O, p1Es, qcS, labelsS, labelsO, labelsEs, Stmt.label,
    ocut, hR, List.count_append, List.count_cons] <;> omega))

mutual
theorem cntS (x : Label) (C : List Scope) : ∀ s,
    (olabelsS R C s).count x + (p1S R s).count x + (qcS R C s).count x = (labelsS s).count x
  | .expr l e => by have := cntE R x e; cntSC
  | .assign l ts e => by have := cntEs R x ts; have := cntE R x e; cntSC
  | .augassign l t _ e => by have := cntE R x t; have := cntE R x e; cntSC
  | .annassign l t a v => by have := cntE R x t; have := cntE R x a; have := cntO R x v; cntSC
  | .del l ts => by have := cntEs R x ts; cntSC
  | .ite l c t u => by have := cntE R x c; have := cntB x C t; have := cntB x C u; cntSC
  | .while l c t u => by have := cntE R x c; have := cntB x C t; have := cntB x C u; cntSC
  | .for l t it b u => by
    have := cntE R x t; have := cntE R x it; have := cntB x C b; have := cntB x C u; cntSC
  | .brk l | .cont l | .pass l | .glob l _ | .nonloc l _ | .imp l _ | .impFrom l _ _ _ => by cntSC
  | .ret l e => by have := cntO R x e; cntSC
  | .defn l f ps b ds r => by
    have := cntPs R x ps; have := cntB x (.fn l f ps b :: C) b; have := cntEs R x ds; have := cntO R x r
    cases hq : qualCh R C f <;> cases hR : R.s l <;>
      simp [olabelsS, p1S, p1Site, qcS, labelsS, Stmt.label, hR, hq, List.count_append, List.count_cons] <;>
      omega
  | .cls l y bs ks b ds => by
    have := cntEs R x bs; have := cntKs R x ks; have := cntB x (.cl l y b :: C) b; have := cntEs R x ds
    cases hq : qualCh R C y <;> cases hR : R.s l <;>
      simp [olabelsS, p1S, p1Site, qcS, labelsS, Stmt.label, hR, hq, List.count_append, List.count_cons] <;>
      omega
  | .tryE l b hs u => by have := cntB x C b; have := cntHs x C hs; have := cntB x C u; cntSC
  | .raise l e c => by have := cntO R x e; have := cntO R x c; cntSC
  | .assert l t m => by have := cntE R x t; have := cntO R x m; cntSC
theorem cntHs (x : Label) (C : List Scope) : ∀ hs,
    (olabelsHs R C hs).count x + (p1Hs R hs).count x + (qcHs R C hs).count x = (labelsHs hs).count x
  | [] => rfl
  | .mk l ty _ b :: hs => by
    have := cntO R x ty; have := cntB x C b; have := cntHs x C hs
    cases hR : R.h l <;> simp [olabelsHs, p1Hs, qcHs, labelsHs, ocut, hR, List.count_append, List.count_cons] <;>
      omega
theorem cntB (x : Label) (C : List Scope) : ∀ ss,
    (olabelsB R C ss).count x + (p1B R ss).count x + (qcB R C ss).count x = (labelsB ss).count x
  | [] => rfl
  | s :: ss => by
    have := cntS x C s; have := cntB x C ss
    simp [olabelsB, p1B, qcB, labelsB, List.count_append]; omega
end

end


/-! ## `trEdit` fits: the roots of its sites -/

/-- The roots a PyCore site for the Surf node `l` may have: the nodes made for it. -/
def rt (l : Label) : List Label := (List.range 64).map (sub l)

theorem sub_inj {l l' k k' : Nat} (hk : k < 64) (hk' : k' < 64) (h : sub l k = sub l' k') :
    l = l' ∧ k = k' := by
  have h' : 64 * l + k = 64 * l' + k' := h
  have : l = l' := by omega
  subst this; omega

theorem sub_ne {a b k k' : Nat} (hk : k < 64) (hk' : k' < 64) (h : k ≠ k') : sub a k ≠ sub b k' :=
  fun he => h (sub_inj hk hk' he).2

theorem mem_rt {l k : Nat} (hk : k < 64) : sub l k ∈ rt l := List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem mem_rts {A : List Label} {l k : Nat} (hl : l ∈ A) (hk : k < 64) : sub l k ∈ A.flatMap rt :=
  List.mem_flatMap.mpr ⟨l, hl, mem_rt hk⟩

theorem labelsE_head (e : Expr) : e.label ∈ labelsE e := by cases e <;> simp [labelsE, Expr.label]
theorem labelsS_head (s : Stmt) : s.label ∈ labelsS s := by cases s <;> simp [labelsS, Stmt.label]

theorem labelsE_unstar (e : Expr) : ∀ x ∈ labelsE (unstar e), x ∈ labelsE e := by
  cases e <;> intro x hx <;> simp_all [unstar, labelsE]

theorem ccR_label (r : Label) (g : String) (es : List PE) : (ccR r g es).label = r := rfl

/-- The root of an expression's translation is made for a node of it. -/
theorem trE_root (C : List Scope) : ∀ e, ∃ l' ∈ labelsE e, (trE C e).label = sub l' 0
  | .boolop l op [a] => by
    obtain ⟨l', h1, h2⟩ := trE_root C a
    exact ⟨l', by simp [labelsE, labelsEs, h1], by simpa [trE, trEs, boolChain] using h2⟩
  | .boolop l _ [] => ⟨l, by simp [labelsE], by simp [trE, trEs, boolChain, gad, cc, ccR, PyCore.Expr.label]⟩
  | .boolop l _ (_ :: _ :: _) => ⟨l, by simp [labelsE], by simp [trE, trEs, boolChain, PyCore.Expr.label]⟩
  | .compare l a ops es => ⟨l, by simp [labelsE], by
      rcases es with _ | ⟨b, _ | ⟨c, rest⟩⟩ <;> simp [trE, trLs, cmpOps, cmpChain, ccR, PyCore.Expr.label]⟩
  | .fmt l _ _ s => ⟨l, by simp [labelsE], by cases s <;> rfl⟩
  | .comp l _ _ gs => ⟨l, by simp [labelsE], by simp only [trE]; split <;> rfl⟩
  | .const l _ | .name l _ | .bin l _ _ _ | .unary l _ _ | .ifexp l _ _ _ | .call l _ _ _ | .attr l _ _
  | .sub l _ _ | .slice l _ _ _ | .star l _ | .list l _ | .tuple l _ | .set l _ | .dict l _ | .lam l _ _
  | .walrus l _ _ | .yield l _ | .yieldFrom l _ | .fstr l _ => ⟨l, by simp [labelsE], rfl⟩

theorem trT_labels (C : List Scope) (src : Label → PE) (t : Expr) (tE : PE) :
    (trT C src t tE).map PyCore.Stmt.label = [sub t.label 0] ∨
      (trT C src t tE).map PyCore.Stmt.label = [sub t.label 55, sub t.label 54] := by
  cases t <;> simp [trT, blk, stuckAt, dead, PyCore.Stmt.label, Expr.label]

theorem trD_labels (C : List Scope) (t : Expr) (tD : PS) :
    (trD C t tD).map PyCore.Stmt.label = [sub t.label 0] ∨
      (trD C t tD).map PyCore.Stmt.label = [sub t.label 55, sub t.label 54] := by
  cases t <;> simp [trD, blk, stuckAt, dead, PyCore.Stmt.label, Expr.label]

theorem stmtSites_roots (ss r : PS) : (stmtSites ss r).map PSite.root = ss.map PyCore.Stmt.label := by
  cases ss <;> simp [stmtSites, PSite.root, Function.comp_def]

theorem count_le_of_sub {A B : List Label} (hA : A.Nodup) (h : ∀ x ∈ A, x ∈ B) (L : Label) :
    A.count L ≤ B.count L := by
  have h1 := List.nodup_iff_count.mp hA L
  by_cases hL : L ∈ A
  · have := List.count_pos_iff.mpr (h L hL); omega
  · simp [List.count_eq_zero.mpr hL]

/-- Two roots made for nodes of `A` with different indices. -/
theorem two_roots {A : List Label} {a b k k' : Nat} (ha : a ∈ A) (hb : b ∈ A) (hk : k < 64) (hk' : k' < 64)
    (h : k ≠ k') (L : Label) : [sub a k, sub b k'].count L ≤ (A.flatMap rt).count L :=
  count_le_of_sub (by simp [sub_ne hk hk' h]) (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact mem_rts ha hk
    · exact mem_rts hb hk') L

theorem three_roots {A : List Label} {a b c k k' k'' : Nat} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hk : k < 64)
    (hk' : k' < 64) (hk'' : k'' < 64) (h1 : k ≠ k') (h2 : k ≠ k'') (h3 : k' ≠ k'') (L : Label) :
    [sub a k, sub b k', sub c k''].count L ≤ (A.flatMap rt).count L :=
  count_le_of_sub (by simp [sub_ne hk hk' h1, sub_ne hk hk'' h2, sub_ne hk' hk'' h3]) (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact mem_rts ha hk
    · exact mem_rts hb hk'
    · exact mem_rts hc hk'') L

theorem one_root {A : List Label} {a k : Nat} (ha : a ∈ A) (hk : k < 64) (L : Label) :
    [sub a k].count L ≤ (A.flatMap rt).count L :=
  count_le_of_sub (by simp) (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact mem_rts ha hk) L

theorem trT_root (C : List Scope) (src : Label → PE) (t : Expr) (tE : PE) {A : List Label} (ht : t.label ∈ A)
    (L : Label) : ((trT C src t tE).map PyCore.Stmt.label).count L ≤ (A.flatMap rt).count L := by
  rcases trT_labels C src t tE with h | h <;> rw [h]
  · exact one_root ht (by omega) L
  · exact two_roots ht ht (by omega) (by omega) (by omega) L

theorem trD_root (C : List Scope) (t : Expr) (tD : PS) {A : List Label} (ht : t.label ∈ A)
    (L : Label) : ((trD C t tD).map PyCore.Stmt.label).count L ≤ (A.flatMap rt).count L := by
  rcases trD_labels C t tD with h | h <;> rw [h]
  · exact one_root ht (by omega) L
  · exact two_roots ht ht (by omega) (by omega) (by omega) L

section
variable (R : Edit)

theorem p1E_site {e : Expr} {e' : Expr} (h : R.e e.label = some e') : p1E R e = labelsE e := by
  cases e <;> simp_all [p1E, Expr.label]

/-- A replaced item: its value's root and its marker. -/
theorem item_roots (C : List Scope) (e : Expr) (r m : PE) (L : Label) :
    [(trE C (unstar e)).label, sub e.label 57].count L ≤ ((labelsE e).flatMap rt).count L := by
  obtain ⟨l', h1, h2⟩ := trE_root C (unstar e)
  rw [h2]; exact two_roots (labelsE_unstar e _ h1) (labelsE_head e) (by omega) (by omega) (by omega) L

set_option hygiene false in
macro "rtC" : tactic => `(tactic| (cases hR : R.e l with
  | some e' =>
    simp only [sitesE, p1E, hR, Option.isSome_some, ite_true, List.map_cons, List.map_nil, siteE, PSite.root]
    obtain ⟨l', h1, h2⟩ := trE_root C _; rw [h2]; exact one_root h1 (by omega) L
  | none => simp [sitesE, sitesO, p1E, p1O, hR, List.count_append, List.map_append, List.flatMap_append] <;> omega))

mutual
/-- Each root of a site of `e` is made for a node of part (1), as often. -/
theorem rootE (C : List Scope) : ∀ (e : Expr) (L : Label),
    ((sitesE R C e).map PSite.root).count L ≤ ((p1E R e).flatMap rt).count L
  | .const l _, L | .name l _, L | .yield l none, L => by rtC
  | .bin l _ a b, L | .sub l a b, L => by have := rootE C a L; have := rootE C b L; rtC
  | .unary l _ a, L | .attr l a _, L | .yieldFrom l a, L | .walrus l _ a, L | .star l a, L
  | .yield l (some a), L => by have := rootE C a L; rtC
  | .boolop l _ es, L | .fstr l es, L => by have := rootEs C es L; rtC
  | .list l es, L | .tuple l es, L => by have := rootA C es L; rtC
  | .set l es, L => by have := rootSet C es L; rtC
  | .compare l a _ es, L => by have := rootE C a L; have := rootEs C es L; rtC
  | .ifexp l c a b, L => by have := rootE C c L; have := rootE C a L; have := rootE C b L; rtC
  | .call l f as ks, L => by have := rootE C f L; have := rootA C as L; have := rootKs C ks L; rtC
  | .slice l a b c, L => by have := rootO C a L; have := rootO C b L; have := rootO C c L; rtC
  | .dict l kvs, L => by have := rootKV C kvs L; rtC
  | .lam l ps b, L => by
    have hps := rootPs C ps L; have := rootE (.lam l ps b :: C) b L
    rw [List.map_append, List.count_append] at hps; rtC
  | .comp l k es gs, L => by
    have := rootEs (.comp l k es gs :: C) es L; have := rootComp C (.comp l k es gs :: C) gs L
    simp only [List.map_append, List.count_append] at this; rtC
  | .fmt l a _ sp, L => by have := rootE C a L; have := rootO C sp L; rtC
theorem rootO (C : List Scope) : ∀ (o : Option Expr) (L : Label),
    ((sitesO R C o).map PSite.root).count L ≤ ((p1O R o).flatMap rt).count L
  | none, _ => by simp [sitesO, p1O]
  | some e, L => rootE C e L
theorem rootEs (C : List Scope) : ∀ (es : List Expr) (L : Label),
    ((sitesEs R C es).map PSite.root).count L ≤ ((p1Es R es).flatMap rt).count L
  | [], _ => by simp [sitesEs, p1Es]
  | e :: es, L => by
    have := rootE C e L; have := rootEs C es L
    simp [sitesEs, p1Es, List.count_append, List.map_append, List.flatMap_append]; omega
theorem rootA (C : List Scope) : ∀ (es : List Expr) (L : Label),
    ((sitesA R C es).map PSite.root).count L ≤ ((p1Es R es).flatMap rt).count L
  | [], _ => by simp [sitesA, p1Es]
  | e :: es, L => by
    have := rootA C es L
    cases hR : R.e e.label with
    | some e' =>
      have h := item_roots C e (trE C e) (starMark e') L
      rw [← p1E_site R hR] at h
      simp only [sitesA, hR, p1Es, List.map_append, List.map_cons, List.map_nil, PSite.root,
        List.count_append, List.flatMap_append] at h ⊢
      simp only [List.count_cons, List.count_nil] at h ⊢; omega
    | none =>
      have := rootE C e L
      simp [sitesA, p1Es, hR, List.count_append, List.map_append, List.flatMap_append]; omega
theorem rootSet (C : List Scope) : ∀ (es : List Expr) (L : Label),
    ((sitesSet R C es).map PSite.root).count L ≤ ((p1Es R es).flatMap rt).count L
  | [], _ => by simp [sitesSet, p1Es]
  | e :: es, L => by
    have := rootSet C es L
    cases hR : R.e e.label with
    | some e' =>
      have h := item_roots C e (trE C e) (constMark 57 e') L
      rw [← p1E_site R hR] at h
      simp only [sitesSet, hR, p1Es, List.map_append, List.map_cons, List.map_nil, PSite.root,
        List.count_append, List.flatMap_append] at h ⊢
      simp only [List.count_cons, List.count_nil] at h ⊢; omega
    | none =>
      have := rootCm C e hR (rootE C e) L
      simp only [List.map_append, List.count_append] at this
      simp [sitesSet, p1Es, hR, List.count_append, List.map_append, List.flatMap_append]; omega
/-- A set item's value and constness marker sites. -/
theorem rootCm (C : List Scope) : ∀ (e : Expr), R.e e.label = none →
    (∀ L, ((sitesE R C e).map PSite.root).count L ≤ ((p1E R e).flatMap rt).count L) → ∀ L : Label,
    ((sitesE R C e ++ cmSites R e).map PSite.root).count L ≤ ((p1E R e).flatMap rt).count L
  | .unary l op a, hR, _, L => by
    simp only [Expr.label] at hR
    cases ha : R.e a.label with
    | some a' =>
      obtain ⟨l', h1, h2⟩ := trE_root C a
      have h := two_roots (A := labelsE a) h1 (labelsE_head a) (by omega : 0 < 64) (by omega : 50 < 64)
        (by omega) L
      have hs : sitesE R C a = [siteE R C a a'] := by cases a <;> simp_all [sitesE, Expr.label]
      simp only [sitesE, cmSites, hR, ha, hs, p1E, p1E_site R ha, List.map_append, List.map_cons,
        List.map_nil, siteE, PSite.root, h2, Option.isSome_none, Bool.false_eq_true, ite_false,
        List.cons_append, List.nil_append]
      exact h
    | none =>
      have := rootCm C a ha (rootE C a) L
      simp only [sitesE, cmSites, hR, ha, p1E, Option.isSome_none, Bool.false_eq_true, ite_false] at this ⊢
      exact this
  | .tuple l es, hR, _, L => by
    simp only [Expr.label] at hR
    have := rootCmL C es L
    simp only [sitesE, cmSites, hR, p1E, Option.isSome_none, Bool.false_eq_true, ite_false] at this ⊢
    exact this
  | .const .., _, he, L | .name .., _, he, L | .bin .., _, he, L | .boolop .., _, he, L
  | .compare .., _, he, L | .ifexp .., _, he, L | .call .., _, he, L | .attr .., _, he, L
  | .sub .., _, he, L | .slice .., _, he, L | .star .., _, he, L | .list .., _, he, L | .set .., _, he, L
  | .dict .., _, he, L | .lam .., _, he, L | .comp .., _, he, L | .walrus .., _, he, L
  | .yield .., _, he, L | .yieldFrom .., _, he, L | .fstr .., _, he, L | .fmt .., _, he, L => by
    simp only [cmSites, List.append_nil]; exact he L
theorem rootCmL (C : List Scope) : ∀ (es : List Expr) (L : Label),
    ((sitesA R C es ++ cmSitesL R es).map PSite.root).count L ≤ ((p1Es R es).flatMap rt).count L
  | [], _ => by simp [sitesA, cmSitesL, p1Es]
  | e :: es, L => by
    have ih := rootCmL C es L
    simp only [List.map_append, List.count_append] at ih
    cases hR : R.e e.label with
    | some e' =>
      obtain ⟨l', h1, h2⟩ := trE_root C (unstar e)
      have h := three_roots (A := labelsE e) (labelsE_unstar e _ h1) (labelsE_head e) (labelsE_head e)
        (by omega : 0 < 64) (by omega : 57 < 64) (by omega : 50 < 64) (by omega) (by omega) (by omega) L
      rw [← p1E_site R hR] at h
      simp only [sitesA, cmSitesL, hR, p1Es, List.map_append, List.map_cons, List.map_nil, PSite.root, h2,
        List.count_append, List.flatMap_append] at h ⊢
      simp only [List.count_cons, List.count_nil] at h ⊢; omega
    | none =>
      have := rootCm C e hR (rootE C e) L
      simp only [List.map_append, List.count_append] at this
      simp [sitesA, cmSitesL, p1Es, hR, List.count_append, List.map_append, List.flatMap_append]; omega
theorem rootKs (C : List Scope) : ∀ (ks : List Kw) (L : Label),
    ((sitesKs R C ks).map PSite.root).count L ≤ ((p1Ks R ks).flatMap rt).count L
  | [], _ => by simp [sitesKs, p1Ks]
  | .mk _ _ e :: ks, L => by
    have := rootE C e L; have := rootKs C ks L
    simp [sitesKs, p1Ks, List.count_append, List.map_append, List.flatMap_append]; omega
theorem rootKV (C : List Scope) : ∀ (kvs : List DItem) (L : Label),
    ((sitesKV R C kvs).map PSite.root).count L ≤ ((p1Ds R kvs).flatMap rt).count L
  | [], _ => by simp [sitesKV, p1Ds]
  | .mk k v :: kvs, L => by
    have := rootO C k L; have := rootE C v L; have := rootKV C kvs L
    simp [sitesKV, p1Ds, List.count_append, List.map_append, List.flatMap_append]; omega
theorem rootPs (C : List Scope) : ∀ (ps : List Param) (L : Label),
    ((sitesDf R C ps ++ sitesAn R C ps).map PSite.root).count L ≤ ((p1Ps R ps).flatMap rt).count L
  | [], _ => by simp [sitesDf, sitesAn, p1Ps]
  | .mk _ _ _ d a :: ps, L => by
    have := rootO C d L; have := rootO C a L; have := rootPs C ps L
    simp [sitesDf, sitesAn, p1Ps, List.count_append, List.map_append, List.flatMap_append] at *; omega
theorem rootGs (C : List Scope) : ∀ (first : Bool) (gs : List Gen) (L : Label),
    ((sitesGs R C first gs).map PSite.root).count L ≤ ((p1Gs R gs).flatMap rt).count L
  | _, [], _ => by simp [sitesGs, p1Gs]
  | first, .mk lg t i ifs :: gs, L => by
    have := rootE C i L; have := rootT C (forSrc lg) t (sitesE R C t) (rootE C t) L
    have := rootEs C ifs L; have := rootGs C false gs L
    cases first <;> simp [sitesGs, p1Gs, List.count_append, List.map_append, List.flatMap_append] <;> omega
/-- A comprehension's first iterable (in the scope around) and its generators (in its own). -/
theorem rootComp (C C' : List Scope) : ∀ (gs : List Gen) (L : Label),
    ((sitesG1 R C gs ++ sitesGs R C' true gs).map PSite.root).count L ≤ ((p1Gs R gs).flatMap rt).count L
  | [], _ => by simp [sitesG1, sitesGs, p1Gs]
  | .mk lg t i ifs :: gs, L => by
    have := rootE C i L; have := rootT C' (forSrc lg) t (sitesE R C' t) (rootE C' t) L
    have := rootEs C' ifs L; have := rootGs C' false gs L
    simp [sitesG1, sitesGs, p1Gs, List.count_append, List.map_append, List.flatMap_append]; omega
theorem rootT (C : List Scope) (src : Label → PE) : ∀ (t : Expr) (tS : List PSite),
    (∀ L, (tS.map PSite.root).count L ≤ ((p1E R t).flatMap rt).count L) → ∀ L,
    ((sitesT R C src t tS).map PSite.root).count L ≤ ((p1E R t).flatMap rt).count L
  | t, tS, htS, L => by
    cases hR : R.e t.label with
    | some t' =>
      unfold sitesT; simp only [hR]; rw [stmtSites_roots, p1E_site R hR]
      exact trT_root C src t _ (labelsE_head t) L
    | none =>
      cases t with
      | name lt x => simp only [Expr.label] at hR; simp [sitesT, Expr.label, hR]
      | attr lt o a =>
        have := rootE C o L
        simp only [Expr.label] at hR; simp [sitesT, p1E, Expr.label, hR] at this ⊢; omega
      | sub lt o i =>
        have := rootE C o L; have := rootE C i L
        simp only [Expr.label] at hR; simp [sitesT, p1E, Expr.label, hR, List.count_append] at *; omega
      | tuple lt ts =>
        have := rootIt C lt 0 ts L
        simp only [Expr.label] at hR; simp [sitesT, p1E, Expr.label, hR] at this ⊢; omega
      | list lt ts =>
        have := rootIt C lt 0 ts L
        simp only [Expr.label] at hR; simp [sitesT, p1E, Expr.label, hR] at this ⊢; omega
      | star ls e =>
        have := rootT C src e (sitesE R C e) (rootE C e) L
        simp only [Expr.label] at hR; simp [sitesT, p1E, Expr.label, hR] at this ⊢; omega
      | _ => simp only [Expr.label] at hR; simp only [sitesT, Expr.label, hR]; exact htS L
theorem rootIt (C : List Scope) (lt : Label) : ∀ (i : Nat) (ts : List Expr) (L : Label),
    ((sitesIt R C lt i ts).map PSite.root).count L ≤ ((p1Es R ts).flatMap rt).count L
  | _, [], _ => by simp [sitesIt, p1Es]
  | i, t :: ts, L => by
    have := rootIt C lt (i + 1) ts L
    cases hR : R.e t.label with
    | some t' =>
      have h : ((trT C (itemSrc lt i) (unstar t) (trE C (unstar t))).map PyCore.Stmt.label ++
          [sub t.label 57]).count L ≤ ((labelsE t).flatMap rt).count L := by
        have hu := labelsE_unstar t _ (labelsE_head (unstar t))
        rcases trT_labels C (itemSrc lt i) (unstar t) (trE C (unstar t)) with h | h <;> rw [h] <;>
          simp only [List.cons_append, List.nil_append]
        · exact two_roots hu (labelsE_head t) (by omega) (by omega) (by omega) L
        · exact three_roots hu hu (labelsE_head t) (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) L
      rw [← p1E_site R hR] at h
      simp only [sitesIt, hR, p1Es, List.map_append, List.map_cons, List.map_nil, PSite.root,
        List.count_append, List.flatMap_append, stmtSites_roots] at h ⊢
      simp only [List.count_cons, List.count_nil] at h ⊢; omega
    | none =>
      have := rootT C (itemSrc lt i) t (sitesE R C t) (rootE C t) L
      simp [sitesIt, p1Es, hR, List.count_append, List.map_append, List.flatMap_append]; omega
end

end

/-- Roots made for one node `lt` with distinct indices. -/
theorem roots_of {A : List Label} {lt : Nat} (ks : List Nat) (hk : ∀ k ∈ ks, k < 64) (hn : ks.Nodup)
    (ht : lt ∈ A) (L : Label) : (ks.map (sub lt)).count L ≤ (A.flatMap rt).count L := by
  refine count_le_of_sub ?_ (fun x hx => ?_) L
  · clear hk ht; induction ks with
    | nil => simp
    | cons k ks ih =>
      simp only [List.nodup_cons, List.map_cons, List.mem_map] at hn ⊢
      refine ⟨fun ⟨a, ha, h⟩ => hn.1 ?_, ih hn.2⟩
      have h' : 64 * lt + a = 64 * lt + k := h
      have : a = k := by omega
      subst this; exact ha
  · obtain ⟨k, hk', rfl⟩ := List.mem_map.mp hx; exact mem_rts ht (hk k hk')

theorem annBare_labels (C : List Scope) (t : Expr) (tT : PS) :
    (annBare C t tT).map PyCore.Stmt.label = [sub t.label 62] ∨
      (annBare C t tT).map PyCore.Stmt.label = [sub t.label 55, sub t.label 54] := by
  cases t <;> simp [annBare, stuckAt, dead, PyCore.Stmt.label, Expr.label]

theorem annT_labels (C : List Scope) (l : Label) (t : Expr) :
    (annT C l t).map PyCore.Stmt.label = [sub t.label 58] := by
  cases t <;> simp [annT, PyCore.Stmt.label, Expr.label]

theorem annBind_labels (C : List Scope) (t : Expr) :
    (annBind C t).map PyCore.Stmt.label = [sub t.label 60] := by
  cases t <;> simp [annBind, PyCore.Stmt.label, Expr.label]

section
variable (R : Edit)

theorem rootBare (C : List Scope) (t : Expr) (tS : List PSite) (ht : R.e t.label = none)
    (htS : ∀ L, (tS.map PSite.root).count L ≤ ((p1E R t).flatMap rt).count L) (L : Label) :
    ((sitesBare R C t tS).map PSite.root).count L ≤ ((p1E R t).flatMap rt).count L := by
  cases t with
  | name lt x => simp only [Expr.label] at ht; simp [sitesBare, Expr.label, ht]
  | attr lt o a =>
    have := rootE R C o L
    simp only [Expr.label] at ht; simp [sitesBare, p1E, Expr.label, ht] at this ⊢; omega
  | sub lt o i =>
    have := rootE R C o L; have := rootE R C i L
    simp only [Expr.label] at ht; simp [sitesBare, p1E, Expr.label, ht, List.count_append] at *; omega
  | _ => simp only [Expr.label] at ht; simp only [sitesBare, Expr.label, ht]; exact htS L

mutual
theorem rootD (C : List Scope) : ∀ (t : Expr) (tS : List PSite),
    (∀ L, (tS.map PSite.root).count L ≤ ((p1E R t).flatMap rt).count L) → ∀ L,
    ((sitesD R C t tS).map PSite.root).count L ≤ ((p1E R t).flatMap rt).count L
  | t, tS, htS, L => by
    cases hR : R.e t.label with
    | some t' =>
      unfold sitesD; simp only [hR]; rw [stmtSites_roots, p1E_site R hR]
      exact trD_root C t _ (labelsE_head t) L
    | none =>
      cases t with
      | name lt x => simp only [Expr.label] at hR; simp [sitesD, Expr.label, hR]
      | attr lt o a =>
        have := rootE R C o L
        simp only [Expr.label] at hR; simp [sitesD, p1E, Expr.label, hR] at this ⊢; omega
      | sub lt o i =>
        have := rootE R C o L; have := rootE R C i L
        simp only [Expr.label] at hR; simp [sitesD, p1E, Expr.label, hR, List.count_append] at *; omega
      | tuple lt ts =>
        have := rootDl C ts L
        simp only [Expr.label] at hR; simp [sitesD, p1E, Expr.label, hR] at this ⊢; omega
      | list lt ts =>
        have := rootDl C ts L
        simp only [Expr.label] at hR; simp [sitesD, p1E, Expr.label, hR] at this ⊢; omega
      | _ => simp only [Expr.label] at hR; simp only [sitesD, Expr.label, hR]; exact htS L
theorem rootDl (C : List Scope) : ∀ (ts : List Expr) (L : Label),
    ((sitesDl R C ts).map PSite.root).count L ≤ ((p1Es R ts).flatMap rt).count L
  | [], _ => by simp [sitesDl, p1Es]
  | t :: ts, L => by
    have := rootD C t _ (rootT R C deadSrc t (sitesE R C t) (rootE R C t)) L; have := rootDl C ts L
    simp [sitesDl, p1Es, List.count_append, List.map_append, List.flatMap_append]; omega
end

theorem annK_count (C : List Scope) : ∀ ps : List Param, ∀ L,
    ((sitesAnnK R C .pos ps ++ sitesAnnK R C .posonly ps ++ sitesAnnK R C .vararg ps ++
      sitesAnnK R C .kwonly ps ++ sitesAnnK R C .kwarg ps).map PSite.root).count L =
    ((sitesAn R C ps).map PSite.root).count L
  | [], _ => by simp [sitesAnnK, sitesAn]
  | .mk _ _ k _ none :: ps, L => by simpa [sitesAnnK, sitesAn, sitesO] using annK_count C ps L
  | .mk _ _ k _ (some a) :: ps, L => by
    have ih := annK_count C ps L
    simp only [List.map_append, List.count_append] at ih
    cases k <;> simp [sitesAnnK, sitesAn, sitesO, List.count_append, List.map_append] <;> omega

theorem sitesT_site {C : List Scope} {src : Label → PE} {t t' : Expr} {tS : List PSite} (h : R.e t.label = some t') :
    sitesT R C src t tS = stmtSites (trT C src t (trE C t)) (trT (editChain R C) src t' (trE (editChain R C) t')) := by
  unfold sitesT; simp [h]

theorem sitesBare_site {C : List Scope} {t t' : Expr} {tS : List PSite} (h : R.e t.label = some t') :
    sitesBare R C t tS = stmtSites (annBare C t (trT C deadSrc t (trE C t)))
      (annBare (editChain R C) t' (trT (editChain R C) deadSrc t' (trE (editChain R C) t'))) := by
  unfold sitesBare; simp [h]

theorem sitesS_stmtSite (C : List Scope) (s : Stmt) : ∃ rest, sitesS R C s = stmtSite R C s rest := by
  cases s <;> exact ⟨_, rfl⟩

theorem sitesS_site {C : List Scope} {s : Stmt} {ss : List Stmt} (h : R.s s.label = some ss) :
    sitesS R C s = [.s (sub s.label 0) (trB (editChain R C) ss)] := by
  obtain ⟨rest, hr⟩ := sitesS_stmtSite R C s
  rw [hr]; simp [stmtSite, h]

theorem p1S_site {s : Stmt} {ss : List Stmt} (h : R.s s.label = some ss) : p1S R s = labelsS s := by
  cases s <;> simp_all [p1S, p1Site, Stmt.label]

theorem qcS_site {C : List Scope} {s : Stmt} {ss : List Stmt} (h : R.s s.label = some ss) : qcS R C s = [] := by
  cases s <;> simp_all [qcS, Stmt.label]

theorem rootS_site {C : List Scope} {s : Stmt} {ss : List Stmt} (hR : R.s s.label = some ss) (L : Label) :
    ((sitesS R C s).map PSite.root).count L ≤ ((p1S R s).flatMap rt).count L + ((qcS R C s).flatMap rt).count L := by
  rw [sitesS_site R hR, p1S_site R hR, qcS_site R hR, List.flatMap_nil, List.count_nil, Nat.add_zero]
  exact one_root (labelsS_head s) (by omega) L

set_option hygiene false in
macro "siteR" : tactic => `(tactic| (refine rootS_site R (ss := ss) ?_ L; exact hR))
set_option hygiene false in
macro "rtN" : tactic => `(tactic| (simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, sitesO, p1O, qcS, hR,
  List.count_append, List.map_append, List.flatMap_append] at * <;> omega))
set_option hygiene false in
macro "regN" : tactic => `(tactic|
  simp only [regS, hR, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr)

mutual
theorem rootS (C : List Scope) : ∀ (s : Stmt), regS R C s = true → ∀ L : Label,
    ((sitesS R C s).map PSite.root).count L ≤ ((p1S R s).flatMap rt).count L + ((qcS R C s).flatMap rt).count L
  | .expr l e, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none => have := rootE R C e L; rtN
  | .assign l ts e, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      have h1 := rootE R C e L
      have h2 : ∀ ts, ((sitesTs R C (nameSrc "t" l) ts).map PSite.root).count L ≤ ((p1Es R ts).flatMap rt).count L := by
        intro ts; induction ts with
        | nil => simp [sitesTs, p1Es]
        | cons t ts ih =>
          have := rootT R C (nameSrc "t" l) t (sitesE R C t) (rootE R C t) L
          simp [sitesTs, p1Es, List.count_append, List.map_append, List.flatMap_append]; omega
      have := h2 ts; rtN
  | .augassign l t op e, hr, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      have h1 := rootE R C e L
      have haug : augOk R t = true := by simpa [regS, hR] using hr
      have hsimp : simpleT t = true := by simp only [augOk, Bool.and_eq_true] at haug; exact haug.1
      cases hT : R.e t.label with
      | some t' =>
        have h2 : ((trAug C l t (trT C deadSrc t (trE C t))).1.map PyCore.Stmt.label ++
            (trAug C l t (trT C deadSrc t (trE C t))).2.map PyCore.Stmt.label).count L ≤
            ((labelsE t).flatMap rt).count L := by
          cases t with
          | name lt x => simpa [trAug, PyCore.Stmt.label, Expr.label] using roots_of [0, 2] (by decide) (by decide) (labelsE_head (.name lt x)) L
          | attr lt o a => simpa [trAug, PyCore.Stmt.label, Expr.label] using roots_of [4, 5, 2] (by decide) (by decide) (labelsE_head (.attr lt o a)) L
          | sub lt o i => simpa [trAug, PyCore.Stmt.label, Expr.label] using roots_of [4, 5, 6, 2] (by decide) (by decide) (labelsE_head (.sub lt o i)) L
          | _ => simp [simpleT] at hsimp
        rw [← p1E_site R hT] at h2
        simp only [sitesS, stmtSite, Stmt.label, hR, sitesAug, hT, p1S, p1Site, qcS, Option.isSome_none,
          Bool.false_eq_true, ite_false, List.map_append, stmtSites_roots, List.count_append, List.flatMap_append,
          List.flatMap_nil, List.count_nil, Nat.add_zero] at h2 ⊢
        omega
      | none =>
        cases t <;> (try simp [simpleT] at hsimp)
        case name lt x =>
          simp only [Expr.label] at hT
          simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, p1E, sitesAug, Expr.label, hR, hT, qcS,
            List.count_append, List.map_append, List.flatMap_append]; omega
        case attr lt e1 a =>
          have := rootE R C e1 L
          simp only [Expr.label] at hT
          simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, p1E, sitesAug, Expr.label, hR, hT, qcS,
            List.count_append, List.map_append, List.flatMap_append]; omega
        case sub lt e1 i =>
          have := rootE R C e1 L; have := rootE R C i L
          simp only [Expr.label] at hT
          simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, p1E, sitesAug, Expr.label, hR, hT, qcS,
            List.count_append, List.map_append, List.flatMap_append]; omega
  | .annassign l t a v, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      have h1 := rootE R C a L
      cases hT : R.e t.label with
      | some t' =>
        have hp := p1E_site R hT
        cases v with
        | some v =>
          have h3 := rootE R C v L
          have h2 : ((trT C (nameSrc "t" l) t (trE C t)).map PyCore.Stmt.label ++
              (if isTop C then (annT C l t).map PyCore.Stmt.label else [])).count L ≤
              ((labelsE t).flatMap rt).count L := by
            rcases trT_labels C (nameSrc "t" l) t (trE C t) with h | h <;> rw [h] <;>
              cases isTop C <;> simp only [annT_labels, ite_true, Bool.false_eq_true, ite_false,
                List.cons_append, List.nil_append, List.append_nil]
            · exact roots_of [0] (by decide) (by decide) (labelsE_head _) L
            · exact roots_of [0, 58] (by decide) (by decide) (labelsE_head _) L
            · exact roots_of [55, 54] (by decide) (by decide) (labelsE_head _) L
            · exact roots_of [55, 54, 58] (by decide) (by decide) (labelsE_head _) L
          rw [← hp] at h2
          cases hTop : isTop C <;>
          simp only [sitesS, stmtSite, Stmt.label, hR, sitesAnn, sitesAnnA, sitesT_site R hT, hT, hTop, p1S, p1Site, qcS,
            p1O, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true, List.map_append, stmtSites_roots,
            List.count_append, List.flatMap_append, List.flatMap_nil, List.count_nil, Nat.add_zero,
            List.append_nil, List.map_nil] at h2 ⊢ <;> omega
        | none =>
          have h2 : ((annBare C t (trT C deadSrc t (trE C t))).map PyCore.Stmt.label ++
              (if isTop C then (annT C l t).map PyCore.Stmt.label else []) ++
              (annBind C t).map PyCore.Stmt.label).count L ≤ ((labelsE t).flatMap rt).count L := by
            rcases annBare_labels C t (trT C deadSrc t (trE C t)) with h | h <;> rw [h] <;>
              cases isTop C <;> simp only [annT_labels, annBind_labels, ite_true, Bool.false_eq_true, ite_false,
                List.cons_append, List.nil_append, List.append_nil]
            · exact roots_of [62, 60] (by decide) (by decide) (labelsE_head _) L
            · exact roots_of [62, 58, 60] (by decide) (by decide) (labelsE_head _) L
            · exact roots_of [55, 54, 60] (by decide) (by decide) (labelsE_head _) L
            · exact roots_of [55, 54, 58, 60] (by decide) (by decide) (labelsE_head _) L
          rw [← hp] at h2
          cases hTop : isTop C <;>
          simp only [sitesS, stmtSite, Stmt.label, hR, sitesAnn, sitesAnnA, sitesBare_site R hT, hT, hTop, p1S, p1Site,
            qcS, p1O, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true, List.map_append,
            stmtSites_roots, List.count_append, List.flatMap_append, List.flatMap_nil, List.count_nil,
            Nat.add_zero, List.append_nil, List.map_nil] at h2 ⊢ <;> omega
      | none =>
        cases v with
        | some v =>
          have h3 := rootE R C v L
          have h2 := rootT R C (nameSrc "t" l) t (sitesE R C t) (rootE R C t) L
          cases hTop : isTop C <;>
          simp only [sitesS, stmtSite, Stmt.label, hR, sitesAnn, sitesAnnA, hT, hTop, p1S, p1Site, qcS,
            p1O, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true, List.map_append,
            List.count_append, List.flatMap_append, List.flatMap_nil, List.count_nil, Nat.add_zero,
            List.append_nil, List.map_nil] at h2 ⊢ <;> omega
        | none =>
          have h2 := rootBare R C t _ hT (rootT R C deadSrc t (sitesE R C t) (rootE R C t)) L
          cases hTop : isTop C <;>
          simp only [sitesS, stmtSite, Stmt.label, hR, sitesAnn, sitesAnnA, hT, hTop, p1S, p1Site, qcS,
            p1O, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true, List.map_append,
            List.count_append, List.flatMap_append, List.flatMap_nil, List.count_nil, Nat.add_zero,
            List.append_nil, List.map_nil] at h2 ⊢ <;> omega
  | .del l ts, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none => have := rootDl R C ts L; rtN
  | .ite l c t u, hr, L | .while l c t u, hr, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      regN; have := rootE R C c L; have := rootB C t hr.1 L; have := rootB C u hr.2 L; rtN
  | .for l t it b u, hr, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      regN; have := rootE R C it L; have := rootT R C (forSrc l) t (sitesE R C t) (rootE R C t) L
      have := rootB C b hr.1 L; have := rootB C u hr.2 L; rtN
  | .brk l, _, L | .cont l, _, L | .pass l, _, L | .glob l _, _, L | .nonloc l _, _, L | .imp l _, _, L
  | .impFrom l _ _ _, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none => rtN
  | .ret l e, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none => have := rootO R C e L; rtN
  | .defn l f ps b ds r, hr, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      cases hq : qualCh R C f with
      | true =>
        have := one_root (A := l :: (p1Ps R ps ++ p1B R b ++ p1Es R ds ++ p1O R r)) (a := l) (k := 0)
          (by simp) (by omega) L
        simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, qcS, hR, hq, PSite.root, List.count_append,
          List.flatMap_append, List.count_cons] at this ⊢
        omega
      | false =>
        regN; have := rootEs R C ds L; have hp := rootPs R C ps L; have := rootO R C r L
        have := rootB (.fn l f ps b :: C) b hr L
        have hk := annK_count R C ps
        have := hk L
        simp only [List.map_append, List.count_append] at hp this
        simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, sitesO, p1O, qcS, hR, hq, List.count_append,
          List.map_append, List.flatMap_append] at *; omega
  | .cls l x bs ks b ds, hr, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      cases hq : qualCh R C x with
      | true =>
        have := one_root (A := l :: (p1Es R bs ++ p1Ks R ks ++ p1B R b ++ p1Es R ds)) (a := l) (k := 0)
          (by simp) (by omega) L
        simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, qcS, hR, hq, PSite.root, List.count_append,
          List.flatMap_append, List.count_cons] at this ⊢
        omega
      | false =>
        regN; have := rootEs R C ds L; have := rootA R C bs L; have := rootKs R C ks L
        have := rootB (.cl l x b :: C) b hr L
        simp [sitesS, stmtSite, Stmt.label, p1S, p1Site, qcS, hR, hq, List.count_append, List.map_append,
          List.flatMap_append] at *; omega
  | .tryE l b hz u, hr, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none =>
      regN; have := rootB C b hr.1.1 L; have := rootHs C hz hr.1.2 L; have := rootB C u hr.2 L; rtN
  | .raise l e c, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none => have := rootO R C e L; have := rootO R C c L; rtN
  | .assert l t m, _, L => by
    cases hR : R.s l with
    | some ss => siteR
    | none => have := rootE R C t L; have := rootO R C m L; rtN
theorem rootHs (C : List Scope) : ∀ (hz : List Handler), regHs R C hz = true → ∀ L : Label,
    ((sitesHs R C hz).map PSite.root).count L ≤ ((p1Hs R hz).flatMap rt).count L + ((qcHs R C hz).flatMap rt).count L
  | [], _, _ => by simp [sitesHs, p1Hs]
  | .mk l ty x b :: hz, hr, L => by
    simp only [regHs, Bool.and_eq_true] at hr
    have := rootHs C hz hr.2 L
    cases hR : R.h l with
    | some h' =>
      obtain ⟨lh, ty', x', b'⟩ := h'
      have h1 := one_root (A := labelsHs [.mk l ty x b]) (a := l) (k := 0) (by simp [labelsHs]) (by omega) L
      have hc : ∀ (a : Label) (xs : List Label), (a :: xs).count L = [a].count L + xs.count L := by
        intro a xs; rw [← List.singleton_append, List.count_append]
      simp only [sitesHs, p1Hs, qcHs, hR, trHs, PSite.root, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.count_append, List.flatMap_append, Option.isSome_some, ite_true] at *
      rw [hc]; omega
    | none =>
      have := rootO R C ty L; have := rootB C b (by simpa [hR] using hr.1) L
      simp [sitesHs, p1Hs, qcHs, hR, List.count_append, List.map_append, List.flatMap_append]; omega
theorem rootB (C : List Scope) : ∀ (ss : List Stmt), regB R C ss = true → ∀ L : Label,
    ((sitesB R C ss).map PSite.root).count L ≤ ((p1B R ss).flatMap rt).count L + ((qcB R C ss).flatMap rt).count L
  | [], _, _ => by simp [sitesB, p1B]
  | s :: ss, hr, L => by
    simp only [regB, Bool.and_eq_true] at hr
    have := rootS C s hr.1 L; have := rootB C ss hr.2 L
    simp [sitesB, p1B, qcB, List.count_append, List.map_append, List.flatMap_append]; omega
end

end


/-! ## The commutation -/

theorem nodup_map_sub (lt : Nat) : ∀ ks : List Nat, ks.Nodup → (ks.map (sub lt)).Nodup
  | [], _ => by simp
  | k :: ks, hn => by
    simp only [List.nodup_cons, List.map_cons, List.mem_map] at hn ⊢
    refine ⟨fun ⟨a, ha, h⟩ => hn.1 ?_, nodup_map_sub lt ks hn.2⟩
    have h' : 64 * lt + a = 64 * lt + k := h
    have : a = k := by omega
    subst this; exact ha

theorem rt_nodup (l : Label) : (rt l).Nodup := nodup_map_sub l _ List.nodup_range

theorem mem_rt_iff {l L : Label} : L ∈ rt l ↔ ∃ k, k < 64 ∧ L = sub l k := by
  simp only [rt, List.mem_map, List.mem_range]
  exact ⟨fun ⟨k, h1, h2⟩ => ⟨k, h1, h2.symm⟩, fun ⟨k, h1, h2⟩ => ⟨k, h1, h2.symm⟩⟩

theorem count_rt : ∀ P : List Label, P.Nodup → ∀ L, (P.flatMap rt).count L ≤ 1
  | [], _, _ => by simp
  | l :: P, hP, L => by
    rw [List.nodup_cons] at hP
    have ih := count_rt P hP.2 L
    have h1 : (rt l).count L ≤ 1 := List.nodup_iff_count.mp (rt_nodup l) L
    simp only [List.flatMap_cons, List.count_append]
    by_cases h : L ∈ rt l
    · have : (P.flatMap rt).count L = 0 := List.count_eq_zero.mpr fun hm => by
        obtain ⟨l', h3, h4⟩ := List.mem_flatMap.mp hm
        obtain ⟨k, hk, rfl⟩ := mem_rt_iff.mp h
        obtain ⟨k', hk', he⟩ := mem_rt_iff.mp h4
        have : l = l' := (sub_inj hk hk' he).1
        exact hP.1 (this ▸ h3)
      rw [this]; omega
    · simp [List.count_eq_zero.mpr h, ih]

theorem findSome_root {α} (sel : Label → PSite → Option α) (hsel : ∀ y L r, sel L y = some r → y.root = L) :
    ∀ G : List PSite, (G.map PSite.root).Nodup → ∀ x ∈ G, ∀ r, sel x.root x = some r →
      G.findSome? (sel x.root) = some r
  | y :: G, hn, x, hx, r, hr => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [hr]
    · have hy : sel x.root y = none := by
        cases h : sel x.root y with
        | none => rfl
        | some r' => exact absurd (hsel _ _ _ h ▸ List.mem_map_of_mem hx) hn.1
      simp [hy, findSome_root sel hsel G hn.2 x hx r hr]

/-- Each label of `p` is outside the sites, in part (1), or a node of `qcB`, once. -/
theorem cnt_le (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (x : Label) :
    (olabelsB R [] p).count x + (p1B R p).count x + (qcB R [] p).count x ≤ 1 :=
  (cntB R x [] p).symm ▸ List.nodup_iff_count.mp hp x

/-- The roots of the PyCore sites are made for nodes of part (1) or of `qcB`. -/
theorem sites_root (R : Edit) (p : List Stmt) (hr : regB R [] p = true) :
    ∀ x ∈ sitesB R [] p, ∃ l' ∈ p1B R p ++ qcB R [] p, ∃ k, k < 64 ∧ x.root = sub l' k := by
  intro x hx
  have h1 : 0 < ((sitesB R [] p).map PSite.root).count x.root :=
    List.count_pos_iff.mpr (List.mem_map_of_mem hx)
  have h2 := rootB R [] p hr x.root
  have h5 : 0 < ((p1B R p ++ qcB R [] p).flatMap rt).count x.root := by
    rw [List.flatMap_append, List.count_append]; omega
  obtain ⟨l', h3, h4⟩ := List.mem_flatMap.mp (List.count_pos_iff.mp h5)
  obtain ⟨k, hk, he⟩ := mem_rt_iff.mp h4
  exact ⟨l', h3, k, hk, he⟩

/-- `trEdit R p` is `none` wherever no site of `sitesB R [] p` is rooted. -/
theorem trEdit_none (R : Edit) (p : List Stmt) (L : Label) (hL : ∀ x ∈ sitesB R [] p, x.root ≠ L) :
    (trEdit R p).e L = none ∧ (trEdit R p).s L = none ∧ (trEdit R p).h L = none := by
  refine ⟨List.findSome?_eq_none_iff.mpr ?_, List.findSome?_eq_none_iff.mpr ?_,
    List.findSome?_eq_none_iff.mpr ?_⟩ <;> intro y hy <;> have := hL y hy <;>
    cases y <;> simp_all [PSite.selE, PSite.selS, PSite.selH, PSite.root]

/-- The hypotheses of `trB_edit` for `trEdit R p`: it replaces every site of `sitesB R [] p`,
and is `none` at every node made for a label outside the sites, and (with no node labelled 0)
at the nodes below 64, which the module's setup uses. -/
theorem trEdit_ok (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p)
    (hr : regB R [] p = true) :
    (∀ x ∈ sitesB R [] p, x.Agrees (trEdit R p)) ∧ (∀ l ∈ olabelsB R [] p, NB (trEdit R p) l) ∧
      NB (trEdit R p) 0 := by
  have hc := cnt_le R p hp
  have hp1 : (p1B R p ++ qcB R [] p).Nodup := List.nodup_iff_count.mpr fun x => by
    have := hc x; rw [List.count_append]; omega
  have hroot : ∀ L, ((sitesB R [] p).map PSite.root).count L ≤ 1 := fun L => by
    have := rootB R [] p hr L; have := count_rt _ hp1 L
    rw [List.flatMap_append, List.count_append] at this; omega
  have hnd := List.nodup_iff_count.mpr hroot
  have hmem := sites_root R p hr
  have hlab : ∀ l ∈ p1B R p ++ qcB R [] p, l ∈ labelsB p := fun l hl => by
    have := cntB R l [] p
    rcases List.mem_append.mp hl with h | h <;> have := List.count_pos_iff.mpr h <;>
      exact List.count_pos_iff.mp (by omega)
  have hag : ∀ x ∈ sitesB R [] p, x.Agrees (trEdit R p) := by
    intro x hx
    cases x with
    | e l r => exact findSome_root PSite.selE (fun y L r h => by
        cases y <;> simp_all [PSite.selE, PSite.root]) _ hnd _ hx r (by simp [PSite.selE, PSite.root])
    | s l r => exact findSome_root PSite.selS (fun y L r h => by
        cases y <;> simp_all [PSite.selS, PSite.root]) _ hnd _ hx r (by simp [PSite.selS, PSite.root])
    | h l r => exact findSome_root PSite.selH (fun y L r h => by
        cases y <;> simp_all [PSite.selH, PSite.root]) _ hnd _ hx r (by simp [PSite.selH, PSite.root])
  have nbOf : ∀ l, (∀ k, k < 64 → ∀ x ∈ sitesB R [] p, x.root ≠ sub l k) → NB (trEdit R p) l :=
    fun l h => ⟨fun k hk => (trEdit_none R p _ (h k hk)).1, fun k hk => (trEdit_none R p _ (h k hk)).2.1,
      fun k hk => (trEdit_none R p _ (h k hk)).2.2⟩
  have hn2 : ∀ l ∈ olabelsB R [] p, NB (trEdit R p) l := by
    intro l hl
    refine nbOf l fun k hk x hx he => ?_
    obtain ⟨l', h3, k', hk', h⟩ := hmem x hx
    have : l = l' := by rw [h] at he; exact (sub_inj hk' hk he).1.symm
    subst this
    have := hc l
    have := List.count_pos_iff.mpr hl
    rcases List.mem_append.mp h3 with h3 | h3 <;> have := List.count_pos_iff.mpr h3 <;> omega
  have hn0 : NB (trEdit R p) 0 := by
    refine nbOf 0 fun k hk x hx he => ?_
    obtain ⟨l', h3, k', hk', h⟩ := hmem x hx
    rw [h] at he
    have : l' = 0 := (sub_inj hk' hk he).1
    subst this; exact h0 (hlab _ h3)
  exact ⟨hag, hn2, hn0⟩

/-- `⌊editB R p⌋ = editB (trEdit R p) ⌊p⌋`: the translation commutes with an edit whose
replacements keep their sites' labels and that assigns augmentedly only to names, attributes,
and subscripts, when the labels of `p` are distinct and none is 0 (the exporter labels from 1). -/
theorem tr_edit (R : Edit) (p : List Stmt) (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p) (hk : KeepsLabels R)
    (hr : regB R [] p = true) : tr (editB R p) = PyCore.editB (trEdit R p) (tr p) := by
  obtain ⟨hag, hn2, hn0⟩ := trEdit_ok R p hp h0 hr
  have := trB_edit hk [] p hr hag hn2
  simp only [editChain_nil] at this
  simp (disch := omega) [tr, PyCore.editB, setupS, PyCore.editS, PyCore.editE, hn0.1, hn0.2.1, gad, cc,
    peditE_ccR (hn0.1 5 (by omega)), peditE_ccR (hn0.1 6 (by omega)), this]

/-- Theorem 5 for the translation of an edit: `trEdit R p` is a PyCore edit like any
other, so `footprint_theorem` applies to it, and by `tr_edit` its result is `⌊q⌋`. -/
theorem tr_footprint {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt) (σ : Name → Option PyCore.Val) (s : S)
    (hp : (labelsB p).Nodup) (h0 : 0 ∉ labelsB p) (hk : KeepsLabels R) (hr : regB R [] p = true)
    (h : PyCore.NoReach I (PyCore.inFootprint (trEdit R p) (tr p)) (PyCore.init (tr p) σ s)) :
    (∀ o, PyCore.Terminates I (PyCore.init (tr p) σ s) o ↔ PyCore.Terminates I (PyCore.init (tr (editB R p)) σ s) o) ∧
    (PyCore.Diverges I (PyCore.init (tr p) σ s) ↔ PyCore.Diverges I (PyCore.init (tr (editB R p)) σ s)) := by
  rw [tr_edit R p hp h0 hk hr]; exact PyCore.footprint_theorem I _ _ σ s h

end Surf
