/-
Lemma A.2 (Step): related configurations step to related configurations, unless
p's step evaluates a node of F; and Theorem 5 for a set F that covers the
footprint's conditions.
-/
import PyCore.Relation

namespace PyCore
open Py (Op Res Gadget)

section
variable {σ : Type} {R : Edit} {F : Label → Prop}

/-! ## Building related frames and configurations -/

theorem FrameRel.set {f g : Frame σ} (h : FrameRel R F f g) {c1 c2 : Ctrl σ} {k1 k2 : List (Kont σ)}
    (hc : c2 = editCtrl R c1) (hk : k2 = k1.map (editK R))
    (hgc : goodCtrl R F f.chain c1) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    FrameRel R F { f with ctrl := c1, kont := k1 } { g with ctrl := c2, kont := k2 } :=
  ⟨h.id, h.kind, h.chain, h.cls, h.kinds, h.ns, hc, hk, h.κ, hgc, hgk⟩

theorem FrameRel.setNs {f g : Frame σ} (h : FrameRel R F f g) (ns : List (Name × Val))
    {c1 c2 : Ctrl σ} {k1 k2 : List (Kont σ)}
    (hc : c2 = editCtrl R c1) (hk : k2 = k1.map (editK R))
    (hgc : goodCtrl R F f.chain c1) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    FrameRel R F { f with ns := ns, ctrl := c1, kont := k1 } { g with ns := ns, ctrl := c2, kont := k2 } :=
  ⟨h.id, h.kind, h.chain, h.cls, h.kinds, rfl, hc, hk, h.κ, hgc, hgk⟩

theorem FrameRel.setCtrl {f g : Frame σ} (h : FrameRel R F f g) {c1 c2 : Ctrl σ}
    (hc : c2 = editCtrl R c1) (hgc : goodCtrl R F f.chain c1) :
    FrameRel R F { f with ctrl := c1 } { g with ctrl := c2 } :=
  h.set hc h.kont hgc h.good.2

theorem FrameRel.setVal {f g : Frame σ} (h : FrameRel R F f g) (c1 : Ctrl σ)
    (hc : editCtrl R c1 = c1) (hgc : goodCtrl R F f.chain c1) :
    FrameRel R F { f with ctrl := c1 } { g with ctrl := c1 } :=
  h.setCtrl hc.symm hgc

theorem kontExc_edit : ∀ ks : List (Kont σ), kontExc (ks.map (editK R)) = kontExc ks
  | [] => rfl
  | k :: ks => by
    have ih := kontExc_edit ks
    cases k <;> simp [kontExc, editK, ih]

theorem curExc_rel : ∀ {fs gs : List (Frame σ)}, All2 (FrameRel R F) fs gs → curExc gs = curExc fs
  | [], [], _ => rfl
  | f :: fs, g :: gs, h => by
    simp only [curExc, h.1.kont, kontExc_edit, curExc_rel h.2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem FrameRel.curExc {f g : Frame σ} {fs gs : List (Frame σ)} (hfg : FrameRel R F f g)
    (hs : All2 (FrameRel R F) fs gs) : PyCore.curExc (g :: gs) = PyCore.curExc (f :: fs) :=
  curExc_rel (fs := f :: fs) ⟨hfg, hs⟩

theorem FrameRel.raiseNew {f g : Frame σ} {fs gs : List (Frame σ)}
    (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (v : Val) :
    PyCore.raiseNew (g :: gs) v = PyCore.raiseNew (f :: fs) v := by
  simp only [PyCore.raiseNew, hfg.curExc hs]

theorem FrameRel.resCtrl {f g : Frame σ} {fs gs : List (Frame σ)}
    (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (r : Except Val Val) :
    PyCore.resCtrl (g :: gs) r = PyCore.resCtrl (f :: fs) r := by
  cases r <;> simp only [PyCore.resCtrl, hfg.raiseNew hs]

theorem resCtrl_edit {st : List (Frame σ)} {r : Except Val Val} :
    editCtrl R (resCtrl st r) = resCtrl st r := by
  cases r <;> rfl

theorem resCtrl_good {st : List (Frame σ)} {r : Except Val Val} {C : List Scope} :
    goodCtrl R F C (resCtrl st r) := by
  cases r <;> trivial

theorem Rel.withStack {c d : Config σ} (h : Rel R F c d) {s1 s2 : List (Frame σ)}
    (hs : All2 (FrameRel R F) s1 s2) : Rel R F { c with stack := s1 } { d with stack := s2 } :=
  ⟨hs, h.objs, h.cells, h.glob0, h.globW, h.out, h.next, h.res, h.st⟩

theorem top_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} (h : Rel R F c d)
    (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) :
    OptRel (Rel R F) (top c fs f) (top d gs g) :=
  h.withStack ⟨hfg, hs⟩

/-- A raise in the top frame. -/
theorem raise_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} (h : Rel R F c d)
    (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (v : Val) :
    OptRel (Rel R F) (top c fs { f with ctrl := raiseNew (f :: fs) v })
      (top d gs { g with ctrl := raiseNew (g :: gs) v }) := by
  rw [hfg.raiseNew hs]; exact top_sim h (hfg.setVal _ rfl trivial) hs

theorem objs_ins {c d : Config σ} (h : Rel R F c d) (n : Nat) {a b : Obj σ}
    (hab : ObjRel R F (some a) (some b)) :
    ∀ o : Nat, ObjRel R F ((c.objs.insert n a)[o]?) ((d.objs.insert n b)[o]?) := by
  intro o; rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]; split
  · exact hab
  · exact h.objs o

theorem retTo_sim {c d : Config σ} {fs gs : List (Frame σ)} (h : Rel R F c d)
    (hs : All2 (FrameRel R F) fs gs) (ctl : Ctrl σ) (hc : editCtrl R ctl = ctl)
    (hgc : ∀ C, goodCtrl R F C ctl) :
    OptRel (Rel R F) (retTo c fs ctl) (retTo d gs ctl) := by
  cases fs <;> cases gs <;> simp [All2] at hs <;> simp [retTo, OptRel]
  exact h.withStack ⟨hs.1.setVal ctl hc (hgc _), hs.2⟩

/-- Writing one place in both runs keeps them related. -/
theorem writeAt_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} (pl : Place)
    (ov : Option Val) {c1 c2 : Ctrl σ} {k1 k2 : List (Kont σ)} (h : Rel R F c d)
    (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs)
    (hc : c2 = editCtrl R c1) (hk : k2 = k1.map (editK R))
    (hgc : goodCtrl R F f.chain c1) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    Rel R F { (writeAt c f ov pl).1 with
                stack := { (writeAt c f ov pl).2 with ctrl := c1, kont := k1 } :: fs }
            { (writeAt d g ov pl).1 with
                stack := { (writeAt d g ov pl).2 with ctrl := c2, kont := k2 } :: gs } := by
  rcases pl with ⟨y⟩ | ⟨y⟩ | ⟨a⟩
  · exact ⟨⟨hfg.set hc hk hgc hgk, hs⟩, h.objs, h.cells, h.glob0, by simp [writeAt, h.globW],
      h.out, h.next, h.res, h.st⟩
  · refine ⟨⟨?_, hs⟩, h.objs, h.cells, h.glob0, h.globW, h.out, h.next, h.res, h.st⟩
    exact ⟨hfg.id, hfg.kind, hfg.chain, hfg.cls, hfg.kinds, by simp [writeAt, hfg.ns], hc, hk,
      hfg.κ, hgc, hgk⟩
  · exact ⟨⟨hfg.set hc hk hgc hgk, hs⟩, h.objs, by simp [writeAt, h.cells], h.glob0, h.globW,
      h.out, h.next, h.res, h.st⟩

theorem store_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {x : Name} {v : Val}
    {after after' : Ctrl σ} (h : Rel R F c d) (hfg : FrameRel R F f g)
    (hs : All2 (FrameRel R F) fs gs) (hx : alike R f.chain x = true)
    (hc : after' = editCtrl R after) (hgc : goodCtrl R F f.chain after) :
    OptRel (Rel R F) (store c f fs x v after) (store d g gs x v after') := by
  unfold store
  rw [hfg.place hx, hfg.raiseNew hs]
  rcases place f x with _ | pl
  · exact top_sim h (hfg.setVal _ rfl trivial) hs
  · have hw : ∀ (c : Config σ) (f : Frame σ) ov, (writeAt c f ov pl).2.kont = f.kont := by
      intro c f ov; cases pl <;> rfl
    exact writeAt_sim pl _ h hfg hs hc (by rw [hw, hw]; exact hfg.kont) hgc
      (by rw [hw]; exact hfg.good.2)

theorem unsetThen_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {x : Name}
    {c1 c2 : Ctrl σ} {k1 k2 : List (Kont σ)} (h : Rel R F c d) (hfg : FrameRel R F f g)
    (hs : All2 (FrameRel R F) fs gs) (hx : alike R f.chain x = true)
    (hc : c2 = editCtrl R c1) (hk : k2 = k1.map (editK R))
    (hgc : goodCtrl R F f.chain c1) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    OptRel (Rel R F) (unsetThen c f fs x c1 k1) (unsetThen d g gs x c2 k2) := by
  unfold unsetThen
  rw [hfg.place hx]
  rcases place f x with _ | pl
  · exact top_sim h (hfg.set hc hk hgc hgk) hs
  · exact writeAt_sim pl _ h hfg hs hc hk hgc hgk

theorem writeAt_rel {c d : Config σ} {f g : Frame σ} (h : Rel R F c d) (hfg : FrameRel R F f g)
    (pl : Place) (ov : Option Val) :
    Rel R F (writeAt c f ov pl).1 (writeAt d g ov pl).1 ∧
    FrameRel R F (writeAt c f ov pl).2 (writeAt d g ov pl).2 := by
  rcases pl with ⟨y⟩ | ⟨y⟩ | ⟨a⟩
  · exact ⟨⟨h.stack, h.objs, h.cells, h.glob0, by simp [writeAt, h.globW], h.out, h.next, h.res,
      h.st⟩, hfg⟩
  · exact ⟨h, ⟨hfg.id, hfg.kind, hfg.chain, hfg.cls, hfg.kinds, by simp [writeAt, hfg.ns], hfg.ctrl,
      hfg.kont, hfg.κ, hfg.good⟩⟩
  · exact ⟨⟨h.stack, h.objs, by simp [writeAt, h.cells], h.glob0, h.globW, h.out, h.next, h.res,
      h.st⟩, hfg⟩

theorem writeAt_chain (c : Config σ) (f : Frame σ) (ov : Option Val) (pl : Place) :
    (writeAt c f ov pl).2.chain = f.chain := by
  cases pl <;> rfl

/-- The implicit start of a class body keeps the runs related. -/
theorem classStart_sim (I : Py.Interp σ) {c d : Config σ} {g g' : Frame σ} {fs gs : List (Frame σ)} {x : String}
    (h : Rel R F c d) (hg : FrameRel R F g g') (hs : All2 (FrameRel R F) fs gs)
    (himp : ∀ y ∈ classImplicit, alike R g.chain y = true) :
    OptRel (Rel R F) (classStart I c g fs x) (classStart I d g' gs x) := by
  have hn : alike R g.chain "__name__" = true := himp _ (by simp [classImplicit])
  have hm : alike R g.chain "__module__" = true := himp _ (by simp [classImplicit])
  have hq : alike R g.chain "__qualname__" = true := himp _ (by simp [classImplicit])
  unfold classStart
  simp only [readName_rel h hg hn, hg.raiseNew hs]
  cases readName I c g "__name__" none with
  | error e => exact top_sim h (hg.setVal _ rfl trivial) hs
  | ok m =>
    dsimp only
    rw [hg.place hm]
    rcases place g "__module__" with _ | p1
    · exact top_sim h (hg.setVal _ rfl trivial) hs
    · dsimp only
      obtain ⟨h1, hg1⟩ := writeAt_rel h hg p1 (some m)
      rw [hg1.place (by rw [writeAt_chain]; exact hq)]
      rcases place (writeAt c g (some m) p1).2 "__qualname__" with _ | p2
      · exact top_sim h1 (hg1.setVal _ rfl trivial) hs
      · obtain ⟨h2, hg2⟩ := writeAt_rel h1 hg1 p2 (some (I.const s!"'{x}'"))
        exact h2.withStack ⟨hg2, hs⟩

theorem close_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {S : Scope}
    {k1 k2 : List (Kont σ)} (h : Rel R F c d) (hfg : FrameRel R F f g)
    (hs : All2 (FrameRel R F) fs gs) (hS : sameKind R S)
    (hcode : goodScope R F (S :: f.chain) S)
    (hk : k2 = k1.map (editK R)) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    OptRel (Rel R F) (close c f fs S k1) (close d g gs (editSc R S) k2) := by
  simp only [close, OptRel]
  refine ⟨⟨?_, hs⟩, ?_, h.cells, h.glob0, h.globW, h.out, by simp [h.next], h.res, h.st⟩
  · exact hfg.set (by simp [h.next, editCtrl]) hk trivial hgk
  · rw [h.next]
    refine objs_ins h c.next ⟨rfl, hfg.chain, ?_, ?_, rfl, hS, hfg.kinds, hcode⟩
    · intro x hx; rw [Py.memo_eq, Py.memo_eq, hfg.chain]; exact alike_cls (C := S :: f.chain) hx
    · intro x hx; rw [Py.memo_eq, Py.memo_eq]; exact hfg.capture hx

/-! ## The cases of Lemma A.2 -/

theorem good_ev {f : Frame σ} {e : Expr} (hfg : FrameRel R F f g) (hfc : f.ctrl = .ev e) :
    goodE R F f.chain e := by
  have := hfg.good.1; rw [hfc] at this; exact this

theorem good_exec {f : Frame σ} {ss : List Stmt} (hfg : FrameRel R F f g) (hfc : f.ctrl = .exec ss) :
    goodB R F f.chain ss := by
  have := hfg.good.1; rw [hfc] at this; exact this

theorem good_kont {f : Frame σ} {k : Kont σ} {ks : List (Kont σ)} (hfg : FrameRel R F f g)
    (hk : f.kont = k :: ks) : goodK R F f.chain k ∧ ∀ k ∈ ks, goodK R F f.chain k := by
  have := hfg.good.2; rw [hk] at this
  exact ⟨this k (List.mem_cons_self ..), fun k' hk' => this k' (List.mem_cons_of_mem _ hk')⟩

/-- The kont of `g` after popping the counterpart of `k`. -/
theorem kont_cons {f g : Frame σ} {k : Kont σ} {ks : List (Kont σ)} (hfg : FrameRel R F f g)
    (hk : f.kont = k :: ks) : g.kont = editK R k :: ks.map (editK R) := by
  rw [hfg.kont, hk]; rfl

theorem good_cons {C : List Scope} {k : Kont σ} {ks : List (Kont σ)} (hk : goodK R F C k)
    (hks : ∀ k ∈ ks, goodK R F C k) : ∀ k' ∈ k :: ks, goodK R F C k' := by
  intro k' hk'; simp at hk'; rcases hk' with rfl | hk'
  · exact hk
  · exact hks k' hk'

/-- A constant: its value, or a handler marker's match, alike in both runs. -/
theorem constK_edit (I : Py.Interp σ) (k : String) (ks : List (Kont σ)) :
    constK I k (ks.map (editK R)) = ((constK I k ks).1, (constK I k ks).2.map (editK R)) := by
  rcases ks with _ | ⟨k0, ks⟩
  · rfl
  · cases k0 <;> simp only [constK, List.map, editK] <;>
      by_cases h1 : k = "$stop" <;> by_cases h2 : k = "$any" <;> simp [h1, h2, editK]

theorem constK_fst (I : Py.Interp σ) (k : String) (ks : List (Kont σ)) :
    ∃ v, (constK I k ks).1 = Ctrl.val v := by
  rcases ks with _ | ⟨k0, ks⟩
  · exact ⟨_, rfl⟩
  · cases k0 <;> simp only [constK] <;>
      by_cases h1 : k = "$stop" <;> by_cases h2 : k = "$any" <;> simp [h1, h2]

theorem constK_good (I : Py.Interp σ) (k : String) {C : List Scope} (ks : List (Kont σ))
    (hks : ∀ k ∈ ks, goodK R F C k) : ∀ k' ∈ (constK I k ks).2, goodK R F C k' := by
  rcases ks with _ | ⟨k0, ks⟩
  · exact hks
  · have hh := hks _ (List.mem_cons_self ..)
    have ht : ∀ k ∈ ks, goodK R F C k := fun k hk => hks k (List.mem_cons_of_mem _ hk)
    cases k0 <;> simp only [constK] <;> try exact hks
    by_cases h1 : k = "$stop" <;> by_cases h2 : k = "$any" <;> simp only [h1, h2, ↓reduceIte] <;>
      first | exact hks | exact good_cons hh ht

theorem evalStep_sim (I : Py.Interp σ) {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {e : Expr}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs)
    (hfc : f.ctrl = .ev e) (hl : ¬ F e.label) :
    OptRel (Rel R F) (evalStep I c f fs e) (evalStep I d g gs (editE R e)) := by
  have hge := good_ev hfg hfc
  cases e with
  | const l k =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge, Option.getD, evalStep]
    rw [hfg.kont, constK_edit]
    obtain ⟨v, hv⟩ := constK_fst I k f.kont
    rw [hv]
    exact top_sim h (hfg.set rfl rfl trivial (constK_good I k f.kont hfg.good.2)) hs
  | name l x k =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep, readName_rel h hfg hge.2, hfg.resCtrl hs]
    exact top_sim h (hfg.setVal _ resCtrl_edit resCtrl_good) hs
  | bin l op a b =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    refine top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) hge.2.1 ?_) hs
    intro k hk; simp at hk; rcases hk with rfl | hk
    · exact hge.2.2
    · exact hfg.good.2 k hk
  | call l a b =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    refine top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) hge.2.1 ?_) hs
    intro k hk; simp at hk; rcases hk with rfl | hk
    · exact hge.2.2
    · exact hfg.good.2 k hk
  | lam l k x b =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    exact close_sim (S := .fn l k x b) h hfg hs hge.2.1 hge.2.2 hfg.kont hfg.good.2
  | walrus l x e =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    refine top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) hge.2.2 ?_) hs
    intro k hk; simp at hk; rcases hk with rfl | hk
    · exact hge.2.1
    · exact hfg.good.2 k hk
  | yield l e =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) hge.2 (good_cons trivial hfg.good.2)) hs
  | yieldFrom l e =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) hge.2 (good_cons trivial hfg.good.2)) hs
  | cond l e a b =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) hge.2.1
      (good_cons (k := .condK a b) hge.2.2 hfg.good.2)) hs
  | bool l o a b =>
    simp only [goodE, Expr.label] at hge hl; simp only [hl, false_or] at hge
    simp only [editE, hge.1, Option.getD, evalStep]
    exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) hge.2.1
      (good_cons (k := .boolK o b) hge.2.2 hfg.good.2)) hs

/-! ### Calls -/

/-- Entering a closure of related objects. -/
theorem enter_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {S : Scope}
    {C : List Scope} {cl cl' : Name → Cls} {κ κ' : Name → Option Addr}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs)
    (hS : sameKind R S) (hC : ChainKinds R C) (hgood : goodScope R F (S :: C) S)
    (hcl : ∀ x, alike R (S :: C) x = true → cl' x = cl x)
    (hκ : ∀ x, alike R (S :: C) x = true → κ' x = κ x) (bound : List (Name × Val)) :
    OptRel (Rel R F) (enter c f fs S C cl κ bound)
      (enter d g gs (editSc R S) (C.map (editSc R)) cl' κ' bound) := by
  have hks : ChainKinds R (S :: C) := by
    intro S' hS'; simp at hS'; rcases hS' with rfl | hS'
    · exact hS
    · exact hC S' hS'
  cases S with
  | cl l b => simp only [editSc, enter]; exact raise_sim h hfg hs _
  | fn l k x b =>
    have hk : (Scope.fn l k x (editB R b)).kind = (Scope.fn l k x b).kind := hS
    simp only [editSc, enter]
    rw [hk]
    have hfr : FrameRel R F
        ({ id := c.next, chain := Scope.fn l k x b :: C, kind := .fn, cls := cl, κ := κ, ns := [],
           ctrl := .exec b, kont := [] } : Frame σ)
        ({ id := d.next, chain := Scope.fn l k x (editB R b) :: C.map (editSc R), kind := .fn,
           cls := cl', κ := κ', ns := [], ctrl := .exec (editB R b), kont := [] } : Frame σ) :=
      ⟨by simp [h.next], rfl, rfl, hcl, hks, rfl, rfl, rfl, hκ, hgood, by simp⟩
    cases (Scope.fn l k x b).kind with
    | plain =>
      simp only [OptRel]
      exact ⟨⟨hfr, hfg.setVal _ rfl trivial, hs⟩, h.objs, by rw [h.cells, h.next], h.glob0, h.globW,
        h.out, by simp [h.next], h.res, h.st⟩
    | gen =>
      simp only [OptRel]
      refine ⟨⟨by rw [h.next]; exact hfg.setVal _ rfl trivial, hs⟩, ?_, by rw [h.cells, h.next],
        h.glob0, h.globW, h.out, by simp [h.next], h.res, h.st⟩
      rw [h.next]
      exact objs_ins h c.next ⟨by simp, rfl, rfl, hcl, hks, rfl, rfl, rfl, hκ, hgood, by simp⟩

theorem callFn_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (o : Nat)
    (args : List Val) (kws : List (Name × Val)) :
    OptRel (Rel R F) (callFn c f fs o args kws) (callFn d g gs o args kws) := by
  have ho := h.objs o
  unfold callFn
  rcases hc : c.objs[o]? with _ | ⟨⟨S, C, cl, κ, sg⟩ | st⟩ <;>
    rcases hd : d.objs[o]? with _ | ⟨⟨S', C', cl', κ', sg'⟩ | st'⟩ <;>
    rw [hc, hd] at ho <;> simp only [ObjRel] at ho <;> (try dsimp only) <;>
    try exact raise_sim h hfg hs _
  obtain ⟨rfl, rfl, hcl, hκ, rfl, hS, hC, hgood⟩ := ho
  cases S with
  | cl l b => exact raise_sim h hfg hs _
  | fn l k x b =>
    simp only [editSc]
    cases sg' with
    | none =>
      dsimp only
      cases args with
      | nil => exact raise_sim h hfg hs _
      | cons va rest =>
        cases rest with
        | nil => exact enter_sim (S := .fn l k x b) h hfg hs hS hC hgood hcl hκ _
        | cons _ _ => exact raise_sim h hfg hs _
    | some sd =>
      obtain ⟨sig, dflt⟩ := sd
      dsimp only
      cases Py.bindArgs sig dflt args kws with
      | error e => exact raise_sim h hfg hs _
      | ok r =>
        obtain ⟨bound, kx⟩ := r
        cases kx with
        | none => exact enter_sim (S := .fn l k x b) h hfg hs hS hC hgood hcl hκ _
        | some p =>
          exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) trivial
            (good_cons trivial hfg.good.2)) hs

theorem finishArgs_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (t : ArgsT)
    (args : List Val) (kvs : List (Name × Val)) {k1 k2 : List (Kont σ)} (hk : k2 = k1.map (editK R))
    (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    OptRel (Rel R F) (finishArgs c f fs t args kvs k1) (finishArgs d g gs t args kvs k2) := by
  cases t with
  | call fv => exact top_sim h (hfg.set rfl hk trivial hgk) hs
  | cls ds => simp only [finishArgs]; rw [hfg.ns]; exact top_sim h (hfg.setNs _ rfl hk trivial hgk) hs

theorem kwPhase_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (t : ArgsT)
    (args : List Val) (kws : List (Option Name)) (kwvals : List Val) {k1 k2 : List (Kont σ)}
    (hk : k2 = k1.map (editK R)) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    OptRel (Rel R F) (kwPhase c f fs t args kws kwvals k1) (kwPhase d g gs t args kws kwvals k2) := by
  unfold kwPhase; split
  · exact top_sim h (hfg.set rfl (by simp [hk, editK]) trivial (good_cons trivial hgk)) hs
  · exact finishArgs_sim h hfg hs t args _ hk hgk

theorem argPhase_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (t : ArgsT)
    (args : List Val) (stars : List Bool) (kws : List (Option Name)) (kwvals : List Val)
    {k1 k2 : List (Kont σ)} (hk : k2 = k1.map (editK R)) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    OptRel (Rel R F) (argPhase c f fs t args stars kws kwvals k1)
      (argPhase d g gs t args stars kws kwvals k2) := by
  unfold argPhase; split
  · exact top_sim h (hfg.set rfl (by simp [hk, editK]) trivial (good_cons trivial hgk)) hs
  · exact kwPhase_sim h hfg hs t args kws kwvals hk hgk

theorem gadgetStep_sim (I : Py.Interp σ) {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (gd : Gadget)
    (vs : List Val) :
    OptRel (Rel R F) (gadgetStep I c f fs gd vs) (gadgetStep I d g gs gd vs) := by
  have hV : ∀ v, OptRel (Rel R F) (top c fs { f with ctrl := .val v }) (top d gs { g with ctrl := .val v }) :=
    fun v => top_sim h (hfg.setVal _ rfl trivial) hs
  cases gd with
  | call =>
    simp only [gadgetStep]
    cases vs with
    | nil => trivial
    | cons fv rest =>
      dsimp only
      cases (Py.pairs rest).bind Py.splitArgs with
      | none => trivial
      | some r =>
        obtain ⟨st, args, kws, kwvals⟩ := r
        exact argPhase_sim h hfg hs _ _ _ _ _ hfg.kont hfg.good.2
  | defn nd np =>
    simp only [gadgetStep]
    cases vs.getLast? with
    | none => trivial
    | some lv =>
      cases ((vs.dropLast).drop (vs.length - 1 - np)).mapM Py.markParam with
      | none => cases lv <;> trivial
      | some sig =>
        cases lv with
        | fn o =>
          dsimp only
          have ho := h.objs o
          rcases hc : c.objs[o]? with _ | ⟨⟨S, C, cl, κ, sg⟩ | st⟩ <;>
            rcases hd : d.objs[o]? with _ | ⟨⟨S', C', cl', κ', sg'⟩ | st'⟩ <;>
            rw [hc, hd] at ho <;> simp only [ObjRel] at ho <;> (try dsimp only) <;> try trivial
          obtain ⟨rfl, rfl, hcl, hκ, rfl, hS, hC, hgood⟩ := ho
          exact ⟨⟨hfg.set rfl (by simp [hfg.kont, editK]) trivial (good_cons trivial hfg.good.2), hs⟩,
            objs_ins h o ⟨rfl, rfl, hcl, hκ, rfl, hS, hC, hgood⟩, h.cells, h.glob0, h.globW, h.out,
            h.next, h.res, h.st⟩
        | _ => trivial
  | cls nd =>
    simp only [gadgetStep]
    cases (Py.pairs (vs.drop nd)).bind Py.splitArgs with
    | none => trivial
    | some r =>
      obtain ⟨st, args, kws, kwvals⟩ := r
      exact argPhase_sim h hfg hs _ _ _ _ _ hfg.kont hfg.good.2
  | unpack =>
    simp only [gadgetStep]
    cases vs with
    | nil => trivial
    | cons v ms =>
      dsimp only
      cases ms.mapM Py.markStar with
      | none => trivial
      | some st =>
        dsimp only; split
        · trivial
        · exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) trivial (good_cons trivial hfg.good.2)) hs
  | display k =>
    simp only [gadgetStep]
    cases Py.pairs vs with
    | none => trivial
    | some ps =>
      dsimp only
      cases ps.mapM (Py.markStar ·.1) with
      | none => trivial
      | some st => exact top_sim h (hfg.setVal _ rfl trivial) hs
  | cunary op =>
    simp only [gadgetStep]
    rcases vs with _ | ⟨m, _ | ⟨_, _⟩⟩ <;> try trivial
    exact hV _
  | ctuple => exact hV _
  | setup =>
    simp only [gadgetStep]
    cases vs with
    | nil => trivial
    | cons dv rest =>
      cases rest with
      | cons _ _ => trivial
      | nil =>
        dsimp only
        rw [hfg.kind]
        cases f.kind with
        | cls =>
          dsimp only; unfold setupNs
          have e : (g.ns.lookup "__annotations__").isSome = (f.ns.lookup "__annotations__").isSome := by
            rw [hfg.ns]
          rw [e]; split
          · exact hV _
          · rw [hfg.ns]; exact top_sim h (hfg.setNs _ rfl hfg.kont trivial hfg.good.2) hs
        | _ =>
          dsimp only; unfold setupGlob; rw [h.glob]; split
          · exact hV _
          · exact ⟨⟨hfg.setVal _ rfl trivial, hs⟩, h.objs, h.cells, h.glob0, by rw [h.globW],
              h.out, h.next, h.res, h.st⟩
  | annot x =>
    simp only [gadgetStep]
    cases vs with
    | nil => trivial
    | cons a rest =>
      cases rest with
      | cons _ _ => trivial
      | nil =>
        rw [annRead_rel h hfg]
        cases annRead I c f with
        | ok dv => exact top_sim h (hfg.setVal _ rfl trivial) hs
        | error e => exact raise_sim h hfg hs _
  | starstore =>
    simp only [gadgetStep]
    cases vs with
    | nil => trivial
    | cons pv rest =>
      cases rest with
      | cons _ _ => trivial
      | nil =>
        cases pv <;> try trivial
        rename_i ps
        dsimp only
        rw [hfg.kind]
        cases Py.kwPairs ps with
        | none => trivial
        | some kvs =>
          cases f.kind with
          | mod => exact ⟨⟨hfg.setVal _ rfl trivial, hs⟩, h.objs, h.cells, h.glob0, by rw [h.globW],
              h.out, h.next, h.res, h.st⟩
          | cls => unfold starNs; rw [hfg.ns]; exact top_sim h (hfg.setNs _ rfl hfg.kont trivial hfg.good.2) hs
          | _ => trivial
  | reraise =>
    simp only [gadgetStep]
    rw [hfg.curExc hs]
    cases PyCore.curExc (f :: fs) with
    | some hv => exact top_sim h (hfg.setVal _ rfl trivial) hs
    | none => exact raise_sim h hfg hs _
  | raiseK k => exact raise_sim h hfg hs _
  | raiseFrom =>
    simp only [gadgetStep]
    rcases vs with _ | ⟨e, _ | ⟨cv, _ | ⟨_, _⟩⟩⟩ <;> try trivial
    exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) trivial (good_cons trivial hfg.good.2)) hs
  | item i =>
    simp only [gadgetStep]
    rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> try trivial
    cases v <;> try trivial
    rename_i ws
    dsimp only
    cases ws[i]? with
    | none => trivial
    | some w => exact hV _
  | set x =>
    simp only [gadgetStep]
    rcases vs with _ | ⟨v, _ | ⟨_, _⟩⟩ <;> try trivial
    exact ⟨⟨hfg.setVal _ rfl trivial, hs⟩, h.objs, by rw [h.cells, hfg.id], h.glob0,
      h.globW, h.out, h.next, h.res, h.st⟩
  | get x =>
    simp only [gadgetStep]
    rcases vs with _ | ⟨_, _⟩ <;> try trivial
    have e : d.cells[(g.id, x)]? = c.cells[(f.id, x)]? := by rw [h.cells, hfg.id]
    dsimp only
    rw [e]
    cases c.cells[(f.id, x)]? with
    | none => trivial
    | some v => exact hV _
  | stuck => trivial

theorem execStep_sim (I : Py.Interp σ) {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {s : Stmt}
    {ss : List Stmt} (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs)
    (hfc : f.ctrl = .exec (s :: ss)) (hl : ¬ F s.label) :
    ∃ s', editS R s = [s'] ∧
      OptRel (Rel R F) (execStep I c f fs s ss) (execStep I d g gs s' (editB R ss)) := by
  have hgb := good_exec hfg hfc
  simp only [goodB] at hgb
  obtain ⟨hgs, hgss⟩ := hgb
  have hk : ∀ k ∈ Kont.seq ss :: f.kont, goodK R F f.chain k :=
    good_cons (k := .seq ss) hgss hfg.good.2
  have hk' : Kont.seq (editB R ss) :: g.kont = (Kont.seq ss :: f.kont).map (editK R) := by
    simp [hfg.kont, editK]
  cases s with
  | assign l x e =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgs.2.2 (good_cons hgs.2.1 hk)) hs
  | del l x =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    rw [hfg.place hgs.2]
    rcases hp : place f x with _ | pl
    · dsimp only; rw [hfg.raiseNew hs]; exact top_sim h (hfg.set rfl hk' trivial hk) hs
    · dsimp only
      rw [isSet_rel h hfg]
      split
      · exact writeAt_sim pl none h hfg hs rfl hk' trivial hk
      · have he : delErr g x pl = delErr f x pl := by
          cases pl <;> simp only [delErr, hfg.unboundErr hgs.2]
        rw [hfg.raiseNew hs, he]
        exact top_sim h (hfg.set rfl hk' trivial hk) hs
  | expr l e =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgs.2 (good_cons trivial hk)) hs
  | ite l e t u =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgs.2.1
      (good_cons ⟨hgs.2.2.1, hgs.2.2.2⟩ hk)) hs
  | «while» l e b u =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgs.2.1
      (good_cons ⟨hgs.2.1, hgs.2.2⟩ hk)) hs
  | ret l e =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgs.2 (good_cons trivial hk)) hs
  | defn l fn x b =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact close_sim (S := .fn l false x b) h hfg hs hgs.2.2.1 hgs.2.2.2
      (by simp [hk', editK]) (good_cons hgs.2.1 hk)
  | cls l x q b =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    obtain ⟨_, hx, himp, hgb⟩ := hgs
    rw [hfg.ns]
    refine classStart_sim I ⟨h.stack, h.objs, h.cells, h.glob0, h.globW, h.out, by simp [h.next], h.res, h.st⟩
      ?_ ⟨hfg.setNs _ rfl (by simp [hk', editK]) trivial
        (good_cons trivial (good_cons hx hk)), hs⟩ himp
    refine ⟨by simp [h.next], rfl, by simp [hfg.chain, editSc], ?_, ?_, rfl, rfl, rfl,
      fun y hy => hfg.cellOf (alike_tail hy), hgb, by simp⟩
    · intro y hy; rw [Py.memo_eq, Py.memo_eq, hfg.chain]; exact alike_cls (C := .cl l b :: f.chain) hy
    · intro S hS; simp at hS; rcases hS with rfl | hS
      · rfl
      · exact hfg.kinds S hS
  | glob l x =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl hk' trivial hk) hs
  | nonloc l x =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl hk' trivial hk) hs
  | tryE l b hs' u =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    obtain ⟨hr, hgb, hgh, hgu⟩ := hgs
    refine ⟨_, by simp only [editS, hr, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgb (good_cons (k := .tryE hs' u) ⟨hgh, hgu⟩ hk)) hs
  | brk l =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl hk' trivial hk) hs
  | cont l =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl hk' trivial hk) hs
  | raise l e =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgs.2 (good_cons trivial hk)) hs
  | print l e =>
    simp only [goodS, Stmt.label] at hgs hl; simp only [hl, false_or] at hgs
    refine ⟨_, by simp only [editS, hgs.1, Option.getD]; rfl, ?_⟩
    simp only [execStep]
    exact top_sim h (hfg.set rfl (by simp [hk', editK]) hgs.2 (good_cons trivial hk)) hs



theorem callStep_sim (I : Py.Interp σ) {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (vf va : Val) :
    OptRel (Rel R F) (callStep I c f fs vf va) (callStep I d g gs vf va) := by
  cases vf with
  | fn o => exact callFn_sim h hfg hs o [va] []
  | next =>
    simp only [callStep]
    cases va with
    | gen o =>
      have ho := h.objs o
      dsimp only
      rcases hc : c.objs[o]? with _ | ⟨⟨S, C, cl, κ, sg⟩ | st⟩ <;>
        rcases hd : d.objs[o]? with _ | ⟨⟨S', C', cl', κ', sg'⟩ | st'⟩ <;>
        rw [hc, hd] at ho <;> simp only [ObjRel] at ho <;> (try dsimp only) <;>
        try exact raise_sim h hfg hs _
      rcases st with gf | _ | _ <;> rcases st' with gf' | _ | _ <;> simp only [GRel] at ho <;>
        (try dsimp only) <;> try exact raise_sim h hfg hs _
      exact ⟨⟨ho, hfg.setVal _ rfl trivial, hs⟩, objs_ins h o trivial, h.cells, h.glob0, h.globW,
        h.out, h.next, h.res, h.st⟩
    | _ => exact top_sim h (hfg.setVal _ rfl trivial) hs
  | op o => exact top_sim h (hfg.setVal _ rfl trivial) hs
  | prim k =>
    simp only [callStep]
    cases Gadget.ofName k with
    | some gd => exact gadgetStep_sim I h hfg hs gd _
    | none => exact top_sim h (hfg.setVal _ rfl trivial) hs
  | _ => exact top_sim h (hfg.setVal _ rfl trivial) hs

/-- A call with positional and keyword arguments. -/
theorem callArgs_sim (I : Py.Interp σ) {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (vf : Val)
    (args : List Val) (kws : List (Name × Val)) :
    OptRel (Rel R F) (callArgs I c f fs vf args kws) (callArgs I d g gs vf args kws) := by
  cases vf with
  | fn o => exact callFn_sim h hfg hs o args kws
  | next =>
    simp only [callArgs]
    rcases args with _ | ⟨va, _ | ⟨_, _⟩⟩ <;> rcases kws with _ | ⟨_, _⟩ <;>
      first | exact callStep_sim I h hfg hs _ _ | exact raise_sim h hfg hs _
  | op o =>
    simp only [callArgs]; split
    · exact top_sim h (hfg.setVal _ rfl trivial) hs
    · exact raise_sim h hfg hs _
  | _ => exact top_sim h (hfg.setVal _ rfl trivial) hs

/-- A truth test. -/
theorem tst_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {k1 k2 : List (Kont σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (v : Val)
    (hk : k2 = k1.map (editK R)) (hgk : ∀ k ∈ k1, goodK R F f.chain k) :
    OptRel (Rel R F) (tst c f fs v k1) (tst d g gs v k2) := by
  unfold tst
  cases v <;> exact top_sim h (hfg.set rfl hk trivial hgk) hs

/-- An interpretation's result, the same in both runs. -/
theorem handle_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) (r : Res σ) :
    OptRel (Rel R F) (some (handle c.objs c.cells c.glob0 c.globW c.out c.next c.res f fs r))
      (some (handle d.objs d.cells d.glob0 d.globW d.out d.next d.res g gs r)) := by
  cases r with
  | ok s v => exact ⟨⟨hfg.setVal _ rfl trivial, hs⟩, h.objs, h.cells, h.glob0, h.globW, h.out, h.next,
      h.res, rfl⟩
  | raise s e =>
    simp only [handle, OptRel, hfg.raiseNew hs]
    exact ⟨⟨hfg.setVal _ rfl trivial, hs⟩, h.objs, h.cells, h.glob0, h.globW, h.out, h.next, h.res, rfl⟩
  | reraise s e => exact ⟨⟨hfg.setVal _ rfl trivial, hs⟩, h.objs, h.cells, h.glob0, h.globW, h.out,
      h.next, h.res, rfl⟩
  | call s g' args kws k =>
    exact ⟨⟨hfg.set rfl (by simp [hfg.kont, editK]) trivial (good_cons trivial hfg.good.2), hs⟩,
      h.objs, h.cells, h.glob0, h.globW, h.out, h.next, h.res, rfl⟩

theorem nsStep_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs)
    (ns : List (Name × Val)) : OptRel (Rel R F) (nsStep c f fs ns) (nsStep d g gs ns) := by
  unfold nsStep
  rcases hk : f.kont with _ | ⟨k, ks⟩
  · rw [show g.kont = [] by rw [hfg.kont, hk]; rfl]; trivial
  rw [kont_cons hfg hk]
  obtain ⟨_, hgks⟩ := good_kont hfg hk
  cases k with
  | clsEnd x q bases kws ds =>
    exact top_sim h (hfg.set rfl (by simp [editK]) trivial (good_cons trivial hgks)) hs
  | _ => trivial

theorem valStep_sim (I : Py.Interp σ) {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {v : Val}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) :
    OptRel (Rel R F) (valStep I c f fs v) (valStep I d g gs v) := by
  unfold valStep
  rcases hk : f.kont with _ | ⟨k, ks⟩
  · rw [show g.kont = [] by rw [hfg.kont, hk]; rfl]; trivial
  rw [kont_cons hfg hk]
  obtain ⟨hgk, hgks⟩ := good_kont hfg hk
  have hpop : FrameRel R F { f with kont := ks } { g with kont := ks.map (editK R) } :=
    hfg.set (c1 := f.ctrl) hfg.ctrl rfl hfg.good.1 hgks
  cases k with
  | binL op b =>
    exact top_sim h (hfg.set rfl rfl hgk (good_cons trivial hgks)) hs
  | binR op v1 =>
    simp only [editK]; split <;> exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | callF b =>
    exact top_sim h (hfg.set rfl rfl hgk (good_cons trivial hgks)) hs
  | callA vf => exact callStep_sim I h hpop hs vf v
  | walrus x => exact store_sim h hpop hs hgk rfl trivial
  | assign x => exact store_sim h hpop hs hgk rfl trivial
  | exprS => exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | printS =>
    exact ⟨⟨hfg.set rfl rfl trivial hgks, hs⟩, h.objs, h.cells, h.glob0, h.globW, by simp [h.out], h.next,
      h.res, h.st⟩
  | ifS t u =>
    exact tst_sim h hfg hs v (k1 := .ifT t u :: ks) (by simp [editK]) (good_cons hgk hgks)
  | ifT t u =>
    simp only [editK]
    cases v with
    | bool b =>
      cases b
      · exact top_sim h (hfg.set rfl rfl hgk.2 hgks) hs
      · exact top_sim h (hfg.set rfl rfl hgk.1 hgks) hs
    | _ => trivial
  | whileS e b u =>
    exact tst_sim h hfg hs v (k1 := .whileT e b u :: ks) (by simp [editK]) (good_cons hgk hgks)
  | whileT e b u =>
    simp only [editK]
    cases v with
    | bool t =>
      cases t
      · exact top_sim h (hfg.set rfl rfl hgk.2.2 hgks) hs
      · exact top_sim h (hfg.set rfl rfl hgk.2.1 (good_cons (k := .loop e b u) hgk hgks)) hs
    | _ => trivial
  | retS => exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | raiseS => exact top_sim h (hfg.set rfl rfl trivial (good_cons trivial hgks)) hs
  | raiseE => simp only [editK]; rw [hfg.raiseNew hs]; exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | catchS ex x hb hs' u =>
    exact top_sim h (hfg.set rfl (by simp [editK]) trivial (good_cons (k := .catchT ex x hb hs' u) hgk hgks)) hs
  | catchT ex x hb hs' u =>
    simp only [editK]
    cases v with
    | bool t =>
      cases t
      · exact top_sim h (hfg.set rfl rfl trivial (good_cons (k := .tryE hs' u) hgk.2.2 hgks)) hs
      · exact store_sim h (hfg.set (c1 := f.ctrl) hfg.ctrl (by simp [editK]) hfg.good.1
          (good_cons (k := .handler x ex) hgk.1 hgks)) hs hgk.1 rfl hgk.2.1
    | _ => trivial
  | condK a b =>
    exact tst_sim h hfg hs v (k1 := .condT a b :: ks) (by simp [editK]) (good_cons hgk hgks)
  | condT a b =>
    simp only [editK]
    cases v with
    | bool t =>
      cases t
      · exact top_sim h (hfg.set rfl rfl hgk.2 hgks) hs
      · exact top_sim h (hfg.set rfl rfl hgk.1 hgks) hs
    | _ => trivial
  | boolK o b =>
    exact tst_sim h hfg hs v (k1 := .boolT o v b :: ks) (by simp [editK]) (good_cons hgk hgks)
  | boolT o a b =>
    simp only [editK]
    cases v with
    | bool t =>
      dsimp only
      split
      · exact top_sim h (hfg.set rfl rfl hgk hgks) hs
      · exact top_sim h (hfg.set rfl rfl trivial hgks) hs
    | _ => trivial
  | loop => trivial
  | seq => trivial
  | tryE => trivial
  | handler => trivial
  | clsEnd => trivial
  | native k => exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | yfStart =>
    simp only [editK]
    cases v <;> first
      | exact top_sim h (hfg.set rfl rfl trivial hgks) hs
      | exact top_sim h (hfg.set rfl rfl trivial (good_cons trivial hgks)) hs
  | yfIt =>
    simp only [editK]
    cases v <;> exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | yfGot dl =>
    simp only [hfg.kind]
    rcases f.kind with _ | _ | o | _ <;>
      rcases fs with _ | ⟨f0, fs0⟩ <;> rcases gs with _ | ⟨g0, gs0⟩ <;> simp only [All2] at hs <;>
      try trivial
    exact ⟨⟨hs.1.setVal _ rfl trivial, hs.2⟩,
      objs_ins h o ⟨hfg.id, rfl, hfg.chain, hfg.cls, hfg.kinds, hfg.ns, rfl, rfl, hfg.κ, trivial, hgks⟩, h.cells, h.glob0, h.globW, h.out,
      h.next, h.res, h.st⟩
  | yieldS =>
    simp only [hfg.kind]
    rcases f.kind with _ | _ | o | _ <;>
      rcases fs with _ | ⟨f0, fs0⟩ <;> rcases gs with _ | ⟨g0, gs0⟩ <;> simp only [All2] at hs <;>
      try trivial
    exact ⟨⟨hs.1.setVal _ rfl trivial, hs.2⟩,
      objs_ins h o ⟨hfg.id, rfl, hfg.chain, hfg.cls, hfg.kinds, hfg.ns, rfl, rfl, hfg.κ, trivial, hgks⟩, h.cells, h.glob0, h.globW, h.out,
      h.next, h.res, h.st⟩
  | argStar t kws kwvals =>
    cases v with
    | tuple args => exact kwPhase_sim h hfg hs t args kws kwvals rfl hgks
    | _ => trivial
  | argKw t args =>
    cases v with
    | tuple pairs =>
      dsimp only
      cases Py.kwPairs pairs with
      | none => trivial
      | some kvs => exact finishArgs_sim h hfg hs t args kvs rfl hgks
    | _ => trivial
  | enterK o bound kx =>
    have ho := h.objs o
    simp only [editK]
    rcases hc : c.objs[o]? with _ | ⟨⟨S, C, cl, κ, sg⟩ | st⟩ <;>
      rcases hd : d.objs[o]? with _ | ⟨⟨S', C', cl', κ', sg'⟩ | st'⟩ <;>
      rw [hc, hd] at ho <;> simp only [ObjRel] at ho <;> (try dsimp only) <;> try trivial
    obtain ⟨rfl, rfl, hcl, hκ, rfl, hS, hC, hgood⟩ := ho
    exact enter_sim h hpop hs hS hC hgood hcl hκ _
  | decos ds =>
    cases ds with
    | nil => exact top_sim h (hfg.set rfl rfl trivial hgks) hs
    | cons d ds => exact top_sim h (hfg.set rfl (by simp [editK]) trivial (good_cons trivial hgks)) hs
  | raiseC cv =>
    cases cv with
    | none => exact top_sim h (hfg.set (by simp only [hfg.raiseNew hs]; rfl) rfl trivial hgks) hs
    | _ => exact top_sim h (hfg.set rfl (by simp [editK]) trivial (good_cons trivial hgks)) hs
  | raiseW e => simp only [editK]; rw [hfg.raiseNew hs]; exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | unpackK n =>
    simp only [editK]
    cases v with
    | tuple ws => dsimp only; split
                  · exact top_sim h (hfg.set rfl rfl trivial hgks) hs
                  · trivial
    | _ => trivial

theorem genEnd_sim {c d : Config σ} {fs gs : List (Frame σ)} (h : Rel R F c d)
    (hs : All2 (FrameRel R F) fs gs) (o : Nat) (ctl : Ctrl σ) (hc : editCtrl R ctl = ctl)
    (hgc : ∀ C, goodCtrl R F C ctl) : OptRel (Rel R F) (genEnd c fs o ctl) (genEnd d gs o ctl) := by
  cases fs <;> cases gs <;> simp only [All2] at hs <;> simp only [genEnd, OptRel]
  exact ⟨⟨hs.1.setVal ctl hc (hgc _), hs.2⟩, objs_ins h o trivial, h.cells, h.glob0, h.globW, h.out,
    h.next, h.res, h.st⟩

theorem raiseNew_rel {fs gs : List (Frame σ)} (hs : All2 (FrameRel R F) fs gs)
    (v : Val) : raiseNew gs v = raiseNew fs v := by
  simp only [raiseNew, curExc_rel hs]

theorem doneStep_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) :
    OptRel (Rel R F) (doneStep c f fs) (doneStep d g gs) := by
  unfold doneStep
  rcases hk : f.kont with _ | ⟨k, ks⟩
  · rw [show g.kont = [] by rw [hfg.kont, hk]; rfl, hfg.kind]
    cases f.kind with
    | mod => exact ⟨trivial, h.objs, h.cells, h.glob0, h.globW, h.out, h.next, rfl, h.st⟩
    | fn => exact retTo_sim h hs _ rfl (fun _ => trivial)
    | gen o => rw [raiseNew_rel hs]; exact genEnd_sim h hs o _ rfl (fun _ => trivial)
    | cls => simp only [classEnd]; rw [hfg.ns]; exact retTo_sim h hs _ rfl (fun _ => trivial)
  rw [kont_cons hfg hk]
  obtain ⟨hgk, hgks⟩ := good_kont hfg hk
  cases k with
  | seq ss => exact top_sim h (hfg.set rfl rfl hgk hgks) hs
  | loop e b u => exact top_sim h (hfg.set rfl rfl hgk.1 (good_cons (k := .whileS e b u) hgk hgks)) hs
  | tryE hs' u => exact top_sim h (hfg.set rfl rfl hgk.2 hgks) hs
  | handler x ex => exact unsetThen_sim h hfg hs hgk rfl rfl trivial hgks
  | _ => trivial

theorem raiseStep_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {v : Val}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs)
    (hl : ∀ lh e x hb hs u ks, f.kont = .tryE (.mk lh e x hb :: hs) u :: ks → ¬ F lh) :
    OptRel (Rel R F) (raiseStep c f fs v) (raiseStep d g gs v) := by
  unfold raiseStep
  rcases hk : f.kont with _ | ⟨k, ks⟩
  · rw [show g.kont = [] by rw [hfg.kont, hk]; rfl, hfg.kind]
    cases f.kind with
    | mod => exact ⟨trivial, h.objs, h.cells, h.glob0, h.globW, h.out, h.next, rfl, h.st⟩
    | fn => exact retTo_sim h hs _ rfl (fun _ => trivial)
    | gen o => exact genEnd_sim h hs o _ rfl (fun _ => trivial)
    | cls => exact retTo_sim h hs _ rfl (fun _ => trivial)
  rw [kont_cons hfg hk]
  obtain ⟨hgk, hgks⟩ := good_kont hfg hk
  have hdrop := top_sim h (hfg.set (c1 := f.ctrl) hfg.ctrl rfl hfg.good.1 hgks) hs
  cases k with
  | tryE hs' u =>
    cases hs' with
    | nil => exact hdrop
    | cons hd hs' =>
      obtain ⟨lh, e, x, hb⟩ := hd
      have hF := hl lh e x hb hs' u ks hk
      simp only [goodK, goodHs, hF, false_or] at hgk
      obtain ⟨⟨⟨hh, hx, hge, hgb⟩, hgh⟩, hgu⟩ := hgk
      simp only [editK, editHs, hh, Option.getD]
      exact top_sim h (hfg.set rfl rfl hge
        (good_cons (k := .catchS v x hb hs' u) ⟨hx, hgb, hgh, hgu⟩ hgks)) hs
  | handler x ex => exact unsetThen_sim h hfg hs hgk rfl rfl trivial hgks
  | yfGot dl =>
    simp only [editK]
    split
    · exact top_sim h (hfg.set rfl rfl trivial hgks) hs
    · exact hdrop
  | native k => exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | _ => exact hdrop

theorem yfStep_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} (dl : Deleg)
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) :
    OptRel (Rel R F) (yfStepS c f fs dl) (yfStepS d g gs dl) := by
  unfold yfStepS
  cases dl with
  | gen o =>
    have ho := h.objs o
    dsimp only
    rcases hc : c.objs[o]? with _ | ⟨⟨S, C, cl, κ, sg⟩ | st⟩ <;>
      rcases hd : d.objs[o]? with _ | ⟨⟨S', C', cl', κ', sg'⟩ | st'⟩ <;>
      rw [hc, hd] at ho <;> simp only [ObjRel] at ho <;> (try dsimp only) <;> try exact raise_sim h hfg hs _
    rcases st with gf | _ | _ <;> rcases st' with gf' | _ | _ <;> simp only [GRel] at ho <;>
      (try dsimp only) <;> try exact raise_sim h hfg hs _
    · exact ⟨⟨ho, hfg.set rfl (by simp [hfg.kont, editK]) trivial
        (good_cons (k := .yfGot (.gen o)) trivial hfg.good.2), hs⟩, objs_ins h o trivial, h.cells,
        h.glob0, h.globW, h.out, h.next, h.res, h.st⟩
    · exact top_sim h (hfg.setVal _ rfl trivial) hs
  | it v =>
    exact top_sim h (hfg.set rfl (by simp [hfg.kont, editK]) trivial
      (good_cons (k := .yfGot (.it v)) trivial hfg.good.2)) hs

theorem retStep_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)} {v : Val}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) :
    OptRel (Rel R F) (retStep c f fs v) (retStep d g gs v) := by
  unfold retStep
  rcases hk : f.kont with _ | ⟨k, ks⟩
  · rw [show g.kont = [] by rw [hfg.kont, hk]; rfl, hfg.kind]
    cases f.kind with
    | fn => exact retTo_sim h hs _ rfl (fun _ => trivial)
    | gen o => rw [raiseNew_rel hs]; exact genEnd_sim h hs o _ rfl (fun _ => trivial)
    | _ => trivial
  rw [kont_cons hfg hk]
  obtain ⟨hgk, hgks⟩ := good_kont hfg hk
  have hdrop := top_sim h (hfg.set (c1 := f.ctrl) hfg.ctrl rfl hfg.good.1 hgks) hs
  cases k with
  | handler x ex => exact unsetThen_sim h hfg hs hgk rfl rfl trivial hgks
  | _ => exact hdrop

theorem brkStep_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) :
    OptRel (Rel R F) (brkStep c f fs) (brkStep d g gs) := by
  unfold brkStep
  rcases hk : f.kont with _ | ⟨k, ks⟩
  · rw [show g.kont = [] by rw [hfg.kont, hk]; rfl]; trivial
  rw [kont_cons hfg hk]
  obtain ⟨hgk, hgks⟩ := good_kont hfg hk
  have hdrop := top_sim h (hfg.set (c1 := f.ctrl) hfg.ctrl rfl hfg.good.1 hgks) hs
  cases k with
  | loop e b u => exact top_sim h (hfg.set rfl rfl trivial hgks) hs
  | handler x ex => exact unsetThen_sim h hfg hs hgk rfl rfl trivial hgks
  | _ => exact hdrop

theorem contStep_sim {c d : Config σ} {f g : Frame σ} {fs gs : List (Frame σ)}
    (h : Rel R F c d) (hfg : FrameRel R F f g) (hs : All2 (FrameRel R F) fs gs) :
    OptRel (Rel R F) (contStep c f fs) (contStep d g gs) := by
  unfold contStep
  rcases hk : f.kont with _ | ⟨k, ks⟩
  · rw [show g.kont = [] by rw [hfg.kont, hk]; rfl]; trivial
  rw [kont_cons hfg hk]
  obtain ⟨hgk, hgks⟩ := good_kont hfg hk
  have hdrop := top_sim h (hfg.set (c1 := f.ctrl) hfg.ctrl rfl hfg.good.1 hgks) hs
  cases k with
  | loop e b u => exact top_sim h (hfg.set rfl rfl hgk.1 (good_cons (k := .whileS e b u) hgk hgks)) hs
  | handler x ex => exact unsetThen_sim h hfg hs hgk rfl rfl trivial hgks
  | _ => exact hdrop

/-- **Lemma A.2 (Step).** If `c ~ d` and `c`'s step evaluates no node of `F`,
then `d` steps exactly when `c` does, to a related configuration. -/
theorem step_sim (I : Py.Interp σ) {c d : Config σ} (h : Rel R F c d)
    (hF : ∀ l, focus c = some l → ¬ F l) : OptRel (Rel R F) (step I c) (step I d) := by
  have hst := h.stack
  unfold step
  rcases hcs : c.stack with _ | ⟨f, fs⟩ <;> rcases hds : d.stack with _ | ⟨g, gs⟩ <;>
    rw [hcs, hds] at hst <;> simp only [All2] at hst
  · trivial
  obtain ⟨hfg, hs⟩ := hst
  dsimp only
  rw [hfg.ctrl]
  rcases hfc : f.ctrl with e | v | ss | v | v | _ | _ | _ | dl | ⟨o, vs⟩ | ⟨k, r⟩ | ⟨vf, args, kws⟩ | ns
  · have hl : ¬ F e.label := hF _ (by simp [focus, hcs, hfc])
    exact evalStep_sim I h hfg hs hfc hl
  · exact valStep_sim I h hfg hs
  · cases ss with
    | nil => exact doneStep_sim h hfg hs
    | cons s ss =>
      have hl : ¬ F s.label := hF _ (by simp [focus, hcs, hfc])
      obtain ⟨s', hs', hrel⟩ := execStep_sim I h hfg hs hfc hl
      simp only [editCtrl, editB, hs', List.singleton_append]
      exact hrel
  · refine raiseStep_sim h hfg hs fun lh e x hb hs' u ks hk => hF _ ?_
    simp [focus, hcs, hfc, hk]
  · exact retStep_sim h hfg hs
  · trivial
  · exact brkStep_sim h hfg hs
  · exact contStep_sim h hfg hs
  · exact yfStep_sim dl h hfg hs
  · simp only [editCtrl]
    rcases c with ⟨cs, co, cc, cg0, cgW, cout, cn, cres, cst⟩
    rcases d with ⟨ds, dob, dc, dg0, dgW, dout, dn, dres, dst⟩
    dsimp only
    have hst : dst = cst := h.st
    rw [hst]; exact handle_sim h hfg hs _
  · simp only [editCtrl]
    rcases c with ⟨cs, co, cc, cg0, cgW, cout, cn, cres, cst⟩
    rcases d with ⟨ds, dob, dc, dg0, dgW, dout, dn, dres, dst⟩
    dsimp only
    have hst : dst = cst := h.st
    rw [hst]; exact handle_sim h hfg hs _
  · exact callArgs_sim I h (hfg.setVal (.wait) rfl trivial) hs vf args kws
  · exact nsStep_sim h hfg hs ns


/-! ## Executions -/

theorem run_halt {I : Py.Interp σ} {c : Config σ} (h : step I c = none) : ∀ n, run I n c = c
  | 0 => rfl
  | n + 1 => by simp [run, h]

theorem run_some {I : Py.Interp σ} {c c' : Config σ} (h : step I c = some c') (n : Nat) :
    run I (n + 1) c = run I n c' := by simp [run, h]

theorem NoReach.next {I : Py.Interp σ} {c c' : Config σ} (hn : NoReach I F c) (h : step I c = some c') :
    NoReach I F c' := fun n l hl => hn (n + 1) l (by rw [run_some h]; exact hl)

theorem NoReach.now {I : Py.Interp σ} {c : Config σ} (hn : NoReach I F c) :
    ∀ l, focus c = some l → ¬ F l := hn 0

/-- By Lemma A.2 and induction on p's steps, the configurations at each step are
related, and `p` ends exactly when `q` does. -/
theorem run_sim (I : Py.Interp σ) : ∀ (n : Nat) {c d : Config σ}, Rel R F c d → NoReach I F c →
    Rel R F (run I n c) (run I n d) ∧ (step I (run I n c) = none ↔ step I (run I n d) = none)
  | 0, c, d, h, hn => by
    have := step_sim I h hn.now
    refine ⟨h, ?_⟩
    simp only [run]
    revert this; cases step I c <;> cases step I d <;> simp [OptRel]
  | n + 1, c, d, h, hn => by
    have := step_sim I h hn.now
    revert this
    rcases hc : step I c with _ | c' <;> rcases hd : step I d with _ | d' <;> simp only [OptRel] <;>
      intro hr
    · rw [run_halt hc, run_halt hd]; simp [hc, hd, h]
    · cases hr
    · cases hr
    · rw [run_some hc, run_some hd]; exact run_sim I n hr (hn.next hc)

theorem outcome_rel {c d : Config σ} (h : Rel R F c d) : outcome d = outcome c := by
  have hs := h.stack
  unfold outcome
  rw [h.res, h.out, h.glob, h.st]
  cases hc : c.stack <;> cases hd : d.stack <;> rw [hc, hd] at hs <;> simp [All2] at hs <;> rfl

/-- Theorem 5 for any set `F` whose nodes cover what the relation needs: if
`c ~ d` and the execution from `c` evaluates no node of `F`, the executions
from `c` and `d` have the same outcome, or both diverge. -/
theorem same_outcome (I : Py.Interp σ) {c d : Config σ} (h : Rel R F c d) (hn : NoReach I F c) :
    (∀ o, Terminates I c o ↔ Terminates I d o) ∧ (Diverges I c ↔ Diverges I d) := by
  refine ⟨fun o => ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨n, h1, h2⟩
    obtain ⟨hr, hh⟩ := run_sim I n h hn
    exact ⟨n, hh.1 h1, by rw [outcome_rel hr, h2]⟩
  · rintro ⟨n, h1, h2⟩
    obtain ⟨hr, hh⟩ := run_sim I n h hn
    exact ⟨n, hh.2 h1, by rw [← outcome_rel hr, h2]⟩
  · intro hd n h1; exact hd n ((run_sim I n h hn).2.2 h1)
  · intro hd n h1; exact hd n ((run_sim I n h hn).2.1 h1)

end

end PyCore
