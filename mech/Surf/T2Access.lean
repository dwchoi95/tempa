/-
(T2), attributes, subscripts, slices, unary operators, displays, f-strings and formatted values.
-/
import Surf.T2Cases

namespace Surf.T2
open PyCore (Name Label)
open Py (Val)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

/-! Helpers of this group, in its own namespace; the group's lemmas are restated in `Surf.T2` at the end. -/
namespace Access

/-! ## Steps of the access cases -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A continuation item that is no `enterK` added on top. -/
theorem esub_tail {a : Sem.Kont σ} {k K : List (Sem.Kont σ)} (ha : ∀ o b kx, a ≠ .enterK o b kx)
    (h : EnterSub k K) : EnterSub (a :: k) K := fun o b kx hm =>
  (List.mem_cons.1 hm).elim (fun e => absurd e.symm (ha o b kx)) (h o b kx)

theorem t_eq (ht : t.stack = f' :: fs') {c' : PyCore.Ctrl σ} {k' : List (PyCore.Kont σ)} (hc' : f'.ctrl = c')
    (hk' : f'.kont = k') : { t with stack := { f' with ctrl := c', kont := k' } :: fs' } = t := by
  subst hc' hk'; exact t_eta ht

theorem touch_ev (A : At p H s t f fs f' fs') {e : Expr} (hc : f.ctrl = .ev e) : Touch p s e.label :=
  .inl (by simp [Sem.focus, A.hs, hc, lbl_eq])

/-- The continuation relation at the history after a step of `s`. -/
theorem lift (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (hk : KRel A.x U i K K') :
    KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U i K K' :=
  KRel.ext ⟨fun _ h => .inl h, Agree.refl _ _ _⟩ hk

/-- Both runs step to related top frames, PyCore's steps evaluating no node. -/
theorem goP (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)} {xs : List (Sem.Config σ)} {ys : List (PyCore.Config σ)}
    (pa : Path (Sem.step I) s { s with stack := { f with ctrl := c, kont := k } :: fs } xs) (hxs : xs ≠ [])
    (pb : Path (PyCore.step I) t { t with stack := { f' with ctrl := c', kont := k' } :: fs' } ys) (hys : ys ≠ [])
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i k k') (hf : ∀ y ∈ ys, PyCore.focus y = none)
    (he : EnterSub k f.kont := by esub) : Goal I p H s t :=
  goal_b pa hxs pb hys (crelI_seen (A.set hc hk he)) (cover_none hf)

/-- An `ev` case whose PyCore code calls a core constant on an argument record: Surf steps to `c`,
`k`; PyCore reaches the record's first argument, every node on the way made for the node `l`. -/
theorem ev_cc (A : At p H s t f fs f' fs') {l : Label} {g : String} {a : PE} {rest : List PE}
    {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} {U : Label → Prop}
    (ht : Touch p s l) (hc' : f'.ctrl = .ev (ccR (sub l 0) g (a :: rest)))
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := k } :: fs })
    (hcr : CR p f.chain U true c (.ev a))
    (hk : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U true k
      (recK [] rest (.callA (Py.constVal I g) :: f'.kont))) (he : EnterSub k f.kont := by esub) : Goal I p H s t := by
  obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 0) g a rest f'.kont
  rw [t_eq A.ht hc' rfl] at pc
  exact goal_b (.cons e1 (.nil _)) (by simp) pc hys
    (.inl (((A.zero.upd c k (.ev a) (recK [] rest (.callA (Py.constVal I g) :: f'.kont)) he).mono_H
      fun _ h => .inl h).crel hcr hk))
    (cover_of (l := l) (by simp) ht fun y hy x hx => by rw [hfoc y hy x hx]; exact sub_div _ _ (by omega))

/-- PyCore adds a value to an argument record. -/
theorem pstep_rec (ht : t.stack = f' :: fs') {v : Val} {done : List Val} {K1 : List (PyCore.Kont σ)}
    (hc' : f'.ctrl = .val v) (hK' : f'.kont = .binR "," (.data "$args" done) :: K1) :
    PyCore.step I t = some { t with stack := { f' with ctrl := .val (.data "$args" (done ++ [v])), kont := K1 } :: fs' } := by
  simp [PyCore.step, ht, hc', hK', PyCore.valStep, PyCore.top]

/-- A value completes an argument record, whose operation `o` is next (one Surf step to `.op o`). -/
theorem val_recOp (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {o : Py.Op} {done : List Val}
    {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} (hc' : f'.ctrl = .val v)
    (hK' : f'.kont = recK done [] (.callA (.op o) :: K'))
    (pa : Path (Sem.step I) s { s with stack := { f with ctrl := .op o (done ++ [v]), kont := K } :: fs } xs)
    (hxs : xs ≠ []) (hk : KRel A.x U true K K') (he : EnterSub K f.kont := by esub) : Goal I p H s t := by
  have e2 := pstep_rec (I := I) A.ht hc' (by rw [hK']; rfl)
  refine goP A pa hxs (.cons e2 (.cons (by simp [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.top,
    PyCore.argList]) (.nil _))) (by simp) .op hk ?_ he
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc']

/-- A value goes into an argument record, its next argument `e'` evaluated next. -/
theorem val_recNext (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {done : List Val} {e' : PE}
    {rest : List PE} {c : Sem.Ctrl σ} {K : List (Sem.Kont σ)} {K1 : List (PyCore.Kont σ)} (hc' : f'.ctrl = .val v)
    (hK' : f'.kont = recK done (e' :: rest) K1)
    (pa : Path (Sem.step I) s { s with stack := { f with ctrl := c, kont := K } :: fs } xs) (hxs : xs ≠ [])
    (hcr : CR p f.chain U true c (.ev e')) (hk : KRel A.x U true K (recK (done ++ [v]) rest K1))
    (he : EnterSub K f.kont := by esub) : Goal I p H s t := by
  have e2 := pstep_rec (I := I) A.ht hc' (by rw [hK']; rfl)
  refine goP A pa hxs (.cons e2 (.cons (by simp [PyCore.step, PyCore.valStep, PyCore.top, recK]) (.nil _)))
    (by simp) hcr hk ?_ he
  intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc']

/-- `ev_cc` for a call whose first argument is itself a call (a conversion before `format`), the
inner call's nodes made for the same node `l`. -/
theorem ev_cc2 (A : At p H s t f fs f' fs') {l : Label} {g g2 : String} {a : PE} {rest : List PE}
    {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} {U : Label → Prop}
    (ht : Touch p s l) (hc' : f'.ctrl = .ev (ccR (sub l 0) g (ccR (sub l 1) g2 [a] :: rest)))
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := k } :: fs })
    (hcr : CR p f.chain U true c (.ev a))
    (hk : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U true k
      (recK [] [] (.callA (Py.constVal I g2) :: recK [] rest (.callA (Py.constVal I g) :: f'.kont))))
    (he : EnterSub k f.kont := by esub) : Goal I p H s t := by
  obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 0) g (ccR (sub l 1) g2 [a]) rest f'.kont
  obtain ⟨ys2, pc2, -, hfoc2⟩ := cc_enter (I := I) t f' fs' (sub l 1) g2 a []
    (recK [] rest (.callA (Py.constVal I g) :: f'.kont))
  rw [t_eq A.ht hc' rfl] at pc
  exact goal_b (.cons e1 (.nil _)) (by simp) (pc.append pc2) (by simp [hys])
    (.inl (((A.zero.upd c k (.ev a) _ he).mono_H fun _ h => .inl h).crel hcr hk))
    (cover_of (l := l) (by simp) ht fun y hy x hx => by
      rcases List.mem_append.1 hy with hy | hy
      · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
      · rw [hfoc2 y hy x hx]; exact sub_div _ _ (by omega))

theorem s_eq (hs : s.stack = f :: fs) {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} (hc : f.ctrl = c)
    (hk : f.kont = k) : { s with stack := { f with ctrl := c, kont := k } :: fs } = s := by
  subst hc hk; exact s_eta hs

/-- The value of a formatted value, then its spec if any and `format`; `pre` the Surf steps that
reached `fmtC`. -/
theorem val_fmtC (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {spec : Option Expr}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} {xs0 : List (Sem.Config σ)}
    (pre : Path (Sem.step I) s { s with stack := { f with ctrl := .val v, kont := .fmtC spec :: K0 } :: fs } xs0)
    (hc' : f'.ctrl = .val v) (hK' : f'.kont = fmtRest f.chain spec K0') (hg : GoodO p f.chain U spec)
    (hk : KRel A.x U true K0 K0') (he : EnterSub K0 f.kont := by esub) : Goal I p H s t := by
  cases spec with
  | none =>
    exact val_recOp A hc' (done := []) (by rw [hK']; rfl)
      (pre.append (.cons (by simp [Sem.step, Sem.valStep, Sem.doOp, Sem.setC]) (.nil _))) (by simp) hk he
  | some sp =>
    exact val_recNext A hc' (done := []) (by rw [hK']; rfl)
      (pre.append (.cons (by simp [Sem.step, Sem.valStep, Sem.setC]) (.nil _))) (by simp) (.ev hg) (.acc (.fmtS hk))
      (esub_tail (by simp) he)

/-! ### Signals -/

/-- The PyCore items an exception or a return passes with no effect. -/
def Plain : PyCore.Kont σ → Prop
  | .binR .. | .binL .. | .callA .. => True
  | _ => False

/-- A signal passes PyCore's items `pre`. -/
theorem pop_path {c : PyCore.Ctrl σ} (hc : (∃ v, c = .raise v) ∨ (∃ v, c = .retv v) ∨ c = .brk ∨ c = .cont) (K' : List (PyCore.Kont σ)) :
    ∀ pre : List (PyCore.Kont σ), (∀ k ∈ pre, Plain k) →
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := c, kont := pre ++ K' } :: fs' }
      { t with stack := { f' with ctrl := c, kont := K' } :: fs' } ys ∧ ys.length = pre.length ∧
      ∀ y ∈ ys, PyCore.focus y = none
  | [], _ => ⟨[], .nil _, rfl, by simp⟩
  | k :: pre, hp => by
    obtain ⟨ys, py, hl, hf⟩ := pop_path hc K' pre (fun k hk => hp k (List.mem_cons_of_mem _ hk))
    have hk := hp k List.mem_cons_self
    refine ⟨_ :: ys, .cons ?_ py, by simp [hl], ?_⟩
    · rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl <;> cases k <;> simp [Plain] at hk <;>
        simp [PyCore.step, PyCore.raiseStep, PyCore.retStep, PyCore.brkStep, PyCore.contStep, PyCore.top]
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl <;> cases k <;> simp [Plain] at hk <;> simp [PyCore.focus]
      · exact hf y hy

/-- A signal passes one Surf item and PyCore's items `pre` for it. -/
theorem acc_sig_pop (A : At p H s t f fs f' fs') {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} (pre : List (PyCore.Kont σ))
    (hcr : CR p f.chain U true c c') (hsig : (∃ v, c' = .raise v) ∨ (∃ v, c' = .retv v) ∨ c' = .brk ∨ c' = .cont) (hc' : f'.ctrl = c')
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := K } :: fs })
    (hK' : f'.kont = pre ++ K') (hp : ∀ k ∈ pre, Plain k) (hne : pre ≠ []) (hk : KRel A.x U true K K')
    (he : EnterSub K f.kont := by esub) : Goal I p H s t := by
  obtain ⟨ys, py, hl, hf⟩ := pop_path (I := I) (t := t) (f' := f') (fs' := fs') hsig K' pre hp
  rw [t_eq A.ht hc' hK'] at py
  exact goP A (.cons e1 (.nil _)) (by simp) py (by rintro rfl; exact hne (List.length_eq_zero_iff.1 hl.symm))
    hcr hk hf he

end

/-! ## Entering the expressions -/

theorem ev_unary (l op a) : EvCase I p (.unary l op a) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hop : okName op = true := by have := hg.ok; simp only [okE, Bool.and_eq_true] at this; exact this.1
  refine ev_cc A (c := .ev a) (k := .unK op :: f.kont) (touch_ev A hc) (by rw [hc']; rfl)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC]) (.ev (by subg)) ?_
  rw [kc_unop I (nc_ok hop)]; exact .acc (.unK (lift A hk))

theorem ev_sub (l e i) : EvCase I p (.sub l e i) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  refine ev_cc A (c := .ev e) (k := .subL i :: f.kont) (touch_ev A hc) (by rw [hc']; rfl)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC]) (.ev (by subg)) ?_
  rw [kc_getitem I]; exact .acc (.subL (by subg) (lift A hk))

theorem ev_attr (l e a) : EvCase I p (.attr l e a) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have ha : okName a = true := by have := hg.ok; simp only [okE, Bool.and_eq_true] at this; exact this.1
  refine ev_cc A (c := .ev e) (k := .attrK (Sem.mg f a) :: f.kont) (touch_ev A hc) (by rw [hc']; rfl)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC]) (.ev (by subg)) ?_
  rw [kc_getattr I (nc_mangle_pv hg.pv (nc_ok ha))]; exact .acc (.attrK (lift A hk))

theorem ev_fmt (l e c s) : EvCase I p (.fmt l e c s) := by
  intro H s0 t f fs f' fs' U A W hc hc' hg hk
  have e1 : Sem.step I s0 = some { s0 with stack := { f with ctrl := .ev e, kont := .fmtV c s :: f.kont } :: fs } := by
    simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC]
  by_cases hc1 : c = -1
  · subst hc1
    cases s with
    | none =>
      have hk1 := AccK.fmtV (x := cx p (Seen (Touch p) H [s0]) (rdOf t f') (ownOf t f') f) (c := -1) (spec := none)
        trivial (lift A hk)
      simp only [↓reduceIte] at hk1
      refine ev_cc A (l := l) (g := "$op:format") (rest := []) (c := .ev e) (k := .fmtV (-1) none :: f.kont)
        (touch_ev A hc) (by rw [hc']; simp [trE, cc]) e1 (.ev (by subg)) ?_
      rw [kc_format I]; exact .acc hk1
    | some sp =>
      have hk1 := AccK.fmtV (x := cx p (Seen (Touch p) H [s0]) (rdOf t f') (ownOf t f') f) (c := -1) (spec := some sp)
        (show GoodE p f.chain U sp by subg) (lift A hk)
      simp only [↓reduceIte] at hk1
      refine ev_cc A (l := l) (g := "$op:format") (rest := [trE f.chain sp]) (c := .ev e)
        (k := .fmtV (-1) (some sp) :: f.kont) (touch_ev A hc)
        (by rw [hc']; simp [trE, cc]) e1 (.ev (by subg)) ?_
      rw [kc_format I]; exact .acc hk1
  · cases s with
    | none =>
      have hk1 := AccK.fmtV (x := cx p (Seen (Touch p) H [s0]) (rdOf t f') (ownOf t f') f) (c := c) (spec := none)
        trivial (lift A hk)
      simp only [hc1, ↓reduceIte] at hk1
      refine ev_cc2 A (l := l) (g := "$op:format") (g2 := "$op:convert:" ++ toString c) (rest := []) (c := .ev e)
        (k := .fmtV c none :: f.kont) (touch_ev A hc)
        (by rw [hc']; simp [trE, cc, hc1]) e1 (.ev (by subg)) ?_
      rw [kc_format I, kc_convert I]; exact .acc hk1
    | some sp =>
      have hk1 := AccK.fmtV (x := cx p (Seen (Touch p) H [s0]) (rdOf t f') (ownOf t f') f) (c := c) (spec := some sp)
        (show GoodE p f.chain U sp by subg) (lift A hk)
      simp only [hc1, ↓reduceIte] at hk1
      refine ev_cc2 A (l := l) (g := "$op:format") (g2 := "$op:convert:" ++ toString c) (rest := [trE f.chain sp])
        (c := .ev e) (k := .fmtV c (some sp) :: f.kont) (touch_ev A hc)
        (by rw [hc']; simp [trE, cc, hc1]) e1 (.ev (by subg)) ?_
      rw [kc_format I, kc_convert I]; exact .acc hk1

set_option hygiene false in
macro "sstep1" : tactic => `(tactic| simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.doOp])

/-- The Surf items of `AccK`, which a signal passes with no effect. -/
def SPl : Sem.Kont σ → Prop
  | .unK _ | .attrK _ | .subL _ | .subR _ | .fmtV .. | .fmtC _ | .fmtS _ | .evs .. => True
  | _ => False

theorem recK_app (done : List Val) (rest : List PE) (k : PyCore.Kont σ) (K' : List (PyCore.Kont σ)) :
    recK done rest (k :: K') = recK done rest [k] ++ K' := by simp [recK]

theorem recK_plain (done : List Val) (rest : List PE) (g : Val) :
    ∀ k ∈ (recK done rest [.callA g] : List (PyCore.Kont σ)), Plain k := by
  intro k hk
  simp only [recK, List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | ⟨_, _, rfl⟩ | rfl <;> trivial

theorem recK_ne {done : List Val} {rest : List PE} {K : List (PyCore.Kont σ)} : recK done rest K ≠ [] := by
  simp [recK]

/-! ## Slices and f-strings

Their parts (`Kont.evs rest acc (.op o)`) are the entry `AccK.evsOp` of `T2Rel.lean`; `EvsMk` states its
constructor, and the cases are proved from it. -/

/-- The entry `AccK.evsOp`: the parts `rest` still to evaluate, the values `acc` so far (reversed),
then the operation `o`; PyCore holds the record of the values and evaluates the parts `ps` into it. -/
def EvsMk (σ : Type) : Prop :=
  ∀ {x : Cx} {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l : Label}
    {rest : List (Option Expr)} {ps : List PE} {acc : List Val} {o : Py.Op},
    x.H l → PartsR x U l rest ps → KRel x U true K K' →
    KRel x U true (.evs rest acc (.op o) :: K) (recK acc.reverse ps (.callA (.op o) :: K'))

theorem trEs_eq (C : List Scope) : ∀ es : List Expr, trEs C es = es.map (trE C)
  | [] => rfl
  | e :: es => by simp [trEs, trEs_eq C es]

theorem items_foldl (C' : List PyCore.Scope) (r : Label) : ∀ (es : List PE) (init : PE),
    PyCore.itemsE R0 C' (es.foldl (fun acc e => .bin r "," acc e) init) =
      PyCore.itemsE R0 C' init ++ es.flatMap (PyCore.itemsE R0 C')
  | [], init => by simp
  | e :: es, init => by simp [items_foldl C' r es, PyCore.itemsE]

theorem mem_itemsEs {C : List Scope} {e : Expr} {x : Item} : ∀ {es : List Expr}, e ∈ es →
    x ∈ itemsE C e → x ∈ itemsEs C es
  | e' :: es, he, hx => by
    rcases List.mem_cons.1 he with rfl | he
    · simp [itemsEs, hx]
    · simp [itemsEs, mem_itemsEs he hx]

theorem mem_labelsEs {e : Expr} {l : Label} : ∀ {es : List Expr}, e ∈ es → l ∈ labelsE e → l ∈ labelsEs es
  | e' :: es, he, hx => by
    rcases List.mem_cons.1 he with rfl | he
    · simp [labelsEs, hx]
    · simp [labelsEs, mem_labelsEs he hx]

theorem acc_okEs_mem {e : Expr} : ∀ {es : List Expr}, e ∈ es → okEs es = true → okE e = true
  | e' :: es, he, h => by
    simp only [okEs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact acc_okEs_mem he h.2

theorem good_fstr {C : List Scope} {U : Label → Prop} {l : Label} {es : List Expr}
    (hg : GoodE p C U (.fstr l es)) {e : Expr} (he : e ∈ es) : GoodE p C U e :=
  GoodE.of hg (fun x hx => by simpa [itemsE] using mem_itemsEs he hx)
    (fun x hx => by
      simp only [trE, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        items_foldl, trEs_eq, List.nil_append, List.mem_flatMap, List.mem_map]
      exact ⟨_, ⟨e, he, rfl⟩, hx⟩)
    (fun h => acc_okEs_mem he (by simpa [okE] using h))
    (fun x hx => by simp [labelsE, mem_labelsEs he hx])
    (fun h => nodup_labelsEs he (by simp only [labelsE, List.nodup_cons] at h; exact h.2))
    (fun x hx => by simp [touchE, touchEs_mem he hx])

theorem partR_some {x : Cx} {U : Label → Prop} {l : Label} :
    ∀ {es : List Expr}, (∀ e ∈ es, GoodE x.p x.C U e) → PartsR x U l (es.map some) (trEs x.C es)
  | [], _ => trivial
  | _ :: _, h => ⟨⟨h _ List.mem_cons_self, rfl⟩, partR_some fun e he => h e (List.mem_cons_of_mem _ he)⟩

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem pstep_none {K1 : List (PyCore.Kont σ)} {r : Label} (hK : K1 = .binR "," v1 :: K2) :
    PyCore.step I { t with stack := { f' with ctrl := .ev (.const r "$none"), kont := K1 } :: fs' } =
      some { t with stack := { f' with ctrl := .val .none, kont := K1 } :: fs' } := by
  subst hK; simp [PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]

/-- A value reaches the parts of a slice or an f-string (the case of `val_acc` for `AccK.evsOp`). -/
theorem val_evs (mk : EvsMk σ) (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label}
    {rest : List (Option Expr)} {ps : List PE} {acc : List Val} {o : Py.Op} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs rest acc (.op o) :: K0) (hK' : f'.kont = recK acc.reverse ps (.callA (.op o) :: K0'))
    (hH : H l) (hr : PartsR A.x U l rest ps) (hk : KRel A.x U true K0 K0') : Goal I p H s t := by
  match rest, ps, hr with
  | [], [], _ =>
    have e1 : Sem.step I s =
        some { s with stack := { f with ctrl := .val (.tuple (v :: acc).reverse), kont := .evsEnd (.op o) :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
    exact val_recOp A hc' hK' (.cons e1 (.cons (by simp [Sem.step, Sem.valStep, Sem.finish, Sem.doOp, Sem.setC])
      (.nil _))) (by simp) hk
  | a :: rest', pe :: ps', ⟨ha, hr'⟩ =>
    have hk1 := mk (acc := v :: acc) (o := o) hH hr' hk
    rw [List.reverse_cons] at hk1
    cases a with
    | some e =>
      obtain ⟨hg, rfl⟩ := ha
      exact val_recNext A hc' hK' (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC])
        (.nil _)) (by simp) (.ev hg) hk1
    | none =>
      obtain ⟨k, hk64, rfl⟩ := ha
      let K1 : List (PyCore.Kont σ) := recK (acc.reverse ++ [v]) ps' (.callA (.op o) :: K0')
      have e2 := pstep_rec (I := I) A.ht hc' (by rw [hK']; rfl)
      let K2 : List (PyCore.Kont σ) := .binL "," (.const (sub l k) "$none") :: (ps'.map (.binL ",") ++ .callA (.op o) :: K0')
      have e3 : PyCore.step I { t with stack := { f' with ctrl := .val (.data "$args" (acc.reverse ++ [v])), kont := K2 } :: fs' } =
          some { t with stack := { f' with ctrl := .ev (.const (sub l k) "$none"), kont := K1 } :: fs' } := by
        simp [PyCore.step, PyCore.valStep, PyCore.top, K1, K2, recK]
      refine goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]) (.nil _)) (by simp)
        (.cons e2 (.cons e3 (.cons (pstep_none rfl) (.nil _)))) (by simp) (crelI_seen (A.set .val hk1)) ?_
      intro y hy x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      have hx := pfocus_le hx
      rcases hy with rfl | rfl | rfl
      · simp [PyCore.focus, A.ht, hc'] at hx
      · simp [PyCore.focus] at hx
      · simp [PyCore.focus, PyCore.Expr.label] at hx
        rw [← hx, sub_div _ _ hk64]; exact .inl hH

/-- A signal passes the parts of a slice or an f-string (the case of `sig_acc` for `AccK.evsOp`). -/
theorem sig_evs (A : At p H s t f fs f' fs') {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {ps : List PE} {acc : List Val} {o : Py.Op} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hcr : CR p f.chain U true c c') (hsig : (∃ v, c' = .raise v) ∨ (∃ v, c' = .retv v) ∨ c' = .brk ∨ c' = .cont)
    (hc' : f'.ctrl = c')
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := K0 } :: fs })
    (hK' : f'.kont = recK acc.reverse ps (.callA (.op o) :: K0')) (hk : KRel A.x U true K0 K0')
    (he : EnterSub K0 f.kont := by esub) : Goal I p H s t :=
  acc_sig_pop A _ hcr hsig hc' e1 (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne hk he

theorem ev_slice_of (mk : EvsMk σ) (l a b c) : EvCase I p (.slice l a b c) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hpart : ∀ (k : Nat) (o : Option Expr), k < 64 → GoodO p f.chain U o →
      PartR (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U l o (trO f.chain l k o) := by
    intro k o hk64 ho
    cases o with
    | none => exact ⟨k, hk64, rfl⟩
    | some e => exact ⟨ho, rfl⟩
  have gb : GoodO p f.chain U b := by cases b with | none => trivial | some e => subg
  have gc : GoodO p f.chain U c := by cases c with | none => trivial | some e => subg
  have hk1 := mk (x := cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) (acc := []) (o := .display .slice)
    (show Seen (Touch p) H [s] l from .inr ⟨s, by simp, touch_ev A hc⟩)
    (show PartsR _ U l [b, c] [_, _] from ⟨hpart 2 b (by omega) gb, hpart 3 c (by omega) gc, trivial⟩) (lift A hk)
  have hc2 : f'.ctrl = .ev (ccR (sub l 0) "$op:display:slice" [trO f.chain l 1 a, trO f.chain l 2 b, trO f.chain l 3 c]) := by
    rw [hc']; rfl
  cases a with
  | some e =>
    refine ev_cc A (l := l) (c := .ev e) (k := .evs [b, c] [] (.op (.display .slice)) :: f.kont) (touch_ev A hc) hc2
      (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC]) (.ev (by subg)) ?_
    rw [kc_slice I]; exact hk1
  | none =>
    let K1 : List (PyCore.Kont σ) :=
      recK [] [trO f.chain l 2 b, trO f.chain l 3 c] (.callA (.op (.display .slice)) :: f'.kont)
    obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 0) "$op:display:slice" (.const (sub l 1) "$none")
      [trO f.chain l 2 b, trO f.chain l 3 c] f'.kont
    rw [t_eq A.ht (c' := .ev (ccR (sub l 0) "$op:display:slice"
      [.const (sub l 1) "$none", trO f.chain l 2 b, trO f.chain l 3 c])) hc2 rfl, kc_slice I] at pc
    exact goal_b (.cons (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC]) (.nil _)) (by simp)
      (pc.append (.cons (pstep_none (K1 := K1) rfl) (.nil _))) (by simp)
      (.inl (((A.zero.upd (.val .none) (.evs [b, c] [] (.op (.display .slice)) :: f.kont) (.val .none) K1).mono_H
        fun _ h => .inl h).crel .val hk1))
      (cover_of (l := l) (by simp) (touch_ev A hc) fun y hy x hx => by
        rcases List.mem_append.1 hy with hy | hy
        · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
        · simp at hy; subst hy; simp [PyCore.focus, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega))

theorem ev_fstr_of (mk : EvsMk σ) (l es) : EvCase I p (.fstr l es) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  cases es with
  | nil =>
    let r := sub l 0
    let g := "$op:display:fstr"
    let mkT (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ :=
      { t with stack := { f' with ctrl := c, kont := k } :: fs' }
    have p1 : Path (PyCore.step I) t (mkT (.op (.display .fstr) []) f'.kont)
        [t, mkT (.ev (.const r g)) (.callF (.const r "$args") :: f'.kont),
          mkT (.val (.op (.display .fstr))) (.callF (.const r "$args") :: f'.kont),
          mkT (.ev (.const r "$args")) (.callA (.op (.display .fstr)) :: f'.kont),
          mkT (.val (.data "$args" [])) (.callA (.op (.display .fstr)) :: f'.kont)] := by
      refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))))
      · rw [pstep_ev A.ht hc']; simp [trE, trEs, cc, ccR, recR, PyCore.evalStep, PyCore.top, mkT, r, g]
      · simp [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, r, g, kc_fstr I]
      · simp [mkT, PyCore.step, PyCore.valStep, PyCore.top]
      · simp [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
      · simp [mkT, PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.top, PyCore.argList]
    have e1 : Sem.step I s =
        some { s with stack := { f with ctrl := .val (.tuple []), kont := .evsEnd (.op (.display .fstr)) :: f.kont } :: fs } := by
      simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC]
    refine goal_b (.cons e1 (.cons (by simp [Sem.step, Sem.valStep, Sem.finish, Sem.doOp, Sem.setC]) (.nil _)))
      (by simp) p1 (by simp) (crelI_seen (A.set .op hk)) (cover_of (l := l) (by simp) (touch_ev A hc) ?_)
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · simp [PyCore.focus, A.ht, hc', trE, trEs, cc, ccR, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [mkT, PyCore.focus, PyCore.Expr.label, r] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [mkT, PyCore.focus] at hx
    · simp [mkT, PyCore.focus, PyCore.Expr.label, r] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [mkT, PyCore.focus] at hx
  | cons e rest =>
    have hk1 := mk (x := cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) (acc := []) (o := .display .fstr)
      (show Seen (Touch p) H [s] l from .inr ⟨s, by simp, touch_ev A hc⟩)
      (partR_some (l := l) fun e' he => good_fstr hg (List.mem_cons_of_mem _ he)) (lift A hk)
    refine ev_cc A (l := l) (c := .ev e) (k := .evs (rest.map some) [] (.op (.display .fstr)) :: f.kont)
      (touch_ev A hc) (by rw [hc']; rfl)
      (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC]) (.ev (good_fstr hg List.mem_cons_self)) ?_
    rw [kc_fstr I]; exact hk1


/-! ### Dictionary displays

A dictionary's keys and values (`**m` gives `m` alone) are the parts of `AccK.evsOp`. -/

/-- The expressions of a dictionary display's items, in order. -/
def dparts : List DItem → List Expr
  | [] => []
  | .mk (some k) v :: kvs => k :: v :: dparts kvs
  | .mk none v :: kvs => v :: dparts kvs

theorem trKVs_eq (C : List Scope) : ∀ kvs : List DItem, trKVs C kvs = (dparts kvs).map (trE C)
  | [] => rfl
  | .mk (some _) _ :: kvs => by simp [trKVs, dparts, trKVs_eq C kvs]
  | .mk none _ :: kvs => by simp [trKVs, dparts, trKVs_eq C kvs]

theorem dflat_eq : ∀ kvs : List DItem,
    (kvs.flatMap fun | .mk (some k) v => [some k, some v] | .mk none v => [some v]) = (dparts kvs).map some
  | [] => rfl
  | .mk (some _) _ :: kvs => by simp [dparts, dflat_eq kvs]
  | .mk none _ :: kvs => by simp [dparts, dflat_eq kvs]

theorem dparts_tch {e : Expr} {x : Label × Expr} : ∀ {kvs : List DItem}, e ∈ dparts kvs → x ∈ touchE e →
    x ∈ touchDs kvs
  | [], h, _ => by simp [dparts] at h
  | .mk (some k) v :: kvs, h, hx => by
    simp only [dparts, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · simp [touchDs, touchO, hx]
    · simp [touchDs, hx]
    · simp [touchDs, dparts_tch h hx]
  | .mk none v :: kvs, h, hx => by
    simp only [dparts, List.mem_cons] at h
    rcases h with rfl | h
    · simp [touchDs, hx]
    · simp [touchDs, dparts_tch h hx]

theorem dparts_mem {C : List Scope} {e : Expr} : ∀ {kvs : List DItem}, e ∈ dparts kvs →
    (∀ x, x ∈ itemsE C e → x ∈ itemsDs C kvs) ∧ (okDs kvs = true → okE e = true) ∧
      (∀ l, l ∈ labelsE e → l ∈ labelsDs kvs) ∧ ((labelsDs kvs).Nodup → (labelsE e).Nodup)
  | [], h => by simp [dparts] at h
  | .mk k v :: kvs, h => by
    have key : e = v ∨ k = some e ∨ e ∈ dparts kvs := by
      cases k with
      | none =>
        simp only [dparts, List.mem_cons] at h
        rcases h with h | h
        · exact .inl h
        · exact .inr (.inr h)
      | some k =>
        simp only [dparts, List.mem_cons] at h
        rcases h with h | h | h
        · exact .inr (.inl (by rw [h]))
        · exact .inl h
        · exact .inr (.inr h)
    have e0 : labelsDs (.mk k v :: kvs) = labelsO k ++ (labelsE v ++ labelsDs kvs) := by simp [labelsDs]
    rcases key with rfl | rfl | h'
    · refine ⟨fun x hx => by simp [itemsDs, hx], fun h => by simp_all [okDs], fun l hl => by simp [labelsDs, hl],
        fun h => ?_⟩
      rw [e0] at h; exact h.sublist ((List.sublist_append_left _ _).trans (List.sublist_append_right _ _))
    · refine ⟨fun x hx => by simp [itemsDs, itemsO, hx], fun h => by simp_all [okDs, okO],
        fun l hl => by simp [labelsDs, labelsO, hl], fun h => ?_⟩
      rw [e0] at h; exact h.sublist (List.sublist_append_left _ _)
    · obtain ⟨i1, i2, i3, i4⟩ := dparts_mem (C := C) h'
      refine ⟨fun x hx => by simp [itemsDs, i1 x hx], fun h => i2 (by simp_all [okDs]), fun l hl => by simp [labelsDs, i3 l hl],
        fun h => i4 ?_⟩
      rw [e0] at h; exact h.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_right _ _))

theorem good_dict {C : List Scope} {U : Label → Prop} {l : Label} {kvs : List DItem}
    (hg : GoodE p C U (.dict l kvs)) {e : Expr} (he : e ∈ dparts kvs) : GoodE p C U e :=
  have hm := dparts_mem (C := C) he
  GoodE.of hg (fun x hx => by simpa [itemsE] using hm.1 x hx)
    (fun x hx => by
      simp only [trE, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        items_foldl, trKVs_eq, List.nil_append, List.mem_flatMap, List.mem_map]
      exact ⟨_, ⟨e, he, rfl⟩, hx⟩)
    (fun h => hm.2.1 (by simpa [okE] using h))
    (fun x hx => by simp [labelsE, hm.2.2.1 x hx])
    (fun h => hm.2.2.2 (by simp only [labelsE, List.nodup_cons] at h; exact h.2))
    (fun x hx => by simp only [touchE]; exact dparts_tch he hx)


theorem ev_dict_of (mk : EvsMk σ) (l kvs) : EvCase I p (.dict l kvs) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  cases kvs with
  | nil =>
    let r := sub l 0
    let g := "$op:display:dict:" ++ Py.starsStr []
    let o : Py.Op := .display (.dict [])
    let mkT (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ :=
      { t with stack := { f' with ctrl := c, kont := k } :: fs' }
    have p1 : Path (PyCore.step I) t (mkT (.op o []) f'.kont)
        [t, mkT (.ev (.const r g)) (.callF (.const r "$args") :: f'.kont),
          mkT (.val (.op o)) (.callF (.const r "$args") :: f'.kont),
          mkT (.ev (.const r "$args")) (.callA (.op o) :: f'.kont),
          mkT (.val (.data "$args" [])) (.callA (.op o) :: f'.kont)] := by
      refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))))
      · rw [pstep_ev A.ht hc']; simp [trE, trKVs, cc, ccR, recR, PyCore.evalStep, PyCore.top, mkT, r, g]
      · simp only [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, r, g, kc_dict I, o]
      · simp [mkT, PyCore.step, PyCore.valStep, PyCore.top]
      · simp [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
      · simp [mkT, PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.top, PyCore.argList]
    have e1 : Sem.step I s =
        some { s with stack := { f with ctrl := .val (.tuple []), kont := .evsEnd (.op o) :: f.kont } :: fs } := by
      simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC, o]
    refine goal_b (.cons e1 (.cons (by simp [Sem.step, Sem.valStep, Sem.finish, Sem.doOp, Sem.setC]) (.nil _)))
      (by simp) p1 (by simp) (crelI_seen (A.set .op hk)) (cover_of (l := l) (by simp) (touch_ev A hc) ?_)
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · simp [PyCore.focus, A.ht, hc', trE, trKVs, cc, ccR, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [mkT, PyCore.focus, PyCore.Expr.label, r] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [mkT, PyCore.focus] at hx
    · simp [mkT, PyCore.focus, PyCore.Expr.label, r] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · simp [mkT, PyCore.focus] at hx
  | cons d kvs' =>
    obtain ⟨e, rest, hd⟩ : ∃ e rest, dparts (d :: kvs') = e :: rest := by
      rcases d with ⟨_ | k, v⟩ <;> exact ⟨_, _, rfl⟩
    let st := (d :: kvs').map fun | DItem.mk k _ => k.isNone
    have hk1 := mk (x := cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) (acc := []) (o := .display (.dict st))
      (show Seen (Touch p) H [s] l from .inr ⟨s, by simp, touch_ev A hc⟩)
      (partR_some (l := l) fun e' he => good_dict hg (by rw [hd]; exact List.mem_cons_of_mem _ he)) (lift A hk)
    refine ev_cc A (l := l) (rest := trEs f.chain rest) (c := .ev e)
      (k := .evs (rest.map some) [] (.op (.display (.dict st))) :: f.kont)
      (touch_ev A hc) (by rw [hc']; simp only [trE, cc, trKVs_eq, hd, trEs_eq, List.map_cons]; rfl)
      (by
        simp only [Sem.step, A.hs, hc, Sem.evalStep]; erw [dflat_eq, hd]; simp [Sem.startEvs, Sem.setC, st]
        exact ⟨by cases d; rfl, fun a _ => by cases a; rfl⟩)
      (.ev (good_dict hg (by rw [hd]; exact List.mem_cons_self))) ?_
    rw [kc_dict I]; exact hk1


/-! ## Lists, tuples and sets

The items' values go into PyCore's record, then the items' markers (`starMark`, or for a set
`constMark 57`, which PyCore computes from the items' parts' markers), then the gadget
`$display:k` makes the display. -/

/-- PyCore evaluates `m` to `w` in the top frame `f'` (any continuation), every node it evaluates
in `P`. -/
def MEval (I : Py.Interp σ) (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ))
    (P : Label → Prop) (m : PE) (w : Val) : Prop :=
  ∀ K : List (PyCore.Kont σ), ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .ev m, kont := K } :: fs' }
    { t with stack := { f' with ctrl := .val w, kont := K } :: fs' } ys ∧ ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → P x

theorem MEval.mono {t : PyCore.Config σ} {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {P Q : Label → Prop}
    {m : PE} {w : Val} (h : MEval I t f' fs' P m w) (hpq : ∀ x, P x → Q x) : MEval I t f' fs' Q m w := fun K =>
  let ⟨ys, py, hy⟩ := h K; ⟨ys, py, fun y hy' x hx => hpq x (hy y hy' x hx)⟩

theorem meval_const (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) {r : Label}
    {k : String} (h : Py.constVal I k = .prim k) (h1 : k ≠ "$stop") (h2 : k ≠ "$any") :
    MEval I t f' fs' (· = r) (.const r k) (.prim k) := fun K =>
  ⟨_, .cons (by simp only [PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, h]; split <;> simp_all) (.nil _), by
    intro y hy x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; subst hy
    simp [PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm⟩

/-- PyCore evaluates the record's further items (`mws.map (·.1)`, to `mws.map (·.2)`) into it. -/
theorem rec_evals (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) {P : Label → Prop} :
    ∀ (mws : List (PE × Val)), (∀ mw ∈ mws, MEval I t f' fs' P mw.1 mw.2) → ∀ (done : List Val) (K : List (PyCore.Kont σ)),
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with ctrl := .val (.data "$args" done), kont := (mws.map (·.1)).map (.binL ",") ++ K } :: fs' }
      { t with stack := { f' with ctrl := .val (.data "$args" (done ++ mws.map (·.2))), kont := K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → P x
  | [], _, done, K => ⟨[], by simpa using Path.nil _, by simp⟩
  | (m, w) :: mws, hm, done, K => by
    let K1 : List (PyCore.Kont σ) := .binR "," (.data "$args" done) :: ((mws.map (·.1)).map (.binL ",") ++ K)
    obtain ⟨ys1, p1, hf1⟩ := hm (m, w) List.mem_cons_self K1
    obtain ⟨ys2, p2, hf2⟩ := rec_evals t f' fs' mws (fun mw h => hm mw (List.mem_cons_of_mem _ h)) (done ++ [w]) K
    have e : done ++ (List.map (·.2) ((m, w) :: mws)) = done ++ [w] ++ mws.map (·.2) := by simp
    rw [e]
    refine ⟨_ :: (ys1 ++ _ :: ys2), .cons ?_ (p1.append (.cons ?_ p2)), ?_⟩
    · simp [PyCore.step, PyCore.valStep, PyCore.top, K1]
    · simp [PyCore.step, PyCore.valStep, PyCore.top, K1]
    · intro y hy x hx
      simp only [List.mem_cons, List.mem_append] at hy
      rcases hy with rfl | hy | rfl | hy
      · simp [PyCore.focus] at hx
      · exact hf1 y hy x hx
      · simp [PyCore.focus] at hx
      · exact hf2 y hy x hx

theorem zip_mapM_fst (g : Val → Option Bool) : ∀ (ws vs : List Val), ws.length ≤ vs.length →
    (ws.zip vs).mapM (fun p => g p.1) = ws.mapM g
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | w :: ws, v :: vs, h => by
    simp only [List.zip_cons_cons, List.mapM_cons, zip_mapM_fst g ws vs (by simp at h; omega)]

theorem zip_all_fst (g : Val → Bool) : ∀ (ws vs : List Val), ws.length ≤ vs.length →
    (ws.zip vs).all (fun p => g p.1) = ws.all g
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | w :: ws, v :: vs, h => by
    simp only [List.zip_cons_cons, List.all_cons, zip_all_fst g ws vs (by simp at h; omega)]

/-- The display the gadget `$display:k` makes of `n` values whose markers are `ws`. -/
def dispOf (k : String) (n : Nat) (ws : List Val) (st : List Bool) : Py.Disp :=
  if k = "list" then .list st else if k = "tuple" then .tuple st
  else if n > 2 && ws.all Py.markConst then .constSet else .set st

/-- The gadget `$display:k` on the values `vs` and their markers `ws`. -/
theorem disp_step (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ))
    {k : String} (hk : NC k) {vs ws : List Val} (hl : ws.length = vs.length) {st : List Bool}
    (hst : ws.mapM Py.markStar = some st) :
    PyCore.step I { t with stack := { f' with
        ctrl := .val (.data "$args" (vs ++ ws)), kont := .callA (.prim (Py.Gadget.display k).name) :: K } :: fs' } =
      some { t with stack := { f' with ctrl := .op (.display (dispOf k vs.length ws st)) vs, kont := K } :: fs' } := by
  simp [PyCore.step, PyCore.valStep, PyCore.callStep, gad_name (.display k) hk, PyCore.gadgetStep, PyCore.argList,
    pairs_app hl, zip_mapM_fst _ ws vs (by omega), hst, zip_all_fst _ ws vs (by omega),
    List.map_snd_zip (l₁ := ws) (l₂ := vs) (by omega), PyCore.top, hl, dispOf]


theorem trA_cons (C : List Scope) (e : Expr) (es : List Expr) : trA C (e :: es) = trE C (unstar e) :: trA C es := by
  cases e <;> rfl

/-- A display's items (unstarred) at the display's budget. -/
theorem good_elt {C : List Scope} {U : Label → Prop} {E : Expr} {l : Label} {es : List Expr} {M : Expr → PE}
    {g : Py.Gadget} (hE : labelsE E = l :: labelsEs es) (hi : itemsE C E = itemsEs C es) (ho : okE E = okAs es)
    (ht : trE C E = gad l 0 g (trA C es ++ es.map M)) (htc : touchE E = touchEs es) (h : GoodE p C U E) {e : Expr}
    (he : e ∈ es) : GoodE p C U (unstar e) := by
  have hsub : ∀ x, x ∈ labelsE (unstar e) → x ∈ labelsE e := by
    intro x hx; cases e <;> simp_all [unstar, labelsE]
  have hnd : (labelsE E).Nodup := h.nd
  rw [hE, List.nodup_cons] at hnd
  refine ⟨fun x hx => h.s x ?_, fun x hx => h.t x ?_, ?_, fun l' hl' => h.u l' ?_, h.pv, ?_,
    fun x hx => h.tch x (by rw [htc]; exact touchEs_mem he (touch_unstar hx))⟩
  · have : x ∈ itemsE C e := by cases e <;> simp_all [unstar, itemsE]
    rw [hi]; exact itemsEs_mem he this
  · rw [ht]; simp only [gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false,
      List.nil_append]
    exact items_fold _ _ x (.inr ⟨_, List.mem_append_left _ (mem_trA he), hx⟩)
  · have := h.ok; rw [ho] at this; exact okAs_mem this he
  · rw [hE]; exact .tail _ (labelsEs_mem he (hsub _ hl'))
  · have h2 := nodup_labelsEs he hnd.2
    cases e <;> simp_all [unstar, labelsE, List.nodup_cons]

theorem partsR_disp {x : Cx} {U : Label → Prop} {l : Label} :
    ∀ {es : List Expr}, (∀ e ∈ es, GoodE x.p x.C U (unstar e)) →
      PartsR x U l (es.map fun e => some (unstar e)) (trA x.C es)
  | [], _ => trivial
  | e :: es, h => by
    rw [trA_cons]; exact ⟨⟨h e List.mem_cons_self, rfl⟩, partsR_disp fun e' he => h e' (List.mem_cons_of_mem _ he)⟩

theorem PartsR.ext {x x' : Cx} {U : Label → Prop} {l : Label} (hp : x.p = x'.p) (hC : x.C = x'.C) :
    ∀ {rest : List (Option Expr)} {ps : List PE}, PartsR x U l rest ps → PartsR x' U l rest ps
  | [], [], _ => trivial
  | some _ :: _, _ :: _, ⟨⟨hg, he⟩, hr⟩ => ⟨⟨hp ▸ hC ▸ hg, hC ▸ he⟩, PartsR.ext hp hC hr⟩
  | none :: _, _ :: _, ⟨h, hr⟩ => ⟨h, PartsR.ext hp hC hr⟩

/-- The elements of `es` up to the one after `n`, when the rest after `n` starts with `e0`. -/
theorem take_next {es : List Expr} {n : Nat} {e0 : Expr} {tl : List Expr} (hd : es.drop n = e0 :: tl) :
    es.take (n + 1) = es.take n ++ [e0] ∧ es.drop (n + 1) = tl ∧ n < es.length := by
  have hlen : n < es.length := by
    have := congrArg List.length hd; simp at this; omega
  have hsplit : es = es.take n ++ e0 :: tl := by rw [← hd]; exact (List.take_append_drop _ _).symm
  have hA : (es.take n).length = n := by simp; omega
  refine ⟨?_, ?_, hlen⟩
  · conv => lhs; rw [hsplit]
    rw [List.take_append, hA, List.take_of_length_le (by rw [hA]; omega)]; simp
  · conv => lhs; rw [hsplit]
    rw [List.drop_append, hA]; simp; omega

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- An item's value reaches the items of a display (`AccK.evsList`, `evsTuple`, `evsSet`): the display
`D` of the items `es` (node `l`), PyCore's gadget `g` and the items' markers `es.map M`, which read the
nodes `T e` of each item `e`; `mk` gives the entry at the next item. -/
theorem val_disp (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label} {es : List Expr}
    {rest : List (Option Expr)} {acc : List Val} {ps : List PE} {D : Py.Disp} {g : String} {M : Expr → PE}
    {T : Expr → Label → Prop} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs rest acc (.op (.display D)) :: K0)
    (hK' : f'.kont = recK acc.reverse (ps ++ es.map M) (.callA (.prim g) :: K0'))
    (hH : ∀ e ∈ es.take (acc.length + 1), ∀ c, T e c → H c)
    (hlink : rest = (es.drop (acc.length + 1)).map fun e => some (unstar e))
    (hlt : acc.length < es.length) (hr : PartsR A.x U l rest ps) (hk : KRel A.x U true K0 K0')
    (htouch : ∀ e0 ∈ es, ∀ c, T e0 c → ∀ (r : List (Option Expr)) (a : List Val),
      Touch p { s with stack := { f with ctrl := .ev (unstar e0), kont := .evs r a (.op (.display D)) :: K0 } :: fs } c)
    (hend : ∀ vs : List Val, vs.length = es.length → ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with ctrl := .val (.data "$args" vs), kont := (es.map M).map (.binL ",") ++ .callA (.prim g) :: K0' } :: fs' }
      { t with stack := { f' with ctrl := .op (.display D) vs, kont := K0' } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ e ∈ es, T e (x / 64))
    (mk : ∀ (H' : Label → Prop) (acc' : List Val) (rest' : List (Option Expr)) (ps' : List PE),
      (∀ e ∈ es.take (acc'.length + 1), ∀ c, T e c → H' c) →
      rest' = (es.drop (acc'.length + 1)).map (fun e => some (unstar e)) → acc'.length < es.length →
      PartsR (cx p H' (rdOf t f') (ownOf t f') f) U l rest' ps' →
      KRel (cx p H' (rdOf t f') (ownOf t f') f) U true K0 K0' →
      KRel (cx p H' (rdOf t f') (ownOf t f') f) U true (.evs rest' acc' (.op (.display D)) :: K0)
        (recK acc'.reverse (ps' ++ es.map M) (.callA (.prim g) :: K0'))) :
    Goal I p H s t := by
  match rest, ps, hr with
  | [], [], _ =>
    have hlen : es.length ≤ acc.length + 1 := by
      have := congrArg List.length hlink; simp at this; omega
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .val (.tuple (v :: acc).reverse), kont := .evsEnd (.op (.display D)) :: K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
    have e2 : Sem.step I { s with stack := { f with
        ctrl := .val (.tuple (v :: acc).reverse), kont := .evsEnd (.op (.display D)) :: K0 } :: fs } =
        some { s with stack := { f with ctrl := .op (.display D) (acc.reverse ++ [v]), kont := K0 } :: fs } := by
      simp [Sem.step, Sem.valStep, Sem.finish, Sem.doOp, Sem.setC]
    have st1 := pstep_rec (I := I) (done := acc.reverse) A.ht hc'
      (K1 := (es.map M).map (.binL ",") ++ .callA (.prim g) :: K0') (by rw [hK']; simp [recK])
    obtain ⟨ys, py, hfy⟩ := hend (acc.reverse ++ [v]) (by simp; omega)
    rw [List.reverse_cons] at e1 e2
    refine goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons st1 py) (by simp) (crelI_seen (A.set .op hk)) ?_
    intro y hy x hx
    have hx := pfocus_le hx
    rcases List.mem_cons.1 hy with rfl | hy
    · simp [PyCore.focus, A.ht, hc'] at hx
    · obtain ⟨e, he, hT⟩ := hfy y hy x hx
      exact .inl (hH e (by rw [List.take_of_length_le hlen]; exact he) _ hT)
  | some e :: rest', pe :: ps', ⟨⟨hge, hpe⟩, hr'⟩ =>
    subst hpe
    obtain ⟨e0, tl, hd, he0, hrest⟩ : ∃ e0 tl, es.drop (acc.length + 1) = e0 :: tl ∧ unstar e0 = e ∧
        rest' = tl.map (fun e => some (unstar e)) := by
      cases hd : es.drop (acc.length + 1) with
      | nil => rw [hd] at hlink; simp at hlink
      | cons e0 tl => rw [hd] at hlink; simp at hlink; exact ⟨e0, tl, rfl, hlink.1.symm, hlink.2⟩
    obtain ⟨htake, hdrop, hlt'⟩ := take_next hd
    let s1 : Sem.Config σ := { s with stack := { f with
      ctrl := .ev e, kont := .evs rest' (v :: acc) (.op (.display D)) :: K0 } :: fs }
    have e1 : Sem.step I s = some s1 := by simp [s1, Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
    let KR : List (PyCore.Kont σ) := recK (acc.reverse ++ [v]) (ps' ++ es.map M) (.callA (.prim g) :: K0')
    have st1 := pstep_rec (I := I) (done := acc.reverse) A.ht hc'
      (K1 := (trE A.x.C e :: ps' ++ es.map M).map (.binL ",") ++ .callA (.prim g) :: K0') (by rw [hK']; simp [recK])
    have st2 : PyCore.step I { t with stack := { f' with
        ctrl := .val (.data "$args" (acc.reverse ++ [v])),
        kont := (trE A.x.C e :: ps' ++ es.map M).map (.binL ",") ++ .callA (.prim g) :: K0' } :: fs' } =
        some { t with stack := { f' with ctrl := .ev (trE f.chain e), kont := KR } :: fs' } := by
      simp [PyCore.step, PyCore.valStep, PyCore.top, recK, KR]
    have hH' : ∀ l, H l → Seen (Touch p) H [s1, s] l := fun _ h => .inl h
    have hk1 := mk (Seen (Touch p) H [s1, s]) (v :: acc) rest' ps' ?_ (by rw [hrest, ← hdrop]; rfl) (by simpa using hlt')
      (PartsR.ext (x := A.x) (x' := cx p (Seen (Touch p) H [s1, s]) (rdOf t f') (ownOf t f') f) rfl rfl hr') (KRel.ext ⟨hH', Agree.refl _ _ _⟩ hk)
    · rw [List.reverse_cons] at hk1
      refine goal_t (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
        (.inl (((A.zero.upd (.ev e) (.evs rest' (v :: acc) (.op (.display D)) :: K0) (.ev (trE f.chain e)) KR).mono_H
          hH').crel (.ev hge) hk1)) (cover_none ?_)
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc']
    · intro e' he' c hT
      simp only [List.length_cons, htake, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact .inl (hH e' he' c hT)
      · have := htouch e' (List.mem_of_mem_drop (hd ▸ List.mem_cons_self)) c hT rest' (v :: acc)
        rw [he0] at this
        exact .inr ⟨s1, by simp, this⟩
  | none :: _, _, _ =>
    cases hd : es.drop (acc.length + 1) <;> rw [hd] at hlink <;> simp at hlink


/-- A display (node `l`) is entered: Surf evaluates its first item, PyCore enters its record (or, with
no item, both make the empty display). -/
theorem ev_disp (A : At p H s t f fs f' fs') {U : Label → Prop} {l : Label} {es : List Expr} {D : Py.Disp}
    {g : String} {M : Expr → PE} {T : Expr → Label → Prop} (hT : Touch p s l)
    (hst : Sem.step I s = Sem.startEvs s f fs (es.map fun e => some (unstar e)) [] (.op (.display D)) f.kont)
    (hc' : f'.ctrl = .ev (ccR (sub l 0) g (trA f.chain es ++ es.map M)))
    (hg : Py.constVal I g = .prim g) (hge : ∀ e ∈ es, GoodE p f.chain U (unstar e)) (hk : KRel A.x U true f.kont f'.kont)
    (htouch : ∀ e0 ∈ es, ∀ c, T e0 c → ∀ (r : List (Option Expr)) (a : List Val),
      Touch p { s with stack := { f with ctrl := .ev (unstar e0), kont := .evs r a (.op (.display D)) :: f.kont } :: fs } c)
    (hend : ∀ vs : List Val, vs.length = es.length → ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with
        ctrl := .val (.data "$args" vs), kont := (es.map M).map (.binL ",") ++ .callA (.prim g) :: f'.kont } :: fs' }
      { t with stack := { f' with ctrl := .op (.display D) vs, kont := f'.kont } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ e ∈ es, T e (x / 64))
    (mk : ∀ (H' : Label → Prop) (acc' : List Val) (rest' : List (Option Expr)) (ps' : List PE),
      (∀ e ∈ es.take (acc'.length + 1), ∀ c, T e c → H' c) →
      rest' = (es.drop (acc'.length + 1)).map (fun e => some (unstar e)) → acc'.length < es.length →
      PartsR (cx p H' (rdOf t f') (ownOf t f') f) U l rest' ps' →
      KRel (cx p H' (rdOf t f') (ownOf t f') f) U true f.kont f'.kont →
      KRel (cx p H' (rdOf t f') (ownOf t f') f) U true (.evs rest' acc' (.op (.display D)) :: f.kont)
        (recK acc'.reverse (ps' ++ es.map M) (.callA (.prim g) :: f'.kont))) :
    Goal I p H s t := by
  cases es with
  | nil =>
    let r := sub l 0
    let mkT (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ :=
      { t with stack := { f' with ctrl := c, kont := k } :: fs' }
    have p1 : Path (PyCore.step I) t (mkT (.val (.data "$args" [])) (.callA (.prim g) :: f'.kont))
        [t, mkT (.ev (.const r g)) (.callF (.const r "$args") :: f'.kont),
          mkT (.val (.prim g)) (.callF (.const r "$args") :: f'.kont),
          mkT (.ev (.const r "$args")) (.callA (.prim g) :: f'.kont)] := by
      refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _))))
      · rw [pstep_ev A.ht hc']; simp [trA, ccR, recR, PyCore.evalStep, PyCore.top, mkT, r]
      · simp [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, r, hg]
      · simp [mkT, PyCore.step, PyCore.valStep, PyCore.top]
      · simp [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
    obtain ⟨ys, py, hfy⟩ := hend [] rfl
    have e1 : Sem.step I s = some { s with stack := { f with
        ctrl := .val (.tuple []), kont := .evsEnd (.op (.display D)) :: f.kont } :: fs } := by
      rw [hst]; simp [Sem.startEvs, Sem.setC]
    refine goal_b (.cons e1 (.cons (by simp [Sem.step, Sem.valStep, Sem.finish, Sem.doOp, Sem.setC]) (.nil _)))
      (by simp) (p1.append py) (by simp) (crelI_seen (A.set .op hk)) ?_
    intro y hy x hx
    have hx := pfocus_le hx
    rcases List.mem_append.1 hy with hy | hy
    · refine .inr ⟨s, by simp, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · simp [PyCore.focus, A.ht, hc', ccR, PyCore.Expr.label] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hT
      · simp [mkT, PyCore.focus, PyCore.Expr.label, r] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hT
      · simp [mkT, PyCore.focus] at hx
      · simp [mkT, PyCore.focus, PyCore.Expr.label, r] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hT
    · obtain ⟨e, he, -⟩ := hfy y hy x hx; simp at he
  | cons e0 es' =>
    let s1 : Sem.Config σ := { s with stack := { f with
      ctrl := .ev (unstar e0), kont := .evs (es'.map fun e => some (unstar e)) [] (.op (.display D)) :: f.kont } :: fs }
    have e1 : Sem.step I s = some s1 := by rw [hst]; simp [s1, Sem.startEvs, Sem.setC]
    obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 0) g (trE f.chain (unstar e0))
      (trA f.chain es' ++ (e0 :: es').map M) f'.kont
    rw [t_eq A.ht (by rw [hc', trA_cons]; rfl) rfl, hg] at pc
    have hH' : ∀ l, H l → Seen (Touch p) H [s1, s] l := fun _ h => .inl h
    have hk1 := mk (Seen (Touch p) H [s1, s]) [] (es'.map fun e => some (unstar e)) (trA f.chain es') ?_ rfl (by simp)
      (partsR_disp (x := cx p (Seen (Touch p) H [s1, s]) (rdOf t f') (ownOf t f') f) fun e he =>
        hge e (List.mem_cons_of_mem _ he)) (KRel.ext ⟨hH', Agree.refl _ _ _⟩ hk)
    · refine goal_t (.cons e1 (.nil _)) (by simp) pc hys
        (.inl (((A.zero.upd _ _ (.ev (trE f.chain (unstar e0))) _).mono_H hH').crel (.ev (hge e0 List.mem_cons_self))
          hk1)) (cover_of (l := l) (by simp) hT fun y hy x hx => by rw [hfoc y hy x hx]; exact sub_div _ _ (by omega))
    · intro e he c hc
      simp only [List.length_nil, Nat.zero_add, List.take_succ_cons, List.take_zero, List.mem_singleton] at he
      subst he
      exact .inr ⟨s1, by simp, htouch e List.mem_cons_self c hc _ _⟩

end


/-! ### List and tuple displays -/

theorem star_mark (e : Expr) :
    starMark e = .const (sub (Sem.Expr.lbl e) 57) (if isStar e then "$star" else "$pos") := by
  cases e <;> simp [starMark, isStar, Sem.Expr.lbl, Expr.label]

/-- The markers of a list or tuple display, then its gadget. -/
theorem end_star (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ))
    {es : List Expr} {k : String} (hk : NC k) (vs : List Val) (hl : vs.length = es.length) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with
        ctrl := .val (.data "$args" vs), kont := (es.map starMark).map (.binL ",") ++ .callA (.prim (Py.Gadget.display k).name) :: K } :: fs' }
      { t with stack := { f' with
        ctrl := .op (.display (dispOf k vs.length ((es.map starMark).map pval) (es.map isStar))) vs, kont := K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ e ∈ es, x / 64 = Sem.Expr.lbl e := by
  let mws := es.map fun e => (starMark e, pval (starMark e))
  have hm : ∀ mw ∈ mws, MEval I t f' fs' (fun x => ∃ e ∈ es, x / 64 = Sem.Expr.lbl e) mw.1 mw.2 := by
    intro mw hmw
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmw
    have hc : Py.constVal I (if isStar e then "$star" else "$pos") = .prim (if isStar e then "$star" else "$pos") := by
      by_cases h : isStar e <;> simp [h, kc_star I, kc_pos I]
    simp only [star_mark e, pval]
    exact (meval_const t f' fs' hc (by split <;> decide) (by split <;> decide)).mono fun x hx =>
      ⟨e, he, by rw [hx]; exact sub_div _ _ (by omega)⟩
  obtain ⟨ys, py, hfy⟩ := rec_evals t f' fs' mws hm vs (.callA (.prim (Py.Gadget.display k).name) :: K)
  have e1 : mws.map (·.1) = es.map starMark := by simp [mws]
  have e2 : mws.map (·.2) = (es.map starMark).map pval := by simp [mws]
  rw [e1, e2] at py
  have hst : ((es.map starMark).map pval).mapM Py.markStar = some (es.map isStar) := by
    have := marks_star es; rwa [trMarks_eq] at this
  refine ⟨ys ++ [_], py.append (.cons (disp_step t f' fs' K hk (by simp [hl]) hst) (.nil _)), ?_⟩
  intro y hy x hx
  rcases List.mem_append.1 hy with hy | hy
  · exact hfy y hy x hx
  · simp at hy; subst hy; simp [PyCore.focus] at hx

/-- A starred item's node is touched when its operand is entered, an item's own node otherwise. -/
theorem touch_item {s : Sem.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)} (hs : s.stack = f :: fs)
    {e0 : Expr} (htch : ∀ ls a, e0 = .star ls a → (ls, a) ∈ touchB p)
    (hT : ∀ ls a, e0 = .star ls a → f.ctrl = .ev a → (ls, a) ∈ touchB p → TouchF p f ls)
    (hc : f.ctrl = .ev (unstar e0)) : Touch p s (Sem.Expr.lbl e0) := by
  cases e0 with
  | star ls a => exact .inr (by rw [hs]; exact hT ls a rfl hc (htch ls a rfl))
  | _ => exact .inl (by simp [Sem.focus, hs, hc, unstar])

/-- The star nodes of a display's items are touched with their operands. -/
theorem disp_lt {es : List Expr} {n : Nat} (h : n < es.length) : n < (partsDisp es).length := by
  simpa [partsDisp] using h

theorem lt_disp {es : List Expr} {n : Nat} (h : n < (partsDisp es).length) : n < es.length := by
  simpa [partsDisp] using h

theorem disp_rest {es : List Expr} {n : Nat} {rest : List (Option Expr)}
    (h : rest = (es.drop n).map fun e => some (unstar e)) : rest = (partsDisp es).drop n := by
  rw [h, partsDisp, List.map_drop]

theorem rest_disp {es : List Expr} {n : Nat} {rest : List (Option Expr)}
    (h : rest = (partsDisp es).drop n) : rest = (es.drop n).map fun e => some (unstar e) := by
  rw [h, partsDisp, List.map_drop]

def TchOk (p : List Stmt) : Prop := ∀ (C : List Scope) (U : Label → Prop) (E : Expr), GoodE p C U E → SubL (touchE E) (touchB p)

theorem star_touchEs {ls : Label} {a : Expr} : ∀ {es : List Expr}, Expr.star ls a ∈ es → (ls, a) ∈ touchEs es
  | e :: es, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [touchEs, touchE]
    · simp [touchEs, star_touchEs h]



/-- An item of a list or tuple display (`D`) is entered: its node is touched. -/
theorem touch_lt {es : List Expr} {D : Py.Disp} (hD : ∃ st, D = .list st ∨ D = .tuple st)
    (hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p) {s : Sem.Config σ} {f : Sem.Frame σ}
    {fs : List (Sem.Frame σ)} {K : List (Sem.Kont σ)} :
    ∀ e0 ∈ es, ∀ c, c = Sem.Expr.lbl e0 → ∀ (r : List (Option Expr)) (a : List Val),
      Touch p { s with stack := { f with ctrl := .ev (unstar e0), kont := .evs r a (.op (.display D)) :: K } :: fs } c := by
  intro e0 he0 c hc r a; subst hc
  obtain ⟨st, hD | hD⟩ := hD <;> subst hD <;>
    exact touch_item rfl (fun ls a' h => hstar ls a' (h ▸ he0)) (fun _ _ h _ hm => by subst h; simpa [TouchF, unstar] using hm) rfl

theorem end_list (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ))
    {es : List Expr} (vs : List Val) (hl : vs.length = es.length) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with
        ctrl := .val (.data "$args" vs), kont := (es.map starMark).map (.binL ",") ++ .callA (.prim (Py.Gadget.display "list").name) :: K } :: fs' }
      { t with stack := { f' with ctrl := .op (.display (.list (es.map isStar))) vs, kont := K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ e ∈ es, (fun e c => c = Sem.Expr.lbl e) e (x / 64) := by
  obtain ⟨ys, py, hfy⟩ := end_star (I := I) t f' fs' K (k := "list") (by simp [NC]) vs hl
  simp only [dispOf, ↓reduceIte] at py
  exact ⟨ys, py, hfy⟩

theorem end_tuple (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ))
    {es : List Expr} (vs : List Val) (hl : vs.length = es.length) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with
        ctrl := .val (.data "$args" vs), kont := (es.map starMark).map (.binL ",") ++ .callA (.prim (Py.Gadget.display "tuple").name) :: K } :: fs' }
      { t with stack := { f' with ctrl := .op (.display (.tuple (es.map isStar))) vs, kont := K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ e ∈ es, (fun e c => c = Sem.Expr.lbl e) e (x / 64) := by
  obtain ⟨ys, py, hfy⟩ := end_star (I := I) t f' fs' K (k := "tuple") (by simp [NC]) vs hl
  have : dispOf "tuple" vs.length ((es.map starMark).map pval) (es.map isStar) = .tuple (es.map isStar) := by
    simp [dispOf]
  rw [this] at py
  exact ⟨ys, py, hfy⟩

theorem ev_list_of (htch : TchOk p) (l es) : EvCase I p (.list l es) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p :=
    fun ls a h => htch _ _ _ hg _ (by simpa [touchE] using star_touchEs h)
  exact ev_disp A (D := .list (es.map isStar)) (g := (Py.Gadget.display "list").name) (M := starMark)
    (T := fun e c => c = Sem.Expr.lbl e) (touch_ev A hc) (by simp only [Sem.step, A.hs, hc, Sem.evalStep]) (by rw [hc']; rfl)
    (kc_gad I (.display "list") (by simp [GOk, NC])) (fun e he => good_elt rfl rfl rfl rfl rfl hg he) hk
    (touch_lt ⟨_, .inl rfl⟩ hstar) (end_list t f' fs' f'.kont)
    (fun _ _ _ _ hH' h1 h2 hr' k' => .acc (.evsList hg (disp_lt h2) (disp_rest h1) (fun e he => hH' e he _ rfl) hr' k'))

theorem ev_tuple_of (htch : TchOk p) (l es) : EvCase I p (.tuple l es) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p :=
    fun ls a h => htch _ _ _ hg _ (by simpa [touchE] using star_touchEs h)
  exact ev_disp A (D := .tuple (es.map isStar)) (g := (Py.Gadget.display "tuple").name) (M := starMark)
    (T := fun e c => c = Sem.Expr.lbl e) (touch_ev A hc) (by simp only [Sem.step, A.hs, hc, Sem.evalStep]) (by rw [hc']; rfl)
    (kc_gad I (.display "tuple") (by simp [GOk, NC])) (fun e he => good_elt rfl rfl rfl rfl rfl hg he) hk
    (touch_lt ⟨_, .inr rfl⟩ hstar) (end_tuple t f' fs' f'.kont)
    (fun _ _ _ _ hH' h1 h2 hr' k' => .acc (.evsTuple hg (disp_lt h2) (disp_rest h1) (fun e he => hH' e he _ rfl) hr' k'))


end


/-! ### Set displays

A set item's marker (`constMark 57`) is computed by the core from its parts' markers: `cmv` is its
value. -/

mutual
/-- The value of a set item's constness marker. -/
def cmv : Expr → Val
  | .const .. => .prim "$c0"
  | .unary _ op a => .prim (match cmv a with
      | .prim "$c0" => if op == "USub" || op == "UAdd" || op == "Invert" then "$c1" else "$nc"
      | _ => "$nc")
  | .tuple _ es => .prim (if (cmvs es).all Py.markConst then "$c1" else "$nc")
  | .star .. => .prim "$star"
  | _ => .prim "$nc"
def cmvs : List Expr → List Val
  | [] => []
  | e :: es => cmv e :: cmvs es
end

theorem cmvs_eq : ∀ es : List Expr, cmvs es = es.map cmv
  | [] => rfl
  | e :: es => by simp [cmvs, cmvs_eq es]

theorem constMarks_eq : ∀ es : List Expr, constMarks es = es.map (constMark 50)
  | [] => rfl
  | e :: es => by simp [constMarks, constMarks_eq es]

theorem constNodesL_mem {e : Expr} {c : Label} : ∀ {es : List Expr}, e ∈ es → c ∈ constNodes e → c ∈ constNodesL es
  | a :: es, h, hc => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [constNodesL, hc]
    · simp [constNodesL, constNodesL_mem h hc]

theorem okAs_or {e : Expr} : ∀ {es : List Expr}, okAs es = true → e ∈ es → okE e = true ∨ isStar e = true
  | a :: es, ho, h => by
    have ho' : (isStar a = true ∨ okE a = true) ∧ okAs es = true := by
      cases a <;> simp_all [okAs, isStar]
    rcases List.mem_cons.1 h with rfl | h
    · exact ho'.1.symm
    · exact okAs_or ho'.2 h

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore enters the call `ccR r g ms` up to its empty record, the items `ms` and the call waiting. -/
theorem cc_enter0 (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (r : Label) (g : String)
    (ms : List PE) (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .ev (ccR r g ms), kont := K } :: fs' }
      { t with stack := { f' with
        ctrl := .val (.data "$args" []), kont := ms.map (.binL ",") ++ .callA (Py.constVal I g) :: K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = r := by
  obtain ⟨ys, py, hy⟩ := rec_path (I := I) t f' fs' r ms (.const r "$args") (.callA (Py.constVal I g) :: K)
  let c0 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (ccR r g ms), kont := K } :: fs' }
  let c1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const r g), kont := .callF (recR r ms) :: K } :: fs' }
  let c2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (Py.constVal I g), kont := .callF (recR r ms) :: K } :: fs' }
  let c5 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .ev (.const r "$args"), kont := ms.map (.binL ",") ++ .callA (Py.constVal I g) :: K } :: fs' }
  refine ⟨c0 :: c1 :: c2 :: ys ++ [c5], ?_, ?_⟩
  · let c3 : PyCore.Config σ := { t with stack := { f' with
        ctrl := .ev (ms.foldl (fun acc e => .bin r "," acc e) (.const r "$args")),
        kont := .callA (Py.constVal I g) :: K } :: fs' }
    refine .cons (a' := c1) (by simp [c1, ccR, PyCore.step, PyCore.evalStep, PyCore.top])
      (.cons (a' := c2) ?_ (.cons (a' := c3) ?_ ?_))
    · simp [c1, c2, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK]
    · simp [c2, c3, PyCore.step, PyCore.valStep, PyCore.top, recR]
    · let c6 : PyCore.Config σ := { t with stack := { f' with
        ctrl := .val (.data "$args" []), kont := ms.map (.binL ",") ++ .callA (Py.constVal I g) :: K } :: fs' }
      exact py.append (.cons (a' := c6) (by
        simp [c6, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]; split <;> simp_all) (.nil _))
  · intro y hy' x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy'
    rcases hy' with (rfl | rfl | rfl | hy') | rfl
    · simp [c0, PyCore.focus, ccR, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c1, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c2, PyCore.focus] at hx
    · exact hy y hy' x hx
    · simp [c5, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm

/-- A gadget's call on items that PyCore evaluates (`MEval`), the gadget giving `res`. -/
theorem meval_gad (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) {P : Label → Prop}
    {r : Label} {g : String} (mws : List (PE × Val)) (hP : P r) (hg : Py.constVal I g = .prim g)
    (hm : ∀ mw ∈ mws, MEval I t f' fs' P mw.1 mw.2) {res : Val}
    (hres : ∀ K : List (PyCore.Kont σ), PyCore.step I { t with stack := { f' with
      ctrl := .val (.data "$args" (mws.map (·.2))), kont := .callA (.prim g) :: K } :: fs' } =
      some { t with stack := { f' with ctrl := .val res, kont := K } :: fs' }) :
    MEval I t f' fs' P (ccR r g (mws.map (·.1))) res := by
  intro K
  obtain ⟨ys1, p1, h1⟩ := cc_enter0 (I := I) t f' fs' r g (mws.map (·.1)) K
  rw [hg] at p1
  obtain ⟨ys2, p2, h2⟩ := rec_evals t f' fs' mws hm [] (.callA (.prim g) :: K)
  rw [List.nil_append] at p2
  refine ⟨ys1 ++ ys2 ++ [_], (p1.append p2).append (.cons (hres K) (.nil _)), ?_⟩
  intro y hy x hx
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with (hy | hy) | rfl
  · rw [h1 y hy x hx]; exact hP
  · exact h2 y hy x hx
  · simp [PyCore.focus] at hx

theorem meval_cm (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) :
    ∀ (e : Expr), (okE e = true ∨ isStar e = true) → ∀ k, k < 64 →
      MEval I t f' fs' (fun x => x / 64 ∈ constNodes e) (constMark k e) (cmv e) := by
  suffices h : ∀ n (e : Expr), sizeOf e < n → (okE e = true ∨ isStar e = true) → ∀ k, k < 64 →
      MEval I t f' fs' (fun x => x / 64 ∈ constNodes e) (constMark k e) (cmv e) from
    fun e => h _ e (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro e h; omega
  | succ n ih =>
    intro e hs hok k hk
    have hc : ∀ {c : String}, Py.constVal I c = .prim c → c ≠ "$stop" → c ≠ "$any" →
        Sem.Expr.lbl e ∈ constNodes e → ∀ (r : Label), r / 64 = Sem.Expr.lbl e →
        MEval I t f' fs' (fun x => x / 64 ∈ constNodes e) (.const r c) (.prim c) := fun hv h1 h2 hm r hr =>
      (meval_const t f' fs' hv h1 h2).mono fun x hx => by rw [hx, hr]; exact hm
    cases e
    case const l c =>
      exact hc (kc_c0 I) (by decide) (by decide) (by simp [constNodes]) _ (sub_div _ _ hk)
    case star l a =>
      exact hc (kc_star I) (by decide) (by decide) (by simp [constNodes]) _ (sub_div _ _ hk)
    case unary l op a =>
      have hok' : okName op = true ∧ okE a = true := by simpa [okE, isStar] using hok
      have ha := ih a (by simp at hs; omega) (.inl hok'.2) 50 (by omega)
      have := meval_gad (I := I) t f' fs' (P := fun x => x / 64 ∈ constNodes (.unary l op a)) (r := sub l k)
        [(constMark 50 a, cmv a)] (by simp [constNodes, sub_div _ _ hk]) (kc_gad I (.cunary op) (nc_ok hok'.1))
        (by simpa using ha.mono fun x hx => by simp [constNodes, hx])
        (res := cmv (.unary l op a)) (fun K => by
          simp [PyCore.step, PyCore.valStep, PyCore.callStep, gad_name (.cunary op) (nc_ok hok'.1), PyCore.gadgetStep,
            PyCore.argList, PyCore.top, cmv]
          generalize cmv a = m
          cases m with
          | prim c => by_cases h : c = "$c0" <;> simp [h]
          | _ => rfl)
      simpa [constMark] using this
    case tuple l es =>
      have hok' : okAs es = true := by simpa [okE, isStar] using hok
      have := meval_gad (I := I) t f' fs' (P := fun x => x / 64 ∈ constNodes (.tuple l es)) (r := sub l k)
        (es.map fun e => (constMark 50 e, cmv e)) (by simp [constNodes, sub_div _ _ hk]) (kc_gad I .ctuple trivial)
        (by
          intro mw hmw
          obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmw
          have hse : sizeOf e < n := by
            have := List.sizeOf_lt_of_mem he; simp at hs; omega
          exact (ih e hse (okAs_or hok' he) 50 (by omega)).mono fun x hx => by
            simp [constNodes, constNodesL_mem he hx])
        (res := cmv (.tuple l es)) (fun K => by
          simp [PyCore.step, PyCore.valStep, PyCore.callStep, gad_name .ctuple trivial, PyCore.gadgetStep,
            PyCore.argList, PyCore.top, cmv, cmvs_eq])
      have e1 : (es.map fun e => (constMark 50 e, cmv e)).map (·.1) = es.map (constMark 50) := by
        clear this; induction es <;> simp_all
      rw [e1] at this
      simpa [constMark, constMarks_eq] using this
    all_goals exact hc (kc_nc I) (by decide) (by decide) (by simp [constNodes]) _ (by rw [sub_div _ _ hk]; rfl)

end


/-- Whether a value is the marker of a constant. -/
def isC0 : Val → Bool
  | .prim "$c0" => true
  | _ => false

/-- The core's `cunary` on a marker `m`. -/
theorem beq_c0 (op : String) (m : Val) :
    (match m with
      | .prim "$c0" => if op == "USub" || op == "UAdd" || op == "Invert" then "$c1" else "$nc"
      | _ => "$nc") = if (op == "USub" || op == "UAdd" || op == "Invert") && isC0 m then "$c1" else "$nc" := by
  cases m with
  | prim c =>
    by_cases h : c = "$c0"
    · subst h; simp [isC0]
    · simp [isC0, h]
  | _ => simp [isC0]

theorem markStar_if (b : Bool) : Py.markStar (.prim (if b then "$c1" else "$nc")) = some false := by
  cases b <;> rfl

theorem cmv_star (e : Expr) : Py.markStar (cmv e) = some (isStar e) := by
  cases e <;> first | (simp only [cmv, beq_c0, markStar_if] <;> rfl) | simp [cmv, isStar, Py.markStar]

theorem cmvs_star : ∀ es : List Expr, (es.map cmv).mapM Py.markStar = some (es.map isStar)
  | [] => rfl
  | e :: es => by simp [List.mapM_cons, cmv_star e, cmvs_star es]


theorem markConst_if (b : Bool) : Py.markConst (.prim (if b then "$c1" else "$nc")) = b := by
  cases b <;> rfl

theorem isC0_if (b : Bool) : isC0 (.prim (if b then "$c1" else "$nc")) = false := by
  cases b <;> rfl

theorem isC0_cmv (a : Expr) : isC0 (cmv a) = (match a with | .const .. => true | _ => false) := by
  cases a <;> first | (simp only [cmv, beq_c0, isC0_if] <;> rfl) | simp [cmv, isC0]

theorem cmv_const : ∀ e : Expr, Py.markConst (cmv e) = isConstE e := by
  suffices h : ∀ n (e : Expr), sizeOf e < n → Py.markConst (cmv e) = isConstE e from fun e => h _ e (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro e h; omega
  | succ n ih =>
    intro e hs
    cases e
    case unary l op a =>
      simp only [cmv, beq_c0, markConst_if, isC0_cmv]
      cases a <;> simp [isConstE]
    case tuple l es =>
      simp only [cmv, markConst_if, cmvs_eq, List.all_map]
      have : ∀ e ∈ es, Py.markConst (cmv e) = isConstE e := fun e he =>
        ih e (by have := List.sizeOf_lt_of_mem he; simp at hs; omega)
      simp [isConstE]
      clear ih hs
      induction es with
      | nil => rfl
      | cons e es ihs => simp [List.all_cons, this e List.mem_cons_self, ihs fun e' he' => this e' (List.mem_cons_of_mem _ he')]
    all_goals simp [cmv, isConstE, Py.markConst]

theorem setOwners_eq (e : Expr) : setOwners e = constNodes e := by
  cases e <;> simp [setOwners, constNodes, Sem.Expr.lbl]

/-- The markers of a set display, then its gadget. -/
theorem end_set (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (K : List (PyCore.Kont σ))
    {es : List Expr} (hok : ∀ e ∈ es, okE e = true ∨ isStar e = true) (vs : List Val) (hl : vs.length = es.length) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with
        ctrl := .val (.data "$args" vs),
        kont := (es.map (constMark 57)).map (.binL ",") ++ .callA (.prim (Py.Gadget.display "set").name) :: K } :: fs' }
      { t with stack := { f' with
        ctrl := .op (.display (if es.length > 2 && es.all isConstE then .constSet else .set (es.map isStar))) vs,
        kont := K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ e ∈ es, (fun e c => c ∈ setOwners e) e (x / 64) := by
  let mws := es.map fun e => (constMark 57 e, cmv e)
  have hm : ∀ mw ∈ mws, MEval I t f' fs' (fun x => ∃ e ∈ es, x / 64 ∈ setOwners e) mw.1 mw.2 := by
    intro mw hmw
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hmw
    exact (meval_cm t f' fs' e (hok e he) 57 (by omega)).mono fun x hx => ⟨e, he, by rw [setOwners_eq]; exact hx⟩
  obtain ⟨ys, py, hfy⟩ := rec_evals t f' fs' mws hm vs (.callA (.prim (Py.Gadget.display "set").name) :: K)
  have e1 : mws.map (·.1) = es.map (constMark 57) := by simp [mws]
  have e2 : mws.map (·.2) = es.map cmv := by simp [mws]
  rw [e1, e2] at py
  have hd : dispOf "set" vs.length (es.map cmv) (es.map isStar) =
      (if es.length > 2 && es.all isConstE then .constSet else .set (es.map isStar)) := by
    have : (es.map cmv).all Py.markConst = es.all isConstE := by
      simp only [List.all_map]; congr 1; funext e; exact cmv_const e
    simp [dispOf, hl, this]
  refine ⟨ys ++ [_], py.append (.cons ((disp_step t f' fs' K (by simp [NC]) (by simp [hl]) (cmvs_star es)).trans
    (by rw [hd])) (.nil _)), ?_⟩
  intro y hy x hx
  rcases List.mem_append.1 hy with hy | hy
  · exact hfy y hy x hx
  · simp at hy; subst hy; simp [PyCore.focus] at hx

/-- An item of a set display is entered: the nodes its marker reads are touched. -/
theorem touch_set {es : List Expr} {D : Py.Disp}
    (hD : D = if es.length > 2 && es.all isConstE then .constSet else .set (es.map isStar))
    (hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p) {s : Sem.Config σ} {f : Sem.Frame σ}
    {fs : List (Sem.Frame σ)} {K : List (Sem.Kont σ)} :
    ∀ e0 ∈ es, ∀ c, c ∈ setOwners e0 → ∀ (r : List (Option Expr)) (a : List Val),
      Touch p { s with stack := { f with ctrl := .ev (unstar e0), kont := .evs r a (.op (.display D)) :: K } :: fs } c := by
  intro e0 he0 c hc r a
  have key : (c, unstar e0) ∈ touchB p ∨ c ∈ constNodes (unstar e0) := by
    cases e0 with
    | star ls a' => simp [setOwners] at hc; exact .inl (by rw [hc]; exact hstar ls a' he0)
    | _ => exact .inr (by simpa [setOwners, unstar] using hc)
  refine .inr ?_
  show TouchF p { f with ctrl := .ev (unstar e0), kont := .evs r a (.op (.display D)) :: K } c
  subst hD
  split <;> exact key


theorem ev_set_of (htch : TchOk p) (l es) : EvCase I p (.set l es) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p :=
    fun ls a h => htch _ _ _ hg _ (by simpa [touchE] using star_touchEs h)
  have hok : ∀ e ∈ es, okE e = true ∨ isStar e = true := fun e he => okAs_or (by simpa [okE] using hg.ok) he
  exact ev_disp A (D := if es.length > 2 && es.all isConstE then .constSet else .set (es.map isStar))
    (g := (Py.Gadget.display "set").name) (M := constMark 57) (T := fun e c => c ∈ setOwners e) (touch_ev A hc)
    (by simp only [Sem.step, A.hs, hc, Sem.evalStep]) (by rw [hc']; rfl)
    (kc_gad I (.display "set") (by simp [GOk, NC])) (fun e he => good_elt rfl rfl rfl rfl rfl hg he) hk
    (touch_set rfl hstar) (end_set t f' fs' f'.kont hok)
    (fun _ _ _ _ hH' h1 h2 hr' k' => .acc (.evsSet hg (disp_lt h2) (disp_rest h1) hH' hr' k'))

/-- The touches of an expression of the program are the program's. -/
theorem goodE_tch : TchOk p := fun _ _ _ h => h.tch

theorem val_acc : KCase I p true AccK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | unK k => exact val_recOp A hc' (done := []) hK' (.cons (by sstep1) (.nil _)) (by simp) k
  | attrK k => exact val_recOp A hc' (done := []) hK' (.cons (by sstep1) (.nil _)) (by simp) k
  | subR k => exact val_recOp A hc' hK' (.cons (by sstep1) (.nil _)) (by simp) k
  | fmtS k => exact val_recOp A hc' hK' (.cons (by sstep1) (.nil _)) (by simp) k
  | subL g k => exact val_recNext A hc' (done := []) hK' (.cons (by sstep1) (.nil _)) (by simp) (.ev g) (.acc (.subR k))
  | fmtC g k => exact val_fmtC A (by rw [s_eq A.hs hc hK]; exact .nil _) hc' hK' g k
  | @fmtV _ K0 K0' c spec g k =>
    by_cases hc1 : c = -1
    · subst hc1
      simp only [↓reduceIte] at hK'
      exact val_fmtC A (.cons (by sstep1) (.nil _)) hc' hK' g k
    · simp only [hc1, ↓reduceIte] at hK'
      exact val_recOp A hc' (done := []) hK'
        (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.doOp, hc1]) (.nil _)) (by simp) (.acc (.fmtC g k))
  | evsOp hH hr k => exact val_evs (fun h1 h2 k => .acc (.evsOp h1 h2 k)) A hc hc' hK hK' hH hr k
  | @evsList _ K0 K0' l es rest acc ps hg hlt hrest hH hr k =>
    have hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p :=
      fun ls a h => goodE_tch _ _ _ hg _ (by simpa [touchE] using star_touchEs h)
    exact val_disp A (D := .list (es.map isStar)) (g := (Py.Gadget.display "list").name) (M := starMark)
      (T := fun e c => c = Sem.Expr.lbl e) hc hc' hK hK' (fun e he c hc => hc ▸ hH e he)
      (rest_disp hrest) (lt_disp hlt) hr k (touch_lt ⟨_, .inl rfl⟩ hstar) (end_list t f' fs' K0')
      (fun _ _ _ _ hH' h1 h2 hr' k' => .acc (.evsList hg (disp_lt h2) (disp_rest h1) (fun e he => hH' e he _ rfl) hr' k'))
  | @evsTuple _ K0 K0' l es rest acc ps hg hlt hrest hH hr k =>
    have hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p :=
      fun ls a h => goodE_tch _ _ _ hg _ (by simpa [touchE] using star_touchEs h)
    exact val_disp A (D := .tuple (es.map isStar)) (g := (Py.Gadget.display "tuple").name) (M := starMark)
      (T := fun e c => c = Sem.Expr.lbl e) hc hc' hK hK' (fun e he c hc => hc ▸ hH e he)
      (rest_disp hrest) (lt_disp hlt) hr k (touch_lt ⟨_, .inr rfl⟩ hstar) (end_tuple t f' fs' K0')
      (fun _ _ _ _ hH' h1 h2 hr' k' => .acc (.evsTuple hg (disp_lt h2) (disp_rest h1) (fun e he => hH' e he _ rfl) hr' k'))
  | @evsSet _ K0 K0' l es rest acc ps hg hlt hrest hH hr k =>
    have hstar : ∀ ls a, Expr.star ls a ∈ es → (ls, a) ∈ touchB p :=
      fun ls a h => goodE_tch _ _ _ hg _ (by simpa [touchE] using star_touchEs h)
    have hok : ∀ e ∈ es, okE e = true ∨ isStar e = true := fun e he => okAs_or (by simpa [okE] using hg.ok) he
    exact val_disp A (D := if es.length > 2 && es.all isConstE then .constSet else .set (es.map isStar))
      (g := (Py.Gadget.display "set").name) (M := constMark 57) (T := fun e c => c ∈ setOwners e) hc hc' hK hK' hH
      (rest_disp hrest) (lt_disp hlt) hr k (touch_set rfl hstar) (end_set t f' fs' K0' hok)
      (fun _ _ _ _ hH' h1 h2 hr' k' => .acc (.evsSet hg (disp_lt h2) (disp_rest h1) hH' hr' k'))

/-- A signal passes an item of `AccK`. -/
theorem sig_item {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ}
    {fs : List (Sem.Frame σ)} {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} (A : At p H s t f fs f' fs')
    {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ} (hcr : CR p f.chain U true c c')
    (hsig : (∃ v, c' = .raise v) ∨ (∃ v, c' = .retv v) ∨ c' = .brk ∨ c' = .cont) (hc' : f'.ctrl = c')
    (e1 : ∀ k K, f.kont = k :: K → SPl k → Sem.step I s = some { s with stack := { f with ctrl := c, kont := K } :: fs })
    (hk : AccK A.x U i f.kont f'.kont) : Goal I p H s t := by
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  have e1 := fun k K h => e1 k K (hK.trans h)
  cases hk with
  | unK k => exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | attrK k => exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | subL _ k => exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | subR k => exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | fmtS k => exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | evsOp _ _ k => exact sig_evs A hcr hsig hc' (e1 _ _ rfl trivial) hK' k
  | evsList _ _ _ _ _ k =>
    exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | evsTuple _ _ _ _ _ k =>
    exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | evsSet _ _ _ _ _ k =>
    exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK', recK_app]) (recK_plain _ _ _) recK_ne k
  | @fmtC _ K0 K0' spec _ k =>
    cases spec <;>
      exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK']; exact recK_app ..) (recK_plain _ _ _) recK_ne k
  | @fmtV _ K0 K0' cv spec _ k =>
    by_cases hc1 : cv = -1
    · subst hc1; simp only [↓reduceIte] at hK'
      cases spec <;>
        exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial) (by rw [hK']; exact recK_app ..) (recK_plain _ _ _) recK_ne k
    · simp only [hc1, ↓reduceIte] at hK'
      cases spec <;>
        exact acc_sig_pop A _ hcr hsig hc' (e1 _ _ rfl trivial)
          (by rw [hK', recK_app, List.append_assoc]; congr 1; exact recK_app ..)
          (fun k hk => (List.mem_append.1 hk).elim (recK_plain _ _ _ k) (recK_plain _ _ _ k)) (by simp [recK]) k

theorem AccK.idx {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (h : AccK x U i K K') : i = true := by cases h <;> rfl

theorem sig_acc {i : Bool} : KCase I p i AccK CSig := by
  intro H s t f fs f' fs' U A W hc hk
  have hi := AccK.idx hk
  refine sig_item A (csig_cr hc (fun h => by rw [hi] at h; cases h) U) ?_ rfl (fun k K hK hp => ?_) hk
  · rcases hc with ⟨v, -, h⟩ | ⟨v, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> simp [h]
  · rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ <;> cases k <;> simp [SPl] at hp <;>
      simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC]

/-! ## The expressions' cases -/

theorem ev_list (l es) : EvCase I p (.list l es) := ev_list_of goodE_tch l es
theorem ev_tuple (l es) : EvCase I p (.tuple l es) := ev_tuple_of goodE_tch l es
theorem ev_set (l es) : EvCase I p (.set l es) := ev_set_of goodE_tch l es
theorem ev_dict (l kvs) : EvCase I p (.dict l kvs) := ev_dict_of (fun h1 h2 k => .acc (.evsOp h1 h2 k)) l kvs

theorem ev_slice (l a b c) : EvCase I p (.slice l a b c) := ev_slice_of (fun h1 h2 k => .acc (.evsOp h1 h2 k)) l a b c
theorem ev_fstr (l es) : EvCase I p (.fstr l es) := ev_fstr_of (fun h1 h2 k => .acc (.evsOp h1 h2 k)) l es

end Access

theorem ev_unary (l op a) : EvCase I p (.unary l op a) := Access.ev_unary l op a
theorem ev_attr (l e a) : EvCase I p (.attr l e a) := Access.ev_attr l e a
theorem ev_sub (l e i) : EvCase I p (.sub l e i) := Access.ev_sub l e i
theorem ev_slice (l a b c) : EvCase I p (.slice l a b c) := Access.ev_slice l a b c
theorem ev_list (l es) : EvCase I p (.list l es) := Access.ev_list l es
theorem ev_tuple (l es) : EvCase I p (.tuple l es) := Access.ev_tuple l es
theorem ev_set (l es) : EvCase I p (.set l es) := Access.ev_set l es
theorem ev_dict (l kvs) : EvCase I p (.dict l kvs) := Access.ev_dict l kvs
theorem ev_fstr (l es) : EvCase I p (.fstr l es) := Access.ev_fstr l es
theorem ev_fmt (l e c s) : EvCase I p (.fmt l e c s) := Access.ev_fmt l e c s
theorem val_acc : KCase I p true AccK CVal := Access.val_acc
theorem sig_acc {i : Bool} : KCase I p i AccK CSig := Access.sig_acc

end Surf.T2
