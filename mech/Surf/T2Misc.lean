/-
(T2), chained comparisons, `yield from`, `raise` (`from`, bare), imports, `assert`, bare `except`,
and the footprint's labels. The helper lemmas are in `Surf.T2.Misc`; the cases `T2.lean` calls keep
their names in `Surf.T2`: `ev_compare`, `ev_yieldFrom`, `exec_raise`, `exec_assert`, `exec_imp`,
`exec_impFrom`, `raise_bare`, `resume_yf`, `inF_labels`, `val_misc`, `done_misc`, `sig_misc`.
-/
import Surf.T2Cases

namespace Surf.T2
open PyCore (Name Label)
open Py (Val Gadget)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

namespace Misc

/-! ## Constant facts -/

section ConstFacts
theorem cv_reraise (I : Py.Interp σ) : Py.constVal I Gadget.reraise.name = .prim Gadget.reraise.name :=
  kc_gad I .reraise trivial
theorem cv_raiseFrom (I : Py.Interp σ) : Py.constVal I Gadget.raiseFrom.name = .prim Gadget.raiseFrom.name :=
  kc_gad I .raiseFrom trivial
theorem cv_raiseAssert (I : Py.Interp σ) :
    Py.constVal I (Gadget.raiseK "AssertionError").name = .prim (Gadget.raiseK "AssertionError").name :=
  kc_gad I _ (by simp [GOk, NC])
theorem on_reraise : Gadget.ofName Gadget.reraise.name = some .reraise := gad_name _ trivial
theorem on_raiseFrom : Gadget.ofName Gadget.raiseFrom.name = some .raiseFrom := gad_name _ trivial
theorem on_raiseAssert : Gadget.ofName (Gadget.raiseK "AssertionError").name = some (.raiseK "AssertionError") :=
  gad_name _ (by simp [GOk, NC])
theorem cv_import (I : Py.Interp σ) (a : Alias) (ha : okAl a = true) :
    Py.constVal I s!"$op:import:{a.name}:{if a.asname.isSome then 1 else 0}" = .op (.import a.name a.asname.isSome) :=
  kc_import I (nc_path (by simp only [okAl, Bool.and_eq_true] at ha; exact ha.1)) _
end ConstFacts

theorem cv_gad (I : Py.Interp σ) (g : Gadget) (hg : g = .reraise ∨ g = .raiseFrom ∨ g = .raiseK "AssertionError") :
    Py.constVal I g.name = .prim g.name := by
  rcases hg with rfl | rfl | rfl
  · exact cv_reraise I
  · exact cv_raiseFrom I
  · exact cv_raiseAssert I

theorem on_gad (g : Gadget) (hg : g = .reraise ∨ g = .raiseFrom ∨ g = .raiseK "AssertionError") :
    Gadget.ofName g.name = some g := by
  rcases hg with rfl | rfl | rfl
  · exact on_reraise
  · exact on_raiseFrom
  · exact on_raiseAssert

theorem constVal_gad (I : Py.Interp σ) {g : Gadget}
    (hg : g = .reraise ∨ g = .raiseFrom ∨ g = .raiseK "AssertionError") (t : PyCore.Config σ) (f : PyCore.Frame σ)
    (fs : List (PyCore.Frame σ)) (va : Val) :
    PyCore.callStep I t f fs (Py.constVal I g.name) va = PyCore.gadgetStep I t f fs g (PyCore.argList va) := by
  rw [cv_gad I g hg]; simp only [PyCore.callStep, on_gad g hg]

/-! ## PyCore's call of a constant on the empty record -/

theorem cc0_path (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (r : Label) (g : String)
    (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .ev (ccR r g []), kont := K } :: fs' }
      { t with stack := { f' with ctrl := .val (.data "$args" []), kont := .callA (Py.constVal I g) :: K } :: fs' } ys ∧
      ys ≠ [] ∧ ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = r := by
  let c0 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (ccR r g []), kont := K } :: fs' }
  let c1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const r g), kont := .callF (.const r "$args") :: K } :: fs' }
  let c2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (Py.constVal I g), kont := .callF (.const r "$args") :: K } :: fs' }
  let c3 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const r "$args"), kont := .callA (Py.constVal I g) :: K } :: fs' }
  refine ⟨[c0, c1, c2, c3], ?_, by simp, ?_⟩
  · refine .cons (a' := c1) (by simp [c0, c1, ccR, recR, PyCore.step, PyCore.evalStep, PyCore.top]) ?_
    refine .cons (a' := c2) (by simp [c1, c2, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK]) ?_
    refine .cons (a' := c3) (by simp [c2, c3, PyCore.step, PyCore.valStep, PyCore.top]) ?_
    exact .cons (by simp [c3, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]) (.nil _)
  · intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · simp [c0, PyCore.focus, ccR, recR, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c1, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c2, PyCore.focus] at hx
    · simp [c3, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm

macro "gsM" : tactic => `(tactic| (intro x hx; simp_all [itemsS, trS, PyCore.itemsS, PyCore.itemsB, trO, itemsO, blk,
  trEs, itemsEs, gad, cc, ccR, recR, PyCore.itemsE, List.foldl, assertRaise]))
macro "gseM" : tactic => `(tactic| exact GoodB.e ‹_› (by gs) (by gsM) (by gso) (by gsl) (by gsnd) (by gst))

/-! ## `yield from` entered -/

theorem _root_.Surf.T2.ev_yieldFrom (l e) : EvCase I p (.yieldFrom l e) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  exact A.go11 (c := .ev e) (k := .yfK :: f.kont)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
    (by simp [PyCore.step, A.ht, hc', trE, PyCore.evalStep, PyCore.top])
    (.ev (by subg)) (.misc (.yfK hk))
    (cov_ev A hc hc' (by simp [trE, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem curExc_top {gl cs} {g : Sem.Frame σ} {g' : PyCore.Frame σ} {gs : List (Sem.Frame σ)}
    {gs' : List (PyCore.Frame σ)}
    (hfs : PyCore.All2 (fun f f' => FRel p H (rdAt gl cs f') (ownAt cs f') f f') gs gs')
    (he : PyCore.kontExc g'.kont = Sem.kontExc g.kont) : PyCore.curExc (g' :: gs') = Sem.curExc (g :: gs) := by
  simp only [PyCore.curExc, Sem.curExc, he, curExc_rel hfs]
  cases Sem.kontExc g.kont <;> rfl

theorem touch_exec {st : Stmt} {ss : List Stmt} (hs : s.stack = f :: fs) (hc : f.ctrl = .exec (st :: ss)) :
    Touch p s st.label := .inl (by simp [Sem.focus, hs, hc]; cases st <;> rfl)

/-- A bare `raise`: the handled exception, or `RuntimeError`. -/
theorem exec_raise_bare (A : At p H s t f fs f' fs') {l : Label} {U : Label → Prop} {ss : List Stmt}
    (hc : f.ctrl = .exec (.raise l none none :: ss)) (hc' : f'.ctrl = .exec (trB f.chain (.raise l none none :: ss)))
    (hg : GoodB p f.chain U (.raise l none none :: ss)) (hnc : NoCompH f.chain) (hk : KRel A.x U false f.kont f'.kont) :
    Goal I p H s t := by
  let K' : List (PyCore.Kont σ) := .exprS :: .seq (trB f.chain ss) :: f'.kont
  let X : Val := match Sem.curExc (f :: fs) with | some h => h | none => Py.err "RuntimeError"
  have hcur : PyCore.curExc ({ f' with ctrl := .val (.data "$args" []), kont := K' } :: fs') = Sem.curExc (f :: fs) :=
    curExc_top A.stk.2 (by simp [K', PyCore.kontExc]; exact KRel.kexc hk)
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .raise X, kont := .seq ss :: f.kont } :: fs } := by
    simp only [Sem.step, A.hs, hc, Sem.execStep, X]
    cases h : Sem.curExc (f :: fs) <;> simp [Sem.setC, Sem.raiseNew, h, Sem.withCtx]
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (ccR (sub l 1) Gadget.reraise.name []), kont := K' } :: fs' }
  let t5 : PyCore.Config σ :=
    { t with stack := { f' with ctrl := .val (.data "$args" []), kont := .callA (Py.constVal I Gadget.reraise.name) :: K' } :: fs' }
  let t6 : PyCore.Config σ := { t with stack := { f' with ctrl := .raise X, kont := K' } :: fs' }
  let t7 : PyCore.Config σ := { t with stack := { f' with ctrl := .raise X, kont := .seq (trB f.chain ss) :: f'.kont } :: fs' }
  have st0 : PyCore.step I t = some t1 := by
    rw [pstep_exec A.ht (by rw [hc']; rfl)]; rfl
  obtain ⟨ys, py, hys, hfoc⟩ := cc0_path (I := I) t f' fs' (sub l 1) Gadget.reraise.name K'
  have st5 : PyCore.step I t5 = some t6 := by
    rw [pstep_val (t := t5) rfl rfl]
    simp only [PyCore.valStep]
    rw [constVal_gad I (.inl rfl)]
    simp only [PyCore.gadgetStep, PyCore.argList, hcur, X]
    cases h : Sem.curExc (f :: fs) <;> simp [PyCore.top, PyCore.raiseNew, hcur, h, PyCore.withCtx, t5, t6, K', X, PyCore.errRuntime]
  have st6 : PyCore.step I t6 = some t7 := by
    rw [pstep_raise (t := t6) rfl rfl]; rfl
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons st0 (py.append (.cons st5 (.cons st6 (.nil _))))) (by simp)
    (crelI_seen (A.set .raise (krel_seq hnc hg.tail hk))) (cover_of (l := l) (by simp) (touch_exec A.hs hc) ?_)
  intro y hy x hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | hy | rfl | rfl
  · simp [PyCore.focus, A.ht, hc', trB, trS, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
  · simp [t5, PyCore.focus] at hx
  · simp [t6, K', PyCore.focus] at hx

theorem exec_raise_from (A : At p H s t f fs f' fs') {l : Label} {e c : Expr} {U : Label → Prop} {ss : List Stmt}
    (hc : f.ctrl = .exec (.raise l (some e) (some c) :: ss))
    (hc' : f'.ctrl = .exec (trB f.chain (.raise l (some e) (some c) :: ss)))
    (hg : GoodB p f.chain U (.raise l (some e) (some c) :: ss)) (hnc : NoCompH f.chain)
    (hk : KRel A.x U false f.kont f'.kont) : Goal I p H s t := by
  let K' : List (PyCore.Kont σ) := .exprS :: .seq (trB f.chain ss) :: f'.kont
  obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 1) Gadget.raiseFrom.name (trE f.chain e)
    [trE f.chain c] K'
  rw [cv_gad I Gadget.raiseFrom (.inr (.inl rfl))] at pc
  have st0 : PyCore.step I t = some { t with stack := { f' with
      ctrl := .ev (ccR (sub l 1) Gadget.raiseFrom.name [trE f.chain e, trE f.chain c]), kont := K' } :: fs' } := by
    rw [pstep_exec A.ht (by rw [hc']; rfl)]; rfl
  have he : GoodE p f.chain U e := by gseM
  have hcg : GoodE p f.chain U c := by gseM
  refine goal_b (.cons (by simp [Sem.step, A.hs, hc, Sem.execStep, Sem.startEvs, Sem.setC]) (.nil _)) (by simp)
    (.cons st0 pc) (by simp)
    (crelI_seen (A.set (c := .ev e) (k := .evs [some c] [] (.raise true) :: .seq ss :: f.kont) (.ev he)
      (.misc (.evsRaiseFrom hcg (krel_seq hnc hg.tail hk)))))
    (cover_of (l := l) (by simp) (touch_exec A.hs hc) ?_)
  intro y hy x hx
  rcases List.mem_cons.1 hy with rfl | hy
  · simp [PyCore.focus, A.ht, hc', trB, trS, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)

theorem _root_.Surf.T2.exec_raise (l e c) : ExecCase I p (.raise l e c) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hn := hnc (by simp)
  cases e with
  | none =>
    cases c with
    | none => exact exec_raise_bare A hc hc' hg hn hk
    | some c => exfalso; have := hg.ok; simp [okB, okS] at this
  | some e =>
    cases c with
    | none =>
      exact A.go11 (c := .ev e) (k := .evs [] [] (.raise false) :: .seq ss :: f.kont)
        (by simp [Sem.step, A.hs, hc, Sem.execStep, Sem.startEvs, Sem.setC]) (by pestep)
        (.ev (by gse)) (.misc (.evsRaise (krel_seq hn hg.tail hk)))
        (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))
    | some c => exact exec_raise_from A hc hc' hg hn hk

/-- One step on each side changing only the top frames' code, the continuation related at the history
that counts `s`'s touches. -/
theorem _root_.Surf.T2.At.go11S (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := k } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with ctrl := c', kont := k' } :: fs' })
    (hc : CR p f.chain U i c c') (hk : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U i k k')
    (hcov : ∀ x, pfocus t = some x → Touch p s (x / 64)) (he : EnterSub k f.kont := by esub) : Goal I p H s t :=
  goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp)
    (.inl (((A.zero.upd c k c' k' he).mono_H (fun _ h => .inl h)).crel hc hk))
    (fun y hy x hx => by simp at hy; subst hy; exact .inr ⟨s, by simp, hcov x hx⟩)

theorem hH_seen {zs : List (Sem.Config σ)} : ∀ l, H l → Seen (Touch p) H zs l := fun _ h => .inl h

theorem _root_.Surf.T2.exec_assert (l tg m) : ExecCase I p (.assert l tg m) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hn := hnc (by simp)
  have hm : GoodO p f.chain U m := by
    cases m with
    | none => trivial
    | some e => show GoodE p f.chain U e; gseM
  exact A.go11S (c := .ev tg) (k := .assertK m :: .seq ss :: f.kont) (by estep) (by pestep; rfl)
    (.ev (by gse)) (.misc (.assertK (l := l) (seen_s (by simp) (touch_exec A.hs hc)) hm
      (KRel.ext ⟨hH_seen, Agree.refl _ _ _⟩ (krel_seq hn hg.tail hk))))
    (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))

/-! ### Values reaching `raise` and `assert` items -/

theorem cov1 (ht : t.stack = f' :: fs') (hf : PyCore.focus t = none) {zs : List (Sem.Config σ)} :
    Cover (Touch p) pfocus H zs [t] :=
  cover_none fun y hy => by simp at hy; subst hy; exact hf

theorem val_evsRaise (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs [] [] (.raise false) :: K0) (hK' : f'.kont = .raiseS :: K0') (hk : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .val (.tuple [v]), kont := .evsEnd (.raise false) :: K0 } :: fs } := by
    simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
  have e2 : Sem.step I { s with stack := { f with ctrl := .val (.tuple [v]), kont := .evsEnd (.raise false) :: K0 } :: fs } =
      some { s with stack := { f with ctrl := .op .mkExc [v], kont := .raiseC none :: K0 } :: fs } := by
    simp [Sem.step, Sem.valStep, Sem.finish, Sem.doOp, Sem.setC]
  have e3 : PyCore.step I t = some { t with stack := { f' with ctrl := .op .mkExc [v], kont := .raiseE :: K0' } :: fs' } := by
    simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top]
  exact goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons e3 (.nil _)) (by simp)
    (crelI_seen (A.set .op (.misc (.raiseCn hk)))) (cov1 A.ht (by simp [PyCore.focus, A.ht, hc']))

theorem val_raiseCn (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .raiseC none :: K0) (hK' : f'.kont = .raiseE :: K0') (hk : KRel A.x U false K0 K0') :
    Goal I p H s t :=
  A.go11 (c := Sem.raiseNew (f :: fs) v) (c' := PyCore.raiseNew (f' :: fs') v) (k := K0) (k' := K0')
    (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC])
    (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top])
    (by rw [raiseNew_s, raiseNew_t A.stk]; exact .raise) hk (cov_none A (by simp [PyCore.focus, A.ht, hc']))

theorem val_evsRaiseFrom (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {c : Expr} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs [some c] [] (.raise true) :: K0)
    (hK' : f'.kont = recK [] [trE f.chain c] (.callA (.prim Gadget.raiseFrom.name) :: .exprS :: K0'))
    (hg : GoodE p f.chain U c) (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" [v]), kont := .binL "," (trE f.chain c) :: .callA (.prim Gadget.raiseFrom.name) :: .exprS :: K0' } :: fs' }
  have e2 : PyCore.step I t = some t1 := by
    simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, recK, t1]
  have e3 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .ev (trE f.chain c), kont := recK [v] [] (.callA (.prim Gadget.raiseFrom.name) :: .exprS :: K0') } :: fs' } := by
    simp [t1, PyCore.step, PyCore.valStep, PyCore.top, recK]
  refine goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]) (.nil _)) (by simp)
    (.cons e2 (.cons e3 (.nil _))) (by simp) (crelI_seen (A.set (.ev hg) (.misc (.evsRaiseFrom2 hk))))
    (cover_none fun y hy => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · simp [PyCore.focus, A.ht, hc']
  · simp [t1, PyCore.focus]

theorem val_evsRaiseFrom2 (A : At p H s t f fs f' fs') {U : Label → Prop} {cv v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val cv) (hc' : f'.ctrl = .val cv)
    (hK : f.kont = .evs [] [v] (.raise true) :: K0)
    (hK' : f'.kont = recK [v] [] (.callA (.prim Gadget.raiseFrom.name) :: .exprS :: K0'))
    (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  let s1 : Sem.Config σ := { s with stack := { f with ctrl := .val (.tuple [v, cv]), kont := .evsEnd (.raise true) :: K0 } :: fs }
  have e1 : Sem.step I s = some s1 := by simp [s1, Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
  have e2 : Sem.step I s1 = some { s with stack := { f with ctrl := .op .mkExc [v], kont := .raiseC (some cv) :: K0 } :: fs } := by
    simp [s1, Sem.step, Sem.valStep, Sem.finish, Sem.doOp, Sem.setC]
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" [v, cv]), kont := .callA (.prim Gadget.raiseFrom.name) :: .exprS :: K0' } :: fs' }
  have e3 : PyCore.step I t = some t1 := by
    simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, recK, t1]
  have e4 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .op .mkExc [v], kont := .raiseC cv :: .exprS :: K0' } :: fs' } := by
    rw [pstep_val (t := t1) rfl rfl]
    simp only [t1, PyCore.valStep, PyCore.callStep, on_gad _ (.inr (.inl rfl))]
    simp [PyCore.gadgetStep, PyCore.argList, PyCore.top]
  refine goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons e3 (.cons e4 (.nil _))) (by simp)
    (crelI_seen (A.set .op (.misc (.raiseCs hk)))) (cover_none fun y hy => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · simp [PyCore.focus, A.ht, hc']
  · simp [t1, PyCore.focus]

/-! ### Signals passing items -/

/-- Surf items every signal passes (pops). -/
def sPlain : Sem.Kont σ → Bool
  | .tryE (_ :: _) _ | .handler .. | .forNext .. | .cNext .. | .yfN _ | .native _ | .loop .. | .forLoop .. => false
  | _ => true

/-- PyCore items every signal passes (pops). -/
def pPlain : PyCore.Kont σ → Bool
  | .tryE (_ :: _) _ | .handler .. | .yfGot _ | .native _ | .loop .. => false
  | _ => true

def SSig (c : Sem.Ctrl σ) : Prop := (∃ v, c = .raise v) ∨ (∃ v, c = .retv v) ∨ c = .brk ∨ c = .cont
def PSig (c : PyCore.Ctrl σ) : Prop := (∃ v, c = .raise v) ∨ (∃ v, c = .retv v) ∨ c = .brk ∨ c = .cont

theorem ssig_pop {c : Sem.Config σ} {g : Sem.Frame σ} {gs : List (Sem.Frame σ)} {κ : Sem.Kont σ} {ks : List (Sem.Kont σ)}
    {ctl : Sem.Ctrl σ} (hs : c.stack = g :: gs) (hc : g.ctrl = ctl) (hk : g.kont = κ :: ks) (hp : sPlain κ = true)
    (hsig : SSig ctl) : Sem.step I c = some { c with stack := { g with ctrl := ctl, kont := ks } :: gs } := by
  rcases hsig with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl <;> simp only [Sem.step, hs, hc] <;>
    cases κ <;> simp_all [sPlain, Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC] <;>
    (rename_i hs' _; cases hs' <;> simp_all [sPlain])

theorem psig_pop {t : PyCore.Config σ} {g : PyCore.Frame σ} {gs : List (PyCore.Frame σ)} {κ : PyCore.Kont σ}
    {ks : List (PyCore.Kont σ)} (ht : t.stack = g :: gs) (hk : g.kont = κ :: ks) (hp : pPlain κ = true)
    (hsig : PSig g.ctrl) : PyCore.step I t = some { t with stack := { g with kont := ks } :: gs } := by
  rcases hsig with ⟨v, hc⟩ | ⟨v, hc⟩ | hc | hc <;> simp only [PyCore.step, ht, hc] <;>
    cases κ <;> simp_all [pPlain, PyCore.raiseStep, PyCore.retStep, PyCore.brkStep, PyCore.contStep, PyCore.top] <;>
    (rename_i hs' _; cases hs' <;> simp_all [pPlain])

theorem pfocus_sig {t : PyCore.Config σ} {g : PyCore.Frame σ} {gs : List (PyCore.Frame σ)} {κ : PyCore.Kont σ}
    {ks : List (PyCore.Kont σ)} (ht : t.stack = g :: gs) (hk : g.kont = κ :: ks) (hp : pPlain κ = true)
    (hsig : PSig g.ctrl) : PyCore.focus t = none := by
  rcases hsig with ⟨v, hc⟩ | ⟨v, hc⟩ | hc | hc <;> simp only [PyCore.focus, ht, hc] <;>
    cases κ <;> simp_all [pPlain] <;> (rename_i hs' _; cases hs' <;> simp_all [pPlain])

theorem psig_pops (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (hsig : PSig g.ctrl) :
    ∀ (P : List (PyCore.Kont σ)) (ks : List (PyCore.Kont σ)), (∀ κ ∈ P, pPlain κ = true) →
    ∃ ys, Path (PyCore.step I) { t with stack := { g with kont := P ++ ks } :: gs }
      { t with stack := { g with kont := ks } :: gs } ys ∧ ys.length = P.length ∧ ∀ y ∈ ys, PyCore.focus y = none
  | [], ks, _ => ⟨[], .nil _, rfl, by simp⟩
  | κ :: P, ks, hP => by
    obtain ⟨ys, py, hl, hf⟩ := psig_pops t g gs hsig P ks fun κ h => hP κ (List.mem_cons_of_mem _ h)
    refine ⟨_ :: ys, .cons (psig_pop (g := { g with kont := κ :: P ++ ks }) rfl rfl (hP κ (by simp)) hsig) py,
      by simp [hl], ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact pfocus_sig (g := { g with kont := κ :: P ++ ks }) rfl rfl (hP κ (by simp)) hsig
    · exact hf y hy

theorem psig_pops' {t : PyCore.Config σ} {g : PyCore.Frame σ} {gs : List (PyCore.Frame σ)} {ctl : PyCore.Ctrl σ}
    {P ks : List (PyCore.Kont σ)} (ht : t.stack = g :: gs) (hc : g.ctrl = ctl) (hk : g.kont = P ++ ks)
    (hsig : PSig ctl) (hP : ∀ κ ∈ P, pPlain κ = true) :
    ∃ ys, Path (PyCore.step I) t { t with stack := { g with ctrl := ctl, kont := ks } :: gs } ys ∧
      ys.length = P.length ∧ ∀ y ∈ ys, PyCore.focus y = none := by
  obtain ⟨ys, py, h1, h2⟩ := psig_pops (I := I) t { g with ctrl := ctl } gs hsig P ks hP
  have e : { t with stack := { { g with ctrl := ctl } with kont := P ++ ks } :: gs } = t := by
    rw [← hc, ← hk]; exact t_eta ht
  rw [e] at py
  exact ⟨ys, py, h1, h2⟩

/-- Surf raises `X` with `K0` in one step; PyCore reaches the raise of `X` with `P ++ K0'` in the steps `ys`,
then pops `P`. -/
theorem goal_raise (A : At p H s t f fs f' fs') {U : Label → Prop} {X : Val} {K0 : List (Sem.Kont σ)}
    {K0' P : List (PyCore.Kont σ)} {ys : List (PyCore.Config σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := .raise X, kont := K0 } :: fs })
    (py : Path (PyCore.step I) t { t with stack := { f' with ctrl := .raise X, kont := P ++ K0' } :: fs' } ys)
    (hys : ys ≠ []) (hP : ∀ κ ∈ P, pPlain κ = true) (hk : KRel A.x U false K0 K0')
    (hc : Cover (Touch p) pfocus H [{ s with stack := { f with ctrl := .raise X, kont := K0 } :: fs }, s] ys)
    (he : EnterSub K0 f.kont := by esub) : Goal I p H s t := by
  obtain ⟨zs, pz, -, hz⟩ := psig_pops (I := I) t { f' with ctrl := .raise X, kont := P ++ K0' } fs' (.inl ⟨X, rfl⟩) P K0' hP
  refine goal_b (.cons e1 (.nil _)) (by simp) (py.append pz) (by simp [hys]) (crelI_seen (A.set .raise hk he))
    (Cover.append hc (cover_none hz))

theorem val_raiseCs (A : At p H s t f fs f' fs') {U : Label → Prop} {e cv : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val e) (hc' : f'.ctrl = .val e)
    (hK : f.kont = .raiseC (some cv) :: K0) (hK' : f'.kont = .raiseC cv :: .exprS :: K0') (hk : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  by_cases hcv : cv = .none
  · subst hcv
    have he : PyCore.kontExc f'.kont = Sem.kontExc f.kont := by
      rw [hK, hK']; simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc hk
    refine goal_raise A (X := exc (f :: fs) (Py.setCause e .none)) (P := [.exprS])
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.raiseNew, exc])
      (.cons (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, raiseNew_top A.stk.2 he]) (.nil _))
      (by simp) (by simp [pPlain]) hk (cov1 A.ht (by simp [PyCore.focus, A.ht, hc']))
  · exact A.go11 (c := .op .mkExc [cv]) (c' := .op .mkExc [cv]) (k := .raiseW e :: K0) (k' := .raiseW e :: .exprS :: K0')
      (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.doOp, hcv])
      (by cases cv <;> simp_all [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top]) .op (.misc (.raiseW hk))
      (cov_none A (by simp [PyCore.focus, A.ht, hc']))

theorem val_raiseW (A : At p H s t f fs f' fs') {U : Label → Prop} {e v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .raiseW e :: K0) (hK' : f'.kont = .raiseW e :: .exprS :: K0') (hk : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  have he : PyCore.kontExc f'.kont = Sem.kontExc f.kont := by
    rw [hK, hK']; simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc hk
  exact goal_raise A (X := exc (f :: fs) (Py.setCause e v)) (P := [.exprS])
    (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.raiseNew, exc])
    (.cons (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, raiseNew_top A.stk.2 he]) (.nil _))
    (by simp) (by simp [pPlain]) hk (cov1 A.ht (by simp [PyCore.focus, A.ht, hc']))

theorem val_assertK (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label} {m : Option Expr}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .assertK m :: K0) (hK' : f'.kont = .ifS [] [assertRaise f.chain l m] :: K0')
    (hH : H l) (hm : GoodO p f.chain U m) (hk : KRel A.x U false K0 K0') : Goal I p H s t :=
  val_tst A (v := v) (by sstep) (by pstep) (.misc (.assertT hH hm hk)) (by simp [PyCore.focus, A.ht, hc'])

theorem val_assertM (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .assertM :: K0)
    (hK' : f'.kont = recK [] [] (.callA (.prim (Gadget.raiseK "AssertionError").name) :: .exprS :: .seq [] :: K0'))
    (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  let K1 : List (PyCore.Kont σ) := .exprS :: .seq [] :: K0'
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" [v]), kont := .callA (.prim (Gadget.raiseK "AssertionError").name) :: K1 } :: fs' }
  have he : PyCore.kontExc K1 = Sem.kontExc f.kont := by
    rw [hK]; simp only [K1, PyCore.kontExc, Sem.kontExc]; exact KRel.kexc hk
  have e2 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .raise (exc (f :: fs) (.err "AssertionError" [v])), kont := [.exprS, .seq []] ++ K0' } :: fs' } := by
    rw [pstep_val (t := t1) rfl rfl]
    simp only [t1, PyCore.valStep, PyCore.callStep, on_gad _ (.inr (.inr rfl))]
    simp only [PyCore.gadgetStep, PyCore.argList, PyCore.top]
    rw [raiseNew_top (g' := { f' with ctrl := .val (.data "$args" [v]), kont := K1 }) A.stk.2 he]
    rfl
  refine goal_raise A (X := exc (f :: fs) (.err "AssertionError" [v])) (P := [.exprS, .seq []])
    (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.raiseNew, exc])
    (.cons (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, recK, t1, K1]) (.cons e2 (.nil _)))
    (by simp) (by simp [pPlain]) hk (cover_none fun y hy => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · simp [PyCore.focus, A.ht, hc']
  · simp [t1, PyCore.focus]

theorem val_assertT (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label} {m : Option Expr}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .assertT m :: K0) (hK' : f'.kont = .ifT [] [assertRaise f.chain l m] :: K0')
    (hH : H l) (hm : GoodO p f.chain U m) (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  have hn := cov_none A (by simp [PyCore.focus, A.ht, hc'])
  cases v
  case bool b =>
    cases b
    case true =>
      exact A.go11 (c := .exec []) (c' := .exec []) (by sstep) (by pstep) (.exec (goodB_nil _ U) (by simp)) hk hn
    case false =>
      let K1 : List (PyCore.Kont σ) := .exprS :: .seq [] :: K0'
      have st1 : PyCore.step I t = some { t with stack := { f' with ctrl := .exec [assertRaise f.chain l m], kont := K0' } :: fs' } := by
        simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top]
      have hl : ∀ {zs : List (Sem.Config σ)} (x : Label), x / 64 = l → Seen (Touch p) H zs (x / 64) :=
        fun x h => .inl (by rw [h]; exact hH)
      cases m with
      | some e =>
        have st2 : PyCore.step I { t with stack := { f' with ctrl := .exec [assertRaise f.chain l (some e)], kont := K0' } :: fs' } =
            some { t with stack := { f' with ctrl := .ev (ccR (sub l 2) (Gadget.raiseK "AssertionError").name [trE f.chain e]), kont := K1 } :: fs' } := by
          rw [pstep_exec rfl rfl]; rfl
        obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 2) (Gadget.raiseK "AssertionError").name
          (trE f.chain e) [] K1
        rw [cv_gad I _ (.inr (.inr rfl))] at pc
        refine goal_b (.cons (by sstep) (.nil _)) (by simp) (.cons st1 (.cons st2 pc)) (by simp)
          (crelI_seen (A.set (c := .ev e) (k := .assertM :: K0) (.ev hm) (.misc (.assertM hk)))) ?_
        intro y hy x hx
        simp only [List.mem_cons] at hy
        rcases hy with rfl | rfl | hy
        · have := pfocus_le hx; simp [PyCore.focus, A.ht, hc'] at this
        · have := pfocus_le hx; simp [PyCore.focus, assertRaise, PyCore.Stmt.label] at this
          exact hl x (by rw [← this]; exact sub_div _ _ (by omega))
        · exact hl x (by rw [hfoc y hy x (pfocus_le hx)]; exact sub_div _ _ (by omega))
      | none =>
        have st2 : PyCore.step I { t with stack := { f' with ctrl := .exec [assertRaise f.chain l none], kont := K0' } :: fs' } =
            some { t with stack := { f' with ctrl := .ev (ccR (sub l 2) (Gadget.raiseK "AssertionError").name []), kont := K1 } :: fs' } := by
          rw [pstep_exec rfl rfl]; rfl
        obtain ⟨ys, pc, hys, hfoc⟩ := cc0_path (I := I) t f' fs' (sub l 2) (Gadget.raiseK "AssertionError").name K1
        have he : PyCore.kontExc K1 = Sem.kontExc f.kont := by
          rw [hK]; simp only [K1, PyCore.kontExc, Sem.kontExc]; exact KRel.kexc hk
        let t6 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" []), kont := .callA (Py.constVal I (Gadget.raiseK "AssertionError").name) :: K1 } :: fs' }
        have st6 : PyCore.step I t6 = some { t with stack := { f' with ctrl := .raise (exc (f :: fs) (.err "AssertionError" [])), kont := [.exprS, .seq []] ++ K0' } :: fs' } := by
          rw [pstep_val (t := t6) rfl rfl]
          simp only [t6, PyCore.valStep]
          rw [constVal_gad I (.inr (.inr rfl))]
          simp only [PyCore.gadgetStep, PyCore.argList, PyCore.top]
          rw [raiseNew_top (g' := { f' with ctrl := .val (.data "$args" []), kont := K1 }) A.stk.2 he]
          rfl
        refine goal_raise A (X := exc (f :: fs) (.err "AssertionError" [])) (P := [.exprS, .seq []])
          (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.raiseNew, exc])
          (.cons st1 (.cons st2 (pc.append (.cons st6 (.nil _))))) (by simp) (by simp [pPlain]) hk ?_
        intro y hy x hx
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | hy | rfl
        · have := pfocus_le hx; simp [PyCore.focus, A.ht, hc'] at this
        · have := pfocus_le hx; simp [PyCore.focus, assertRaise, PyCore.Stmt.label] at this
          exact hl x (by rw [← this]; exact sub_div _ _ (by omega))
        · exact hl x (by rw [hfoc y hy x (pfocus_le hx)]; exact sub_div _ _ (by omega))
        · have := pfocus_le hx; simp [t6, PyCore.focus] at this
  all_goals exact fin_stuck A (by sstep) (by pstep) hn

/-! ### `import` -/

theorem alias_nodot (W : WF p) {C : List Scope} {U : Label → Prop} {l : Label} {al : List Alias} {ss : List Stmt}
    (hg : GoodB p C U (.imp l al :: ss)) {a : Alias} (ha : a ∈ al) (hn : a.name ≠ "*") :
    ¬ Dot (mangle (priv C) a.bound) :=
  W.nodot a.l _ C (hg.s _ (by
    simp only [itemsB, itemsS, bindingAliases, List.mem_append, List.mem_map, List.mem_filter]
    exact .inl ⟨a, ⟨ha, by simpa using hn⟩, rfl⟩))

/-- PyCore binds one alias of `import`: the statement, the constant's call, up to the operation. -/
theorem imp_alias_path (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (C : List Scope)
    (a : Alias) (ha : okAl a = true) (hn : a.name ≠ "*") (rest : PS) (KK : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { g with ctrl := .exec (impS C a :: rest), kont := KK } :: gs }
      { t with stack := { g with ctrl := .op (.import a.name a.asname.isSome) [], kont := .assign (mangle (priv C) a.bound) :: .seq rest :: KK } :: gs } ys ∧
      ys ≠ [] ∧ ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = a.l := by
  let str : String := s!"$op:import:{a.name}:{if a.asname.isSome then 1 else 0}"
  have hi : impS C a = .assign (sub a.l 0) (mangle (priv C) a.bound) (cc a.l 1 str []) := by simp [impS, hn]; rfl
  let K1 : List (PyCore.Kont σ) := .assign (mangle (priv C) a.bound) :: .seq rest :: KK
  have st0 : PyCore.step I { t with stack := { g with ctrl := .exec (impS C a :: rest), kont := KK } :: gs } =
      some { t with stack := { g with ctrl := .ev (ccR (sub a.l 1) str []), kont := K1 } :: gs } := by
    rw [pstep_exec rfl rfl, hi]; rfl
  obtain ⟨ys, pc, hys, hfoc⟩ := cc0_path (I := I) t g gs (sub a.l 1) str K1
  rw [cv_import I a ha] at pc
  have st5 : PyCore.step I { t with stack := { g with ctrl := .val (.data "$args" []), kont := .callA (.op (.import a.name a.asname.isSome)) :: K1 } :: gs } =
      some { t with stack := { g with ctrl := .op (.import a.name a.asname.isSome) [], kont := K1 } :: gs } := by
    rw [pstep_val rfl rfl]; simp [PyCore.valStep, PyCore.callStep, PyCore.top, PyCore.argList]
  refine ⟨_ :: (ys ++ [_]), .cons st0 (pc.append (.cons st5 (.nil _))), by simp, ?_⟩
  intro y hy x hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | hy | rfl
  · simp [PyCore.focus, hi, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
  · simp [PyCore.focus] at hx

/-- PyCore's `stuckAt r`: the steps up to the gadget `$stuck`, which takes none. -/
theorem stuckAt_path (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (r : Label) (rest : PS)
    (KK : List (PyCore.Kont σ)) :
    ∃ ys t', Path (PyCore.step I) { t with stack := { g with ctrl := .exec (stuckAt r :: rest), kont := KK } :: gs } t' ys ∧
      PyCore.step I t' = none ∧ t'.st = t.st ∧ t'.out = t.out ∧ t'.stack ≠ [] ∧
      ∀ y ∈ t' :: ys, ∀ x, PyCore.focus y = some x → x = r := by
  let K : List (PyCore.Kont σ) := .exprS :: .seq rest :: KK
  have st0 : PyCore.step I { t with stack := { g with ctrl := .exec (stuckAt r :: rest), kont := KK } :: gs } =
      some { t with stack := { g with ctrl := .ev (ccR r Gadget.stuck.name []), kont := K } :: gs } := by
    rw [pstep_exec rfl rfl]; rfl
  obtain ⟨ys, pc, -, hfoc⟩ := cc0_path (I := I) t g gs r Gadget.stuck.name K
  refine ⟨_ :: ys, _, .cons st0 pc, ?_, rfl, rfl, by simp, ?_⟩
  · simp [PyCore.step, PyCore.valStep, PyCore.callStep, Gadget.name, kc_stuck, gad_stuck', PyCore.gadgetStep]
  · intro y hy x hx
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · simp [PyCore.focus] at hx
    · simp [PyCore.focus, stuckAt, PyCore.Stmt.label] at hx; exact hx.symm
    · exact hfoc y hy x hx

theorem touch_imp {a : Alias} {l : Label} {ss : List Stmt} (hs : s.stack = f :: fs) (hc : f.ctrl = .exec (.imp l [a] :: ss)) :
    Touch p s a.l := .inr (by simp [hs, TouchF, hc])

theorem exec_imp_ok (A : At p H s t f fs f' fs') (W : WF p) {l : Label} {al : List Alias} {U : Label → Prop}
    {ss : List Stmt} (hc : f.ctrl = .exec (.imp l al :: ss)) (hc' : f'.ctrl = .exec (trB f.chain (.imp l al :: ss)))
    (hg : GoodB p f.chain U (.imp l al :: ss)) (hn : NoCompH f.chain) (hk : KRel A.x U false f.kont f'.kont)
    (hst : ∀ a ∈ al, a.name ≠ "*") : Goal I p H s t := by
  have hok : ∀ a ∈ al, okAl a = true := by
    have := hg.ok; simp only [okB, okS, Bool.and_eq_true, List.all_eq_true] at this; exact this.1.1
  have hK' : PyCore.step I t = some { t with stack := { f' with ctrl := .exec (al.map (impS f.chain)), kont := .tryE [] [] :: .seq (trB f.chain ss) :: f'.kont } :: fs' } := by
    rw [pstep_exec A.ht (by rw [hc']; rfl)]; simp [PyCore.execStep, PyCore.top, blk, impS, trS]
  cases al with
  | nil =>
    exact A.go11 (c := .exec []) (c' := .exec []) (k := .seq ss :: f.kont) (by estep) (by rw [hK']; rfl)
      (.exec (goodB_nil _ U) (by simp)) (.core (.seq (pre := [.tryE [] []]) (fun _ => hn) (.inr (.inl rfl)) hg.tail hk))
      (cov_exec A hc hc' (by simp [trS, blk, PyCore.Stmt.label, Stmt.label, sub_div]))
  | cons a al =>
    have hy := alias_nodot W hg (a := a) (by simp) (hst a (by simp))
    obtain ⟨ys, py, hys, hfoc⟩ := imp_alias_path (I := I) t f' fs' f.chain a (hok a (by simp)) (hst a (by simp)) (al.map (impS f.chain))
      (.tryE [] [] :: .seq (trB f.chain ss) :: f'.kont)
    have ht0 : ∀ x, PyCore.focus t = some x → x / 64 = l := by
      intro x hx; simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    cases al with
    | nil =>
      refine goal_b (.cons (by simp [Sem.step, A.hs, hc, Sem.execStep, Sem.doOp, Sem.setC, Sem.mg, hst a (by simp)]) (.nil _)) (by simp)
        (.cons hK' py) (by simp)
        (crelI_seen (A.set (c := .op (.import a.name a.asname.isSome) []) (k := .assignN (mangle (priv f.chain) a.bound) :: .seq ss :: f.kont) .op
          (.core (.assignN hy (.core (.seq (pre := [.seq [], .tryE [] []]) (fun _ => hn) (.inr (.inr rfl)) hg.tail hk))))))
        ?_
      intro y hy' x hx
      rcases List.mem_cons.1 hy' with rfl | hy'
      · exact .inr ⟨s, by simp, by rw [ht0 x (pfocus_le hx)]; exact touch_exec A.hs hc⟩
      · exact .inr ⟨s, by simp, by rw [hfoc y hy' x (pfocus_le hx)]; exact touch_imp A.hs hc⟩
    | cons b rest =>
      let s1 : Sem.Config σ := { s with stack := { f with ctrl := .exec ((a :: b :: rest).map fun a => .imp l [a]), kont := .seq ss :: f.kont } :: fs }
      have e1 : Sem.step I s = some s1 := by
        simp [s1, Sem.step, A.hs, hc, Sem.execStep, Sem.setC]
      have e2 : Sem.step I s1 = some { s with stack := { f with ctrl := .op (.import a.name a.asname.isSome) [], kont := .assignN (mangle (priv f.chain) a.bound) :: .seq ((b :: rest).map fun a => .imp l [a]) :: .seq ss :: f.kont } :: fs } := by
        simp [s1, Sem.step, Sem.execStep, Sem.doOp, Sem.setC, Sem.mg, hst a (by simp)]
      refine goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons hK' py) (by simp)
        (crelI_seen (A.set .op (.misc (.impMany (l := l) hy (fun a h => hok a (by simp [h]))
          (fun a h => alias_nodot W hg (by simp [h]) (hst a (by simp [h]))) (krel_seq hn hg.tail hk)))))
        ?_
      intro y hy' x hx
      rcases List.mem_cons.1 hy' with rfl | hy'
      · exact .inr ⟨s, by simp, by rw [ht0 x (pfocus_le hx)]; exact touch_exec A.hs hc⟩
      · exact .inr ⟨s1, by simp, by rw [hfoc y hy' x (pfocus_le hx)]; exact touch_imp (f := { f with ctrl := _, kont := _ }) rfl rfl⟩

/-- A value reaches the binding of an alias of `import`; the next alias (whose bound name has no dot) follows. -/
theorem val_impMany (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label} {y : Name}
    {al : List Alias} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v)
    (hc' : f'.ctrl = .val v) (hK : f.kont = .assignN y :: .seq (al.map fun a => .imp l [a]) :: K0)
    (hK' : f'.kont = .assign y :: .seq (al.map (impS f.chain)) :: .tryE [] [] :: K0') (hy : ¬ Dot y)
    (hok : ∀ a ∈ al, okAl a = true) (hnd : ∀ a ∈ al, ¬ Dot (mangle (priv f.chain) a.bound))
    (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  obtain ⟨s1, t1, g, g', e1, e2, A1, hch, hgk, hgk', hcc, ha⟩ :=
    store0 A.zero hy v (.exec []) (.seq (al.map fun a => .imp l [a]) :: K0) (.exec [])
      (.seq (al.map (impS f.chain)) :: .tryE [] [] :: K0') (by rw [hK]; simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc hk)
  have es : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, Sem.valStep, hK]; exact e1
  have et : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
  have hk1 : KRel (cx p H (rdOf t1 g') (ownOf t1 g') g) U false K0 K0' :=
    krel_move hk hch (ha.mono fun _ h => h.elim) fun _ h => h
  have hf0 : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  rcases hcc with ⟨h1, h2⟩ | ⟨ex, h1, h2⟩
  · have hf1 : PyCore.focus t1 = none := by simp [PyCore.focus, A1.ht, h2]
    cases al with
    | nil =>
      let s2 : Sem.Config σ := { s1 with stack := { g with ctrl := .exec [], kont := K0 } :: fs }
      have es1 : Sem.step I s1 = some s2 := by simp [s2, Sem.step, A1.hs, h1, hgk, Sem.doneStep, Sem.setC]
      let t2 : PyCore.Config σ := { t1 with stack := { g' with ctrl := .exec [], kont := .tryE [] [] :: K0' } :: fs' }
      have et1 : PyCore.step I t1 = some t2 := by
        rw [pstep_done A1.ht h2]; simp [t2, PyCore.doneStep, hgk', PyCore.top]
      have et2 : PyCore.step I t2 = some { t1 with stack := { g' with ctrl := .exec [], kont := K0' } :: fs' } := by
        rw [pstep_done (t := t2) rfl rfl]; simp [t2, PyCore.doneStep, PyCore.top]
      refine goal_b (.cons es (.cons es1 (.nil _))) (by simp) (.cons et (.cons et1 (.cons et2 (.nil _)))) (by simp)
        (.inl (((A1.upd (.exec []) K0 (.exec []) K0').mono_H hH_seen).crel (U := U) (i := false)
          (.exec (goodB_nil _ U) (by simp)) (KRel.ext ⟨hH_seen, Agree.refl _ _ _⟩ hk1)))
        (cover_none fun y hy => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact hf0
      · exact hf1
      · simp [t2, PyCore.focus]
    | cons b rest =>
      let s2 : Sem.Config σ := { s1 with stack := { g with ctrl := .exec (Stmt.imp l [b] :: rest.map fun a => .imp l [a]), kont := K0 } :: fs }
      have es1 : Sem.step I s1 = some s2 := by simp [s2, Sem.step, A1.hs, h1, hgk, Sem.doneStep, Sem.setC]
      have et1 : PyCore.step I t1 = some { t1 with stack := { g' with ctrl := .exec (impS f.chain b :: rest.map (impS f.chain)), kont := .tryE [] [] :: K0' } :: fs' } := by
        rw [pstep_done A1.ht h2]; simp [PyCore.doneStep, hgk', PyCore.top]
      by_cases hbs : b.name = "*"
      · -- `import *` is no Python: both runs are stuck
        have es2 : Sem.step I s2 = none := by simp [s2, Sem.step, Sem.execStep, hbs]
        have hi : impS f.chain b = stuckAt (sub b.l 0) := by simp [impS, hbs]
        rw [hi] at et1
        obtain ⟨ys, t', py, hn', hst', hout', hstk', hfoc⟩ := stuckAt_path (I := I) t1 g' fs' (sub b.l 0)
          (rest.map (impS f.chain)) (.tryE [] [] :: K0')
        refine .inl ⟨s2, t', [s, s1], t :: t1 :: ys, .cons es (.cons es1 (.nil _)), es2, .cons et (.cons et1 py), hn', ?_, ?_⟩
        · cases ht' : t'.stack with
          | nil => exact absurd ht' hstk'
          | cons => simp [Fin, Sem.outcome, PyCore.outcome, ht', s2, OCorr, hst', hout', A1.out, A1.st]
        · intro y hy x hx
          simp only [List.mem_cons] at hy
          rcases hy with rfl | rfl | rfl | hy
          · exact .inr ⟨s2, by simp, by rw [hfoc _ (by simp) x (pfocus_le hx), sub_div _ _ (by omega)]; exact touch_imp (s := s2) rfl rfl⟩
          · rw [pfocus_le hx] at hf0; cases hf0
          · rw [pfocus_le hx] at hf1; cases hf1
          · exact .inr ⟨s2, by simp, by rw [hfoc y (by simp [hy]) x (pfocus_le hx), sub_div _ _ (by omega)]; exact touch_imp (s := s2) rfl rfl⟩
      have es2 : Sem.step I s2 = some { s1 with stack := { g with ctrl := .op (.import b.name b.asname.isSome) [], kont := .assignN (mangle (priv g.chain) b.bound) :: .seq (rest.map fun a => .imp l [a]) :: K0 } :: fs } := by
        simp [s2, Sem.step, Sem.execStep, Sem.doOp, Sem.setC, Sem.mg, hbs]
      obtain ⟨ys, py, hys, hfoc⟩ := imp_alias_path (I := I) t1 g' fs' f.chain b (hok b (by simp)) hbs
        (rest.map (impS f.chain)) (.tryE [] [] :: K0')
      have hyb := hnd b (by simp)
      rw [← hch] at hyb py et1
      refine goal_b (.cons es (.cons es1 (.cons es2 (.nil _)))) (by simp) (.cons et (.cons et1 py)) (by simp)
        (.inl (((A1.upd _ _ _ _).mono_H hH_seen).crel (U := U) (i := true) .op
          (.misc (.impMany (l := l) hyb (fun a h => hok a (by simp [h])) (fun a h => by rw [hch]; exact hnd a (by simp [h]))
            (KRel.ext ⟨hH_seen, Agree.refl _ _ _⟩ hk1)))))
        ?_
      intro y hy x hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · rw [pfocus_le hx] at hf0; cases hf0
      · rw [pfocus_le hx] at hf1; cases hf1
      · exact .inr ⟨s2, by simp, by rw [hfoc y hy x (pfocus_le hx)]; exact touch_imp (f := { g with ctrl := _, kont := _ }) rfl rfl⟩
  · let s2 : Sem.Config σ := { s1 with stack := { g with ctrl := .raise ex, kont := K0 } :: fs }
    have es1 : Sem.step I s1 = some s2 := ssig_pop A1.hs h1 hgk rfl (.inl ⟨ex, rfl⟩)
    obtain ⟨zs, pz, -, hz⟩ := psig_pops' (I := I) A1.ht h2 (by rw [hgk']; rfl) (.inl ⟨ex, rfl⟩)
      (P := [.seq (al.map (impS f.chain)), .tryE [] []]) (by simp [pPlain])
    refine goal_b (.cons es (.cons es1 (.nil _))) (by simp) (.cons et pz) (by simp)
      (.inl (((A1.upd (.raise ex) K0 (.raise ex) K0').mono_H hH_seen).crel (U := U) (i := false) .raise
        (KRel.ext ⟨hH_seen, Agree.refl _ _ _⟩ hk1)))
      (cover_none fun y hy => by
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hf0
        · exact hz y hy)

end

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-! ### `yield from`: asking the delegate -/

theorem isStop_exc (st : List (Sem.Frame σ)) {k : String} (hk : k ≠ "StopIteration") :
    Py.isStop (exc st (Py.err k)) = false := by
  unfold exc; cases Sem.curExc st <;> simp [Sem.withCtx, Py.isStop, Py.Val.setCtx, Py.Val.base, Py.err, hk]

theorem stop_exc (st : List (Sem.Frame σ)) :
    Py.isStop (exc st (Py.stopOf .none)) = true ∧ Py.stopValue (exc st (Py.stopOf .none)) = .none := by
  unfold exc; cases Sem.curExc st <;> simp [Sem.withCtx, Py.isStop, Py.stopValue, Py.Val.setCtx, Py.Val.base, Py.stopOf]

theorem cov1B {zs : List (Sem.Config σ)} (hf : PyCore.focus t = none) : Cover (Touch p) pfocus H zs [t] :=
  cover_none fun y hy => by simp at hy; subst hy; exact hf

/-- One step of each run (Surf's `s0 → s`, PyCore's `t0 → t`, evaluating no node) before a step from `s ~ t`. -/
theorem goalB_pre {H0 : Label → Prop} {s0 : Sem.Config σ} {t0 : PyCore.Config σ} (e0 : Sem.step I s0 = some s)
    (et : PyCore.step I t0 = some t) (hf0 : PyCore.focus t0 = none)
    (h : GoalB I p (Seen (Touch p) H0 [s0]) s t) : GoalB I p H0 s0 t0 :=
  SimStepB.pre (.cons e0 (.nil _)) (by simp) (.cons et (.nil _)) (by simp) (cov1B hf0) h

/-- The delegate's `next` raised `E` (no `StopIteration`) in both runs: Surf passes `yield from`'s item. -/
theorem yf_raise (A : At0 p H s t f fs f' fs') {U : Label → Prop} {sb E : Val} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (hk : f.kont = .yfN sb :: K)
    (hK : KRel (cx p H (rdOf t f') (ownOf t f') f) U true K K') (hE : Py.isStop E = false)
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := .raise E, kont := f.kont } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .raise E, kont := K' } :: fs' })
    (hf : PyCore.focus t = none) : GoalB I p H s t := by
  have e3 : Sem.step I { s with stack := { f with ctrl := .raise E, kont := f.kont } :: fs } =
      some { s with stack := { f with ctrl := .raise E, kont := K } :: fs } := by
    simp [Sem.step, Sem.raiseStep, hk, hE, Sem.setC]
  exact goalB_b (.cons e1 (.cons e3 (.nil _))) (by simp) (.cons e2 (.nil _)) (by simp)
    (.inl (((A.upd (.raise E) K (.raise E) K').mono_H hH_seen).crel (U := U) (i := true) .raise
      (KRel.ext ⟨hH_seen, Agree.refl _ _ _⟩ hK))) (cov1B hf)

theorem yf_deleg_it (A : At0 p H s t f fs f' fs') {U : Label → Prop} {sb : Val} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (hc : f.ctrl = .call .next [sb] []) (hk : f.kont = .yfN sb :: K)
    (hc' : f'.ctrl = .yfStep (.it sb)) (hk' : f'.kont = K') (hsb : ∀ o, sb ≠ .gen o)
    (hK : KRel (cx p H (rdOf t f') (ownOf t f') f) U true K K') : GoalB I p H s t := by
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .op .next [sb], kont := .yfN sb :: K } :: fs } := by
    simp only [Sem.step, A.hs, hc]
    cases sb <;> simp_all [Sem.callStep, Sem.doOp, Sem.setC]
  have e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .op .next [sb], kont := .yfGot (.it sb) :: K' } :: fs' } := by
    simp [PyCore.step, A.ht, hc', PyCore.yfStepS, PyCore.top, hk']
  exact goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp)
    (crelI_seen ((A.upd _ _ _ _).crel (U := U) (i := true) .op (.misc (.yfN (.inr ⟨hsb, rfl⟩) hK))))
    (cov1B (by simp [PyCore.focus, A.ht, hc']))

/-- `yield from` asks its delegate for the next item (Surf's `call next [sb]`, PyCore's `yfStep d`), the
configurations `s`, `t` reached by a step of each run from `s0`, `t0`. A generator delegate in a
`yield from` itself asks its own delegate (the measure: suspended generators). -/
theorem yf_deleg (W : WF p) : ∀ (n : Nat) {H0 : Label → Prop} {s0 s : Sem.Config σ} {t0 t : PyCore.Config σ}
    {f : Sem.Frame σ} {fs : List (Sem.Frame σ)} {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}
    {U : Label → Prop} {sb : Val} {d : PyCore.Deleg} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)},
    nSusp t < n → Sem.step I s0 = some s → PyCore.step I t0 = some t → PyCore.focus t0 = none →
    At0 p (Seen (Touch p) H0 [s0]) s t f fs f' fs' → f.ctrl = .call .next [sb] [] → f.kont = .yfN sb :: K →
    f'.ctrl = .yfStep d → f'.kont = K' → DelegR sb d →
    KRel (cx p (Seen (Touch p) H0 [s0]) (rdOf t f') (ownOf t f') f) U true K K' → GoalB I p H0 s0 t0
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn, _, _, _, _, _, _, _, _, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, H0, s0, s, t0, t, f, fs, f', fs', U, sb, d, K, K', hn, e0, et0', hf0, A, hc, hk, hc', hk', hd, hK => by
    rcases hd with ⟨o, rfl, rfl⟩ | ⟨hsb, rfl⟩
    case inr => exact goalB_pre e0 et0' hf0 (yf_deleg_it A hc hk hc' hk' hsb hK)
    have hf : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
    have he : PyCore.kontExc f'.kont = Sem.kontExc f.kont := by
      rw [hk, hk']; simp only [Sem.kontExc]; exact KRel.kexc hK
    have hrn : ∀ v, PyCore.raiseNew (f' :: fs') v = .raise (exc (f :: fs) v) := raiseNew_top A.hfs he
    have hrel := A.objs o
    have es0 : Sem.step I s = Sem.callStep s { f with ctrl := .wait } fs .next [.gen o] [] := by
      simp only [Sem.step, A.hs, hc]
    have et0 : PyCore.step I t = PyCore.yfStepS t f' fs' (.gen o) := by simp only [PyCore.step, A.ht, hc']
    have tyE : (∀ g, sObj s o ≠ some (.gen (.susp g))) → (sObj s o ≠ some (.gen .running)) →
        (sObj s o ≠ some (.gen .done)) → (∀ g', pObj t o ≠ some (.gen (.susp g'))) →
        (pObj t o ≠ some (.gen .running)) → (pObj t o ≠ some (.gen .done)) → GoalB I p H0 s0 t0 := by
      intro h1 h2 h3 h4 h5 h6
      refine goalB_pre e0 et0' hf0 (yf_raise A hk hK (E := exc (f :: fs) (Py.err "TypeError"))
        (isStop_exc (f :: fs) (by decide)) ?_ ?_ hf)
      · rw [es0]; simp only [Sem.callStep]
        revert h1 h2 h3; simp only [sObj]
        cases s.objs[o]? with
        | none => intros; simp [Sem.setC, Sem.raiseNew, exc, Sem.curExc]
        | some ob =>
          cases ob with
          | clo => intros; simp [Sem.setC, Sem.raiseNew, exc, Sem.curExc]
          | gen g0 => cases g0 <;> simp_all [Sem.setC, Sem.raiseNew, exc, Sem.curExc]
      · rw [et0]; simp only [PyCore.yfStepS]
        revert h4 h5 h6; simp only [pObj]
        cases t.objs[o]? with
        | none => intros; simp [PyCore.top, hrn, PyCore.errType, hk']
        | some ob =>
          cases ob with
          | clo => intros; simp [PyCore.top, hrn, PyCore.errType, hk']
          | gen g0 => cases g0 <;> simp_all [PyCore.top, PyCore.errType]
    cases hs : sObj s o with
    | none =>
      rw [hs] at hrel
      cases ht : pObj t o with
      | none => exact tyE (by simp [hs]) (by simp [hs]) (by simp [hs]) (by simp [ht]) (by simp [ht]) (by simp [ht])
      | some _ => rw [ht] at hrel; exact hrel.elim
    | some ob =>
      rw [hs] at hrel
      cases ht : pObj t o with
      | none => rw [ht] at hrel; exact hrel.elim
      | some ob' =>
        rw [ht] at hrel
        cases hrel with
        | clo => exact tyE (by simp [hs]) (by simp [hs]) (by simp [hs]) (by simp [ht]) (by simp [ht]) (by simp [ht])
        | gen hG =>
          have hkw : KRel (cx p (Seen (Touch p) H0 [s0]) (rdOf t f') (ownOf t f') f) U true f.kont (.yfGot (.gen o) :: K') := by
            rw [hk]; exact .misc (.yfN (.inl ⟨o, rfl, rfl⟩) hK)
          cases hG with
          | running =>
            refine goalB_pre e0 et0' hf0 (yf_raise A hk hK (E := exc (f :: fs) (Py.err "ValueError"))
              (isStop_exc (f :: fs) (by decide)) ?_ ?_ hf)
            · rw [es0]; simp [Sem.callStep, sObj] at hs ⊢; simp [hs, Sem.setC, Sem.raiseNew, exc, Sem.curExc]
            · rw [et0]; simp [PyCore.yfStepS, pObj] at ht ⊢; simp [ht, PyCore.top, hrn, PyCore.errValue, hk']
          | done =>
            have hst := stop_exc (f :: fs)
            let s1 : Sem.Config σ := { s with stack := { f with ctrl := .raise (exc (f :: fs) (Py.stopOf .none)), kont := f.kont } :: fs }
            have e1 : Sem.step I s = some s1 := by
              rw [es0]; simp [Sem.callStep, sObj] at hs ⊢; simp [s1, hs, Sem.setC, Sem.raiseNew, exc]; rfl
            have e3 : Sem.step I s1 = some { s with stack := { f with ctrl := .val .none, kont := K } :: fs } := by
              simp [s1, Sem.step, Sem.raiseStep, hk, hst.1, hst.2, Sem.setC]
            have e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .val .none, kont := K' } :: fs' } := by
              rw [et0]; simp [PyCore.yfStepS, pObj] at ht ⊢; simp [ht, PyCore.top, hk']
            exact goalB_pre e0 et0' hf0 (goalB_b (.cons e1 (.cons e3 (.nil _))) (by simp) (.cons e2 (.nil _)) (by simp)
              (.inl (((A.upd (.val .none) K (.val .none) K' (esub_cons hk)).mono_H hH_seen).crel (U := U) (i := true) .val
                (KRel.ext ⟨hH_seen, Agree.refl _ _ _⟩ hK))) (cov1B hf))
          | @susp g g' hfr =>
            have A1 := A.push ht hfr.toFRel0 hfr.hl f.kont (.yfGot (.gen o) :: K') hkw hs
            obtain ⟨U1, i1, hc1, hk1⟩ := hfr.code
            have e1 : Sem.step I s = some { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) } := by
              rw [es0]; simp [Sem.callStep, sObj] at hs ⊢; simp [hs]
            have e2 : PyCore.step I t = some { t with stack := g' :: { f' with ctrl := .wait, kont := .yfGot (.gen o) :: K' } :: fs', objs := t.objs.insert o (.gen .running) } := by
              rw [et0]; simp [PyCore.yfStepS, pObj] at ht ⊢; simp [ht, hk']
            exact goalB_pre e0 et0' hf0 (goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp)
              (crelI_seen (A1.crel hc1 hk1)) (cov1B hf))
          | @special g g' h0 hl hS =>
            -- a generator not yet run: Surf calls `next` on it, PyCore's `yield from` asks it
            have hpend : GoalB I p H0 s0 t0 := goalB_b (.cons e0 (.nil _)) (by simp) (.cons et0' (.nil _)) (by simp)
              (pend_yf A hc hc' hk' ht hkw) (cov1B hf0)
            rcases Special.inv hS with - | - | - | ⟨U2, sb2, d2, K2, K2', h1, h2, h3, h4, hd2, hK2⟩
            · exact hpend
            · exact hpend
            · exact hpend
            · have A1 := A.push ht h0 hl f.kont (.yfGot (.gen o) :: K') hkw hs
              let s1 : Sem.Config σ := { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) }
              let t1 : PyCore.Config σ := { t with stack := g' :: { f' with ctrl := .wait, kont := .yfGot (.gen o) :: K' } :: fs', objs := t.objs.insert o (.gen .running) }
              have e1 : Sem.step I s = some s1 := by
                rw [es0]; simp [Sem.callStep, sObj] at hs ⊢; simp [s1, hs]
              have e2 : PyCore.step I t = some t1 := by
                rw [et0]; simp [PyCore.yfStepS, pObj] at ht ⊢; simp [t1, ht, hk']
              have e3 : Sem.step I s1 = some { s1 with stack := { g with ctrl := .call .next [sb2] [], kont := .yfN sb2 :: K2 } :: { f with ctrl := .wait, kont := f.kont } :: fs } := by
                simp [s1, Sem.step, h1, Sem.valStep, h2, Sem.setC]
              have hH1 : ∀ l, Seen (Touch p) H0 [s0] l → Seen (Touch p) (Seen (Touch p) H0 [s0, s]) [s1] l :=
                fun l h => .inl (seen_mono (by simp) h)
              have A2 := (A1.updS (.call .next [sb2] []) (.yfN sb2 :: K2)).mono_H hH1
              have hlt : nSusp t1 < n := by
                have : nSusp t1 < nSusp t :=
                  nSusp_run (S := g' :: { f' with ctrl := .wait, kont := .yfGot (.gen o) :: K' } :: fs') ht (A.ids.obj o _ ht)
                omega
              have IH := yf_deleg W n hlt e3 e2 hf A2 rfl rfl h3 h4 hd2 (KRel.ext ⟨hH1, Agree.refl _ _ _⟩ hK2)
              exact SimStepB.pre (.cons e0 (.cons e1 (.nil _))) (by simp) (.cons et0' (.nil _)) (by simp) (cov1B hf0) IH

/-! ### Values reaching `yield from`'s items -/

/-- Both runs are stuck after Surf's step `e1`. -/
theorem fin_stuck1 (A : At p H s t f fs f' fs') {s1 : Sem.Config σ} (e1 : Sem.step I s = some s1)
    (h1 : Sem.step I s1 = none) (h2 : PyCore.step I t = none) (hs1 : s1.stack ≠ []) (hst : s1.st = s.st)
    (hf : PyCore.focus t = none) : Goal I p H s t := by
  refine Or.inl ⟨s1, t, [s], [], .cons e1 (.nil _), h1, .nil _, h2, ?_, cov1B hf⟩
  cases hs : s1.stack with
  | nil => exact absurd hs hs1
  | cons => simp [Fin, Sem.outcome, PyCore.outcome, hs, A.ht, OCorr, A.r.out, A.r.st, hst]

/-- The step to the delegate's `next` from Surf's `call next [sb]` and PyCore's `yfStep d`. -/
theorem goal_yf (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {sb : Val} {d : PyCore.Deleg}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hd : DelegR sb d) (hk : KRel A.x U true K0 K0')
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := .call .next [sb] [], kont := .yfN sb :: K0 } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .yfStep d, kont := K0' } :: fs' })
    (hf : PyCore.focus t = none) (he : EnterSub (.yfN sb :: K0) f.kont := by esub) : Goal I p H s t :=
  (yf_deleg W _ (Nat.lt_succ_self _) e1 e2 hf ((A.zero.upd _ _ _ _ he).mono_H hH_seen) rfl rfl rfl rfl hd
    (KRel.ext ⟨hH_seen, Agree.refl _ _ _⟩ hk)).goal

theorem val_yfK (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .yfK :: K0)
    (hK' : f'.kont = .yfStart :: K0') (hk : KRel A.x U true K0 K0') : Goal I p H s t := by
  have hf : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  by_cases hv : ∃ o, v = .gen o
  · obtain ⟨o, rfl⟩ := hv
    exact goal_yf A W (.inl ⟨o, rfl, rfl⟩) hk (by sstep) (by pstep) hf
  · have hv' : ∀ o, v ≠ .gen o := fun o h => hv ⟨o, h⟩
    exact A.go11 (c := .op .iter [v]) (c' := .op .iter [v]) (k := .yfIt :: K0) (k' := .yfIt :: K0')
      (by simp only [Sem.step, A.hs, hc, Sem.valStep, hK]; simp [Sem.doOp, Sem.setC])
      (by simp only [PyCore.step, A.ht, hc', PyCore.valStep, hK']; simp [PyCore.top]) .op (.misc (.yfIt hk)) (cov_none A hf)

theorem val_yfIt (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .yfIt :: K0)
    (hK' : f'.kont = .yfIt :: K0') (hk : KRel A.x U true K0 K0') : Goal I p H s t := by
  have hf : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  by_cases hv : ∃ o, v = .gen o
  · obtain ⟨o, rfl⟩ := hv
    exact goal_yf A W (.inl ⟨o, rfl, rfl⟩) hk (by sstep) (by pstep) hf
  · have hv' : ∀ o, v ≠ .gen o := fun o h => hv ⟨o, h⟩
    exact goal_yf A W (d := .it v) (.inr ⟨hv', rfl⟩) hk (by sstep)
      (by simp only [PyCore.step, A.ht, hc', PyCore.valStep, hK']; simp [PyCore.top]) hf

/-- The delegate gave `v`: both generators are suspended inside `yield from`, the caller gets `v`. -/
theorem val_yfN (A : At p H s t f fs f' fs') {U : Label → Prop} {v sb : Val} {d : PyCore.Deleg}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .yfN sb :: K0) (hK' : f'.kont = .yfGot d :: K0') (hd : DelegR sb d) (hk : KRel A.x U true K0 K0') :
    Goal I p H s t := by
  have hf : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  let s1 : Sem.Config σ := { s with stack := { f with ctrl := .val v, kont := .yieldK :: .yfR sb :: K0 } :: fs }
  have e1 : Sem.step I s = some s1 := by simp [s1, Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
  have hkd : f'.kind = fk f.kind := A.hf.kind
  have hst := A.stk
  cases hko : f.kind
  case gen o =>
    cases fs with
    | nil =>
      cases fs' with
      | nil =>
        exact fin_stuck1 A e1 (by simp [s1, Sem.step, Sem.valStep, hko]) (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, hkd, hko, fk])
          (by simp [s1]) rfl hf
      | cons => exact hst.2.elim
    | cons g gs =>
      cases fs' with
      | nil => exact hst.2.elim
      | cons g' gs' =>
        have hko' : f'.kind = .gen o := by rw [hkd, hko]; rfl
        let fr : Sem.Frame σ := { f with ctrl := .val .none, kont := .yfR sb :: K0 }
        let fr' : PyCore.Frame σ := { f' with ctrl := .yfStep d, kont := K0' }
        have e2 : Sem.step I s1 = some { s with stack := { g with ctrl := .val v } :: gs, objs := s.objs.insert o (.gen (.susp fr)) } := by
          simp [s1, Sem.step, Sem.valStep, hko, fr]
        have e3 : PyCore.step I t = some { t with stack := { g' with ctrl := .val v } :: gs', objs := t.objs.insert o (.gen (.susp fr')) } := by
          simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, hko', fr']
        have hG : ORel p H t.glob t.cells (.gen (.susp fr)) (.gen (.susp fr')) :=
          .gen (.special (A.hf.toFRel0.upd _ _ _ _) A.hf.hl (.yf hd hk))
        have hgo : o = f'.id := (A.r.ids.gk f' (by rw [A.ht]; simp) o hko').symm
        exact ret_goal2 A rfl rfl (objs_ins A o hG)
          (hob_ins hgo fun h e => by cases e; exact ⟨hgo.symm, hko'⟩)
          (fun _ h => h.ins (insOk_gen _) fun g e => by
            cases e; refine (A.r.enter.1 f (by rw [A.hs]; exact List.mem_cons_self)).sub fun o b kx hm => ?_
            rw [hK]; simp only [fr, List.mem_cons, reduceCtorEq, false_or] at hm ⊢; exact hm) e1 e2 e3 hf
  all_goals
    exact fin_stuck1 A e1 (by simp [s1, Sem.step, Sem.valStep, hko])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, hkd, hko, fk]) (by simp [s1]) rfl hf

/-- `next` of a generator suspended inside a `yield from`: both ask the delegate again. -/
theorem _root_.Surf.T2.resume_yf {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') (W : WF p) {o : Nat} (hc : f.ctrl = .call .next [.gen o] [])
    (hc' : f'.ctrl = .call .next [.gen o] []) (hk : KRel A.x U true f.kont f'.kont)
    {g : Sem.Frame σ} {g' : PyCore.Frame σ} (ho : sObj s o = some (.gen (.susp g)))
    (ho' : pObj t o = some (.gen (.susp g'))) (h0 : FRel0 g g') (hl : ∀ S C, g.chain = S :: C → H S.label)
    {U' : Label → Prop} {sb : Val} {d : PyCore.Deleg} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hg : g.ctrl = .val .none) (hgk : g.kont = .yfR sb :: K) (hg' : g'.ctrl = .yfStep d) (hgk' : g'.kont = K')
    (hd : DelegR sb d) (hK : KRel (cx p H (rdOf t g') (ownOf t g') g) U' true K K') : GoalB I p H s t := by
  have hf : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  have A1 := A.zero.push ho' h0 hl f.kont f'.kont hk ho
  let s1 : Sem.Config σ := { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) }
  let t1 : PyCore.Config σ := { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) }
  have e1 : Sem.step I s = some s1 := by
    simp [sObj] at ho; simp [s1, Sem.step, A.hs, hc, Sem.callStep, ho]
  have e2 : PyCore.step I t = some t1 := by
    simp [pObj] at ho'; simp [t1, PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callStep, ho']
  have e3 : Sem.step I s1 = some { s1 with stack := { g with ctrl := .call .next [sb] [], kont := .yfN sb :: K } :: { f with ctrl := .wait, kont := f.kont } :: fs } := by
    simp [s1, Sem.step, hg, Sem.valStep, hgk, Sem.setC]
  have hH1 : ∀ l, H l → Seen (Touch p) (Seen (Touch p) H [s]) [s1] l := fun _ h => .inl (.inl h)
  have A2 := (A1.updS (.call .next [sb] []) (.yfN sb :: K)).mono_H hH1
  exact SimStepB.preSurf e1
    (yf_deleg W _ (Nat.lt_succ_self _) e3 e2 hf A2 rfl rfl hg' hgk' hd (KRel.ext ⟨hH1, Agree.refl _ _ _⟩ hK))

end

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-! ### A bare `except` -/

theorem goodHs_hb {C : List Scope} {U : Label → Prop} {lh : Label} {ty : Option Expr} {y : Option Name}
    {hb : List Stmt} {hs : List Handler} (h : GoodHs p C U (.mk lh ty y hb :: hs)) : GoodB p C U hb :=
  ⟨fun x hx => h.s x (by simp [itemsHs, hx]), fun x hx => h.t x (by simp [trHs, PyCore.itemsHs, hx]),
    by have := h.ok; simp only [okHs, Bool.and_eq_true] at this; exact this.1.2, fun l hl => h.u l (by simp [labelsHs, hl]),
    fun _ => h.pv (by simp), by have := h.nd; simp_all [labelsHs, List.nodup_cons, List.nodup_append],
    fun x hx => h.tch x (by simp [touchHs, hx])⟩

/-- The head of a frame whose continuation starts with a `try` is no comprehension. -/
theorem nocomp_tryE (A : At p H s t f fs f' fs') {hs : List Handler} {u : List Stmt} {K0 : List (Sem.Kont σ)}
    (hK : f.kont = .tryE hs u :: K0) : NoCompH f.chain := by
  obtain ⟨U, i, -, hk⟩ := A.hf.code
  rw [hK] at hk
  generalize f'.kont = K' at hk
  cases hk with
  | core k => cases k with | tryE hn _ _ _ => exact hn
  | call k => cases k
  | cls k => cases k
  | comp k => cases k
  | loop k => cases k
  | asg k => cases k
  | acc k => cases k
  | misc k => cases k

/-- An exception meets a bare `except` (no name): PyCore matches `$any` by the core and binds `.e`. -/
theorem raise_bare_none (A : At p H s t f fs f' fs') (W : WF p) {v : Val} {U : Label → Prop} {lh : Label}
    {hb : List Stmt} {hs : List Handler} {u : List Stmt} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hc : f.ctrl = .raise v) (hc' : f'.ctrl = .raise v) (hK : f.kont = .tryE (.mk lh none none hb :: hs) u :: K0)
    (hK' : f'.kont = .tryE (trHs f.chain (.mk lh none none hb :: hs)) (trB f.chain u) :: K0')
    (hg : GoodHs p f.chain U (.mk lh none none hb :: hs)) (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  have hn := nocomp_tryE A hK
  have hU : U lh := hg.u lh (by simp [labelsHs])
  have hfo : FOk f.chain (fresh "e" lh) :=
    fok_of (L := sub lh 0) W (hg.t _ (by simp [trHs, PyCore.itemsHs])) ⟨"e", lh, rfl⟩ (not_cmp _ _ (by omega) (by omega) (by omega))
  let x' := fresh "e" lh
  let hb' := trB f.chain hb
  let hs' := trHs f.chain hs
  let u' := trB f.chain u
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const (sub lh 1) "$any"), kont := .catchS v x' hb' hs' u' :: K0' } :: fs' }
  let t2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.bool true), kont := .catchT v x' hb' hs' u' :: K0' } :: fs' }
  have e1 : PyCore.step I t = some t1 := by
    rw [pstep_raise A.ht hc']; simp [PyCore.raiseStep, hK', trHs, PyCore.top, t1, x', hb', hs', u']
  have e2 : PyCore.step I t1 = some t2 := by
    rw [pstep_ev (t := t1) rfl rfl]
    simp [t1, t2, PyCore.evalStep, PyCore.constK, PyCore.top]
  have A2 := A.zero.updT (.val (.bool true)) (.catchT v x' hb' hs' u' :: K0')
  obtain ⟨t3, g', e3, A3, hgc, hgk, -, ha⟩ := pstore0 A2 (by decide) hfo v (.exec hb') (.handler x' v :: K0')
  have e3' : PyCore.step I t2 = some t3 := by
    rw [pstep_val (t := t2) rfl rfl]; simp only [t2, PyCore.valStep]; exact e3
  have es : Sem.step I s = some { s with stack := { f with ctrl := .exec hb, kont := .handler none v :: K0 } :: fs } := by
    simp [Sem.step, A.hs, hc, Sem.raiseStep, hK, Sem.setC]
  have ht : Touch p s lh := .inl (by simp [Sem.focus, A.hs, hc, hK, Sem.Handler.lbl])
  refine goal_b (.cons es (.nil _)) (by simp) (.cons e1 (.cons e2 (.cons e3' (.nil _)))) (by simp)
    (crelI_seen ((A3.updS (.exec hb) (.handler none v :: K0)).crel (U := U) (i := false)
      (by rw [hgc]; exact .exec (goodHs_hb hg) fun _ => hn)
      (by rw [hgk]; exact .core (.handler hn (.inr ⟨rfl, ⟨lh, rfl, hU⟩, hfo⟩)
        (krel_move hk rfl (ha.mono fun l h => h ▸ hU) fun _ h => h)))))
    (cover_of (l := lh) (by simp) ht ?_)
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · simp [PyCore.focus, A.ht, hc', hK', trHs] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t1, PyCore.focus, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t2, PyCore.focus] at hx

/-- An exception meets a bare `except`: PyCore matches `$any` by the core and binds `.e`. -/
theorem _root_.Surf.T2.raise_bare {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') (W : WF p) {v : Val} {i : Bool} (hc : f.ctrl = .raise v) (hc' : f'.ctrl = .raise v)
    (hb : BareAt A.x U i f.kont f'.kont) : Goal I p H s t := by
  obtain ⟨lh, y, hb, hs, u, K0, K0', hK, hK', hg, -, hk⟩ := hb
  cases y with
  | none => exact raise_bare_none A W hc hc' hK hK' hg hk
  | some y => exfalso; have := hg.ok; simp [okHs] at this

end

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-! ### Signals passing the items -/

theorem ssig_pops (s : Sem.Config σ) (g : Sem.Frame σ) (gs : List (Sem.Frame σ)) (ctl : Sem.Ctrl σ) (hsig : SSig ctl) :
    ∀ (Q : List (Sem.Kont σ)) (ks : List (Sem.Kont σ)), (∀ κ ∈ Q, sPlain κ = true) →
    ∃ xs, Path (Sem.step I) { s with stack := { g with ctrl := ctl, kont := Q ++ ks } :: gs }
      { s with stack := { g with ctrl := ctl, kont := ks } :: gs } xs ∧ xs.length = Q.length
  | [], ks, _ => ⟨[], .nil _, rfl⟩
  | κ :: Q, ks, hQ => by
    obtain ⟨xs, px, hl⟩ := ssig_pops s g gs ctl hsig Q ks fun κ h => hQ κ (List.mem_cons_of_mem _ h)
    exact ⟨_ :: xs, .cons (ssig_pop (g := { g with ctrl := ctl, kont := κ :: Q ++ ks }) rfl rfl rfl (hQ κ (by simp)) hsig) px,
      by simp [hl]⟩

theorem csig_s {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ} (hc : CSig i C U c c') :
    SSig c := by
  rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ <;> subst h1
  · exact .inl ⟨v, rfl⟩
  · exact .inr (.inl ⟨v, rfl⟩)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

theorem csig_p {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ} (hc : CSig i C U c c') :
    PSig c' := by
  rcases hc with ⟨v, -, h2⟩ | ⟨v, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, -, h2⟩ <;> subst h2
  · exact .inl ⟨v, rfl⟩
  · exact .inr (.inl ⟨v, rfl⟩)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))

/-- A signal passes the Surf items `Q` and the PyCore items `P`. -/
theorem sig_pops (A : At p H s t f fs f' fs') {U U0 : Label → Prop} {i i0 : Bool} {Q K0 : List (Sem.Kont σ)}
    {P K0' : List (PyCore.Kont σ)} (hc : CSig i f.chain U f.ctrl f'.ctrl) (hij : i = false → i0 = false) (hK : f.kont = Q ++ K0) (hQ : Q ≠ [])
    (hK' : f'.kont = P ++ K0') (hQp : ∀ κ ∈ Q, sPlain κ = true) (hP : ∀ κ ∈ P, pPlain κ = true)
    (hk : KRel A.x U0 i0 K0 K0') : Goal I p H s t := by
  obtain ⟨xs, px, hxl⟩ := ssig_pops (I := I) s f fs f.ctrl (csig_s hc) Q K0 hQp
  rw [← hK, s_eta A.hs] at px
  obtain ⟨ys, py, hyl, hyf⟩ := psig_pops' (I := I) A.ht rfl hK' (csig_p hc) hP
  have hr := A.set (csig_cr hc hij U0) hk
  have hxs : xs ≠ [] := by intro h; rw [h] at hxl; cases Q <;> simp_all
  by_cases hPn : P = []
  · subst hPn
    simp only [List.nil_append] at hK'
    rw [← hK', t_eta A.ht] at hr
    refine Or.inr (Or.inr (Or.inl ⟨_, xs, px, hxs, crelI_seen hr, ?_⟩))
    simp [μ, A.hs, A.ht, hK]; cases Q <;> simp_all
  · exact goal_b px hxs py (by intro h; rw [h] at hyl; cases P <;> simp_all) (crelI_seen hr) (cover_none hyf)

/-- A signal meets `yield from`'s item: a `StopIteration` gives the expression its value. -/
theorem sig_yfN (A : At p H s t f fs f' fs') {U U0 : Label → Prop} {sb : Val} {d : PyCore.Deleg}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : CSig true f.chain U f.ctrl f'.ctrl)
    (hK : f.kont = .yfN sb :: K0) (hK' : f'.kont = .yfGot d :: K0') (hk : KRel A.x U0 true K0 K0') : Goal I p H s t := by
  have hf : PyCore.focus t = none := by
    rcases hc with ⟨v, -, h2⟩ | ⟨v, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, -, h2⟩ <;> simp [PyCore.focus, A.ht, h2, hK']
  rcases hc with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ | ⟨hi, -⟩ | ⟨hi, -⟩
  · by_cases hv : Py.isStop v = true
    · exact A.go11 (c := .val (Py.stopValue v)) (c' := .val (Py.stopValue v)) (k := K0) (k' := K0')
        (by simp [Sem.step, A.hs, h1, Sem.raiseStep, hK, hv, Sem.setC])
        (by simp [PyCore.step, A.ht, h2, PyCore.raiseStep, hK', PyCore.isStop, hv, PyCore.top, PyCore.stopVal]) .val hk
        (cov_none A hf)
    · exact A.go11 (c := .raise v) (c' := .raise v) (k := K0) (k' := K0')
        (by simp [Sem.step, A.hs, h1, Sem.raiseStep, hK, hv, Sem.setC])
        (by simp [PyCore.step, A.ht, h2, PyCore.raiseStep, hK', PyCore.isStop, hv, PyCore.top]) .raise hk (cov_none A hf)
  · exact A.go11 (c := f.ctrl) (c' := f'.ctrl) (k := K0) (k' := K0')
      (by simp [Sem.step, A.hs, h1, Sem.retStep, hK, Sem.setC])
      (by simp [PyCore.step, A.ht, h2, PyCore.retStep, hK', PyCore.top])
      (by rw [h1, h2]; exact .retv) hk (cov_none A hf)
  all_goals cases hi
end

/-! ## The footprint's labels -/

/-- The node of a Surf item. -/
def itemLab : Item → Label
  | .occ l _ _ | .fn l _ _ => l

theorem mem_labelsPs_m {q : Param} : ∀ {ps : List Param}, q ∈ ps → q.label ∈ labelsPs ps
  | .mk .. :: ps, h => by
    rcases List.mem_cons.mp h with rfl | h
    · simp [labelsPs, Param.label]
    · simp [labelsPs, mem_labelsPs_m h]

set_option hygiene false in
macro "labM" : tactic => `(tactic| (
  simp only [itemsE, itemsO, itemsEs, itemsKs, itemsDs, itemsPs, itemsG1, itemsGs, itemsS, itemsHs, itemsB,
    labelsE, labelsO, labelsEs, labelsKs, labelsDs, labelsPs, labelsGs, labelsS, labelsHs, labelsB,
    List.mem_append, List.mem_cons, List.mem_map, paramOccs, Option.map, Option.toList,
    List.mem_filter, bindingAliases, List.not_mem_nil, or_false] at hj ⊢
  repeat' (first | (obtain ⟨_, hq, rfl⟩ : ∃ _, _ ∧ _ = _ := hj) | (rcases hj with hj | hj))
  all_goals first
    | (simp [itemLab]; done)
    | (subst hj; simp [itemLab]; done)
    | (simp [itemLab, mem_labelsPs_m hq]; done)
    | (simp [itemLab]; exact .inr ⟨_, hq.1, rfl⟩)
    | solve_by_elim (maxDepth := 10) [Or.inl, Or.inr]))

mutual
theorem labME : ∀ (e : Expr) (C : List Scope) (j : Item), j ∈ itemsE C e → itemLab j ∈ labelsE e
  | .const .., _, _, hj => by labM
  | .name .., _, _, hj => by labM
  | .bin _ _ a b, _, _, hj | .sub _ a b, _, _, hj => by have h1 := labME a; have h2 := labME b; labM
  | .unary _ _ a, _, _, hj | .attr _ a _, _, _, hj | .star _ a, _, _, hj | .yieldFrom _ a, _, _, hj => by
    have h1 := labME a; labM
  | .boolop _ _ es, _, _, hj | .set _ es, _, _, hj | .fstr _ es, _, _, hj | .list _ es, _, _, hj
  | .tuple _ es, _, _, hj => by have h1 := labMEs es; labM
  | .compare _ a _ es, _, _, hj => by have h1 := labME a; have h2 := labMEs es; labM
  | .ifexp _ c a b, _, _, hj => by have h1 := labME c; have h2 := labME a; have h3 := labME b; labM
  | .call _ f as ks, _, _, hj => by have h1 := labME f; have h2 := labMEs as; have h3 := labMKs ks; labM
  | .slice _ a b c, _, _, hj => by have h1 := labMO a; have h2 := labMO b; have h3 := labMO c; labM
  | .dict _ kvs, _, _, hj => by have h1 := labMDs kvs; labM
  | .lam _ ps b, _, _, hj => by have h1 := labMPs ps; have h2 := labME b; labM
  | .comp _ _ es gs, _, _, hj => by have h1 := labMEs es; have h2 := labMG1 gs; have h3 := labMGs gs; labM
  | .walrus _ _ a, _, _, hj => by have h1 := labME a; labM
  | .yield _ e, _, _, hj => by have h1 := labMO e; labM
  | .fmt _ e _ s, _, _, hj => by have h1 := labME e; have h2 := labMO s; labM
theorem labMO : ∀ (o : Option Expr) (C : List Scope) (j : Item), j ∈ itemsO C o → itemLab j ∈ labelsO o
  | none, _, _, hj => by labM
  | some e, _, _, hj => by have h1 := labME e; labM
theorem labMEs : ∀ (es : List Expr) (C : List Scope) (j : Item), j ∈ itemsEs C es → itemLab j ∈ labelsEs es
  | [], _, _, hj => by labM
  | e :: es, _, _, hj => by have h1 := labME e; have h2 := labMEs es; labM
theorem labMKs : ∀ (ks : List Kw) (C : List Scope) (j : Item), j ∈ itemsKs C ks → itemLab j ∈ labelsKs ks
  | [], _, _, hj => by labM
  | .mk _ _ e :: ks, _, _, hj => by have h1 := labME e; have h2 := labMKs ks; labM
theorem labMDs : ∀ (kvs : List DItem) (C : List Scope) (j : Item), j ∈ itemsDs C kvs → itemLab j ∈ labelsDs kvs
  | [], _, _, hj => by labM
  | .mk k v :: kvs, _, _, hj => by have h1 := labMO k; have h2 := labME v; have h3 := labMDs kvs; labM
theorem labMPs : ∀ (ps : List Param) (C : List Scope) (j : Item), j ∈ itemsPs C ps → itemLab j ∈ labelsPs ps
  | [], _, _, hj => by labM
  | .mk _ _ _ d a :: ps, _, _, hj => by have h1 := labMO d; have h2 := labMO a; have h3 := labMPs ps; labM
theorem labMG1 : ∀ (gs : List Gen) (C : List Scope) (j : Item), j ∈ itemsG1 C gs → itemLab j ∈ labelsGs gs
  | [], _, _, hj => by labM
  | .mk _ _ i _ :: _, _, _, hj => by have h1 := labME i; labM
theorem labMGs : ∀ (gs : List Gen) (C : List Scope) (f : Bool) (j : Item), j ∈ itemsGs C f gs → itemLab j ∈ labelsGs gs
  | [], _, _, _, hj => by labM
  | .mk _ t i ifs :: gs, _, true, _, hj | .mk _ t i ifs :: gs, _, false, _, hj => by
    have h1 := labME t; have h2 := labME i; have h3 := labMEs ifs; have h4 := labMGs gs; labM
end

mutual
theorem labMS : ∀ (s : Stmt) (C : List Scope) (j : Item), j ∈ itemsS C s → itemLab j ∈ labelsS s
  | .expr _ e, _, _, hj => by have h1 := labME e; labM
  | .assign _ ts e, _, _, hj => by have h1 := labMEs ts; have h2 := labME e; labM
  | .augassign _ t _ e, _, _, hj => by have h1 := labME t; have h2 := labME e; labM
  | .annassign _ t a v, _, _, hj => by have h1 := labME t; have h2 := labME a; have h3 := labMO v; labM
  | .del _ ts, _, _, hj => by have h1 := labMEs ts; labM
  | .ite _ c t u, _, _, hj | .while _ c t u, _, _, hj => by have h1 := labME c; have h2 := labMB t; have h3 := labMB u; labM
  | .for _ t it b u, _, _, hj => by
    have h1 := labME t; have h2 := labME it; have h3 := labMB b; have h4 := labMB u; labM
  | .brk .., _, _, hj | .cont .., _, _, hj | .pass .., _, _, hj => by labM
  | .ret _ e, _, _, hj => by have h1 := labMO e; labM
  | .defn _ _ ps b ds r, _, _, hj => by have h1 := labMPs ps; have h2 := labMB b; have h3 := labMEs ds; have h4 := labMO r; labM
  | .cls _ _ bs ks b ds, _, _, hj => by have h1 := labMEs bs; have h2 := labMKs ks; have h3 := labMB b; have h4 := labMEs ds; labM
  | .glob .., _, _, hj | .nonloc .., _, _, hj => by labM
  | .tryE _ b hs u, _, _, hj => by have h1 := labMB b; have h2 := labMHs hs; have h3 := labMB u; labM
  | .raise _ e c, _, _, hj => by have h1 := labMO e; have h2 := labMO c; labM
  | .imp .., _, _, hj | .impFrom .., _, _, hj => by labM
  | .assert _ t m, _, _, hj => by have h1 := labME t; have h2 := labMO m; labM
theorem labMHs : ∀ (hs : List Handler) (C : List Scope) (j : Item), j ∈ itemsHs C hs → itemLab j ∈ labelsHs hs
  | [], _, _, hj => by labM
  | .mk _ ty none b :: hs, _, _, hj | .mk _ ty (some _) b :: hs, _, _, hj => by
    have h1 := labMO ty; have h2 := labMB b; have h3 := labMHs hs; labM
theorem labMB : ∀ (ss : List Stmt) (C : List Scope) (j : Item), j ∈ itemsB C ss → itemLab j ∈ labelsB ss
  | [], _, _, hj => by labM
  | s :: ss, _, _, hj => by have h1 := labMS s; have h2 := labMB ss; labM
end


section
variable (R : Edit)

set_option hygiene false in
macro "p1M" : tactic => `(tactic| (
  intro x hx
  simp only [p1E, p1O, p1Es, p1Ks, p1Ds, p1Ps, p1Gs] at hx
  split at hx
  · exact hx
  · simp only [labelsE, labelsO, labelsEs, labelsKs, labelsDs, labelsPs, labelsGs, List.mem_append,
      List.mem_cons] at hx ⊢
    repeat' (rcases hx with hx | hx)
    all_goals solve_by_elim (maxDepth := 10) [Or.inl, Or.inr]))

set_option hygiene false in
macro "p1L" : tactic => `(tactic| (
  intro x hx
  simp only [p1Ks, p1Ds, p1Ps, p1Gs, labelsKs, labelsDs, labelsPs, labelsGs, List.mem_append, List.mem_cons] at hx ⊢
  repeat' (rcases hx with hx | hx)
  all_goals solve_by_elim (maxDepth := 10) [Or.inl, Or.inr]))

mutual
theorem p1ME : ∀ e : Expr, ∀ x ∈ p1E R e, x ∈ labelsE e
  | .const .. | .name .. => by p1M
  | .bin _ _ a b | .sub _ a b => by have h1 := p1ME a; have h2 := p1ME b; p1M
  | .unary _ _ a | .attr _ a _ | .star _ a | .yieldFrom _ a | .walrus _ _ a => by have h1 := p1ME a; p1M
  | .boolop _ _ es | .set _ es | .fstr _ es | .list _ es | .tuple _ es => by have h1 := p1MEs es; p1M
  | .compare _ a _ es => by have h1 := p1ME a; have h2 := p1MEs es; p1M
  | .ifexp _ c a b => by have h1 := p1ME c; have h2 := p1ME a; have h3 := p1ME b; p1M
  | .call _ f as ks => by have h1 := p1ME f; have h2 := p1MEs as; have h3 := p1MKs ks; p1M
  | .slice _ a b c => by have h1 := p1MO a; have h2 := p1MO b; have h3 := p1MO c; p1M
  | .dict _ kvs => by have h1 := p1MDs kvs; p1M
  | .lam _ ps b => by have h1 := p1MPs ps; have h2 := p1ME b; p1M
  | .comp _ _ es gs => by have h1 := p1MEs es; have h2 := p1MGs gs; p1M
  | .yield _ e => by have h1 := p1MO e; p1M
  | .fmt _ e _ s => by have h1 := p1ME e; have h2 := p1MO s; p1M
theorem p1MO : ∀ o : Option Expr, ∀ x ∈ p1O R o, x ∈ labelsO o
  | none => by intro x hx; simp [p1O] at hx
  | some e => by have h1 := p1ME e; intro x hx; simpa [p1O, labelsO] using h1 x hx
theorem p1MEs : ∀ es : List Expr, ∀ x ∈ p1Es R es, x ∈ labelsEs es
  | [] => by intro x hx; simp [p1Es] at hx
  | e :: es => by
    have h1 := p1ME e; have h2 := p1MEs es; intro x hx
    simp only [p1Es, labelsEs, List.mem_append] at hx ⊢; rcases hx with hx | hx
    · exact .inl (h1 x hx)
    · exact .inr (h2 x hx)
theorem p1MKs : ∀ ks : List Kw, ∀ x ∈ p1Ks R ks, x ∈ labelsKs ks
  | [] => by intro x hx; simp [p1Ks] at hx
  | .mk _ _ e :: ks => by have h1 := p1ME e; have h2 := p1MKs ks; p1L
theorem p1MDs : ∀ kvs : List DItem, ∀ x ∈ p1Ds R kvs, x ∈ labelsDs kvs
  | [] => by intro x hx; simp [p1Ds] at hx
  | .mk k v :: kvs => by have h1 := p1MO k; have h2 := p1ME v; have h3 := p1MDs kvs; p1L
theorem p1MPs : ∀ ps : List Param, ∀ x ∈ p1Ps R ps, x ∈ labelsPs ps
  | [] => by intro x hx; simp [p1Ps] at hx
  | .mk _ _ _ d a :: ps => by have h1 := p1MO d; have h2 := p1MO a; have h3 := p1MPs ps; p1L
theorem p1MGs : ∀ gs : List Gen, ∀ x ∈ p1Gs R gs, x ∈ labelsGs gs
  | [] => by intro x hx; simp [p1Gs] at hx
  | .mk _ t i ifs :: gs => by
    have h1 := p1ME t; have h2 := p1ME i; have h3 := p1MEs ifs; have h4 := p1MGs gs; p1L
end


set_option hygiene false in
macro "p1N" : tactic => `(tactic| (
  intro x hx
  simp only [p1S, p1Site] at hx
  split at hx
  · exact hx
  · simp only [labelsS, labelsO, labelsEs, labelsKs, labelsPs, labelsHs, labelsB, p1O, p1Es, p1Ks, p1Ps, p1Hs, p1B,
      List.mem_append, List.mem_cons, List.not_mem_nil] at hx ⊢
    repeat' (rcases hx with hx | hx)
    all_goals solve_by_elim (maxDepth := 10) [Or.inl, Or.inr]))

mutual
theorem p1MS : ∀ s : Stmt, ∀ x ∈ p1S R s, x ∈ labelsS s
  | .expr _ e => by have h1 := p1ME R e; p1N
  | .assign _ ts e => by have h1 := p1MEs R ts; have h2 := p1ME R e; p1N
  | .augassign _ t _ e => by have h1 := p1ME R t; have h2 := p1ME R e; p1N
  | .annassign _ t a v => by have h1 := p1ME R t; have h2 := p1ME R a; have h3 := p1MO R v; p1N
  | .del _ ts => by have h1 := p1MEs R ts; p1N
  | .ite _ c t u | .while _ c t u => by have h1 := p1ME R c; have h2 := p1MB t; have h3 := p1MB u; p1N
  | .for _ t it b u => by have h1 := p1ME R t; have h2 := p1ME R it; have h3 := p1MB b; have h4 := p1MB u; p1N
  | .ret _ e => by have h1 := p1MO R e; p1N
  | .defn _ _ ps b ds r => by
    have h1 := p1MPs R ps; have h2 := p1MB b; have h3 := p1MEs R ds; have h4 := p1MO R r; p1N
  | .cls _ _ bs ks b ds => by
    have h1 := p1MEs R bs; have h2 := p1MKs R ks; have h3 := p1MB b; have h4 := p1MEs R ds; p1N
  | .tryE _ b hs u => by have h1 := p1MB b; have h2 := p1MHs hs; have h3 := p1MB u; p1N
  | .raise _ e c => by have h1 := p1MO R e; have h2 := p1MO R c; p1N
  | .assert _ t m => by have h1 := p1ME R t; have h2 := p1MO R m; p1N
  | .brk .. | .cont .. | .pass .. | .glob .. | .nonloc .. | .imp .. | .impFrom .. => by p1N
theorem p1MHs : ∀ hs : List Handler, ∀ x ∈ p1Hs R hs, x ∈ labelsHs hs
  | [] => by intro x hx; simp [p1Hs] at hx
  | .mk l ty y b :: hs => by
    have h1 := p1MO R ty; have h2 := p1MB b; have h3 := p1MHs hs
    intro x hx
    simp only [p1Hs, List.mem_append] at hx
    rcases hx with hx | hx
    · split at hx
      · simp only [labelsHs, List.append_nil] at hx ⊢
        exact List.mem_cons.2 ((List.mem_cons.1 hx).imp id (List.mem_append_left _))
      · simp only [labelsHs, List.mem_cons, List.mem_append] at hx ⊢
        rcases hx with hx | hx
        all_goals solve_by_elim (maxDepth := 10) [Or.inl, Or.inr]
    · have := h3 x hx
      simp only [labelsHs, List.mem_cons, List.mem_append]
      solve_by_elim (maxDepth := 10) [Or.inl, Or.inr]
theorem p1MB : ∀ ss : List Stmt, ∀ x ∈ p1B R ss, x ∈ labelsB ss
  | [] => by intro x hx; simp [p1B] at hx
  | s :: ss => by
    have h1 := p1MS s; have h2 := p1MB ss; intro x hx
    simp only [p1B, labelsB, List.mem_append] at hx ⊢; rcases hx with hx | hx
    · exact .inl (h1 x hx)
    · exact .inr (h2 x hx)
end

end

/-- F_surf(p, q) holds nodes of `p` only. -/
theorem _root_.Surf.T2.inF_labels (R : Edit) (p : List Stmt) {l : Label} (h : inF R p l) : l ∈ labelsB p := by
  unfold inF footprint? at h
  split at h
  · rename_i L hL
    split at hL
    · cases hL
      rcases List.mem_append.1 h with h | h
      · exact p1MB R p l h
      · obtain ⟨j, hj, hj'⟩ := List.mem_filterMap.1 h
        have := labMB p [] j hj
        cases j with
        | occ l' x C =>
          simp only at hj'
          split at hj' <;> simp at hj'
          subst hj'; exact this
        | fn => simp at hj'
    · cases hL
  · exact h

/-! ### Chained comparisons -/

theorem nc_c (lb : Label) : NC (fresh "c" lb) := nc_fresh (by decide) lb
theorem kc_setc (I : Py.Interp σ) (lb : Label) :
    Py.constVal I (Gadget.set (fresh "c" lb)).name = .prim (Gadget.set (fresh "c" lb)).name := kc_gad I _ (nc_c lb)
theorem kc_getc (I : Py.Interp σ) (lb : Label) :
    Py.constVal I (Gadget.get (fresh "c" lb)).name = .prim (Gadget.get (fresh "c" lb)).name := kc_gad I _ (nc_c lb)
theorem on_setc (lb : Label) : Gadget.ofName (Gadget.set (fresh "c" lb)).name = some (.set (fresh "c" lb)) :=
  gad_name _ (nc_c lb)
theorem on_getc (lb : Label) : Gadget.ofName (Gadget.get (fresh "c" lb)).name = some (.get (fresh "c" lb)) :=
  gad_name _ (nc_c lb)

theorem label_mem (e : Expr) : e.label ∈ labelsE e := by cases e <;> simp [labelsE, Expr.label]

theorem goodE_up {C : List Scope} {U : Label → Prop} {lb : Label} {e : Expr} (h : GoodE p C (Rm U lb) e) :
    GoodE p C U e := ⟨h.s, h.t, h.ok, fun l hl => (h.u l hl).1, h.pv, h.nd, h.tch⟩

/-- The operands after `e` lose its node from their budget, their labels being distinct from its. -/
theorem goodEs_rm {C : List Scope} {U : Label → Prop} {e : Expr} {es : List Expr} (h : GoodEs p C U es)
    (hnd : (labelsEs (e :: es)).Nodup) : GoodEs p C (Rm U e.label) es := by
  intro e' he'
  refine (h e' he').rm fun hl => ?_
  simp only [labelsEs, List.nodup_append] at hnd
  exact hnd.2.2 _ (label_mem e) _ (labelsEs_mem he' hl) rfl

theorem nodup_tail {e : Expr} {es : List Expr} (h : (labelsEs (e :: es)).Nodup) : (labelsEs es).Nodup := by
  simp only [labelsEs, List.nodup_append] at h; exact h.2.1

theorem okName_comma {q : String} (h : okName q = true) : q ≠ "," := by
  rintro rfl; simp [okName] at h

/-- PyCore's `$get` of a comparison's middle operand (`getE l lb`): the frame's own cell. -/
theorem get_path (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (l lb : Label)
    (K : List (PyCore.Kont σ)) {b : Val} (hb : t.cells[(g.id, fresh "c" lb)]? = some b) :
    ∃ ys, Path (PyCore.step I) { t with stack := { g with ctrl := .ev (getE l lb), kont := K } :: gs }
      { t with stack := { g with ctrl := .val b, kont := K } :: gs } ys ∧ ys ≠ [] ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l := by
  obtain ⟨ys, pc, hys, hfoc⟩ := cc0_path (I := I) t g gs (sub l 4) (Gadget.get (fresh "c" lb)).name K
  rw [kc_getc] at pc
  refine ⟨ys ++ [_], pc.append (.cons ?_ (.nil _)), by simp, ?_⟩
  · simp [PyCore.step, PyCore.valStep, PyCore.callStep, on_getc, PyCore.gadgetStep, PyCore.argList, hb, PyCore.top]
  · intro y hy x hx
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
    · simp [PyCore.focus] at hx

/-- PyCore's `$set` of a comparison's middle operand: the value into the frame's own cell. -/
theorem set_path {t : PyCore.Config σ} {g : PyCore.Frame σ} {gs : List (PyCore.Frame σ)} {lb : Label}
    {K : List (PyCore.Kont σ)} {v : Val} (ht : t.stack = g :: gs) (hc : g.ctrl = .val v)
    (hk : g.kont = recK [] [] (.callA (.prim (Gadget.set (fresh "c" lb)).name) :: K)) :
    ∃ ys, Path (PyCore.step I) t
      { t with cells := t.cells.insert (g.id, fresh "c" lb) v, stack := { g with ctrl := .val v, kont := K } :: gs } ys ∧
      ys ≠ [] ∧ ∀ y ∈ ys, PyCore.focus y = none := by
  let t1 : PyCore.Config σ := { t with stack := { g with ctrl := .val (.data "$args" [v]), kont := .callA (.prim (Gadget.set (fresh "c" lb)).name) :: K } :: gs }
  refine ⟨[t, t1], .cons ?_ (.cons ?_ (.nil _)), by simp, ?_⟩
  · simp [t1, PyCore.step, ht, hc, hk, PyCore.valStep, recK, PyCore.top]
  · simp [t1, PyCore.step, PyCore.valStep, PyCore.callStep, on_setc, PyCore.gadgetStep, PyCore.argList]
  · intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · simp [PyCore.focus, ht, hc]
    · simp [t1, PyCore.focus]

theorem seenH {H : Label → Prop} {zs : List (Sem.Config σ)} {l x : Label} (hH : H l) (h : x / 64 = l) :
    Seen (Touch p) H zs (x / 64) := .inl (h ▸ hH)

theorem mem_cmpOps : ∀ (ops : List String) (L : List (Label × PE)) (q : Label × PE), q ∈ L →
    ∃ op, (op, q) ∈ cmpOps ops L
  | _, [], _, h => by simp at h
  | ops, q0 :: L, q, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨ops.headD "?", by simp [cmpOps]⟩
    · obtain ⟨op, hop⟩ := mem_cmpOps ops.tail L q h
      exact ⟨op, by simp [cmpOps, hop]⟩

theorem items_cmpChain {C : List PyCore.Scope} (l : Label) : ∀ (L : List (String × Label × PE)) (r : Label) (left : PE)
    (x : PyCore.Item), (x ∈ PyCore.itemsE R0 C left ∨ ∃ q ∈ L, x ∈ PyCore.itemsE R0 C q.2.2) →
    x ∈ PyCore.itemsE R0 C (cmpChain l r left L)
  | [], r, left, x, h => by
    rcases h with h | ⟨q, hq, _⟩
    · simp [cmpChain, ccR, recR, PyCore.itemsE, h]
    · simp at hq
  | [(op, lb, b)], r, left, x, h => by
    simp only [cmpChain, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append]
    rcases h with h | ⟨q, hq, h⟩
    · exact .inl h
    · simp at hq; subst hq; exact .inr h
  | (op, lb, b) :: q2 :: L, r, left, x, h => by
    simp only [cmpChain, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append]
    rcases h with h | ⟨q, hq, h⟩
    · exact .inl (.inl h)
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact .inl (.inr (by simp [gad, cc, ccR, recR, PyCore.itemsE, h]))
      · exact .inr (items_cmpChain l (q2 :: L) _ _ x (.inr ⟨q, hq, h⟩))

theorem goodE_cmpA {C : List Scope} {U : Label → Prop} {l a ops es} (h : GoodE p C U (.compare l a ops es)) :
    GoodE p C U a :=
  GoodE.of h (fun x hx => by simp [itemsE, hx]) (fun x hx => by simp only [trE]; exact items_cmpChain l _ _ _ x (.inl hx))
    (fun hok => by simp only [okE, Bool.and_eq_true] at hok; exact hok.1.1.1.1)
    (fun x hx => by simp [labelsE, hx]) (fun hnd => by simp only [labelsE, List.nodup_cons, List.nodup_append] at hnd; exact hnd.1.2)
    (fun x hx => by simp [touchE, hx])

theorem goodEs_cmp {C : List Scope} {U : Label → Prop} {l a ops es} (h : GoodE p C U (.compare l a ops es)) :
    GoodEs p C U es := by
  intro e he
  refine GoodE.of h (fun x hx => by simp only [itemsE, List.mem_append]; exact .inr (itemsEs_mem he hx)) (fun x hx => ?_)
    (fun hok => by simp only [okE, Bool.and_eq_true] at hok; exact okEs_mem hok.1.1.1.2 he)
    (fun x hx => by simp [labelsE, labelsEs_mem he hx])
    (fun hnd => by simp only [labelsE, List.nodup_cons, List.nodup_append] at hnd; exact nodup_labelsEs he hnd.2.1)
    (fun x hx => by simp only [touchE, List.mem_append]; exact .inr (touchEs_mem he hx))
  simp only [trE]
  obtain ⟨op, hop⟩ := mem_cmpOps ops _ _ (mem_trLs (C := C) he)
  exact items_cmpChain l _ _ _ x (.inr ⟨_, hop, hx⟩)

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem val_cmpL1 (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {o : String} {e : Expr}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .cmpL [o] [e] :: K0) (hK' : f'.kont = .binL o (trE f.chain e) :: K0')
    (hg : GoodE p f.chain U e) (hop : o ≠ ",") (hk : KRel A.x U true K0 K0') : Goal I p H s t :=
  A.go11 (c := .ev e) (k := .cmpR v o [] [] :: K0) (c' := .ev (trE f.chain e)) (k' := .binR o v :: K0')
    (by sstep) (by pstep) (.ev hg) (.misc (.cmpR1 hop hk)) (cov_none A (by simp [PyCore.focus, A.ht, hc']))

theorem val_cmpR1 (A : At p H s t f fs f' fs') {U : Label → Prop} {v a : Val} {o : String}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .cmpR a o [] [] :: K0) (hK' : f'.kont = .binR o a :: K0') (hop : o ≠ ",")
    (hk : KRel A.x U true K0 K0') : Goal I p H s t :=
  A.go11 (c := .op (.binop o) [a, v]) (k := .cmpO v [] [] :: K0) (c' := .op (.binop o) [a, v]) (k' := K0')
    (by sstep) (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, hop]) .op (.misc (.cmpONil hk))
    (cov_none A (by simp [PyCore.focus, A.ht, hc']))

theorem val_cmpONil (A : At p H s t f fs f' fs') {U : Label → Prop} {v b : Val} {es : List Expr}
    {K0 : List (Sem.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .cmpO b [] es :: K0) (hk : KRel A.x U true K0 f'.kont) : Goal I p H s t := by
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .val v, kont := K0 } :: fs } := by
    simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC]
  refine Or.inr (Or.inr (Or.inl ⟨_, [s], .cons e1 (.nil _), by simp, ?_, ?_⟩))
  · have := A.set (c := .val v) (c' := .val v) (k' := f'.kont) .val hk
    rw [← hc', t_eta A.ht] at this
    exact crelI_seen this
  · simp [μ, A.hs, A.ht, hK]

theorem val_cmpO (A : At p H s t f fs f' fs') {U : Label → Prop} {v b : Val} {l lb : Label} {ops : List String}
    {es : List Expr} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v)
    (hc' : f'.ctrl = .val v) (hK : f.kont = .cmpO b ops es :: K0)
    (hK' : f'.kont = .boolK true (cmpRest f.chain l lb ops es) :: K0') (hH : H l)
    (ho : ownOf t f' (fresh "c" lb) = some b) (hg : GoodEs p f.chain (Rm U lb) es) (hl : ops.length = es.length)
    (hne : ops ≠ []) (hq : ∀ q ∈ ops, q ≠ ",") (hnd : (labelsEs es).Nodup) (hk : KRel A.x U true K0 K0') :
    Goal I p H s t := by
  obtain ⟨o, ops', rfl⟩ := List.exists_cons_of_ne_nil hne
  exact val_tst A (v := v) (by simp [Sem.step, A.hs, hc, hK, Sem.valStep]) (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep])
    (.misc (.cmpT (r := v) hH ho hg hl hne hq hnd hk)) (by simp [PyCore.focus, A.ht, hc'])

/-- The middle operand's value: PyCore's `$set` keeps it in the frame's own cell, then both compare. -/
theorem val_cmpRm (A : At p H s t f fs f' fs') {U : Label → Prop} {v a : Val} {l lb : Label} {o : String}
    {ops : List String} {es : List Expr} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .cmpR a o ops es :: K0)
    (hK' : f'.kont = recK [] [] (.callA (.prim (Gadget.set (fresh "c" lb)).name) :: .binR o a ::
      .boolK true (cmpRest f.chain l lb ops es) :: K0'))
    (hH : H l) (hU : U lb) (hg : GoodEs p f.chain (Rm U lb) es) (hl : ops.length = es.length) (hne : ops ≠ [])
    (hq : ∀ q ∈ o :: ops, q ≠ ",") (hnd : (labelsEs es).Nodup) (hk : KRel A.x U true K0 K0') : Goal I p H s t := by
  have hop : o ≠ "," := hq o (by simp)
  let K1 : List (PyCore.Kont σ) := .binR o a :: .boolK true (cmpRest f.chain l lb ops es) :: K0'
  obtain ⟨ys, py, hys, hf⟩ := set_path (I := I) A.ht hc' hK'
  obtain ⟨A2, ho, ha⟩ := pcell0 A.zero (tag := "c") (l := lb) (by decide) v (.val v) K1
  have e3 : PyCore.step I { t with cells := t.cells.insert (f'.id, fresh "c" lb) v, stack := { f' with ctrl := .val v, kont := K1 } :: fs' } =
      some { t with cells := t.cells.insert (f'.id, fresh "c" lb) v, stack := { f' with
        ctrl := .op (.binop o) [a, v], kont := .boolK true (cmpRest f.chain l lb ops es) :: K0' } :: fs' } := by
    simp [K1, PyCore.step, PyCore.valStep, PyCore.top, hop]
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .op (.binop o) [a, v], kont := .cmpO v ops es :: K0 } :: fs } := by
    sstep
  refine goal_b (.cons e1 (.nil _)) (by simp) (py.append (.cons e3 (.nil _))) (by simp)
    (crelI_seen ((A2.upd _ _ _ _).crel (U := Rm U lb) (i := true) .op
      (.misc (.cmpO hH ho hg hl hne (fun q h => hq q (by simp [h])) hnd (krel_move hk rfl (ha.mono fun _ h => h ▸ hU) fun _ h => h))))) (cover_none ?_)
  intro y hy
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with hy | rfl
  · exact hf y hy
  · simp [PyCore.focus]

/-- The first operand of a chain: PyCore enters the `$set` of the middle operand. -/
theorem val_cmpLm (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label} {o o' : String}
    {ops : List String} {e e' : Expr} {es : List Expr} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .cmpL (o :: o' :: ops) (e :: e' :: es) :: K0)
    (hK' : f'.kont = .binL o (gad l 3 (.set (fresh "c" e.label)) [trE f.chain e]) ::
      .boolK true (cmpRest f.chain l e.label (o' :: ops) (e' :: es)) :: K0')
    (hH : H l) (hg : GoodEs p f.chain U (e :: e' :: es)) (hl : ops.length = es.length)
    (hq : ∀ q ∈ o :: o' :: ops, q ≠ ",") (hnd : (labelsEs (e :: e' :: es)).Nodup) (hk : KRel A.x U true K0 K0') :
    Goal I p H s t := by
  let K1 : List (PyCore.Kont σ) := .binR o v :: .boolK true (cmpRest f.chain l e.label (o' :: ops) (e' :: es)) :: K0'
  have e2 : PyCore.step I t = some { t with stack := { f' with
      ctrl := .ev (ccR (sub l 3) (Gadget.set (fresh "c" e.label)).name [trE f.chain e]), kont := K1 } :: fs' } := by
    simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, K1, gad, cc]
  obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 3) (Gadget.set (fresh "c" e.label)).name
    (trE f.chain e) [] K1
  rw [kc_setc] at pc
  have he := hg e (by simp)
  refine goal_b (.cons (by sstep) (.nil _)) (by simp) (.cons e2 pc) (by simp)
    (crelI_seen (A.set (.ev he) (.misc (.cmpRm (l := l) hH (he.u _ (label_mem e))
      (goodEs_rm (fun x hx => hg x (by simp [hx])) hnd) (by simp [hl]) (by simp) hq (nodup_tail hnd) hk)))) ?_
  intro y hy x hx
  rcases List.mem_cons.1 hy with rfl | hy
  · have := pfocus_le hx; simp [PyCore.focus, A.ht, hc'] at this
  · exact seenH hH (by rw [hfoc y hy x (pfocus_le hx)]; exact sub_div _ _ (by omega))

/-- The truth of a comparison of the chain: false gives its result; true goes on with the next operand,
PyCore reading the middle operand back with `$get`. -/
theorem val_cmpT (A : At p H s t f fs f' fs') {U : Label → Prop} {v r b : Val} {l lb : Label}
    {ops : List String} {es : List Expr} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .cmpT r b ops es :: K0)
    (hK' : f'.kont = .boolT true r (cmpRest f.chain l lb ops es) :: K0') (hH : H l)
    (ho : ownOf t f' (fresh "c" lb) = some b) (hg : GoodEs p f.chain (Rm U lb) es) (hl : ops.length = es.length)
    (hne : ops ≠ []) (hq : ∀ q ∈ ops, q ≠ ",") (hnd : (labelsEs es).Nodup) (hk : KRel A.x U true K0 K0') :
    Goal I p H s t := by
  have hn := cov_none A (by simp [PyCore.focus, A.ht, hc'])
  obtain ⟨o, ops', rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := by
    cases es with
    | nil => simp at hl
    | cons e es' => exact ⟨e, es', rfl⟩
  cases v
  case bool bv =>
    cases bv
    case false => exact A.go11 (c := .val r) (c' := .val r) (by sstep) (by pstep) .val hk hn
    case true =>
      have he : GoodE p f.chain U e := goodE_up (hg e (by simp))
      have hcell : t.cells[(f'.id, fresh "c" lb)]? = some b := ho
      have e1 : PyCore.step I t = some { t with stack := { f' with
          ctrl := .ev (cmpRest f.chain l lb (o :: ops') (e :: es')), kont := K0' } :: fs' } := by pstep
      cases es' with
      | nil =>
        obtain rfl : ops' = [] := by simpa using hl
        have e2 : PyCore.step I { t with stack := { f' with ctrl := .ev (cmpRest f.chain l lb [o] [e]), kont := K0' } :: fs' } =
            some { t with stack := { f' with ctrl := .ev (getE l lb), kont := .binL o (trE f.chain e) :: K0' } :: fs' } := by
          simp [cmpRest, cmpChain, cmpOps, trLs, PyCore.step, PyCore.evalStep, PyCore.top]
        obtain ⟨ys, py, hys, hfoc⟩ := get_path (I := I) t f' fs' l lb (.binL o (trE f.chain e) :: K0') hcell
        have e3 : PyCore.step I { t with stack := { f' with ctrl := .val b, kont := .binL o (trE f.chain e) :: K0' } :: fs' } =
            some { t with stack := { f' with ctrl := .ev (trE f.chain e), kont := .binR o b :: K0' } :: fs' } := by
          simp [PyCore.step, PyCore.valStep, PyCore.top]
        refine goal_b (.cons (by sstep) (.nil _)) (by simp) (.cons e1 (.cons e2 (py.append (.cons e3 (.nil _)))))
          (by simp) (crelI_seen (A.set (.ev he) (.misc (.cmpR1 (hq o (by simp)) hk)))) ?_
        intro y hy x hx
        have hx' := pfocus_le hx
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | hy | rfl
        · simp [PyCore.focus, A.ht, hc'] at hx'
        · simp [PyCore.focus, cmpRest, cmpChain, cmpOps, trLs, PyCore.Expr.label] at hx'
          exact seenH hH (by rw [← hx']; exact sub_div _ _ (by omega))
        · exact seenH hH (hfoc y hy x hx')
        · simp [PyCore.focus] at hx'
      | cons e2 es2 =>
        obtain ⟨o2, ops2, rfl⟩ : ∃ o2 ops2, ops' = o2 :: ops2 := by
          cases ops' with
          | nil => simp at hl
          | cons o2 ops2 => exact ⟨o2, ops2, rfl⟩
        let SET : PE := ccR (sub l 3) (Gadget.set (fresh "c" e.label)).name [trE f.chain e]
        let REST : PE := cmpRest f.chain l e.label (o2 :: ops2) (e2 :: es2)
        let K1 : List (PyCore.Kont σ) := .boolK true REST :: K0'
        have e2' : PyCore.step I { t with stack := { f' with
            ctrl := .ev (cmpRest f.chain l lb (o :: o2 :: ops2) (e :: e2 :: es2)), kont := K0' } :: fs' } =
            some { t with stack := { f' with ctrl := .ev (.bin (sub l 2) o (getE l lb) SET), kont := K1 } :: fs' } := by
          simp [cmpRest, cmpChain, cmpOps, trLs, PyCore.step, PyCore.evalStep, PyCore.top, K1, REST, SET, getE, gad, cc]
        have e3 : PyCore.step I { t with stack := { f' with ctrl := .ev (.bin (sub l 2) o (getE l lb) SET), kont := K1 } :: fs' } =
            some { t with stack := { f' with ctrl := .ev (getE l lb), kont := .binL o SET :: K1 } :: fs' } := by
          simp [PyCore.step, PyCore.evalStep, PyCore.top]
        obtain ⟨ys, py, hys, hfoc⟩ := get_path (I := I) t f' fs' l lb (.binL o SET :: K1) hcell
        have e4 : PyCore.step I { t with stack := { f' with ctrl := .val b, kont := .binL o SET :: K1 } :: fs' } =
            some { t with stack := { f' with ctrl := .ev SET, kont := .binR o b :: K1 } :: fs' } := by
          simp [PyCore.step, PyCore.valStep, PyCore.top]
        obtain ⟨zs, pc, hzs, hfc⟩ := cc_enter (I := I) t f' fs' (sub l 3) (Gadget.set (fresh "c" e.label)).name
          (trE f.chain e) [] (.binR o b :: K1)
        rw [kc_setc] at pc
        have hg' : GoodEs p f.chain U (e :: e2 :: es2) := fun x hx => goodE_up (hg x hx)
        refine goal_b (.cons (by sstep) (.nil _)) (by simp)
          (.cons e1 (.cons e2' (.cons e3 (py.append (.cons e4 pc))))) (by simp)
          (crelI_seen (A.set (.ev he) (.misc (.cmpRm (l := l) hH (he.u _ (label_mem e))
            (goodEs_rm (fun x hx => hg' x (by simp [hx])) hnd) (by simpa using hl) (by simp) hq (nodup_tail hnd) hk)))) ?_
        intro y hy x hx
        have hx' := pfocus_le hx
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | hy | rfl | hy
        · simp [PyCore.focus, A.ht, hc'] at hx'
        · simp [PyCore.focus, cmpRest, cmpChain, cmpOps, trLs, PyCore.Expr.label] at hx'
          exact seenH hH (by rw [← hx']; exact sub_div _ _ (by omega))
        · simp [PyCore.focus, PyCore.Expr.label] at hx'
          exact seenH hH (by rw [← hx']; exact sub_div _ _ (by omega))
        · exact seenH hH (hfoc y hy x hx')
        · simp [PyCore.focus] at hx'
        · exact seenH hH (by rw [hfc y hy x hx']; exact sub_div _ _ (by omega))
  all_goals exact fin_stuck A (by sstep) (by pstep) hn

end

/-! ### `from … import` -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem cv_raiseImport (I : Py.Interp σ) :
    Py.constVal I (Gadget.raiseK "ImportError").name = .prim (Gadget.raiseK "ImportError").name :=
  kc_gad I _ (by simp [GOk, NC])
theorem on_raiseImport : Gadget.ofName (Gadget.raiseK "ImportError").name = some (.raiseK "ImportError") :=
  gad_name _ (by simp [GOk, NC])

/-- A relative `from . import …` (no module system): both raise `ImportError`. -/
theorem exec_impFrom_rel (A : At p H s t f fs f' fs') {l : Label} {m : Option String} {al : List Alias} {lvl : Nat}
    {U : Label → Prop} {ss : List Stmt} (hlvl : lvl > 0) (hc : f.ctrl = .exec (.impFrom l m al lvl :: ss))
    (hc' : f'.ctrl = .exec (trB f.chain (.impFrom l m al lvl :: ss)))
    (hg : GoodB p f.chain U (.impFrom l m al lvl :: ss)) (hn : NoCompH f.chain) (hk : KRel A.x U false f.kont f'.kont) :
    Goal I p H s t := by
  let D : PyCore.Stmt := dead (sub l 3) ((bindingAliases al).map fun a =>
    .assign (sub a.l 0) (mangle (priv f.chain) a.bound) (.const (sub a.l 1) "$none"))
  let K1 : List (PyCore.Kont σ) := .tryE [] [] :: .seq (trB f.chain ss) :: f'.kont
  let K2 : List (PyCore.Kont σ) := .exprS :: .seq [D] :: K1
  let X : Val := exc (f :: fs) (Py.err "ImportError")
  let t1 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .exec [.expr (sub l 1) (gad l 2 (.raiseK "ImportError") []), D], kont := K1 } :: fs' }
  have st0 : PyCore.step I t = some t1 := by
    rw [pstep_exec A.ht (by rw [hc']; rfl)]; simp [trS, hlvl, blk, PyCore.execStep, PyCore.top, t1, K1, D]
  have st1 : PyCore.step I t1 = some { t with stack := { f' with
      ctrl := .ev (ccR (sub l 2) (Gadget.raiseK "ImportError").name []), kont := K2 } :: fs' } := by
    rw [pstep_exec (t := t1) rfl rfl]; rfl
  obtain ⟨ys, pc, hys, hfoc⟩ := cc0_path (I := I) t f' fs' (sub l 2) (Gadget.raiseK "ImportError").name K2
  have he : PyCore.kontExc K2 = Sem.kontExc f.kont := by
    simp only [K2, K1, PyCore.kontExc]; exact KRel.kexc hk
  let t5 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" []), kont := .callA (Py.constVal I (Gadget.raiseK "ImportError").name) :: K2 } :: fs' }
  have st5 : PyCore.step I t5 = some { t with stack := { f' with ctrl := .raise X, kont := [.exprS, .seq [D], .tryE [] []] ++ .seq (trB f.chain ss) :: f'.kont } :: fs' } := by
    rw [pstep_val (t := t5) rfl rfl]
    simp only [PyCore.valStep]
    rw [cv_raiseImport]
    simp only [PyCore.callStep, on_raiseImport, PyCore.gadgetStep, PyCore.argList, PyCore.top]
    rw [raiseNew_top (g' := { f' with ctrl := .val (.data "$args" []), kont := K2 }) A.stk.2 he]
    rfl
  have hts : Touch p s l := touch_exec A.hs hc
  refine goal_raise A (X := X) (P := [.exprS, .seq [D], .tryE [] []])
    (by simp [Sem.step, A.hs, hc, Sem.execStep, hlvl, Sem.setC, Sem.raiseNew, X, exc])
    (.cons st0 (.cons st1 (pc.append (.cons st5 (.nil _))))) (by simp) (by simp [pPlain])
    (krel_seq hn hg.tail hk) (cover_of (l := l) (by simp) hts ?_)
  intro y hy x hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | hy | rfl
  · simp [PyCore.focus, A.ht, hc', trB, trS, hlvl, blk, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t1, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
  · simp [t5, PyCore.focus] at hx

theorem str_import1 (M : String) : s!"$op:import:{M}:1" = s!"$op:import:{M}:{if true then 1 else 0}" := by
  simp [String.append_assoc]; decide

theorem from_nodot (W : WF p) {C : List Scope} {U : Label → Prop} {l : Label} {m : Option String} {al : List Alias}
    {lvl : Nat} {ss : List Stmt} (hg : GoodB p C U (.impFrom l m al lvl :: ss)) {a : Alias} (ha : a ∈ al)
    (hn : a.name ≠ "*") : ¬ Dot (mangle (priv C) a.bound) :=
  W.nodot a.l _ C (hg.s _ (by
    simp only [itemsB, itemsS, bindingAliases, List.mem_append, List.mem_map, List.mem_filter]
    exact .inl ⟨a, ⟨ha, by simpa using hn⟩, rfl⟩))

/-- `from m import …`: both import the module, which PyCore then stores in `.m l`. -/
theorem exec_impFrom_mod (A : At p H s t f fs f' fs') (W : WF p) {l : Label} {m : Option String} {al : List Alias}
    {U : Label → Prop} {ss : List Stmt} (hc : f.ctrl = .exec (.impFrom l m al 0 :: ss))
    (hc' : f'.ctrl = .exec (trB f.chain (.impFrom l m al 0 :: ss)))
    (hg : GoodB p f.chain U (.impFrom l m al 0 :: ss)) (hn : NoCompH f.chain) (hk : KRel A.x U false f.kont f'.kont) :
    Goal I p H s t := by
  have hok := hg.ok
  simp only [okB, okS, Bool.and_eq_true] at hok
  have hm : okPath (m.getD "") = true := by cases m <;> simp_all [okPath]
  have hal : ∀ a ∈ al, okAl a = true := by simpa using hok.1.1.2
  let M : String := s!"$op:import:{m.getD ""}:1"
  let K1 : List (PyCore.Kont σ) := .tryE [] [] :: .seq (trB f.chain ss) :: f'.kont
  let K2 : List (PyCore.Kont σ) := .assign (fresh "m" l) :: .seq (al.map (fromS f.chain l)) :: K1
  let t1 : PyCore.Config σ := { t with stack := { f' with
    ctrl := .exec (.assign (sub l 1) (fresh "m" l) (cc l 2 M []) :: al.map (fromS f.chain l)), kont := K1 } :: fs' }
  have st0 : PyCore.step I t = some t1 := by
    rw [pstep_exec A.ht (by rw [hc']; rfl)]; rfl
  have st1 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .ev (ccR (sub l 2) M []), kont := K2 } :: fs' } := by
    rw [pstep_exec (t := t1) rfl rfl]; rfl
  obtain ⟨ys, pc, hys, hfoc⟩ := cc0_path (I := I) t f' fs' (sub l 2) M K2
  have hM : Py.constVal I M = .op (.import (m.getD "") true) := by
    simp only [M]; rw [str_import1]; exact kc_import I (nc_path hm) true
  rw [hM] at pc
  have st5 : PyCore.step I { t with stack := { f' with ctrl := .val (.data "$args" []), kont := .callA (.op (.import (m.getD "") true)) :: K2 } :: fs' } =
      some { t with stack := { f' with ctrl := .op (.import (m.getD "") true) [], kont := K2 } :: fs' } := by
    rw [pstep_val rfl rfl]; simp [PyCore.valStep, PyCore.callStep, PyCore.top, PyCore.argList]
  have hU : U l := hg.u l (by simp [labelsB, labelsS])
  have hfo : FOk f.chain (fresh "m" l) :=
    fok_of (L := sub l 1) W (hg.t _ (by simp [trB, trS, blk, PyCore.itemsB, PyCore.itemsS]))
      ⟨"m", l, rfl⟩ (not_cmp _ _ (by omega) (by omega) (by omega))
  have hts : Touch p s l := touch_exec A.hs hc
  refine goal_b (.cons (by simp [Sem.step, A.hs, hc, Sem.execStep, Sem.doOp, Sem.setC]) (.nil _)) (by simp)
    (.cons st0 (.cons st1 (pc.append (.cons st5 (.nil _))))) (by simp)
    (crelI_seen (A.set .op (.misc (.impMod hU hfo hal (fun a ha hs => from_nodot W hg ha hs) (krel_seq hn hg.tail hk)))))
    (cover_of (l := l) (by simp) hts ?_)
  intro y hy x hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | hy | rfl
  · simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t1, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
  · simp [PyCore.focus] at hx

/-- A value reaches `from … import`'s module item: PyCore keeps the module in `.m l`. -/
theorem val_impMod (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {l : Label} {al : List Alias}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .impMod al :: K0)
    (hK' : f'.kont = .assign (fresh "m" l) :: .seq (al.map (fromS f.chain l)) :: .tryE [] [] :: K0')
    (hU : U l) (hfo : FOk f.chain (fresh "m" l)) (hok : ∀ a ∈ al, okAl a = true)
    (hnd : ∀ a ∈ al, a.name ≠ "*" → ¬ Dot (mangle (priv f.chain) a.bound)) (hk : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  let K1 : List (PyCore.Kont σ) := .seq (al.map (fromS f.chain l)) :: .tryE [] [] :: K0'
  obtain ⟨t1, g', e2, A1, hgc, hgk, hrd, ha⟩ := pstore0 A.zero (tag := "m") (l := l) (by decide) hfo v (.exec []) K1
  have et : PyCore.step I t = some t1 := by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2
  have es : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := .impNext v al :: K0 } :: fs } := by
    sstep
  refine goal_b (.cons es (.nil _)) (by simp) (.cons et (.nil _)) (by simp)
    (crelI_seen ((A1.updS (.exec []) (.impNext v al :: K0)).crel (U := Rm U l) (i := false)
      (by rw [hgc]; exact .exec (goodB_nil _ _) (by simp))
      (by rw [hgk]; exact .misc (.impNext hrd hok hnd (krel_move hk rfl (ha.mono fun _ h => h ▸ hU) fun _ h => h)))))
    (cover_none fun y hy => by simp at hy; subst hy; simp [PyCore.focus, A.ht, hc'])

/-- Both runs end after Surf's none and PyCore's one step. -/
theorem fin_stuckP (A : At p H s t f fs f' fs') {t1 : PyCore.Config σ} (h1 : Sem.step I s = none)
    (e2 : PyCore.step I t = some t1) (h2 : PyCore.step I t1 = none) (hs1 : t1.stack ≠ []) (hst : t1.st = t.st)
    (hout : t1.out = t.out) (hf : PyCore.focus t = none) (hf1 : PyCore.focus t1 = none) : Goal I p H s t := by
  refine .inl ⟨s, t1, [], [t], .nil _, h1, .cons e2 (.nil _), h2, ?_, cover_none fun y hy => ?_⟩
  · cases ht1 : t1.stack with
    | nil => exact absurd ht1 hs1
    | cons => simp [Fin, Sem.outcome, PyCore.outcome, A.hs, ht1, OCorr, hst, hout, A.r.out, A.r.st]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hf1
    · exact hf

def nd (kvs : List (Name × Val)) : List (Name × Val) := kvs.filter (fun p => !p.1.startsWith ".")

theorem nd_nodot {kvs : List (Name × Val)} : ∀ q ∈ nd kvs, ¬ Dot q.1 := by
  intro q hq h
  simp only [nd, List.mem_filter, Bool.not_eq_true'] at hq
  have := (startsWith_dot q.1).2 h
  simp_all

theorem gmatch_fold (g0 : Name → Option Val) : ∀ (kvs : List (Name × Val)) (W : Std.HashMap Name (Option Val))
    (G : Std.HashMap Name Val), (∀ x, ¬ Dot x → (match W[x]? with | some ov => ov | none => g0 x) = G[x]?) →
    ∀ x, ¬ Dot x → (match (kvs.foldl (fun g p => g.insert p.1 (some p.2)) W)[x]? with | some ov => ov | none => g0 x) =
      (kvs.foldl (fun g p => g.insert p.1 p.2) G)[x]?
  | [], _, _, h => h
  | (k, w) :: kvs, W, G, h => by
    refine gmatch_fold g0 kvs _ _ fun x hx => ?_
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
    by_cases e : k = x
    · simp [e]
    · simp only [e, ite_false]; exact h x hx

theorem fold_dot : ∀ (kvs : List (Name × Val)) (W : Std.HashMap Name (Option Val)), (∀ q ∈ kvs, ¬ Dot q.1) →
    ∀ x, Dot x → (kvs.foldl (fun g p => g.insert p.1 (some p.2)) W)[x]? = W[x]?
  | [], _, _, _, _ => rfl
  | (k, w) :: kvs, W, h, x, hx => by
    rw [List.foldl_cons, fold_dot kvs _ (fun q hq => h q (by simp [hq])) x hx, Std.HashMap.getElem?_insert]
    have : k ≠ x := fun e => h (k, w) (by simp) (e ▸ hx)
    simp [this]

theorem drop_fold : ∀ (kvs : List (Name × Val)) (ns : List (Name × Val)), (∀ q ∈ kvs, ¬ Dot q.1) →
    PyCore.dropReserved (kvs.foldl (fun n p => PyCore.nsSet n p.1 (some p.2)) ns) =
      kvs.foldl (fun n p => Sem.nsSet n p.1 (some p.2)) (PyCore.dropReserved ns)
  | [], _, _ => rfl
  | (k, w) :: kvs, ns, h => by
    rw [List.foldl_cons, List.foldl_cons, drop_fold kvs _ (fun q hq => h q (by simp [hq])),
      drop_nsSet k (h (k, w) (by simp))]

theorem lookup_fold : ∀ (kvs : List (Name × Val)) (ns : List (Name × Val)), (∀ q ∈ kvs, ¬ Dot q.1) →
    ∀ x, Dot x → (kvs.foldl (fun n p => PyCore.nsSet n p.1 (some p.2)) ns).lookup x = ns.lookup x
  | [], _, _, _, _ => rfl
  | (k, w) :: kvs, ns, h, x, hx => by
    rw [List.foldl_cons, lookup_fold kvs _ (fun q hq => h q (by simp [hq])) x hx]
    exact lookup_nsSet_ne (fun e : x = k => h (k, w) (by simp) (by simpa [← e] using hx)) ns _

/-- `from m import *`'s names (but the reserved ones) into the module dictionary or the class namespace. -/
theorem val_starStore (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .starStore :: K0)
    (hK' : f'.kont = recK [] [] (.callA (.prim Gadget.starstore.name) :: .exprS :: K0')) (hk : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  let KS : List (PyCore.Kont σ) := .exprS :: K0'
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" [v]), kont := .callA (.prim Gadget.starstore.name) :: KS } :: fs' }
  have e1 : PyCore.step I t = some t1 := by simp [t1, KS, PyCore.step, A.ht, hc', hK', PyCore.valStep, recK, PyCore.top]
  have hf : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  have hf1 : PyCore.focus t1 = none := by simp [t1, PyCore.focus]
  have hgs : Gadget.ofName Gadget.starstore.name = some .starstore := gad_name _ trivial
  have hstuck : Sem.step I s = none → PyCore.step I t1 = none → Goal I p H s t :=
    fun h1 h2 => fin_stuckP A h1 e1 h2 (by simp [t1]) rfl rfl hf hf1
  have hkd : f'.kind = fk f.kind := A.hf.kind
  cases v
  case tuple ps =>
    cases hp : Py.kwPairs ps with
    | none =>
      exact hstuck (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hp])
        (by simp [t1, PyCore.step, PyCore.valStep, PyCore.callStep, hgs, PyCore.gadgetStep, PyCore.argList, hp])
    | some kvs0 =>
      have hnd := nd_nodot (kvs := kvs0)
      cases hkf : f.kind
      case mod =>
        let W' := (nd kvs0).foldl (fun g p => g.insert p.1 (some p.2)) t.globW
        let G' := (nd kvs0).foldl (fun g p => g.insert p.1 p.2) s.glob
        let s1 : Sem.Config σ := { s with glob := G', stack := { f with ctrl := .exec [], kont := K0 } :: fs }
        let t2 : PyCore.Config σ := { t with globW := W', stack := { f' with ctrl := .val .none, kont := KS } :: fs' }
        let t3 : PyCore.Config σ := { t with globW := W', stack := { f' with ctrl := .exec [], kont := K0' } :: fs' }
        have es : Sem.step I s = some s1 := by simp [s1, G', nd, Sem.step, A.hs, hc, hK, Sem.valStep, hp, hkf]
        have e2 : PyCore.step I t1 = some t2 := by
          simp [t1, t2, W', nd, PyCore.step, PyCore.valStep, PyCore.callStep, hgs, PyCore.gadgetStep, PyCore.argList, hp,
            hkd, hkf, fk, PyCore.starGlob]
        have e3 : PyCore.step I t2 = some t3 := by simp [t2, t3, PyCore.step, PyCore.valStep, PyCore.top, KS]
        have hdot : ∀ x, Dot x → t3.glob x = t.glob x := fun x hx => by
          simp only [PyCore.Config.glob, t3, W']; rw [fold_dot _ t.globW hnd x hx]
        have A3 : At0 p H s1 t3 { f with ctrl := .exec [], kont := K0 } fs { f' with ctrl := .exec [], kont := K0' } fs' :=
          A.zero.write rfl rfl (A.hf.toFRel0.upd _ _ _ _) rfl rfl rfl rfl rfl A.zero.cells
            (fun x hx => gmatch_fold t.glob0 _ t.globW s.glob (fun y hy => A.zero.glob y hy) x hx)
            (fun h' _ => agree_nd h' _ hdot fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl
        refine goal_b (.cons es (.nil _)) (by simp) (.cons e1 (.cons e2 (.cons e3 (.nil _)))) (by simp)
          (crelI_seen (A3.crel (U := U) (i := false) (.exec (goodB_nil _ _) (by simp))
            (krel_move hk rfl (agree_nd f' U hdot fun _ _ => rfl) fun _ h => h))) (cover_none fun y hy => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · exact hf
        · exact hf1
        · simp [t2, PyCore.focus]
      case cls =>
        let NS := (nd kvs0).foldl (fun n p => Sem.nsSet n p.1 (some p.2)) f.ns
        let NS' := (nd kvs0).foldl (fun n p => PyCore.nsSet n p.1 (some p.2)) f'.ns
        let s1 : Sem.Config σ := { s with stack := { f with ns := NS, ctrl := .exec [], kont := K0 } :: fs }
        let t2 : PyCore.Config σ := { t with stack := { f' with ns := NS', ctrl := .val .none, kont := KS } :: fs' }
        let t3 : PyCore.Config σ := { t with stack := { f' with ns := NS', ctrl := .exec [], kont := K0' } :: fs' }
        have es : Sem.step I s = some s1 := by simp [s1, NS, nd, Sem.step, A.hs, hc, hK, Sem.valStep, hp, hkf, Sem.setC]
        have e2 : PyCore.step I t1 = some t2 := by
          simp [t1, t2, NS', nd, PyCore.step, PyCore.valStep, PyCore.callStep, hgs, PyCore.gadgetStep, PyCore.argList, hp,
            hkd, hkf, fk, PyCore.starNs, PyCore.top]
        have e3 : PyCore.step I t2 = some t3 := by simp [t2, t3, PyCore.step, PyCore.valStep, PyCore.top, KS]
        have hf0 := A.hf
        have A3 : At0 p H s1 t3 { f with ns := NS, ctrl := .exec [], kont := K0 } fs
            { f' with ns := NS', ctrl := .exec [], kont := K0' } fs' :=
          A.zero.write rfl rfl ⟨hf0.id, hf0.chain, hf0.cls, hf0.pcls, hf0.kind, hf0.kc, hf0.κ, hf0.κa,
              by simp only [NS, NS']; rw [drop_fold _ f'.ns hnd, hf0.ns], hf0.kok⟩ rfl rfl rfl rfl rfl A.zero.cells
            A.zero.glob (fun h' _ => Agree.refl _ _ _) rfl rfl rfl rfl rfl rfl rfl
        have ha : Agree U (rdOf t f') (ownOf t f') (rdOf t3 { f' with ns := NS', ctrl := .exec [], kont := K0' })
            (ownOf t3 { f' with ns := NS', ctrl := .exec [], kont := K0' }) :=
          agree_of (P := fun y => ¬ Dot y) (fun tag l _ _ h => h (dot_fresh tag l))
            (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun _ z hz =>
              lookup_fold _ f'.ns hnd z (Classical.not_not.1 hz))
        refine goal_b (.cons es (.nil _)) (by simp) (.cons e1 (.cons e2 (.cons e3 (.nil _)))) (by simp)
          (crelI_seen (A3.crel (U := U) (i := false) (.exec (goodB_nil _ _) (by simp))
            (krel_move hk rfl ha fun _ h => h))) (cover_none fun y hy => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · exact hf
        · exact hf1
        · simp [t2, PyCore.focus]
      all_goals
        exact hstuck (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hp, hkf])
          (by simp [t1, PyCore.step, PyCore.valStep, PyCore.callStep, hgs, PyCore.gadgetStep, PyCore.argList, hp, hkd, hkf, fk])
  all_goals
    exact hstuck (by simp [Sem.step, A.hs, hc, hK, Sem.valStep])
      (by simp [t1, PyCore.step, PyCore.valStep, PyCore.callStep, hgs, PyCore.gadgetStep, PyCore.argList])

/-- PyCore reads a fresh name into an operation's record: the operation on its value. -/
theorem name_op_path (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (r : Label) (x : Name)
    (o : Py.Op) (K : List (PyCore.Kont σ)) {m : Val} (hm : rdOf t g x = some m) :
    ∃ ys, Path (PyCore.step I) { t with stack := { g with ctrl := .ev (.name r x none), kont := recK [] [] (.callA (.op o) :: K) } :: gs }
      { t with stack := { g with ctrl := .op o [m], kont := K } :: gs } ys ∧
      ∀ y ∈ ys, ∀ z, PyCore.focus y = some z → z = r := by
  let K1 : List (PyCore.Kont σ) := recK [] [] (.callA (.op o) :: K)
  let g1 : PyCore.Frame σ := { g with ctrl := .ev (.name r x none), kont := K1 }
  let t1 : PyCore.Config σ := { t with stack := g1 :: gs }
  let t2 : PyCore.Config σ := { t with stack := { g with ctrl := .val m, kont := K1 } :: gs }
  let t3 : PyCore.Config σ := { t with stack := { g with ctrl := .val (.data "$args" [m]), kont := .callA (.op o) :: K } :: gs }
  have hr : PyCore.readName I t1 g1 x none = .ok m := readName_rd hm
  refine ⟨[t1, t2, t3], .cons ?_ (.cons ?_ (.cons ?_ (.nil _))), ?_⟩
  · rw [pstep_ev (e := .name r x none) (t := t1) rfl rfl]
    show PyCore.top t1 gs { g1 with ctrl := PyCore.resCtrl (g1 :: gs) (PyCore.readName I t1 g1 x none) } = _
    rw [hr]; rfl
  · simp [t2, t3, K1, recK, PyCore.step, PyCore.valStep, PyCore.top]
  · simp [t3, PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, PyCore.top]
  · intro y hy z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · simp [t1, g1, PyCore.focus, PyCore.Expr.label] at hz; exact hz.symm
    · simp [t2, PyCore.focus] at hz
    · simp [t3, PyCore.focus] at hz

/-- The binding of an alias of `from … import` ended (or the module was stored): the next alias. -/
theorem done_impNext (A : At p H s t f fs f' fs') {U : Label → Prop} {l : Label} {m : Val} {al : List Alias}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .exec []) (hc' : f'.ctrl = .exec [])
    (hK : f.kont = .impNext m al :: K0) (hK' : f'.kont = .seq (al.map (fromS f.chain l)) :: .tryE [] [] :: K0')
    (hrd : rdOf t f' (fresh "m" l) = some m) (hok : ∀ a ∈ al, okAl a = true)
    (hnd : ∀ a ∈ al, a.name ≠ "*" → ¬ Dot (mangle (priv f.chain) a.bound))
    (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  have hf0 : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  cases al with
  | nil =>
    let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .exec [], kont := .tryE [] [] :: K0' } :: fs' }
    have e1 : PyCore.step I t = some t1 := by simp [t1, PyCore.step, A.ht, hc', hK', PyCore.doneStep, PyCore.top]
    have e2 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .exec [], kont := K0' } :: fs' } := by
      simp [t1, PyCore.step, PyCore.doneStep, PyCore.top]
    refine goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]) (.nil _)) (by simp)
      (.cons e1 (.cons e2 (.nil _))) (by simp) (crelI_seen (A.set (.exec (goodB_nil _ U) (by simp)) hk))
      (cover_none fun y hy => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact hf0
    · simp [t1, PyCore.focus]
  | cons a al =>
    have hts : Touch p s a.l := .inr (by simp [A.hs, TouchF, hc, hK])
    have ha := hok a (by simp)
    have hok' : ∀ b ∈ al, okAl b = true := fun b hb => hok b (by simp [hb])
    have hnd' : ∀ b ∈ al, b.name ≠ "*" → ¬ Dot (mangle (priv f.chain) b.bound) := fun b hb => hnd b (by simp [hb])
    let R : PS := al.map (fromS f.chain l)
    have e1 : PyCore.step I t = some { t with stack := { f' with ctrl := .exec (fromS f.chain l a :: R), kont := .tryE [] [] :: K0' } :: fs' } := by
      simp [R, PyCore.step, A.ht, hc', hK', PyCore.doneStep, PyCore.top]
    have hm : rdOf t f' (fresh "m" l) = some m := hrd
    by_cases hs : a.name = "*"
    · -- `from m import *`
      let KB : List (PyCore.Kont σ) := .exprS :: .seq R :: .tryE [] [] :: K0'
      have e2 : PyCore.step I { t with stack := { f' with ctrl := .exec (fromS f.chain l a :: R), kont := .tryE [] [] :: K0' } :: fs' } =
          some { t with stack := { f' with ctrl := .ev (ccR (sub a.l 1) Gadget.starstore.name [cc a.l 2 "$op:importStar" [nm a.l 3 (fresh "m" l)]]), kont := KB } :: fs' } := by
        rw [pstep_exec rfl rfl]; simp [fromS, hs, PyCore.execStep, PyCore.top, KB, gad, cc]
      obtain ⟨ys1, p1, -, hf1⟩ := cc_enter (I := I) t f' fs' (sub a.l 1) Gadget.starstore.name
        (cc a.l 2 "$op:importStar" [nm a.l 3 (fresh "m" l)]) [] KB
      rw [kc_gad I .starstore trivial] at p1
      let KC : List (PyCore.Kont σ) := recK [] [] (.callA (.prim Gadget.starstore.name) :: KB)
      obtain ⟨ys2, p2, -, hf2⟩ := cc_enter (I := I) t f' fs' (sub a.l 2) "$op:importStar" (nm a.l 3 (fresh "m" l)) [] KC
      rw [kc_importStar] at p2
      obtain ⟨ys3, p3, hf3⟩ := name_op_path (I := I) t f' fs' (sub a.l 3) (fresh "m" l) .importStar KC hm
      have es : Sem.step I s = some { s with stack := { f with ctrl := .op .importStar [m], kont := .starStore :: .impNext m al :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.doneStep, hs, Sem.doOp, Sem.setC]
      refine goal_b (.cons es (.nil _)) (by simp) (.cons e1 (.cons e2 (p1.append (p2.append p3)))) (by simp)
        (crelI_seen (A.set .op (.misc (.starStore (.misc (.impNext hrd hok' hnd' hk)))))) (cover_of (l := a.l) (by simp) hts ?_)
      intro y hy x hx
      simp only [List.mem_cons, List.mem_append] at hy
      rcases hy with rfl | rfl | hy | hy | hy
      · simp [PyCore.focus, A.ht, hc'] at hx
      · simp [fromS, hs, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
      · rw [hf1 y hy x hx]; exact sub_div _ _ (by omega)
      · rw [hf2 y hy x hx]; exact sub_div _ _ (by omega)
      · rw [hf3 y hy x hx]; exact sub_div _ _ (by omega)
    · -- `from m import a as b`
      let y := mangle (priv f.chain) a.bound
      let KA : List (PyCore.Kont σ) := .assign y :: .seq R :: .tryE [] [] :: K0'
      let N : String := "$op:importFrom:" ++ a.name
      have e2 : PyCore.step I { t with stack := { f' with ctrl := .exec (fromS f.chain l a :: R), kont := .tryE [] [] :: K0' } :: fs' } =
          some { t with stack := { f' with ctrl := .ev (ccR (sub a.l 1) N [nm a.l 3 (fresh "m" l)]), kont := KA } :: fs' } := by
        rw [pstep_exec rfl rfl]; simp [fromS, hs, PyCore.execStep, PyCore.top, KA, cc, y, N]
      obtain ⟨ys1, p1, -, hf1⟩ := cc_enter (I := I) t f' fs' (sub a.l 1) N (nm a.l 3 (fresh "m" l)) [] KA
      rw [kc_importFrom I (nc_path (by simp only [okAl, Bool.and_eq_true] at ha; exact ha.1))] at p1
      obtain ⟨ys3, p3, hf3⟩ := name_op_path (I := I) t f' fs' (sub a.l 3) (fresh "m" l) (.importFrom a.name) KA hm
      have es : Sem.step I s = some { s with stack := { f with
          ctrl := .op (.importFrom a.name) [m], kont := .assignN y :: .impNext m al :: K0 } :: fs } := by
        simp [Sem.step, A.hs, hc, hK, Sem.doneStep, hs, Sem.doOp, Sem.setC, Sem.mg, y]
      refine goal_b (.cons es (.nil _)) (by simp) (.cons e1 (.cons e2 (p1.append p3))) (by simp)
        (crelI_seen (A.set .op (.core (.assignN (hnd a (by simp) hs) (.misc (.impNext hrd hok' hnd' hk))))))
        (cover_of (l := a.l) (by simp) hts ?_)
      intro y hy x hx
      simp only [List.mem_cons, List.mem_append] at hy
      rcases hy with rfl | rfl | hy | hy
      · simp [PyCore.focus, A.ht, hc'] at hx
      · simp [fromS, hs, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
      · rw [hf1 y hy x hx]; exact sub_div _ _ (by omega)
      · rw [hf3 y hy x hx]; exact sub_div _ _ (by omega)

end

/-! ## The cases -/

theorem _root_.Surf.T2.ev_compare (l a ops es) : EvCase I p (.compare l a ops es) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hok := hg.ok
  simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hl : ops.length = es.length := hok.1.1.2
  have hq : ∀ q ∈ ops, q ≠ "," := fun q h => okName_comma (List.all_eq_true.1 hok.2 q h)
  have hnd : (labelsEs es).Nodup := by
    have := hg.nd; simp only [labelsE, List.nodup_cons, List.nodup_append] at this; exact this.2.1
  have hes := goodEs_cmp hg
  have ha := goodE_cmpA hg
  have hts : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Expr.lbl])
  cases es with
  | nil => simp at hok
  | cons e es2 =>
    cases ops with
    | nil => simp at hl
    | cons o ops2 =>
      cases es2 with
      | nil =>
        cases ops2 with
        | cons _ _ => simp at hl
        | nil =>
          exact A.go11 (c := .ev a) (k := .cmpL [o] [e] :: f.kont) (c' := .ev (trE f.chain a))
            (k' := .binL o (trE f.chain e) :: f'.kont) (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
            (by simp [PyCore.step, A.ht, hc', trE, cmpChain, cmpOps, trLs, PyCore.evalStep, PyCore.top])
            (.ev ha) (.misc (.cmpL1 (hes e (by simp)) (hq o (by simp)) hk))
            (cov_ev A hc hc' (by simp [trE, cmpChain, cmpOps, trLs, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))
      | cons e' es3 =>
        cases ops2 with
        | nil => simp at hl
        | cons o' ops3 =>
          let SET : PE := gad l 3 (.set (fresh "c" e.label)) [trE f.chain e]
          let REST : PE := cmpRest f.chain l e.label (o' :: ops3) (e' :: es3)
          let t1 : PyCore.Config σ := { t with stack := { f' with
            ctrl := .ev (.bin (sub l 2) o (trE f.chain a) SET), kont := .boolK true REST :: f'.kont } :: fs' }
          have e1 : PyCore.step I t = some t1 := by
            simp [t1, SET, REST, PyCore.step, A.ht, hc', trE, cmpChain, cmpOps, trLs, cmpRest, getE, PyCore.evalStep, PyCore.top]
          have e2 : PyCore.step I t1 = some { t with stack := { f' with
              ctrl := .ev (trE f.chain a), kont := .binL o SET :: .boolK true REST :: f'.kont } :: fs' } := by
            simp [t1, PyCore.step, PyCore.evalStep, PyCore.top]
          refine goal_b (.cons (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC]) (.nil _)) (by simp)
            (.cons e1 (.cons e2 (.nil _))) (by simp)
            (.inl ((A.mono fun _ => seen_of).set (.ev ha) (.misc (.cmpLm (l := l) (seen_s (by simp) hts) hes
              (by simpa using hl) hq hnd hk.seen)))) (cover_of (l := l) (by simp) hts ?_)
          intro y hy x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · simp [PyCore.focus, A.ht, hc', trE, cmpChain, cmpOps, trLs, PyCore.Expr.label] at hx
            rw [← hx]; exact sub_div _ _ (by omega)
          · simp [t1, PyCore.focus, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)

theorem _root_.Surf.T2.exec_impFrom (l m al lvl) : ExecCase I p (.impFrom l m al lvl) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hn := hnc (by simp)
  by_cases hlvl : lvl > 0
  · exact exec_impFrom_rel A hlvl hc hc' hg hn hk
  · obtain rfl : lvl = 0 := by omega
    exact exec_impFrom_mod A W hc hc' hg hn hk

theorem _root_.Surf.T2.exec_imp (l al) : ExecCase I p (.imp l al) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  refine exec_imp_ok A W hc hc' hg (hnc (by simp)) hk fun a ha => ?_
  have := hg.ok; simp only [okB, okS, Bool.and_eq_true, List.all_eq_true] at this
  simpa using this.1.2 a ha

theorem _root_.Surf.T2.val_misc : KCase I p true MiscK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | cmpL1 g hq k => exact val_cmpL1 A hc hc' hK hK' g hq k
  | cmpLm hH g hl hq hd k => exact val_cmpLm A hc hc' hK hK' hH g hl hq hd k
  | cmpR1 hq k => exact val_cmpR1 A hc hc' hK hK' hq k
  | cmpRm hH hU g hl hn hq hd k => exact val_cmpRm A hc hc' hK hK' hH hU g hl hn hq hd k
  | cmpONil k => exact val_cmpONil A hc hc' hK (hK' ▸ k)
  | cmpO hH ho g hl hn hq hd k => exact val_cmpO A hc hc' hK hK' hH ho g hl hn hq hd k
  | cmpT hH ho g hl hn hq hd k => exact val_cmpT A hc hc' hK hK' hH ho g hl hn hq hd k
  | impMod hU hfo hok hd k => exact val_impMod A hc hc' hK hK' hU hfo hok hd k
  | starStore k => exact val_starStore A hc hc' hK hK' k
  | assertK hH hm k => exact val_assertK A hc hc' hK hK' hH hm k
  | assertT hH hm k => exact val_assertT A hc hc' hK hK' hH hm k
  | assertM k => exact val_assertM A hc hc' hK hK' k
  | evsRaise k => exact val_evsRaise A hc hc' hK hK' k
  | raiseCn k => exact val_raiseCn A hc hc' hK hK' k
  | evsRaiseFrom g k => exact val_evsRaiseFrom A hc hc' hK hK' g k
  | evsRaiseFrom2 k => exact val_evsRaiseFrom2 A hc hc' hK hK' k
  | raiseCs k => exact val_raiseCs A hc hc' hK hK' k
  | raiseW k => exact val_raiseW A hc hc' hK hK' k
  | impMany hy hok hnd k => exact val_impMany A hc hc' hK hK' hy hok hnd k
  | yfK k => exact val_yfK A W hc hc' hK hK' k
  | yfIt k => exact val_yfIt A W hc hc' hK hK' k
  | yfN hd k => exact val_yfN A hc hc' hK hK' hd k

theorem _root_.Surf.T2.done_misc : KCase I p false MiscK CDone := by
  intro H s t f fs f' fs' U A W ⟨hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | impNext hrd hok hd k => exact done_impNext A hc hc' hK hK' hrd hok hd k

macro "ijM" : tactic => `(tactic| first | (intro h; cases h) | (intro _; rfl))

theorem _root_.Surf.T2.sig_misc {i : Bool} : KCase I p i MiscK CSig := by
  intro H s t f fs f' fs' U A W hc hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | yfN hd k => exact sig_yfN A hc hK hK' k
  | @cmpL1 _ K0 K0' o e _ _ => exact sig_pops (Q := [.cmpL [o] [e]]) (P := [.binL _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | cmpLm => exact sig_pops (Q := [.cmpL _ _]) (P := [.binL _ _, .boolK _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | cmpR1 => exact sig_pops (Q := [.cmpR _ _ _ _]) (P := [.binR _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | cmpRm => exact sig_pops (Q := [.cmpR _ _ _ _]) (P := [.binR _ _, .callA _, .binR _ _, .boolK _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | cmpONil => exact sig_pops (Q := [.cmpO _ _ _]) (P := []) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | cmpO => exact sig_pops (Q := [.cmpO _ _ _]) (P := [.boolK _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | cmpT => exact sig_pops (Q := [.cmpT _ _ _ _]) (P := [.boolT _ _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | assertK => exact sig_pops (Q := [.assertK _]) (P := [.ifS _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | assertT => exact sig_pops (Q := [.assertT _]) (P := [.ifT _ _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | assertM => exact sig_pops (Q := [.assertM]) (P := [.binR _ _, .callA _, .exprS, .seq _]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | evsRaise => exact sig_pops (Q := [.evs _ _ _]) (P := [.raiseS]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | raiseCn => exact sig_pops (Q := [.raiseC _]) (P := [.raiseE]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | evsRaiseFrom => exact sig_pops (Q := [.evs _ _ _]) (P := [.binR _ _, .binL _ _, .callA _, .exprS]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | evsRaiseFrom2 => exact sig_pops (Q := [.evs _ _ _]) (P := [.binR _ _, .callA _, .exprS]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | raiseCs => exact sig_pops (Q := [.raiseC _]) (P := [.raiseC _, .exprS]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | raiseW => exact sig_pops (Q := [.raiseW _]) (P := [.raiseW _, .exprS]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | impMany => exact sig_pops (Q := [.assignN _, .seq _]) (P := [.assign _, .seq _, .tryE [] []]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | impMod => exact sig_pops (Q := [.impMod _]) (P := [.assign _, .seq _, .tryE [] []]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | impNext => exact sig_pops (Q := [.impNext _ _]) (P := [.seq _, .tryE [] []]) A hc (fun _ => rfl) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | starStore => exact sig_pops (Q := [.starStore]) (P := [.binR _ _, .callA _, .exprS]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | yfK => exact sig_pops (Q := [.yfK]) (P := [.yfStart]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›
  | yfIt => exact sig_pops (Q := [.yfIt]) (P := [.yfIt]) A hc (by ijM) (by rw [hK]; rfl) (by simp) (by rw [hK']; rfl) (by simp [sPlain]) (by simp [pPlain]) ‹KRel _ _ _ _ _›

end Misc
end Surf.T2
