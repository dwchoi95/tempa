/-
(T2), calls, `def`, lambdas, parameters, decorators.

A call of a function object of a `def` or lambda (`call_fn`) binds the arguments by `Py.bindArgs`
on both sides (the signature PyCore's `$def` gave the closure is Surf's, `SigR`); an error raises in
the caller, a `**` parameter's dictionary is made first (`CallK.enterK`), then the frame is pushed
(or the generator made) with the bound cells. PyCore's body starts with the parameters' bindings in
branches that never run (`paramBind`), which it runs in the same simulation step (`param_path`); a
generator runs them at its first `next` (`resume_genFn`, `resume_genLam`).
-/
import Surf.T2Cases

namespace Surf.T2
open PyCore (Name Label)
open Py (Val Gadget)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

namespace Call

/-! ## The parameters' bindings -/

/-- PyCore runs the parameters' bindings at the start of a function body: branches that never run, each
focusing on its parameter's node. -/
theorem param_path (t : PyCore.Config σ) (g : PyCore.Frame σ) (gs : List (PyCore.Frame σ)) (C : List Scope)
    (rest : PS) (K : List (PyCore.Kont σ)) : ∀ ps : List Param,
    ∃ ys, Path (PyCore.step I) { t with stack := { g with ctrl := .exec (paramBind C ps ++ rest), kont := K } :: gs }
      { t with stack := { g with ctrl := .exec rest, kont := K } :: gs } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ q ∈ ps, x = sub q.label 2
  | [] => ⟨[], by simpa [paramBind] using Path.nil _, by simp⟩
  | q :: ps => by
    obtain ⟨ys, py, hf⟩ := param_path t g gs C rest K ps
    let ss := paramBind C ps ++ rest
    let r := sub q.label 2
    let asg : PS := [.assign (sub q.label 0) (mangle (priv C) q.name) (.const (sub q.label 1) "$none")]
    let mk (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ :=
      { t with stack := { g with ctrl := c, kont := k } :: gs }
    have e0 : paramBind C (q :: ps) ++ rest = dead r asg :: ss := by simp [paramBind, ss, r, asg]
    rw [e0]
    refine ⟨mk (.exec (dead r asg :: ss)) K :: mk (.ev (.const r "$false")) (.ifS asg [] :: .seq ss :: K) ::
      mk (.val .no) (.ifS asg [] :: .seq ss :: K) :: mk (.val (.bool false)) (.ifT asg [] :: .seq ss :: K) ::
      mk (.exec []) (.seq ss :: K) :: ys, ?_, ?_⟩
    · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ py))))
      · simp [mk, PyCore.step, PyCore.execStep, PyCore.top, dead]
      · simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
      · simp [mk, PyCore.step, PyCore.valStep, PyCore.top, PyCore.tst]
      · simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
      · simp [mk, PyCore.step, PyCore.doneStep, PyCore.top, ss]
    · intro y hy x hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | hy
      · simp [mk, PyCore.focus, dead, PyCore.Stmt.label, r] at hx; exact ⟨q, by simp, hx.symm⟩
      · simp [mk, PyCore.focus, PyCore.Expr.label, r] at hx; exact ⟨q, by simp, hx.symm⟩
      · simp [mk, PyCore.focus] at hx
      · simp [mk, PyCore.focus] at hx
      · simp [mk, PyCore.focus] at hx
      · obtain ⟨q', hq', he⟩ := hf y hy x hx; exact ⟨q', List.mem_cons_of_mem _ hq', he⟩

/-! ## Cells of a new frame -/

theorem fold_ne (n : Nat) : ∀ (bound : List (Name × Val)) (cs : Std.HashMap (Nat × Name) Val) (a : Nat × Name),
    a.1 ≠ n → (bound.foldl (fun m q => m.insert (n, q.1) q.2) cs)[a]? = cs[a]?
  | [], _, _, _ => rfl
  | q :: bound, cs, a, h => by
    simp only [List.foldl_cons]
    rw [fold_ne n bound _ a h, Std.HashMap.getElem?_insert]
    have : ((n, q.1) == a) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro e; exact h (by rw [← e])
    simp [this]

theorem fold_cells (n : Nat) : ∀ (bound : List (Name × Val)) (cs1 cs2 : Std.HashMap (Nat × Name) Val),
    (∀ a : Nat × Name, ¬ Dot a.2 → cs1[a]? = cs2[a]?) → ∀ a : Nat × Name, ¬ Dot a.2 →
      (bound.foldl (fun m q => m.insert (n, q.1) q.2) cs1)[a]? = (bound.foldl (fun m q => m.insert (n, q.1) q.2) cs2)[a]?
  | [], _, _, h => h
  | q :: bound, cs1, cs2, h => by
    simp only [List.foldl_cons]
    refine fold_cells n bound _ _ fun a ha => ?_
    rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    split
    · rfl
    · exact h a ha

/-- A frame's readings of names, when the cells at its own id and the module dictionary are the same. -/
theorem agree_same {t t1 : PyCore.Config σ} (h' : PyCore.Frame σ) (hgl : ∀ x, t1.glob x = t.glob x)
    (hc : ∀ x : Name, t1.cells[(h'.id, x)]? = t.cells[(h'.id, x)]?) :
    Agree (fun _ => False) (rdOf t h') (ownOf t h') (rdOf t1 h') (ownOf t1 h') :=
  agree_of (P := fun _ => False) (fun _ _ _ _ h => h)
    (rd_same rfl rfl rfl (fun _ x _ => hgl x) (fun x _ => hc x) (fun _ _ _ => rfl))


/-! ## Frame ids after a push or a generator -/

section
variable {t : PyCore.Config σ} {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore's frame ids after a new frame (id `next`) is pushed above the caller. -/
theorem ids_push {t1 : PyCore.Config σ} {g' g0' : PyCore.Frame σ} (h : Ids t) (ht : t.stack = f' :: fs')
    (ht1 : t1.stack = g' :: g0' :: fs') (ho : t1.objs = t.objs) (hn : t1.next = t.next + 1)
    (hid : g'.id = t.next) (hk : g'.kind = .fn) (hid0 : g0'.id = f'.id) (hk0 : g0'.kind = f'.kind) : Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  have hlt : ∀ g ∈ f' :: fs', g.id < t.next := h2
  have hob : ∀ o b, pObj t1 o = some b → pObj t o = some b := fun o b hb => by simpa [pObj, ho] using hb
  refine ⟨?_, fun g hg => ?_, fun o b hb => ?_, fun o g ho1 => ?_, fun g hg o hgo => ?_, fun g hg hm => ?_,
    fun o g ho1 => h7 o g (hob _ _ ho1)⟩
  · rw [ht1, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, by simpa [hid0] using h1⟩
    obtain ⟨h', hh', e⟩ := List.mem_map.1 hm
    rcases List.mem_cons.1 hh' with rfl | hh'
    · have := hlt f' (by simp); omega
    · have := hlt h' (by simp [hh']); omega
  · rw [ht1, List.mem_cons, List.mem_cons] at hg; rw [hn]
    rcases hg with rfl | rfl | hg
    · omega
    · have := hlt f' (by simp); omega
    · have := hlt g (by simp [hg]); omega
  · rw [hn]; have := h3 o b (hob _ _ hb); omega
  · obtain ⟨e, hne⟩ := h4 o g (hob _ _ ho1)
    have hlo := h3 o _ (hob _ _ ho1)
    refine ⟨e, fun h' hh' => ?_⟩
    rw [ht1, List.mem_cons, List.mem_cons] at hh'
    rcases hh' with rfl | rfl | hh'
    · omega
    · rw [hid0]; exact hne _ (by simp)
    · exact hne _ (by simp [hh'])
  · rw [ht1, List.mem_cons, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · rw [hk] at hgo; cases hgo
    · rw [hid0]; exact h5 _ (by simp) o (by rw [← hk0]; exact hgo)
    · exact h5 _ (by simp [hg]) o hgo
  · rw [ht1, List.mem_cons, List.mem_cons] at hg
    rcases hg with rfl | rfl | hg
    · rw [hk] at hm; cases hm
    · rw [hid0]; exact h6 _ (by simp) (by rw [← hk0]; exact hm)
    · exact h6 _ (by simp [hg]) hm

/-- PyCore's frame ids after a generator (its frame's id `next`) is made. -/
theorem ids_gen {t1 : PyCore.Config σ} {g' g0' : PyCore.Frame σ} (h : Ids t) (ht : t.stack = f' :: fs')
    (ht1 : t1.stack = g0' :: fs') (ho : t1.objs = t.objs.insert t.next (.gen (.susp g'))) (hn : t1.next = t.next + 1)
    (hid : g'.id = t.next) (hk : g'.kind = .gen t.next) (hid0 : g0'.id = f'.id) (hk0 : g0'.kind = f'.kind) :
    Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  have hlt : ∀ g ∈ f' :: fs', g.id < t.next := h2
  have ho' : ∀ o, pObj t1 o = if t.next = o then some (.gen (.susp g')) else pObj t o := by
    intro o; simp only [pObj]; rw [ho, Std.HashMap.getElem?_insert]; simp [beq_iff_eq]
  refine ⟨?_, fun g hg => ?_, fun o b hb => ?_, fun o g ho1 => ?_, fun g hg o hgo => ?_, fun g hg hm => ?_,
    fun o g ho1 => ?_⟩
  · rw [ht1]; simpa [hid0] using h1
  · rw [ht1, List.mem_cons] at hg; rw [hn]
    rcases hg with rfl | hg
    · rw [hid0]; have := hlt f' (by simp); omega
    · have := hlt g (by simp [hg]); omega
  · rw [hn]; rw [ho'] at hb; split at hb
    · omega
    · have := h3 o b hb; omega
  · rw [ho'] at ho1; split at ho1
    · rename_i e; cases ho1
      refine ⟨by rw [hid, e], fun h' hh' => ?_⟩
      rw [ht1, List.mem_cons] at hh'
      rcases hh' with rfl | hh'
      · rw [hid0, ← e]; have := hlt f' (by simp); omega
      · rw [← e]; have := hlt h' (by simp [hh']); omega
    · obtain ⟨e, hne⟩ := h4 o g ho1
      refine ⟨e, fun h' hh' => ?_⟩
      rw [ht1, List.mem_cons] at hh'
      rcases hh' with rfl | hh'
      · rw [hid0]; exact hne _ (by simp)
      · exact hne _ (by simp [hh'])
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [hid0]; exact h5 _ (by simp) o (by rw [← hk0]; exact hgo)
    · exact h5 _ (by simp [hg]) o hgo
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [hid0]; exact h6 _ (by simp) (by rw [← hk0]; exact hm)
    · exact h6 _ (by simp [hg]) hm
  · rw [ho'] at ho1; split at ho1
    · rename_i e; cases ho1; rw [hk, e]
    · exact h7 o g ho1

end

/-! ## Related configurations after a frame is pushed or a generator made -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The readings of the frames other than the new one (id `next`) stay. -/
theorem agree_new (bound : List (Name × Val)) (h' : PyCore.Frame σ) (hne : h'.id ≠ t.next) :
    Agree (fun _ => False) (rdOf t h') (ownOf t h') (rdAt t.glob (PyCore.initCells t.cells t.next bound) h')
      (ownAt (PyCore.initCells t.cells t.next bound) h') :=
  agree_same (t1 := { t with cells := PyCore.initCells t.cells t.next bound }) h' (fun _ => rfl)
    (fun x => fold_ne _ _ _ _ hne)

theorem below_lt (A : At p H s t f fs f' fs') {h' : PyCore.Frame σ} (hh : h' ∈ f' :: fs') : h'.id ≠ t.next := by
  have := A.r.ids.lt h' (by rw [A.ht]; exact hh); omega

theorem susp_lt (A : At p H s t f fs f' fs') {o : Nat} {h' : PyCore.Frame σ} (ho : pObj t o = some (.gen (.susp h'))) :
    h'.id ≠ t.next := by
  have e := (A.r.ids.susp o h' ho).1
  have := A.r.ids.obj o _ ho; omega

/-- A new frame (id `next`, the bound parameters in its cells) above the caller, which waits. -/
theorem crel_push (A : At p H s t f fs f' fs') {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hk : KRel A.x U true K K') (bound : List (Name × Val)) {g : Sem.Frame σ} {g' : PyCore.Frame σ}
    (hid : g'.id = t.next) (hkd : g'.kind = .fn)
    (hg : FRel p H (rdAt t.glob (PyCore.initCells t.cells t.next bound) g') (ownAt (PyCore.initCells t.cells t.next bound) g')
      g g') (hgk : EnterOk s.objs g.kont) (hE : EnterSub K f.kont) :
    CRel p H
      { s with
        stack := g :: { f with ctrl := .wait, kont := K } :: fs
        cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
        next := s.next + 1 }
      { t with
        stack := g' :: { f' with ctrl := .wait, kont := K' } :: fs'
        cells := PyCore.initCells t.cells t.next bound
        next := t.next + 1 } := by
  have hst := A.r.stack; rw [A.hs, A.ht] at hst
  have hn : t.next = s.next := A.r.next
  refine ⟨⟨hg, ⟨A.hf.toFRel0.upd .wait K .wait K', A.hf.hl, U, true, .wait,
      KRel.ext ⟨fun _ h => h, (agree_new bound f' (below_lt A (by simp))).mono fun _ h => h.elim⟩ hk⟩,
      all2_agree hst.2 fun h' hh => agree_new bound h' (below_lt A (by simp [hh]))⟩, fun o => ?_, ?_, A.r.glob,
      A.r.out, by simp [hn], A.r.res, A.r.st, ?_, ?_, ?_⟩
  · have := A.r.objs o
    simp only [sObj, pObj] at this ⊢
    cases h1 : s.objs[o]? <;> cases h2 : t.objs[o]? <;> rw [h1, h2] at this <;> simp only [PyCore.OptRel] at this ⊢
    exact this.agree fun h' e => agree_new bound h' (susp_lt A (o := o) (by simp [pObj, h2, e]))
  · intro a ha
    simp only [pCell, sCell, PyCore.initCells]
    rw [hn]; exact fold_cells _ bound _ _ A.r.cells a ha
  · intro g1 hg1
    simp only [List.tail_cons, List.mem_cons] at hg1
    rcases hg1 with rfl | hg1
    · rfl
    · exact A.r.wait g1 (by rw [A.hs]; exact hg1)
  · exact ids_push A.r.ids A.ht rfl rfl rfl hid hkd rfl rfl
  · have hen := A.r.enter; rw [A.hs] at hen
    have h2 := hen.top .wait hE
    exact ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ hgk) (h2.1 x), h2.2⟩

/-- A new generator (its frame's id `next`, the bound parameters in its cells), given to the caller. -/
theorem crel_gen (A : At p H s t f fs f' fs') {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hk : KRel A.x U true K K') (bound : List (Name × Val)) {g : Sem.Frame σ} {g' : PyCore.Frame σ}
    (hid : g'.id = t.next) (hkd : g'.kind = .gen t.next)
    (hg : GRel p H t.glob (PyCore.initCells t.cells t.next bound) (.susp g) (.susp g'))
    (hgk : EnterOk s.objs g.kont) (hE : EnterSub K f.kont) :
    CRel p H
      { s with
        stack := { f with ctrl := .val (.gen s.next), kont := K } :: fs
        objs := s.objs.insert s.next (.gen (.susp g))
        cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
        next := s.next + 1 }
      { t with
        stack := { f' with ctrl := .val (.gen t.next), kont := K' } :: fs'
        objs := t.objs.insert t.next (.gen (.susp g'))
        cells := PyCore.initCells t.cells t.next bound
        next := t.next + 1 } := by
  have hst := A.r.stack; rw [A.hs, A.ht] at hst
  have hn : t.next = s.next := A.r.next
  refine ⟨⟨⟨A.hf.toFRel0.upd _ K _ K', A.hf.hl, U, true, by rw [hn]; exact .val,
      KRel.ext ⟨fun _ h => h, (agree_new bound f' (below_lt A (by simp))).mono fun _ h => h.elim⟩ hk⟩,
      all2_agree hst.2 fun h' hh => agree_new bound h' (below_lt A (by simp [hh]))⟩, fun o => ?_, ?_, A.r.glob,
      A.r.out, by simp [hn], A.r.res, A.r.st, ?_, ?_, ?_⟩
  · simp only [sObj, pObj]
    rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]
    by_cases e : t.next = o
    · have e' : s.next = o := hn ▸ e
      rw [if_pos (by simp [e']), if_pos (by simp [e])]
      exact .gen hg
    · have e' : ¬ s.next = o := hn ▸ e
      simp only [beq_iff_eq, e, e', ite_false]
      have := A.r.objs o
      simp only [sObj, pObj] at this
      cases h1 : s.objs[o]? <;> cases h2 : t.objs[o]? <;> rw [h1, h2] at this <;> simp only [PyCore.OptRel] at this ⊢
      exact this.agree fun h' e => agree_new bound h' (susp_lt A (o := o) (by simp [pObj, h2, e]))
  · intro a ha
    simp only [pCell, sCell, PyCore.initCells]
    rw [hn]; exact fold_cells _ bound _ _ A.r.cells a ha
  · intro g1 hg1
    exact A.r.wait g1 (by rw [A.hs]; exact hg1)
  · exact ids_gen A.r.ids A.ht rfl rfl rfl hid hkd rfl rfl
  · have hen := A.r.enter; rw [A.hs] at hen
    exact (hen.top _ hE).ins (insOk_gen _) fun _ e => by cases e; exact hgk

end

/-! ## Entering a function object -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- Every node PyCore's steps focus has its Surf node touched before. -/
theorem cover_H {zs : List (Sem.Config σ)} {ys : List (PyCore.Config σ)}
    (h : ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → H (x / 64)) : Cover (Touch p) pfocus H zs ys :=
  fun y hy x hx => .inl (h y hy x (pfocus_le hx))

/-- The frame of a function is pushed on both sides (PyCore then runs its parameters' bindings, `pb`). -/
theorem enter_plain (A : At p H s t f fs f' fs') {U : Label → Prop} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (hk : KRel A.x U true K K') (bound : List (Name × Val)) {g : Sem.Frame σ}
    {g0' g1' : PyCore.Frame σ} {ys : List (PyCore.Config σ)}
    (e1 : Sem.step I s = some
      { s with
        stack := g :: { f with ctrl := .wait, kont := K } :: fs
        cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
        next := s.next + 1 })
    (e2 : PyCore.step I t = some
      { t with
        stack := g0' :: { f' with ctrl := .wait, kont := K' } :: fs'
        cells := PyCore.initCells t.cells t.next bound
        next := t.next + 1 })
    (pb : Path (PyCore.step I)
      { t with
        stack := g0' :: { f' with ctrl := .wait, kont := K' } :: fs'
        cells := PyCore.initCells t.cells t.next bound
        next := t.next + 1 }
      { t with
        stack := g1' :: { f' with ctrl := .wait, kont := K' } :: fs'
        cells := PyCore.initCells t.cells t.next bound
        next := t.next + 1 } ys)
    (hfoc : PyCore.focus t = none) (hcov : ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → H (x / 64))
    (hid : g1'.id = t.next) (hkd : g1'.kind = .fn)
    (hg : FRel p H (rdAt t.glob (PyCore.initCells t.cells t.next bound) g1') (ownAt (PyCore.initCells t.cells t.next bound) g1')
      g g1') (hgk : EnterOk s.objs g.kont) (hE : EnterSub K f.kont) : GoalB I p H s t :=
  goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 pb) (by simp) (crelI_seen (crel_push A hk bound hid hkd hg hgk hE))
    (cover_H fun y hy x hx => by
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [hfoc] at hx; cases hx
      · exact hcov y hy x hx)

/-- A generator of a function is made on both sides. -/
theorem enter_gen (A : At p H s t f fs f' fs') {U : Label → Prop} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (hk : KRel A.x U true K K') (bound : List (Name × Val)) {g : Sem.Frame σ}
    {g' : PyCore.Frame σ}
    (e1 : Sem.step I s = some
      { s with
        stack := { f with ctrl := .val (.gen s.next), kont := K } :: fs
        objs := s.objs.insert s.next (.gen (.susp g))
        cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
        next := s.next + 1 })
    (e2 : PyCore.step I t = some
      { t with
        stack := { f' with ctrl := .val (.gen t.next), kont := K' } :: fs'
        objs := t.objs.insert t.next (.gen (.susp g'))
        cells := PyCore.initCells t.cells t.next bound
        next := t.next + 1 })
    (hfoc : PyCore.focus t = none) (hid : g'.id = t.next) (hkd : g'.kind = .gen t.next)
    (hg : GRel p H t.glob (PyCore.initCells t.cells t.next bound) (.susp g) (.susp g'))
    (hgk : EnterOk s.objs g.kont) (hE : EnterSub K f.kont) : GoalB I p H s t :=
  goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen (crel_gen A hk bound hid hkd hg hgk hE))
    (cover_none fun y hy => by simp at hy; subst hy; exact hfoc)

end


/-! ## Parts of a call -/

/-- A keyword argument's name and value. -/
def kwN : Kw → Option Name | .mk _ x _ => x
def kwV : Kw → Option Expr | .mk _ _ v => some v

theorem itemsKs_mem {C : List Scope} {lk : Label} {y : Option Name} {v : Expr} {it : Item} :
    ∀ {kws : List Kw}, Kw.mk lk y v ∈ kws → it ∈ itemsE C v → it ∈ itemsKs C kws
  | [], h, _ => by simp at h
  | .mk _ _ _ :: kws, h, hx => by
    rcases List.mem_cons.1 h with e | h
    · cases e; simp [itemsKs, hx]
    · simp [itemsKs, itemsKs_mem h hx]

theorem mem_trKs {C : List Scope} {lk : Label} {y : Option Name} {v : Expr} :
    ∀ {kws : List Kw}, Kw.mk lk y v ∈ kws → trE C v ∈ trKs C kws
  | [], h => by simp at h
  | .mk _ _ _ :: kws, h => by
    rcases List.mem_cons.1 h with e | h
    · cases e; simp [trKs]
    · simp [trKs, mem_trKs h]

theorem okKs_mem {lk : Label} {y : Option Name} {v : Expr} :
    ∀ {kws : List Kw}, okKs kws = true → Kw.mk lk y v ∈ kws → okE v = true
  | [], _, h => by simp at h
  | .mk _ _ _ :: kws, ho, h => by
    simp only [okKs, Bool.and_eq_true] at ho
    rcases List.mem_cons.1 h with e | h
    · cases e; exact ho.1.2
    · exact okKs_mem ho.2 h

theorem labelsKs_mem {lk : Label} {y : Option Name} {v : Expr} {l : Label} :
    ∀ {kws : List Kw}, Kw.mk lk y v ∈ kws → l ∈ labelsE v → l ∈ labelsKs kws
  | [], h, _ => by simp at h
  | .mk _ _ _ :: kws, h, hx => by
    rcases List.mem_cons.1 h with e | h
    · cases e; simp [labelsKs, hx]
    · simp [labelsKs, labelsKs_mem h hx]

theorem touchKs_mem {lk : Label} {y : Option Name} {v : Expr} {x : Label × Expr} :
    ∀ {kws : List Kw}, Kw.mk lk y v ∈ kws → x ∈ touchE v → x ∈ touchKs kws
  | [], h, _ => by simp at h
  | .mk _ _ _ :: kws, h, hx => by
    rcases List.mem_cons.1 h with e | h
    · cases e; simp [touchKs, hx]
    · simp [touchKs, touchKs_mem h hx]

theorem lblKs_mem {k : Kw} : ∀ {kws : List Kw}, k ∈ kws → k.lbl ∈ labelsKs kws
  | [], h => by simp at h
  | .mk _ _ _ :: kws, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [labelsKs, Kw.lbl]
    · simp [labelsKs, lblKs_mem h]

theorem nodup_labelsKs {lk : Label} {y : Option Name} {v : Expr} :
    ∀ {kws : List Kw}, Kw.mk lk y v ∈ kws → (labelsKs kws).Nodup → (labelsE v).Nodup
  | [], h, _ => by simp at h
  | .mk _ _ _ :: kws, h, hn => by
    simp only [labelsKs, List.nodup_cons, List.nodup_append] at hn
    rcases List.mem_cons.1 h with e | h
    · cases e; exact hn.1.2
    · exact nodup_labelsKs h hn.2.1

theorem call_pitems {C : List Scope} {l : Label} {f : Expr} {args : List Expr} {kws : List Kw} {x : PyCore.Item} {e : PE}
    (he : e = trE C f ∨ e ∈ trA C args ∨ e ∈ trKs C kws) (hx : x ∈ PyCore.itemsE R0 (trChain C) e) :
    x ∈ PyCore.itemsE R0 (trChain C) (trE C (.call l f args kws)) := by
  simp only [trE, gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false,
    List.nil_append]
  refine items_fold _ _ x (.inr ⟨e, ?_, hx⟩)
  rcases he with rfl | he | he
  · simp
  · simp [he]
  · simp [he]

theorem call_labels {l : Label} {f : Expr} {args : List Expr} {kws : List Kw} :
    labelsE (.call l f args kws) = l :: (labelsE f ++ labelsEs args ++ labelsKs kws) := by
  simp [labelsE]

section
variable {C : List Scope} {U : Label → Prop} {l : Label} {f : Expr} {args : List Expr} {kws : List Kw}

theorem good_call_f (h : GoodE p C U (.call l f args kws)) : GoodE p C U f := by
  have hnd := h.nd; rw [call_labels, List.nodup_cons, List.nodup_append, List.nodup_append] at hnd
  have hok := h.ok; simp only [okE, Bool.and_eq_true] at hok
  exact GoodE.of h (fun x hx => by simp [itemsE, hx]) (fun x hx => call_pitems (.inl rfl) hx) (fun _ => hok.1.1)
    (fun x hx => by rw [call_labels]; simp [hx]) (fun _ => hnd.2.1.1) (fun x hx => by simp [touchE, hx])

theorem good_call_arg (h : GoodE p C U (.call l f args kws)) {a : Expr} (ha : a ∈ args) : GoodE p C U (unstar a) := by
  have hnd := h.nd; rw [call_labels, List.nodup_cons, List.nodup_append, List.nodup_append] at hnd
  have hok := h.ok; simp only [okE, Bool.and_eq_true] at hok
  have hsub : ∀ x, x ∈ labelsE (unstar a) → x ∈ labelsE a := by
    intro x hx; cases a <;> simp_all [unstar, labelsE]
  have hnd2 : (labelsE (unstar a)).Nodup := by
    have := nodup_labelsEs ha hnd.2.1.2.1
    cases a <;> simp_all [unstar, labelsE, List.nodup_cons]
  refine GoodE.of h (fun x hx => ?_) (fun x hx => call_pitems (.inr (.inl (mem_trA ha))) hx) (fun _ => okAs_mem hok.1.2 ha)
    (fun x hx => by rw [call_labels]; simp [labelsEs_mem ha (hsub x hx)]) (fun _ => hnd2)
    (fun x hx => by simp [touchE, touchEs_mem ha (touch_unstar hx)])
  have : x ∈ itemsE C a := by cases a <;> simp_all [unstar, itemsE]
  simp [itemsE, itemsEs_mem ha this]

theorem good_call_kw (h : GoodE p C U (.call l f args kws)) {lk : Label} {y : Option Name} {v : Expr}
    (hk : Kw.mk lk y v ∈ kws) : GoodE p C U v := by
  have hnd := h.nd; rw [call_labels, List.nodup_cons, List.nodup_append, List.nodup_append] at hnd
  have hok := h.ok; simp only [okE, Bool.and_eq_true] at hok
  exact GoodE.of h (fun x hx => by simp [itemsE, itemsKs_mem hk hx]) (fun x hx => call_pitems (.inr (.inr (mem_trKs hk))) hx)
    (fun _ => okKs_mem hok.2 hk) (fun x hx => by rw [call_labels]; simp [labelsKs_mem hk hx])
    (fun _ => nodup_labelsKs hk hnd.2.2.1) (fun x hx => by simp [touchE, touchKs_mem hk hx])

end

theorem partsR_app {x : Cx} {U : Label → Prop} {l : Label} :
    ∀ {r1 : List (Option Expr)} {p1 : List PE} {r2 : List (Option Expr)} {p2 : List PE},
    PartsR x U l r1 p1 → PartsR x U l r2 p2 → PartsR x U l (r1 ++ r2) (p1 ++ p2)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, ⟨h1, h2⟩, h => ⟨h1, partsR_app h2 h⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

theorem partsR_args {x : Cx} {U : Label → Prop} {l : Label} :
    ∀ {args : List Expr}, (∀ a ∈ args, GoodE x.p x.C U (unstar a)) →
      PartsR x U l (args.map fun a => some (unstar a)) (trA x.C args)
  | [], _ => trivial
  | a :: args, h => by
    have ih := partsR_args (l := l) fun a' ha => h a' (List.mem_cons_of_mem _ ha)
    cases a <;> exact ⟨⟨h _ List.mem_cons_self, rfl⟩, ih⟩

theorem partsR_kws {x : Cx} {U : Label → Prop} {l : Label} :
    ∀ {kws : List Kw}, (∀ lk y v, Kw.mk lk y v ∈ kws → GoodE x.p x.C U v) →
      PartsR x U l (kws.map kwV) (trKs x.C kws)
  | [], _ => trivial
  | .mk lk y v :: kws, h => ⟨⟨h lk y v List.mem_cons_self, rfl⟩, partsR_kws fun a b c hm => h a b c (List.mem_cons_of_mem _ hm)⟩

/-! ## Steps on argument records (as in `T2Access.lean`) -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

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

end


/-! ## Signals passing the call items -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- Both runs step to related top frames, PyCore's steps evaluating no node. -/
theorem goP (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)} {xs : List (Sem.Config σ)} {ys : List (PyCore.Config σ)}
    (pa : Path (Sem.step I) s { s with stack := { f with ctrl := c, kont := k } :: fs } xs) (hxs : xs ≠ [])
    (pb : Path (PyCore.step I) t { t with stack := { f' with ctrl := c', kont := k' } :: fs' } ys) (hys : ys ≠ [])
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i k k') (hf : ∀ y ∈ ys, PyCore.focus y = none)
    (he : EnterSub k f.kont) : Goal I p H s t :=
  goal_b pa hxs pb hys (crelI_seen (A.set hc hk he)) (cover_none hf)

/-- The PyCore items an exception or a return passes with no effect. -/
def PopOk : PyCore.Kont σ → Prop
  | .binR .. | .binL .. | .callA .. | .argStar .. | .argKw .. | .enterK .. | .assign .. => True
  | _ => False

theorem recK_pop (done : List Val) (rest : List PE) (ks : List (PyCore.Kont σ)) (h : ∀ k ∈ ks, PopOk k) :
    ∀ k ∈ recK done rest ks, PopOk k := by
  intro k hk
  simp only [recK, List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at hk
  rcases hk with rfl | ⟨_, _, rfl⟩ | hk
  · trivial
  · trivial
  · exact h k hk

theorem recK_split (done : List Val) (rest : List PE) (ks K' : List (PyCore.Kont σ)) :
    recK done rest (ks ++ K') = recK done rest ks ++ K' := by simp [recK]

/-- A raise or a return passes PyCore's items `pre`. -/
theorem pop_path {c : PyCore.Ctrl σ} (hc : (∃ v, c = .raise v) ∨ (∃ v, c = .retv v)) (K' : List (PyCore.Kont σ)) :
    ∀ pre : List (PyCore.Kont σ), (∀ k ∈ pre, PopOk k) →
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := c, kont := pre ++ K' } :: fs' }
      { t with stack := { f' with ctrl := c, kont := K' } :: fs' } ys ∧ ys.length = pre.length ∧
      ∀ y ∈ ys, PyCore.focus y = none
  | [], _ => ⟨[], .nil _, rfl, by simp⟩
  | k :: pre, hp => by
    obtain ⟨ys, py, hl, hf⟩ := pop_path hc K' pre (fun k hk => hp k (List.mem_cons_of_mem _ hk))
    have hk := hp k List.mem_cons_self
    refine ⟨_ :: ys, .cons ?_ py, by simp [hl], ?_⟩
    · rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases k <;> simp [PopOk] at hk <;>
        simp [PyCore.step, PyCore.raiseStep, PyCore.retStep, PyCore.top]
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩
        · cases k <;> simp [PopOk] at hk <;> simp [PyCore.focus]
        · simp [PyCore.focus]
      · exact hf y hy

/-- A raise or a return passes one Surf item and PyCore's items `pre` for it. -/
theorem call_sig_pop (A : At p H s t f fs f' fs') {U : Label → Prop} {j : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} (pre : List (PyCore.Kont σ))
    (hcr : CR p f.chain U j c c') (hsig : (∃ v, c' = .raise v) ∨ (∃ v, c' = .retv v)) (hc' : f'.ctrl = c')
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := K } :: fs })
    (hK' : f'.kont = pre ++ K') (hp : ∀ k ∈ pre, PopOk k) (hne : pre ≠ []) (hk : KRel A.x U j K K')
    (he : EnterSub K f.kont) : Goal I p H s t := by
  obtain ⟨ys, py, hl, hf⟩ := pop_path (I := I) (t := t) (f' := f') (fs' := fs') hsig K' pre hp
  rw [t_eq A.ht hc' hK'] at py
  exact goP A (.cons e1 (.nil _)) (by simp) py (by rintro rfl; exact hne (List.length_eq_zero_iff.1 hl.symm))
    hcr hk hf he

end


/-- Entering the function object of a `def` or lambda with the bound parameters (`bound`): its frame
pushed (PyCore then running the parameters' bindings), or its generator made. -/
theorem enter_clo {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ}
    {fs : List (Sem.Frame σ)} {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}
    (A : At p H s t f fs f' fs') {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hk : KRel A.x U true K K') {S : Scope} {C : List Scope} {cl κ kd dflt cl' κ' sg}
    (hr : ORel (σ := σ) p H t.glob t.cells (.clo S C cl κ kd dflt) (.clo (trScope C S) (trChain C) cl' κ' sg))
    (hS : S.isComp = false) (bound : List (Name × Val)) (cS : Sem.Ctrl σ) (cP : PyCore.Ctrl σ)
    (e1 : Sem.step I s = Sem.enter s { f with ctrl := cS, kont := K } fs S C cl κ kd bound)
    (e2 : PyCore.step I t = PyCore.enter t { f' with ctrl := cP, kont := K' } fs' (trScope C S) (trChain C) cl' κ' bound)
    (hfoc : PyCore.focus t = none) (hE : EnterSub K f.kont) : GoalB I p H s t := by
  have hn : t.next = s.next := A.r.next
  have hK := kind_tr C S
  have hnil : EnterOk s.objs ([] : List (Sem.Kont σ)) := enterOk_nil
  have hret : EnterOk s.objs [(Sem.Kont.retS : Sem.Kont σ)] := fun _ _ _ h => by simp at h
  cases hr with
  | clo h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
  cases S with
  | comp => simp [Scope.isComp] at hS
  | cl => cases sg <;> simp [SigR, Scope.isComp] at h6
  | fn l gn ps b =>
    let Sf := Scope.fn l gn ps b
    let bd := paramBind (Sf :: C) ps ++ trB (Sf :: C) b
    have hkS : PyCore.Scope.kind (.fn (sub l 1) false (fresh "a" l)
        (paramBind (Scope.fn l gn ps b :: C) ps ++ trB (Scope.fn l gn ps b :: C) b)) = (Scope.fn l gn ps b).kind C := hK rfl
    by_cases hg : kd = .gen
    · subst hg
      rw [← h3] at hkS
      let g : Sem.Frame σ :=
        { id := s.next, chain := Sf :: C, kind := .gen s.next, cls := cl, κ := κ, ns := [],
          ctrl := .exec b, kont := [] }
      let g' : PyCore.Frame σ :=
        { id := t.next, chain := trScope C Sf :: trChain C, kind := .gen t.next, cls := cl',
          κ := κ', ns := [], ctrl := .exec bd, kont := [] }
      have e1' : Sem.step I s = some
          { s with
            stack := { f with ctrl := .val (.gen s.next), kont := K } :: fs
            objs := s.objs.insert s.next (.gen (.susp g))
            cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
            next := s.next + 1 } := by
        rw [e1]; simp [Sem.enter, g, Sf]
      have e2' : PyCore.step I t = some
          { t with
            stack := { f' with ctrl := .val (.gen t.next), kont := K' } :: fs'
            objs := t.objs.insert t.next (.gen (.susp g'))
            cells := PyCore.initCells t.cells t.next bound
            next := t.next + 1 } := by
        rw [e2]; simp [trScope, PyCore.enter, g', Sf, bd, hkS]
      exact enter_gen A hk bound e1' e2' hfoc rfl rfl
        (.special ⟨hn, rfl, h1, h2, by simp [g, g', fk, hn], trivial, h4, h5, rfl, h10⟩
          (fun S' C' e => by cases e; exact h7) (.genFn rfl h8 h9)) hnil hE
    · have hkp : kd = .plain := by cases kd <;> simp_all
      subst hkp
      rw [← h3] at hkS
      let g : Sem.Frame σ :=
        { id := s.next, chain := Sf :: C, kind := .fn, cls := cl, κ := κ, ns := [],
          ctrl := .exec b, kont := [] }
      let g0' : PyCore.Frame σ :=
        { id := t.next, chain := trScope C Sf :: trChain C, kind := .fn, cls := cl',
          κ := κ', ns := [], ctrl := .exec bd, kont := [] }
      have e1' : Sem.step I s = some
          { s with
            stack := g :: { f with ctrl := .wait, kont := K } :: fs
            cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
            next := s.next + 1 } := by
        rw [e1]; simp [Sem.enter, g, Sf]
      have e2' : PyCore.step I t = some
          { t with
            stack := g0' :: { f' with ctrl := .wait, kont := K' } :: fs'
            cells := PyCore.initCells t.cells t.next bound
            next := t.next + 1 } := by
        rw [e2]; simp [trScope, PyCore.enter, g0', Sf, bd, hkS]
      obtain ⟨ys, py, hfy⟩ := param_path (I := I)
        { t with cells := PyCore.initCells t.cells t.next bound, next := t.next + 1 } g0'
        ({ f' with ctrl := .wait, kont := K' } :: fs') (Sf :: C) (trB (Sf :: C) b) [] ps
      exact enter_plain A hk bound (g1' := { g0' with ctrl := .exec (trB (Sf :: C) b), kont := [] }) e1' e2' py hfoc
        (fun y hy x hx => by obtain ⟨q, hq, rfl⟩ := hfy y hy x hx; rw [sub_div _ _ (by omega)]; exact h8 q hq)
        rfl rfl
        ⟨⟨hn, rfl, h1, h2, rfl, trivial, h4, h5, rfl, h10⟩, fun S' C' e => by cases e; exact h7, UAll, false,
          .exec h9 (fun _ => hS), .nil⟩ hnil hE
  | lam l ps b =>
    let Sf := Scope.lam l ps b
    let bd := paramBind (Sf :: C) ps ++ [.ret (sub l 2) (trE (Sf :: C) b)]
    have hkS : PyCore.Scope.kind (.fn (sub l 1) false (fresh "a" l)
        (paramBind (Scope.lam l ps b :: C) ps ++ [.ret (sub l 2) (trE (Scope.lam l ps b :: C) b)])) =
        (Scope.lam l ps b).kind C := hK rfl
    by_cases hg : kd = .gen
    · subst hg
      rw [← h3] at hkS
      let g : Sem.Frame σ :=
        { id := s.next, chain := Sf :: C, kind := .gen s.next, cls := cl, κ := κ, ns := [],
          ctrl := .ev b, kont := [.retS] }
      let g' : PyCore.Frame σ :=
        { id := t.next, chain := trScope C Sf :: trChain C, kind := .gen t.next, cls := cl',
          κ := κ', ns := [], ctrl := .exec bd, kont := [] }
      have e1' : Sem.step I s = some
          { s with
            stack := { f with ctrl := .val (.gen s.next), kont := K } :: fs
            objs := s.objs.insert s.next (.gen (.susp g))
            cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
            next := s.next + 1 } := by
        rw [e1]; simp [Sem.enter, g, Sf]
      have e2' : PyCore.step I t = some
          { t with
            stack := { f' with ctrl := .val (.gen t.next), kont := K' } :: fs'
            objs := t.objs.insert t.next (.gen (.susp g'))
            cells := PyCore.initCells t.cells t.next bound
            next := t.next + 1 } := by
        rw [e2]; simp [trScope, PyCore.enter, g', Sf, bd, hkS]
      exact enter_gen A hk bound e1' e2' hfoc rfl rfl
        (.special ⟨hn, rfl, h1, h2, by simp [g, g', fk, hn], trivial, h4, h5, rfl, h10⟩
          (fun S' C' e => by cases e; exact h7) (.genLam rfl h8 h9)) hret hE
    · have hkp : kd = .plain := by cases kd <;> simp_all
      subst hkp
      rw [← h3] at hkS
      let g : Sem.Frame σ :=
        { id := s.next, chain := Sf :: C, kind := .fn, cls := cl, κ := κ, ns := [],
          ctrl := .ev b, kont := [.retS] }
      let g0' : PyCore.Frame σ :=
        { id := t.next, chain := trScope C Sf :: trChain C, kind := .fn, cls := cl',
          κ := κ', ns := [], ctrl := .exec bd, kont := [] }
      have e1' : Sem.step I s = some
          { s with
            stack := g :: { f with ctrl := .wait, kont := K } :: fs
            cells := bound.foldl (fun m q => m.insert (s.next, q.1) q.2) s.cells
            next := s.next + 1 } := by
        rw [e1]; simp [Sem.enter, g, Sf]
      have e2' : PyCore.step I t = some
          { t with
            stack := g0' :: { f' with ctrl := .wait, kont := K' } :: fs'
            cells := PyCore.initCells t.cells t.next bound
            next := t.next + 1 } := by
        rw [e2]; simp [trScope, PyCore.enter, g0', Sf, bd, hkS]
      let t1 : PyCore.Config σ := { t with cells := PyCore.initCells t.cells t.next bound, next := t.next + 1 }
      let gs : List (PyCore.Frame σ) := { f' with ctrl := .wait, kont := K' } :: fs'
      obtain ⟨ys, py, hfy⟩ := param_path (I := I) t1 g0' gs (Sf :: C) [.ret (sub l 2) (trE (Sf :: C) b)] [] ps
      have e3 : PyCore.step I { t1 with stack := { g0' with ctrl := .exec [.ret (sub l 2) (trE (Sf :: C) b)], kont := [] } :: gs } =
          some { t1 with stack := { g0' with ctrl := .ev (trE (Sf :: C) b), kont := [.retS, .seq []] } :: gs } := by
        simp [PyCore.step, PyCore.execStep, PyCore.top]
      exact enter_plain A hk bound (g1' := { g0' with ctrl := .ev (trE (Sf :: C) b), kont := [.retS, .seq []] }) e1' e2'
        (py.append (.cons e3 (.nil _))) hfoc
        (fun y hy x hx => by
          rcases List.mem_append.1 hy with hy | hy
          · obtain ⟨q, hq, rfl⟩ := hfy y hy x hx; rw [sub_div _ _ (by omega)]; exact h8 q hq
          · simp only [List.mem_singleton] at hy; subst hy
            simp [PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx, sub_div _ _ (by omega)]; exact h7)
        rfl rfl
        ⟨⟨hn, rfl, h1, h2, rfl, trivial, h4, h5, rfl, h10⟩, fun S' C' e => by cases e; exact h7, UAll, true,
          .ev h9, .core (.retS (.core .seqNil))⟩ hret hE


/-! ## Parts of a parameter list -/

/-- A parameter's default and annotation. -/
def pex (q : Param) : List Expr := q.dflt.toList ++ q.ann.toList

theorem pex_dflt {q : Param} {e : Expr} (h : q.dflt = some e) : e ∈ pex q := by simp [pex, h]

theorem pex_ann {q : Param} {e : Expr} (h : q.ann = some e) : e ∈ pex q := by simp [pex, h]

theorem itemsPs_mem {C : List Scope} {q : Param} {e : Expr} {x : Item} :
    ∀ {ps : List Param}, q ∈ ps → e ∈ pex q → x ∈ itemsE C e → x ∈ itemsPs C ps
  | [], h, _, _ => by simp at h
  | .mk l y k d a :: ps, h, he, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [pex, Param.dflt, Param.ann, List.mem_append, Option.mem_toList] at he
      rcases he with rfl | rfl <;> simp [itemsPs, itemsO, hx]
    · simp [itemsPs, itemsPs_mem h he hx]

theorem touchPs_mem {q : Param} {e : Expr} {x : Label × Expr} :
    ∀ {ps : List Param}, q ∈ ps → e ∈ pex q → x ∈ touchE e → x ∈ touchPs ps
  | [], h, _, _ => by simp at h
  | .mk l y k d a :: ps, h, he, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [pex, Param.dflt, Param.ann, List.mem_append, Option.mem_toList] at he
      rcases he with rfl | rfl <;> simp [touchPs, touchO, hx]
    · simp [touchPs, touchPs_mem h he hx]

theorem okPs_mem {q : Param} {e : Expr} : ∀ {ps : List Param}, okPs ps = true → q ∈ ps → e ∈ pex q → okE e = true
  | [], _, h, _ => by simp at h
  | .mk l y k d a :: ps, ho, h, he => by
    simp only [okPs, Bool.and_eq_true] at ho
    rcases List.mem_cons.1 h with rfl | h
    · simp only [pex, Param.dflt, Param.ann, List.mem_append, Option.mem_toList] at he
      rcases he with rfl | rfl
      · simpa [okO] using ho.1.1.2
      · simpa [okO] using ho.1.2
    · exact okPs_mem ho.2 h he

theorem labelsPs_mem {q : Param} {e : Expr} {l' : Label} :
    ∀ {ps : List Param}, q ∈ ps → e ∈ pex q → l' ∈ labelsE e → l' ∈ labelsPs ps
  | [], h, _, _ => by simp at h
  | .mk l y k d a :: ps, h, he, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [pex, Param.dflt, Param.ann, List.mem_append, Option.mem_toList] at he
      rcases he with rfl | rfl <;> simp [labelsPs, labelsO, hx]
    · simp [labelsPs, labelsPs_mem h he hx]

theorem nodup_labelsPs {q : Param} {e : Expr} :
    ∀ {ps : List Param}, q ∈ ps → e ∈ pex q → (labelsPs ps).Nodup → (labelsE e).Nodup
  | [], h, _, _ => by simp at h
  | .mk l y k d a :: ps, h, he, hn => by
    simp only [labelsPs, List.nodup_cons, List.nodup_append] at hn
    rcases List.mem_cons.1 h with rfl | h
    · simp only [pex, Param.dflt, Param.ann, List.mem_append, Option.mem_toList] at he
      rcases he with rfl | rfl
      · simpa [labelsO] using hn.1.1.2
      · simpa [labelsO] using hn.1.2.1
    · exact nodup_labelsPs h he hn.2.1

theorem trDfs_eq (C : List Scope) : ∀ ps : List Param, trDfs C ps = (ps.filterMap Param.dflt).map (trE C)
  | [] => rfl
  | .mk _ _ _ none _ :: ps => by simp only [trDfs, trDfs_eq C ps]; rfl
  | .mk _ _ _ (some d) _ :: ps => by simp only [trDfs, trDfs_eq C ps]; rfl

theorem mem_dflts {e : Expr} {ps : List Param} (h : e ∈ ps.filterMap Param.dflt) : ∃ q ∈ ps, e ∈ pex q := by
  obtain ⟨q, hq, he⟩ := List.mem_filterMap.1 h
  exact ⟨q, hq, pex_dflt he⟩

theorem partsR_map {x : Cx} {U : Label → Prop} {l : Label} :
    ∀ {es : List Expr}, (∀ e ∈ es, GoodE x.p x.C U e) → PartsR x U l (es.map some) (es.map (trE x.C))
  | [], _ => trivial
  | _ :: _, h => ⟨⟨h _ List.mem_cons_self, rfl⟩, partsR_map fun e he => h e (List.mem_cons_of_mem _ he)⟩

section
variable {C : List Scope} {U : Label → Prop} {l : Label} {ps : List Param} {b : Expr}

theorem lam_pitems {x : PyCore.Item} {e : PE} (he : e ∈ trDfs C ps) (hx : x ∈ PyCore.itemsE R0 (trChain C) e) :
    x ∈ PyCore.itemsE R0 (trChain C) (trE C (.lam l ps b)) := by
  simp only [trE, gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false,
    List.nil_append]
  exact items_fold _ _ x (.inr ⟨e, by simp [he], hx⟩)

/-- A lambda's default, in the scope around it. -/
theorem good_lam_dflt (h : GoodE p C U (.lam l ps b)) {e : Expr} (he : e ∈ ps.filterMap Param.dflt) :
    GoodE p C U e := by
  obtain ⟨q, hq, hpe⟩ := mem_dflts he
  have hnd := h.nd; simp only [labelsE, List.nodup_cons, List.nodup_append] at hnd
  have hok := h.ok; simp only [okE, Bool.and_eq_true] at hok
  exact GoodE.of h (fun x hx => by simp [itemsE, itemsPs_mem hq hpe hx])
    (fun x hx => lam_pitems (by rw [trDfs_eq]; exact List.mem_map_of_mem he) hx) (fun _ => okPs_mem hok.1 hq hpe)
    (fun x hx => by simp [labelsE, labelsPs_mem hq hpe hx]) (fun _ => nodup_labelsPs hq hpe hnd.1.2)
    (fun x hx => by simp [touchE, touchPs_mem hq hpe hx])

end


/-! ## Parts of a `def` -/

/-- The annotations a `def` evaluates, in CPython's order (`annOrder`). -/
def annL (ps : List Param) (r : Option Expr) : List Expr :=
  let of (k : PKind) := (ps.filter (Param.kind · == k)).filterMap Param.ann
  of .pos ++ of .posonly ++ of .vararg ++ of .kwonly ++ of .kwarg ++ r.toList

theorem annOrder_eq (ps : List Param) (r : Option Expr) : annOrder ps r = (annL ps r).map some := rfl

/-- The PyCore record of a `def`'s decorators, defaults and annotations. -/
def defParts (C : List Scope) (ps : List Param) (ds : List Expr) (r : Option Expr) : List PE :=
  trEs C ds ++ trDfs C ps ++ trAnnK C .pos ps ++ trAnnK C .posonly ps ++ trAnnK C .vararg ps ++
    trAnnK C .kwonly ps ++ trAnnK C .kwarg ps ++ (match r with | some r => [trE C r] | none => [])

theorem trEs_eq' (C : List Scope) : ∀ es : List Expr, trEs C es = es.map (trE C)
  | [] => rfl
  | e :: es => by simp [trEs, trEs_eq' C es]

theorem trAnnK_eq (C : List Scope) (k : PKind) : ∀ ps : List Param,
    trAnnK C k ps = ((ps.filter (Param.kind · == k)).filterMap Param.ann).map (trE C)
  | [] => rfl
  | .mk l x k' d a :: ps => by
    have ih := trAnnK_eq C k ps
    have hf : (Param.mk l x k' d a :: ps).filter (Param.kind · == k) =
        if k' = k then Param.mk l x k' d a :: ps.filter (Param.kind · == k) else ps.filter (Param.kind · == k) := by
      rw [List.filter_cons]; by_cases h : k' = k <;> simp [h, Param.kind]
    rw [hf]
    cases a <;> by_cases h : k' = k <;> simp [trAnnK, h, ih, Param.ann, List.filterMap_cons]

theorem defParts_eq (C : List Scope) (ps : List Param) (ds : List Expr) (r : Option Expr) :
    defParts C ps ds r = (ds ++ ps.filterMap Param.dflt ++ annL ps r).map (trE C) := by
  simp only [defParts, trEs_eq', trDfs_eq, trAnnK_eq, annL, List.map_append]
  cases r <;> simp

theorem mem_annL {e : Expr} {ps : List Param} {r : Option Expr} (h : e ∈ annL ps r) :
    (∃ q ∈ ps, e ∈ pex q) ∨ r = some e := by
  simp only [annL, List.mem_append, Option.mem_toList] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  all_goals first
    | exact .inr h
    | (obtain ⟨q, hq, he⟩ := List.mem_filterMap.1 h
       exact .inl ⟨q, (List.mem_filter.1 hq).1, pex_ann he⟩)

theorem trS_defn (C : List Scope) (l : Label) (g : Name) (ps : List Param) (b : List Stmt) (ds : List Expr)
    (r : Option Expr) : trS C (.defn l g ps b ds r) = .assign (sub l 0) (mangle (priv C) g)
      (gad l 2 (.defn ds.length ps.length) (defParts C ps ds r ++ ps.map (paramMark (.fn l g ps b :: C)) ++
        [defFn C l g ps b])) := rfl

theorem GoodB.head {C : List Scope} {U : Label → Prop} {st : Stmt} {ss : List Stmt} (h : GoodB p C U (st :: ss)) :
    GoodB p C U [st] :=
  ⟨fun x hx => h.s x (by simp_all [itemsB]), fun x hx => h.t x (by simp_all [trB, PyCore.itemsB]),
    by have := h.ok; simp [okB] at this; simp [okB, this.1], fun l hl => h.u l (by simp_all [labelsB]),
    fun _ => h.pv (by simp), by have := h.nd; simp only [labelsB, List.nodup_append] at this; simpa [labelsB] using this.1,
    fun x hx => h.tch x (by simp_all [touchB])⟩

/-- A `def`'s decorator, default or annotation, in the scope around it. -/
theorem good_defn_part {C : List Scope} {U : Label → Prop} {l : Label} {g : Name} {ps : List Param} {b : List Stmt}
    {ds : List Expr} {r : Option Expr} {ss : List Stmt} (h : GoodB p C U (.defn l g ps b ds r :: ss)) {e : Expr}
    (he : e ∈ ds ++ ps.filterMap Param.dflt ++ annL ps r) : GoodE p C U e := by
  have hpe : trE C e ∈ defParts C ps ds r := by rw [defParts_eq]; exact List.mem_map_of_mem he
  have ht : ∀ x, x ∈ PyCore.itemsE R0 (trChain C) (trE C e) →
      x ∈ PyCore.itemsS R0 (trChain C) (trS C (.defn l g ps b ds r)) := by
    intro x hx
    rw [trS_defn]
    simp only [gad, cc, ccR, recR, PyCore.itemsS, PyCore.itemsE, r0_s, r0_e, Option.isSome_none, Bool.false_eq_true,
      ite_false, List.nil_append]
    exact List.mem_cons_of_mem _ (items_fold _ _ x (.inr ⟨_, by simp [hpe], hx⟩))
  simp only [List.mem_append] at he
  rcases he with (he | he) | he
  · exact GoodB.e h (fun x hx => by simp [itemsS, itemsEs_mem he hx]) ht
      (fun ho => by simp only [okS, Bool.and_eq_true] at ho; exact okEs_mem ho.1.2 he)
      (fun x hx => by simp [labelsS, labelsEs_mem he hx])
      (fun hn => by simp only [labelsS, List.nodup_cons, List.nodup_append] at hn; exact nodup_labelsEs he hn.1.2.1)
      (fun x hx => by simp [touchS, touchEs_mem he hx])
  · obtain ⟨q, hq, hpq⟩ := mem_dflts he
    exact GoodB.e h (fun x hx => by simp [itemsS, itemsPs_mem hq hpq hx]) ht
      (fun ho => by simp only [okS, Bool.and_eq_true] at ho; exact okPs_mem ho.1.1.1.2 hq hpq)
      (fun x hx => by simp [labelsS, labelsPs_mem hq hpq hx])
      (fun hn => by simp only [labelsS, List.nodup_cons, List.nodup_append] at hn; exact nodup_labelsPs hq hpq hn.1.1.1.2)
      (fun x hx => by simp [touchS, touchPs_mem hq hpq hx])
  · rcases mem_annL he with ⟨q, hq, hpq⟩ | rfl
    · exact GoodB.e h (fun x hx => by simp [itemsS, itemsPs_mem hq hpq hx]) ht
        (fun ho => by simp only [okS, Bool.and_eq_true] at ho; exact okPs_mem ho.1.1.1.2 hq hpq)
        (fun x hx => by simp [labelsS, labelsPs_mem hq hpq hx])
        (fun hn => by simp only [labelsS, List.nodup_cons, List.nodup_append] at hn; exact nodup_labelsPs hq hpq hn.1.1.1.2)
        (fun x hx => by simp [touchS, touchPs_mem hq hpq hx])
    · exact GoodB.e h (fun x hx => by simp [itemsS, itemsO, hx]) ht
        (fun ho => by simp only [okS, Bool.and_eq_true] at ho; simpa [okO] using ho.2)
        (fun x hx => by simp [labelsS, labelsO, hx])
        (fun hn => by simp only [labelsS, List.nodup_cons, List.nodup_append] at hn; simpa [labelsO] using hn.2.1)
        (fun x hx => by simp [touchS, touchO, hx])

/-! ## `$call`'s split of its record (as `$cls`'s, `T2Class.lean`) -/

theorem markStar_kw (x : Option Name) : Py.markStar (.prim (Py.kwMarker x)) = none := by
  cases x with
  | none => simp [Py.kwMarker, Py.markStar]
  | some x =>
    simp only [Py.kwMarker, Py.markStar]
    split <;> rename_i h <;> (try rfl) <;> (have := congrArg String.toList (Val.prim.inj h); simp at this)

theorem markStar_sm (e : Expr) : (Py.markStar (pval (starMark e))).isSome = true := by
  cases e <;> simp [starMark, pval, Py.markStar]

theorem takeWhile_appP {α} {q : α → Bool} : ∀ {A B : List α}, (∀ a ∈ A, q a = true) →
    (∀ b, B.head? = some b → q b = false) → (A ++ B).takeWhile q = A
  | [], [], _, _ => rfl
  | [], b :: B, _, hb => by simp [hb b rfl]
  | a :: A, B, ha, hb => by
    simp [ha a List.mem_cons_self, takeWhile_appP (fun c hc => ha c (List.mem_cons_of_mem _ hc)) hb]

theorem zip_star : ∀ (bs : List Expr) (bv : List Val), bv.length = bs.length →
    ∀ p ∈ ((bs.map starMark).map pval).zip bv, (Py.markStar p.1).isSome = true
  | [], [], _ => by simp
  | e :: bs, v :: bv, h => by
    intro p hp
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact markStar_sm e
    · exact zip_star bs bv (by simpa using h) p hp

theorem zip_star_mapM : ∀ (bs : List Expr) (bv : List Val), bv.length = bs.length →
    (((bs.map starMark).map pval).zip bv).mapM (Py.markStar ·.1) = some (bs.map isStar)
  | [], [], _ => rfl
  | e :: bs, v :: bv, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, zip_star_mapM bs bv (by simpa using h)]
    cases e <;> simp [starMark, pval, Py.markStar, isStar]

theorem zip_kw_mapM : ∀ (kws : List Kw) (kv : List Val), kv.length = kws.length →
    (((kws.map kwMark).map pval).zip kv).mapM (Py.markKw ·.1) = some (kws.map kwN)
  | [], [], _ => rfl
  | .mk l x e :: kws, v :: kv, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, zip_kw_mapM kws kv (by simpa using h)]
    simp [kwMark, pval, markKw_kw, kwN]

theorem zip_snd : ∀ (ms vs : List Val), ms.length = vs.length → (ms.zip vs).map (·.2) = vs
  | [], [], _ => rfl
  | _ :: ms, v :: vs, h => by simp [zip_snd ms vs (by simpa using h)]

/-- `$call` splits its record's values and markers into the positional arguments and the keywords. -/
theorem split_call (bs : List Expr) (kws : List Kw) (bv kv : List Val) (hb : bv.length = bs.length)
    (hk : kv.length = kws.length) :
    (Py.pairs (bv ++ kv ++ (bs.map starMark ++ kws.map kwMark).map pval)).bind Py.splitArgs =
      some (bs.map isStar, bv, kws.map kwN, kv) := by
  rw [pairs_app (by simp [hb, hk])]
  simp only [Option.bind_some, List.map_append]
  rw [List.zip_append (by simp [hb])]
  have htw : (((bs.map starMark).map pval).zip bv ++ ((kws.map kwMark).map pval).zip kv).takeWhile
      (fun p => (Py.markStar p.1).isSome) = ((bs.map starMark).map pval).zip bv := by
    refine takeWhile_appP (zip_star bs bv hb) fun b hb' => ?_
    cases kws with
    | nil => simp at hb'
    | cons k kws =>
      cases kv with
      | nil => simp at hb'
      | cons v kv =>
        cases k with
        | mk l x e =>
          simp only [List.map_cons, List.zip_cons_cons, List.head?_cons, Option.some.injEq] at hb'
          subst hb'; simp [kwMark, pval, markStar_kw]
  simp only [Py.splitArgs, htw, List.drop_left]
  rw [zip_star_mapM bs bv hb, zip_kw_mapM kws kv hk, zip_snd _ _ (by simp [hb]), zip_snd _ _ (by simp [hk])]

/-- Both runs' positional and keyword phases of a call, from the same arguments. -/
theorem arg_phase {C : List Scope} {x : Cx} {U : Label → Prop} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hk : KRel x U true K0 K0') (c : Sem.Config σ) (g0 : Sem.Frame σ) (gs : List (Sem.Frame σ))
    (c' : PyCore.Config σ) (g0' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (gv : Val) (args : List Val)
    (st : List Bool) (kws : List (Option Name)) (kwvals : List Val) :
    ∃ ctl ctl' k k', Sem.argPhase I c g0 gs (.call gv) args st kws kwvals K0 =
        some { c with stack := { g0 with ctrl := ctl, kont := k } :: gs } ∧
      PyCore.argPhase c' g0' gs' (.call gv) args st kws kwvals K0' =
        some { c' with stack := { g0' with ctrl := ctl', kont := k' } :: gs' } ∧
      CR p C U true ctl ctl' ∧ KRel x U true k k' ∧ EnterSub k K0 := by
  by_cases h1 : st.any id = true
  · exact ⟨.op (.display (.tuple st)) args, .op (.display (.tuple st)) args, .argStar (.call gv) kws kwvals :: K0,
      .argStar (.call gv) kws kwvals :: K0', by simp [Sem.argPhase, h1, Sem.doOp, Sem.setC],
      by simp [PyCore.argPhase, h1, PyCore.top], .op, .call (.argStar hk), fun _ _ _ hm => by simpa using hm⟩
  · by_cases h2 : kws.any Option.isNone = true
    · exact ⟨.op (.display (.kwargs kws)) kwvals, .op (.display (.kwargs kws)) kwvals, .argKw (.call gv) args :: K0,
        .argKw (.call gv) args :: K0', by simp [Sem.argPhase, h1, Sem.kwPhase, h2, Sem.doOp, Sem.setC],
        by simp [PyCore.argPhase, h1, PyCore.kwPhase, h2, PyCore.top], .op, .call (.argKw hk),
        fun _ _ _ hm => by simpa using hm⟩
    · exact ⟨.call gv args ((kws.filterMap id).zip kwvals), .call gv args ((kws.filterMap id).zip kwvals), K0, K0',
        by simp [Sem.argPhase, h1, Sem.kwPhase, h2, Sem.finishArgs, Sem.setC],
        by simp [PyCore.argPhase, h1, PyCore.kwPhase, h2, PyCore.finishArgs, PyCore.top], .call, hk, esub_refl⟩

/-! ## A part's value, the next part entered -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A part's value reaches an `evs` item with a next part `e`: Surf enters `e`, PyCore adds the value to
the record and enters `e`'s translation. -/
theorem val_mid (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {e : Expr} {rest' : List (Option Expr)}
    {acc : List Val} {T : Sem.Then} {K0 : List (Sem.Kont σ)} {ps : List PE} {K1 : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs (some e :: rest') acc T :: K0) (hK' : f'.kont = recK acc.reverse (trE f.chain e :: ps) K1)
    (hge : GoodE p f.chain U e)
    (hk1 : KRel (cx p (Seen (Touch p) H
        [{ s with stack := { f with ctrl := .ev e, kont := .evs rest' (v :: acc) T :: K0 } :: fs }, s])
        (rdOf t f') (ownOf t f') f) U true (.evs rest' (v :: acc) T :: K0) (recK (v :: acc).reverse ps K1)) :
    Goal I p H s t := by
  let s1 : Sem.Config σ := { s with stack := { f with ctrl := .ev e, kont := .evs rest' (v :: acc) T :: K0 } :: fs }
  have e1 : Sem.step I s = some s1 := by simp [s1, Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
  let KR : List (PyCore.Kont σ) := recK (acc.reverse ++ [v]) ps K1
  have st1 := pstep_rec (I := I) (done := acc.reverse) A.ht hc'
    (K1 := (trE f.chain e :: ps).map (.binL ",") ++ K1) (by rw [hK']; simp [recK])
  have st2 : PyCore.step I { t with stack := { f' with
      ctrl := .val (.data "$args" (acc.reverse ++ [v])), kont := (trE f.chain e :: ps).map (.binL ",") ++ K1 } :: fs' } =
      some { t with stack := { f' with ctrl := .ev (trE f.chain e), kont := KR } :: fs' } := by
    simp [PyCore.step, PyCore.valStep, PyCore.top, recK, KR]
  have hH' : ∀ l, H l → Seen (Touch p) H [s1, s] l := fun _ h => .inl h
  rw [List.reverse_cons] at hk1
  refine goal_t (.cons e1 (.nil _)) (by simp) (.cons st1 (.cons st2 (.nil _))) (by simp)
    (.inl (((A.zero.upd (.ev e) (.evs rest' (v :: acc) T :: K0) (.ev (trE f.chain e)) KR
      (fun _ _ _ hm => by rw [hK]; simpa using hm)).mono_H hH').crel (.ev hge) hk1)) (cover_none ?_)
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl <;> simp [PyCore.focus, A.ht, hc']

end

/-- The next part of a call after the `n + 1` values so far: an argument (unstarred) or a keyword's value. -/
theorem call_next {g : Expr} {args : List Expr} {kws : List Kw} {n : Nat} {e : Expr} {rest' : List (Option Expr)}
    (h : (partsCall g args kws).drop (n + 1) = some e :: rest') :
    (∃ a, args[n]? = some a ∧ e = unstar a ∧ args.take (n + 1) = args.take n ++ [a] ∧
      kws.take (n + 1 - args.length) = kws.take (n - args.length)) ∨
    (∃ lk y, args.length ≤ n ∧ kws[n - args.length]? = some (.mk lk y e) ∧ args.take (n + 1) = args.take n ∧
      kws.take (n + 1 - args.length) = kws.take (n - args.length) ++ [.mk lk y e]) := by
  have h1 : (partsCall g args kws)[n + 1]? = some (some e) := by
    rw [← List.head?_drop, h]; rfl
  simp only [partsCall, List.cons_append, List.getElem?_cons_succ] at h1
  by_cases hn : n < args.length
  · left
    rw [List.getElem?_append_left (by simpa using hn), List.getElem?_map] at h1
    obtain ⟨a, ha⟩ : ∃ a, args[n]? = some a := ⟨_, List.getElem?_eq_getElem hn⟩
    rw [ha] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    refine ⟨a, ha, h1.symm, by rw [List.take_add_one, ha]; rfl, ?_⟩
    rw [show n + 1 - args.length = 0 by omega, show n - args.length = 0 by omega]
  · right
    rw [List.getElem?_append_right (by simp; omega), List.getElem?_map, List.length_map] at h1
    cases hk : kws[n - args.length]? with
    | none => rw [hk] at h1; cases h1
    | some k =>
      rw [hk] at h1
      obtain ⟨lk, y, v⟩ := k
      simp only [Option.map_some, Option.some.injEq] at h1
      subst h1
      refine ⟨lk, y, by omega, rfl, by rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)], ?_⟩
      rw [show n + 1 - args.length = n - args.length + 1 by omega, List.take_add_one, hk]; rfl

theorem star_mark (e : Expr) :
    starMark e = .const (sub (Sem.Expr.lbl e) 57) (if isStar e then "$star" else "$pos") := by
  cases e <;> simp [starMark, isStar, Sem.Expr.lbl, Expr.label]

theorem touchKs_self {lk : Label} {y : Option Name} {v : Expr} :
    ∀ {kws : List Kw}, Kw.mk lk y v ∈ kws → (lk, v) ∈ touchKs kws
  | [], h => by simp at h
  | .mk _ _ _ :: kws, h => by
    rcases List.mem_cons.1 h with e | h
    · cases e; simp [touchKs]
    · simp [touchKs, touchKs_self h]

theorem call_marks_const (args : List Expr) (kws : List Kw) :
    ∀ m ∈ args.map starMark ++ kws.map kwMark, ∃ r k, m = .const r k ∧ Py.constVal I k = .prim k := by
  intro m hm
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hm
    rw [star_mark]; exact ⟨_, _, rfl, by split <;> first | exact kc_star I | exact kc_pos I⟩
  · obtain ⟨⟨lk, y, e⟩, -, rfl⟩ := List.mem_map.1 hm
    exact ⟨_, _, rfl, kc_kw I y⟩

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A value reaches a call's `evs` item: the next part entered, or (the last) the call's phases. -/
theorem val_evsCall (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} {l : Label} {g : Expr} {args : List Expr} {kws : List Kw}
    {rest : List (Option Expr)} {acc : List Val} {ps : List PE}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs rest acc (.call args.length (args.map isStar) (kws.map kwN)) :: K0)
    (hK' : f'.kont = recK acc.reverse (ps ++ args.map starMark ++ kws.map kwMark) (.callA (.prim Gadget.call.name) :: K0'))
    (hg : GoodE p f.chain U (.call l g args kws)) (hlt : acc.length < (partsCall g args kws).length)
    (hrest : rest = (partsCall g args kws).drop (acc.length + 1))
    (hHa : ∀ a ∈ args.take acc.length, H (Sem.Expr.lbl a)) (hHk : ∀ k ∈ kws.take (acc.length - args.length), H k.lbl)
    (hpr : PartsR A.x U l rest ps) (hk : KRel A.x U true K0 K0') : Goal I p H s t := by
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  match rest, ps, hpr with
  | [], [], _ =>
    have hlen : acc.length + 1 = (partsCall g args kws).length := by
      have := congrArg List.length hrest; simp at this; omega
    have hpl : (partsCall g args kws).length = 1 + args.length + kws.length := by simp [partsCall]; omega
    have hHa' : ∀ a ∈ args, H (Sem.Expr.lbl a) := fun a ha =>
      hHa a (by rw [List.take_of_length_le (by omega)]; exact ha)
    have hHk' : ∀ k ∈ kws, H k.lbl := fun k hk =>
      hHk k (by rw [List.take_of_length_le (by omega)]; exact hk)
    obtain ⟨g0, restv, hv⟩ : ∃ g0 restv, acc.reverse ++ [v] = g0 :: restv := by
      cases acc.reverse with
      | nil => exact ⟨v, [], rfl⟩
      | cons a as => exact ⟨a, as ++ [v], rfl⟩
    have hrl : restv.length = args.length + kws.length := by
      have := congrArg List.length hv; simp at this; omega
    let T : Sem.Then := .call args.length (args.map isStar) (kws.map kwN)
    let fe : Sem.Frame σ := { f with ctrl := .val (.tuple (acc.reverse ++ [v])), kont := .evsEnd T :: K0 }
    let se : Sem.Config σ := { s with stack := fe :: fs }
    have e1 : Sem.step I s = some se := by
      simp [se, fe, T, Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC]
    obtain ⟨ctl, ctl', k, k', ha1, ha2, hcr, hk1, he1⟩ := arg_phase (I := I) (C := f.chain) hk se fe fs
      { t with stack := { f' with ctrl := .val (.data "$args" (acc.reverse ++ [v] ++
          (args.map starMark ++ kws.map kwMark).map pval)), kont := .callA (.prim Gadget.call.name) :: K0' } :: fs' }
      { f' with ctrl := .val (.data "$args" (acc.reverse ++ [v] ++
          (args.map starMark ++ kws.map kwMark).map pval)), kont := K0' } fs' g0
      (restv.take args.length) (args.map isStar) (kws.map kwN) (restv.drop args.length)
    have e2 : Sem.step I se = some { s with stack := { f with ctrl := ctl, kont := k } :: fs } := by
      have : Sem.step I se = Sem.argPhase I se fe fs (.call g0) (restv.take args.length) (args.map isStar)
          (kws.map kwN) (restv.drop args.length) K0 := by
        simp [se, fe, T, Sem.step, Sem.valStep, Sem.finish, hv]
      rw [this, ha1]
    have st1 := pstep_rec (I := I) (done := acc.reverse) A.ht hc'
      (K1 := (args.map starMark ++ kws.map kwMark).map (.binL ",") ++ .callA (.prim Gadget.call.name) :: K0')
      (by rw [hK']; simp [recK])
    obtain ⟨ys, py, hfy⟩ := rec_consts (I := I) t f' fs' (args.map starMark ++ kws.map kwMark) (acc.reverse ++ [v])
      (.callA (.prim Gadget.call.name) :: K0') (call_marks_const args kws)
    have st2 : PyCore.step I { t with stack := { f' with ctrl := .val (.data "$args" (acc.reverse ++ [v] ++
          (args.map starMark ++ kws.map kwMark).map pval)), kont := .callA (.prim Gadget.call.name) :: K0' } :: fs' } =
        some { t with stack := { f' with ctrl := ctl', kont := k' } :: fs' } := by
      rw [← ha2]
      have hsp := split_call args kws (restv.take args.length) (restv.drop args.length) (by simp; omega) (by simp; omega)
      have hvs : acc.reverse ++ [v] ++ (args.map starMark ++ kws.map kwMark).map pval = g0 :: (restv.take args.length ++
          restv.drop args.length ++ (args.map starMark ++ kws.map kwMark).map pval) := by
        rw [hv, List.take_append_drop]; rfl
      rw [hvs]
      simp only [PyCore.step, PyCore.valStep, PyCore.callStep, gad_name .call trivial, PyCore.gadgetStep, PyCore.argList,
        hsp]
    refine goal_b (.cons e1 (.cons e2 (.nil _))) (by simp) (.cons st1 (py.append (.cons st2 (.nil _)))) (by simp)
      (crelI_seen (A.set hcr hk1 fun o b kx hm => by rw [hK]; exact List.mem_cons_of_mem _ (he1 o b kx hm))) ?_
    intro y hy x hx
    have hx := pfocus_le hx
    rcases List.mem_cons.1 hy with rfl | hy
    · simp [PyCore.focus, A.ht, hc'] at hx
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨m, hm, rfl⟩ := hfy y hy x hx
      refine .inl ?_
      rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hm
        rw [star_mark]; simp only [PyCore.Expr.label]; rw [sub_div _ _ (by omega)]; exact hHa' a ha
      · obtain ⟨⟨lk, y, e⟩, hk, rfl⟩ := List.mem_map.1 hm
        simp only [kwMark, PyCore.Expr.label]; rw [sub_div _ _ (by omega)]; exact hHk' _ hk
    · simp at hy; subst hy; simp [PyCore.focus] at hx
  | some e :: rest', pe :: ps', ⟨⟨hge, hpe⟩, hr'⟩ =>
    subst hpe
    have hd : (partsCall g args kws).drop (acc.length + 1) = some e :: rest' := hrest.symm
    let T : Sem.Then := .call args.length (args.map isStar) (kws.map kwN)
    let s1 : Sem.Config σ := { s with stack := { f with ctrl := .ev e, kont := .evs rest' (v :: acc) T :: K0 } :: fs }
    have hT : ∀ c, (c, e) ∈ touchB p → Touch p s1 c := fun c h => .inr (by simp [s1, TouchF, h])
    have hlt2 : acc.length + 1 < (partsCall g args kws).length := by
      have := congrArg List.length hd; simp at this; omega
    have hrest2 : rest' = (partsCall g args kws).drop ((v :: acc).length + 1) := by
      rw [List.length_cons, ← List.drop_drop, hd]; rfl
    have hHa2 : ∀ a ∈ args.take (acc.length + 1), Seen (Touch p) H [s1, s] (Sem.Expr.lbl a) := by
      intro a ha
      rcases call_next hd with ⟨a0, ha0, he0, htk, -⟩ | ⟨lk, y, -, -, htk, -⟩
      · rw [htk] at ha
        rcases List.mem_append.1 ha with ha | ha
        · exact .inl (hHa a ha)
        · simp only [List.mem_singleton] at ha; subst ha; subst he0
          refine .inr ⟨s1, by simp, ?_⟩
          cases a with
          | star ls a1 =>
            have h1 : (ls, a1) ∈ touchE (.star ls a1) := by simp [touchE]
            have h2 : (ls, a1) ∈ touchE (.call l g args kws) := by
              simp [touchE, touchEs_mem (List.mem_of_getElem? ha0) h1]
            exact hT ls (hg.tch _ h2)
          | _ => exact .inl (by simp [s1, Sem.focus, unstar])
      · rw [htk] at ha; exact .inl (hHa a ha)
    have hHk2 : ∀ k ∈ kws.take ((v :: acc).length - args.length), Seen (Touch p) H [s1, s] k.lbl := by
      intro k hk
      rw [List.length_cons] at hk
      rcases call_next hd with ⟨-, -, -, -, htk⟩ | ⟨lk, y, -, hk0, -, htk⟩
      · rw [htk] at hk; exact .inl (hHk k hk)
      · rw [htk] at hk
        rcases List.mem_append.1 hk with hk | hk
        · exact .inl (hHk k hk)
        · simp only [List.mem_singleton] at hk; subst hk
          exact .inr ⟨s1, by simp, hT lk (hg.tch _ (by simp [touchE, touchKs_self (List.mem_of_getElem? hk0)]))⟩
    exact val_mid A (e := e) (rest' := rest') (T := .call args.length (args.map isStar) (kws.map kwN)) (K0 := K0)
      (ps := ps' ++ args.map starMark ++ kws.map kwMark) (K1 := .callA (.prim Gadget.call.name) :: K0') hc hc' hK
      (by rw [hK']; rfl) hge
      (.call (.evsCall hg (by simpa using hlt2) hrest2 hHa2 hHk2 (partsR_with hr')
        (KRel.ext ⟨fun _ h => .inl h, Agree.refl _ _ _⟩ hk)))
  | none :: _, _, _ =>
    have := List.mem_of_mem_drop (hrest ▸ List.mem_cons_self : none ∈ (partsCall g args kws).drop (acc.length + 1))
    simp [partsCall] at this
    obtain ⟨⟨_, _, _⟩, -, h⟩ := this
    cases h

end

/-! ## The function object made: Surf's `close`, PyCore's `Close` then `$def` -/

/-- PyCore's closure of `S'`, made in the frame `f'`, with the signature `sg`. -/
def cloP (f' : PyCore.Frame σ) (S' : PyCore.Scope) (sg : Option PyCore.Sig) : PyCore.Obj σ :=
  .clo S' f'.chain (Py.memo S'.names (PyCore.clsOf (S' :: f'.chain))).get (Py.memo S'.names (PyCore.capture f' S')).get sg

theorem cellOf_eq {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {x : Name} (hx : ¬ Dot x) :
    PyCore.cellOf f' x = Sem.cellOf f x := by
  simp only [PyCore.cellOf, Sem.cellOf, hf.kind, cls_eq hf hx, hf.id, hf.κ x hx]
  cases f.kind <;> rfl

/-- A function object made for a `def` or lambda, related to PyCore's closure of its translated scope. -/
theorem orel_fn {H : Label → Prop} {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {gl cs} {S : Scope}
    {dflt : List (Option Val)} {sg : Option PyCore.Sig} (hsig : SigR S f.chain dflt sg) (hH : H S.label)
    (hp : ∀ q ∈ S.params, H q.label) (hg : GoodSc p f.chain S) (hk : KOk (S :: f.chain)) :
    ORel p H gl cs (Sem.mkClo f S dflt) (cloP f' (trScope f.chain S) sg) := by
  simp only [Sem.mkClo, cloP]
  rw [hf.chain]
  refine ORel.clo (Py.memo_eq _ _) (Py.memo_eq _ _) rfl (fun x hx => ?_) (fun x a h => ?_) hsig hH hp hg hk
  · simp only [Py.memo_eq, PyCore.capture, hf.chain]
    rw [show PyCore.clsOf (trScope f.chain S :: trChain f.chain) x = PyCore.clsOf (trChain (S :: f.chain)) x from rfl,
      cls_tr (not_fresh hx), cellOf_eq hf hx]
  · simp only [Py.memo_eq] at h
    split at h
    · simp only [Sem.cellOf] at h
      split at h <;> (try split at h) <;> first | (cases h; rfl) | exact hf.κa x a h
    · cases h

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore's frame ids after an object is allocated at `next`. -/
theorem ids_alloc {t1 : PyCore.Config σ} {g' : PyCore.Frame σ} {ob : PyCore.Obj σ} (h : Ids t)
    (ht : t.stack = f' :: fs') (ht1 : t1.stack = g' :: fs') (ho : ∀ o, t1.objs[o]? = if t.next = o then some ob else t.objs[o]?)
    (hn : t1.next = t.next + 1) (hid : g'.id = f'.id) (hk : g'.kind = f'.kind) (hob : ∀ g, ob ≠ .gen (.susp g)) :
    Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  refine ⟨by rw [ht1]; simpa [hid] using h1, fun g hg => ?_, fun o b hb => ?_, fun o g ho1 => ?_,
    fun g hg o hgo => ?_, fun g hg hm => ?_, fun o g ho1 => ?_⟩
  · rw [ht1, List.mem_cons] at hg; rw [hn]
    rcases hg with rfl | hg
    · rw [hid]; have := h2 f' (by simp); omega
    · have := h2 g (by simp [hg]); omega
  · rw [hn]; simp only [pObj, ho] at hb; split at hb
    · omega
    · have := h3 o b hb; omega
  · simp only [pObj, ho] at ho1; split at ho1
    · cases ho1; exact absurd rfl (hob g)
    · obtain ⟨e, hne⟩ := h4 o g ho1
      refine ⟨e, fun h hh => ?_⟩
      rw [ht1, List.mem_cons] at hh
      rcases hh with rfl | hh
      · rw [hid]; exact hne _ (by simp)
      · exact hne _ (by simp [hh])
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [hid]; exact h5 _ (by simp) o (by rw [← hk]; exact hgo)
    · exact h5 _ (by simp [hg]) o hgo
  · rw [ht1, List.mem_cons] at hg
    rcases hg with rfl | hg
    · rw [hid]; exact h6 _ (by simp) (by rw [← hk]; exact hm)
    · exact h6 _ (by simp [hg]) hm
  · simp only [pObj, ho] at ho1; split at ho1
    · cases ho1; exact absurd rfl (hob g)
    · exact h7 o g ho1

/-- The configurations after a function object is made: Surf's `oS` at `next`, PyCore's `oP` (written over
the closure `o0` by `$def`), the top frames' code changed. -/
theorem crel_close (A : At p H s t f fs f' fs') {H' : Label → Prop} (hH : ∀ l, H l → H' l)
    {oS : Sem.Obj σ} {o0 oP : PyCore.Obj σ} (hob : ORel p H' t.glob t.cells oS oP)
    (hng : ∀ g, oP ≠ .gen (.susp g)) (hnS : ∀ g, oS ≠ .gen (.susp g))
    {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ} {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (hc : CR p f.chain U true c c') (hk : KRel (cx p H' (rdOf t f') (ownOf t f') f) U true k k')
    (hE : EnterSub k f.kont) :
    CRel p H'
      { s with stack := { f with ctrl := c, kont := k } :: fs, objs := s.objs.insert s.next oS, next := s.next + 1 }
      { t with
        stack := { f' with ctrl := c', kont := k' } :: fs'
        objs := (t.objs.insert t.next o0).insert t.next oP
        next := t.next + 1 } := by
  have hst := A.r.stack; rw [A.hs, A.ht] at hst
  have hn : t.next = s.next := A.r.next
  have hfree : s.objs[s.next]? = none := by
    have hr := A.r.objs s.next
    have hp : pObj t s.next = none := by
      cases h : pObj t s.next with
      | none => rfl
      | some b => have := A.r.ids.obj _ b h; omega
    simp only [sObj] at hr; rw [hp] at hr
    cases h : s.objs[s.next]? with
    | none => rfl
    | some a => rw [h] at hr; exact hr.elim
  have hlk : ∀ o, ((t.objs.insert t.next o0).insert t.next oP)[o]? = if t.next = o then some oP else t.objs[o]? := by
    intro o; rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert]; by_cases e : t.next = o <;> simp [e]
  have hen := A.r.enter; rw [A.hs] at hen
  refine ⟨⟨⟨A.hf.toFRel0.upd c k c' k', fun S C e => hH _ (A.hf.hl S C e), U, true, hc, hk⟩,
      all2_mono (fun _ _ h => h.mono_H hH) hst.2⟩, fun o => ?_, A.r.cells, A.r.glob, A.r.out, by simp [hn], A.r.res,
    A.r.st, fun x hx => A.r.wait x (by rw [A.hs]; exact hx), ?_,
    (hen.top c hE).ins (.inl hfree) fun g e => absurd e (hnS g)⟩
  · simp only [sObj, pObj]
    rw [hlk, Std.HashMap.getElem?_insert]
    by_cases e : t.next = o
    · have e' : s.next = o := hn ▸ e
      simp only [e, e', beq_self_eq_true, ite_true, PyCore.OptRel]; exact hob
    · have e' : ¬ s.next = o := hn ▸ e
      simp only [e, ite_false, beq_iff_eq, e']
      exact optRel_mono (fun _ _ h => h.mono_H hH) (A.r.objs o)
  · exact ids_alloc A.r.ids A.ht rfl hlk rfl rfl rfl hng

end

/-- PyCore's end of a `def`'s or lambda's record: the parameters' markers `ms`, the function (`Close`), then
`$def`, which writes the signature and the defaults into the closure. -/
theorem fin_def (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (vals : List Val)
    (ms : List PE) (r : Label) (kk : Bool) (x : Name) (body : PS) (nd np : Nat) (K : List (PyCore.Kont σ))
    (sig : List (Name × Py.PK × Bool))
    (hms : ∀ m ∈ ms, ∃ r k, m = .const r k ∧ Py.constVal I k = .prim k) (hnp : ms.length = np)
    (hsig : (ms.map pval).mapM Py.markParam = some sig) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with ctrl := .val (.data "$args" vals), kont := (ms ++ [PyCore.Expr.lam r kk x body]).map (.binL ",") ++ .callA (.prim (Gadget.defn nd np).name) :: K } :: fs' }
      { t with
        stack := { f' with ctrl := .val (.fn t.next), kont := .decos ((vals ++ ms.map pval ++ [Val.fn t.next]).take nd).reverse :: K } :: fs'
        objs := (t.objs.insert t.next (cloP f' (.fn r kk x body) none)).insert t.next
            (cloP f' (.fn r kk x body) (some (sig.map fun q => (q.1, q.2.1),
              Py.alignDefaults (sig.map (·.2.2))
                (((vals ++ ms.map pval ++ [Val.fn t.next]).drop nd).take (sig.filter (·.2.2)).length))))
        next := t.next + 1 } ys ∧
      ∀ y ∈ ys, ∀ z, PyCore.focus y = some z → (∃ m ∈ ms, z = m.label) ∨ z = r := by
  let lamE : PE := .lam r kk x body
  let g : Val := .prim (Gadget.defn nd np).name
  obtain ⟨ys, py, hfy⟩ := rec_consts (I := I) t f' fs' ms vals ([lamE].map (.binL ",") ++ .callA g :: K) hms
  have ek : (ms ++ [lamE]).map (.binL ",") ++ .callA g :: K = ms.map (.binL ",") ++ ([lamE].map (.binL ",") ++ .callA g :: K) := by
    simp
  let n := t.next
  let mv := ms.map pval
  let c1 : PyCore.Config σ :=
    { t with stack := { f' with ctrl := .val (.data "$args" (vals ++ mv)), kont := [lamE].map (.binL ",") ++ .callA g :: K } :: fs' }
  let c2 : PyCore.Config σ :=
    { t with stack := { f' with ctrl := .ev lamE, kont := .binR "," (.data "$args" (vals ++ mv)) :: .callA g :: K } :: fs' }
  let c3 : PyCore.Config σ :=
    { t with
      stack := { f' with ctrl := .val (.fn n), kont := .binR "," (.data "$args" (vals ++ mv)) :: .callA g :: K } :: fs'
      objs := t.objs.insert n (cloP f' (.fn r kk x body) none)
      next := n + 1 }
  let c4 : PyCore.Config σ :=
    { t with
      stack := { f' with ctrl := .val (.data "$args" (vals ++ mv ++ [Val.fn n])), kont := .callA g :: K } :: fs'
      objs := t.objs.insert n (cloP f' (.fn r kk x body) none)
      next := n + 1 }
  have st1 : PyCore.step I c1 = some c2 := by simp [c1, c2, PyCore.step, PyCore.valStep, PyCore.top]
  have st2 : PyCore.step I c2 = some c3 := by
    simp only [c2, c3, PyCore.step, PyCore.evalStep, PyCore.close, cloP]; rfl
  have st3 : PyCore.step I c3 = some c4 := by simp [c3, c4, PyCore.step, PyCore.valStep, PyCore.top]
  have hl : (vals ++ mv ++ [Val.fn n]).length - 1 - np = vals.length := by simp [mv, hnp]
  let cE : PyCore.Config σ :=
    { t with
      stack := { f' with ctrl := .val (.fn t.next), kont := .decos ((vals ++ ms.map pval ++ [Val.fn t.next]).take nd).reverse :: K } :: fs'
      objs := (t.objs.insert t.next (cloP f' (.fn r kk x body) none)).insert t.next
          (cloP f' (.fn r kk x body) (some (sig.map fun q => (q.1, q.2.1),
            Py.alignDefaults (sig.map (·.2.2))
              (((vals ++ ms.map pval ++ [Val.fn t.next]).drop nd).take (sig.filter (·.2.2)).length))))
      next := t.next + 1 }
  have st4 : PyCore.step I c4 = some cE := by
    simp only [c4, PyCore.step, PyCore.valStep, PyCore.callStep, g, gad_name (.defn nd np) trivial, PyCore.gadgetStep,
      PyCore.argList, hl, List.dropLast_concat, List.drop_left, List.getLast?_concat]
    simp only [mv, hsig, Std.HashMap.getElem?_insert_self, cloP]
    rfl
  rw [ek]
  refine ⟨ys ++ [c1, c2, c3, c4], py.append (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.nil _))))), ?_⟩
  intro y hy z hz
  rcases List.mem_append.1 hy with hy | hy
  · exact .inl (hfy y hy z hz)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · simp [c1, PyCore.focus] at hz
    · simp [c2, PyCore.focus, lamE, PyCore.Expr.label] at hz; exact .inr hz.symm
    · simp [c3, PyCore.focus] at hz
    · simp [c4, PyCore.focus] at hz

/-- PyCore evaluates a lambda's annotations' branch that never runs: `None` joins the record. -/
theorem dead_path (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (C : List Scope) (l : Label)
    (ps : List Param) (vals : List Val) (rest : List PE) (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with ctrl := .val (.data "$args" vals), kont := (lamDead C l ps :: rest).map (.binL ",") ++ K } :: fs' }
      { t with stack := { f' with ctrl := .val (.data "$args" (vals ++ [.none])), kont := rest.map (.binL ",") ++ K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ z, PyCore.focus y = some z → z = sub l 3 := by
  let KR : List (PyCore.Kont σ) := rest.map (.binL ",") ++ K
  let B : List (PyCore.Kont σ) := .binR "," (.data "$args" vals) :: KR
  let a : PE := recR (sub l 3) (trAnns C ps)
  let d : PE := .const (sub l 3) "$none"
  let mk (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ := { t with stack := { f' with ctrl := c, kont := k } :: fs' }
  refine ⟨[mk (.val (.data "$args" vals)) (.binL "," (lamDead C l ps) :: KR), mk (.ev (lamDead C l ps)) B,
    mk (.ev (.const (sub l 3) "$false")) (.condK a d :: B), mk (.val .no) (.condK a d :: B),
    mk (.val (.bool false)) (.condT a d :: B), mk (.ev d) B, mk (.val .none) B], ?_, ?_⟩
  · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))))))
    · simp [mk, KR, PyCore.step, PyCore.valStep, PyCore.top, B]
    · simp [mk, B, PyCore.step, PyCore.evalStep, PyCore.top, lamDead, a, d]
    · simp [mk, B, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
    · simp [mk, B, PyCore.step, PyCore.valStep, PyCore.top, PyCore.tst]
    · simp [mk, B, PyCore.step, PyCore.valStep, PyCore.top]
    · simp [mk, B, d, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, Py.constVal]
    · simp [mk, B, KR, PyCore.step, PyCore.valStep, PyCore.top]
  · intro y hy z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mk, PyCore.focus, lamDead, d, PyCore.Expr.label] at hz <;> exact hz.symm

/-- The parameters' markers read back the signature and the defaults' presence. -/
theorem marks_sig {C' : List Scope} (hpv : ∀ c, priv C' = some c → okName c = true) :
    ∀ ps : List Param, (∀ q ∈ ps, okName q.name = true) →
    ((ps.map (paramMark C')).map pval).mapM Py.markParam =
      some (ps.map fun q => (mangle (priv C') q.name, q.kind.pk, q.dflt.isSome))
  | [], _ => rfl
  | q :: ps, h => by
    simp only [List.map_cons, List.mapM_cons, paramMark, pval, markParam_ok hpv (h q List.mem_cons_self),
      marks_sig hpv ps (fun q' hq => h q' (List.mem_cons_of_mem _ hq))]
    rfl

theorem marks_const (C' : List Scope) (ps : List Param) :
    ∀ m ∈ ps.map (paramMark C'), ∃ r k, m = .const r k ∧ Py.constVal I k = .prim k := by
  intro m hm
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hm
  exact ⟨_, _, rfl, kc_param I _ _ _⟩

theorem okPs_name : ∀ {ps : List Param}, okPs ps = true → ∀ q ∈ ps, okName q.name = true
  | [], _, _, h => by simp at h
  | .mk l y k d a :: ps, ho, q, hq => by
    simp only [okPs, Bool.and_eq_true] at ho
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ho.1.1.1
    · exact okPs_name ho.2 q hq

theorem sig_fst (C' : List Scope) (ps : List Param) :
    (ps.map fun q => (mangle (priv C') q.name, q.kind.pk, q.dflt.isSome)).map (fun q => (q.1, q.2.1)) =
      ps.map fun q => (mangle (priv C') q.name, q.kind.pk) := by simp

theorem sig_snd (C' : List Scope) (ps : List Param) :
    (ps.map fun q => (mangle (priv C') q.name, q.kind.pk, q.dflt.isSome)).map (·.2.2) = ps.map (·.dflt.isSome) := by simp

theorem sig_count (C' : List Scope) : ∀ ps : List Param,
    ((ps.map fun q => (mangle (priv C') q.name, q.kind.pk, q.dflt.isSome)).filter (·.2.2)).length =
      (ps.filterMap Param.dflt).length
  | [] => rfl
  | .mk _ _ _ none _ :: ps => by simpa [List.filterMap_cons, Param.dflt] using sig_count C' ps
  | .mk _ _ _ (some _) _ :: ps => by simpa [List.filterMap_cons, Param.dflt] using sig_count C' ps

theorem pitemsB_app (C : List PyCore.Scope) :
    ∀ a b : PS, PyCore.itemsB R0 C (a ++ b) = PyCore.itemsB R0 C a ++ PyCore.itemsB R0 C b
  | [], _ => rfl
  | _ :: a, b => by simp [PyCore.itemsB, pitemsB_app C a b]

/-- A `def`'s body is code of `p` in its own scope. -/
theorem goodSc_fn {C : List Scope} {U : Label → Prop} {l : Label} {g : Name} {ps : List Param} {b : List Stmt}
    {ds : List Expr} {r : Option Expr} (h : GoodB p C U [.defn l g ps b ds r]) : GoodSc p C (.fn l g ps b) := by
  have hok := h.ok; simp only [okB, okS, Bool.and_eq_true] at hok
  have hnd : (labelsB b).Nodup := by
    have h0 := h.nd; simp only [labelsB, labelsS, List.append_nil] at h0
    exact (List.nodup_cons.1 h0).2.sublist (by
      simpa [List.append_assoc] using (List.infix_append (labelsPs ps) (labelsB b) (labelsEs ds ++ labelsO r)).sublist)
  refine ⟨fun x hx => h.s x (by simp [itemsB, itemsS, hx]), fun x hx => h.t x ?_, by simpa using hok.1.1.1.2,
    fun _ _ => trivial, fun _ c hc => h.pv (by simp) c (by simpa [priv] using hc), hnd,
    fun x hx => h.tch x (by simp [touchB, touchS, hx])⟩
  simp only [trB, trS_defn, gad, cc, ccR, recR, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, r0_s, r0_e,
    Option.isSome_none, Bool.false_eq_true, ite_false, List.nil_append, List.append_nil]
  refine List.mem_cons_of_mem _ (items_fold _ _ x (.inr ⟨defFn C l g ps b, by simp, ?_⟩))
  simp only [defFn, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false, pitemsB_app]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx))

/-- A lambda's body is code of `p` in its own scope. -/
theorem goodSc_lam {C : List Scope} {U : Label → Prop} {l : Label} {ps : List Param} {b : Expr}
    (h : GoodE p C U (.lam l ps b)) : GoodSc p C (.lam l ps b) := by
  have hok := h.ok; simp only [okE, Bool.and_eq_true] at hok
  have hnd : (labelsE b).Nodup := by
    have h0 := h.nd; simp only [labelsE] at h0
    exact (List.nodup_cons.1 h0).2.sublist (List.sublist_append_right _ _)
  refine ⟨fun x hx => h.s x (by simp [itemsE, hx]), fun x hx => h.t x ?_, hok.2,
    fun _ _ => trivial, fun c hc => h.pv c (by simpa [priv] using hc), hnd,
    fun x hx => h.tch x (by simp [touchE, hx])⟩
  simp only [trE, gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false,
    List.nil_append]
  refine items_fold _ _ x (.inr ⟨lamFn C l ps b, by simp [lamFn], ?_⟩)
  simp only [lamFn, PyCore.itemsE, r0_e, r0_s, Option.isSome_none, Bool.false_eq_true, ite_false, pitemsB_app,
    PyCore.itemsB, PyCore.itemsS, List.append_nil]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx))

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A `def`'s function object is made (Surf: `evsEnd`, then `close`; PyCore: the parameters' markers, the function,
`$def`): both give it to the decorators, then store it. `pb0` is PyCore's way to the record's markers. -/
theorem goal_defn (A : At p H s t f fs f' fs') {U : Label → Prop} {l : Label} {g : Name} {ps : List Param}
    {b : List Stmt} {ds : List Expr} {r : Option Expr} {vals : List Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} {ys0 : List (PyCore.Config σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := .val (.tuple vals), kont := .evsEnd (.defn l g ps b ds.length (ps.filterMap Param.dflt).length) :: K0 } :: fs })
    (pb0 : Path (PyCore.step I) t { t with stack := { f' with ctrl := .val (.data "$args" vals), kont := (ps.map (paramMark (.fn l g ps b :: f.chain)) ++ [defFn f.chain l g ps b]).map (.binL ",") ++ .callA (.prim (Gadget.defn ds.length ps.length).name) :: .assign (mangle (priv f.chain) g) :: K0' } :: fs' } ys0)
    (hys0 : ys0 ≠ []) (hcov0 : ∀ y ∈ ys0, ∀ x, PyCore.focus y = some x → H (x / 64) ∨ Touch p s (x / 64))
    (hlen : vals.length = (partsDef ds ps r).length) (hl : H l ∨ Touch p s l)
    (hgb : GoodB p f.chain U [.defn l g ps b ds r]) (hnd : ¬ Dot (mangle (priv f.chain) g))
    (hk : KRel A.x U false K0 K0') (hE : EnterSub K0 f.kont) : Goal I p H s t := by
  have hn : t.next = s.next := A.r.next
  let nd := ds.length
  let nf := (ps.filterMap Param.dflt).length
  let S : Scope := .fn l g ps b
  let C' : List Scope := S :: f.chain
  let dflt := Py.alignDefaults (ps.map (·.dflt.isSome)) ((vals.drop nd).take nf)
  let y := mangle (priv f.chain) g
  let se : Sem.Config σ := { s with stack := { f with ctrl := .val (.tuple vals), kont := .evsEnd (.defn l g ps b nd nf) :: K0 } :: fs }
  let s1 : Sem.Config σ :=
    { s with
      stack := { f with ctrl := .val (.fn s.next), kont := .decos (vals.take nd).reverse :: .assignN y :: K0 } :: fs
      objs := s.objs.insert s.next (Sem.mkClo f S dflt)
      next := s.next + 1 }
  have e2 : Sem.step I se = some s1 := by
    simp [se, s1, Sem.step, Sem.valStep, Sem.finish, Sem.close, Sem.mg, y, dflt] <;> rfl
  have hok := hgb.ok; simp only [okB, okS, Bool.and_eq_true] at hok
  have hpv : ∀ c, priv C' = some c → okName c = true := fun c hc => hgb.pv (by simp) c (by simpa [priv, C'] using hc)
  have hokq : ∀ q ∈ ps, okName q.name = true := okPs_name hok.1.1.1.1.2
  have hpl : (partsDef ds ps r).length = nd + nf + (annOrder ps r).length := by simp [partsDef, nd, nf, Nat.add_assoc]
  obtain ⟨ys1, py1, hfy1⟩ := fin_def (I := I) t f' fs' vals (ps.map (paramMark C')) (sub l 1) false (fresh "a" l)
    (paramBind C' ps ++ trB C' b) nd ps.length (.assign y :: K0') _ (marks_const (I := I) C' ps) (by simp) (marks_sig hpv ps hokq)
  have htake : (vals ++ (ps.map (paramMark C')).map pval ++ [Val.fn t.next]).take nd = vals.take nd := by
    rw [List.append_assoc, List.take_append_of_le_length (by omega)]
  have hdrop : ((vals ++ (ps.map (paramMark C')).map pval ++ [Val.fn t.next]).drop nd).take (ps.filterMap Param.dflt).length =
      (vals.drop nd).take (ps.filterMap Param.dflt).length := by
    rw [List.append_assoc, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
  rw [htake, sig_fst, sig_snd, sig_count, hdrop] at py1
  have hH : ∀ l', H l' → Seen (Touch p) H [s1, s, se] l' := fun _ h => .inl h
  have hTs : ∀ l', Touch p s l' → Seen (Touch p) H [s1, s, se] l' := fun _ h => .inr ⟨s, by simp, h⟩
  have hq : ∀ q ∈ ps, Seen (Touch p) H [s1, s, se] q.label := fun q hq =>
    .inr ⟨se, by simp, .inr (by simp only [se, TouchF]; exact ⟨q, hq, rfl⟩)⟩
  have hob : ORel p (Seen (Touch p) H [s1, s, se]) t.glob t.cells (Sem.mkClo f S dflt)
      (cloP f' (trScope f.chain S) (some (ps.map fun q => (mangle (priv C') q.name, q.kind.pk), dflt))) :=
    orel_fn A.hf.toFRel0 ⟨rfl, rfl⟩ (hl.elim (hH l) (hTs l)) hq (goodSc_fn hgb) ⟨trivial, A.hf.kok⟩
  have hr := crel_close A hH (o0 := cloP f' (trScope f.chain S) none) hob (fun _ h => by simp [cloP] at h)
    (fun _ h => by simp [Sem.mkClo] at h) (U := U) (c := .val (.fn s.next)) (c' := .val (.fn t.next))
    (k := .decos (vals.take nd).reverse :: .assignN y :: K0) (k' := .decos (vals.take nd).reverse :: .assign y :: K0')
    (by rw [hn]; exact .val) (.core (.decos (.core (.assignN hnd (KRel.ext ⟨fun _ h => .inl h, Agree.refl _ _ _⟩ hk)))))
    (fun _ _ _ hm => hE _ _ _ (by simpa using hm))
  refine goal_t (.cons e1 (.cons e2 (.nil _))) (by simp) (pb0.append py1) (by simp [hys0]) (.inl hr) ?_
  intro z hz x hx
  have hx := pfocus_le hx
  rcases List.mem_append.1 hz with hz | hz
  · exact (hcov0 z hz x hx).elim (hH _) (hTs _)
  · rcases hfy1 z hz x hx with ⟨m, hm, rfl⟩ | rfl
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hm
      simp only [paramMark, PyCore.Expr.label]; rw [sub_div _ _ (by omega)]; exact hq q hq'
    · rw [sub_div _ _ (by omega)]; exact hl.elim (hH l) (hTs l)

/-- A lambda's function object is made (Surf: `evsEnd`, then `close`; PyCore: its annotations' dead branch, the
parameters' markers, the function, `$def`, its empty decorators). -/
theorem goal_lam (A : At p H s t f fs f' fs') {U : Label → Prop} {l : Label} {ps : List Param} {b : Expr}
    {dvals : List Val} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} {ys0 : List (PyCore.Config σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := .val (.tuple dvals), kont := .evsEnd (.lam l ps b) :: K0 } :: fs })
    (pb0 : Path (PyCore.step I) t { t with stack := { f' with ctrl := .val (.data "$args" dvals), kont := (lamDead f.chain l ps :: (ps.map (paramMark (.lam l ps b :: f.chain)) ++ [lamFn f.chain l ps b])).map (.binL ",") ++ .callA (.prim (Gadget.defn 0 ps.length).name) :: K0' } :: fs' } ys0)
    (hys0 : ys0 ≠ []) (hcov0 : ∀ y ∈ ys0, ∀ x, PyCore.focus y = some x → H (x / 64) ∨ Touch p s (x / 64))
    (hlen : dvals.length = (ps.filterMap Param.dflt).length) (hl : H l ∨ Touch p s l)
    (hge : GoodE p f.chain U (.lam l ps b)) (hk : KRel A.x U true K0 K0') (hE : EnterSub K0 f.kont) : Goal I p H s t := by
  have hn : t.next = s.next := A.r.next
  let nf := (ps.filterMap Param.dflt).length
  let S : Scope := .lam l ps b
  let C' : List Scope := S :: f.chain
  let dflt := Py.alignDefaults (ps.map (·.dflt.isSome)) dvals
  let se : Sem.Config σ := { s with stack := { f with ctrl := .val (.tuple dvals), kont := .evsEnd (.lam l ps b) :: K0 } :: fs }
  let s1 : Sem.Config σ :=
    { s with
      stack := { f with ctrl := .val (.fn s.next), kont := K0 } :: fs
      objs := s.objs.insert s.next (Sem.mkClo f S dflt)
      next := s.next + 1 }
  have e2 : Sem.step I se = some s1 := by
    simp [se, s1, Sem.step, Sem.valStep, Sem.finish, Sem.close, dflt] <;> rfl
  have hok := hge.ok; simp only [okE, Bool.and_eq_true] at hok
  have hpv : ∀ c, priv C' = some c → okName c = true := fun c hc => hge.pv c (by simpa [priv, C'] using hc)
  have hokq : ∀ q ∈ ps, okName q.name = true := okPs_name hok.1
  obtain ⟨ys1, py1, hfy1⟩ := dead_path (I := I) t f' fs' f.chain l ps dvals (ps.map (paramMark C') ++ [lamFn f.chain l ps b])
    (.callA (.prim (Gadget.defn 0 ps.length).name) :: K0')
  obtain ⟨ys2, py2, hfy2⟩ := fin_def (I := I) t f' fs' (dvals ++ [Val.none]) (ps.map (paramMark C')) (sub l 1) false (fresh "a" l)
    (paramBind C' ps ++ [.ret (sub l 2) (trE C' b)]) 0 ps.length K0' _ (marks_const (I := I) C' ps) (by simp) (marks_sig hpv ps hokq)
  have hdrop : ((dvals ++ [Val.none] ++ (ps.map (paramMark C')).map pval ++ [Val.fn t.next]).drop 0).take
      (ps.filterMap Param.dflt).length = dvals := by
    rw [List.drop_zero, List.append_assoc, List.append_assoc, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  rw [sig_fst, sig_snd, sig_count, hdrop] at py2
  simp only [List.take_zero, List.reverse_nil] at py2
  have st3 : PyCore.step I
      { t with
        stack := { f' with ctrl := .val (.fn t.next), kont := .decos [] :: K0' } :: fs'
        objs := (t.objs.insert t.next (cloP f' (trScope f.chain S) none)).insert t.next
          (cloP f' (trScope f.chain S) (some (ps.map fun q => (mangle (priv C') q.name, q.kind.pk), dflt)))
        next := t.next + 1 } =
      some { t with
        stack := { f' with ctrl := .val (.fn t.next), kont := K0' } :: fs'
        objs := (t.objs.insert t.next (cloP f' (trScope f.chain S) none)).insert t.next
          (cloP f' (trScope f.chain S) (some (ps.map fun q => (mangle (priv C') q.name, q.kind.pk), dflt)))
        next := t.next + 1 } := by
    simp [PyCore.step, PyCore.valStep, PyCore.top]
  have hH : ∀ l', H l' → Seen (Touch p) H [s1, s, se] l' := fun _ h => .inl h
  have hTs : ∀ l', Touch p s l' → Seen (Touch p) H [s1, s, se] l' := fun _ h => .inr ⟨s, by simp, h⟩
  have hq : ∀ q ∈ ps, Seen (Touch p) H [s1, s, se] q.label := fun q hq =>
    .inr ⟨se, by simp, .inr (by simp only [se, TouchF]; exact ⟨q, hq, rfl⟩)⟩
  have hob : ORel p (Seen (Touch p) H [s1, s, se]) t.glob t.cells (Sem.mkClo f S dflt)
      (cloP f' (trScope f.chain S) (some (ps.map fun q => (mangle (priv C') q.name, q.kind.pk), dflt))) :=
    orel_fn A.hf.toFRel0 ⟨rfl, rfl⟩ (hl.elim (hH l) (hTs l)) hq (goodSc_lam hge) ⟨trivial, A.hf.kok⟩
  have hr := crel_close A hH (o0 := cloP f' (trScope f.chain S) none) hob (fun _ h => by simp [cloP] at h)
    (fun _ h => by simp [Sem.mkClo] at h) (U := U) (c := .val (.fn s.next)) (c' := .val (.fn t.next))
    (k := K0) (k' := K0') (by rw [hn]; exact .val) (KRel.ext ⟨fun _ h => .inl h, Agree.refl _ _ _⟩ hk) hE
  refine goal_t (.cons e1 (.cons e2 (.nil _))) (by simp) ((pb0.append py1).append (py2.append (.cons st3 (.nil _))))
    (by simp [hys0]) (.inl hr) ?_
  intro z hz x hx
  have hx := pfocus_le hx
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with (hz | hz) | hz | rfl
  · exact (hcov0 z hz x hx).elim (hH _) (hTs _)
  · rw [hfy1 z hz x hx, sub_div _ _ (by omega)]; exact hl.elim (hH l) (hTs l)
  · rcases hfy2 z hz x hx with ⟨m, hm, rfl⟩ | rfl
    · obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hm
      simp only [paramMark, PyCore.Expr.label]; rw [sub_div _ _ (by omega)]; exact hq q hq'
    · rw [sub_div _ _ (by omega)]; exact hl.elim (hH l) (hTs l)
  · simp [PyCore.focus] at hx

end

/-- PyCore enters the call `ccR r g es` of a core constant: it reaches the empty record, `es` still to
evaluate. Every node it focuses on the way is labelled `r`. -/
theorem cc_enter0 (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (r : Label) (g : String)
    (es : List PE) (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .ev (ccR r g es), kont := K } :: fs' }
      { t with stack := { f' with ctrl := .val (.data "$args" []), kont := es.map (.binL ",") ++ .callA (Py.constVal I g) :: K } :: fs' } ys ∧
      ys ≠ [] ∧ ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = r := by
  obtain ⟨ys, py, hy⟩ := rec_path (I := I) t f' fs' r es (.const r "$args") (.callA (Py.constVal I g) :: K)
  let mk (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ := { t with stack := { f' with ctrl := c, kont := k } :: fs' }
  let c0 := mk (.ev (ccR r g es)) K
  let c1 := mk (.ev (.const r g)) (.callF (recR r es) :: K)
  let c2 := mk (.val (Py.constVal I g)) (.callF (recR r es) :: K)
  let c3 := mk (.ev (.const r "$args")) (es.map (.binL ",") ++ .callA (Py.constVal I g) :: K)
  refine ⟨c0 :: c1 :: c2 :: ys ++ [c3], ?_, by simp, ?_⟩
  · refine .cons (a' := c1) (by simp [c0, c1, mk, ccR, PyCore.step, PyCore.evalStep, PyCore.top])
      (.cons (a' := c2) (by simp [c1, c2, mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK])
        (.cons (by simp [c2, mk, PyCore.step, PyCore.valStep, PyCore.top, recR]) (py.append (.cons ?_ (.nil _)))))
    cases es <;> simp [c3, mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
  · intro y hy' x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy'
    rcases hy' with (rfl | rfl | rfl | hy') | rfl
    · simp [c0, mk, PyCore.focus, ccR, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c1, mk, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c2, mk, PyCore.focus] at hx
    · exact hy y hy' x hx
    · simp [c3, mk, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A value reaches a `def`'s `evs` item: the next part entered, or (the last) the function object made. -/
theorem val_evsDefn (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} {l : Label} {g : Name} {ps : List Param} {b : List Stmt} {ds : List Expr}
    {r : Option Expr} {rest : List (Option Expr)} {acc : List Val} {pes : List PE}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs rest acc (.defn l g ps b ds.length (ps.filterMap Param.dflt).length) :: K0)
    (hK' : f'.kont = recK acc.reverse (pes ++ ps.map (paramMark (.fn l g ps b :: f.chain)) ++ [defFn f.chain l g ps b])
      (.callA (.prim (Gadget.defn ds.length ps.length).name) :: .assign (mangle (priv f.chain) g) :: K0'))
    (hH : H l) (hgb : GoodB p f.chain U [.defn l g ps b ds r]) (hnd : ¬ Dot (mangle (priv f.chain) g))
    (hlt : acc.length < (partsDef ds ps r).length) (hrest : rest = (partsDef ds ps r).drop (acc.length + 1))
    (hpr : PartsR A.x U l rest pes) (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  match rest, pes, hpr with
  | [], [], _ =>
    have hlen : (acc.reverse ++ [v]).length = (partsDef ds ps r).length := by
      have := congrArg List.length hrest; simp at this ⊢; omega
    have st1 := pstep_rec (I := I) (done := acc.reverse) A.ht hc'
      (K1 := (ps.map (paramMark (.fn l g ps b :: f.chain)) ++ [defFn f.chain l g ps b]).map (.binL ",") ++
        .callA (.prim (Gadget.defn ds.length ps.length).name) :: .assign (mangle (priv f.chain) g) :: K0')
      (by rw [hK']; simp [recK])
    exact goal_defn A (vals := acc.reverse ++ [v]) (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC])
      (.cons st1 (.nil _)) (by simp) (fun y hy x hx => by simp at hy; subst hy; simp [PyCore.focus, A.ht, hc'] at hx)
      hlen (.inl hH) hgb hnd hk (fun _ _ _ hm => by rw [hK]; exact List.mem_cons_of_mem _ hm)
  | some e :: rest', pe :: ps', ⟨⟨hge, hpe⟩, hr'⟩ =>
    subst hpe
    have hd : (partsDef ds ps r).drop (acc.length + 1) = some e :: rest' := hrest.symm
    have hlt2 : acc.length + 1 < (partsDef ds ps r).length := by
      have := congrArg List.length hd; simp at this; omega
    have hrest2 : rest' = (partsDef ds ps r).drop ((v :: acc).length + 1) := by
      rw [List.length_cons, ← List.drop_drop, hd]; rfl
    exact val_mid A (e := e) (rest' := rest') (T := .defn l g ps b ds.length (ps.filterMap Param.dflt).length) (K0 := K0)
      (ps := ps' ++ ps.map (paramMark (.fn l g ps b :: f.chain)) ++ [defFn f.chain l g ps b])
      (K1 := .callA (.prim (Gadget.defn ds.length ps.length).name) :: .assign (mangle (priv f.chain) g) :: K0') hc hc' hK
      (by rw [hK']; rfl) hge
      (.call (.evsDefn (.inl hH) hgb hnd (by simpa using hlt2) hrest2 (partsR_with hr')
        (KRel.ext ⟨fun _ h => .inl h, Agree.refl _ _ _⟩ hk)))
  | none :: _, _, _ =>
    have := List.mem_of_mem_drop (hrest ▸ List.mem_cons_self : none ∈ (partsDef ds ps r).drop (acc.length + 1))
    simp [partsDef, annOrder_eq] at this

/-- A value reaches a lambda's `evs` item: the next default entered, or (the last) the function object made. -/
theorem val_evsLam (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} {l : Label} {ps : List Param} {b : Expr}
    {rest : List (Option Expr)} {acc : List Val} {pes : List PE}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .evs rest acc (.lam l ps b) :: K0)
    (hK' : f'.kont = recK acc.reverse (pes ++ lamDead f.chain l ps :: ps.map (paramMark (.lam l ps b :: f.chain)) ++
      [lamFn f.chain l ps b]) (.callA (.prim (Gadget.defn 0 ps.length).name) :: K0'))
    (hH : H l) (hge : GoodE p f.chain U (.lam l ps b))
    (hlt : acc.length < (partsLam ps).length) (hrest : rest = (partsLam ps).drop (acc.length + 1))
    (hpr : PartsR A.x U l rest pes) (hk : KRel A.x U true K0 K0') : Goal I p H s t := by
  match rest, pes, hpr with
  | [], [], _ =>
    have hlen : (acc.reverse ++ [v]).length = (ps.filterMap Param.dflt).length := by
      have := congrArg List.length hrest; simp [partsLam] at this hlt ⊢; omega
    have st1 := pstep_rec (I := I) (done := acc.reverse) A.ht hc'
      (K1 := (lamDead f.chain l ps :: (ps.map (paramMark (.lam l ps b :: f.chain)) ++ [lamFn f.chain l ps b])).map (.binL ",") ++
        .callA (.prim (Gadget.defn 0 ps.length).name) :: K0')
      (by rw [hK']; simp [recK])
    exact goal_lam A (dvals := acc.reverse ++ [v]) (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC])
      (.cons st1 (.nil _)) (by simp) (fun y hy x hx => by simp at hy; subst hy; simp [PyCore.focus, A.ht, hc'] at hx)
      hlen (.inl hH) hge hk (fun _ _ _ hm => by rw [hK]; exact List.mem_cons_of_mem _ hm)
  | some e :: rest', pe :: ps', ⟨⟨hge', hpe⟩, hr'⟩ =>
    subst hpe
    have hd : (partsLam ps).drop (acc.length + 1) = some e :: rest' := hrest.symm
    have hlt2 : acc.length + 1 < (partsLam ps).length := by
      have := congrArg List.length hd; simp at this; omega
    have hrest2 : rest' = (partsLam ps).drop ((v :: acc).length + 1) := by
      rw [List.length_cons, ← List.drop_drop, hd]; rfl
    exact val_mid A (e := e) (rest' := rest') (T := .lam l ps b) (K0 := K0)
      (ps := ps' ++ lamDead f.chain l ps :: ps.map (paramMark (.lam l ps b :: f.chain)) ++ [lamFn f.chain l ps b])
      (K1 := .callA (.prim (Gadget.defn 0 ps.length).name) :: K0') hc hc' hK (by rw [hK']; rfl) hge'
      (.call (.evsLam (.inl hH) hge (by simpa using hlt2) hrest2 (partsR_with hr')
        (KRel.ext ⟨fun _ h => .inl h, Agree.refl _ _ _⟩ hk)))
  | none :: _, _, _ =>
    have := List.mem_of_mem_drop (hrest ▸ List.mem_cons_self : none ∈ (partsLam ps).drop (acc.length + 1))
    simp [partsLam] at this

end

end Call

open Call

/-- `At.go11B` for a step that pushes an `enterK o` item (`o` holds no comprehension's function object). -/
theorem Call.enterK_go {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'}
    (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {o : Nat} {bd : List (Name × Val)} {kx : Name} {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := .enterK o bd kx :: k } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with ctrl := c', kont := k' } :: fs' })
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i (.enterK o bd kx :: k) k')
    (hcov : ∀ x, pfocus t = some x → Touch p s (x / 64)) (hE : EnterSub k f.kont) (ho : NoCompObj s.objs o) :
    GoalB I p H s t :=
  goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp)
    (crelI_seen (A.setE hc hk fun o' b' kx' hm => (List.mem_cons.1 hm).elim
      (fun e => by cases e; exact ho) fun hm => A.etop o' b' kx' (hE o' b' kx' hm)))
    (fun y hy x hx => by simp at hy; subst hy; exact .inr ⟨s, by simp, hcov x hx⟩)

/-- A call of a function object of a `def` or lambda: binding (an error raises in the caller), the
`**` dictionary, the frame (or generator), the parameters' bindings PyCore's body starts with. -/
theorem call_fn {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') (W : WF p) {o : Nat} {args : List Val} {kws : List (Name × Val)}
    (hc : f.ctrl = .call (.fn o) args kws) (hc' : f'.ctrl = .call (.fn o) args kws)
    (hk : KRel A.x U true f.kont f'.kont) {S : Scope} {C : List Scope} {cl κ kd dflt}
    (ho : sObj s o = some (.clo S C cl κ kd dflt)) (hS : S.isComp = false) : GoalB I p H s t := by
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  have hr := A.r.objs o
  rw [ho] at hr
  cases ho' : pObj t o with
  | none => rw [ho'] at hr; exact hr.elim
  | some b0 =>
  rw [ho'] at hr
  have hr0 := hr
  cases hr with
  | @clo _ _ _ cl' _ κ' _ _ sg h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
  have ho1 : s.objs[o]? = some (.clo S C cl κ kd dflt) := ho
  have ho2 : t.objs[o]? = some (.clo (trScope C S) (trChain C) cl' κ' sg) := ho'
  cases S with
  | comp => simp [Scope.isComp] at hS
  | cl l x b => cases sg <;> simp [SigR, Scope.isComp] at h6
  | fn l gn ps b =>
    cases sg with
    | none => simp [SigR, Scope.isComp] at h6
    | some sd =>
    obtain ⟨sig, d⟩ := sd
    simp only [SigR] at h6
    obtain ⟨rfl, rfl⟩ := h6
    cases hb : Py.bindArgs (ps.map fun q => (mangle (priv (Scope.fn l gn ps b :: C)) q.name, q.kind.pk)) d args kws with
    | error e =>
      exact call_raise A hk e (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.setC, ho1, hb])
        (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, PyCore.top, ho2, trScope, hb]) hfoc
    | ok r =>
      obtain ⟨bound, _ | ⟨kx, items⟩⟩ := r
      · exact enter_clo A hk hr0 hS bound .wait .wait (by simp [Sem.step, A.hs, hc, Sem.callStep, ho1, hb])
          (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, ho2, trScope, hb]) hfoc esub_refl
      · exact enterK_go A (c := .op (.display (.dict (items.map fun _ => false))) (items.flatMap fun p => [.str p.1, p.2]))
          (c' := .op (.display (.dict (items.map fun _ => false))) (items.flatMap fun p => [.str p.1, p.2]))
          (k := f.kont) (k' := .enterK o bound kx :: f'.kont)
          (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.doOp, Sem.setC, ho1, hb])
          (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, PyCore.top, ho2, trScope, hb])
          .op (.call (.enterK hk)) (cov_none A hfoc) esub_refl ⟨by simp [ho1], fun S' C' cl0 κ0 kd0 d0 h => by
            rw [ho1] at h; cases h; exact hS⟩
  | lam l ps b =>
    cases sg with
    | none => simp [SigR, Scope.isComp] at h6
    | some sd =>
    obtain ⟨sig, d⟩ := sd
    simp only [SigR] at h6
    obtain ⟨rfl, rfl⟩ := h6
    cases hb : Py.bindArgs (ps.map fun q => (mangle (priv (Scope.lam l ps b :: C)) q.name, q.kind.pk)) d args kws with
    | error e =>
      exact call_raise A hk e (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.setC, ho1, hb])
        (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, PyCore.top, ho2, trScope, hb]) hfoc
    | ok r =>
      obtain ⟨bound, _ | ⟨kx, items⟩⟩ := r
      · exact enter_clo A hk hr0 hS bound .wait .wait (by simp [Sem.step, A.hs, hc, Sem.callStep, ho1, hb])
          (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, ho2, trScope, hb]) hfoc esub_refl
      · exact enterK_go A (c := .op (.display (.dict (items.map fun _ => false))) (items.flatMap fun p => [.str p.1, p.2]))
          (c' := .op (.display (.dict (items.map fun _ => false))) (items.flatMap fun p => [.str p.1, p.2]))
          (k := f.kont) (k' := .enterK o bound kx :: f'.kont)
          (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.doOp, Sem.setC, ho1, hb])
          (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callFn, PyCore.top, ho2, trScope, hb])
          .op (.call (.enterK hk)) (cov_none A hfoc) esub_refl ⟨by simp [ho1], fun S' C' cl0 κ0 kd0 d0 h => by
            rw [ho1] at h; cases h; exact hS⟩

/-- `next` of a generator function not yet run: PyCore runs its parameters' bindings (branches that
never run), then both run the body. -/
theorem resume_genFn {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') (W : WF p) {o : Nat} (hc : f.ctrl = .call .next [.gen o] [])
    (hc' : f'.ctrl = .call .next [.gen o] []) (hk : KRel A.x U true f.kont f'.kont)
    {g : Sem.Frame σ} {g' : PyCore.Frame σ} (ho : sObj s o = some (.gen (.susp g)))
    (ho' : pObj t o = some (.gen (.susp g'))) (h0 : FRel0 g g') (hl : ∀ S C, g.chain = S :: C → H S.label)
    {l gn ps b C0} (hC : g.chain = .fn l gn ps b :: C0) (hg : g.ctrl = .exec b) (hgk : g.kont = [])
    (hg' : g'.ctrl = .exec (paramBind g.chain ps ++ trB g.chain b)) (hgk' : g'.kont = [])
    (hs : Special (cx p H (rdOf t g') (ownOf t g') g) g.ctrl g.kont g'.ctrl g'.kont) : GoalB I p H s t := by
  obtain ⟨hq, hgb⟩ : (∀ q ∈ ps, H q.label) ∧ GoodB p g.chain UAll b := by
    generalize e1 : g.ctrl = c at hs
    generalize e2 : g.kont = k at hs
    generalize e3 : g'.ctrl = c' at hs
    generalize e4 : g'.kont = k' at hs
    cases hs with
    | genFn hC' hq hb =>
      have hC'' : g.chain = _ := hC'
      rw [hC] at hC''
      cases hC''
      rw [hg] at e1; cases e1
      exact ⟨hq, hb⟩
    | genComp => rw [hg] at e1; cases e1
    | genLam => rw [hg] at e1; cases e1
    | yf => rw [hg] at e1; cases e1
  have A1 := A.zero.push ho' h0 hl f.kont f'.kont hk ho
  have e1 : Sem.step I s =
      some { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) } := by
    simp only [sObj] at ho
    simp [Sem.step, A.hs, hc, Sem.callStep, ho]
  have e2 : PyCore.step I t =
      some { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) } := by
    simp only [pObj] at ho'
    simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callStep, ho']
  let t1 : PyCore.Config σ :=
    { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) }
  let gs : List (PyCore.Frame σ) := { f' with ctrl := .wait, kont := f'.kont } :: fs'
  obtain ⟨ys, py, hfy⟩ := param_path (I := I) t1 g' gs g.chain (trB g.chain b) [] ps
  have et1 : { t1 with stack := { g' with ctrl := .exec (paramBind g.chain ps ++ trB g.chain b), kont := [] } :: gs } = t1 := by
    rw [← hg', ← hgk']
  rw [et1] at py
  have A2 := A1.updT (.exec (trB g.chain b)) []
  have hr := A2.crel (U := UAll) (i := false) (by rw [hg]; exact .exec hgb (fun _ => by rw [hC]; rfl)) (by rw [hgk]; exact .nil)
  exact goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 py) (by simp) (crelI_seen hr)
    (cover_H fun y hy x hx => by
      rcases List.mem_cons.1 hy with rfl | hy
      · simp [PyCore.focus, A.ht, hc'] at hx
      · obtain ⟨q, hq', rfl⟩ := hfy y hy x hx; rw [sub_div _ _ (by omega)]; exact hq q hq')

/-- `next` of a generator lambda not yet run. -/
theorem resume_genLam {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') (W : WF p) {o : Nat} (hc : f.ctrl = .call .next [.gen o] [])
    (hc' : f'.ctrl = .call .next [.gen o] []) (hk : KRel A.x U true f.kont f'.kont)
    {g : Sem.Frame σ} {g' : PyCore.Frame σ} (ho : sObj s o = some (.gen (.susp g)))
    (ho' : pObj t o = some (.gen (.susp g'))) (h0 : FRel0 g g') (hl : ∀ S C, g.chain = S :: C → H S.label)
    {l ps b C0} (hC : g.chain = .lam l ps b :: C0) (hg : g.ctrl = .ev b) (hgk : g.kont = [.retS])
    (hg' : g'.ctrl = .exec (paramBind g.chain ps ++ [.ret (sub l 2) (trE g.chain b)])) (hgk' : g'.kont = [])
    (hs : Special (cx p H (rdOf t g') (ownOf t g') g) g.ctrl g.kont g'.ctrl g'.kont) : GoalB I p H s t := by
  obtain ⟨hq, hgb⟩ : (∀ q ∈ ps, H q.label) ∧ GoodE p g.chain UAll b := by
    generalize e1 : g.ctrl = c at hs
    generalize e2 : g.kont = k at hs
    generalize e3 : g'.ctrl = c' at hs
    generalize e4 : g'.kont = k' at hs
    cases hs with
    | genLam hC' hq hb =>
      have hC'' : g.chain = _ := hC'
      rw [hC] at hC''
      cases hC''
      exact ⟨hq, hb⟩
    | genComp => rw [hg] at e1; cases e1
    | genFn => rw [hg] at e1; cases e1
    | yf => rw [hg] at e1; cases e1
  have A1 := A.zero.push ho' h0 hl f.kont f'.kont hk ho
  have e1 : Sem.step I s =
      some { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) } := by
    simp only [sObj] at ho
    simp [Sem.step, A.hs, hc, Sem.callStep, ho]
  have e2 : PyCore.step I t =
      some { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) } := by
    simp only [pObj] at ho'
    simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callStep, ho']
  let t1 : PyCore.Config σ :=
    { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) }
  let gs : List (PyCore.Frame σ) := { f' with ctrl := .wait, kont := f'.kont } :: fs'
  let rs : PS := [.ret (sub l 2) (trE g.chain b)]
  obtain ⟨ys, py, hfy⟩ := param_path (I := I) t1 g' gs g.chain rs [] ps
  have et1 : { t1 with stack := { g' with ctrl := .exec (paramBind g.chain ps ++ rs), kont := [] } :: gs } = t1 := by
    rw [← hg', ← hgk']
  rw [et1] at py
  have e3 : PyCore.step I { t1 with stack := { g' with ctrl := .exec rs, kont := [] } :: gs } =
      some { t1 with stack := { g' with ctrl := .ev (trE g.chain b), kont := [.retS, .seq []] } :: gs } := by
    simp [PyCore.step, PyCore.execStep, PyCore.top, rs]
  have A2 := A1.updT (.ev (trE g.chain b)) [.retS, .seq []]
  have hr := A2.crel (U := UAll) (i := true) (by rw [hg]; exact .ev hgb) (by rw [hgk]; exact .core (.retS (.core .seqNil)))
  have hll : H l := hl _ _ hC
  exact goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 (py.append (.cons e3 (.nil _)))) (by simp) (crelI_seen hr)
    (cover_H fun y hy x hx => by
      rcases List.mem_cons.1 hy with rfl | hy
      · simp [PyCore.focus, A.ht, hc'] at hx
      · rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨q, hq', rfl⟩ := hfy y hy x hx; rw [sub_div _ _ (by omega)]; exact hq q hq'
        · simp only [List.mem_singleton] at hy; subst hy
          simp [PyCore.focus, PyCore.Stmt.label, rs] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hll)

theorem ev_call (l f args kws) : EvCase I p (.call l f args kws) := by
  intro H s t fr fs fr' fs' U A W hc hc' hg hk
  have hk1 : KRel (cx p (Seen (Touch p) H [s]) (rdOf t fr') (ownOf t fr') fr) U true
      (.evs ((args.map fun a => some (unstar a)) ++ kws.map kwV) [] (.call args.length (args.map isStar) (kws.map kwN))
        :: fr.kont)
      (recK [] (trA fr.chain args ++ trKs fr.chain kws ++ args.map starMark ++ kws.map kwMark)
        (.callA (.prim Gadget.call.name) :: fr'.kont)) :=
    .call (.evsCall hg (by simp [partsCall]) rfl (by simp) (by simp)
      (partsR_app (partsR_args fun a ha => good_call_arg hg ha) (partsR_kws fun _ _ _ hm => good_call_kw hg hm))
      (lift A hk))
  refine ev_cc A (l := l) (c := .ev f) (touch_ev A hc) (by rw [hc']; rfl)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC]; constructor <;> rfl) (.ev (good_call_f hg)) ?_
  rw [kc_gad I .call trivial]; exact hk1

set_option hygiene false in
macro "se1" : tactic => `(tactic| (rw [h1]; simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.retStep, Sem.setC]))

theorem sig_call {i : Bool} : KCase I p i CallK CSig := by
  intro H s t f fs f' fs' U A W hc hk
  rcases hc with ⟨v, h1, h2⟩ | ⟨v, h1, h2⟩ | ⟨rfl, -, -, -⟩ | ⟨rfl, -, -, -⟩
  case inr.inr.inl => cases hk
  case inr.inr.inr => cases hk
  all_goals
    have hsig : (∃ w, f'.ctrl = .raise w) ∨ (∃ w, f'.ctrl = .retv w) := by simp [h2]
    have hcr : ∀ j, CR p f.chain U j f.ctrl f'.ctrl := fun j => by rw [h1, h2]; first | exact .raise | exact .retv
    generalize hK : f.kont = K at hk
    generalize hK' : f'.kont = K' at hk
    cases hk with
    | argStar k =>
      exact call_sig_pop A [_] (hcr true) hsig rfl (by se1) (by rw [hK']; rfl) (by simp [PopOk]) (by simp) k (esub_cons hK)
    | argKw k =>
      exact call_sig_pop A [_] (hcr true) hsig rfl (by se1) (by rw [hK']; rfl) (by simp [PopOk]) (by simp) k (esub_cons hK)
    | enterK k =>
      exact call_sig_pop A [_] (hcr true) hsig rfl (by se1) (by rw [hK']; rfl) (by simp [PopOk]) (by simp) k (esub_cons hK)
    | evsCall _ _ _ _ _ _ k =>
      exact call_sig_pop A _ (hcr true) hsig rfl (by se1)
        (by rw [hK', ← recK_split _ _ [_]]; rfl) (recK_pop _ _ _ (by simp [PopOk])) (by simp [recK]) k (esub_cons hK)
    | evsDefn _ _ _ _ _ _ k =>
      exact call_sig_pop A _ (hcr false) hsig rfl (by se1)
        (by rw [hK', ← recK_split _ _ [_, _]]; rfl) (recK_pop _ _ _ (by simp [PopOk])) (by simp [recK]) k (esub_cons hK)
    | evsLam _ _ _ _ _ k =>
      exact call_sig_pop A _ (hcr true) hsig rfl (by se1)
        (by rw [hK', ← recK_split _ _ [_]]; rfl) (recK_pop _ _ _ (by simp [PopOk])) (by simp [recK]) k (esub_cons hK)

/-- The arguments after the `*` phase: the `**` phase or the call (`kwPhase`, both sides). -/
theorem kw_goal {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} {U : Label → Prop}
    (A : At p H s t f fs f' fs') {g : Val} {args : List Val} {kws : List (Option Name)} {kwvals : List Val}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (k : KRel A.x U true K0 K0')
    (e1 : Sem.step I s = Sem.kwPhase I s f fs (.call g) args kws kwvals K0)
    (e2 : PyCore.step I t = PyCore.kwPhase t f' fs' (.call g) args kws kwvals K0')
    (hfoc : PyCore.focus t = none) (he : EnterSub K0 f.kont) : Goal I p H s t := by
  by_cases hn : kws.any Option.isNone = true
  · exact A.go11 (c := .op (.display (.kwargs kws)) kwvals) (c' := .op (.display (.kwargs kws)) kwvals)
      (k := .argKw (.call g) args :: K0) (k' := .argKw (.call g) args :: K0')
      (by rw [e1]; simp [Sem.kwPhase, hn, Sem.doOp, Sem.setC])
      (by rw [e2]; simp [PyCore.kwPhase, hn, PyCore.top]) .op (.call (.argKw k)) (cov_none A hfoc)
      (fun _ _ _ hm => he _ _ _ (by simpa using hm))
  · exact A.go11 (c := .call g args ((kws.filterMap id).zip kwvals)) (c' := .call g args ((kws.filterMap id).zip kwvals))
      (k := K0) (k' := K0')
      (by rw [e1]; simp [Sem.kwPhase, hn, Sem.finishArgs, Sem.setC])
      (by rw [e2]; simp [PyCore.kwPhase, hn, PyCore.finishArgs, PyCore.top]) .call k (cov_none A hfoc) he

set_option hygiene false in
macro "vstuck" : tactic => `(tactic| exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.valStep])
  (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep]) (cov_none A hfoc))

theorem val_call : KCase I p true CallK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @argStar _ K0 K0' g kws kwvals k =>
    cases v
    case tuple args =>
      exact kw_goal A (g := g) (args := args) (kws := kws) (kwvals := kwvals) k (by simp [Sem.step, A.hs, hc, hK, Sem.valStep]) (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep])
        hfoc (esub_cons hK)
    all_goals vstuck
  | @argKw _ K0 K0' g args k =>
    cases v
    case tuple pairs =>
      cases hp : Py.kwPairs pairs with
      | none =>
        exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hp])
          (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, hp]) (cov_none A hfoc)
      | some kvs =>
        exact A.go11 (c := .call g args kvs) (c' := .call g args kvs) (k := K0) (k' := K0')
          (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hp, Sem.finishArgs, Sem.setC])
          (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, hp, PyCore.finishArgs, PyCore.top]) .call k (cov_none A hfoc)
    all_goals vstuck
  | @enterK _ K0 K0' o bound kx k =>
    have hr := A.r.objs o
    cases h1 : sObj s o <;> cases h2 : pObj t o <;> rw [h1, h2] at hr <;> simp only [PyCore.OptRel] at hr
    · have h1' : s.objs[o]? = none := h1
      have h2' : t.objs[o]? = none := h2
      exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, h1'])
        (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, h2']) (cov_none A hfoc)
    · rename_i a b
      have h1' : s.objs[o]? = some a := h1
      have h2' : t.objs[o]? = some b := h2
      have hr0 := hr
      cases hr with
      | gen hg =>
        exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, h1'])
          (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, h2']) (cov_none A hfoc)
      | @clo S C cl cl' κ κ' kd dflt sg _ _ _ _ _ _ _ _ _ _ =>
        cases hS : S.isComp
        · exact (enter_clo A k hr0 hS (bound ++ [(kx, v)]) (.val v) (.val v)
            (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, h1']) (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, h2'])
            hfoc (esub_cons hK)).sim
        · -- `o` holds no comprehension's function object (`CRel.enter`)
          have hno := A.etop o bound kx (by rw [hK]; exact List.mem_cons_self)
          rw [hno.2 _ _ _ _ _ _ h1'] at hS; cases hS
  | evsCall hg hlt hrest hHa hHk hpr k => exact val_evsCall A hc hc' hK hK' hg hlt hrest hHa hHk hpr k
  | evsDefn hH hgb hnd hlt hrest hpr k => exact val_evsDefn A hc hc' hK hK' hH hgb hnd hlt hrest hpr k
  | evsLam hH hge hlt hrest hpr k => exact val_evsLam A hc hc' hK hK' hH hge hlt hrest hpr k

theorem ev_lam (l ps b) : EvCase I p (.lam l ps b) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  cases hd : ps.filterMap Param.dflt with
  | nil =>
    -- no default: the function object is made
    have hes : trE f.chain (.lam l ps b) = ccR (sub l 0) (Gadget.defn 0 ps.length).name
        (lamDead f.chain l ps :: (ps.map (paramMark (.lam l ps b :: f.chain)) ++ [lamFn f.chain l ps b])) := by
      simp [trE, gad, cc, trDfs_eq, hd, lamDead, lamFn]
    obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter0 (I := I) t f' fs' (sub l 0) (Gadget.defn 0 ps.length).name
      (lamDead f.chain l ps :: (ps.map (paramMark (.lam l ps b :: f.chain)) ++ [lamFn f.chain l ps b])) f'.kont
    rw [t_eq A.ht (by rw [hc', hes]) rfl, kc_gad I (.defn 0 ps.length) trivial] at pc
    have htl : Touch p s l := touch_ev A hc
    exact goal_lam A (dvals := []) (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC, hd]) pc hys
      (fun y hy x hx => .inr (by rw [hfoc y hy x hx, sub_div _ _ (by omega)]; exact htl))
      (by simp [hd]) (.inr htl) hg hk esub_refl
  | cons d rest =>
    have hk1 : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U true
        (.evs (rest.map some) [] (.lam l ps b) :: f.kont)
        (recK [] (rest.map (trE f.chain) ++ lamDead f.chain l ps :: ps.map (paramMark (.lam l ps b :: f.chain)) ++
          [lamFn f.chain l ps b]) (.callA (.prim (Gadget.defn 0 ps.length).name) :: f'.kont)) :=
      .call (.evsLam (.inr ⟨s, by simp, touch_ev A hc⟩) hg (by simp [partsLam, hd]) (by simp [partsLam, hd])
        (partsR_map fun e he => good_lam_dflt hg (by rw [hd]; exact List.mem_cons_of_mem _ he)) (lift A hk))
    refine ev_cc A (l := l) (g := (Gadget.defn 0 ps.length).name) (c := .ev d)
      (k := .evs (rest.map some) [] (.lam l ps b) :: f.kont) (touch_ev A hc)
      (rest := rest.map (trE f.chain) ++ lamDead f.chain l ps :: ps.map (paramMark (.lam l ps b :: f.chain)) ++
        [lamFn f.chain l ps b])
      (by rw [hc']; simp [trE, gad, cc, trDfs_eq, hd, lamDead, lamFn])
      (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.startEvs, Sem.setC, hd])
      (.ev (good_lam_dflt hg (by rw [hd]; exact List.mem_cons_self))) ?_
    rw [kc_gad I (.defn 0 ps.length) trivial]; exact hk1
theorem exec_defn (l g ps b ds r) : ExecCase I p (.defn l g ps b ds r) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hgd : ∀ e ∈ ds ++ ps.filterMap Param.dflt ++ annL ps r, GoodE p f.chain U e := fun e he => good_defn_part hg he
  have hnd : ¬ Dot (mangle (priv f.chain) g) := fun hd => W.nodot l _ f.chain (hg.s _ (by simp [itemsB, itemsS])) hd
  have ht : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Stmt.lbl])
  cases hE : ds ++ ps.filterMap Param.dflt ++ annL ps r with
  | nil =>
    -- no decorator, default or annotation: the function object is made
    have hEL : ds.map some ++ (ps.filterMap Param.dflt).map some ++ annOrder ps r = [] := by
      rw [annOrder_eq, ← List.map_append, ← List.map_append, hE]; rfl
    have hpd : partsDef ds ps r = [] := hEL
    have hit : defParts f.chain ps ds r = [] := by rw [defParts_eq, hE]; rfl
    let nm := (Gadget.defn ds.length ps.length).name
    let es := ps.map (paramMark (.fn l g ps b :: f.chain)) ++ [defFn f.chain l g ps b]
    let K1 : List (PyCore.Kont σ) := .assign (mangle (priv f.chain) g) :: .seq (trB f.chain ss) :: f'.kont
    have e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .ev (ccR (sub l 2) nm es), kont := K1 } :: fs' } := by
      rw [pstep_exec A.ht (show f'.ctrl = .exec (trS f.chain (.defn l g ps b ds r) :: trB f.chain ss) from hc')]
      simp [PyCore.execStep, PyCore.top, trS_defn, gad, cc, hit, nm, es, K1]
    obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter0 (I := I) t f' fs' (sub l 2) nm es K1
    rw [kc_gad I (.defn ds.length ps.length) trivial] at pc
    exact goal_defn A (vals := []) (K0 := .seq ss :: f.kont) (K0' := .seq (trB f.chain ss) :: f'.kont)
      (by simp [Sem.step, A.hs, hc, Sem.execStep, hEL, Sem.startEvs, Sem.setC]) (.cons e2 pc) (by simp)
      (fun y hy x hx => by
        rcases List.mem_cons.1 hy with rfl | hy
        · simp [PyCore.focus, A.ht, hc', trB, trS_defn, PyCore.Stmt.label] at hx; rw [← hx, sub_div _ _ (by omega)]
          exact .inr ht
        · rw [hfoc y hy x hx, sub_div _ _ (by omega)]; exact .inr ht)
      (by rw [hpd]; rfl) (.inr ht) (GoodB.head hg) hnd (krel_seq (hnc (by simp)) hg.tail hk)
      (fun _ _ _ hm => by simpa using hm)
  | cons e rest =>
    have hEL : ds.map some ++ (ps.filterMap Param.dflt).map some ++ annOrder ps r = some e :: rest.map some := by
      rw [annOrder_eq, ← List.map_append, ← List.map_append, hE]; rfl
    have hpd : partsDef ds ps r = some e :: rest.map some := hEL
    have hit : defParts f.chain ps ds r = trE f.chain e :: rest.map (trE f.chain) := by rw [defParts_eq, hE]; rfl
    let nm := (Gadget.defn ds.length ps.length).name
    let rest' := rest.map (trE f.chain) ++ ps.map (paramMark (.fn l g ps b :: f.chain)) ++ [defFn f.chain l g ps b]
    let K1 : List (PyCore.Kont σ) := .assign (mangle (priv f.chain) g) :: .seq (trB f.chain ss) :: f'.kont
    let Ks : List (Sem.Kont σ) :=
      .evs (rest.map some) [] (.defn l g ps b ds.length (ps.filterMap Param.dflt).length) :: .seq ss :: f.kont
    have e1 : Sem.step I s = some { s with stack := { f with ctrl := .ev e, kont := Ks } :: fs } := by
      simp [Sem.step, A.hs, hc, Sem.execStep, hEL, Sem.startEvs, Sem.setC, Ks]
    have e2 : PyCore.step I t =
        some { t with stack := { f' with ctrl := .ev (ccR (sub l 2) nm (trE f.chain e :: rest')), kont := K1 } :: fs' } := by
      rw [pstep_exec A.ht (show f'.ctrl = .exec (trS f.chain (.defn l g ps b ds r) :: trB f.chain ss) from hc')]
      simp [PyCore.execStep, PyCore.top, trS_defn, gad, cc, hit, nm, rest', K1]
    obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub l 2) nm (trE f.chain e) rest' K1
    have hk1 : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U true
        (.evs (rest.map some) [] (.defn l g ps b ds.length (ps.filterMap Param.dflt).length) :: .seq ss :: f.kont)
        (recK [] rest' (.callA (Py.constVal I nm) :: K1)) := by
      rw [kc_gad I (.defn ds.length ps.length) trivial]
      exact .call (.evsDefn (.inr ⟨s, by simp, ht⟩) (GoodB.head hg) hnd (by rw [hpd]; simp)
        (by rw [hpd]; simp)
        (partsR_map fun e' he' => hgd e' (by rw [hE]; exact List.mem_cons_of_mem _ he'))
        (lift A (krel_seq (hnc (by simp)) hg.tail hk)))
    exact goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 pc) (by simp)
      (.inl (((A.zero.upd (.ev e) Ks (.ev (trE f.chain e)) (recK [] rest' (.callA (Py.constVal I nm) :: K1))
        (fun _ _ _ hm => by simpa [Ks] using hm)).mono_H
        fun _ h => .inl h).crel (.ev (hgd e (by rw [hE]; exact List.mem_cons_self))) hk1))
      (cover_of (l := l) (by simp) ht fun y hy x hx => by
        rcases List.mem_cons.1 hy with rfl | hy
        · simp [PyCore.focus, A.ht, hc', trB, trS_defn, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
        · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega))

end Surf.T2
