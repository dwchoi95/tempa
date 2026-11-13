/-
(T2), class statements and bodies, `SETUP_ANNOTATIONS`, the initial configurations.
-/
import Surf.T2Cases

namespace Surf.T2
open PyCore (Name Label)
open Py (Val Gadget)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

namespace Cls

/-! ## Signals -/

/-- The PyCore items a signal passes with no effect. -/
def PlainK : PyCore.Kont σ → Prop
  | .binR .. | .binL .. | .callA _ | .exprS | .seq _ | .clsEnd .. | .assign _ | .argStar .. | .argKw .. => True
  | .tryE [] _ => True
  | _ => False

theorem esub_tail {a : Sem.Kont σ} {k K : List (Sem.Kont σ)} (ha : ∀ o b kx, a ≠ .enterK o b kx)
    (h : EnterSub k K) : EnterSub (a :: k) K :=
  fun o b kx hm => h o b kx ((List.mem_cons.1 hm).resolve_left fun e => ha o b kx e.symm)

/-- A signal passes PyCore's items `pre`. -/
theorem pop_path {c : PyCore.Ctrl σ} (hc : (∃ v, c = .raise v) ∨ (∃ v, c = .retv v) ∨ c = .brk ∨ c = .cont)
    (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (K' : List (PyCore.Kont σ)) :
    ∀ pre : List (PyCore.Kont σ), (∀ k ∈ pre, PlainK k) →
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := c, kont := pre ++ K' } :: fs' }
      { t with stack := { f' with ctrl := c, kont := K' } :: fs' } ys ∧ ys.length = pre.length ∧
      ∀ y ∈ ys, PyCore.focus y = none
  | [], _ => ⟨[], .nil _, rfl, by simp⟩
  | k :: pre, hp => by
    obtain ⟨ys, py, hl, hf⟩ := pop_path hc t f' fs' K' pre (fun k hk => hp k (List.mem_cons_of_mem _ hk))
    have hk := hp k List.mem_cons_self
    refine ⟨_ :: ys, .cons ?_ py, by simp [hl], ?_⟩
    · rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl <;> cases k <;> simp [PlainK] at hk <;>
        (try (rename_i hs _; cases hs <;> simp at hk)) <;>
        simp [PyCore.step, PyCore.raiseStep, PyCore.retStep, PyCore.brkStep, PyCore.contStep, PyCore.top]
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rcases hc with ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl <;> cases k <;> simp [PlainK] at hk <;>
          (try (rename_i hs _; cases hs <;> simp at hk)) <;> simp [PyCore.focus]
      · exact hf y hy

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A signal passes one Surf item and PyCore's items `pre` for it. -/
theorem sig_popK (A : At p H s t f fs f' fs') {U U' : Label → Prop} {i j : Bool} (hc : CSig i f.chain U f.ctrl f'.ctrl)
    (hij : i = false → j = false) {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (pre : List (PyCore.Kont σ)) (hK' : f'.kont = pre ++ K0') (hp : ∀ k ∈ pre, PlainK k) (hne : pre ≠ [])
    (e1 : Sem.step I s = some { s with stack := { f with kont := K0 } :: fs })
    (hk : KRel A.x U' j K0 K0') (he : EnterSub K0 f.kont) : Goal I p H s t := by
  have hsig : (∃ v, f'.ctrl = .raise v) ∨ (∃ v, f'.ctrl = .retv v) ∨ f'.ctrl = .brk ∨ f'.ctrl = .cont := by
    rcases hc with ⟨v, -, h⟩ | ⟨v, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ <;> simp [h]
  obtain ⟨ys, py, hl, hf⟩ := pop_path (I := I) hsig t f' fs' K0' pre hp
  have ht0 : { t with stack := { f' with ctrl := f'.ctrl, kont := pre ++ K0' } :: fs' } = t := by
    rw [← hK']; exact t_eta A.ht
  rw [ht0] at py
  have hr := A.set (c := f.ctrl) (c' := f'.ctrl) (k := K0) (k' := K0') (csig_cr hc hij U') hk he
  exact goal_b (.cons e1 (.nil _)) (by simp) py (by rintro rfl; exact hne (List.length_eq_zero_iff.1 hl.symm))
    (crelI_seen hr) (cover_none hf)

end

/-! ## `SETUP_ANNOTATIONS` -/

theorem kc_setup : Py.constVal I "$setup" = .prim Gadget.setup.name := kc_gad I .setup trivial

theorem kc_dict0 : Py.constVal I "$op:display:dict:" = .op (.display (.dict [])) := by
  have := kc_dict (I := I) []; simpa [Py.starsStr] using this

/-- PyCore runs `setupS l` up to its dictionary's operation, every node on the way made for `l`. -/
theorem setup_path (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) (l : Label)
    (rest : PS) (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { g' with ctrl := .exec (setupS l :: rest), kont := K } :: gs' }
      { t with stack := { g' with ctrl := (.op (.display (.dict [])) []), kont := recK [] [] (.callA (.prim Gadget.setup.name) :: .exprS :: .seq rest :: K) } :: gs' } ys ∧
      ys ≠ [] ∧ ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l := by
  let K1 : List (PyCore.Kont σ) := .exprS :: .seq rest :: K
  let K2 : List (PyCore.Kont σ) := recK [] [] (.callA (.prim Gadget.setup.name) :: K1)
  let r := sub l 6
  let g := "$op:display:dict:"
  let mk (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ := { t with stack := { g' with ctrl := c, kont := k } :: gs' }
  obtain ⟨ys, pc, -, hfoc⟩ := cc_enter (I := I) t g' gs' (sub l 5) "$setup" (cc l 6 g []) [] K1
  rw [kc_setup] at pc
  have e0 : PyCore.step I (mk (.exec (setupS l :: rest)) K) = some (mk (.ev (ccR (sub l 5) "$setup" [cc l 6 g []])) K1) := by
    simp [mk, K1, g, PyCore.step, PyCore.execStep, PyCore.top, setupS, gad, cc, Gadget.name]
  have p2 : Path (PyCore.step I) (mk (.ev (cc l 6 g [])) K2) (mk (.op (.display (.dict [])) []) K2)
      [mk (.ev (cc l 6 g [])) K2, mk (.ev (.const r g)) (.callF (.const r "$args") :: K2),
        mk (.val (.op (.display (.dict [])))) (.callF (.const r "$args") :: K2),
        mk (.ev (.const r "$args")) (.callA (.op (.display (.dict []))) :: K2),
        mk (.val (.data "$args" [])) (.callA (.op (.display (.dict []))) :: K2)] := by
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))))
    · simp [mk, cc, ccR, recR, r, PyCore.step, PyCore.evalStep, PyCore.top]
    · simp [mk, r, g, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, kc_dict0]
    · simp [mk, PyCore.step, PyCore.valStep, PyCore.top]
    · simp [mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
    · simp [mk, PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.top, PyCore.argList]
  refine ⟨mk (.exec (setupS l :: rest)) K :: ys ++ _, .cons e0 (pc.append p2), by simp, ?_⟩
  intro y hy x hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with (rfl | hy) | rfl | rfl | rfl | rfl | rfl
  · simp [mk, PyCore.focus, setupS, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)
  · simp [mk, PyCore.focus, cc, ccR, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [mk, PyCore.focus, r, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [mk, PyCore.focus] at hx
  · simp [mk, PyCore.focus, r, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [mk, PyCore.focus] at hx

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- `handle_sim` after PyCore steps that evaluate no node of a Surf node (`pfocus`). -/
theorem handle_simP (A : At p H s t f fs f' fs') {U : Label → Prop} (r : Py.Res σ) (hk : KRel A.x U true f.kont f'.kont)
    (e1 : Sem.step I s = some (Sem.handle s.objs s.cells s.glob s.next s.res f fs r))
    (e2 : PyCore.step I t = some (PyCore.handle t.objs t.cells t.glob0 t.globW t.out t.next t.res f' fs' r))
    (hfoc : PyCore.focus t = none) {t0 : PyCore.Config σ} {ys0 : List (PyCore.Config σ)}
    (pb : Path (PyCore.step I) t0 t ys0) (hc0 : ∀ y ∈ ys0, pfocus y = none) : Goal I p H s t0 := by
  have hcov : ∀ zs : List (Sem.Config σ), Cover (Touch p) pfocus H zs (ys0 ++ [t]) := by
    intro zs y hy x hx
    rcases List.mem_append.1 hy with hy | hy
    · rw [hc0 y hy] at hx; cases hx
    · rw [List.mem_singleton] at hy; rw [hy] at hx
      rw [pfocus_le hx] at hfoc; cases hfoc
  have pb' := fun t1 (e : PyCore.step I t = some t1) => pb.append (.cons e (.nil t1))
  cases r with
  | ok st' v =>
    exact goal_b (.cons e1 (.nil _)) (by simp) (pb' _ e2) (by simp) (crelI_seen (A.setSt st' .val hk)) (hcov _)
  | raise st' e =>
    have h := A.setSt st' (c := Sem.raiseNew (f :: fs) e) (c' := PyCore.raiseNew (f' :: fs') e)
      (by rw [raiseNew_s, raiseNew_t A.stk]; exact .raise) hk
    exact goal_b (.cons e1 (.nil _)) (by simp) (pb' _ e2) (by simp) (crelI_seen h) (hcov _)
  | reraise st' e =>
    exact goal_b (.cons e1 (.nil _)) (by simp) (pb' _ e2) (by simp) (crelI_seen (A.setSt st' .raise hk)) (hcov _)
  | call st' g args kws k =>
    exact goal_b (.cons e1 (.nil _)) (by simp) (pb' _ e2) (by simp)
      (crelI_seen (A.setSt st' .call (.core (.native hk)))) (hcov _)

end

/-- The module's code is `p`'s. -/
theorem goodB_p (W : WF p) : GoodB p [] UAll p :=
  ⟨fun _ h => h, fun x hx => (by simp [PI, tr, PyCore.itemsB, trChain] at hx ⊢; simp [hx]), W.ok,
    fun _ _ => trivial, fun _ c h => (by cases h), W.nodup, fun _ h => h⟩

theorem ann_nd : ¬ Dot "__annotations__" := by decide

@[simp] theorem pglob_stack (t : PyCore.Config σ) (S : List (PyCore.Frame σ)) :
    ({ t with stack := S } : PyCore.Config σ).glob = t.glob := rfl

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- `SETUP_ANNOTATIONS`' dictionary reaches its item: `__annotations__` set in the class namespace or
the module dictionary unless set (PyCore: by `$setup`, two steps more). -/
theorem val_setAnn (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} {K0 : List (Sem.Kont σ)}
    {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) (hK : f.kont = .setAnn :: K0)
    (hK' : f'.kont = recK [] [] (.callA (.prim Gadget.setup.name) :: .exprS :: K0'))
    (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  let y := "__annotations__"
  let fr' : PyCore.Frame σ := { f' with ctrl := .val (.data "$args" [v]), kont := .callA (.prim Gadget.setup.name) :: .exprS :: K0' }
  have e2a : PyCore.step I t = some { t with stack := fr' :: fs' } := by
    simp [PyCore.step, A.ht, hc', hK', recK, PyCore.valStep, PyCore.top, fr']
  have hg := gad_name Gadget.setup trivial
  have hcov : ∀ (zs : List (Sem.Config σ)) (ys : List (PyCore.Config σ)), (∀ y ∈ ys, PyCore.focus y = none) →
      Cover (Touch p) pfocus H zs (t :: ys) := by
    intro zs ys hy
    refine cover_none fun z hz => ?_
    rcases List.mem_cons.1 hz with rfl | hz
    · simp [PyCore.focus, A.ht, hc']
    · exact hy z hz
  have hd : f'.kind = fk f.kind := A.hf.kind
  have hl : f'.ns.lookup y = f.ns.lookup y := drop_lookup A.hf.toFRel0 ann_nd
  have hgl : t.glob y = s.glob[y]? := A.r.glob y ann_nd
  have hcr : CR (σ := σ) p f.chain U false (.exec []) (.exec (trB f.chain [])) := .exec (goodB_nil _ _) (fun h => absurd rfl h)
  cases hkd : f.kind
  case cls =>
    have hd' : f'.kind = .cls := by rw [hd, hkd]; rfl
    by_cases hs : (f.ns.lookup y).isSome = true
    · let t2 : PyCore.Config σ := { t with stack := { fr' with ctrl := .val .none, kont := .exprS :: K0' } :: fs' }
      have e2b : PyCore.step I { t with stack := fr' :: fs' } = some t2 := by
        simp [PyCore.step, fr', PyCore.valStep, PyCore.callStep, PyCore.argList, hg, PyCore.gadgetStep, hd',
          PyCore.setupNs, PyCore.top, t2, hl, hs, y]
      have e2c : PyCore.step I t2 = some { t with stack := { f' with ctrl := .exec [], kont := K0' } :: fs' } := by
        simp [PyCore.step, t2, fr', PyCore.valStep, PyCore.top]
      exact goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hkd, Sem.setC, hs, y]) (.nil _)) (by simp)
        (.cons e2a (.cons e2b (.cons e2c (.nil _)))) (by simp) (crelI_seen (A.set hcr hk))
        (hcov _ _ (by simp [PyCore.focus, t2, fr']))
    · simp only [Bool.not_eq_true] at hs
      let ns' := PyCore.nsSet f'.ns y (some v)
      let g' : PyCore.Frame σ := { f' with ns := ns', ctrl := .exec [], kont := K0' }
      let g : Sem.Frame σ := { f with ns := Sem.nsSet f.ns y (some v), ctrl := .exec [], kont := K0 }
      let t2 : PyCore.Config σ := { t with stack := { fr' with ns := ns', ctrl := .val .none, kont := .exprS :: K0' } :: fs' }
      have e2b : PyCore.step I { t with stack := fr' :: fs' } = some t2 := by
        simp [PyCore.step, fr', PyCore.valStep, PyCore.callStep, PyCore.argList, hg, PyCore.gadgetStep, hd',
          PyCore.setupNs, PyCore.top, t2, hl, hs, y, ns']
      have e2c : PyCore.step I t2 = some { t with stack := g' :: fs' } := by
        simp [PyCore.step, t2, fr', PyCore.valStep, PyCore.top, g']
      have hf := A.hf
      have A1 := A.zero.write (s1 := { s with stack := g :: fs }) (t1 := { t with stack := g' :: fs' }) rfl rfl
        ⟨hf.id, hf.chain, hf.cls, hf.pcls, hf.kind, hf.kc, hf.κ, hf.κa,
          by simp only [g', g, ns']; rw [drop_nsSet y ann_nd, hf.ns], hf.kok⟩
        rfl rfl rfl rfl rfl A.r.cells A.r.glob (fun _ _ => Agree.refl _ _ _) rfl rfl rfl rfl rfl rfl rfl
        (esub_cons hK)
      have ha : Agree U (rdOf t f') (ownOf t f') (rdOf { t with stack := g' :: fs' } g') (ownOf { t with stack := g' :: fs' } g') :=
        agree_of (P := fun y => ¬ Dot y) (fun tag l _ _ h => h (dot_fresh tag l))
          (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun _ z hz =>
            lookup_nsSet_ne (x := z) (y := y) (by intro e; subst e; exact hz ann_nd) f'.ns (some v))
      exact goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hkd, Sem.setC, hs, y, g]) (.nil _)) (by simp)
        (.cons e2a (.cons e2b (.cons e2c (.nil _)))) (by simp)
        (crelI_seen (A1.crel hcr (krel_move hk rfl ha fun _ h => h)))
        (hcov _ _ (by simp [PyCore.focus, t2, fr']))
  all_goals
    have hd' : f'.kind ≠ .cls := by rw [hd, hkd]; simp [fk]
    have hgk : ∀ (c : PyCore.Config σ) (fr : PyCore.Frame σ) (gs : List (PyCore.Frame σ)), fr.kind = f'.kind →
        PyCore.gadgetStep I c fr gs .setup [v] = PyCore.setupGlob c fr gs v := by
      intro c fr gs hfr
      simp only [PyCore.gadgetStep]; split
      · rename_i h; rw [hfr] at h; exact absurd h hd'
      · rfl
    by_cases hs : s.glob.contains y = true
    · let t2 : PyCore.Config σ := { t with stack := { fr' with ctrl := .val .none, kont := .exprS :: K0' } :: fs' }
      have hs' : (t.glob y).isSome = true := by rw [hgl, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hs
      have e2b : PyCore.step I { t with stack := fr' :: fs' } = some t2 := by
        simp only [PyCore.step, fr', PyCore.valStep, PyCore.callStep, PyCore.argList, hg]
        rw [hgk _ { f' with ctrl := .val (.data "$args" [v]), kont := .exprS :: K0' } _ rfl]; simp [PyCore.setupGlob, hs', PyCore.top, t2, fr', y]
      have e2c : PyCore.step I t2 = some { t with stack := { f' with ctrl := .exec [], kont := K0' } :: fs' } := by
        simp [PyCore.step, t2, fr', PyCore.valStep, PyCore.top]
      exact goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hkd, Sem.setC, hs, y]) (.nil _)) (by simp)
        (.cons e2a (.cons e2b (.cons e2c (.nil _)))) (by simp) (crelI_seen (A.set hcr hk))
        (hcov _ _ (by simp [PyCore.focus, t2, fr']))
    · simp only [Bool.not_eq_true] at hs
      have hs' : (t.glob y).isSome = false := by rw [hgl, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hs
      let gW := t.globW.insert y (some v)
      let t2 : PyCore.Config σ := { t with globW := gW, stack := { fr' with ctrl := .val .none, kont := .exprS :: K0' } :: fs' }
      let t3 : PyCore.Config σ := { t with globW := gW, stack := { f' with ctrl := .exec [], kont := K0' } :: fs' }
      have e2b : PyCore.step I { t with stack := fr' :: fs' } = some t2 := by
        simp only [PyCore.step, fr', PyCore.valStep, PyCore.callStep, PyCore.argList, hg]
        rw [hgk _ { f' with ctrl := .val (.data "$args" [v]), kont := .exprS :: K0' } _ rfl]; simp [PyCore.setupGlob, hs', PyCore.top, t2, fr', y, gW]
      have e2c : PyCore.step I t2 = some t3 := by
        simp [PyCore.step, t2, fr', PyCore.valStep, PyCore.top, t3]
      let s3 : Sem.Config σ := { s with glob := s.glob.insert y v, stack := { f with ctrl := .exec [], kont := K0 } :: fs }
      have hg3 : ∀ z, t3.glob z = if y = z then some v else t.glob z := fun z => pglob_ins t _ y z (some v)
      have A1 := A.zero.write (s1 := s3) (t1 := t3) rfl rfl (A.hf.upd _ _ _ _) rfl rfl rfl rfl rfl A.r.cells
        (fun z hz => by
          simp only [pGlob, sGlob, hg3, s3, Std.HashMap.getElem?_insert, beq_iff_eq]
          split
          · rfl
          · exact A.r.glob z hz)
        (fun h' _ => agree_nd (t := t) (t1 := t3) h' _ (fun z hz => by rw [hg3, ite_ne]; rintro rfl; exact ann_nd hz) fun _ _ => rfl)
        rfl rfl rfl rfl rfl rfl rfl
      have ha : Agree U (rdOf t f') (ownOf t f') (rdOf t3 { f' with ctrl := .exec [], kont := K0' })
          (ownOf t3 { f' with ctrl := .exec [], kont := K0' }) :=
        (agree_nd (t := t) (t1 := t3) f' _ (fun z hz => by rw [hg3, ite_ne]; rintro rfl; exact ann_nd hz) fun _ _ => rfl).trans
          (Agree.refl _ _ _)
      exact goal_b (.cons (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, hkd, Sem.setC, hs, y, s3]) (.nil _))
        (by simp) (.cons e2a (.cons e2b (.cons e2c (.nil _)))) (by simp)
        (crelI_seen (A1.crel hcr (krel_move hk rfl ha fun _ h => h)))
        (hcov _ _ (by simp [PyCore.focus, t2, fr']))

/-! ## The start of a class body -/

/-- A class body's block, at the bottom of its frame. -/
theorem seq_at {x : Cx} {U : Label → Prop} {C : List Scope} {b : List Stmt} (hC : x.C = C) (hn : NoCompH C)
    (hb : GoodB x.p C U b) : CoreK (σ := σ) x U false [.seq b] [.seq (trB C b)] := by
  subst hC; exact .seq (pre := []) (fun _ => hn) (.inl rfl) hb .nil

/-- The start of a class body: `__module__`, `__qualname__` written through the body's
classification in both runs (or both raise), then PyCore runs `setupS l` up to the dictionary of
`SETUP_ANNOTATIONS`, which Surf's body starts with. -/
theorem cstart_sim {g : Sem.Frame σ} {gs : List (Sem.Frame σ)} {g' : PyCore.Frame σ} {gs' : List (PyCore.Frame σ)}
    (A : At0 p H s t g gs g' gs') {l : Label} {b : List Stmt} (q : String)
    (hc : g.ctrl = .exec b) (hk : g.kont = []) (hc' : g'.ctrl = .exec (setupS l :: trB g.chain b)) (hk' : g'.kont = [])
    (hb : GoodB p g.chain UAll b) (hnc : NoCompH g.chain) (S : List (Sem.Frame σ)) (S' : List (PyCore.Frame σ)) :
    ∃ s2 tX t2 ys, Sem.classStart I { s with stack := S } g gs q b = some s2 ∧
      PyCore.classStart I { t with stack := S' } g' gs' q = some tX ∧
      Path (PyCore.step I) tX t2 ys ∧ (∀ z ∈ ys, ∀ x, PyCore.focus z = some x → x / 64 = l) ∧ CRel p H s2 t2 := by
  have hn : ¬ Dot "__name__" := by decide
  have hm : ¬ Dot "__module__" := by decide
  have hq : ¬ Dot "__qualname__" := by decide
  have hr := readName_eq (I := I) (⟨A.hf, A.cells, A.glob⟩ : Ctx0 p H s t g g') hn
  have hrS : Sem.readName I { s with stack := S } g "__name__" = Sem.readName I s g "__name__" := rfl
  have hrS' : PyCore.readName I { t with stack := S' } g' "__name__" none = PyCore.readName I t g' "__name__" none := rfl
  have he : PyCore.kontExc g'.kont = Sem.kontExc g.kont := by rw [hk, hk']; rfl
  have hraise : ∀ e, CRel p H { s with stack := { g with ctrl := Sem.raiseNew (g :: gs) e, kont := g.kont } :: gs }
      { t with stack := { g' with ctrl := PyCore.raiseNew (g' :: gs') e, kont := g'.kont } :: gs' } := fun e =>
    (A.upd _ _ _ _).crel (U := UAll) (i := false) (by rw [raiseNew_s, raiseNew_top A.hfs he]; exact .raise)
      (by rw [hk, hk']; exact .nil)
  cases hrn : Sem.readName I s g "__name__" with
  | error e =>
    refine ⟨_, _, _, [], ?_, ?_, .nil _, by simp, hraise e⟩
    · simp only [Sem.classStart, hrS, hrn]
    · simp only [PyCore.classStart, hrS', hr, hrn]
  | ok m =>
    have hp := place_eq A.hf hm
    cases hp1 : Sem.place g "__module__" with
    | none =>
      rw [hp1] at hp
      refine ⟨_, _, _, [], ?_, ?_, .nil _, by simp, hraise (Py.err "NameError")⟩
      · simp only [Sem.classStart, hrS, hrn, hp1]
      · simp only [PyCore.classStart, hrS', hr, hrn, hp, Option.map]; rfl
    | some p1 =>
      rw [hp1] at hp
      obtain ⟨A2, hch2, -⟩ := write0 A hp1 hm (some m) g.ctrl g.kont g'.ctrl g'.kont
      have hpq : ∀ c : Sem.Config σ, Sem.place (Sem.writeAt c g (some m) p1).2 "__qualname__" = Sem.place g "__qualname__" := by
        intro c; cases p1 <;> rfl
      have hpq' : ∀ c : PyCore.Config σ, PyCore.place (PyCore.writeAt c g' (some m) (pl p1)).2 "__qualname__" =
          PyCore.place g' "__qualname__" := by
        intro c; cases p1 <;> rfl
      have hp2' := place_eq A.hf hq
      have hp2'' := place_eq A2.hf hq
      cases hp2 : Sem.place g "__qualname__" with
      | none =>
        rw [hp2] at hp2'
        have hr2 : CRel p H
            { (Sem.writeAt s g (some m) p1).1 with stack := { (Sem.writeAt s g (some m) p1).2 with
                ctrl := Sem.raiseNew (g :: gs) (Py.err "NameError"), kont := g.kont } :: gs }
            { (PyCore.writeAt t g' (some m) (pl p1)).1 with stack := { (PyCore.writeAt t g' (some m) (pl p1)).2 with
                ctrl := PyCore.raiseNew (g' :: gs') (Py.err "NameError"), kont := g'.kont } :: gs' } :=
          (A2.upd _ _ _ _).crel (U := UAll) (i := false) (by rw [raiseNew_s, raiseNew_top A.hfs he]; exact .raise)
            (by rw [hk, hk']; exact .nil)
        refine ⟨_, _, _, [], ?_, ?_, .nil _, by simp, hr2⟩
        · simp only [Sem.classStart, hrS, hrn, hp1, hpq, hp2]
          cases p1 <;> rfl
        · simp only [PyCore.classStart, hrS', hr, hrn, hp, Option.map, hpq', hp2']
          cases p1 <;> rfl
      | some p2 =>
        rw [hp2] at hp2'
        have hp3 : Sem.place { (Sem.writeAt s g (some m) p1).2 with ctrl := g.ctrl, kont := g.kont } "__qualname__" =
            some p2 := by rw [splace_ck, hpq s, hp2]
        obtain ⟨A3, hch3, -⟩ := write0 A2 hp3 hq (some (I.const s!"'{q}'")) (.op (.display (.dict [])) [])
          [.setAnn, .seq b] g'.ctrl g'.kont
        have hch : ((Sem.writeAt { (Sem.writeAt s g (some m) p1).1 with
            stack := { (Sem.writeAt s g (some m) p1).2 with ctrl := g.ctrl, kont := g.kont } :: gs }
            { (Sem.writeAt s g (some m) p1).2 with ctrl := g.ctrl, kont := g.kont } (some (I.const s!"'{q}'")) p2).2).chain =
            g.chain := hch3.trans hch2
        let W3 := PyCore.writeAt { (PyCore.writeAt t g' (some m) (pl p1)).1 with
            stack := { (PyCore.writeAt t g' (some m) (pl p1)).2 with ctrl := g'.ctrl, kont := g'.kont } :: gs' }
            { (PyCore.writeAt t g' (some m) (pl p1)).2 with ctrl := g'.ctrl, kont := g'.kont }
            (some (I.const s!"'{q}'")) (pl p2)
        have e : ({ W3.1 with stack := { W3.2 with ctrl := .exec (setupS l :: trB g.chain b), kont := [] } :: gs' } :
            PyCore.Config σ) = { W3.1 with stack := { W3.2 with ctrl := g'.ctrl, kont := g'.kont } :: gs' } := by
          rw [hc', hk']
        obtain ⟨ys, py, -, hfoc⟩ := setup_path (I := I) W3.1 W3.2 gs' l (trB g.chain b) []
        rw [e] at py
        have A4 := A3.updT (.op (.display (.dict [])) [])
          (recK [] [] [.callA (.prim Gadget.setup.name), .exprS, .seq (trB g.chain b)])
        refine ⟨_, _, _, ys, ?_, ?_, py, hfoc, A4.crel (U := UAll) (i := true) .op ?_⟩
        · simp only [Sem.classStart, hrS, hrn, hp1, hpq, hp2]
          cases p1 <;> cases p2 <;> rfl
        · simp only [PyCore.classStart, hrS', hr, hrn, hp, Option.map, hpq', hp2']
          cases p1 <;> cases p2 <;> rfl
        · exact .cls (.setAnn (.core (seq_at hch hnc hb)))


/-! ## Pushing a class body's frame -/

theorem kwPairs_map : ∀ kvs : List (Name × Val), Py.kwPairs (kvs.map fun p => .tuple [.str p.1, p.2]) = some kvs
  | [] => rfl
  | (k, v) :: kvs => by simp [Py.kwPairs, kwPairs_map kvs]

theorem unstash (dv args : List Val) (kvs : List (Name × Val)) :
    PyCore.clsUnstash (some (PyCore.clsStash dv args kvs)) = (dv, args, kvs) := by
  simp [PyCore.clsUnstash, PyCore.clsStash, kwPairs_map]

theorem fresh_ne_dot (tag : String) (l : Label) : fresh tag l ≠ "." := by
  intro h
  have := congrArg String.toList h
  simp [fresh] at this

theorem dot_dot : Dot "." := by decide

/-- The class body's code is the class statement's. -/
theorem good_body {C : List Scope} {U : Label → Prop} {l : Label} {y : Name} {bs : List Expr} {kws : List Kw}
    {b : List Stmt} {ds : List Expr} (hg : GoodB p C U [.cls l y bs kws b ds]) : GoodB p (.cl l y b :: C) UAll b := by
  have hok := hg.ok
  simp only [okB, okS, Bool.and_eq_true] at hok
  refine ⟨fun x hx => hg.s x (by simp [itemsB, itemsS, hx]), fun x hx => hg.t x ?_, hok.1.1.2, fun _ _ => trivial,
    fun _ c hc => by simp only [priv, Option.some.injEq] at hc; subst hc; exact hok.1.1.1.1.1, ?_,
    fun x hx => hg.tch x (by simp [touchB, touchS, hx])⟩
  · simp only [trB, trS, blk, PyCore.itemsB, PyCore.itemsS, PyCore.itemsHs, trChain, trScope, r0_s,
      Option.isSome_none, Bool.false_eq_true, ite_false, List.append_nil, List.mem_append, List.mem_cons] at hx ⊢
    simp [hx]
  · have hsub : List.Sublist (labelsB b) (labelsB [Stmt.cls l y bs kws b ds]) := by
      simp only [labelsB, labelsS, List.append_nil]
      exact .cons _ ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _))
    exact hg.nd.sublist hsub

theorem cellOf_eq {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {x : Name} (hx : ¬ Dot x) :
    PyCore.cellOf f' x = Sem.cellOf f x := by
  simp only [PyCore.cellOf, Sem.cellOf, hf.kind, cls_eq hf hx, hf.id, hf.κ x hx]
  cases f.kind <;> rfl

theorem cellOf_a {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') (x : Name) (a : Sem.Addr)
    (h : Sem.cellOf f x = some a) : a.2 = x := by
  simp only [Sem.cellOf] at h
  cases hk : f.kind <;> simp only [hk] at h
  all_goals first | exact hf.κa x a h | (split at h <;> first | (cases h; rfl) | exact hf.κa x a h)

/-- The frame of a class body pushed: by Surf's `pushClass`, by PyCore's class statement after `$cls`
left the arguments (and the statement's block); then the start of the body (`cstart_sim`). -/
theorem push_cls (A : At0 p H s t f fs f' fs') {U : Label → Prop} {l : Label} {y : Name} {bs : List Expr}
    {kws0 : List Kw} {b : List Stmt} {ds : List Expr} (hg : GoodB p f.chain U [.cls l y bs kws0 b ds])
    (hy : ¬ Dot (mangle (priv f.chain) y)) (hH : H l) (dv args : List Val) (kvs : List (Name × Val))
    (Kc : List (Sem.Kont σ)) (K' : List (PyCore.Kont σ))
    (hkc : KRel (cx p H (rdOf t f') (ownOf t f') f) U false Kc (.seq [] :: .tryE [] [] :: K'))
    (hen : EnterOk s.objs Kc) :
    ∃ s2 t2 ys, Sem.pushClass I s f fs l y b dv args kvs Kc = some s2 ∧
      Path (PyCore.step I)
        { t with stack := { f' with ns := PyCore.nsSet f'.ns "." (some (PyCore.clsStash dv args kvs)), ctrl := .val .none, kont := .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] :: K' } :: fs' }
        t2 ys ∧
      ys ≠ [] ∧ (∀ z ∈ ys, ∀ x, PyCore.focus z = some x → x / 64 = l) ∧ CRel p H s2 t2 := by
  let C := f.chain
  let y' := mangle (priv C) y
  let q := qualIn C y
  let bP : PS := setupS l :: trB (.cl l y b :: C) b
  let nsb := PyCore.nsSet f'.ns "." (some (PyCore.clsStash dv args kvs))
  let fe : PyCore.Frame σ := { f' with ns := nsb, ctrl := .exec [clsS C l y b], kont := .tryE [] [] :: K' }
  let gP : PyCore.Frame σ := {
      id := t.next, chain := .cl (sub l 1) bP :: fe.chain, kind := .cls,
      cls := (Py.memo (PyCore.Scope.cl (sub l 1) bP).names (PyCore.clsOf (.cl (sub l 1) bP :: fe.chain))).get,
      κ := PyCore.cellOf fe, ns := [], ctrl := .exec bP, kont := [] }
  let fcP : PyCore.Frame σ := { fe with
      ns := PyCore.nsSet fe.ns "." none, ctrl := .wait,
      kont := .clsEnd y' q args kvs dv :: .assign y' :: .seq [] :: .tryE [] [] :: K' }
  let gS : Sem.Frame σ := {
      id := s.next, chain := .cl l y b :: C, kind := .cls,
      cls := (Py.memo (Sem.Scope.names C (Scope.cl l y b)) (clsOf (.cl l y b :: C))).get, κ := Sem.cellOf f, ns := [],
      ctrl := .exec b, kont := [] }
  let fcS : Sem.Frame σ := { f with ctrl := .wait, kont := .clsEnd (Sem.mg f y) q args kvs dv :: Kc }
  let s1 : Sem.Config σ := { s with next := s.next + 1, stack := gS :: fcS :: fs }
  let t1 : PyCore.Config σ := { t with next := t.next + 1, stack := gP :: fcP :: fs' }
  have hf := A.hf
  -- the caller
  have hfc0 : FRel0 fcS fcP := ⟨hf.id, hf.chain, hf.cls, hf.pcls, hf.kind, hf.kc, hf.κ, hf.κa,
    by simp only [fcP, fe, nsb]; rw [drop_nsSet_dot _ dot_dot, drop_nsSet_dot _ dot_dot, hf.ns], hf.kok⟩
  have ha : Agree U (rdOf t f') (ownOf t f') (rdOf t1 fcP) (ownOf t1 fcP) :=
    agree_of (P := (· = ".")) (fun tag l _ _ h => fresh_ne_dot tag l h)
      (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun _ z hz => by
        simp only [fcP, fe, nsb]; rw [lookup_nsSet_ne hz, lookup_nsSet_ne hz])
  have hfc : FRel p H (rdOf t1 fcP) (ownOf t1 fcP) fcS fcP :=
    ⟨hfc0, A.hl, U, false, .wait, .cls (.clsEnd hy (krel_move hkc rfl ha fun _ h => h))⟩
  -- the body's frame
  have hok := hg.ok
  simp only [okB, okS, Bool.and_eq_true] at hok
  have hg0 : FRel0 gS gP := by
    refine ⟨by simp [gP, gS, A.next], by simp [gP, gS, fe, trChain, trScope, hf.chain, bP, C], by simp [gS, Py.memo_eq],
      by simp [gP, Py.memo_eq], rfl, trivial, fun x hx => cellOf_eq hf hx, fun x a h => cellOf_a hf x a h, rfl,
      ⟨hok.1.1.1.1.1, hf.kok⟩⟩
  have ids : Ids t1 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.ids
    rw [A.ht] at h1 h2 h4 h5 h6
    have hlt : ∀ g ∈ f' :: fs', g.id < t.next := h2
    refine ⟨?_, fun g hg => ?_, fun o b hb => ?_, fun o g ho => ?_, fun g hg o hk => ?_, fun g hg hm => ?_,
      fun o g ho => h7 o g ho⟩
    · simp only [t1, List.map_cons, List.nodup_cons] at h1 ⊢
      refine ⟨?_, h1⟩
      intro hm
      simp only [gP, List.mem_cons, List.mem_map] at hm
      rcases hm with e | ⟨g, hg, e⟩
      · exact absurd (hlt f' (by simp)) (by simp [fcP, fe] at e; omega)
      · exact absurd (hlt g (by simp [hg])) (by omega)
    · simp only [t1, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp [gP, t1]
      · have := hlt f' (by simp); simp [fcP, fe, t1]; omega
      · have := hlt g (by simp [hg]); simp [t1]; omega
    · have := h3 o b hb; simp [t1]; omega
    · obtain ⟨e, hne⟩ := h4 o g ho
      have hob := h3 o _ ho
      refine ⟨e, fun h hh => ?_⟩
      simp only [t1, List.mem_cons] at hh
      rcases hh with rfl | rfl | hh
      · simp [gP]; omega
      · exact hne f' (by simp)
      · exact hne h (by simp [hh])
    · simp only [t1, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp [gP] at hk
      · exact h5 f' (by simp) o hk
      · exact h5 g (by simp [hg]) o hk
    · simp only [t1, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · simp [gP] at hm
      · exact h6 f' (by simp) hm
      · exact h6 g (by simp [hg]) hm
  have A1 : At0 p H s1 t1 gS (fcS :: fs) gP (fcP :: fs') :=
    ⟨rfl, rfl, hg0, fun S C' e => by simp only [gS, List.cons.injEq] at e; rw [← e.1]; exact hH, ⟨hfc, A.hfs⟩,
      A.objs, A.cells, A.glob, A.out, by simp [t1, s1, A.next], A.res, A.st,
      fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg
        · rfl
        · exact A.wait g hg, ids,
      ⟨fun g hg => by
        rcases List.mem_cons.1 hg with rfl | hg
        · exact enterOk_nil
        rcases List.mem_cons.1 hg with rfl | hg
        · exact fun o b kx hm => hen o b kx (by simpa [fcS] using hm)
        · exact A.enter.1 g (List.mem_cons_of_mem _ hg), A.enter.2⟩⟩
  obtain ⟨s2, tX, t2, ys, e1, e2, py, hfoc, hr⟩ := cstart_sim (I := I) A1 q rfl rfl rfl rfl (good_body hg) rfl s.stack
    (fe :: fs')
  let td : PyCore.Config σ :=
    { t with stack := { f' with ns := nsb, ctrl := .exec [], kont := .seq [clsS C l y b] :: .tryE [] [] :: K' } :: fs' }
  let te : PyCore.Config σ := { t with stack := fe :: fs' }
  refine ⟨s2, t2, _ :: td :: te :: ys, e1, .cons (a' := td) ?_ (.cons (a' := te) ?_ (.cons (a' := tX) ?_ py)),
    by simp, ?_, hr⟩
  · simp [PyCore.step, PyCore.valStep, PyCore.top, td, nsb, C]
  · simp [PyCore.step, PyCore.doneStep, PyCore.top, td, te, fe]
  · rw [← e2]
    simp [PyCore.step, PyCore.execStep, clsS, te, fe, nsb, lookup_nsSet, unstash, gP, fcP, y', q, bP, C, t1]
  · intro z hz x hx
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | hz
    · simp [PyCore.focus] at hx
    · simp [PyCore.focus] at hx
    · simp [PyCore.focus, te, fe, clsS, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · exact hfoc z hz x hx

end

/-! ## `$cls`'s split of its record -/

/-- A keyword argument's name (`none` for `**m`). -/
def kwName : Kw → Option Name | .mk _ x _ => x

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
    (((kws.map kwMark).map pval).zip kv).mapM (Py.markKw ·.1) = some (kws.map kwName)
  | [], [], _ => rfl
  | .mk l x e :: kws, v :: kv, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.mapM_cons, zip_kw_mapM kws kv (by simpa using h)]
    simp [kwMark, pval, markKw_kw, kwName]

theorem zip_snd : ∀ (ms vs : List Val), ms.length = vs.length → (ms.zip vs).map (·.2) = vs
  | [], [], _ => rfl
  | _ :: ms, v :: vs, h => by simp [zip_snd ms vs (by simpa using h)]

/-- `$cls` (and `$call`) split their record's values and markers into the positional arguments and
the keywords, as Surf's statement has them. -/
theorem split_cls (bs : List Expr) (kws : List Kw) (bv kv : List Val) (hb : bv.length = bs.length)
    (hk : kv.length = kws.length) :
    (Py.pairs (bv ++ kv ++ (bs.map starMark ++ kws.map kwMark).map pval)).bind Py.splitArgs =
      some (bs.map isStar, bv, kws.map kwName, kv) := by
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

/-! ## The arguments ready: the class's code next -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- Surf's step pushes the class body (`pushClass`, after `pa`), PyCore's path `pb` reaches `$cls`'s
stash: both reach the class body's dictionary of `SETUP_ANNOTATIONS`. -/
theorem goal_push (A : At p H s t f fs f' fs') {U : Label → Prop} {l : Label} {y : Name} {bs : List Expr}
    {kws0 : List Kw} {b : List Stmt} {ds : List Expr} (hg : GoodB p f.chain U [.cls l y bs kws0 b ds])
    (hy : ¬ Dot (mangle (priv f.chain) y)) (dv args : List Val) (kvs : List (Name × Val))
    (Kc : List (Sem.Kont σ)) (K' : List (PyCore.Kont σ))
    (hkc : KRel A.x U false Kc (.seq [] :: .tryE [] [] :: K'))
    {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} (hen : EnterSub Kc f.kont) (hek : EnterSub k f.kont) {xs : List (Sem.Config σ)}
    (pa : Path (Sem.step I) s { s with stack := { f with ctrl := c, kont := k } :: fs } xs)
    (ea : Sem.step I { s with stack := { f with ctrl := c, kont := k } :: fs } =
      Sem.pushClass I { s with stack := { f with ctrl := c, kont := k } :: fs } { f with ctrl := c, kont := k } fs
        l y b dv args kvs Kc)
    (hH : Seen (Touch p) H (xs ++ [{ s with stack := { f with ctrl := c, kont := k } :: fs }]) l)
    {ys0 : List (PyCore.Config σ)}
    (pb : Path (PyCore.step I) t
      { t with stack := { f' with ns := PyCore.nsSet f'.ns "." (some (PyCore.clsStash dv args kvs)), ctrl := .val .none, kont := .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] :: K' } :: fs' }
      ys0)
    (hcov0 : ∀ z ∈ ys0, ∀ x, pfocus z = some x →
      Seen (Touch p) H (xs ++ [{ s with stack := { f with ctrl := c, kont := k } :: fs }]) (x / 64)) :
    Goal I p H s t := by
  let sa : Sem.Config σ := { s with stack := { f with ctrl := c, kont := k } :: fs }
  let H' := Seen (Touch p) H (xs ++ [sa])
  have hHH : ∀ l, H l → H' l := fun _ h => .inl h
  obtain ⟨s2, t2, ys, e1, py, hys, hfoc, hr⟩ := push_cls (I := I) (((A.zero.updS c k hek).mono_H hHH)) hg hy hH dv args kvs
    Kc K' (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hkc) ((A.r.enter.1 f (A.hs ▸ List.mem_cons_self)).sub hen)
  refine goal_b (pa.append (.cons (ea.trans e1) (.nil s2))) (by simp) (pb.append py) (by simp [hys]) (.inl hr) ?_
  intro z hz x hx
  have hm : ∀ {l}, H' l → Seen (Touch p) H (s2 :: (xs ++ [sa])) l := fun h =>
    seen_sub (fun z hz => List.mem_cons_of_mem _ hz) _ h
  rcases List.mem_append.1 hz with hz | hz
  · exact hm (hcov0 z hz x hx)
  · rw [hfoc z hz x (pfocus_le hx)]; exact hm hH

end

/-! ### The entries of the argument items

`ClsK.evsCls`, `ClsK.argStarC`, `ClsK.argKwC`, written with `clsArgs` and `kwName` (`evsMk`, `starMk`,
`kwMk` below build them from the constructors). -/

/-- A keyword argument's value. -/
def kwVal : Kw → Expr | .mk _ _ e => e

/-- The class statement's argument items, as Surf evaluates them: decorators, bases, keyword values. -/
def clsArgs (ds bs : List Expr) (kws : List Kw) : List (Option Expr) :=
  ds.map some ++ bs.map (fun a => some (unstar a)) ++ kws.map (fun k => some (kwVal k))

/-- `ClsK.evsCls`. -/
def EvsMkC (σ : Type) : Prop :=
  ∀ {x : Cx} {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l : Label} {y : Name}
    {bs : List Expr} {kws : List Kw} {b : List Stmt} {ds : List Expr} {ss : List Stmt}
    {rest : List (Option Expr)} {acc : List Val} {ps : List PE},
    x.H l → GoodB x.p x.C U [.cls l y bs kws b ds] → ¬ Dot (mangle (priv x.C) y) →
    acc.length < (clsArgs ds bs kws).length → rest = (clsArgs ds bs kws).drop (acc.length + 1) →
    (∀ a ∈ bs.take (acc.length + 1 - ds.length), x.H (Sem.Expr.lbl a)) →
    (∀ k ∈ kws.take (acc.length + 1 - ds.length - bs.length), x.H k.lbl) →
    PartsR x U l rest ps → (ss ≠ [] → NoCompH x.C) → GoodB x.p x.C U ss → KRel x U false K K' →
    KRel x U true (.evs rest acc (.cls l y b ds.length (bs.map isStar) (kws.map kwName)) :: .seq ss :: K)
      (recK acc.reverse (ps ++ bs.map starMark ++ kws.map kwMark)
        (.callA (.prim (Gadget.cls ds.length).name) :: .exprS :: .seq [clsS x.C l y b] :: .tryE [] [] ::
          .seq (trB x.C ss) :: K'))

/-- `ClsK.argStarC`. -/
def StarMkC (σ : Type) : Prop :=
  ∀ {x : Cx} {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l : Label} {y : Name}
    {bs : List Expr} {kws0 : List Kw} {b : List Stmt} {ds : List Expr} {ss : List Stmt} {dv : List Val}
    {kws : List (Option Name)} {kwvals : List Val},
    x.H l → GoodB x.p x.C U [.cls l y bs kws0 b ds] → ¬ Dot (mangle (priv x.C) y) →
    (ss ≠ [] → NoCompH x.C) → GoodB x.p x.C U ss → KRel x U false K K' →
    KRel x U true (.argStar (.cls l y b dv) kws kwvals :: .seq ss :: K)
      (.argStar (.cls dv) kws kwvals :: .exprS :: .seq [clsS x.C l y b] :: .tryE [] [] :: .seq (trB x.C ss) :: K')

/-- `ClsK.argKwC`. -/
def KwMkC (σ : Type) : Prop :=
  ∀ {x : Cx} {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} {l : Label} {y : Name}
    {bs : List Expr} {kws0 : List Kw} {b : List Stmt} {ds : List Expr} {ss : List Stmt} {dv : List Val}
    {args : List Val},
    x.H l → GoodB x.p x.C U [.cls l y bs kws0 b ds] → ¬ Dot (mangle (priv x.C) y) →
    (ss ≠ [] → NoCompH x.C) → GoodB x.p x.C U ss → KRel x U false K K' →
    KRel x U true (.argKw (.cls l y b dv) args :: .seq ss :: K)
      (.argKw (.cls dv) args :: .exprS :: .seq [clsS x.C l y b] :: .tryE [] [] :: .seq (trB x.C ss) :: K')

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The keyword phase of a class statement's arguments on both sides: `**m` expanded, or the class's code. -/
theorem kw_goal (mw : KwMkC σ) (A : At p H s t f fs f' fs') {U : Label → Prop} {l : Label} {y : Name}
    {bs : List Expr} {kws0 : List Kw} {b : List Stmt} {ds : List Expr}
    (hg : GoodB p f.chain U [.cls l y bs kws0 b ds]) (hy : ¬ Dot (mangle (priv f.chain) y)) {ss : List Stmt}
    (hnc : ss ≠ [] → NoCompH f.chain) (hgs : GoodB p f.chain U ss) {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (hk : KRel A.x U false K K') (dv args : List Val) (kws : List (Option Name))
    (kwvals : List Val) {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} {xs : List (Sem.Config σ)}
    (hen : EnterSub (.seq ss :: K) f.kont) (hek : EnterSub k f.kont)
    (pa : Path (Sem.step I) s { s with stack := { f with ctrl := c, kont := k } :: fs } xs)
    (ea : Sem.step I { s with stack := { f with ctrl := c, kont := k } :: fs } =
      Sem.kwPhase I { s with stack := { f with ctrl := c, kont := k } :: fs } { f with ctrl := c, kont := k } fs
        (.cls l y b dv) args kws kwvals (.seq ss :: K))
    (hH : Seen (Touch p) H (xs ++ [{ s with stack := { f with ctrl := c, kont := k } :: fs }]) l)
    {c' : PyCore.Ctrl σ} {k' : List (PyCore.Kont σ)} {ys0 : List (PyCore.Config σ)}
    (pb : Path (PyCore.step I) t { t with stack := { f' with ctrl := c', kont := k' } :: fs' } ys0)
    (eb : PyCore.step I { t with stack := { f' with ctrl := c', kont := k' } :: fs' } =
      PyCore.kwPhase { t with stack := { f' with ctrl := c', kont := k' } :: fs' } { f' with ctrl := c', kont := k' }
        fs' (.cls dv) args kws kwvals
        (.exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] :: .seq (trB f.chain ss) :: K'))
    (hfA : PyCore.focus { t with stack := { f' with ctrl := c', kont := k' } :: fs' } = none)
    (hcov0 : ∀ z ∈ ys0, ∀ x, pfocus z = some x →
      Seen (Touch p) H (xs ++ [{ s with stack := { f with ctrl := c, kont := k } :: fs }]) (x / 64)) :
    Goal I p H s t := by
  let sa : Sem.Config σ := { s with stack := { f with ctrl := c, kont := k } :: fs }
  let tA : PyCore.Config σ := { t with stack := { f' with ctrl := c', kont := k' } :: fs' }
  have hcovA : ∀ z ∈ ys0 ++ [tA], ∀ x, pfocus z = some x → Seen (Touch p) H (xs ++ [sa]) (x / 64) := by
    intro z hz x hx
    rcases List.mem_append.1 hz with hz | hz
    · exact hcov0 z hz x hx
    · rw [List.mem_singleton] at hz; subst hz; rw [pfocus_le hx] at hfA; cases hfA
  by_cases hkw : kws.any Option.isNone = true
  · let H' := Seen (Touch p) H (xs ++ [sa])
    have hHH : ∀ l, H l → H' l := fun _ h => .inl h
    have A' := A.mono hHH
    have hr := A'.set (c := .op (.display (.kwargs kws)) kwvals) (c' := .op (.display (.kwargs kws)) kwvals)
      (k := .argKw (.cls l y b dv) args :: .seq ss :: K)
      (k' := .argKw (.cls dv) args :: .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] :: .seq (trB f.chain ss) :: K')
      .op (mw hH hg hy hnc hgs (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hk)) (esub_tail (fun _ _ _ h => by cases h) hen)
    refine goal_b (pa.append (.cons (by rw [ea]; simp [Sem.kwPhase, hkw, Sem.doOp, Sem.setC]) (.nil _))) (by simp)
      (pb.append (.cons (by rw [eb]; simp [PyCore.kwPhase, hkw, PyCore.top]) (.nil _))) (by simp) (.inl hr) ?_
    intro z hz x hx
    exact seen_sub (fun z hz => List.mem_cons_of_mem _ hz) _ (hcovA z hz x hx)
  · simp only [Bool.not_eq_true] at hkw
    refine goal_push A hg hy dv args ((kws.filterMap id).zip kwvals) (.seq ss :: K)
      (.seq (trB f.chain ss) :: K') (.core (.seq (pre := [.seq [], .tryE [] []]) hnc (.inr (.inr rfl)) hgs hk))
      hen hek pa (by rw [ea]; simp [Sem.kwPhase, hkw, Sem.finishArgs]) hH
      (pb.append (.cons (by rw [eb]; simp [PyCore.kwPhase, hkw, PyCore.finishArgs, PyCore.top]) (.nil _))) hcovA

/-- The positional phase of a class statement's arguments on both sides: `*e` expanded, or the keyword phase. -/
theorem star_goal (ms : StarMkC σ) (mw : KwMkC σ) (A : At p H s t f fs f' fs') {U : Label → Prop} {l : Label}
    {y : Name} {bs : List Expr} {kws0 : List Kw} {b : List Stmt} {ds : List Expr}
    (hg : GoodB p f.chain U [.cls l y bs kws0 b ds]) (hy : ¬ Dot (mangle (priv f.chain) y)) {ss : List Stmt}
    (hnc : ss ≠ [] → NoCompH f.chain) (hgs : GoodB p f.chain U ss) {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (hk : KRel A.x U false K K') (dv args : List Val) (stars : List Bool)
    (kws : List (Option Name)) (kwvals : List Val) {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} {xs : List (Sem.Config σ)}
    (hen : EnterSub (.seq ss :: K) f.kont) (hek : EnterSub k f.kont)
    (pa : Path (Sem.step I) s { s with stack := { f with ctrl := c, kont := k } :: fs } xs)
    (ea : Sem.step I { s with stack := { f with ctrl := c, kont := k } :: fs } =
      Sem.argPhase I { s with stack := { f with ctrl := c, kont := k } :: fs } { f with ctrl := c, kont := k } fs
        (.cls l y b dv) args stars kws kwvals (.seq ss :: K))
    (hH : Seen (Touch p) H (xs ++ [{ s with stack := { f with ctrl := c, kont := k } :: fs }]) l)
    {c' : PyCore.Ctrl σ} {k' : List (PyCore.Kont σ)} {ys0 : List (PyCore.Config σ)}
    (pb : Path (PyCore.step I) t { t with stack := { f' with ctrl := c', kont := k' } :: fs' } ys0)
    (eb : PyCore.step I { t with stack := { f' with ctrl := c', kont := k' } :: fs' } =
      PyCore.argPhase { t with stack := { f' with ctrl := c', kont := k' } :: fs' } { f' with ctrl := c', kont := k' }
        fs' (.cls dv) args stars kws kwvals
        (.exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] :: .seq (trB f.chain ss) :: K'))
    (hfA : PyCore.focus { t with stack := { f' with ctrl := c', kont := k' } :: fs' } = none)
    (hcov0 : ∀ z ∈ ys0, ∀ x, pfocus z = some x →
      Seen (Touch p) H (xs ++ [{ s with stack := { f with ctrl := c, kont := k } :: fs }]) (x / 64)) :
    Goal I p H s t := by
  by_cases hst : stars.any id = true
  · let sa : Sem.Config σ := { s with stack := { f with ctrl := c, kont := k } :: fs }
    let tA : PyCore.Config σ := { t with stack := { f' with ctrl := c', kont := k' } :: fs' }
    let H' := Seen (Touch p) H (xs ++ [sa])
    have hHH : ∀ l, H l → H' l := fun _ h => .inl h
    have A' := A.mono hHH
    have hr := A'.set (c := .op (.display (.tuple stars)) args) (c' := .op (.display (.tuple stars)) args)
      (k := .argStar (.cls l y b dv) kws kwvals :: .seq ss :: K)
      (k' := .argStar (.cls dv) kws kwvals :: .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] ::
        .seq (trB f.chain ss) :: K')
      .op (ms hH hg hy hnc hgs (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hk)) (esub_tail (fun _ _ _ h => by cases h) hen)
    refine goal_b (pa.append (.cons (by rw [ea]; simp [Sem.argPhase, hst, Sem.doOp, Sem.setC]) (.nil _))) (by simp)
      (pb.append (.cons (by rw [eb]; simp [PyCore.argPhase, hst, PyCore.top]) (.nil _))) (by simp) (.inl hr) ?_
    intro z hz x hx
    refine seen_sub (fun z hz => List.mem_cons_of_mem _ hz) _ ?_
    rcases List.mem_append.1 hz with hz | hz
    · exact hcov0 z hz x hx
    · rw [List.mem_singleton] at hz; subst hz; rw [pfocus_le hx] at hfA; cases hfA
  · simp only [Bool.not_eq_true] at hst
    exact kw_goal mw A hg hy hnc hgs hk dv args kws kwvals hen hek pa (by rw [ea]; simp [Sem.argPhase, hst]) hH pb
      (by rw [eb]; simp [PyCore.argPhase, hst]) hfA hcov0

/-- A value reaches `**m`'s expansion of a class statement's keywords: the class's code next. -/
theorem val_argKwC_of (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val} (hc : f.ctrl = .val v)
    (hc' : f'.ctrl = .val v) {l : Label} {y : Name} {bs : List Expr} {kws0 : List Kw} {b : List Stmt}
    {ds : List Expr} {ss : List Stmt} {dv args : List Val} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hK : f.kont = .argKw (.cls l y b dv) args :: .seq ss :: K)
    (hK' : f'.kont = .argKw (.cls dv) args :: .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] ::
      .seq (trB f.chain ss) :: K')
    (hH : H l) (hg : GoodB p f.chain U [.cls l y bs kws0 b ds]) (hy : ¬ Dot (mangle (priv f.chain) y))
    (hnc : ss ≠ [] → NoCompH f.chain) (hgs : GoodB p f.chain U ss) (hk : KRel A.x U false K K') :
    Goal I p H s t := by
  have hft : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  by_cases hv : ∃ pairs kvs, v = .tuple pairs ∧ Py.kwPairs pairs = some kvs
  · obtain ⟨pairs, kvs, rfl, hp⟩ := hv
    have pa : Path (Sem.step I) s { s with stack := { f with ctrl := f.ctrl, kont := f.kont } :: fs } [] := by
      rw [s_eta A.hs]; exact .nil s
    refine goal_push A hg hy dv args kvs (.seq ss :: K) (.seq (trB f.chain ss) :: K')
      (.core (.seq (pre := [.seq [], .tryE [] []]) hnc (.inr (.inr rfl)) hgs hk)) (esub_cons hK) esub_refl pa ?_ (.inl hH)
      (.cons ?_ (.nil _)) ?_
    · simp [Sem.step, hc, hK, Sem.valStep, hp, Sem.finishArgs]
    · simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, hp, PyCore.finishArgs, PyCore.top]
    · intro z hz x hx; simp at hz; subst hz; rw [pfocus_le hx] at hft; cases hft
  · refine fin_stuck A ?_ ?_ (cov_none A hft)
    · simp only [Sem.step, A.hs, hc, hK, Sem.valStep]
      split
      · rename_i pairs
        split
        · rename_i kvs hp; exact absurd ⟨pairs, kvs, rfl, hp⟩ hv
        · rfl
      · rfl
    · simp only [PyCore.step, A.ht, hc', hK', PyCore.valStep]
      split
      · rename_i pairs
        split
        · rename_i kvs hp; exact absurd ⟨pairs, kvs, rfl, hp⟩ hv
        · rfl
      · rfl

/-- A value reaches `*e`'s expansion of a class statement's bases: the keyword phase next. -/
theorem val_argStarC_of (mw : KwMkC σ) (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val}
    (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) {l : Label} {y : Name} {bs : List Expr} {kws0 : List Kw}
    {b : List Stmt} {ds : List Expr} {ss : List Stmt} {dv : List Val} {kws : List (Option Name)} {kwvals : List Val}
    {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hK : f.kont = .argStar (.cls l y b dv) kws kwvals :: .seq ss :: K)
    (hK' : f'.kont = .argStar (.cls dv) kws kwvals :: .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] ::
      .seq (trB f.chain ss) :: K')
    (hH : H l) (hg : GoodB p f.chain U [.cls l y bs kws0 b ds]) (hy : ¬ Dot (mangle (priv f.chain) y))
    (hnc : ss ≠ [] → NoCompH f.chain) (hgs : GoodB p f.chain U ss) (hk : KRel A.x U false K K') :
    Goal I p H s t := by
  have hft : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  by_cases hv : ∃ args, v = .tuple args
  · obtain ⟨args, rfl⟩ := hv
    have pa : Path (Sem.step I) s { s with stack := { f with ctrl := f.ctrl, kont := f.kont } :: fs } [] := by
      rw [s_eta A.hs]; exact .nil s
    have pb : Path (PyCore.step I) t { t with stack := { f' with ctrl := f'.ctrl, kont := f'.kont } :: fs' } [] := by
      rw [t_eta A.ht]; exact .nil t
    exact kw_goal mw A hg hy hnc hgs hk dv args kws kwvals (esub_cons hK) esub_refl pa
      (by simp [Sem.step, hc, hK, Sem.valStep]) (.inl hH) pb
      (by simp [PyCore.step, hc', hK', PyCore.valStep]) (by simp [PyCore.focus, hc']) (by simp)
  · refine fin_stuck A ?_ ?_ (cov_none A hft)
    · simp only [Sem.step, A.hs, hc, hK, Sem.valStep]
      split
      · rename_i args; exact absurd ⟨args, rfl⟩ hv
      · rfl
    · simp only [PyCore.step, A.ht, hc', hK', PyCore.valStep]
      split
      · rename_i args; exact absurd ⟨args, rfl⟩ hv
      · rfl

end

/-! ### The argument items -/

theorem clsArgs_len (ds bs : List Expr) (kws : List Kw) :
    (clsArgs ds bs kws).length = ds.length + bs.length + kws.length := by simp [clsArgs, Nat.add_assoc]

theorem clsArgs_get {ds bs : List Expr} {kws : List Kw} {i : Nat} {o : Option Expr}
    (h : (clsArgs ds bs kws)[i]? = some o) :
    (i < ds.length ∧ ∃ d ∈ ds, o = some d) ∨
    (ds.length ≤ i ∧ i < ds.length + bs.length ∧ ∃ a, bs[i - ds.length]? = some a ∧ o = some (unstar a)) ∨
    (ds.length + bs.length ≤ i ∧ ∃ k, kws[i - ds.length - bs.length]? = some k ∧ o = some (kwVal k)) := by
  simp only [clsArgs] at h
  by_cases h1 : i < ds.length
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)] at h
    simp only [List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    exact .inl ⟨h1, d, List.mem_of_getElem? hd, rfl⟩
  by_cases h2 : i < ds.length + bs.length
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by simp; omega)] at h
    simp only [List.getElem?_map, Option.map_eq_some_iff, List.length_map] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact .inr (.inl ⟨by omega, h2, a, ha, rfl⟩)
  · rw [List.getElem?_append_right (by simp; omega)] at h
    simp only [List.getElem?_map, Option.map_eq_some_iff, List.length_map, List.length_append] at h
    obtain ⟨k, hk, rfl⟩ := h
    exact .inr (.inr ⟨by omega, k, by rw [← hk]; congr 1; omega, rfl⟩)

theorem take_step {α} {P : α → Prop} {l : List α} {m : Nat} {a : α} (hl : l[m]? = some a) (hold : ∀ x ∈ l.take m, P x)
    (hnew : P a) : ∀ x ∈ l.take (m + 1), P x := by
  intro x hx
  rw [List.take_add_one, hl] at hx
  rcases List.mem_append.1 hx with hx | hx
  · exact hold x hx
  · simp at hx; subst hx; exact hnew

theorem take_full {α} {P : α → Prop} {l : List α} {m n : Nat} (hm : l.length ≤ m) (hold : ∀ x ∈ l.take m, P x) :
    ∀ x ∈ l.take n, P x := fun x hx => hold x (by rw [List.take_of_length_le hm]; exact List.mem_of_mem_take hx)

/-- The touched prefix of the bases and keywords extends to the item `i` once its node is touched. -/
theorem touch_next {P : Label → Prop} {ds bs : List Expr} {kws : List Kw} {i : Nat} {e : Expr}
    (hi : (clsArgs ds bs kws)[i]? = some (some e))
    (hP : ∀ a ∈ bs, unstar a = e → P (Sem.Expr.lbl a)) (hPk : ∀ k ∈ kws, kwVal k = e → P k.lbl)
    (hb : ∀ a ∈ bs.take (i - ds.length), P (Sem.Expr.lbl a))
    (hk : ∀ k ∈ kws.take (i - ds.length - bs.length), P k.lbl) :
    (∀ a ∈ bs.take (i + 1 - ds.length), P (Sem.Expr.lbl a)) ∧
      (∀ k ∈ kws.take (i + 1 - ds.length - bs.length), P k.lbl) := by
  rcases clsArgs_get hi with ⟨h1, -⟩ | ⟨h1, h2, a, ha, he⟩ | ⟨h1, k, hk', he⟩
  · exact ⟨fun x hx => by rw [show i + 1 - ds.length = 0 by omega] at hx; simp at hx,
      fun x hx => by rw [show i + 1 - ds.length - bs.length = 0 by omega] at hx; simp at hx⟩
  · simp only [Option.some.injEq] at he
    refine ⟨?_, fun x hx => by rw [show i + 1 - ds.length - bs.length = 0 by omega] at hx; simp at hx⟩
    rw [show i + 1 - ds.length = i - ds.length + 1 by omega]
    exact take_step ha hb (hP a (List.mem_of_getElem? ha) he.symm)
  · simp only [Option.some.injEq] at he
    refine ⟨take_full (m := i - ds.length) (by omega) hb, ?_⟩
    rw [show i + 1 - ds.length - bs.length = i - ds.length - bs.length + 1 by omega]
    exact take_step hk' hk (hPk k (List.mem_of_getElem? hk') he.symm)

theorem touchKs_mem {k : Kw} : ∀ {kws : List Kw}, k ∈ kws → (k.lbl, kwVal k) ∈ touchKs kws
  | k0 :: kws, h => by
    rcases List.mem_cons.1 h with rfl | h
    · cases k; simp [touchKs, Kw.lbl, kwVal]
    · have := touchKs_mem h
      cases k0 with
      | mk l x e => simp only [touchKs]; exact List.mem_cons_of_mem _ (List.mem_append_right _ this)

theorem touchKs_val {k : Kw} {x : Label × Expr} : ∀ {kws : List Kw}, k ∈ kws → x ∈ touchE (kwVal k) →
    x ∈ touchKs kws
  | k0 :: kws, h, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · cases k; simp_all [touchKs, kwVal]
    · have := touchKs_val h hx; cases k0; simp [touchKs, this]

section
variable {H : Label → Prop} {s : Sem.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}

/-- The node of a base or keyword whose value is entered is touched (a starred base's and a keyword's
through `touchB p`). -/
theorem touch_item {l : Label} {y : Name} {bs : List Expr} {kws : List Kw} {b : List Stmt} {ds : List Expr}
    (htc : SubL (touchS (.cls l y bs kws b ds)) (touchB p)) {e : Expr} (hs : s.stack = f :: fs) (hc : f.ctrl = .ev e)
    {rest : List (Option Expr)} {acc : List Val} {th : Sem.Then} {K : List (Sem.Kont σ)}
    (hK : f.kont = .evs rest acc th :: K) (hth : ∀ o, th ≠ .op o) :
    (∀ a ∈ bs, unstar a = e → Touch p s (Sem.Expr.lbl a)) ∧ (∀ k ∈ kws, kwVal k = e → Touch p s k.lbl) := by
  have hT : ∀ l', (l', e) ∈ touchB p → Touch p s l' := by
    intro l' h
    refine .inr ?_
    rw [hs]; simp only [TouchF, hc, hK]
    cases th <;> first | exact absurd rfl (hth _) | exact h
  refine ⟨fun a ha he => ?_, fun k hk he => ?_⟩
  · cases a
    case star l0 e0 =>
      simp only [unstar] at he; subst he
      exact hT l0 (htc _ (by simp only [touchS]; exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (touchEs_mem ha (by simp [touchE]))))))
    all_goals
      simp only [unstar] at he; subst he
      exact .inl (by simp [Sem.focus, hs, hc])
  · subst he
    exact hT k.lbl (htc _ (by simp only [touchS]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (touchKs_mem hk)))))

end

theorem itemsKs_mem {C : List Scope} {k : Kw} {x : Item} : ∀ {kws : List Kw}, k ∈ kws → x ∈ itemsE C (kwVal k) →
    x ∈ itemsKs C kws
  | k0 :: kws, h, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · cases k; simp [itemsKs, kwVal] at hx ⊢; exact .inl hx
    · have ih := itemsKs_mem h hx; cases k0; simp only [itemsKs, List.mem_append]; exact .inr ih

theorem mem_trKs {C : List Scope} {k : Kw} : ∀ {kws : List Kw}, k ∈ kws → trE C (kwVal k) ∈ trKs C kws
  | k0 :: kws, h => by
    rcases List.mem_cons.1 h with rfl | h
    · cases k; simp [trKs, kwVal]
    · have ih := mem_trKs (C := C) h; cases k0; simp only [trKs, List.mem_cons]; exact .inr ih

theorem okKs_mem {k : Kw} : ∀ {kws : List Kw}, okKs kws = true → k ∈ kws → okE (kwVal k) = true
  | k0 :: kws, ho, h => by
    cases k0 with
    | mk l0 x0 e0 =>
      simp only [okKs, Bool.and_eq_true] at ho
      rcases List.mem_cons.1 h with rfl | h
      · exact ho.1.2
      · exact okKs_mem ho.2 h

theorem labelsKs_mem {k : Kw} {l : Label} : ∀ {kws : List Kw}, k ∈ kws → l ∈ labelsE (kwVal k) → l ∈ labelsKs kws
  | k0 :: kws, h, hl => by
    rcases List.mem_cons.1 h with rfl | h
    · cases k; simp [labelsKs, kwVal] at hl ⊢; exact .inr (.inl hl)
    · have ih := labelsKs_mem h hl; cases k0; simp only [labelsKs, List.mem_cons, List.mem_append, List.cons_append]
      exact .inr (.inr ih)

theorem nodup_labelsKs {k : Kw} : ∀ {kws : List Kw}, k ∈ kws → (labelsKs kws).Nodup → (labelsE (kwVal k)).Nodup
  | k0 :: kws, h, hn => by
    cases k0 with
    | mk l0 x0 e0 =>
      simp only [labelsKs, List.nodup_cons, List.nodup_append] at hn
      rcases List.mem_cons.1 h with rfl | h
      · exact hn.1.2
      · exact nodup_labelsKs h hn.2.1

theorem labels_unstar {a : Expr} {l : Label} (h : l ∈ labelsE (unstar a)) : l ∈ labelsE a := by
  cases a <;> simp_all [unstar, labelsE]

theorem nodup_unstar {a : Expr} (h : (labelsE a).Nodup) : (labelsE (unstar a)).Nodup := by
  cases a <;> simp_all [unstar, labelsE]

theorem items_unstar {C : List Scope} {a : Expr} {x : Item} (h : x ∈ itemsE C (unstar a)) : x ∈ itemsE C a := by
  cases a <;> simp_all [unstar, itemsE]

/-- An argument item of a class statement is code of `p`. -/
theorem good_item {C : List Scope} {U : Label → Prop} {l : Label} {y : Name} {bs : List Expr} {kws : List Kw}
    {b : List Stmt} {ds : List Expr} (hg : GoodB p C U [.cls l y bs kws b ds]) {e : Expr}
    (he : some e ∈ clsArgs ds bs kws) : GoodE p C U e := by
  have hok := hg.ok
  simp only [okB, okS, Bool.and_eq_true] at hok
  have hfold : ∀ (pe : PE), pe ∈ trEs C ds ++ trA C bs ++ trKs C kws → ∀ x, x ∈ PyCore.itemsE R0 (trChain C) pe →
      x ∈ PyCore.itemsS R0 (trChain C) (trS C (.cls l y bs kws b ds)) := by
    intro pe hpe x hx
    simp only [trS, blk, gad, cc, ccR, recR, PyCore.itemsS, PyCore.itemsB, PyCore.itemsE, PyCore.itemsHs, r0_s, r0_e,
      Option.isSome_none, Bool.false_eq_true, ite_false, List.nil_append, List.append_nil]
    refine List.mem_append_left _ (items_fold _ _ x (.inr ⟨pe, ?_, hx⟩))
    simp only [List.mem_append] at hpe ⊢
    rcases hpe with (h | h) | h <;> simp [h]
  have hnd : ∀ L : List Label, List.Sublist L (labelsS (.cls l y bs kws b ds)) → (labelsB [.cls l y bs kws b ds]).Nodup →
      L.Nodup := by
    intro L hL hn; simp only [labelsB, List.append_nil] at hn; exact hn.sublist hL
  simp only [clsArgs, List.mem_append, List.mem_map, Option.some.injEq] at he
  rcases he with (⟨d, hd, rfl⟩ | ⟨a, ha, rfl⟩) | ⟨k, hk, he⟩
  · refine GoodB.e hg (fun x hx => ?_) (hfold _ (by simp [mem_trEs hd])) (fun _ => okEs_mem hok.1.2 hd)
      (fun x hx => ?_) (fun hn => nodup_labelsEs hd (hnd _ ?_ (by simpa [labelsB] using hn)))
      (fun x hx => by simp [touchS, touchEs_mem hd hx])
    · simp [itemsS, itemsEs_mem hd hx]
    · simp [labelsS, labelsEs_mem hd hx]
    · simp only [labelsS]; exact .cons _ (List.sublist_append_right _ _)
  · refine GoodB.e hg (fun x hx => ?_) (hfold _ (by simp [mem_trA ha])) (fun _ => okAs_mem hok.1.1.1.1.2 ha)
      (fun x hx => ?_) (fun hn => nodup_unstar (nodup_labelsEs ha (hnd _ ?_ (by simpa [labelsB] using hn))))
      (fun x hx => by simp [touchS, touchEs_mem ha (touch_unstar hx)])
    · simp [itemsS, itemsEs_mem ha (items_unstar hx)]
    · simp [labelsS, labelsEs_mem ha (labels_unstar hx)]
    · simp only [labelsS]
      exact .cons _ ((List.sublist_append_left _ _).trans ((List.sublist_append_left _ _).trans
        (List.sublist_append_left _ _)))
  · subst he
    refine GoodB.e hg (fun x hx => ?_) (hfold _ (by simp [mem_trKs hk])) (fun _ => okKs_mem hok.1.1.1.2 hk)
      (fun x hx => ?_) (fun hn => nodup_labelsKs hk (hnd _ ?_ (by simpa [labelsB] using hn)))
      (fun x hx => by simp [touchS, touchKs_val hk hx])
    · simp [itemsS, itemsKs_mem hk hx]
    · simp [labelsS, labelsKs_mem hk hx]
    · simp only [labelsS]
      exact .cons _ ((List.sublist_append_right _ _).trans ((List.sublist_append_left _ _).trans
        (List.sublist_append_left _ _)))

theorem partsR_app {x : Cx} {U : Label → Prop} {l : Label} : ∀ {a c : List (Option Expr)} {b d : List PE},
    PartsR x U l a b → PartsR x U l c d → PartsR x U l (a ++ c) (b ++ d)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, partsR_app h2 h⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem partsR_drop {x : Cx} {U : Label → Prop} {l : Label} : ∀ (n : Nat) {a : List (Option Expr)} {b : List PE},
    PartsR x U l a b → PartsR x U l (a.drop n) (b.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, ⟨_, h⟩ => partsR_drop n h
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

/-- The items of a class statement and their translations. -/
theorem parts_cls {x : Cx} {U : Label → Prop} {l l0 : Label} {y : Name} {bs : List Expr} {kws : List Kw}
    {b : List Stmt} {ds : List Expr} (hg : GoodB x.p x.C U [.cls l0 y bs kws b ds]) :
    PartsR x U l (clsArgs ds bs kws) (trEs x.C ds ++ trA x.C bs ++ trKs x.C kws) := by
  have hge := fun e (he : some e ∈ clsArgs ds bs kws) => good_item hg he
  simp only [clsArgs] at hge ⊢
  refine partsR_app (partsR_app ?_ ?_) ?_
  · have : ∀ es : List Expr, (∀ e ∈ es, GoodE x.p x.C U e) → PartsR x U l (es.map some) (trEs x.C es) := by
      intro es h
      induction es with
      | nil => trivial
      | cons e es ih => exact ⟨⟨h e (by simp), rfl⟩, ih fun e' he => h e' (by simp [he])⟩
    exact this ds fun e he => hge e (by simp [he])
  · have : ∀ es : List Expr, (∀ e ∈ es, GoodE x.p x.C U (unstar e)) →
        PartsR x U l (es.map fun a => some (unstar a)) (trA x.C es) := by
      intro es h
      induction es with
      | nil => trivial
      | cons e es ih =>
        have h1 : PartsR x U l (es.map fun a => some (unstar a)) (trA x.C es) := ih fun e' he => h e' (by simp [he])
        cases e <;> exact ⟨⟨h _ (by simp), rfl⟩, h1⟩
    exact this bs fun a ha => hge _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨a, ha, rfl⟩)))
  · have : ∀ ks : List Kw, (∀ k ∈ ks, GoodE x.p x.C U (kwVal k)) →
        PartsR x U l (ks.map fun k => some (kwVal k)) (trKs x.C ks) := by
      intro ks h
      induction ks with
      | nil => trivial
      | cons k ks ih =>
        have h1 := ih fun k' hk => h k' (by simp [hk])
        cases k with
        | mk lk xk ek => exact ⟨⟨h _ (by simp), rfl⟩, h1⟩
    exact this kws fun k hk => hge _ (List.mem_append_right _ (List.mem_map.2 ⟨k, hk, rfl⟩))

theorem drop_cons {α} {l : List α} {n : Nat} {a : α} {r : List α} (h : l.drop n = a :: r) :
    l[n]? = some a ∧ r = l.drop (n + 1) := by
  refine ⟨?_, ?_⟩
  · have := congrArg (·[0]?) h; simpa using this
  · have := congrArg List.tail h; simp [List.tail_drop] at this; exact this.symm

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore adds a value to an argument record. -/
theorem pstep_rec (ht : t.stack = f' :: fs') {v : Val} {done : List Val} {K1 : List (PyCore.Kont σ)}
    (hc' : f'.ctrl = .val v) (hK' : f'.kont = .binR "," (.data "$args" done) :: K1) :
    PyCore.step I t = some { t with stack := { f' with ctrl := .val (.data "$args" (done ++ [v])), kont := K1 } :: fs' } := by
  simp [PyCore.step, ht, hc', hK', PyCore.valStep, PyCore.top]

/-- A value reaches the arguments of a class statement: the next one, or (the last) `$cls`'s phases. -/
theorem val_evsCls_of (mk : EvsMkC σ) (ms : StarMkC σ) (mw : KwMkC σ) (A : At p H s t f fs f' fs')
    {U : Label → Prop} {v : Val} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v) {l : Label} {y : Name}
    {bs : List Expr} {kws : List Kw} {b : List Stmt} {ds : List Expr} {ss : List Stmt} {rest : List (Option Expr)}
    {acc : List Val} {ps : List PE} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hK : f.kont = .evs rest acc (.cls l y b ds.length (bs.map isStar) (kws.map kwName)) :: .seq ss :: K)
    (hK' : f'.kont = recK acc.reverse (ps ++ bs.map starMark ++ kws.map kwMark)
      (.callA (.prim (Gadget.cls ds.length).name) :: .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] ::
        .seq (trB f.chain ss) :: K'))
    (hH : H l) (hg : GoodB p f.chain U [.cls l y bs kws b ds]) (htc : SubL (touchS (.cls l y bs kws b ds)) (touchB p))
    (hy : ¬ Dot (mangle (priv f.chain) y))
    (hlt : acc.length < (clsArgs ds bs kws).length) (hrest : rest = (clsArgs ds bs kws).drop (acc.length + 1))
    (hbs : ∀ a ∈ bs.take (acc.length + 1 - ds.length), H (Sem.Expr.lbl a))
    (hkw : ∀ k ∈ kws.take (acc.length + 1 - ds.length - bs.length), H k.lbl)
    (hps : PartsR A.x U l rest ps) (hnc : ss ≠ [] → NoCompH f.chain) (hgs : GoodB p f.chain U ss)
    (hk : KRel A.x U false K K') : Goal I p H s t := by
  let th : Sem.Then := .cls l y b ds.length (bs.map isStar) (kws.map kwName)
  let ks' : List (PyCore.Kont σ) := .exprS :: .seq [clsS f.chain l y b] :: .tryE [] [] :: .seq (trB f.chain ss) :: K'
  let marks : List PE := bs.map starMark ++ kws.map kwMark
  have hft : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  cases rest with
  | nil =>
    obtain rfl : ps = [] := by cases ps; rfl; exact hps.elim
    have hlen : acc.length + 1 = (clsArgs ds bs kws).length := by
      have := congrArg List.length hrest; simp at this; omega
    rw [clsArgs_len] at hlen
    let vs := acc.reverse ++ [v]
    have hvl : vs.length = ds.length + bs.length + kws.length := by simp [vs]; omega
    let s1 : Sem.Config σ := { s with stack := { f with ctrl := .val (.tuple vs), kont := .evsEnd th :: .seq ss :: K } :: fs }
    have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC, s1, vs, th]
    -- PyCore: the value into the record, then the markers
    have e2 := pstep_rec (I := I) (done := acc.reverse)
      (K1 := marks.map (.binL ",") ++ .callA (.prim (Gadget.cls ds.length).name) :: ks') A.ht hc'
      (by rw [hK']; simp [recK, marks, ks'])
    obtain ⟨ys, py, hfo⟩ := rec_consts (I := I) t f' fs' marks (acc.reverse ++ [v]) (.callA (.prim (Gadget.cls ds.length).name) :: ks')
      (fun m hm => by
        simp only [marks, List.mem_append, List.mem_map] at hm
        rcases hm with ⟨a, -, rfl⟩ | ⟨k, -, rfl⟩
        · cases a <;> first | exact ⟨_, _, rfl, kc_pos I⟩ | exact ⟨_, _, rfl, kc_star I⟩
        · cases k; exact ⟨_, _, rfl, kc_kw I _⟩)
    have hsplit : (Py.pairs ((vs ++ marks.map pval).drop ds.length)).bind Py.splitArgs =
        some (bs.map isStar, (vs.drop ds.length).take bs.length, kws.map kwName, vs.drop (ds.length + bs.length)) := by
      rw [List.drop_append_of_le_length (by omega)]
      have e : vs.drop ds.length = (vs.drop ds.length).take bs.length ++ vs.drop (ds.length + bs.length) := by
        rw [← List.drop_drop, List.take_append_drop]
      have hs := split_cls bs kws ((vs.drop ds.length).take bs.length) (vs.drop (ds.length + bs.length))
        (by simp only [List.length_take, List.length_drop]; omega) (by simp only [List.length_drop]; omega)
      rw [← e] at hs
      exact hs
    have htake : (vs ++ marks.map pval).take ds.length = vs.take ds.length := List.take_append_of_le_length (by omega)
    refine star_goal ms mw A hg hy hnc hgs hk (vs.take ds.length) ((vs.drop ds.length).take bs.length) (bs.map isStar)
      (kws.map kwName) (vs.drop (ds.length + bs.length)) (esub_cons hK)
      (esub_tail (fun _ _ _ h => by cases h) (esub_cons hK)) (.cons e1 (.nil s1)) ?_ (.inl hH)
      (.cons e2 py) ?_ (by simp [PyCore.focus]) ?_
    · simp [s1, Sem.step, Sem.valStep, Sem.finish, th]
    · simp only [vs] at hsplit htake
      simp only [PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, gad_name (Gadget.cls ds.length) trivial,
        PyCore.gadgetStep, hsplit, htake, ks']
      rfl
    · intro z hz x hx
      have hx := pfocus_le hx
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · rw [hft] at hx; cases hx
      · obtain ⟨m, hm, rfl⟩ := hfo z hz x hx
        refine .inl ?_
        simp only [marks, List.mem_append, List.mem_map] at hm
        rcases hm with ⟨a, ha, rfl⟩ | ⟨k, hk, rfl⟩
        · have h1 : (starMark a).label / 64 = Sem.Expr.lbl a := by
            rw [lbl_eq]; cases a <;> simp [starMark, PyCore.Expr.label, Expr.label, sub_div]
          rw [h1]; exact hbs a (by rw [List.take_of_length_le (by omega)]; exact ha)
        · have h1 : (kwMark k).label / 64 = k.lbl := by cases k; simp [kwMark, PyCore.Expr.label, Kw.lbl, sub_div]
          rw [h1]; exact hkw k (by rw [List.take_of_length_le (by omega)]; exact hk)
  | cons o rest' =>
    obtain ⟨hget, hrest'⟩ := drop_cons hrest.symm
    have hlt' : acc.length + 1 < (clsArgs ds bs kws).length := by
      rcases Nat.lt_or_ge (acc.length + 1) (clsArgs ds bs kws).length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hget; cases hget
    obtain ⟨e0, rfl⟩ : ∃ e0, o = some e0 := by
      rcases clsArgs_get hget with ⟨-, d, -, h⟩ | ⟨-, -, a, -, h⟩ | ⟨-, k, -, h⟩ <;> exact ⟨_, h⟩
    obtain ⟨pe, ps', rfl⟩ : ∃ pe ps', ps = pe :: ps' := by
      cases ps
      · exact hps.elim
      · exact ⟨_, _, rfl⟩
    obtain ⟨⟨hge, rfl⟩, hps'⟩ := hps
    let s1 : Sem.Config σ := { s with stack := { f with ctrl := .ev e0, kont := .evs rest' (v :: acc) th :: .seq ss :: K } :: fs }
    have e1 : Sem.step I s = some s1 := by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.startEvs, Sem.setC, s1, th]
    let H' := Seen (Touch p) H [s1, s]
    have hHH : ∀ l, H l → H' l := fun _ h => .inl h
    have hT1 : ∀ l', Touch p s1 l' → H' l' := fun l' h => .inr ⟨s1, by simp, h⟩
    obtain ⟨hTb, hTk⟩ := touch_item (p := p) htc (s := s1)
      (f := { f with ctrl := .ev e0, kont := .evs rest' (v :: acc) th :: .seq ss :: K }) (fs := fs) rfl rfl rfl
      (fun o h => Sem.Then.noConfusion h)
    obtain ⟨hbs', hkw'⟩ := touch_next (P := H') hget (fun a ha he => hT1 _ (hTb a ha he))
      (fun k hk he => hT1 _ (hTk k hk he)) (fun a ha => hHH _ (hbs a ha)) (fun k hk => hHH _ (hkw k hk))
    have e2 := pstep_rec (I := I) (done := acc.reverse)
      (K1 := ((trE f.chain e0 :: ps') ++ bs.map starMark ++ kws.map kwMark).map (.binL ",") ++
        .callA (.prim (Gadget.cls ds.length).name) :: ks')
      A.ht hc' (by rw [hK']; rfl)
    let t2 : PyCore.Config σ := { t with stack := { f' with
      ctrl := .ev (trE f.chain e0),
      kont := recK (v :: acc).reverse (ps' ++ bs.map starMark ++ kws.map kwMark)
        (.callA (.prim (Gadget.cls ds.length).name) :: ks') } :: fs' }
    have e3 : PyCore.step I { t with stack := { f' with
        ctrl := .val (.data "$args" (acc.reverse ++ [v])),
        kont := ((trE f.chain e0 :: ps') ++ bs.map starMark ++ kws.map kwMark).map (.binL ",") ++
          .callA (.prim (Gadget.cls ds.length).name) :: ks' } :: fs' } = some t2 := by
      simp [PyCore.step, PyCore.valStep, PyCore.top, t2, recK]
    have A' := A.mono hHH
    have hr := A'.set (c := .ev e0) (c' := .ev (trE f.chain e0)) (k := .evs rest' (v :: acc) th :: .seq ss :: K)
      (k' := recK (v :: acc).reverse (ps' ++ bs.map starMark ++ kws.map kwMark)
        (.callA (.prim (Gadget.cls ds.length).name) :: ks')) (.ev hge)
      (mk (hHH _ hH) hg hy hlt' hrest' hbs' hkw' (partsR_with hps') hnc hgs (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hk))
    refine goal_t (.cons e1 (.nil s1)) (by simp) (.cons e2 (.cons e3 (.nil t2))) (by simp) (.inl hr)
      (cover_none fun z hz => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact hft
    · simp [PyCore.focus]

/-- A class statement: its first argument item, or (none) `$cls`'s phases. -/
theorem exec_cls_of (mk : EvsMkC σ) (ms : StarMkC σ) (mw : KwMkC σ)
    (htc : ∀ {C : List Scope} {U : Label → Prop} {st : Stmt} {ss : List Stmt}, GoodB p C U (st :: ss) →
      SubL (touchS st) (touchB p)) (l : Label) (x : Name) (bs : List Expr) (ks : List Kw) (b : List Stmt)
    (ds : List Expr) : ExecCase I p (.cls l x bs ks b ds) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have hg1 : GoodB p f.chain U [.cls l x bs ks b ds] :=
    GoodB.b hg (fun y hy => by simpa [itemsB] using hy) (fun y hy => by simpa [trB, PyCore.itemsB] using hy)
      (fun h => by simp [okB, h]) (fun y hy => by simpa [labelsB] using hy) (fun h => by simpa [labelsB] using h)
      (fun y hy => by simpa [touchB] using hy)
  have hy : ¬ Dot (mangle (priv f.chain) x) := W.nodot l _ f.chain (hg.s _ (by simp [itemsB, itemsS]))
  have hnc1 : ss ≠ [] → NoCompH f.chain := fun _ => hnc (by simp)
  have hgs := hg.tail
  let C := f.chain
  let th : Sem.Then := .cls l x b ds.length (bs.map isStar) (ks.map kwName)
  let ks' : List (PyCore.Kont σ) := .exprS :: .seq [clsS C l x b] :: .tryE [] [] :: .seq (trB C ss) :: f'.kont
  let pargs : List PE := trEs C ds ++ trA C bs ++ trKs C ks
  let g := (Gadget.cls ds.length).name
  let r := sub l 3
  have hsl : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Stmt.lbl])
  have e0 : Sem.step I s = Sem.startEvs s f fs (clsArgs ds bs ks) [] th (.seq ss :: f.kont) := by
    simp only [Sem.step, A.hs, hc, Sem.execStep]
    congr 1
    simp only [clsArgs]; congr 1; exact List.map_congr_left (fun k _ => by cases k; rfl)
  let mkT (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) : PyCore.Config σ := { t with stack := { f' with ctrl := c, kont := k } :: fs' }
  let c1 := mkT (.exec [.expr (sub l 2) (ccR r g (pargs ++ bs.map starMark ++ ks.map kwMark)), clsS C l x b])
    (.tryE [] [] :: .seq (trB C ss) :: f'.kont)
  let c2 := mkT (.ev (ccR r g (pargs ++ bs.map starMark ++ ks.map kwMark))) ks'
  have ea : PyCore.step I t = some c1 := by
    simp [PyCore.step, A.ht, hc', trB, trS, blk, PyCore.execStep, PyCore.top, clsS, c1, mkT, gad, cc, r, g, pargs, C]
  have eb : PyCore.step I c1 = some c2 := by simp [c1, c2, mkT, PyCore.step, PyCore.execStep, PyCore.top, ks', C]
  have hfoc12 : ∀ z ∈ [t, c1, c2], ∀ y, PyCore.focus z = some y → y / 64 = l := by
    intro z hz y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hy; rw [← hy]; exact sub_div _ _ (by omega)
    · simp [PyCore.focus, c1, mkT, PyCore.Stmt.label] at hy; rw [← hy]; exact sub_div _ _ (by omega)
    · simp [PyCore.focus, c2, mkT, ccR, PyCore.Expr.label, r] at hy; rw [← hy]; exact sub_div _ _ (by omega)
  cases hca : clsArgs ds bs ks with
  | nil =>
    have hl : ds.length + bs.length + ks.length = 0 := by rw [← clsArgs_len, hca]; rfl
    have hds : ds = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hks : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hds hbs hks
    let s1 : Sem.Config σ := { s with stack := { f with ctrl := .val (.tuple []), kont := .evsEnd th :: .seq ss :: f.kont } :: fs }
    have e1 : Sem.step I s = some s1 := by rw [e0, hca]; simp [Sem.startEvs, Sem.setC, s1]
    have p2 : Path (PyCore.step I) c2 (mkT (.val (.data "$args" [])) (.callA (.prim g) :: ks'))
        [c2, mkT (.ev (.const r g)) (.callF (.const r "$args") :: ks'), mkT (.val (.prim g)) (.callF (.const r "$args") :: ks'),
          mkT (.ev (.const r "$args")) (.callA (.prim g) :: ks')] := by
      refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _))))
      · simp [c2, mkT, ccR, recR, pargs, trEs, trA, trKs, PyCore.step, PyCore.evalStep, PyCore.top]
      · simp [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, g, kc_gad I (Gadget.cls 0) trivial]
      · simp [mkT, PyCore.step, PyCore.valStep, PyCore.top]
      · simp [mkT, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
    refine star_goal ms mw A hg1 hy hnc1 hgs hk [] [] [] [] [] (esub_tail (fun _ _ _ h => by cases h) esub_refl)
      (esub_tail (fun _ _ _ h => by cases h) (esub_tail (fun _ _ _ h => by cases h) esub_refl)) (.cons e1 (.nil s1)) ?_
      (.inr ⟨s, by simp, hsl⟩) (.cons ea (.cons eb p2)) ?_ (by simp [PyCore.focus, mkT]) ?_
    · simp [s1, Sem.step, Sem.valStep, Sem.finish, th]
    · simp [mkT, PyCore.step, PyCore.valStep, PyCore.callStep, PyCore.argList, g, gad_name (Gadget.cls 0) trivial,
        PyCore.gadgetStep, Py.pairs, Py.splitArgs]
      rfl
    · intro z hz y hy
      have hy := pfocus_le hy
      refine .inr ⟨s, by simp, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hfoc12 _ (by simp) y hy]; exact hsl
      · rw [hfoc12 _ (by simp) y hy]; exact hsl
      · rw [hfoc12 _ (by simp) y hy]; exact hsl
      all_goals simp [mkT, PyCore.focus, PyCore.Expr.label, r] at hy
      all_goals rw [← hy, sub_div _ _ (by omega)]; exact hsl
  | cons o rest =>
    have hget : (clsArgs ds bs ks)[0]? = some o := by rw [hca]; rfl
    obtain ⟨e0', rfl⟩ : ∃ e0', o = some e0' := by
      rcases clsArgs_get hget with ⟨-, d, -, h⟩ | ⟨-, -, a, -, h⟩ | ⟨-, k, -, h⟩ <;> exact ⟨_, h⟩
    have hps := parts_cls (x := A.x) (l := l) hg1
    rw [hca] at hps
    obtain ⟨pe, ps0, hpa⟩ : ∃ pe ps0, pargs = pe :: ps0 := by
      cases hp : pargs with
      | nil => simp only [pargs] at hp; rw [hp] at hps; exact hps.elim
      | cons pe ps0 => exact ⟨pe, ps0, rfl⟩
    simp only [pargs] at hpa
    rw [hpa] at hps
    obtain ⟨⟨hge, rfl⟩, hps0⟩ := hps
    let s1 : Sem.Config σ := { s with stack := { f with ctrl := .ev e0', kont := .evs rest [] th :: .seq ss :: f.kont } :: fs }
    have e1 : Sem.step I s = some s1 := by rw [e0, hca]; simp [Sem.startEvs, Sem.setC, s1]
    let H' := Seen (Touch p) H [s1, s]
    have hHH : ∀ l, H l → H' l := fun _ h => .inl h
    have hT1 : ∀ l', Touch p s1 l' → H' l' := fun l' h => .inr ⟨s1, by simp, h⟩
    obtain ⟨hTb, hTk⟩ := touch_item (p := p) (htc hg) (s := s1)
      (f := { f with ctrl := .ev e0', kont := .evs rest [] th :: .seq ss :: f.kont }) (fs := fs) rfl rfl rfl
      (fun o h => Sem.Then.noConfusion h)
    obtain ⟨hbs', hkw'⟩ := touch_next (P := H') hget (fun a ha he => hT1 _ (hTb a ha he))
      (fun k hk he => hT1 _ (hTk k hk he)) (fun a ha => by simp at ha) (fun k hk => by simp at hk)
    obtain ⟨ys, pc, hys, hfo⟩ := cc_enter (I := I) t f' fs' r g (trE C e0') (ps0 ++ bs.map starMark ++ ks.map kwMark) ks'
    have hc2 : c2 = mkT (.ev (ccR r g (trE C e0' :: (ps0 ++ bs.map starMark ++ ks.map kwMark)))) ks' := by
      simp only [c2, pargs, hpa]; rfl
    have hkg : Py.constVal I g = .prim g := kc_gad I (Gadget.cls ds.length) trivial
    replace pc : Path (PyCore.step I) c2 (mkT (.ev (trE C e0'))
        (recK [] (ps0 ++ bs.map starMark ++ ks.map kwMark) (.callA (.prim g) :: ks'))) ys := by
      rw [hc2, ← hkg]; exact pc
    have A' := A.mono hHH
    have hlt0 : ([] : List Val).length < (clsArgs ds bs ks).length := by rw [hca]; simp
    have hr := A'.set (c := .ev e0') (c' := .ev (trE C e0')) (k := .evs rest [] th :: .seq ss :: f.kont)
      (k' := recK [] (ps0 ++ bs.map starMark ++ ks.map kwMark) (.callA (.prim g) :: ks')) (.ev hge)
      (mk (.inr ⟨s, by simp, hsl⟩) hg1 hy hlt0 (by rw [hca]; rfl) hbs' hkw' (partsR_with hps0) hnc1 hgs
        (KRel.ext ⟨hHH, Agree.refl _ _ _⟩ hk))
    refine goal_t (.cons e1 (.nil s1)) (by simp) (.cons ea (.cons eb pc)) (by simp) (.inl hr) ?_
    intro z hz y hy
    have hy := pfocus_le hy
    refine .inr ⟨s, by simp, ?_⟩
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | hz
    · rw [hfoc12 _ (by simp) y hy]; exact hsl
    · rw [hfoc12 _ (by simp) y hy]; exact hsl
    · rw [hfo z hz y hy, sub_div _ _ (by omega)]; exact hsl

end

end Cls

open Cls

/-- The first step from the initial configurations: PyCore runs `setupS 0` up to the operation
Surf's module frame starts with, both perform it. -/
theorem init_sim {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} (W : WF p) (h : InitRel p s t) :
    Goal I p H s t := by
  obtain ⟨σ0, s0, rfl, rfl⟩ := h
  let t0 : PyCore.Config σ := PyCore.init (tr p) (fun x => σ0[x]?) s0
  let g0 : PyCore.Frame σ := PyCore.modFrame (tr p)
  let K1 : List (PyCore.Kont σ) := recK [] [] (.callA (.prim Gadget.setup.name) :: .exprS :: .seq (trB [] p) :: [])
  let g1 : PyCore.Frame σ := { g0 with ctrl := (.op (.display (.dict [])) []), kont := K1 }
  let t1 : PyCore.Config σ := { t0 with stack := [g1] }
  let f0 : Sem.Frame σ := Sem.modFrame p
  obtain ⟨ys, pc, -, hfoc⟩ := setup_path (I := I) t0 g0 [] 0 (trB [] p) []
  have e0 : ({ t0 with stack := [{ g0 with ctrl := .exec (setupS 0 :: trB [] p), kont := [] }] } : PyCore.Config σ) = t0 := rfl
  rw [e0] at pc
  have hk : KRel (cx p H (rdOf t1 g1) (ownOf t1 g1) f0) UAll true f0.kont g1.kont :=
    .cls (.setAnn (.core (.seq (pre := []) (fun _ => trivial) (.inl rfl) (goodB_p W) .nil)))
  have hf : FRel p H (rdOf t1 g1) (ownOf t1 g1) f0 g1 :=
    ⟨⟨rfl, rfl, (by funext x; rfl), (by funext x; rfl), rfl, trivial, fun _ _ => rfl, fun _ _ h => (by cases h), rfl,
      trivial⟩, fun _ _ h => (by cases h), UAll, true, .op, hk⟩
  have ids : Ids t1 := by
    refine ⟨by simp [t1, g1, g0, PyCore.modFrame], fun g hg => ?_, fun o b hb => ?_, fun o g ho => ?_, fun g hg o hk => ?_,
      fun g hg _ => ?_, fun o g ho => ?_⟩
    · simp [t1] at hg; subst hg; exact Nat.zero_lt_one
    · simp [pObj, t1, t0, PyCore.init] at hb
    · simp [pObj, t1, t0, PyCore.init] at ho
    · simp [t1] at hg; subst hg; simp [g1, g0, PyCore.modFrame] at hk
    · simp [t1] at hg; subst hg; rfl
    · simp [pObj, t1, t0, PyCore.init] at ho
  have r : CRel p H (Sem.init p σ0 s0) t1 :=
    ⟨⟨hf, trivial⟩, fun o => by simp [sObj, pObj, t1, t0, Sem.init, PyCore.init, PyCore.OptRel],
      fun a _ => by simp [pCell, sCell, t1, t0, Sem.init, PyCore.init],
      fun x _ => by simp [pGlob, sGlob, t1, t0, Sem.init, PyCore.init, PyCore.Config.glob],
      rfl, rfl, rfl, rfl, fun g hg => by simp [Sem.init] at hg, ids,
      ⟨fun g hg o b kx hm => by
        simp only [Sem.init, List.mem_singleton] at hg; subst hg; simp [Sem.modFrame] at hm,
       fun o g ho => by simp [Sem.init] at ho⟩⟩
  have A : At p H (Sem.init p σ0 s0) t1 f0 [] g1 [] := ⟨r, rfl, rfl, hf⟩
  refine handle_simP A (I.op s0 (.display (.dict [])) []) hk ?_ ?_ (by simp [PyCore.focus, t1, g1]) pc ?_
  · simp [Sem.step, Sem.init, f0, Sem.modFrame, Sem.opStep]
  · simp [PyCore.step, t1, g1, t0, PyCore.init]
  · intro y hy
    cases hy' : PyCore.focus y with
    | none => simp [pfocus, hy']
    | some x =>
      have h64 : ¬ 64 ≤ x := Nat.not_le_of_lt (Nat.lt_of_div_eq_zero (by decide) (hfoc y hy x hy'))
      simp [pfocus, hy', h64]

theorem sig_cls {i : Bool} : KCase I p i ClsK CSig := by
  intro H s t f fs f' fs' U A W hc hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | clsEnd hy k =>
    refine sig_popK A hc (fun _ => rfl) (pre := [_, _]) (by rw [hK']; rfl) (by simp [PlainK]) (by simp) ?_ k
      (esub_cons hK)
    rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ <;>
      simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC]
  | setAnn k =>
    refine sig_popK A hc (fun h => by cases h) (pre := [_, _, _]) (by rw [hK']; rfl) (by simp [PlainK]) (by simp) ?_ k
      (esub_cons hK)
    rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨h0, -, -, -⟩ | ⟨h0, -, -, -⟩
    · simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.setC]
    · simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.setC]
    · cases h0
    · cases h0
  | @evsCls _ Kr Kr' l y bs kws b ds ss rest acc ps _ _ _ _ _ _ _ _ hnc hgs k =>
    refine sig_popK A hc (fun h => by cases h)
      (pre := .binR "," (.data "$args" acc.reverse) :: (ps ++ bs.map starMark ++ kws.map kwMark).map (.binL ",") ++
        [.callA (.prim (Gadget.cls ds.length).name), .exprS, .seq [clsS f.chain l y b], .tryE [] []])
      (K0' := .seq (trB f.chain ss) :: Kr')
      (by rw [hK']; simp [recK]) ?_ (by simp) ?_ (.core (.seq (pre := []) hnc (.inl rfl) hgs k)) (esub_cons hK)
    · intro k hk
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at hk
      rcases hk with rfl | ⟨_, _, rfl⟩ | rfl | rfl | rfl | rfl | hk <;> first | trivial | simp at hk
    · rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨h0, -, -, -⟩ | ⟨h0, -, -, -⟩
      · simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.setC]
      · simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.setC]
      · cases h0
      · cases h0
  | @argStarC _ Kr Kr' l y bs kws0 b ds ss _ _ _ _ _ _ hnc hgs k =>
    refine sig_popK A hc (fun h => by cases h) (pre := [_, _, _, _]) (K0' := .seq (trB f.chain ss) :: Kr')
      (by rw [hK']; rfl) (by simp [PlainK]) (by simp) ?_ (.core (.seq (pre := []) hnc (.inl rfl) hgs k)) (esub_cons hK)
    rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨h0, -, -, -⟩ | ⟨h0, -, -, -⟩
    · simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.setC]
    · simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.setC]
    · cases h0
    · cases h0
  | @argKwC _ Kr Kr' l y bs kws0 b ds ss _ _ _ _ _ hnc hgs k =>
    refine sig_popK A hc (fun h => by cases h) (pre := [_, _, _, _]) (K0' := .seq (trB f.chain ss) :: Kr')
      (by rw [hK']; rfl) (by simp [PlainK]) (by simp) ?_ (.core (.seq (pre := []) hnc (.inl rfl) hgs k)) (esub_cons hK)
    rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨h0, -, -, -⟩ | ⟨h0, -, -, -⟩
    · simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.setC]
    · simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.setC]
    · cases h0
    · cases h0

/-- The class body's namespace reaches the class statement: `mkClass`, the decorators next. -/
theorem ns_cls {i : Bool} : KCase I p i ClsK CNs := by
  intro H s t f fs f' fs' U A W ⟨ns, hc, hc'⟩ hk
  have hcov := cov_none A (by simp [PyCore.focus, A.ht, hc'])
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @clsEnd _ K0 K0' y q bs kws ds hy k =>
    exact A.go11 (c := .op (.mkClass y q (kws.map (·.1)) (ns.map (·.1))) (bs ++ kws.map (·.2) ++ ns.map (·.2)))
      (c' := .op (.mkClass y q (kws.map (·.1)) (ns.map (·.1))) (bs ++ kws.map (·.2) ++ ns.map (·.2)))
      (k := .decos ds.reverse :: .assignN y :: K0) (k' := .decos ds.reverse :: .assign y :: K0')
      (by simp [Sem.step, A.hs, hc, hK, Sem.nsStep, Sem.doOp, Sem.setC])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.nsStep, PyCore.top])
      .op (.core (.decos (.core (.assignN hy k)))) hcov
  | setAnn k =>
    exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.nsStep])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.nsStep, recK]) hcov
  | evsCls _ _ _ _ _ _ k =>
    exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.nsStep])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.nsStep, recK]) hcov
  | argStarC _ _ _ k =>
    exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.nsStep])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.nsStep]) hcov
  | argKwC _ _ _ k =>
    exact fin_stuck A (by simp [Sem.step, A.hs, hc, hK, Sem.nsStep])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.nsStep]) hcov

theorem clsArgs_eq (ds bs : List Expr) (kws : List Kw) : clsArgs ds bs kws = partsCls ds bs kws := by
  simp only [clsArgs, partsCls]; congr 1; exact List.map_congr_left (fun k _ => by cases k; rfl)

theorem evsMk : EvsMkC σ := by
  intro x U K K' l y bs kws b ds ss rest acc ps hl hg hy hlt hr hb hk hp hn hgs hK
  rw [clsArgs_eq] at hlt hr
  exact .cls (.evsCls hl hg hy hlt hr hb hk hp hn hgs hK)

theorem starMk : StarMkC σ := fun hl hg hy hn hgs hK => .cls (.argStarC hl hg hy hn hgs hK)

theorem kwMk : KwMkC σ := fun hl hg hy hn hgs hK => .cls (.argKwC hl hg hy hn hgs hK)

theorem exec_cls (l x bs ks b ds) : ExecCase I p (.cls l x bs ks b ds) :=
  exec_cls_of evsMk starMk kwMk (fun hg y hy => hg.tch y (by simp [touchB, hy])) l x bs ks b ds

theorem val_cls : KCase I p true ClsK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | setAnn k => exact val_setAnn A hc hc' hK hK' k
  | evsCls hl hg hy hlt hr hb hkw hps hnc hgs k =>
    exact val_evsCls_of evsMk starMk kwMk A hc hc' hK hK' hl hg (fun z hz => hg.tch z (by simp [touchB, hz])) hy
      (by rw [clsArgs_eq]; exact hlt) (by rw [clsArgs_eq]; exact hr) hb hkw hps hnc hgs k
  | argStarC hl hg hy hnc hgs k => exact val_argStarC_of kwMk A hc hc' hK hK' hl hg hy hnc hgs k
  | argKwC hl hg hy hnc hgs k => exact val_argKwC_of A hc hc' hK hK' hl hg hy hnc hgs k

end Surf.T2
