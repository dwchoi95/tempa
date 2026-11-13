/-
(T2): the translation keeps outcomes, and the reach correspondence; with them, the footprint
theorem on Surf runs.

`step_sim` is the simulation step from related configurations, by cases on the top frame's
control and on the family of its continuation's top item; each case is a lemma of `T2Cases.lean`
(the constructs the translation maps to PyCore's own) or of one file per group of constructs
(`T2Call`, `T2Class`, `T2Comp`, `T2Loop`, `T2Assign`, `T2Access`, `T2Misc`). The generic
stuttering simulation (`T2Sim.lean`) turns it into termination with corresponding outcomes and
divergence, both ways, and into the reach correspondence.
-/
import Surf.T2Call
import Surf.T2Class
import Surf.T2Comp
import Surf.T2Loop
import Surf.T2Assign
import Surf.T2Access
import Surf.T2Misc

namespace Surf.T2
open PyCore (Name Label)
open Py (Val)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

theorem ev_sim : ∀ e, EvCase I p e
  | .const l k => ev_const l k
  | .name l x => ev_name l x
  | .bin l op a b => ev_bin l op a b
  | .unary l op a => ev_unary l op a
  | .boolop l op es => ev_boolop l op es
  | .compare l a ops es => ev_compare l a ops es
  | .ifexp l c a b => ev_ifexp l c a b
  | .call l g args kws => ev_call l g args kws
  | .attr l e a => ev_attr l e a
  | .sub l e i => ev_sub l e i
  | .slice l a b c => ev_slice l a b c
  | .star l e => ev_star l e
  | .list l es => ev_list l es
  | .tuple l es => ev_tuple l es
  | .set l es => ev_set l es
  | .dict l kvs => ev_dict l kvs
  | .lam l ps b => ev_lam l ps b
  | .comp l k es gs => ev_comp l k es gs
  | .walrus l x e => ev_walrus l x e
  | .yield l none => ev_yield_none l
  | .yield l (some e) => ev_yield l e
  | .yieldFrom l e => ev_yieldFrom l e
  | .fstr l es => ev_fstr l es
  | .fmt l e c s => ev_fmt l e c s

theorem exec_sim : ∀ st, ExecCase I p st
  | .expr l e => exec_expr l e
  | .assign l ts e => exec_assign l ts e
  | .augassign l tg op e => exec_augassign l tg op e
  | .annassign l tg a v => exec_annassign l tg a v
  | .del l ts => exec_del l ts
  | .ite l c tb ub => exec_ite l c tb ub
  | .while l c b u => exec_while l c b u
  | .for l tg it b u => exec_for l tg it b u
  | .brk l => exec_brk l
  | .cont l => exec_cont l
  | .pass l => exec_pass l
  | .ret l none => exec_ret_none l
  | .ret l (some e) => exec_ret l e
  | .defn l g ps b ds r => exec_defn l g ps b ds r
  | .cls l x bs ks b ds => exec_cls l x bs ks b ds
  | .glob l xs => exec_glob l xs
  | .nonloc l xs => exec_nonloc l xs
  | .tryE l b hs u => exec_tryE l b hs u
  | .raise l e c => exec_raise l e c
  | .imp l al => exec_imp l al
  | .impFrom l m al lvl => exec_impFrom l m al lvl
  | .assert l tg m => exec_assert l tg m

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem val_sim {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) {v : Val} (hc : f.ctrl = .val v)
    (hc' : f'.ctrl = .val v) (hk : KRel A.x U true f.kont f'.kont) : Goal I p H s t := by
  have hv : CVal true f.chain U f.ctrl f'.ctrl := ⟨v, hc, hc'⟩
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | core k => exact val_core A W hv (by rw [hK, hK']; exact k)
  | call k => exact val_call A W hv (by rw [hK, hK']; exact k)
  | cls k => exact val_cls A W hv (by rw [hK, hK']; exact k)
  | comp k => exact val_comp A W hv (by rw [hK, hK']; exact k)
  | loop k => exact val_loop A W hv (by rw [hK, hK']; exact k)
  | asg k => exact val_asg A W hv (by rw [hK, hK']; exact k)
  | acc k => exact val_acc A W hv (by rw [hK, hK']; exact k)
  | misc k => exact val_misc A W hv (by rw [hK, hK']; exact k)

theorem done_sim {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) (hc : f.ctrl = .exec [])
    (hc' : f'.ctrl = .exec []) (hk : KRel A.x U false f.kont f'.kont) : Goal I p H s t := by
  have hd : CDone false f.chain U f.ctrl f'.ctrl := ⟨hc, hc'⟩
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | nil => exact done_nil A W hc hc' hK hK'
  | core k => exact done_core A W hd (by rw [hK, hK']; exact k)
  | call k => cases k
  | cls k =>
    cases k
    exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.doneStep, hK]) (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hK'])
      (cov_none A (by simp [PyCore.focus, A.ht, hc']))
  | comp k => exact done_comp A W hd (by rw [hK, hK']; exact k)
  | loop k => exact done_loop A W hd (by rw [hK, hK']; exact k)
  | asg k => exact done_asg A W hd (by rw [hK, hK']; exact k)
  | acc k => cases k
  | misc k => exact done_misc A W hd (by rw [hK, hK']; exact k)

theorem sig_sim {U : Label → Prop} {i : Bool} (A : At p H s t f fs f' fs') (W : WF p)
    (hc : CSig i f.chain U f.ctrl f'.ctrl) (hb : (∃ v, f.ctrl = .raise v) → ¬ BareAt A.x U i f.kont f'.kont)
    (hk : KRel A.x U i f.kont f'.kont) : Goal I p H s t := by
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | nil => exact sig_nil A W hc hK hK'
  | core k => exact sig_core A W hc hb (by rw [hK, hK']; exact k)
  | call k => exact sig_call A W hc (by rw [hK, hK']; exact k)
  | cls k => exact sig_cls A W hc (by rw [hK, hK']; exact k)
  | comp k => exact sig_comp A W hc (by rw [hK, hK']; exact k)
  | loop k => exact sig_loop A W hc (by rw [hK, hK']; exact k)
  | asg k => exact sig_asg A W hc (by rw [hK, hK']; exact k)
  | acc k => exact sig_acc A W hc (by rw [hK, hK']; exact k)
  | misc k => exact sig_misc A W hc (by rw [hK, hK']; exact k)

theorem ns_sim {U : Label → Prop} {i : Bool} (A : At p H s t f fs f' fs') (W : WF p) {ns : List (Name × Val)}
    (hc : f.ctrl = .ns ns) (hc' : f'.ctrl = .ns ns) (hk : KRel A.x U i f.kont f'.kont) : Goal I p H s t := by
  by_cases hn : ∃ x q bs kws ds K0, f.kont = .clsEnd x q bs kws ds :: K0
  · obtain ⟨x, q, bs, kws, ds, K0, he⟩ := hn
    generalize hK : f.kont = K at hk
    generalize hK' : f'.kont = K' at hk
    rw [he] at hK; subst hK
    cases hk with
    | cls k => exact ns_cls A W ⟨ns, hc, hc'⟩ (by rw [he, hK']; exact k)
    | core k => cases k
    | call k => cases k
    | comp k => cases k
    | loop k => cases k
    | asg k => cases k
    | acc k => cases k
    | misc k => cases k
  · exact ns_other A W hc hc' hk fun x q bs kws ds K0 h => hn ⟨x, q, bs, kws, ds, K0, h⟩

/-- `next`: of a suspended generator (related, or not yet run, or inside `yield from`), or of anything else. -/
theorem next_simB {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) {args : List Val}
    {kws : List (Name × Val)} (hc : f.ctrl = .call .next args kws) (hc' : f'.ctrl = .call .next args kws)
    (hk : KRel A.x U true f.kont f'.kont) : GoalB I p H s t := by
  by_cases hn : ∃ o g, args = [.gen o] ∧ kws = [] ∧ sObj s o = some (.gen (.susp g))
  · obtain ⟨o, g, rfl, rfl, ho⟩ := hn
    have hr := A.r.objs o
    rw [ho] at hr
    cases ho' : pObj t o with
    | none => rw [ho'] at hr; exact hr.elim
    | some b =>
      rw [ho'] at hr
      cases hr with
      | gen hg =>
        cases hg with
        | susp hfr => exact call_next_susp A W hc hc' hk ho ho' hfr
        | special h0 hl hs =>
          rcases Special.inv hs with ⟨l, es, gr, rest, C0, it, hC, e1, e2, e3, e4⟩ |
              ⟨l, gn, ps, b, C0, hC, e1, e2, e3, e4⟩ | ⟨l, ps, b, C0, hC, e1, e2, e3, e4⟩ |
              ⟨U', sb, d, K, K', e1, e2, e3, e4, hd, hK⟩
          · exact resume_genComp A W hc hc' hk ho ho' h0 hl hC e1 e2 e3 e4 hs
          · exact resume_genFn A W hc hc' hk ho ho' h0 hl hC e1 e2 e3 e4 hs
          · exact resume_genLam A W hc hc' hk ho ho' h0 hl hC e1 e2 e3 e4 hs
          · exact resume_yf A W hc hc' hk ho ho' h0 hl e1 e2 e3 e4 hd hK
  · exact call_next_other A W hc hc' hk hn

theorem call_sim {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) {g : Val} {args : List Val}
    {kws : List (Name × Val)} (hc : f.ctrl = .call g args kws) (hc' : f'.ctrl = .call g args kws)
    (hk : KRel A.x U true f.kont f'.kont) : Goal I p H s t := by
  by_cases h1 : ∃ o S C cl κ kd dflt, g = .fn o ∧ sObj s o = some (.clo S C cl κ kd dflt)
  · obtain ⟨o, S, C, cl, κ, kd, dflt, rfl, ho⟩ := h1
    cases hS : S.isComp
    · exact (call_fn A W hc hc' hk ho hS).sim
    · exact (call_comp A W hc hc' hk ho hS).sim
  by_cases h2 : g = .next
  · subst h2; exact (next_simB A W hc hc' hk).sim
  by_cases h3 : ∃ o, g = .op o
  · obtain ⟨o, rfl⟩ := h3; exact call_op A W hc hc' hk
  exact (call_other A W hc hc' hk (fun o S C cl κ kd dflt hg ho => h1 ⟨o, S, C, cl, κ, kd, dflt, hg, ho⟩) h2
    (fun o hg => h3 ⟨o, hg⟩)).sim

end

/-- A pending call (`PendRel`): the step of the call, PyCore's configuration stepping as the call. -/
theorem pend_sim (W : WF p) {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} (h : PendRel p H s t) :
    Goal I p H s t := by
  obtain ⟨f, fs, f', fs', g, v, K', hs, ht, hc, ⟨hc', hK', hg, hr⟩ | ⟨o, g0, rfl, rfl, hc', hK', ho, hr⟩⟩ := h
  · have A := At.ofCRel hr hs rfl
    obtain ⟨U, i, hcr, hk⟩ := A.hf.code
    have hi : i = true := by
      generalize hcc : f.ctrl = c at hcr; rw [hc] at hcc; subst hcc; cases hcr; rfl
    subst hi
    have hG : GoalB I p H s { t with stack := { f' with ctrl := .call g [v] [], kont := K' } :: fs' } := by
      rcases hg with rfl | ⟨o, rfl⟩
      · exact next_simB A W hc rfl hk
      · by_cases h1 : ∃ S C cl κ kd dflt, sObj s o = some (.clo S C cl κ kd dflt)
        · obtain ⟨S, C, cl, κ, kd, dflt, ho⟩ := h1
          cases hS : S.isComp
          · exact call_fn A W hc rfl hk ho hS
          · exact call_comp A W hc rfl hk ho hS
        · exact call_other A W hc rfl hk
            (fun o' S C cl κ kd dflt hg ho => h1 ⟨S, C, cl, κ, kd, dflt, by cases hg; exact ho⟩) (by simp) (by simp)
    have hg' : (∃ o, g = .fn o) ∨ g = .next := by
      rcases hg with rfl | ⟨o, rfl⟩
      · exact .inr rfl
      · exact .inl ⟨o, rfl⟩
    refine (SimStepB.swap (pstep_callA hg' ht hc' hK') ?_ ?_ ?_ hG).sim
    · simp [pfocus, PyCore.focus, ht, hc']
    · simp [μ, hs, ht, hK', hc'] <;> omega
    · intro _ a' hf; simpa [Fin, PyCore.outcome, ht] using hf
  · have A := At.ofCRel hr hs rfl
    obtain ⟨U, i, hcr, hk⟩ := A.hf.code
    have hi : i = true := by
      generalize hcc : f.ctrl = c at hcr; rw [hc] at hcc; subst hcc; cases hcr; rfl
    subst hi
    refine (SimStepB.swap (pstep_yf ht hc' hK' ho) ?_ ?_ ?_ (next_simB A W hc rfl hk)).sim
    · simp [pfocus, PyCore.focus, ht, hc']
    · simp [μ, hs, ht, hc', hK']
    · intro _ a' hf; simpa [Fin, PyCore.outcome, ht] using hf

/-- The simulation step from related configurations. -/
theorem step_sim (W : WF p) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) (h : CRelI p H s t) :
    Goal I p H s t := by
  rcases h with h | h | h
  case inr.inl => exact init_sim W h
  case inr.inr => exact pend_sim W h
  have hst := h.stack
  cases hs : s.stack with
  | nil =>
    cases ht : t.stack with
    | nil =>
      refine Or.inl ⟨s, t, [], [], .nil _, by simp [Sem.step, hs], .nil _, by simp [PyCore.step, ht], ?_, ?_⟩
      · simp only [Fin, Sem.outcome, PyCore.outcome, hs, ht, h.res]
        cases s.res with
        | none => simp [OCorr, h.out, h.st]
        | some r => cases r <;> simp [OCorr, h.out, h.st]; exact h.glob
      · intro y hy x hx; simp at hy; subst hy; simp [pfocus, PyCore.focus, ht] at hx
    | cons => rw [hs, ht] at hst; exact hst.elim
  | cons f fs =>
    cases ht : t.stack with
    | nil => rw [hs, ht] at hst; exact hst.elim
    | cons f' fs' =>
      rw [hs, ht] at hst
      have A : At p H s t f fs f' fs' := ⟨h, hs, ht, hst.1⟩
      obtain ⟨U, i, hcr, hkr⟩ := hst.1.code
      generalize hc : f.ctrl = c at hcr
      generalize hc' : f'.ctrl = c' at hcr
      cases hcr with
      | ev hg => exact ev_sim _ A W hc hc' hg hkr
      | val => exact val_sim A W hc hc' hkr
      | @exec ss hg hnc =>
        cases ss with
        | nil => exact done_sim A W hc hc' hkr
        | cons st ss => exact exec_sim st A W hc hc' hg hnc hkr
      | raise =>
        by_cases hb : BareAt A.x U i f.kont f'.kont
        · exact raise_bare A W hc hc' hb
        · exact sig_sim A W (Or.inl ⟨_, hc, hc'⟩) (fun _ => hb) hkr
      | retv => exact sig_sim A W (Or.inr (Or.inl ⟨_, hc, hc'⟩)) (fun ⟨v, h⟩ => by rw [hc] at h; cases h) hkr
      | brk hn => exact sig_sim A W (Or.inr (Or.inr (Or.inl ⟨rfl, hn, hc, hc'⟩))) (fun ⟨v, h⟩ => by rw [hc] at h; cases h) hkr
      | cont hn => exact sig_sim A W (Or.inr (Or.inr (Or.inr ⟨rfl, hn, hc, hc'⟩))) (fun ⟨v, h⟩ => by rw [hc] at h; cases h) hkr
      | wait => exact wait_sim A hc hc'
      | op => exact op_sim A hc hc' hkr
      | kapp => exact kapp_sim A hc hc' hkr
      | call => exact call_sim A W hc hc' hkr
      | ns => exact ns_sim A W hc hc' hkr

/-! ## (T2) and the reach correspondence -/

/-- (T2): for every interpretation, the Surf run of `p` and the PyCore run of ⌊p⌋, on the same
module dictionary and interpretation state, terminate with corresponding outcomes (`OCorr`: the
same state, the same exception or module dictionary on every name with no dot, PyCore's output
list empty) or diverge together. -/
theorem t2 (I : Py.Interp σ) (p : List Stmt) (W : WF p) (σ0 : Std.HashMap Name Val) (s0 : σ) :
    (∀ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) →
      ∃ o', PyCore.Terminates I (PyCore.init (tr p) (fun x => σ0[x]?) s0) o' ∧ OCorr o o') ∧
    (∀ o', PyCore.Terminates I (PyCore.init (tr p) (fun x => σ0[x]?) s0) o' →
      ∃ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) ∧ OCorr o o') ∧
    (Sem.Diverges I (Sem.init p σ0 s0) ↔ PyCore.Diverges I (PyCore.init (tr p) (fun x => σ0[x]?) s0)) := by
  have HS := fun H s t h => step_sim (I := I) W H s t h
  have h0 : CRelI p (fun _ => False) (Sem.init p σ0 s0) (PyCore.init (tr p) (fun x => σ0[x]?) s0) :=
    .inr (.inl ⟨σ0, s0, rfl, rfl⟩)
  refine ⟨fun o ⟨n, hn, ho⟩ => ?_, fun o' ⟨m, hm, ho⟩ => ?_, ⟨fun hd m => ?_, fun hd n => ?_⟩⟩
  · rw [run_eq] at hn ho
    obtain ⟨m, hm, hf⟩ := sim_term_ab HS n _ _ _ h0 hn
    exact ⟨_, ⟨m, by rwa [prun_eq], rfl⟩, by rw [← ho, ← prun_eq] at *; exact hf⟩
  · rw [prun_eq] at hm ho
    obtain ⟨n, hn, hf⟩ := sim_term_ba HS m _ _ _ h0 hm
    exact ⟨_, ⟨n, by rwa [run_eq], rfl⟩, by rw [← ho, run_eq]; exact hf⟩
  · rw [prun_eq]
    exact sim_div_ab HS m _ _ _ h0 (fun n => by rw [← run_eq]; exact hd n)
  · rw [run_eq]
    exact sim_div_ba HS n _ _ _ h0 (fun m => by rw [← prun_eq]; exact hd m)

/-- The reach correspondence: if the PyCore run of ⌊p⌋ evaluates a node made for a node of
F_surf, the Surf run of `p` touches a node of F_surf. -/
theorem reach_corr (I : Py.Interp σ) (R : Edit) (p : List Stmt) (W : WF p) (σ0 : Std.HashMap Name Val) (s0 : σ)
    (h : NoReachT p I (inF R p) (Sem.init p σ0 s0)) :
    PyCore.NoReach I (imgF R p) (PyCore.init (tr p) (fun x => σ0[x]?) s0) := by
  intro n x hx hF
  obtain ⟨l, k, rfl, hk, hl⟩ := hF
  by_cases h64 : 64 ≤ sub l k
  · have hx' : pfocus (runF (PyCore.step I) n (PyCore.init (tr p) (fun x => σ0[x]?) s0)) = some (sub l k) := by
      rw [← prun_eq]; simp [pfocus, hx, h64]
    rcases sim_reach (fun H s t h => step_sim (I := I) W H s t h) n (fun _ => False) _ _ _
        (.inr (.inl ⟨σ0, s0, rfl, rfl⟩)) hx' with hm | ⟨m, hm⟩
    · exact hm
    · rw [sub_div l k hk] at hm
      exact h m l (by rw [run_eq]; exact hm) hl
  · have hl0 : l = 0 := by
      have h1 : 64 * l + k < 64 := Nat.lt_of_not_le h64
      rcases Nat.eq_zero_or_pos l with h | h
      · exact h
      · have : 64 ≤ 64 * l := Nat.le_mul_of_pos_right 64 h
        exact absurd h1 (Nat.not_lt.2 (Nat.le_trans this (Nat.le_add_right _ _)))
    subst hl0
    exact absurd (W.pos 0 (inF_labels R p hl)) (Nat.lt_irrefl 0)

/-! ## Every generator expression of a well-formed program has one element -/

/-- The function scopes among `L` are no generator expression with other than one element. -/
def GenL (L : List Item) : Prop := ∀ l C S, Item.fn l C S ∈ L → S.genOk = true

theorem gok_nil : GenL [] := fun _ _ _ h => nomatch h
theorem gok_app {L M : List Item} (h1 : GenL L) (h2 : GenL M) : GenL (L ++ M) := fun l C S h =>
  (List.mem_append.1 h).elim (h1 l C S) (h2 l C S)
theorem gok_occ {l x C'} {L : List Item} (h : GenL L) : GenL (.occ l x C' :: L) := fun l C S h' =>
  (List.mem_cons.1 h').elim (fun e => nomatch e) (h l C S)
theorem gok_fn {l C'} {S' : Scope} {L : List Item} (hS : S'.genOk = true) (h : GenL L) :
    GenL (.fn l C' S' :: L) := fun l C S h' =>
  (List.mem_cons.1 h').elim (fun e => by cases e; exact hS) (h l C S)
theorem gok_occs {L : List Item} (h : ∀ i ∈ L, ∃ l x C, i = .occ l x C) : GenL L := fun _ _ _ hm => by
  obtain ⟨_, _, _, e⟩ := h _ hm; cases e

theorem ok_unstar {a : Expr} (h : okE a = true) : okE (unstar a) = true := by
  cases a <;> simp_all [unstar, okE]
theorem okAs_cons {e : Expr} {es : List Expr} (h : okAs (e :: es) = true) :
    okE (unstar e) = true ∧ okAs es = true := by
  cases e <;> simp_all [okAs, unstar]

mutual
theorem gokE (C : List Scope) : ∀ e, okE (unstar e) = true → GenL (itemsE C e)
  | .const .., _ => gok_nil
  | .name .., _ => gok_occ gok_nil
  | .bin _ _ a b, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gokE C a (ok_unstar h.1.2)) (gokE C b (ok_unstar h.2))
  | .sub _ a b, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gokE C a (ok_unstar h.1)) (gokE C b (ok_unstar h.2))
  | .unary _ _ a, h | .attr _ a _, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h; exact gokE C a (ok_unstar h.2)
  | .yieldFrom _ a, h => by simp only [unstar, okE] at h; exact gokE C a (ok_unstar h)
  | .star _ a, h => by simp only [unstar] at h; exact gokE C a (ok_unstar h)
  | .boolop _ _ es, h | .fstr _ es, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    first | exact gokEs C es h.2 | exact gokEs C es h
  | .list _ es, h | .tuple _ es, h | .set _ es, h => by
    simp only [unstar, okE] at h; exact gokAs C es h
  | .compare _ a _ es, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gokE C a (ok_unstar h.1.1.1.1)) (gokEs C es h.1.1.1.2)
  | .ifexp _ c a b, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokE C c (ok_unstar h.1.1)) (gokE C a (ok_unstar h.1.2))) (gokE C b (ok_unstar h.2))
  | .call _ f args kws, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokE C f (ok_unstar h.1.1)) (gokAs C args h.1.2)) (gokKs C kws h.2)
  | .slice _ a b c, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokO C a h.1.1) (gokO C b h.1.2)) (gokO C c h.2)
  | .dict _ kvs, h => by simp only [unstar, okE] at h; exact gokDs C kvs h
  | .lam l ps b, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokPs C ps h.1) (gok_fn (by rfl) (gok_occs (by simp [paramOccs]))))
      (gokE _ b (ok_unstar h.2))
  | .comp l k es gs, h => by
    simp only [unstar, okE, Bool.and_eq_true, decide_eq_true_eq] at h
    refine gok_app (gok_app (gokG1 C gs h.1.1.1.2) (gok_fn ?_ (gokGs _ true gs h.1.1.1.2)))
      (gokEs _ es h.1.1.1.1)
    have hl := h.1.2
    cases k <;> simp_all [Scope.genOk]
  | .walrus .., h => by
    simp only [unstar, okE] at h; exact gok_occ (gokE C _ (ok_unstar h))
  | .yield _ e, h => by simp only [unstar, okE] at h; exact gokO C e h
  | .fmt _ e _ s, h => by
    simp only [unstar, okE, Bool.and_eq_true] at h
    exact gok_app (gokE C e (ok_unstar h.1)) (gokO C s h.2)
theorem gokO (C : List Scope) : ∀ e, okO e = true → GenL (itemsO C e)
  | none, _ => gok_nil
  | some e, h => gokE C e (ok_unstar h)
theorem gokEs (C : List Scope) : ∀ es, okEs es = true → GenL (itemsEs C es)
  | [], _ => gok_nil
  | e :: es, h => by
    simp only [okEs, Bool.and_eq_true] at h
    exact gok_app (gokE C e (ok_unstar h.1)) (gokEs C es h.2)
theorem gokAs (C : List Scope) : ∀ es, okAs es = true → GenL (itemsEs C es)
  | [], _ => gok_nil
  | e :: es, h => gok_app (gokE C e (okAs_cons h).1) (gokAs C es (okAs_cons h).2)
theorem gokKs (C : List Scope) : ∀ ks, okKs ks = true → GenL (itemsKs C ks)
  | [], _ => gok_nil
  | .mk _ _ e :: ks, h => by
    simp only [okKs, Bool.and_eq_true] at h
    exact gok_app (gokE C e (ok_unstar h.1.2)) (gokKs C ks h.2)
theorem gokDs (C : List Scope) : ∀ kvs, okDs kvs = true → GenL (itemsDs C kvs)
  | [], _ => gok_nil
  | .mk k v :: kvs, h => by
    simp only [okDs, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokO C k h.1.1) (gokE C v (ok_unstar h.1.2))) (gokDs C kvs h.2)
theorem gokPs (C : List Scope) : ∀ ps, okPs ps = true → GenL (itemsPs C ps)
  | [], _ => gok_nil
  | .mk _ _ _ d a :: ps, h => by
    simp only [okPs, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokO C d h.1.1.2) (gokO C a h.1.2)) (gokPs C ps h.2)
theorem gokG1 (C : List Scope) : ∀ gs, okGs gs = true → GenL (itemsG1 C gs)
  | [], _ => gok_nil
  | .mk _ _ i _ :: _, h => by
    simp only [okGs, Bool.and_eq_true] at h
    exact gokE C i (ok_unstar h.1.1.2)
theorem gokGs (C : List Scope) (first : Bool) : ∀ gs, okGs gs = true → GenL (itemsGs C first gs)
  | [], _ => gok_nil
  | .mk _ t i ifs :: gs, h => by
    simp only [okGs, Bool.and_eq_true] at h
    refine gok_app (gok_app (gok_app ?_ (gokE C t (ok_unstar h.1.1.1.1))) (gokEs C ifs h.1.2))
      (gokGs C false gs h.2)
    cases first
    · exact gokE C i (ok_unstar h.1.1.2)
    · exact gok_nil
end

mutual
theorem gokS (C : List Scope) : ∀ s, okS s = true → GenL (itemsS C s)
  | .expr _ e, h => by simp only [okS] at h; exact gokE C e (ok_unstar h)
  | .assign _ ts e, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gokE C e (ok_unstar h.2)) (gokAs C ts h.1.1)
  | .augassign _ t _ e, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gokE C t (ok_unstar h.1.2)) (gokE C e (ok_unstar h.2))
  | .annassign _ t a v, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokE C t (ok_unstar h.1.1.2)) (gokE C a (ok_unstar h.1.2))) (gokO C v h.2)
  | .del _ ts, h => by simp only [okS, Bool.and_eq_true] at h; exact gokAs C ts h.1
  | .ite _ c t u, h | .while _ c t u, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokE C c (ok_unstar h.1.1)) (gokB C t h.1.2)) (gokB C u h.2)
  | .for _ t it b u, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gok_app (gok_app (gokE C t (ok_unstar h.1.1.1.1)) (gokE C it (ok_unstar h.1.1.2)))
      (gokB C b h.1.2)) (gokB C u h.2)
  | .brk _, _ | .cont _, _ | .pass _, _ => gok_nil
  | .ret _ e, h => by simp only [okS] at h; exact gokO C e h
  | .defn l f ps b ds r, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gok_app (gok_app (gok_app (gokPs C ps h.1.1.1.2) (gokEs C ds h.1.2)) (gokO C r h.2))
      (gok_occ (gok_fn (by rfl) (gok_occs (by simp [paramOccs]))))) (gokB _ b h.1.1.2)
  | .cls l x bs ks b ds, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gok_app (gok_app (gok_app (gokAs C bs h.1.1.1.2) (gokKs C ks h.1.1.2)) (gokEs C ds h.2))
      (gok_occ (gok_occs (by simp)))) (gokB _ b h.1.2)
  | .glob .., _ | .nonloc .., _ => gok_occs (by simp [itemsS])
  | .imp .., _ | .impFrom .., _ => gok_occs (by simp [itemsS])
  | .tryE _ b hs u, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gok_app (gokB C b h.1.1) (gokHs C hs h.1.2)) (gokB C u h.2)
  | .raise _ e c, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gokO C e h.1.2) (gokO C c h.2)
  | .assert _ t m, h => by
    simp only [okS, Bool.and_eq_true] at h
    exact gok_app (gokE C t (ok_unstar h.1)) (gokO C m h.2)
theorem gokHs (C : List Scope) : ∀ hs, okHs hs = true → GenL (itemsHs C hs)
  | [], _ => gok_nil
  | .mk _ ty x b :: hs, h => by
    simp only [okHs, Bool.and_eq_true] at h
    refine gok_app (gok_app (gok_app (gokO C ty h.1.1.1.1) (gok_occs ?_)) (gokB C b h.1.2)) (gokHs C hs h.2)
    cases x <;> simp
theorem gokB (C : List Scope) : ∀ ss, okB ss = true → GenL (itemsB C ss)
  | [], _ => gok_nil
  | s :: ss, h => by
    simp only [okB, Bool.and_eq_true] at h
    exact gok_app (gokS C s h.1) (gokB C ss h.2)
end

theorem genOk_of_ok {p : List Stmt} (h : okB p = true) : GenOk p := gokB [] p h

/-! ## The footprint theorem on Surf runs -/

/-- Equal Surf outcomes, module dictionaries compared on the names with no dot. -/
def OEq : Sem.Outcome σ → Sem.Outcome σ → Prop
  | .normal st g, .normal st' g' => st = st' ∧ ∀ x, ¬ Dot x → g[x]? = g'[x]?
  | .exc v st, .exc v' st' => v = v' ∧ st = st'
  | .stuck st, .stuck st' => st = st'
  | _, _ => False

theorem ocorr_oeq : ∀ {o o2 : Sem.Outcome σ} {o' : PyCore.Outcome σ}, OCorr o o' → OCorr o2 o' → OEq o o2
  | .normal _ _, .normal _ _, .normal _ _ _, ⟨_, h1, h2⟩, ⟨_, h3, h4⟩ =>
    ⟨h1.symm.trans h3, fun x hx => (h2 x hx).symm.trans (h4 x hx)⟩
  | .exc _ _, .exc _ _, .exc _ _ _, ⟨h1, _, h2⟩, ⟨h3, _, h4⟩ => ⟨h1.symm.trans h3, h2.symm.trans h4⟩
  | .stuck _, .stuck _, .stuck _ _, ⟨_, h1⟩, ⟨_, h2⟩ => h1.symm.trans h2
  | .normal _ _, _, .exc _ _ _, h, _ | .normal _ _, _, .stuck _ _, h, _
  | .exc _ _, _, .normal _ _ _, h, _ | .exc _ _, _, .stuck _ _, h, _
  | .stuck _, _, .normal _ _ _, h, _ | .stuck _, _, .exc _ _ _, h, _ => h.elim
  | _, .normal _ _, .exc _ _ _, _, h | _, .normal _ _, .stuck _ _, _, h
  | _, .exc _ _, .normal _ _ _, _, h | _, .exc _ _, .stuck _ _, _, h
  | _, .stuck _, .normal _ _ _, _, h | _, .stuck _, .exc _ _ _, _, h => h.elim

/-- Theorem 5 on Surf runs: let `q = editB R p`. For every interpretation and input, if the
Surf run of `p` touches no node of F_surf(p, q), then `p` and `q` end with equal outcomes (module
dictionaries compared on the names with no dot) and diverge together. The conditions: `p` and `q`
are Python programs (`WF`), each expression replacement keeps its site's label, and the
augmented targets outside the sites and their replacements are names, attributes or subscripts. -/
theorem footprint_theorem_surf_sem (I : Py.Interp σ) (R : Edit) (p : List Stmt) (σ0 : Std.HashMap Name Val)
    (s0 : σ) (W : WF p) (Wq : WF (editB R p)) (hk : KeepsLabels R) (hr : regB R [] p = true)
    (h : NoReachT p I (inF R p) (Sem.init p σ0 s0)) :
    (∀ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) →
      ∃ o', Sem.Terminates I (Sem.init (editB R p) σ0 s0) (· = o') ∧ OEq o o') ∧
    (∀ o', Sem.Terminates I (Sem.init (editB R p) σ0 s0) (· = o') →
      ∃ o, Sem.Terminates I (Sem.init p σ0 s0) (· = o) ∧ OEq o o') ∧
    (Sem.Diverges I (Sem.init p σ0 s0) ↔ Sem.Diverges I (Sem.init (editB R p) σ0 s0)) := by
  have hP := footprint_theorem_surf I R p (fun x => σ0[x]?) s0 W.nodup Wq.nodup
    (fun h0 => Nat.lt_irrefl 0 (W.pos 0 h0)) W.nodot Wq.nodot (genOk_of_ok W.ok) hk hr W.reg Wq.reg
    (reach_corr I R p W σ0 s0 h)
  have Tp := t2 I p W σ0 s0
  have Tq := t2 I (editB R p) Wq σ0 s0
  refine ⟨fun o ho => ?_, fun o' ho => ?_, Tp.2.2.trans (hP.2.trans Tq.2.2.symm)⟩
  · obtain ⟨o1, h1, c1⟩ := Tp.1 o ho
    obtain ⟨o2, h2, c2⟩ := Tq.2.1 o1 ((hP.1 o1).1 h1)
    exact ⟨o2, h2, ocorr_oeq c1 c2⟩
  · obtain ⟨o1, h1, c1⟩ := Tq.1 o' ho
    obtain ⟨o2, h2, c2⟩ := Tp.2.1 o1 ((hP.1 o1).2 h1)
    exact ⟨o2, h2, ocorr_oeq c2 c1⟩

end Surf.T2
