/-
(T2): the framework's lemmas and the cases of the constructs the translation maps to PyCore's own.
-/
import Surf.T2Rel

namespace Surf.T2
open PyCore (Name Label)
open Py (Val Gadget)

variable {σ : Type} {I : Py.Interp σ} {p : List Stmt}

/-! ## The core constants

`Py.constVal` fixes the operations (`$op:…`), the gadgets' names and the markers whatever the
interpretation. These are the values of the constants the translation makes. A name inside a
constant has no `:` (`NC`): a program's names (`okName`), mangled in a chain whose class names are
(`KOk`), and the fresh names (a dot, a tag, digits). -/

section KC
variable (I)

/-- No `:` in a string. -/
abbrev NC (s : String) : Prop := ':' ∉ s.toList

/-- Unfolds the parse of a core constant. -/
macro "kcs" : tactic => `(tactic| simp [Py.Op.ofName, Gadget.ofName, Gadget.name, Py.splitBy,
  List.splitOn_cons_eq_ite_modifyHead, Py.Op.ofParts, Py.isMarker, Py.hasPrefix])

theorem kc_op {k : String} {o : Py.Op} (h : Py.Op.ofName k = some o) : Py.constVal I k = .op o := by
  unfold Py.constVal
  by_cases h1 : k = "$false"
  · subst h1; simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead] at h
  by_cases h2 : k = "$true"
  · subst h2; simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead] at h
  by_cases h3 : k = "$none"
  · subst h3; simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead] at h
  by_cases h4 : k = "$args"
  · subst h4; simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead] at h
  by_cases h5 : k = "$next"
  · subst h5; simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead] at h
  simp [h1, h2, h3, h4, h5, h]

theorem kc_prim {k : String} (h0 : Py.Op.ofName k = none) (h : ((Gadget.ofName k).isSome || Py.isMarker k) = true)
    (h1 : k ≠ "$false") (h2 : k ≠ "$true") (h3 : k ≠ "$none") (h4 : k ≠ "$args") (h5 : k ≠ "$next") :
    Py.constVal I k = .prim k := by
  unfold Py.constVal; simp [h1, h2, h3, h4, h5, h0, h]

/-! ### Names with no `:` -/

theorem nc_digits (n : Nat) : NC (toString n) := by
  intro h
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at h
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  simp at this

theorem nc_append {a b : String} (ha : NC a) (hb : NC b) : NC (a ++ b) := by
  simp only [NC, String.toList_append, List.mem_append, not_or]; exact ⟨ha, hb⟩

theorem nc_fresh {tag : String} (h : NC tag) (l : Label) : NC (fresh tag l) :=
  nc_append (nc_append (by simp [NC]) h) (nc_digits l)

theorem nc_ok {x : String} (h : okName x = true) : NC x := by
  simp only [okName, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro hm; have := h.1.1.1; rw [String.contains_char_eq] at this; simp_all

theorem nc_path {x : String} (h : okPath x = true) : NC x := by
  simp only [okPath, Bool.and_eq_true, Bool.not_eq_true'] at h
  intro hm; have := h.1; rw [String.contains_char_eq] at this; simp_all

/-! ### Operations -/

theorem kc_iter : Py.constVal I "$op:iter" = .op .iter := kc_op I (by kcs)
theorem kc_getitem : Py.constVal I "$op:getitem" = .op .getitem := kc_op I (by kcs)
theorem kc_setitem : Py.constVal I "$op:setitem" = .op .setitem := kc_op I (by kcs)
theorem kc_delitem : Py.constVal I "$op:delitem" = .op .delitem := kc_op I (by kcs)
theorem kc_format : Py.constVal I "$op:format" = .op .format := kc_op I (by kcs)
theorem kc_importStar : Py.constVal I "$op:importStar" = .op .importStar := kc_op I (by kcs)
theorem kc_slice : Py.constVal I "$op:display:slice" = .op (.display .slice) := kc_op I (by kcs)
theorem kc_fstr : Py.constVal I "$op:display:fstr" = .op (.display .fstr) := kc_op I (by kcs)
theorem kc_accum_list : Py.constVal I "$op:accum:list" = .op (.accum .list) := kc_op I (by kcs)
theorem kc_accum_set : Py.constVal I "$op:accum:set" = .op (.accum .set) := kc_op I (by kcs)
theorem kc_accum_dict : Py.constVal I "$op:accum:dict" = .op (.accum .dict) := kc_op I (by kcs)

/-- A comprehension's empty accumulator (`compWrap`). -/
theorem kc_acc (k : CompKind) : Py.constVal I ("$op:display:" ++ accName k ++ ":") =
    .op (.display (match k with | .set => .set [] | .dict => .dict [] | _ => .list [])) := by
  cases k <;> exact kc_op I (by simp [accName, Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, Py.Op.ofParts])

theorem kc_getattr {a : String} (h : NC a) : Py.constVal I ("$op:getattr:" ++ a) = .op (.getattr a) :=
  kc_op I (by simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_eq_singleton h, Py.Op.ofParts])
theorem kc_setattr {a : String} (h : NC a) : Py.constVal I ("$op:setattr:" ++ a) = .op (.setattr a) :=
  kc_op I (by simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_eq_singleton h, Py.Op.ofParts])
theorem kc_delattr {a : String} (h : NC a) : Py.constVal I ("$op:delattr:" ++ a) = .op (.delattr a) :=
  kc_op I (by simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_eq_singleton h, Py.Op.ofParts])
theorem kc_unop {a : String} (h : NC a) : Py.constVal I ("$op:unop:" ++ a) = .op (.unop a) :=
  kc_op I (by simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_eq_singleton h, Py.Op.ofParts])
theorem kc_importFrom {a : String} (h : NC a) : Py.constVal I ("$op:importFrom:" ++ a) = .op (.importFrom a) :=
  kc_op I (by simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_eq_singleton h, Py.Op.ofParts])



theorem nc_dropWhile (c : String) (h : NC c) : NC (c.dropWhile (· == '_')).toString := by
  have e := @String.Slice.takeWhile_append_dropWhile _ (· == '_') _ _ _ c.toSlice
  intro hm; apply h
  have e2 : (c.dropWhile (· == '_')).toString = (c.toSlice.dropWhile (· == '_')).copy := rfl
  rw [e2] at hm
  have : c.toList = (c.toSlice.takeWhile (· == '_')).copy.toList ++ (c.toSlice.dropWhile (· == '_')).copy.toList := by
    rw [← String.toList_append, e]; simp
  rw [this]; exact List.mem_append_right _ hm

theorem kok_priv : ∀ {C : List Scope}, KOk C → ∀ c, priv C = some c → okName c = true
  | [], _, _, h => by simp [priv] at h
  | S :: C, ⟨h1, h2⟩, c, h => by
    cases S with
    | cl l x b => simp [priv] at h; subst h; exact h1
    | fn => exact kok_priv h2 c h
    | lam => exact kok_priv h2 c h
    | comp => exact kok_priv h2 c h

/-- A program's name mangled in a chain whose class names are a program's (`GoodE.pv`). -/
theorem nc_mangle_pv {C : List Scope} (hpv : ∀ c, priv C = some c → okName c = true) {a : String} (ha : NC a) :
    NC (mangle (priv C) a) := by
  unfold mangle
  cases hp : priv C with
  | none => exact ha
  | some c =>
    simp only
    split
    · exact nc_append (nc_append (by simp [NC]) (nc_dropWhile c (nc_ok (hpv c hp)))) ha
    · exact ha

/-- A program's name mangled in a chain of the relation (`KOk`). -/
theorem nc_mangle {C : List Scope} (hC : KOk C) {a : String} (ha : NC a) : NC (mangle (priv C) a) :=
  nc_mangle_pv (kok_priv hC) ha

theorem natOf_toString (n : Nat) : Py.natOf (toString n) = some n := by
  have hf : ∀ (l : List Char), (∀ c ∈ l, c.isDigit = true) → ∀ init, l.foldl (fun acc d => acc.bind fun n =>
      if d.isDigit then some (10 * n + (d.toNat - '0'.toNat)) else none) (some init) = some (Nat.ofDigitChars 10 l init) := by
    intro l h
    induction l with
    | nil => intro init; simp [Nat.ofDigitChars_nil]
    | cons c cs ih =>
      intro init
      simp only [List.foldl_cons, Option.bind_some, h c (by simp), ite_true]
      rw [ih (fun d hd => h d (by simp [hd])), Nat.ofDigitChars_cons]
  unfold Py.natOf
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList]
  have hne := @Nat.toDigits_ne_nil n 10
  have hd : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  cases h : Nat.toDigits 10 n with
  | nil => exact absurd h hne
  | cons c cs => simp only; rw [← h, hf _ hd, Nat.ofDigitChars_ten_toDigits]

theorem intOf_toString (c : Int) : Py.intOf (toString c) = some c := by
  cases c with
  | ofNat n =>
    show Py.intOf (toString n) = some (Int.ofNat n)
    unfold Py.intOf
    have hd : ∀ c ∈ (toString n).toList, c.isDigit = true := by
      intro c hc; rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hc
      exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
    split
    · rename_i cs heq; have := hd '-' (by rw [heq]; simp); simp at this
    · rw [natOf_toString]; rfl
  | negSucc n =>
    show Py.intOf ("-" ++ toString (n + 1)) = some (Int.negSucc n)
    unfold Py.intOf
    simp only [String.toList_append]
    simp only [show "-".toList = ['-'] from rfl, List.cons_append, List.nil_append, String.ofList_toList,
      natOf_toString]
    rfl

theorem kc_convert (c : Int) : Py.constVal I ("$op:convert:" ++ toString c) = .op (.convert c) := by
  have hc : NC (toString c) := by
    cases c with
    | ofNat n => exact nc_digits n
    | negSucc n => exact nc_append (by simp [NC]) (nc_digits (n + 1))
  have hc' : ':' ∉ c.repr.toList := hc
  have hi : Py.intOf c.repr = some c := intOf_toString c
  exact kc_op I (by simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_eq_singleton hc',
    Py.Op.ofParts, hi])

theorem kc_import {m : String} (h : NC m) (b : Bool) :
    Py.constVal I s!"$op:import:{m}:{if b then 1 else 0}" = .op (.import m b) := by
  have e : ∀ s : String, toString s = s := fun _ => rfl
  cases b <;> exact kc_op I (by simp [e, Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead,
    Nat.toDigits_of_lt_base, Nat.digitChar, List.splitOn_append_cons_self_of_not_mem h, Py.Op.ofParts])

theorem stars_starsStr (st : List Bool) : (Py.starsStr st).toList.map (· == '1') = st := by
  simp only [Py.starsStr, String.toList_ofList, List.map_map]
  induction st with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all

theorem nc_starsStr (st : List Bool) : NC (Py.starsStr st) := by
  intro hm; simp [Py.starsStr] at hm

theorem kc_dict (st : List Bool) : Py.constVal I ("$op:display:dict:" ++ Py.starsStr st) = .op (.display (.dict st)) :=
  kc_op I (by simp [Py.Op.ofName, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead,
    List.splitOn_eq_singleton (nc_starsStr st), Py.Op.ofParts, stars_starsStr])


/-! ### Gadgets and markers -/

/-- A gadget whose name parses back: its parameters have no `:`. -/
def GOk : Gadget → Prop
  | .display k | .cunary k | .annot k | .raiseK k | .set k | .get k => NC k
  | _ => True

theorem nc_toDigits (n : Nat) : ':' ∉ Nat.toDigits 10 n := by
  have := nc_digits n; simpa [NC, Nat.toString_eq_ofList_toDigits, String.toList_ofList] using this

theorem natOf_toDigits (n : Nat) : Py.natOf (String.ofList (Nat.toDigits 10 n)) = some n := by
  rw [← Nat.toString_eq_ofList_toDigits]; exact natOf_toString n

/-- Unfolds the parse of a gadget's name. -/
macro "kcg" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp [Py.Op.ofName, Gadget.ofName, Gadget.name, Py.splitBy,
  List.splitOn_cons_eq_ite_modifyHead, Py.Op.ofParts, Py.isMarker, Py.hasPrefix, natOf_toDigits,
  List.splitOn_append_cons_self_of_not_mem (nc_toDigits _), List.splitOn_eq_singleton (nc_toDigits _)] $[$loc]?)

theorem gad_op (g : Gadget) : Py.Op.ofName g.name = none := by
  cases g <;> kcg

theorem gad_name (g : Gadget) (h : GOk g) : Gadget.ofName g.name = some g := by
  cases g <;> simp only [GOk] at h
  case display k | cunary k | annot k | raiseK k | set k | get k =>
    have h' : ':' ∉ k.toList := h
    simp [Gadget.ofName, Gadget.name, Py.splitBy, List.splitOn_cons_eq_ite_modifyHead, List.splitOn_eq_singleton h']
  all_goals kcg

theorem kc_gad (g : Gadget) (h : GOk g) : Py.constVal I g.name = .prim g.name := by
  have hg := gad_name g h
  refine kc_prim I (gad_op g) (by simp [hg]) ?_ ?_ ?_ ?_ ?_ <;> intro e <;> rw [e] at hg <;> kcg at hg

theorem kc_stuck : Py.constVal I "$stuck" = .prim "$stuck" := kc_gad I .stuck trivial
theorem op_stuck' : Py.Op.ofName "$stuck" = none := gad_op .stuck
theorem gad_stuck' : Gadget.ofName "$stuck" = some .stuck := gad_name .stuck trivial

theorem kc_marker {k : String} (h : Py.isMarker k = true) (h0 : Py.Op.ofName k = none) : Py.constVal I k = .prim k := by
  refine kc_prim I h0 (by simp [h]) ?_ ?_ ?_ ?_ ?_ <;> intro e <;> rw [e] at h <;> kcg at h

theorem kc_pos : Py.constVal I "$pos" = .prim "$pos" := kc_marker I (by kcg) (by kcg)
theorem kc_star : Py.constVal I "$star" = .prim "$star" := kc_marker I (by kcg) (by kcg)
theorem kc_c0 : Py.constVal I "$c0" = .prim "$c0" := kc_marker I (by kcg) (by kcg)
theorem kc_c1 : Py.constVal I "$c1" = .prim "$c1" := kc_marker I (by kcg) (by kcg)
theorem kc_nc : Py.constVal I "$nc" = .prim "$nc" := kc_marker I (by kcg) (by kcg)

theorem kc_kw (x : Option Name) : Py.constVal I (Py.kwMarker x) = .prim (Py.kwMarker x) := by
  cases x with
  | none => exact kc_marker I (by simp [Py.kwMarker]; kcg) (by simp [Py.kwMarker]; kcg)
  | some x =>
    refine kc_marker I ?_ (by simp [Py.kwMarker]; kcg)
    simp [Py.kwMarker, Py.isMarker, Py.hasPrefix]

theorem kc_param (x : Name) (k : Py.PK) (d : Bool) :
    Py.constVal I (Py.paramMarker x k d) = .prim (Py.paramMarker x k d) :=
  kc_marker I (by simp [Py.paramMarker]; kcg) (by simp [Py.paramMarker]; kcg)

theorem markKw_kw (x : Option Name) : Py.markKw (.prim (Py.kwMarker x)) = some x := by
  cases x with
  | none => simp [Py.markKw, Py.kwMarker]
  | some x =>
    have hne : "$kw:" ++ x ≠ "$kwstar" := fun e => by have := congrArg String.toList e; simp at this
    simp [Py.markKw, Py.kwMarker, Py.hasPrefix, Py.dropChars, hne]

theorem markParam_param {x : Name} (hx : ',' ∉ x.toList) (he : x.toList.head? ≠ some '=') (k : Py.PK) (d : Bool) :
    Py.markParam (.prim (Py.paramMarker x k d)) = some (x, k, d) := by
  have hk : k.chr ≠ ',' := by cases k <;> decide
  have hk' : Py.PK.ofChr k.chr = some k := by cases k <;> rfl
  cases d with
  | true =>
    have hn : ',' ∉ k.chr :: '=' :: x.toList := by simp [hk.symm, hx]
    simp [Py.markParam, Py.paramMarker, Py.sigStr, Py.hasPrefix, Py.dropChars, Py.sigOf, Py.splitBy,
      List.splitOn_eq_singleton hn, hk']
  | false =>
    have hn : ',' ∉ k.chr :: x.toList := by simp [hk.symm, hx]
    cases hxl : x.toList with
    | nil =>
      have : x = "" := by rw [← String.ofList_toList (s := x), hxl]
      subst this
      have hn' : ',' ∉ [k.chr] := by simpa using hk.symm
      simp [Py.markParam, Py.paramMarker, Py.sigStr, Py.hasPrefix, Py.dropChars, Py.sigOf, Py.splitBy, hk',
        List.splitOn_eq_singleton hn']
    | cons y ys =>
      have hy : y ≠ '=' := by rw [hxl] at he; simpa using he
      rw [hxl] at hn
      simp [Py.markParam, Py.paramMarker, Py.sigStr, Py.hasPrefix, Py.dropChars, Py.sigOf, Py.splitBy, hxl,
        List.splitOn_eq_singleton hn, hk', hy]
      have := String.ofList_toList (s := x); rw [hxl] at this; simpa [String.ofList_cons] using this

/-! ### A parameter's marker: its name has no `,` and no leading `=` -/

theorem ncomma_ok {x : String} (h : okName x = true) : ',' ∉ x.toList := by
  intro hm; simp [okName, String.contains_char_eq, hm] at h

theorem neq_ok {x : String} (h : okName x = true) : x.toList.head? ≠ some '=' := by
  intro he
  have hs : x.startsWith "=" = true := by
    rw [String.startsWith_string_iff]
    cases hx : x.toList with
    | nil => simp [hx] at he
    | cons c cs =>
      simp [hx] at he; subst he
      exact ⟨cs, by simp [hx]⟩
  simp [okName, hs] at h

theorem ncomma_mangle_pv {C : List Scope} (hpv : ∀ c, priv C = some c → okName c = true) {a : String}
    (ha : ',' ∉ a.toList) : ',' ∉ (mangle (priv C) a).toList := by
  unfold mangle
  cases hp : priv C with
  | none => exact ha
  | some c =>
    simp only
    split
    · have hc := ncomma_ok (hpv c hp)
      have hd : ',' ∉ (c.dropWhile (· == '_')).toString.toList := by
        have e := @String.Slice.takeWhile_append_dropWhile _ (· == '_') _ _ _ c.toSlice
        intro hm; apply hc
        have e2 : (c.dropWhile (· == '_')).toString = (c.toSlice.dropWhile (· == '_')).copy := rfl
        rw [e2] at hm
        have : c.toList = (c.toSlice.takeWhile (· == '_')).copy.toList ++ (c.toSlice.dropWhile (· == '_')).copy.toList := by
          rw [← String.toList_append, e]; simp
        rw [this]; exact List.mem_append_right _ hm
      simp only [String.toList_append, List.mem_append, not_or]
      exact ⟨⟨by simp, hd⟩, ha⟩
    · exact ha

theorem neq_mangle_pv {C : List Scope} {a : String} (ha : a.toList.head? ≠ some '=') :
    (mangle (priv C) a).toList.head? ≠ some '=' := by
  unfold mangle
  cases priv C with
  | none => exact ha
  | some c =>
    simp only
    split
    · simp [String.toList_append]
    · exact ha

/-- A parameter's marker reads back its mangled name, kind and default (`$def`'s signature). -/
theorem markParam_ok {C : List Scope} (hpv : ∀ c, priv C = some c → okName c = true) {x : Name}
    (hx : okName x = true) (k : Py.PK) (d : Bool) :
    Py.markParam (.prim (Py.paramMarker (mangle (priv C) x) k d)) = some (mangle (priv C) x, k, d) :=
  markParam_param (ncomma_mangle_pv hpv (ncomma_ok hx)) (neq_mangle_pv (neq_ok hx)) k d


theorem markStar_pos : Py.markStar (.prim "$pos") = some false := by simp [Py.markStar]
theorem markStar_star : Py.markStar (.prim "$star") = some true := by simp [Py.markStar]
theorem markStar_c0 : Py.markStar (.prim "$c0") = some false := by simp [Py.markStar]
theorem markStar_c1 : Py.markStar (.prim "$c1") = some false := by simp [Py.markStar]
theorem markStar_nc : Py.markStar (.prim "$nc") = some false := by simp [Py.markStar]

/-- A gadget's record: the values, then as many markers. -/
theorem pairs_app {vs ms : List Val} (h : ms.length = vs.length) : Py.pairs (vs ++ ms) = some (ms.zip vs) := by
  have h2 : (vs ++ ms).length / 2 = vs.length := by simp [h]; omega
  simp only [Py.pairs, h2]
  rw [if_pos (by simp [h]; omega)]
  simp [List.drop_append, List.take_append]

end KC


/-! ## Changing what a continuation relation reads

A continuation relation holds again when more nodes were touched and the fresh names of the nodes
outside its budget read the same. -/

/-- The context `x` with other readings of fresh names and a larger history. -/
abbrev Cx.with (x : Cx) (rd own : Name → Option Val) (H : Label → Prop) : Cx := ⟨x.p, x.C, rd, own, H⟩

/-- Readings `rd'`, `own'` that agree with `rd`, `own` on the fresh names (of tags `tagOk`) of the
nodes outside `U`. -/
def Agree (U : Label → Prop) (rd own rd' own' : Name → Option Val) : Prop :=
  ∀ tag l, tagOk tag = true → ¬ U l → rd' (fresh tag l) = rd (fresh tag l) ∧ own' (fresh tag l) = own (fresh tag l)

/-- `rd`, `own` read like `x` the fresh names of the nodes outside `U`, and `H` holds more. -/
structure Ext (x : Cx) (rd own : Name → Option Val) (H U : Label → Prop) : Prop where
  H : ∀ l, x.H l → H l
  ag : Agree U x.rd x.own rd own

theorem Agree.mono {U U' : Label → Prop} {rd own rd' own' : Name → Option Val} (h : Agree U' rd own rd' own')
    (hU : ∀ l, U' l → U l) : Agree U rd own rd' own' :=
  fun t l ht hl => h t l ht fun h' => hl (hU l h')

theorem Agree.refl (U : Label → Prop) (rd own : Name → Option Val) : Agree U rd own rd own :=
  fun _ _ _ _ => ⟨rfl, rfl⟩

theorem Agree.trans {U : Label → Prop} {rd own rd1 own1 rd2 own2 : Name → Option Val}
    (h1 : Agree U rd own rd1 own1) (h2 : Agree U rd1 own1 rd2 own2) : Agree U rd own rd2 own2 :=
  fun t l ht hl => ⟨(h2 t l ht hl).1.trans (h1 t l ht hl).1, (h2 t l ht hl).2.trans (h1 t l ht hl).2⟩

section
variable {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop}

theorem Ext.rm {l : Label} (h : Ext x rd own H (Rm U l)) : Ext x rd own H U :=
  ⟨h.H, h.ag.mono fun _ h2 => h2.1⟩

theorem rm_self (U : Label → Prop) (l : Label) : ¬ Rm U l l := fun h => h.2 rfl

theorem Ext.rdl {l : Label} (h : Ext x rd own H (Rm U l)) (tag : String) {v : Val}
    (hv : x.rd (fresh tag l) = some v) (ht : tagOk tag = true := by decide) : rd (fresh tag l) = some v := by
  rw [(h.ag tag l ht (rm_self U l)).1]; exact hv

theorem Ext.ownl {l : Label} (h : Ext x rd own H (Rm U l)) (tag : String) {v : Val}
    (hv : x.own (fresh tag l) = some v) (ht : tagOk tag = true := by decide) : own (fresh tag l) = some v := by
  rw [(h.ag tag l ht (rm_self U l)).2]; exact hv

theorem Ext.rdn {l : Label} (h : Ext x rd own H U) (hl : ¬ U l) (tag : String) {v : Val}
    (hv : x.rd (fresh tag l) = some v) (ht : tagOk tag = true := by decide) : rd (fresh tag l) = some v := by
  rw [(h.ag tag l ht hl).1]; exact hv

theorem srcR_ext (h : Ext x rd own H U) {lt : Label} {src : PE} {v : Val} :
    SrcR x U lt src v → SrcR (x.with rd own H) U lt src v
  | .name hk ht hl hv => .name hk ht hl (h.rdn hl _ hv ht)
  | .item hl hv hi => .item hl (h.rdn hl _ hv (by decide)) hi

theorem augT_ext {l lt : Label} (h : Ext x rd own H (Rm U l)) {t : Sem.ATgt} {w : PyCore.Stmt}
    (ha : AugT x l lt t w) : AugT (x.with rd own H) l lt t w := by
  cases t with
  | name y => exact ha
  | attr ob a => exact ⟨h.rdl _ ha.1, ha.2⟩
  | item ob i => exact ⟨h.rdl _ ha.1, h.rdl _ ha.2.1, ha.2.2⟩

theorem partsR_with {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {l : Label} :
    ∀ {rest : List (Option Expr)} {ps : List PE}, PartsR x U l rest ps → PartsR (x.with rd own H) U l rest ps
  | [], [], h => h
  | a :: _, _ :: _, ⟨h1, h2⟩ => ⟨by cases a <;> exact h1, partsR_with h2⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

end

mutual
theorem KRel.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : KRel x U i K K' → KRel (x.with rd own H) U i K K'
  | .nil => .nil
  | .core k => .core (CoreK.ext h k)
  | .call k => .call (CallK.ext h k)
  | .cls k => .cls (ClsK.ext h k)
  | .comp k => .comp (CompK.ext h k)
  | .loop k => .loop (LoopK.ext h k)
  | .asg k => .asg (AsgK.ext h k)
  | .acc k => .acc (AccK.ext h k)
  | .misc k => .misc (MiscK.ext h k)
theorem CoreK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : CoreK x U i K K' → CoreK (x.with rd own H) U i K K'
  | .exprS k => .exprS (KRel.ext h k)
  | .binL ho g k => .binL ho g (KRel.ext h k)
  | .binR ho k => .binR ho (KRel.ext h k)
  | .seq hn hp g k => (CoreK.seq hn hp (g) (KRel.ext h k))
  | .seqNil => .seqNil
  | .ifS hn g1 g2 k => (CoreK.ifS hn (g1) (g2) (KRel.ext h k))
  | .ifST hn g1 g2 k => (CoreK.ifST hn (g1) (g2) (KRel.ext h k))
  | .whileS hn g1 g2 g3 k => (CoreK.whileS hn (g1) (g2) (g3) (KRel.ext h k))
  | .whileT hn g1 g2 g3 k => (CoreK.whileT hn (g1) (g2) (g3) (KRel.ext h k))
  | .loop hn g1 g2 g3 k => (CoreK.loop hn (g1) (g2) (g3) (KRel.ext h k))
  | .retS k => .retS (KRel.ext h k)
  | .tryE hn g1 g2 k => (CoreK.tryE hn (g1) (g2) (KRel.ext h k))
  | .catchS hn g1 g2 g3 hx k => (CoreK.catchS (ex := _) hn (g1) (g2) (g3) hx
      (KRel.ext h k))
  | .catchT hn g1 g2 g3 hx k => (CoreK.catchT (ex := _) hn (g1) (g2) (g3) hx
      (KRel.ext h k))
  | .handler hn hx k => .handler hn hx (KRel.ext h k)
  | .ifK g1 g2 k => (CoreK.ifK (g1) (g2) (KRel.ext h k))
  | .ifT g1 g2 k => (CoreK.ifT (g1) (g2) (KRel.ext h k))
  | .boolK (o := o) hH g k => (CoreK.boolK (o := o) (h.H _ hH) (g) (KRel.ext h k))
  | .boolT (o := o) (v := v) hH g k => (CoreK.boolT (o := o) (v := v) (h.H _ hH) (g) (KRel.ext h k))
  | .boolNil k => .boolNil (KRel.ext h k)
  | .walrusK hy k => .walrusK hy (KRel.ext h k)
  | .yieldK k => .yieldK (KRel.ext h k)
  | .native k => .native (KRel.ext h k)
  | .assignN hy k => .assignN hy (KRel.ext h k)
  | .decos k => .decos (KRel.ext h k)
theorem CallK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : CallK x U i K K' → CallK (x.with rd own H) U i K K'
  | .argStar k => .argStar (KRel.ext h k)
  | .argKw k => .argKw (KRel.ext h k)
  | .enterK k => .enterK (KRel.ext h k)
  | .evsCall g hl he h1 h2 hr k => .evsCall g hl he (fun a ha => h.H _ (h1 a ha)) (fun k' hk => h.H _ (h2 k' hk))
      (partsR_with hr) (KRel.ext h k)
  | .evsDefn hH g hd hl he hr k => .evsDefn (h.H _ hH) g hd hl he (partsR_with hr) (KRel.ext h k)
  | .evsLam hH g hl he hr k => .evsLam (h.H _ hH) g hl he (partsR_with hr) (KRel.ext h k)
theorem ClsK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : ClsK x U i K K' → ClsK (x.with rd own H) U i K K'
  | .clsEnd hy k => .clsEnd hy (KRel.ext h k)
  | .setAnn k => .setAnn (KRel.ext h k)
  | .evsCls hH g hd hl he h1 h2 hr hn gs k => .evsCls (h.H _ hH) g hd hl he (fun a ha => h.H _ (h1 a ha))
      (fun k' hk => h.H _ (h2 k' hk)) (partsR_with hr) hn gs (KRel.ext h k)
  | .argStarC hH g hd hn gs k => .argStarC (h.H _ hH) g hd hn gs (KRel.ext h k)
  | .argKwC hH g hd hn gs k => .argKwC (h.H _ hH) g hd hn gs (KRel.ext h k)
theorem CompK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : CompK x U i K K' → CompK (x.with rd own H) U i K K'
  | .compIt k => .compIt (KRel.ext h k)
  | .compCall k => .compCall (KRel.ext h k)
  | .compStart hC hk ha hl hU ho hr f1 f2 f3 g1 g2 g3 hn n1 n2 n3 n4 => (CompK.compStart (x := x.with rd own H) hC hk ha
      (h.H _ hl) hU (h.ownl _ ho) (h.rdl _ hr) f1 f2 f3 (g1) (g2) (g3) hn n1 n2 n3 n4)
  | .cAcc hC hr => (CompK.cAcc (x := x.with rd own H) hC (h.rdl _ hr))
  | .cNext (g := g) (iv := iv) (it := it) (n := n) hC hl hiv hr hg ha hH f1 f2 hu g1 g2 g3 g4 k => by
    have hr' : rd iv = some it := by
      rcases hiv with rfl | rfl
      · exact h.rdn (fun h' => hl h'.1) _ hr
      · exact h.rdl _ hr
    have := CompK.cNext (x := x.with rd own H) (n := n) hC hl hiv hr' (h.rdl _ hg)
      (fun hk => h.rdn (fun h' => hl h'.1) _ (ha hk)) (h.H _ hH) f1 f2 hu (g1) (g2)
      (g3) g4 (KRel.ext h.rm k)
    exact this
  | .cLoop (g := g) (iv := iv) (it := it) (n0 := n0) (n := n) hC hl hiv hr hg ha hH f1 f2 hu g1 g2 g3 g4 k => by
    have hr' : rd iv = some it := by
      rcases hiv with rfl | rfl
      · exact h.rdn (fun h' => hl h'.1) _ hr
      · exact h.rdl _ hr
    have := CompK.cLoop (x := x.with rd own H) (n0 := n0) (n := n) hC hl hiv hr' (h.rdl _ hg)
      (fun hk => h.rdn (fun h' => hl h'.1) _ (ha hk)) (h.H _ hH) f1 f2 hu (g1) (g2)
      (g3) g4 (KRel.ext h.rm k)
    exact this
  | .cConds hC hl hH ha f1 g1 g2 g3 hn k => (CompK.cConds (x := x.with rd own H) hC hl (h.H _ hH) (fun hk => h.rdn hl _ (ha hk))
      f1 (g1) (g2) (g3) hn (KRel.ext h k))
  | .cCond hC hl hH ha f1 g1 g2 g3 hn k => (CompK.cCond (x := x.with rd own H) hC hl (h.H _ hH) (fun hk => h.rdn hl _ (ha hk))
      f1 (g1) (g2) (g3) hn (KRel.ext h k))
  | .cCondT hC hl hH ha f1 g1 g2 g3 hn k => (CompK.cCondT (x := x.with rd own H) hC hl (h.H _ hH) (fun hk => h.rdn hl _ (ha hk))
      f1 (g1) (g2) (g3) hn (KRel.ext h k))
  | .cIter hC hl ha hH hU f1 f2 g1 g2 g3 g4 k => (CompK.cIter (x := x.with rd own H) hC hl (fun hk => h.rdn hl _ (ha hk)) (h.H _ hH) hU f1 f2
      (g1) (g2) (g3) g4 (KRel.ext h k))
  | .cIt hC hl ha hH hU f1 f2 g1 g2 g3 g4 k => (CompK.cIt (x := x.with rd own H) hC hl (fun hk => h.rdn hl _ (ha hk)) (h.H _ hH) hU f1 f2
      (g1) (g2) (g3) g4 (KRel.ext h k))
  | .cExpr k => .cExpr (KRel.ext h k)
  | .cElt k => .cElt (KRel.ext h k)
  | .cKey g k => (CompK.cKey (g) (KRel.ext h k))
  | .cVal k => .cVal (KRel.ext h k)
theorem LoopK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : LoopK x U i K K' → LoopK (x.with rd own H) U i K K'
  | .forIt hn hH hU hf g1 ht hT g2 g3 g4 k =>
    LoopK.forIt (x := x.with rd own H) hn (h.H _ hH) hU hf g1 ht hT g2 g3 g4 (KRel.ext h k)
  | .forStart hn hH hU hf g1 ht hT g2 g3 g4 k =>
    LoopK.forStart (x := x.with rd own H) hn (h.H _ hH) hU hf g1 ht hT g2 g3 g4 (KRel.ext h k)
  | .forNext hn hH hU hi hg hf g1 ht hT g2 g3 g4 k =>
    LoopK.forNext (x := x.with rd own H) hn (h.H _ hH) hU (h.rdl _ hi) (h.rdl _ hg) hf g1 ht hT g2 g3 g4 (KRel.ext h.rm k)
  | .forLoop hn hH hU hi hg hf g1 ht hT g2 g3 g4 k =>
    LoopK.forLoop (x := x.with rd own H) hn (h.H _ hH) hU (h.rdl _ hi) (h.rdl _ hg) hf g1 ht hT g2 g3 g4 (KRel.ext h.rm k)
theorem AsgK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : AsgK x U i K K' → AsgK (x.with rd own H) U i K K'
  | .assignK hU hf g hT k => (AsgK.assignK (x := x.with rd own H) hU hf (g) hT (KRel.ext h k))
  | .stManyT hr g hT k => (AsgK.stManyT (x := x.with rd own H) (h.rdl _ hr) (g) hT (KRel.ext h.rm k))
  | .stAttr hH hs k => .stAttr (h.H _ hH) (srcR_ext h hs) (KRel.ext h k)
  | .stSubL hH g hs k => (AsgK.stSubL (x := x.with rd own H) (h.H _ hH) (g) (srcR_ext h hs) (KRel.ext h k))
  | .stSubR hH hs k => .stSubR (h.H _ hH) (srcR_ext h hs) (KRel.ext h k)
  | .stUnpack hH hU hf g hT k => .stUnpack (h.H _ hH) hU hf g hT (KRel.ext h k)
  | .stManyU hr hl g hT k => (AsgK.stManyU (x := x.with rd own H) (h.rdl _ hr) hl g hT (KRel.ext h.rm k))
  | .annK hH hU hf g hs ha ho k => .annK (h.H _ hH) hU hf g hs ha ho (KRel.ext h k)
  | .annA h1 h2 ha ho ht k => .annA (h.H _ h1) (h.H _ h2) ha ho ht (KRel.ext h.rm k)
  | .annV h1 h2 hi ho ht k => .annV (h.H _ h1) (h.H _ h2) hi ho ht (KRel.ext h k)
  | .annE h1 h2 hi hn ho ht k => .annE (h.H _ h1) (h.H _ h2) hi hn ho ht (KRel.ext h k)
  | .exprBlk ht k => .exprBlk (ht.imp id fun ⟨l, t, hl, ht⟩ => ⟨l, t, h.H _ hl, ht⟩)
      (KRel.ext h k)
  | .evsDrop1 k => .evsDrop1 (KRel.ext h k)
  | .evsDropR hH hr k => .evsDropR (h.H _ hH) (partsR_with hr) (KRel.ext h k)
  | .augN h1 h2 hU hf hy g k => (AsgK.augN (x := x.with rd own H) (h.H _ h1) (h.H _ h2) hU hf hy (g) (KRel.ext h k))
  | .augAttr h1 h2 hU hf ha g k => (AsgK.augAttr (x := x.with rd own H) (h.H _ h1) (h.H _ h2) hU hf ha (g) (KRel.ext h k))
  | .augAttrV h1 h2 hU ho hf ha g k =>
    (AsgK.augAttrV (x := x.with rd own H) (h.H _ h1) (h.H _ h2) hU (h.rdl _ ho) hf ha (g) (KRel.ext h.rm k))
  | .augSubL h1 h2 hU hf g1 g2 k => (AsgK.augSubL (x := x.with rd own H) (h.H _ h1) (h.H _ h2) hU hf (g1) (g2) (KRel.ext h k))
  | .augSubI h1 h2 hU ho hf g k =>
    (AsgK.augSubI (x := x.with rd own H) (h.H _ h1) (h.H _ h2) hU (h.rdl _ ho) hf (g) (KRel.ext h.rm k))
  | .augSubV h1 h2 hU ho hk hf g k =>
    (AsgK.augSubV (x := x.with rd own H) (h.H _ h1) (h.H _ h2) hU (h.rdl _ ho) (h.rdl _ hk) hf (g) (KRel.ext h.rm k))
  | .augR (op := op) (old := old) h1 h2 hU hf ha k =>
    .augR (op := op) (old := old) (h.H _ h1) (h.H _ h2) hU hf (augT_ext h ha) (KRel.ext h.rm k)
  | .augW h1 h2 hU hf ha k => .augW (h.H _ h1) (h.H _ h2) hU hf (augT_ext h ha) (KRel.ext h.rm k)
  | .delMany g hds hd k => AsgK.delMany (x := x.with rd own H) g hds hd (KRel.ext h k)
  | .delAttr k => .delAttr (KRel.ext h k)
  | .delSubL g k => (AsgK.delSubL g (KRel.ext h k))
  | .delSubR k => .delSubR (KRel.ext h k)
theorem AccK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : AccK x U i K K' → AccK (x.with rd own H) U i K K'
  | .unK k => .unK (KRel.ext h k)
  | .attrK k => .attrK (KRel.ext h k)
  | .subL g k => (AccK.subL (g) (KRel.ext h k))
  | .subR k => .subR (KRel.ext h k)
  | .fmtV (c := c) g k => (AccK.fmtV (c := c) (g) (KRel.ext h k))
  | .fmtC g k => (AccK.fmtC (g) (KRel.ext h k))
  | .fmtS k => .fmtS (KRel.ext h k)
  | .evsOp hH hr k => .evsOp (h.H _ hH) (partsR_with hr) (KRel.ext h k)
  | .evsList g hl he ho hr k => .evsList g hl he (fun e he => h.H _ (ho e he)) (partsR_with hr) (KRel.ext h k)
  | .evsTuple g hl he ho hr k => .evsTuple g hl he (fun e he => h.H _ (ho e he)) (partsR_with hr) (KRel.ext h k)
  | .evsSet g hl he ho hr k => .evsSet g hl he (fun e he c hc => h.H _ (ho e he c hc)) (partsR_with hr) (KRel.ext h k)
theorem MiscK.ext {x : Cx} {rd own : Name → Option Val} {H U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)}
    {K' : List (PyCore.Kont σ)} (h : Ext x rd own H U) : MiscK x U i K K' → MiscK (x.with rd own H) U i K K'
  | .cmpL1 g hq k => (MiscK.cmpL1 (g) hq (KRel.ext h k))
  | .cmpLm (o := o) hH g hl hq hd k => (MiscK.cmpLm (o := o) (h.H _ hH) (g) hl hq hd (KRel.ext h k))
  | .cmpR1 hq k => .cmpR1 hq (KRel.ext h k)
  | .cmpRm (a := a) (o := o) hH hU g hl hn hq hd k =>
    (MiscK.cmpRm (a := a) (o := o) (h.H _ hH) hU (g) hl hn hq hd (KRel.ext h k))
  | .cmpONil k => .cmpONil (KRel.ext h k)
  | .cmpO hH ho g hl hn hq hd k => (MiscK.cmpO (h.H _ hH) (h.ownl _ ho) (g) hl hn hq hd (KRel.ext h.rm k))
  | .cmpT (r := r) hH ho g hl hn hq hd k => (MiscK.cmpT (r := r) (h.H _ hH) (h.ownl _ ho) (g) hl hn hq hd (KRel.ext h.rm k))
  | .assertK hH g k => (MiscK.assertK (h.H _ hH) (g) (KRel.ext h k))
  | .assertT hH g k => (MiscK.assertT (h.H _ hH) (g) (KRel.ext h k))
  | .assertM k => .assertM (KRel.ext h k)
  | .evsRaise k => .evsRaise (KRel.ext h k)
  | .raiseCn k => .raiseCn (KRel.ext h k)
  | .evsRaiseFrom g k => (MiscK.evsRaiseFrom (g) (KRel.ext h k))
  | .evsRaiseFrom2 k => .evsRaiseFrom2 (KRel.ext h k)
  | .raiseCs k => .raiseCs (KRel.ext h k)
  | .raiseW k => .raiseW (KRel.ext h k)
  | .impMany (l := l) hy ha hb k => (MiscK.impMany (l := l) hy ha hb (KRel.ext h k))
  | .impMod hU hf ha hd k => (MiscK.impMod hU hf ha hd (KRel.ext h k))
  | .impNext hr ha hd k => (MiscK.impNext (h.rdl _ hr) ha hd (KRel.ext h.rm k))
  | .starStore k => .starStore (KRel.ext h k)
  | .yfK k => .yfK (KRel.ext h k)
  | .yfIt k => .yfIt (KRel.ext h k)
  | .yfN hd k => .yfN hd (KRel.ext h k)
end


/-! ## More nodes touched before -/

theorem all2_mono {α β} {r r' : α → β → Prop} (hr : ∀ a b, r a b → r' a b) :
    ∀ {as : List α} {bs : List β}, PyCore.All2 r as bs → PyCore.All2 r' as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨hr _ _ h1, all2_mono hr h2⟩
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem optRel_mono {α β} {r r' : α → β → Prop} (hr : ∀ a b, r a b → r' a b) :
    ∀ {a : Option α} {b : Option β}, PyCore.OptRel r a b → PyCore.OptRel r' a b
  | some _, some _, h => hr _ _ h
  | none, none, _ => trivial
  | some _, none, h | none, some _, h => h.elim


section
variable {H H' : Label → Prop} (hH : ∀ l, H l → H' l)
include hH

theorem ext_H (x : Cx) (U : Label → Prop) (h : x.H = H) : Ext x x.rd x.own H' U :=
  ⟨fun l hl => hH l (h ▸ hl), Agree.refl _ _ _⟩

theorem FRel.mono_H {rd own : Name → Option Val} {f : Sem.Frame σ} {f' : PyCore.Frame σ}
    (h : FRel p H rd own f f') : FRel p H' rd own f f' := by
  obtain ⟨U, i, hc, hk⟩ := h.code
  exact ⟨h.toFRel0, fun S C e => hH _ (h.hl S C e), U, i, hc, KRel.ext (ext_H hH _ U rfl) hk⟩

theorem Special.mono_H {x : Cx} (hx : x.H = H) {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} {c' : PyCore.Ctrl σ}
    {k' : List (PyCore.Kont σ)} (h : Special x c k c' k') : Special (x.with x.rd x.own H') c k c' k' := by
  cases h with
  | genComp hC h1 hn n1 n2 n3 n4 hr ho f1 f2 g1 g2 g3 => exact .genComp hC (hH _ (hx ▸ h1)) hn n1 n2 n3 n4 hr ho f1 f2 g1 g2 g3
  | genFn hC hq g => exact .genFn hC (fun q h' => hH _ (hx ▸ hq q h')) g
  | genLam hC hq g => exact .genLam hC (fun q h' => hH _ (hx ▸ hq q h')) g
  | yf hd hk => exact .yf hd (KRel.ext (ext_H hH _ _ hx) hk)

theorem GRel.mono_H {gl cs} {g : Sem.GSt σ} {g' : PyCore.GSt σ} (h : GRel p H gl cs g g') :
    GRel p H' gl cs g g' := by
  cases h with
  | susp h => exact .susp (h.mono_H hH)
  | special h0 hl hs => exact .special h0 (fun S C e => hH _ (hl S C e)) (Special.mono_H hH rfl hs)
  | running => exact .running
  | done => exact .done

theorem ORel.mono_H {gl cs} {a : Sem.Obj σ} {b : PyCore.Obj σ} (h : ORel p H gl cs a b) :
    ORel p H' gl cs a b := by
  cases h with
  | clo h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .clo h1 h2 h3 h4 h5 h6 (hH _ h7) (fun q hq => hH _ (h8 q hq)) h9 h10
  | gen h => exact .gen (h.mono_H hH)

theorem CRel.mono_H {s : Sem.Config σ} {t : PyCore.Config σ} (h : CRel p H s t) : CRel p H' s t :=
  ⟨all2_mono (fun _ _ hf => hf.mono_H hH) h.stack, fun o => optRel_mono (fun _ _ ho => ho.mono_H hH) (h.objs o),
    h.cells, h.glob, h.out, h.next, h.res, h.st, h.wait, h.ids, h.enter⟩

end

/-! ## Pending `enterK` items

A `**` parameter's dictionary is made before its function is entered (`Kont.enterK o …`); the
address `o` holds no comprehension's function object (`CRel.enter`), so that both runs enter it alike
(or are both stuck). -/

section
variable {O O' : Std.HashMap Nat (Sem.Obj σ)}

theorem esub_refl {K : List (Sem.Kont σ)} : EnterSub K K := fun _ _ _ h => h

theorem esub_cons {k K : List (Sem.Kont σ)} {a : Sem.Kont σ} (h : K = a :: k) : EnterSub k K :=
  fun _ _ _ hm => h ▸ List.mem_cons_of_mem _ hm

theorem EnterOk.sub {k K : List (Sem.Kont σ)} (h : EnterOk O K) (hs : EnterSub k K) : EnterOk O k :=
  fun o b kx hm => h o b kx (hs o b kx hm)

theorem EnterOk.mono {K : List (Sem.Kont σ)} (h : EnterOk O K) (hO : ∀ o, NoCompObj O o → NoCompObj O' o) :
    EnterOk O' K :=
  fun o b kx hm => hO o (h o b kx hm)

theorem enterOk_nil : EnterOk O ([] : List (Sem.Kont σ)) := fun _ _ _ h => nomatch h

/-- An object written at a free address, or one that is no function object written anywhere. -/
def InsOk (O : Std.HashMap Nat (Sem.Obj σ)) (n : Nat) (v : Sem.Obj σ) : Prop :=
  O[n]? = none ∨ ∀ S C cl κ kd dflt, v ≠ .clo S C cl κ kd dflt

theorem insOk_gen {n : Nat} (g : Sem.GSt σ) : InsOk O n (.gen g) := .inr fun _ _ _ _ _ _ h => nomatch h

theorem ncomp_ins {n : Nat} {v : Sem.Obj σ} (hn : InsOk O n v) (o : Nat) (h : NoCompObj O o) :
    NoCompObj (O.insert n v) o := by
  obtain ⟨h1, h2⟩ := h
  by_cases e : n = o
  · subst e
    rcases hn with hn | hn
    · rw [hn] at h1; cases h1
    · refine ⟨by simp, fun S C cl κ kd dflt hv => ?_⟩
      simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq] at hv
      exact absurd hv (hn S C cl κ kd dflt)
  · exact ⟨by simp [Std.HashMap.getElem?_insert, e, h1], fun S C cl κ kd dflt hv => h2 S C cl κ kd dflt
      (by simpa [Std.HashMap.getElem?_insert, e] using hv)⟩

/-- The top frame's continuation changes to one with fewer pending `enterK` items. -/
theorem EnterInv.top {f : Sem.Frame σ} {fs : List (Sem.Frame σ)} (h : EnterInv O (f :: fs)) (c : Sem.Ctrl σ)
    {k : List (Sem.Kont σ)} (he : EnterSub k f.kont) : EnterInv O ({ f with ctrl := c, kont := k } :: fs) :=
  ⟨fun g hg => (List.mem_cons.1 hg).elim (fun e => e ▸ (h.1 f List.mem_cons_self).sub he)
    (fun hg => h.1 g (List.mem_cons_of_mem _ hg)), h.2⟩

/-- An object written at an address with no function object, its suspended frame's (if any) items
named function objects. -/
theorem EnterInv.ins {st : List (Sem.Frame σ)} (h : EnterInv O st) {n : Nat} {v : Sem.Obj σ}
    (hn : InsOk O n v) (hv : ∀ g, v = .gen (.susp g) → EnterOk O g.kont) : EnterInv (O.insert n v) st := by
  refine ⟨fun g hg => (h.1 g hg).mono (ncomp_ins hn), fun o g ho => ?_⟩
  simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at ho
  split at ho
  · cases ho; exact (hv g rfl).mono (ncomp_ins hn)
  · exact (h.2 o g ho).mono (ncomp_ins hn)

theorem EnterInv.tail {st : List (Sem.Frame σ)} {g : Sem.Frame σ} (h : EnterInv O (g :: st)) : EnterInv O st :=
  ⟨fun x hx => h.1 x (List.mem_cons_of_mem _ hx), h.2⟩

/-- The top frame's control changes, its continuation stays. -/
theorem EnterInv.ctrl {st : List (Sem.Frame σ)} {g : Sem.Frame σ} (h : EnterInv O (g :: st)) (c : Sem.Ctrl σ) :
    EnterInv O ({ g with ctrl := c } :: st) :=
  ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ h.1 g List.mem_cons_self)
    (fun hx => h.1 x (List.mem_cons_of_mem _ hx)), h.2⟩

end

/-- `EnterSub k K` for the continuations of a step: `k` is `K`, or items pushed on (part of) it. -/
macro "esub" : tactic => `(tactic| first
  | exact esub_refl
  | (intro _ _ _ hm
     try simp only [List.mem_cons, List.mem_append, reduceCtorEq, false_or, or_false, List.not_mem_nil] at hm
     all_goals first | exact hm | simp_all))

/-! ## Building related configurations -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem FRel0.upd {g : Sem.Frame σ} {g' : PyCore.Frame σ} (h : FRel0 g g') (c : Sem.Ctrl σ)
    (k : List (Sem.Kont σ)) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    FRel0 { g with ctrl := c, kont := k } { g' with ctrl := c', kont := k' } :=
  ⟨h.id, h.chain, h.cls, h.pcls, h.kind, h.kc, h.κ, h.κa, h.ns, h.kok⟩

/-- The top frame changes (same id and kind), the objects and `next` stay. -/
theorem Ids.top' {t1 : PyCore.Config σ} {g' : PyCore.Frame σ} (h : Ids t) (ht : t.stack = f' :: fs')
    (ht1 : t1.stack = g' :: fs') (ho : t1.objs = t.objs) (hn : t1.next = t.next) (hid : g'.id = f'.id)
    (hk : g'.kind = f'.kind) : Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  refine ⟨by rw [ht1]; simpa [hid] using h1, fun g hg => ?_, fun o b hb => ?_, fun o g ho' => ?_,
    fun g hg o hgo => ?_, fun g hg hm => ?_, fun o g ho' => ?_⟩
  · rw [ht1, List.mem_cons] at hg; rw [hn]
    rcases hg with rfl | hg
    · rw [hid]; exact h2 _ (by simp)
    · exact h2 _ (by simp [hg])
  · rw [hn]; exact h3 o b (by simpa [pObj, ho] using hb)
  · obtain ⟨e, hne⟩ := h4 o g (by simpa [pObj, ho] using ho')
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
  · exact h7 o g (by simpa [pObj, ho] using ho')

theorem Ids.top {g' : PyCore.Frame σ} (h : Ids t) (ht : t.stack = f' :: fs') (hid : g'.id = f'.id)
    (hk : g'.kind = f'.kind) : Ids { t with stack := g' :: fs' } :=
  h.top' ht rfl rfl rfl hid hk

/-- The top frames' control and continuation change. -/
theorem At.set (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i k k') (he : EnterSub k f.kont := by esub) :
    CRel p H { s with stack := { f with ctrl := c, kont := k } :: fs }
      { t with stack := { f' with ctrl := c', kont := k' } :: fs' } := by
  have hst := A.r.stack
  rw [A.hs, A.ht] at hst
  have hen := A.r.enter; rw [A.hs] at hen
  exact ⟨⟨⟨A.hf.toFRel0.upd c k c' k', A.hf.hl, U, i, hc, hk⟩, hst.2⟩, A.r.objs, A.r.cells, A.r.glob, A.r.out,
    A.r.next, A.r.res, A.r.st, fun x hx => A.r.wait x (by rw [A.hs]; exact hx), A.r.ids.top A.ht rfl rfl,
    hen.top c he⟩

/-- The top frame's pending `enterK` items name addresses with no comprehension's function object. -/
theorem At.etop (A : At p H s t f fs f' fs') : EnterOk s.objs f.kont :=
  A.r.enter.1 f (by rw [A.hs]; exact List.mem_cons_self)

/-- `At.set` for a continuation with new pending `enterK` items (a call's `**` dictionary). -/
theorem At.setE (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i k k') (hE : EnterOk s.objs k) :
    CRel p H { s with stack := { f with ctrl := c, kont := k } :: fs }
      { t with stack := { f' with ctrl := c', kont := k' } :: fs' } := by
  have hst := A.r.stack
  rw [A.hs, A.ht] at hst
  have hen := A.r.enter; rw [A.hs] at hen
  exact ⟨⟨⟨A.hf.toFRel0.upd c k c' k', A.hf.hl, U, i, hc, hk⟩, hst.2⟩, A.r.objs, A.r.cells, A.r.glob, A.r.out,
    A.r.next, A.r.res, A.r.st, fun x hx => A.r.wait x (by rw [A.hs]; exact hx), A.r.ids.top A.ht rfl rfl,
    ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => by rw [e]; exact hE)
      (fun hx => hen.1 x (List.mem_cons_of_mem _ hx)), hen.2⟩⟩

theorem seen_of {zs : List (Sem.Config σ)} {l : Label} (h : H l) : Seen (Touch p) H zs l := .inl h

theorem crelI_seen {zs : List (Sem.Config σ)} {s1 : Sem.Config σ} {t1 : PyCore.Config σ} (h : CRel p H s1 t1) :
    CRelI p (Seen (Touch p) H zs) s1 t1 :=
  .inl (h.mono_H fun _ => seen_of)

theorem CRelI.mono_H {H H' : Label → Prop} (hH : ∀ l, H l → H' l) {s : Sem.Config σ} {t : PyCore.Config σ} :
    CRelI p H s t → CRelI p H' s t
  | .inl h => .inl (h.mono_H hH)
  | .inr (.inl h) => .inr (.inl h)
  | .inr (.inr ⟨f, fs, f', fs', g, v, K', hs, ht, hc, .inl ⟨h1, h2, h3, h4⟩⟩) =>
    .inr (.inr ⟨f, fs, f', fs', g, v, K', hs, ht, hc, .inl ⟨h1, h2, h3, h4.mono_H hH⟩⟩)
  | .inr (.inr ⟨f, fs, f', fs', g, v, K', hs, ht, hc, .inr ⟨o, g0, h1, h2, h3, h4, h5, h6⟩⟩) =>
    .inr (.inr ⟨f, fs, f', fs', g, v, K', hs, ht, hc, .inr ⟨o, g0, h1, h2, h3, h4, h5, h6.mono_H hH⟩⟩)

instance : HMono (CRelI (σ := σ) p) := ⟨fun hH h => h.mono_H hH⟩

/-- Both runs step; the relation reached holds with the touches of the Surf configurations on the way
(`goal_t`: also with those of the configuration reached). -/
theorem goal_t {s1 : Sem.Config σ} {t1 : PyCore.Config σ} {xs ys}
    (pa : Path (Sem.step I) s s1 xs) (hxs : xs ≠ []) (pb : Path (PyCore.step I) t t1 ys) (hys : ys ≠ [])
    (hr : CRelI p (Seen (Touch p) H (s1 :: xs)) s1 t1) (hc : Cover (Touch p) pfocus H (s1 :: xs) ys) : Goal I p H s t :=
  Or.inr (Or.inl ⟨s1, t1, xs, ys, pa, hxs, pb, hys, hr, hc⟩)

theorem goal_b {s1 : Sem.Config σ} {t1 : PyCore.Config σ} {xs ys}
    (pa : Path (Sem.step I) s s1 xs) (hxs : xs ≠ []) (pb : Path (PyCore.step I) t t1 ys) (hys : ys ≠ [])
    (hr : CRelI p (Seen (Touch p) H xs) s1 t1) (hc : Cover (Touch p) pfocus H (s1 :: xs) ys) : Goal I p H s t :=
  goal_t pa hxs pb hys (hr.mono_H (seen_sub fun z hz => List.mem_cons_of_mem _ hz)) hc

/-- A simulation step in which neither run stutters alone: both end, or both step (the store lemmas). -/
def GoalS (I : Py.Interp σ) (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) : Prop :=
  (∃ a' b' xs ys, Path (Sem.step I) s a' xs ∧ Sem.step I a' = none ∧ Path (PyCore.step I) t b' ys ∧
      PyCore.step I b' = none ∧ Fin a' b' ∧ Cover (Touch p) pfocus H (a' :: xs) (b' :: ys)) ∨
  (∃ a' b' xs ys, Path (Sem.step I) s a' xs ∧ xs ≠ [] ∧ Path (PyCore.step I) t b' ys ∧ ys ≠ [] ∧
      CRelI p (Seen (Touch p) H (a' :: xs)) a' b' ∧ Cover (Touch p) pfocus H (a' :: xs) ys)

theorem GoalS.goal {s : Sem.Config σ} {t : PyCore.Config σ} : GoalS I p H s t → Goal I p H s t
  | .inl h => .inl h
  | .inr h => .inr (.inl h)

theorem goalS_b {s1 : Sem.Config σ} {t1 : PyCore.Config σ} {xs ys}
    (pa : Path (Sem.step I) s s1 xs) (hxs : xs ≠ []) (pb : Path (PyCore.step I) t t1 ys) (hys : ys ≠ [])
    (hr : CRelI p (Seen (Touch p) H xs) s1 t1) (hc : Cover (Touch p) pfocus H (s1 :: xs) ys) : GoalS I p H s t :=
  .inr ⟨s1, t1, xs, ys, pa, hxs, pb, hys, hr.mono_H (seen_sub fun z hz => List.mem_cons_of_mem _ hz), hc⟩

theorem Path.start_mem {α} {f : α → Option α} {a b : α} {xs : List α} (h : Path f a b xs) : a ∈ b :: xs := by
  cases h with
  | nil => exact List.mem_cons_self
  | cons => exact List.mem_cons_of_mem _ List.mem_cons_self

/-- A step whose relations and covers count the touches of its start `s` is one at the history before `s`
(the runs' paths start at `s`). -/
theorem GoalS.unseen {s : Sem.Config σ} {t : PyCore.Config σ} (h : GoalS I p (Seen (Touch p) H [s]) s t) :
    GoalS I p H s t := by
  have key : ∀ {zs : List (Sem.Config σ)}, s ∈ zs → ∀ l, Seen (Touch p) (Seen (Touch p) H [s]) zs l →
      Seen (Touch p) H zs l := fun hs l h' => by
    rw [seen_cons] at h'
    exact seen_mono (fun z hz => (List.mem_cons.1 hz).elim (fun e => e ▸ hs) id) h'
  rcases h with ⟨a', b', xs, ys, pa, ha, pb, hb, hf, hc⟩ | ⟨a', b', xs, ys, pa, hxs, pb, hys, hr, hc⟩
  · exact .inl ⟨a', b', xs, ys, pa, ha, pb, hb, hf, hc.mono (key pa.start_mem)⟩
  · exact .inr ⟨a', b', xs, ys, pa, hxs, pb, hys, hr.mono_H (key pa.start_mem), hc.mono (key pa.start_mem)⟩

/-- One step on each side that changes only the top frame's control and continuation. -/
theorem At.go11 (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := k } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with ctrl := c', kont := k' } :: fs' })
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i k k')
    (hcov : ∀ x, pfocus t = some x → Touch p s (x / 64)) (he : EnterSub k f.kont := by esub) : Goal I p H s t :=
  goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen (A.set hc hk he))
    (fun y hy x hx => by simp at hy; subst hy; exact .inr ⟨s, by simp, hcov x hx⟩)

theorem At.mono (A : At p H s t f fs f' fs') {H' : Label → Prop} (hH : ∀ l, H l → H' l) : At p H' s t f fs f' fs' :=
  ⟨A.r.mono_H hH, A.hs, A.ht, A.hf.mono_H hH⟩

/-- A continuation relation in a larger history. -/
theorem KRel.seen {zs : List (Sem.Config σ)} {rd own : Name → Option Val} {U : Label → Prop} {i : Bool}
    {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} (hk : KRel (cx p H rd own f) U i K K') :
    KRel (cx p (Seen (Touch p) H zs) rd own f) U i K K' :=
  KRel.ext (ext_H (fun _ => seen_of) _ U rfl) hk

/-- `At.go11` with the continuation related in the history that has `s`'s touches (for an item
recording a node that `s` touches). -/
theorem At.go11T (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := k } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with ctrl := c', kont := k' } :: fs' })
    (hc : CR p f.chain U i c c') (hk : KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U i k k')
    (hcov : ∀ x, pfocus t = some x → Touch p s (x / 64)) (he : EnterSub k f.kont := by esub) : Goal I p H s t :=
  goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (.inl ((A.mono fun _ => seen_of).set hc hk he))
    (fun y hy x hx => by simp at hy; subst hy; exact .inr ⟨s, by simp, hcov x hx⟩)

theorem pfocus_le {t : PyCore.Config σ} {x : Label} (h : pfocus t = some x) : PyCore.focus t = some x := by
  unfold pfocus at h; split at h
  · rename_i y hy; split at h <;> simp_all
  · cases h

theorem cov_ev (A : At p H s t f fs f' fs') {e : Expr} {e' : PyCore.Expr} (hc : f.ctrl = .ev e)
    (hc' : f'.ctrl = .ev e') (hl : e'.label / 64 = Sem.Expr.lbl e) :
    ∀ x, pfocus t = some x → Touch p s (x / 64) := by
  intro x hx
  have hx := pfocus_le hx
  simp [PyCore.focus, A.ht, hc'] at hx
  left; simp [Sem.focus, A.hs, hc, ← hx, hl]

theorem cov_none (A : At p H s t f fs f' fs') (h : PyCore.focus t = none) :
    ∀ x, pfocus t = some x → Touch p s (x / 64) := by
  intro x hx; rw [pfocus_le hx] at h; cases h

theorem fin_stuck (A : At p H s t f fs f' fs') (h1 : Sem.step I s = none) (h2 : PyCore.step I t = none)
    (hcov : ∀ x, pfocus t = some x → Touch p s (x / 64)) : Goal I p H s t := by
  refine Or.inl ⟨s, t, [], [], .nil _, h1, .nil _, h2, ?_, ?_⟩
  · simp [Fin, Sem.outcome, PyCore.outcome, A.hs, A.ht, OCorr, A.r.out, A.r.st]
  · intro y hy x hx; simp at hy; subst hy; exact .inr ⟨s, by simp, hcov x hx⟩

end

@[simp] theorem r0_e (l : Label) : R0.e l = none := rfl
@[simp] theorem r0_s (l : Label) : R0.s l = none := rfl
@[simp] theorem r0_h (l : Label) : R0.h l = none := rfl

theorem GoodE.of {C : List Scope} {U : Label → Prop} {e e0 : Expr} (h : GoodE p C U e0)
    (hs : ∀ x, x ∈ itemsE C e → x ∈ itemsE C e0)
    (ht : ∀ x, x ∈ PyCore.itemsE R0 (trChain C) (trE C e) → x ∈ PyCore.itemsE R0 (trChain C) (trE C e0))
    (hok : okE e0 = true → okE e = true) (hu : ∀ l ∈ labelsE e, l ∈ labelsE e0)
    (hnd : (labelsE e0).Nodup → (labelsE e).Nodup) (htc : ∀ x, x ∈ touchE e → x ∈ touchE e0) : GoodE p C U e :=
  ⟨fun x hx => h.s x (hs x hx), fun x hx => h.t x (ht x hx), hok h.ok, fun l hl => h.u l (hu l hl), h.pv, hnd h.nd,
    fun x hx => h.tch x (htc x hx)⟩

macro "gd" : tactic => `(tactic| (intro x hx; simp_all [itemsE, itemsEs, itemsO, trE, trO, trEs,
  PyCore.itemsE, cc, ccR, recR, List.foldl]))
macro "gok" : tactic => `(tactic| (intro h; simp_all [okE, okEs, okO]))
macro "gl" : tactic => `(tactic| (intro x hx; simp_all [labelsE, labelsEs, labelsO]))
macro "gnd" : tactic => `(tactic| (intro h; simp_all [labelsE, labelsEs, labelsO, List.nodup_cons, List.nodup_append]))
macro "gtc" : tactic => `(tactic| (intro x hx; simp_all [touchE, touchEs, touchO, touchKs, touchDs, touchPs, touchGs]))
macro "subg" : tactic => `(tactic| exact GoodE.of ‹_› (by gd) (by gd) (by gok) (by gl) (by gnd) (by gtc))

theorem sub_div (l k : Nat) (hk : k < 64) : sub l k / 64 = l := by
  show (64 * l + k) / 64 = l; omega

theorem lbl_eq : ∀ e : Expr, Sem.Expr.lbl e = e.label := by
  intro e; cases e <;> rfl

theorem constK_of {k : String} (h : (!k.startsWith "$") = true) (ks : List (PyCore.Kont σ)) :
    PyCore.constK I k ks = (.val (Py.constVal I k), ks) := by
  have h1 : k ≠ "$stop" := by rintro rfl; simp at h
  have h2 : k ≠ "$any" := by rintro rfl; simp at h
  unfold PyCore.constK; split <;> simp [h1, h2]

/-! ## Places, reads -/

def pl : Sem.Place → PyCore.Place
  | .glob x => .glob x
  | .ns x => .ns x
  | .cell a => .cell a

def snm : Sem.Place → Name
  | .glob x | .ns x => x
  | .cell a => a.2

def pnm : PyCore.Place → Name
  | .glob x | .ns x => x
  | .cell a => a.2

theorem cls_eq {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {x : Name} (hx : ¬ Dot x) :
    f'.cls x = f.cls x := by
  rw [hf.pcls, hf.chain, hf.cls, cls_tr (not_fresh hx)]

theorem place_eq {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {x : Name} (hx : ¬ Dot x) :
    PyCore.place f' x = (Sem.place f x).map pl := by
  simp only [PyCore.place, Sem.place, cls_eq hf hx, hf.kind, hf.id, hf.κ x hx]
  cases f.cls x <;> cases f.kind <;> simp [fk, pl] <;> cases f.κ x <;> simp [pl]

theorem place_nm {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {x : Name} {q : Sem.Place}
    (h : Sem.place f x = some q) : snm q = x := by
  simp only [Sem.place] at h
  split at h
  · cases h; rfl
  · split at h <;> cases h <;> rfl
  · cases hk : f.κ x with
    | none => simp [hk] at h
    | some a => simp [hk] at h; subst h; exact hf.κa x a hk

theorem lookup_drop {α} (y : Name) (hy : ¬ Dot y) :
    ∀ ns : List (Name × α), (ns.filter fun q => !q.1.startsWith ".").lookup y = ns.lookup y
  | [] => rfl
  | (k, v) :: ns => by
    have ih := lookup_drop y hy ns
    by_cases hk : k.startsWith "." = true
    · have : (y == k) = false := by
        rw [beq_eq_false_iff_ne]; rintro rfl; exact hy ((startsWith_dot _).1 hk)
      simp [List.filter, hk, List.lookup, this, ih]
    · simp [List.filter, hk, List.lookup, ih]

theorem drop_lookup {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {y : Name} (hy : ¬ Dot y) :
    f'.ns.lookup y = f.ns.lookup y := by
  rw [← hf.ns, PyCore.dropReserved, lookup_drop y hy]

theorem lookupGlobal_eq {s : Sem.Config σ} {t : PyCore.Config σ} (hr : ∀ x, ¬ Dot x → pGlob t x = sGlob s x)
    {y : Name} (hy : ¬ Dot y) : PyCore.lookupGlobal I t y = Sem.lookupGlobal I s y := by
  simp only [PyCore.lookupGlobal, Sem.lookupGlobal]
  have := hr y hy; simp only [pGlob, sGlob] at this; rw [this]; rfl

mutual
theorem inl_go {x : Name} (hx : ¬ Dot x) : ∀ C : List Scope, KOk C →
    PyCore.inlinedLocal.go x (trChain C) = Surf.inlinedLocal.go x C
  | [], _ => rfl
  | S :: C, ⟨h1, h2⟩ => by
    cases S with
    | comp l k es gs =>
      simp only [trChain, trScope, PyCore.inlinedLocal.go, Surf.inlinedLocal.go] at h1 ⊢
      rw [← inl_go hx C h2, h1]; cases k <;> rfl
    | fn l g ps b =>
      simp only [trChain, trScope, PyCore.inlinedLocal.go, Surf.inlinedLocal.go]
      have := cls_tr (not_fresh hx) (.fn l g ps b :: C)
      simp only [trChain, trScope] at this; rw [this]
    | lam l ps b =>
      simp only [trChain, trScope, PyCore.inlinedLocal.go, Surf.inlinedLocal.go]
      have := cls_tr (not_fresh hx) (.lam l ps b :: C)
      simp only [trChain, trScope] at this; rw [this]
    | cl l y b => rfl
end

theorem inl_tr {x : Name} (hx : ¬ Dot x) : ∀ C : List Scope, KOk C →
    PyCore.inlinedLocal (trChain C) x = Surf.inlinedLocal C x
  | [], _ => rfl
  | S :: C, ⟨h1, h2⟩ => by
    cases S with
    | comp l k es gs =>
      simp only [trChain, trScope, PyCore.inlinedLocal, Surf.inlinedLocal] at h1 ⊢
      rw [inl_go hx C h2, h1]; cases k <;> rfl
    | fn => rfl
    | lam => rfl
    | cl => rfl

/-- What the relation's context for the top frames gives about names with no dot. -/
structure Ctx0 (p : List Stmt) (H : Label → Prop) (s : Sem.Config σ) (t : PyCore.Config σ) (f : Sem.Frame σ)
    (f' : PyCore.Frame σ) : Prop where
  hf : FRel0 f f'
  cells : ∀ a : Sem.Addr, ¬ Dot a.2 → pCell t a = sCell s a
  glob : ∀ x, ¬ Dot x → pGlob t x = sGlob s x

theorem At.c0 {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} (A : At p H s t f fs f' fs') :
    Ctx0 p H s t f f' := ⟨A.hf.toFRel0, A.r.cells, A.r.glob⟩

theorem readName_eq {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {f'}
    (A : Ctx0 p H s t f f') {x : Name} (hx : ¬ Dot x) :
    PyCore.readName I t f' x none = Sem.readName I s f x := by
  have hf := A.hf
  simp only [PyCore.readName, place_eq hf hx, Sem.readName]
  cases hq : Sem.place f x with
  | none => rfl
  | some q =>
    have hn : ¬ Dot (snm q) := by rw [place_nm hf hq]; exact hx
    cases q <;> simp only [snm] at hn
    case glob y => simp only [Option.map, pl]; exact lookupGlobal_eq A.glob hn
    case ns y =>
      simp only [Option.map, pl, drop_lookup hf hn]
      cases f.ns.lookup y <;> simp [lookupGlobal_eq A.glob hn]
    case cell a =>
      have hc := A.cells a hn
      simp only [pCell, sCell] at hc
      simp only [Option.map, pl, hc, PyCore.unboundErr, Sem.unboundErr, cls_eq hf hx, hf.chain,
        inl_tr hx _ hf.kok]
      cases s.cells[a]? <;> simp [PyCore.errUnbound, PyCore.errName]

/-! ## Exception contexts -/

@[simp] theorem kexc_binLs {K' : List (PyCore.Kont σ)} : ∀ rest : List PE,
    PyCore.kontExc (rest.map (.binL ",") ++ K') = PyCore.kontExc K'
  | [] => rfl
  | _ :: rest => by simp [PyCore.kontExc, kexc_binLs rest]

@[simp] theorem kexc_recK {done : List Val} {rest : List PE} {K' : List (PyCore.Kont σ)} :
    PyCore.kontExc (recK done rest K') = PyCore.kontExc K' := by
  simp [recK, PyCore.kontExc]

@[simp] theorem kexc_seqs {K' : List (PyCore.Kont σ)} : ∀ n, PyCore.kontExc (seqs n ++ K') = PyCore.kontExc K'
  | 0 => rfl
  | n + 1 => by simp [seqs, List.replicate_succ, PyCore.kontExc] at *; exact kexc_seqs n

@[simp] theorem kexc_fmtRest {C : List Scope} {spec : Option Expr} {K' : List (PyCore.Kont σ)} :
    PyCore.kontExc (fmtRest C spec K') = PyCore.kontExc K' := by
  cases spec <;> simp [fmtRest, PyCore.kontExc]

theorem kexc_blk {pre K' : List (PyCore.Kont σ)} (h : BlkTail pre) (ss : PS) :
    PyCore.kontExc (pre ++ .seq ss :: K') = PyCore.kontExc K' := by
  rcases h with rfl | rfl | rfl <;> simp [PyCore.kontExc]

theorem kexc_del {C : List Scope} {ts : List Expr} {Kp K' : List (PyCore.Kont σ)} (h : DelSeg C ts Kp K') :
    PyCore.kontExc Kp = PyCore.kontExc K' := by
  induction h with
  | base => simp [PyCore.kontExc]
  | nest _ ih => simpa [PyCore.kontExc] using ih

mutual
theorem KRel.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    KRel x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .nil => rfl
  | .core k => CoreK.kexc k
  | .call k => CallK.kexc k
  | .cls k => ClsK.kexc k
  | .comp k => CompK.kexc k
  | .loop k => LoopK.kexc k
  | .asg k => AsgK.kexc k
  | .acc k => AccK.kexc k
  | .misc k => MiscK.kexc k
theorem CoreK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    CoreK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .exprS k | .binL _ _ k | .binR _ k | .ifS _ _ _ k | .ifST _ _ _ k | .whileS _ _ _ _ k | .whileT _ _ _ _ k | .loop _ _ _ _ k
  | .retS k | .tryE _ _ _ k | .ifK _ _ k | .ifT _ _ k | .boolK _ _ k | .boolT _ _ k | .walrusK _ k | .yieldK k
  | .native k | .assignN _ k | .decos k => by simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc k
  | .seq _ hp _ k => by rw [kexc_blk hp]; simp only [Sem.kontExc]; exact KRel.kexc k
  | .seqNil => rfl
  | .catchS .. | .catchT .. | .handler .. => rfl
  | .boolNil k => by simp only [Sem.kontExc]; exact KRel.kexc k
theorem CallK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    CallK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .argStar k | .argKw k | .enterK k => by simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc k
  | .evsCall _ _ _ _ _ _ k | .evsLam _ _ _ _ _ k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK]; exact KRel.kexc k
  | .evsDefn _ _ _ _ _ _ k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK]; exact KRel.kexc k
theorem ClsK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    ClsK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .clsEnd _ k => by simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc k
  | .setAnn k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK]; exact KRel.kexc k
  | .evsCls _ _ _ _ _ _ _ _ _ _ k | .argStarC _ _ _ _ _ k | .argKwC _ _ _ _ _ k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK]; exact KRel.kexc k
theorem CompK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    CompK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .compIt k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .compCall k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .compStart .. => rfl
  | .cAcc .. => rfl
  | .cNext _ _ _ _ _ _ _ _ _ _ _ _ _ _ k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .cLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .cConds _ _ _ _ _ _ _ _ _ k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .cCond _ _ _ _ _ _ _ _ _ k | .cCondT _ _ _ _ _ _ _ _ _ k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .cIter _ _ _ _ _ _ _ _ _ _ _ k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .cIt _ _ _ _ _ _ _ _ _ _ _ k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
  | .cElt k | .cVal k | .cKey _ k | .cExpr k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_seqs, List.cons_append, List.append_assoc, nextK, loopK]; exact KRel.kexc k
theorem LoopK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    LoopK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .forIt _ _ _ _ _ _ _ _ _ _ k | .forStart _ _ _ _ _ _ _ _ _ _ k | .forNext _ _ _ _ _ _ _ _ _ _ _ _ k
  | .forLoop _ _ _ _ _ _ _ _ _ _ _ _ k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, nextK, loopK]; exact KRel.kexc k
theorem AsgK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    AsgK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .assignK _ _ _ _ k | .stManyT _ _ _ k | .stAttr _ _ k | .stSubL _ _ _ k | .stSubR _ _ k | .augN _ _ _ _ _ _ k
  | .augAttr _ _ _ _ _ _ k | .augAttrV _ _ _ _ _ _ _ k | .augSubL _ _ _ _ _ _ k | .augSubI _ _ _ _ _ _ k
  | .augSubV _ _ _ _ _ _ _ k | .augR _ _ _ _ _ k | .augW _ _ _ _ _ k | .delAttr k | .delSubL _ k | .delSubR k
  | .stUnpack _ _ _ _ _ k | .stManyU _ _ _ _ k | .annK _ _ _ _ _ _ _ k | .annA _ _ _ _ _ k | .annV _ _ _ _ _ k
  | .annE _ _ _ _ _ _ k | .exprBlk _ k | .evsDrop1 k | .evsDropR _ _ k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK]; exact KRel.kexc k
  | .delMany _ _ hd k => by
    rw [kexc_del hd]; simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc k
theorem AccK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    AccK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .unK k | .attrK k | .subL _ k | .subR k | .fmtC _ k | .fmtS k | .evsOp _ _ k | .evsList _ _ _ _ _ k
  | .evsTuple _ _ _ _ _ k | .evsSet _ _ _ _ _ k => by
    simp only [PyCore.kontExc, Sem.kontExc, kexc_recK, kexc_fmtRest]; exact KRel.kexc k
  | .fmtV (c := c) _ k => by
    simp only [Sem.kontExc]; split <;> simp only [PyCore.kontExc, kexc_recK, kexc_fmtRest] <;> exact KRel.kexc k
theorem MiscK.kexc {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} :
    MiscK x U i K K' → PyCore.kontExc K' = Sem.kontExc K
  | .cmpL1 _ _ k | .cmpLm _ _ _ _ _ k | .cmpR1 _ k | .cmpRm _ _ _ _ _ _ _ k | .cmpO _ _ _ _ _ _ _ k
  | .cmpT _ _ _ _ _ _ _ k
  | .assertK _ _ k | .assertT _ _ k | .assertM k | .evsRaise k | .raiseCn k | .evsRaiseFrom _ k
  | .evsRaiseFrom2 k | .raiseCs k | .raiseW k | .impMod _ _ _ _ k | .impNext _ _ _ k | .starStore k | .yfK k | .yfIt k
  | .yfN _ k => by simp only [PyCore.kontExc, Sem.kontExc, kexc_recK]; exact KRel.kexc k
  | .cmpONil k => by simp only [Sem.kontExc]; exact KRel.kexc k
  | .impMany _ _ _ k => by simp only [PyCore.kontExc, Sem.kontExc]; exact KRel.kexc k
end

theorem curExc_rel {H : Label → Prop} {gl cs} : ∀ {fs : List (Sem.Frame σ)} {fs' : List (PyCore.Frame σ)},
    PyCore.All2 (fun f f' => FRel p H (rdAt gl cs f') (ownAt cs f') f f') fs fs' → PyCore.curExc fs' = Sem.curExc fs
  | [], [], _ => rfl
  | f :: fs, f' :: fs', ⟨hf, hfs⟩ => by
    obtain ⟨_, _, -, hk⟩ := hf.code
    simp only [PyCore.curExc, Sem.curExc, KRel.kexc hk, curExc_rel hfs]
    cases Sem.kontExc f.kont <;> rfl
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem withCtx_eq (o : Option Val) (v : Val) : PyCore.withCtx o v = Sem.withCtx o v := by
  cases o <;> rfl

/-- The exception a new raise makes, with its context. -/
def exc (st : List (Sem.Frame σ)) (v : Val) : Val := Sem.withCtx (Sem.curExc st) v

theorem raiseNew_s (st : List (Sem.Frame σ)) (v : Val) : Sem.raiseNew st v = .raise (exc st v) := rfl

theorem raiseNew_t {H : Label → Prop} {gl cs} {fs : List (Sem.Frame σ)} {fs' : List (PyCore.Frame σ)}
    (h : PyCore.All2 (fun f f' => FRel p H (rdAt gl cs f') (ownAt cs f') f f') fs fs') (v : Val) :
    PyCore.raiseNew fs' v = .raise (exc fs v) := by
  simp only [PyCore.raiseNew, curExc_rel h, withCtx_eq, exc]

theorem At.stk {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} (A : At p H s t f fs f' fs') :
    PyCore.All2 (fun f f' => FRel p H (rdOf t f') (ownOf t f') f f') (f :: fs) (f' :: fs') := by
  have := A.r.stack; rwa [A.hs, A.ht] at this

theorem resCtrl_rel {H : Label → Prop} {gl cs} {C : List Scope} {U : Label → Prop} {fs : List (Sem.Frame σ)}
    {fs' : List (PyCore.Frame σ)} (h : PyCore.All2 (fun f f' => FRel p H (rdAt gl cs f') (ownAt cs f') f f') fs fs')
    (r : Except Val Val) : CR p C U true (Sem.resCtrl fs r) (PyCore.resCtrl fs' r) := by
  cases r with
  | ok v => exact .val
  | error v => simp only [Sem.resCtrl, PyCore.resCtrl, raiseNew_s, raiseNew_t h]; exact .raise

/-- The two `Special` states. -/
theorem Special.inv {x : Cx} {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} {c' : PyCore.Ctrl σ} {k' : List (PyCore.Kont σ)}
    (h : Special x c k c' k') :
    (∃ l es g rest C0 it, x.C = .comp l .gen es (g :: rest) :: C0 ∧ c = .call .next [it] [] ∧
      k = [.cNext ⟨.gen, es, .none⟩ it g rest] ∧
      c' = .exec (trGs x.C (fresh "i" l) true (g :: rest) (compElt l .gen (trEs x.C es))) ∧ k' = []) ∨
    (∃ l g ps b C0, x.C = .fn l g ps b :: C0 ∧ c = .exec b ∧ k = [] ∧
      c' = .exec (paramBind x.C ps ++ trB x.C b) ∧ k' = []) ∨
    (∃ l ps b C0, x.C = .lam l ps b :: C0 ∧ c = .ev b ∧ k = [.retS] ∧
      c' = .exec (paramBind x.C ps ++ [.ret (sub l 2) (trE x.C b)]) ∧ k' = []) ∨
    (∃ U sb d K K', c = .val .none ∧ k = .yfR sb :: K ∧ c' = .yfStep d ∧ k' = K' ∧ DelegR sb d ∧ KRel x U true K K') := by
  cases h with
  | genComp hC => exact .inl ⟨_, _, _, _, _, _, hC, rfl, rfl, rfl, rfl⟩
  | genFn hC => exact .inr (.inl ⟨_, _, _, _, _, hC, rfl, rfl, rfl, rfl⟩)
  | genLam hC => exact .inr (.inr (.inl ⟨_, _, _, _, hC, rfl, rfl, rfl, rfl⟩))
  | yf hd hK => exact .inr (.inr (.inr ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, hd, hK⟩))

/-! ## The cases of the homomorphic fragment -/


theorem ev_const (l k) : EvCase I p (.const l k) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hok : (!k.startsWith "$") = true := by have := hg.ok; simpa [okE] using this
  exact A.go11 (c := .val (Py.constVal I k)) (c' := .val (Py.constVal I k))
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
    (by simp [PyCore.step, A.ht, hc', trE, PyCore.evalStep, PyCore.top, constK_of (I := I) hok]) .val hk
    (cov_ev A hc hc' (by simp [trE, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))
theorem ev_name (l x) : EvCase I p (.name l x) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hx : ¬ Dot (mangle (priv f.chain) x) := W.nodot l _ f.chain (hg.s _ (by simp [itemsE]))
  have hr := readName_eq (I := I) A.c0 hx
  refine A.go11 (c := Sem.resCtrl (f :: fs) (Sem.readName I s f (Sem.mg f x)))
    (c' := PyCore.resCtrl (f' :: fs') (PyCore.readName I t f' (mangle (priv f.chain) x) none))
    ?_ ?_ ?_ hk (cov_ev A hc hc' ?_)
  · simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC]
  · simp [PyCore.step, A.ht, hc', trE, PyCore.evalStep, PyCore.top]
  · rw [hr]; exact resCtrl_rel A.stk _
  · simp [trE, PyCore.Expr.label, Sem.Expr.lbl, sub_div]
theorem ev_bin (l op a b) : EvCase I p (.bin l op a b) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hop : op ≠ "," := by
    have := hg.ok; simp only [okE, okName, Bool.and_eq_true] at this
    rintro rfl; simp at this
  exact A.go11 (c := .ev a) (k := .binL op b :: f.kont)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
    (by simp [PyCore.step, A.ht, hc', trE, PyCore.evalStep, PyCore.top])
    (.ev (by subg)) (.core (.binL hop (by subg) hk))
    (cov_ev A hc hc' (by simp [trE, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))
theorem ev_ifexp (l c a b) : EvCase I p (.ifexp l c a b) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  exact A.go11 (c := .ev c) (k := .ifK a b :: f.kont)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
    (by simp [PyCore.step, A.ht, hc', trE, PyCore.evalStep, PyCore.top])
    (.ev (by subg)) (.core (.ifK (by subg) (by subg) hk))
    (cov_ev A hc hc' (by simp [trE, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))
theorem ev_walrus (l x e) : EvCase I p (.walrus l x e) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hx : ¬ Dot (mangle (priv f.chain) x) := W.nodot l _ f.chain (hg.s _ (by simp [itemsE]))
  exact A.go11 (c := .ev e) (k := .walrusK (Sem.mg f x) :: f.kont)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
    (by simp [PyCore.step, A.ht, hc', trE, PyCore.evalStep, PyCore.top, Sem.mg])
    (.ev (by subg)) (.core (.walrusK hx hk))
    (cov_ev A hc hc' (by simp [trE, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))
theorem ev_yield (l e) : EvCase I p (.yield l (some e)) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  exact A.go11 (c := .ev e) (k := .yieldK :: f.kont)
    (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
    (by simp [PyCore.step, A.ht, hc', trE, trO, PyCore.evalStep, PyCore.top])
    (.ev (by subg)) (.core (.yieldK hk))
    (cov_ev A hc hc' (by simp [trE, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))
theorem ev_star (l e) : EvCase I p (.star l e) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have := hg.ok; simp [okE] at this

theorem GoodB.tail {C : List Scope} {U : Label → Prop} {st : Stmt} {ss : List Stmt} (h : GoodB p C U (st :: ss)) :
    GoodB p C U ss :=
  ⟨fun x hx => h.s x (by simp [itemsB, hx]), fun x hx => h.t x (by simp [trB, PyCore.itemsB, hx]),
    by have := h.ok; simp [okB] at this; exact this.2, fun l hl => h.u l (by simp [labelsB, hl]),
    fun _ => h.pv (by simp), by have := h.nd; simp only [labelsB, List.nodup_append] at this; exact this.2.1,
    fun x hx => h.tch x (by simp [touchB, hx])⟩

theorem GoodB.e {C : List Scope} {U : Label → Prop} {st : Stmt} {ss : List Stmt} (h : GoodB p C U (st :: ss)) {e : Expr}
    (hs : ∀ x, x ∈ itemsE C e → x ∈ itemsS C st)
    (ht : ∀ x, x ∈ PyCore.itemsE R0 (trChain C) (trE C e) → x ∈ PyCore.itemsS R0 (trChain C) (trS C st))
    (hok : okS st = true → okE e = true) (hu : ∀ l ∈ labelsE e, l ∈ labelsS st)
    (hnd : (labelsS st).Nodup → (labelsE e).Nodup) (htc : ∀ x, x ∈ touchE e → x ∈ touchS st) : GoodE p C U e :=
  ⟨fun x hx => h.s x (by simp [itemsB, hs x hx]), fun x hx => h.t x (by simp [trB, PyCore.itemsB, ht x hx]),
    hok (by have := h.ok; simp [okB] at this; exact this.1), fun l hl => h.u l (by simp [labelsB, hu l hl]),
    h.pv (by simp), hnd (by have := h.nd; simp only [labelsB, List.nodup_append] at this; exact this.1),
    fun x hx => h.tch x (by simp [touchB, htc x hx])⟩

theorem GoodB.b {C : List Scope} {U : Label → Prop} {st : Stmt} {ss : List Stmt} (h : GoodB p C U (st :: ss)) {b : List Stmt}
    (hs : ∀ x, x ∈ itemsB C b → x ∈ itemsS C st)
    (ht : ∀ x, x ∈ PyCore.itemsB R0 (trChain C) (trB C b) → x ∈ PyCore.itemsS R0 (trChain C) (trS C st))
    (hok : okS st = true → okB b = true) (hu : ∀ l ∈ labelsB b, l ∈ labelsS st)
    (hnd : (labelsS st).Nodup → (labelsB b).Nodup) (htc : ∀ x, x ∈ touchB b → x ∈ touchS st) : GoodB p C U b :=
  ⟨fun x hx => h.s x (by simp [itemsB, hs x hx]), fun x hx => h.t x (by simp [trB, PyCore.itemsB, ht x hx]),
    hok (by have := h.ok; simp [okB] at this; exact this.1), fun l hl => h.u l (by simp [labelsB, hu l hl]),
    fun _ => h.pv (by simp), hnd (by have := h.nd; simp only [labelsB, List.nodup_append] at this; exact this.1),
    fun x hx => h.tch x (by simp [touchB, htc x hx])⟩

theorem GoodB.hs {C : List Scope} {U : Label → Prop} {st : Stmt} {ss : List Stmt} (h : GoodB p C U (st :: ss))
    {hs : List Handler} (h1 : ∀ x, x ∈ itemsHs C hs → x ∈ itemsS C st)
    (ht : ∀ x, x ∈ PyCore.itemsHs R0 (trChain C) (trHs C hs) → x ∈ PyCore.itemsS R0 (trChain C) (trS C st))
    (hok : okS st = true → okHs hs = true) (hu : ∀ l ∈ labelsHs hs, l ∈ labelsS st)
    (hnd : (labelsS st).Nodup → (labelsHs hs).Nodup) (htc : ∀ x, x ∈ touchHs hs → x ∈ touchS st) : GoodHs p C U hs :=
  ⟨fun x hx => h.s x (by simp [itemsB, h1 x hx]), fun x hx => h.t x (by simp [trB, PyCore.itemsB, ht x hx]),
    hok (by have := h.ok; simp [okB] at this; exact this.1), fun l hl => h.u l (by simp [labelsB, hu l hl]),
    fun _ => h.pv (by simp), hnd (by have := h.nd; simp only [labelsB, List.nodup_append] at this; exact this.1),
    fun x hx => h.tch x (by simp [touchB, htc x hx])⟩

macro "gs" : tactic => `(tactic| (intro x hx; simp_all [itemsS, trS, PyCore.itemsS, PyCore.itemsB, trO, itemsO, blk,
  trEs, itemsEs]))
macro "gso" : tactic => `(tactic| (intro h; simp_all [okS, okO]))
macro "gsl" : tactic => `(tactic| (intro x hx; simp_all [labelsS, labelsO]))
macro "gsnd" : tactic => `(tactic| (intro h; simp_all [labelsS, labelsO, List.nodup_cons, List.nodup_append]))
macro "gst" : tactic => `(tactic| (intro x hx; simp_all [touchS, touchO, touchB, touchHs]))
macro "gse" : tactic => `(tactic| exact GoodB.e ‹_› (by gs) (by gs) (by gso) (by gsl) (by gsnd) (by gst))
macro "gsb" : tactic => `(tactic| exact GoodB.b ‹_› (by gs) (by gs) (by gso) (by gsl) (by gsnd) (by gst))
macro "gsh" : tactic => `(tactic| exact GoodB.hs ‹_› (by gs) (by gs) (by gso) (by gsl) (by gsnd) (by gst))

set_option hygiene false in
macro "estep" : tactic => `(tactic| simp [Sem.step, A.hs, hc, Sem.execStep, Sem.setC])
set_option hygiene false in
macro "pestep" : tactic => `(tactic| simp [PyCore.step, A.ht, hc', trB, trS, trO, PyCore.execStep, PyCore.top])

theorem cov_exec {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f fs f' fs'} (A : At p H s t f fs f' fs')
    {st : Stmt} {ss : List Stmt} {ps : PyCore.Stmt} {pss : PS} (hc : f.ctrl = .exec (st :: ss))
    (hc' : f'.ctrl = .exec (ps :: pss)) (hl : ps.label / 64 = st.label) :
    ∀ x, pfocus t = some x → Touch p s (x / 64) := by
  intro x hx
  have hx := pfocus_le hx
  simp [PyCore.focus, A.ht, hc'] at hx
  left; simp [Sem.focus, A.hs, hc, ← hx, hl, Sem.Stmt.lbl]
  cases st <;> rfl

/-- The rest of the block below a statement. -/
theorem krel_seq {x : Cx} {U : Label → Prop} {ss : List Stmt} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (hn : NoCompH x.C) (hg : GoodB x.p x.C U ss) (hk : KRel x U false K K') :
    KRel x U false (.seq ss :: K) (.seq (trB x.C ss) :: K') :=
  .core (.seq (pre := []) (fun _ => hn) (.inl rfl) hg hk)

theorem exec_expr (l e) : ExecCase I p (.expr l e) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact A.go11 (c := .ev e) (k := .exprS :: .seq ss :: f.kont) (by estep) (by pestep)
    (.ev (by gse)) (.core (.exprS (krel_seq (hnc (by simp)) hg.tail hk)))
    (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))
theorem exec_ite (l c tb ub) : ExecCase I p (.ite l c tb ub) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact A.go11 (c := .ev c) (k := .ifS tb ub :: .seq ss :: f.kont) (by estep) (by pestep)
    (.ev (by gse)) (.core (.ifS (hnc (by simp)) (by gsb) (by gsb) (krel_seq (hnc (by simp)) hg.tail hk)))
    (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))
theorem exec_while (l c b u) : ExecCase I p (.while l c b u) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have h1 : GoodE p f.chain U c := by gse
  have h2 : GoodB p f.chain U b := by gsb
  have h3 : GoodB p f.chain U u := by gsb
  exact A.go11 (c := .ev c) (k := .whileS c b u :: .seq ss :: f.kont) (by estep) (by pestep)
    (.ev h1) (.core (.whileS (hnc (by simp)) h1 h2 h3 (krel_seq (hnc (by simp)) hg.tail hk)))
    (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))
theorem exec_brk (l) : ExecCase I p (.brk l) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact A.go11 (c := .brk) (k := .seq ss :: f.kont) (i := false) (by estep) (by pestep) (.brk (hnc (by simp)))
    (krel_seq (hnc (by simp)) hg.tail hk) (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))
theorem exec_cont (l) : ExecCase I p (.cont l) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact A.go11 (c := .cont) (k := .seq ss :: f.kont) (i := false) (by estep) (by pestep) (.cont (hnc (by simp)))
    (krel_seq (hnc (by simp)) hg.tail hk) (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))
theorem exec_ret (l e) : ExecCase I p (.ret l (some e)) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact A.go11 (c := .ev e) (k := .retS :: .seq ss :: f.kont) (by estep) (by pestep)
    (.ev (by gse)) (.core (.retS (krel_seq (hnc (by simp)) hg.tail hk)))
    (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))
theorem exec_tryE (l b hs u) : ExecCase I p (.tryE l b hs u) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact A.go11 (c := .exec b) (k := .tryE hs u :: .seq ss :: f.kont) (by estep) (by pestep)
    (.exec (by gsb) (fun _ => hnc (by simp))) (.core (.tryE (hnc (by simp)) (by gsh) (by gsb) (krel_seq (hnc (by simp)) hg.tail hk)))
    (cov_exec A hc hc' (by simp [trS, PyCore.Stmt.label, Stmt.label, sub_div]))

theorem goodB_nil (C : List Scope) (U : Label → Prop) : GoodB p C U [] :=
  ⟨by simp [SubL, itemsB], by simp [SubL, trB, PyCore.itemsB], rfl, by simp [labelsB], fun h => absurd rfl h,
    by simp [labelsB], by simp [SubL, touchB]⟩

theorem stst_no {s : Sem.Config σ} {f : Sem.Frame σ} {fs} {v : Val} (h : v ≠ .no) (h2 : ∀ b, v ≠ .bool b)
    (ks : List (Sem.Kont σ)) : Sem.tst s f fs v ks = Sem.doOp s f fs .truth [v] ks := by
  cases v <;> simp_all [Sem.tst]
theorem ptst_no {t : PyCore.Config σ} {f : PyCore.Frame σ} {fs} {v : Val} (h : v ≠ .no) (h2 : ∀ b, v ≠ .bool b)
    (ks : List (PyCore.Kont σ)) : PyCore.tst t f fs v ks = PyCore.top t fs { f with ctrl := .op .truth [v], kont := ks } := by
  cases v <;> simp_all [PyCore.tst]

set_option hygiene false in
macro "sstep" : tactic => `(tactic| simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, Sem.doOp, Sem.doneStep,
  Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep])
set_option hygiene false in
macro "pstep" : tactic => `(tactic| simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, PyCore.doneStep,
  PyCore.raiseStep, PyCore.retStep, PyCore.brkStep, PyCore.contStep, trHs])

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A truth test: `Val.no` and Booleans by the core, anything else asks the interpretation. -/
theorem val_tst (A : At p H s t f fs f' fs') {U : Label → Prop} {v : Val}
    {k0 : List (Sem.Kont σ)} {k0' : List (PyCore.Kont σ)}
    (e1 : Sem.step I s = Sem.tst s f fs v k0) (e2 : PyCore.step I t = PyCore.tst t f' fs' v k0')
    (hk : KRel A.x U true k0 k0') (hcov : PyCore.focus t = none) (he : EnterSub k0 f.kont := by esub) :
    Goal I p H s t := by
  by_cases hv : v = .no
  · subst hv
    exact A.go11 (c := .val (.bool false)) (c' := .val (.bool false)) (by rw [e1]; rfl) (by rw [e2]; rfl) .val hk
      (cov_none A hcov) he
  by_cases hb : ∃ b, v = .bool b
  · obtain ⟨b, rfl⟩ := hb
    exact A.go11 (c := .val (.bool b)) (c' := .val (.bool b)) (by rw [e1]; rfl) (by rw [e2]; rfl) .val hk
      (cov_none A hcov) he
  have hb' : ∀ b, v ≠ .bool b := fun b h => hb ⟨b, h⟩
  exact A.go11 (c := .op .truth [v]) (c' := .op .truth [v]) (by rw [e1, stst_no hv hb']; rfl)
    (by rw [e2, ptst_no hv hb']; rfl) .op hk (cov_none A hcov) he

theorem t_eta (ht : t.stack = f' :: fs') :
    { t with stack := { f' with ctrl := f'.ctrl, kont := f'.kont } :: fs' } = t := by
  cases t; simp only at ht; subst ht; rfl


end

/-! ## Writes -/

section Writes
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem At.zero (A : At p H s t f fs f' fs') : At0 p H s t f fs f' fs' := by
  have hst := A.r.stack; rw [A.hs, A.ht] at hst
  exact ⟨A.hs, A.ht, A.hf.toFRel0, A.hf.hl, hst.2, A.r.objs, A.r.cells, A.r.glob, A.r.out, A.r.next, A.r.res,
    A.r.st, fun g hg => A.r.wait g (by rw [A.hs]; exact hg), A.r.ids, by rw [← A.hs]; exact A.r.enter⟩

theorem At0.crel (A : At0 p H s t f fs f' fs') {U : Label → Prop} {i : Bool}
    (hc : CR p f.chain U i f.ctrl f'.ctrl) (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U i f.kont f'.kont) :
    CRel p H s t :=
  ⟨by rw [A.hs, A.ht]; exact ⟨⟨A.hf, A.hl, U, i, hc, hk⟩, A.hfs⟩, A.objs, A.cells, A.glob, A.out, A.next, A.res,
    A.st, by rw [A.hs]; exact A.wait, A.ids, by rw [A.hs]; exact A.enter⟩

theorem At0.upd (A : At0 p H s t f fs f' fs') (c : Sem.Ctrl σ) (k : List (Sem.Kont σ)) (c' : PyCore.Ctrl σ)
    (k' : List (PyCore.Kont σ)) (he : EnterSub k f.kont := by esub) :
    At0 p H { s with stack := { f with ctrl := c, kont := k } :: fs }
      { t with stack := { f' with ctrl := c', kont := k' } :: fs' }
      { f with ctrl := c, kont := k } fs { f' with ctrl := c', kont := k' } fs' :=
  ⟨rfl, rfl, A.hf.upd c k c' k', A.hl, A.hfs, A.objs, A.cells, A.glob, A.out, A.next, A.res, A.st, A.wait,
    A.ids.top A.ht rfl rfl, A.enter.top c he⟩

theorem At0.updS (A : At0 p H s t f fs f' fs') (c : Sem.Ctrl σ) (k : List (Sem.Kont σ))
    (he : EnterSub k f.kont := by esub) :
    At0 p H { s with stack := { f with ctrl := c, kont := k } :: fs } t { f with ctrl := c, kont := k } fs f' fs' :=
  ⟨rfl, A.ht, ⟨A.hf.id, A.hf.chain, A.hf.cls, A.hf.pcls, A.hf.kind, A.hf.kc, A.hf.κ, A.hf.κa, A.hf.ns, A.hf.kok⟩,
    A.hl, A.hfs, A.objs, A.cells, A.glob, A.out, A.next, A.res, A.st, A.wait, A.ids, A.enter.top c he⟩

theorem At0.updT (A : At0 p H s t f fs f' fs') (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    At0 p H s { t with stack := { f' with ctrl := c', kont := k' } :: fs' } f fs { f' with ctrl := c', kont := k' } fs' :=
  ⟨A.hs, rfl, ⟨A.hf.id, A.hf.chain, A.hf.cls, A.hf.pcls, A.hf.kind, A.hf.kc, A.hf.κ, A.hf.κa, A.hf.ns, A.hf.kok⟩,
    A.hl, A.hfs, A.objs, A.cells, A.glob, A.out, A.next, A.res, A.st, A.wait, A.ids.top A.ht rfl rfl, A.enter⟩

theorem s_eta (hs : s.stack = f :: fs) :
    { s with stack := { f with ctrl := f.ctrl, kont := f.kont } :: fs } = s := by
  cases s; simp only at hs; subst hs; rfl

/-- The continuation relation at another reading of fresh names, agreeing outside its budget, and a
larger history. -/
theorem krel_move {x : Cx} {C : List Scope} {rd own : Name → Option Val} {H' U : Label → Prop} {i : Bool}
    {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)} (hk : KRel x U i K K') (hC : C = x.C)
    (ha : Agree U x.rd x.own rd own) (hH : ∀ l, x.H l → H' l) : KRel ⟨x.p, C, rd, own, H'⟩ U i K K' := by
  subst hC; exact KRel.ext ⟨hH, ha⟩ hk

/-! ### Readings of fresh names -/

theorem agree_of {U : Label → Prop} {P : Name → Prop} {rd own rd' own' : Name → Option Val}
    (hP : ∀ tag l, tagOk tag = true → ¬ U l → ¬ P (fresh tag l))
    (h : ∀ y, ¬ P y → rd' y = rd y ∧ own' y = own y) : Agree U rd own rd' own' :=
  fun tag l ht hl => h _ (hP tag l ht hl)

/-- A frame's reading of the names outside `P`, when the module dictionary, its own cells and namespace
are the same there. -/
theorem rd_same {t t1 : PyCore.Config σ} {h h1 : PyCore.Frame σ} {P : Name → Prop}
    (hcls : h1.cls = h.cls) (hk : h1.kind = h.kind) (hid : h1.id = h.id)
    (hgl : h.kind = .mod → ∀ x, ¬ P x → t1.glob x = t.glob x)
    (hc : ∀ x, ¬ P x → t1.cells[(h.id, x)]? = t.cells[(h.id, x)]?)
    (hns : h.kind = .cls → ∀ x, ¬ P x → h1.ns.lookup x = h.ns.lookup x) :
    ∀ y, ¬ P y → rdOf t1 h1 y = rdOf t h y ∧ ownOf t1 h1 y = ownOf t h y := by
  intro y hy
  refine ⟨?_, by simp only [ownOf, ownAt, hid]; exact hc y hy⟩
  simp only [rdOf, rdAt, hcls, hk, hid]
  cases h.cls y with
  | glob =>
    cases hkk : h.kind
    case mod => simp [hgl hkk y hy]
    all_goals simp
  | loc =>
    cases hkk : h.kind
    case cls => simp [hns hkk y hy]
    all_goals simp [hc y hy]
  | free => rfl

/-- Readings of fresh names in a frame whose PyCore configuration changed only at names with no dot. -/
theorem agree_nd {t t1 : PyCore.Config σ} (h : PyCore.Frame σ) (U : Label → Prop)
    (hgl : ∀ x, Dot x → t1.glob x = t.glob x) (hc : ∀ a : PyCore.Addr, Dot a.2 → t1.cells[a]? = t.cells[a]?) :
    Agree U (rdOf t h) (ownOf t h) (rdOf t1 h) (ownOf t1 h) :=
  agree_of (P := fun y => ¬ Dot y) (fun tag l _ _ h => h (dot_fresh tag l))
    (rd_same rfl rfl rfl (fun _ x hx => hgl x (Classical.not_not.1 hx)) (fun x hx => hc _ (Classical.not_not.1 hx))
      fun _ _ _ => rfl)

theorem FRel.agree {rd own rd' own' : Name → Option Val} {g : Sem.Frame σ} {g' : PyCore.Frame σ}
    (h : FRel p H rd own g g') (ha : Agree (fun _ => False) rd own rd' own') : FRel p H rd' own' g g' := by
  obtain ⟨U, i, hc, hk⟩ := h.code
  exact ⟨h.toFRel0, h.hl, U, i, hc, KRel.ext ⟨fun _ h => h, ha.mono fun _ h => h.elim⟩ hk⟩

theorem Special.agree {x : Cx} {rd own : Name → Option Val} (ha : Agree (fun _ => False) x.rd x.own rd own)
    {c : Sem.Ctrl σ} {k : List (Sem.Kont σ)} {c' : PyCore.Ctrl σ} {k' : List (PyCore.Kont σ)}
    (h : Special x c k c' k') : Special (x.with rd own x.H) c k c' k' := by
  cases h with
  | genComp hC h1 hn n1 n2 n3 n4 hr ho f1 f2 g1 g2 g3 =>
    exact .genComp hC h1 hn n1 n2 n3 n4 (((ha "i" _ (by decide) id).1).trans hr)
      (((ha "i" _ (by decide) id).2).trans ho) f1 f2 g1 g2 g3
  | genFn hC hq g => exact .genFn hC hq g
  | genLam hC hq g => exact .genLam hC hq g
  | yf hd hk => exact .yf hd (KRel.ext ⟨fun _ h => h, ha.mono fun _ h => h.elim⟩ hk)

theorem GRel.agree {gl cs gl' cs'} {g : Sem.GSt σ} {g' : PyCore.GSt σ} (h : GRel p H gl cs g g')
    (ha : ∀ h', g' = .susp h' → Agree (fun _ => False) (rdAt gl cs h') (ownAt cs h') (rdAt gl' cs' h') (ownAt cs' h')) :
    GRel p H gl' cs' g g' := by
  cases h with
  | susp h => exact .susp (h.agree (ha _ rfl))
  | special h0 hl hs => exact .special h0 hl (Special.agree (ha _ rfl) hs)
  | running => exact .running
  | done => exact .done

theorem ORel.agree {gl cs gl' cs'} {a : Sem.Obj σ} {b : PyCore.Obj σ} (h : ORel p H gl cs a b)
    (ha : ∀ h', b = .gen (.susp h') → Agree (fun _ => False) (rdAt gl cs h') (ownAt cs h') (rdAt gl' cs' h') (ownAt cs' h')) :
    ORel p H gl' cs' a b := by
  cases h with
  | clo h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .clo h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | gen h => exact .gen (h.agree fun h' e => ha h' (by rw [e]))

theorem all2_agree {t t1 : PyCore.Config σ} : ∀ {gs : List (Sem.Frame σ)} {gs' : List (PyCore.Frame σ)},
    PyCore.All2 (fun f f' => FRel p H (rdOf t f') (ownOf t f') f f') gs gs' →
    (∀ h' ∈ gs', Agree (fun _ => False) (rdOf t h') (ownOf t h') (rdOf t1 h') (ownOf t1 h')) →
    PyCore.All2 (fun f f' => FRel p H (rdOf t1 f') (ownOf t1 f') f f') gs gs'
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩, ha => ⟨h1.agree (ha _ (by simp)), all2_agree h2 fun h' hh => ha h' (by simp [hh])⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

/-- The configurations after a write: the top frames changed (same id, kind and chain), the readings of
fresh names in the frames below and in the suspended generators the same. -/
theorem At0.write (A : At0 p H s t f fs f' fs') {s1 : Sem.Config σ} {t1 : PyCore.Config σ}
    {g : Sem.Frame σ} {g' : PyCore.Frame σ} (hs1 : s1.stack = g :: fs) (ht1 : t1.stack = g' :: fs')
    (hg : FRel0 g g') (hch : g.chain = f.chain) (hid : g'.id = f'.id) (hk : g'.kind = f'.kind)
    (ho : s1.objs = s.objs) (ho' : t1.objs = t.objs)
    (hc : ∀ a : Sem.Addr, ¬ Dot a.2 → pCell t1 a = sCell s1 a) (hgl : ∀ x, ¬ Dot x → pGlob t1 x = sGlob s1 x)
    (hag : ∀ h', (h' ∈ fs' ∨ ∃ o, pObj t o = some (.gen (.susp h'))) →
      Agree (fun _ => False) (rdOf t h') (ownOf t h') (rdOf t1 h') (ownOf t1 h'))
    (hout : t1.out = t.out) (hn : t1.next = t.next) (hn' : s1.next = s.next) (hres : t1.res = t.res)
    (hres' : s1.res = s.res) (hst : t1.st = t.st) (hst' : s1.st = s.st) (hen : EnterSub g.kont f.kont := by esub) :
    At0 p H s1 t1 g fs g' fs' := by
  refine ⟨hs1, ht1, hg, fun S C e => A.hl S C (hch ▸ e), all2_agree A.hfs fun h' hh => hag h' (.inl hh),
    fun o => ?_, hc, hgl, by rw [hout, A.out], by rw [hn, hn', A.next], by rw [hres, hres', A.res],
    by rw [hst, hst', A.st], A.wait, A.ids.top' A.ht ht1 ho' hn hid hk,
    by rw [ho]; exact ⟨fun x hx => (List.mem_cons.1 hx).elim (fun e => e ▸ (A.enter.1 f List.mem_cons_self).sub hen)
      (fun hx => A.enter.1 x (List.mem_cons_of_mem _ hx)), A.enter.2⟩⟩
  have := A.objs o
  simp only [sObj, pObj, ho, ho'] at this ⊢
  cases h1 : s.objs[o]? <;> cases h2 : t.objs[o]? <;> rw [h1, h2] at this <;> simp only [PyCore.OptRel] at this ⊢
  · exact this.agree fun h' e => hag h' (.inr ⟨o, by simp [pObj, h2, e]⟩)

/-- Another frame with the top frame's id, or a suspended generator, is no stack frame below. -/
theorem At0.below (A : At0 p H s t f fs f' fs') {h' : PyCore.Frame σ}
    (hh : h' ∈ fs' ∨ ∃ o, pObj t o = some (.gen (.susp h'))) : h'.id ≠ f'.id ∧ (f'.kind = .mod → h'.kind ≠ .mod) := by
  have hn := A.ids.nodup; rw [A.ht] at hn
  rcases hh with hh | ⟨o, ho⟩
  · have h1 : h'.id ≠ f'.id := by
      intro e; simp only [List.map_cons, List.nodup_cons] at hn
      exact hn.1 (List.mem_map.2 ⟨h', hh, e⟩)
    refine ⟨h1, fun hm hm' => h1 ?_⟩
    rw [A.ids.m0 h' (by rw [A.ht]; simp [hh]) hm', A.ids.m0 f' (by rw [A.ht]; simp) hm]
  · obtain ⟨e, hne⟩ := A.ids.susp o h' ho
    refine ⟨by rw [e]; exact fun e' => hne f' (by rw [A.ht]; simp) e'.symm, fun _ => ?_⟩
    rw [A.ids.sk o h' ho]; simp

/-! ### Namespaces, the module dictionary, cells -/

theorem any_drop (y : Name) (hy : ¬ Dot y) :
    ∀ ns : List (Name × Val), (PyCore.dropReserved ns).any (·.1 == y) = ns.any (·.1 == y)
  | [] => rfl
  | (k, w) :: ns => by
    have ih := any_drop y hy ns
    simp only [PyCore.dropReserved] at ih ⊢
    by_cases hk : k.startsWith "." = true
    · have : (k == y) = false := by
        rw [beq_eq_false_iff_ne]; rintro rfl; exact hy ((startsWith_dot _).1 hk)
      simp [List.filter, hk, this, ih]
    · simp [List.filter, hk, ih]

theorem filter_map_comm {α} (q : α → Bool) (g : α → α) (h : ∀ a, q (g a) = q a) :
    ∀ l : List α, (l.map g).filter q = (l.filter q).map g
  | [] => rfl
  | a :: l => by
    simp only [List.map, List.filter, h a]
    cases q a <;> simp [filter_map_comm q g h l]

theorem drop_map (y : Name) (v : Val) (ns : List (Name × Val)) :
    PyCore.dropReserved (ns.map fun q => if q.1 == y then (y, v) else q) =
      (PyCore.dropReserved ns).map fun q => if q.1 == y then (y, v) else q := by
  refine filter_map_comm _ _ (fun q => ?_) ns
  by_cases hq : (q.1 == y) = true
  · simp only [hq, ite_true]; rw [beq_iff_eq] at hq; rw [hq]
  · simp only [hq]; rfl

theorem drop_nsSet (y : Name) (hy : ¬ Dot y) (ov : Option Val) (ns : List (Name × Val)) :
    PyCore.dropReserved (PyCore.nsSet ns y ov) = Sem.nsSet (PyCore.dropReserved ns) y ov := by
  have hy' : y.startsWith "." = false := by
    cases h : y.startsWith "." with
    | false => rfl
    | true => exact absurd ((startsWith_dot _).1 h) hy
  cases ov with
  | none =>
    simp only [PyCore.nsSet, Sem.nsSet, PyCore.dropReserved, List.filter_filter]
    congr 1; funext q; exact Bool.and_comm _ _
  | some v =>
    simp only [PyCore.nsSet, Sem.nsSet, any_drop y hy]
    split
    · exact drop_map y v ns
    · simp [PyCore.dropReserved, List.filter_append, hy']

theorem drop_nsSet_dot (y : Name) (hy : Dot y) (ov : Option Val) (ns : List (Name × Val)) :
    PyCore.dropReserved (PyCore.nsSet ns y ov) = PyCore.dropReserved ns := by
  have hy' : y.startsWith "." = true := (startsWith_dot _).2 hy
  cases ov with
  | none =>
    simp only [PyCore.nsSet, PyCore.dropReserved, List.filter_filter]
    congr 1; funext q
    by_cases hq : q.1 = y
    · simp [hq, hy']
    · simp [hq]
  | some v =>
    simp only [PyCore.nsSet]
    split
    · rw [drop_map]
      have : ∀ q ∈ PyCore.dropReserved ns, (fun q : Name × Val => if q.1 == y then (y, v) else q) q = q := by
        intro q hq
        have h1 := (List.mem_filter.1 hq).2
        have : (q.1 == y) = false := by
          rw [beq_eq_false_iff_ne]; rintro h; rw [h, hy'] at h1; simp at h1
        simp [this]
      rw [List.map_congr_left this]; simp
    · simp [PyCore.dropReserved, List.filter_append, hy']

theorem lookup_map_ne {x y : Name} (hxy : x ≠ y) (v : Val) : ∀ ns : List (Name × Val),
    (ns.map fun q => if q.1 == y then (y, v) else q).lookup x = ns.lookup x
  | [] => rfl
  | (k, w) :: ns => by
    have ih := lookup_map_ne hxy v ns
    by_cases hk : k = y
    · subst hk
      have : (x == k) = false := by simpa using hxy
      simp only [List.map_cons, beq_self_eq_true, ite_true, List.lookup, this]; exact ih
    · have : (k == y) = false := by simpa using hk
      simp only [List.map_cons, this, Bool.false_eq_true, ite_false, List.lookup]
      split
      · rfl
      · exact ih

theorem lookup_app_ne {x y : Name} (hxy : x ≠ y) (v : Val) : ∀ ns : List (Name × Val),
    (ns ++ [(y, v)]).lookup x = ns.lookup x
  | [] => by
    have : (x == y) = false := by simpa using hxy
    simp [List.lookup, this]
  | (k, w) :: ns => by
    simp only [List.cons_append, List.lookup]
    split
    · rfl
    · exact lookup_app_ne hxy v ns

theorem lookup_filter_ne {x y : Name} (hxy : x ≠ y) : ∀ ns : List (Name × Val),
    (ns.filter (·.1 != y)).lookup x = ns.lookup x
  | [] => rfl
  | (k, w) :: ns => by
    have ih := lookup_filter_ne hxy ns
    by_cases hk : k = y
    · subst hk
      have : (x == k) = false := by simpa using hxy
      simp [List.filter, List.lookup, this, ih]
    · have : (k != y) = true := by simpa using hk
      simp only [List.filter, this, List.lookup]
      split <;> simp_all

theorem lookup_nsSet_ne {x y : Name} (hxy : x ≠ y) (ns : List (Name × Val)) (ov : Option Val) :
    (PyCore.nsSet ns y ov).lookup x = ns.lookup x := by
  cases ov with
  | none => exact lookup_filter_ne hxy ns
  | some v =>
    simp only [PyCore.nsSet]; split
    · exact lookup_map_ne hxy v ns
    · exact lookup_app_ne hxy v ns

theorem lookup_map (y : Name) (v : Val) : ∀ ns : List (Name × Val), ns.any (·.1 == y) = true →
    (ns.map fun q => if q.1 == y then (y, v) else q).lookup y = some v
  | [], h => by simp at h
  | q :: ns, h => by
    by_cases hq : q.1 = y
    · obtain ⟨a, b⟩ := q; simp only at hq; subst hq; simp [List.lookup]
    · have h1 : (q.1 == y) = false := by simpa using hq
      have h2 : (y == q.1) = false := by rw [beq_eq_false_iff_ne]; exact fun e => hq e.symm
      simp only [List.any_cons, h1, Bool.false_or] at h
      simp only [List.map_cons, h1, Bool.false_eq_true, ite_false, List.lookup, h2]
      exact lookup_map y v ns h

theorem lookup_app (y : Name) (v : Val) : ∀ ns : List (Name × Val), ns.any (·.1 == y) = false →
    (ns ++ [(y, v)]).lookup y = some v
  | [], _ => by simp [List.lookup]
  | q :: ns, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have h2 : (y == q.1) = false := by
      have := h.1; rw [beq_eq_false_iff_ne] at this ⊢; exact fun e => this e.symm
    simp only [List.cons_append, List.lookup, h2]
    exact lookup_app y v ns h.2

theorem lookup_nsSet (ns : List (Name × Val)) (y : Name) (v : Val) :
    (PyCore.nsSet ns y (some v)).lookup y = some v := by
  simp only [PyCore.nsSet]
  split
  · rename_i h; exact lookup_map y v ns h
  · rename_i h; exact lookup_app y v ns (Bool.eq_false_iff.2 h)

theorem ite_ne {α} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]

theorem lookup_nsSet_none (ns : List (Name × Val)) (y : Name) : (PyCore.nsSet ns y none).lookup y = none := by
  simp only [PyCore.nsSet]
  induction ns with
  | nil => rfl
  | cons q ns ih =>
    by_cases hq : q.1 = y
    · simp [List.filter, hq, ih]
    · have h1 : (q.1 != y) = true := by simpa using hq
      have h2 : (y == q.1) = false := by rw [beq_eq_false_iff_ne]; exact fun e => hq e.symm
      simp only [List.filter, h1, List.lookup, h2]; exact ih

theorem pglob_ins (t : PyCore.Config σ) (S : List (PyCore.Frame σ)) (y z : Name) (ov : Option Val) :
    ({ t with globW := t.globW.insert y ov, stack := S } : PyCore.Config σ).glob z = if y = z then ov else t.glob z := by
  simp only [PyCore.Config.glob, Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases h : y = z <;> simp [h]

theorem raiseNew_top {gl cs} {g : Sem.Frame σ} {g' : PyCore.Frame σ} {gs : List (Sem.Frame σ)}
    {gs' : List (PyCore.Frame σ)}
    (hfs : PyCore.All2 (fun f f' => FRel p H (rdAt gl cs f') (ownAt cs f') f f') gs gs')
    (he : PyCore.kontExc g'.kont = Sem.kontExc g.kont) (v : Val) :
    PyCore.raiseNew (g' :: gs') v = .raise (exc (g :: gs) v) := by
  simp only [PyCore.raiseNew, exc, PyCore.curExc, Sem.curExc, he, curExc_rel hfs]
  cases Sem.kontExc g.kont <;> simp [withCtx_eq]

@[simp] theorem pplace_kont (g : PyCore.Frame σ) (k : List (PyCore.Kont σ)) (x : Name) :
    PyCore.place { g with kont := k } x = PyCore.place g x := rfl
@[simp] theorem pplace_ck (g : PyCore.Frame σ) (c : PyCore.Ctrl σ) (k : List (PyCore.Kont σ)) (x : Name) :
    PyCore.place { g with ctrl := c, kont := k } x = PyCore.place g x := rfl
@[simp] theorem splace_ck (g : Sem.Frame σ) (c : Sem.Ctrl σ) (k : List (Sem.Kont σ)) (x : Name) :
    Sem.place { g with ctrl := c, kont := k } x = Sem.place g x := rfl

/-! ### Stores, unsets, deletions -/

/-- A write (`ov`) of a name with no dot in both runs, at corresponding places, the top frames' code set
to `c`, `k` and `c'`, `k'`. -/
theorem write0 (A : At0 p H s t f fs f' fs') {x : Name} {q : Sem.Place} (hq : Sem.place f x = some q)
    (hx : ¬ Dot x) (ov : Option Val) (c : Sem.Ctrl σ) (k : List (Sem.Kont σ)) (c' : PyCore.Ctrl σ)
    (k' : List (PyCore.Kont σ)) (hen : EnterSub k f.kont := by esub) :
    At0 p H { (Sem.writeAt s f ov q).1 with stack := { (Sem.writeAt s f ov q).2 with ctrl := c, kont := k } :: fs }
      { (PyCore.writeAt t f' ov (pl q)).1 with
          stack := { (PyCore.writeAt t f' ov (pl q)).2 with ctrl := c', kont := k' } :: fs' }
      { (Sem.writeAt s f ov q).2 with ctrl := c, kont := k } fs
      { (PyCore.writeAt t f' ov (pl q)).2 with ctrl := c', kont := k' } fs' ∧
    (Sem.writeAt s f ov q).2.chain = f.chain ∧
    Agree (fun _ => False) (rdOf t f') (ownOf t f') (rdOf (PyCore.writeAt t f' ov (pl q)).1 (PyCore.writeAt t f' ov (pl q)).2)
      (ownOf (PyCore.writeAt t f' ov (pl q)).1 (PyCore.writeAt t f' ov (pl q)).2) := by
  have hn := place_nm A.hf hq
  cases q with
  | glob y =>
    simp only [snm] at hn; subst hn
    refine ⟨A.write rfl rfl (A.hf.upd c k c' k') rfl rfl rfl rfl rfl A.cells (fun z hz => ?_)
        (fun h' _ => agree_nd h' _ (fun z hz => ?_) fun _ _ => rfl) rfl rfl rfl rfl rfl rfl rfl hen, rfl,
      agree_nd f' _ (fun z hz => ?_) fun _ _ => rfl⟩
    · simp only [pGlob, sGlob, Sem.writeAt, PyCore.writeAt, pl, pglob_ins]
      cases ov <;> simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, beq_iff_eq] <;> split
      all_goals first | rfl | exact A.glob z hz
    · simp only [PyCore.writeAt, pl, pglob_ins]; rw [ite_ne]; rintro rfl; exact hx hz
    · simp only [PyCore.writeAt, pl, pglob_ins]; rw [ite_ne]; rintro rfl; exact hx hz
  | ns y =>
    simp only [snm] at hn; subst hn
    have hf := A.hf
    refine ⟨A.write rfl rfl ⟨hf.id, hf.chain, hf.cls, hf.pcls, hf.kind, hf.kc, hf.κ, hf.κa,
        by simp only [Sem.writeAt, PyCore.writeAt, pl]; rw [drop_nsSet y hx, hf.ns], hf.kok⟩ rfl rfl rfl rfl rfl
        A.cells A.glob (fun h' _ => Agree.refl _ _ _) rfl rfl rfl rfl rfl rfl rfl hen, rfl, ?_⟩
    exact agree_of (P := fun y => ¬ Dot y) (fun tag l _ _ h => h (dot_fresh tag l))
      (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun _ z hz =>
        lookup_nsSet_ne (x := z) (y := y) (by intro e; subst e; exact hz hx) f'.ns ov)
  | cell a =>
    simp only [snm] at hn
    have hb' : ∀ b : PyCore.Addr, Dot b.2 → b ≠ a := by rintro b hb rfl; rw [hn] at hb; exact hx hb
    refine ⟨A.write rfl rfl (A.hf.upd c k c' k') rfl rfl rfl rfl rfl (fun b hb => ?_) A.glob
        (fun h' _ => agree_nd h' _ (fun _ _ => rfl) fun b hb => ?_) rfl rfl rfl rfl rfl rfl rfl hen, rfl,
      agree_nd f' _ (fun _ _ => rfl) fun b hb => ?_⟩
    · simp only [pCell, sCell, Sem.writeAt, PyCore.writeAt, pl]
      cases ov <;> simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, beq_iff_eq] <;> split
      all_goals first | rfl | exact A.cells b hb
    all_goals
      simp only [PyCore.writeAt, pl]
      cases ov <;> simp only [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase, beq_iff_eq] <;>
        rw [ite_ne] <;> exact fun e => hb' b hb e.symm

/-- Storing a name with no dot in both runs: both store it, or both raise `NameError`. -/
theorem store0 (A : At0 p H s t f fs f' fs') {x : Name} (hx : ¬ Dot x) (v : Val)
    (c : Sem.Ctrl σ) (k : List (Sem.Kont σ)) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ))
    (he : PyCore.kontExc k' = Sem.kontExc f.kont) (hen : EnterSub k f.kont := by esub) :
    ∃ s1 t1 g g', Sem.storeName s f fs x v c k = some s1 ∧
      PyCore.store t { f' with kont := k' } fs' x v c' = some t1 ∧ At0 p H s1 t1 g fs g' fs' ∧
      g.chain = f.chain ∧ g.kont = k ∧ g'.kont = k' ∧
      ((g.ctrl = c ∧ g'.ctrl = c') ∨ ∃ e, g.ctrl = .raise e ∧ g'.ctrl = .raise e) ∧
      Agree (fun _ => False) (rdOf t f') (ownOf t f') (rdOf t1 g') (ownOf t1 g') := by
  have hp := place_eq A.hf hx
  cases hq : Sem.place f x with
  | none =>
    rw [hq] at hp
    refine ⟨_, _, _, _, by unfold Sem.storeName; rw [hq]; rfl, by unfold PyCore.store; rw [pplace_kont, hp]; rfl,
      A.upd _ k _ k' hen, rfl, rfl, rfl, Or.inr ⟨_, rfl, ?_⟩, Agree.refl _ _ _⟩
    rw [show PyCore.errName = Py.err "NameError" from rfl, raiseNew_top A.hfs (g := f) (by exact he)]; rfl
  | some q =>
    rw [hq] at hp
    obtain ⟨A1, hch, ha⟩ := write0 A hq hx (some v) c k c' k' hen
    refine ⟨_, _, _, _, by unfold Sem.storeName; rw [hq], ?_, A1, hch, rfl, rfl, Or.inl ⟨rfl, rfl⟩, ha⟩
    unfold PyCore.store; rw [pplace_kont, hp]; cases q <;> rfl

theorem isSet_eq (A : At0 p H s t f fs f' fs') {x : Name} {q : Sem.Place} (hq : Sem.place f x = some q)
    (hx : ¬ Dot x) : PyCore.isSet t f' (pl q) = Sem.isSet s f q := by
  have hn := place_nm A.hf hq
  cases q with
  | glob y =>
    simp only [snm] at hn; subst hn
    simp only [PyCore.isSet, Sem.isSet, pl, Std.HashMap.contains_eq_isSome_getElem?]
    rw [show t.glob y = s.glob[y]? from A.glob y hx]
  | ns y =>
    simp only [snm] at hn; subst hn
    simp only [PyCore.isSet, Sem.isSet, pl, drop_lookup A.hf hx]
  | cell a =>
    simp only [snm] at hn
    simp only [PyCore.isSet, Sem.isSet, pl, Std.HashMap.contains_eq_isSome_getElem?]
    rw [show t.cells[a]? = s.cells[a]? from A.cells a (by rw [hn]; exact hx)]

theorem unboundErr_eq {f : Sem.Frame σ} {f' : PyCore.Frame σ} (hf : FRel0 f f') {x : Name} (hx : ¬ Dot x) :
    PyCore.unboundErr f' x = Sem.unboundErr f x := by
  simp only [PyCore.unboundErr, Sem.unboundErr, cls_eq hf hx, hf.chain, inl_tr hx _ hf.kok]
  split <;> rfl

/-- `del x` of a name with no dot in both runs: both unset it, or both raise. -/
theorem del0 (A : At0 p H s t f fs f' fs') {x : Name} (hx : ¬ Dot x) (k : List (Sem.Kont σ)) (L : Label)
    (ss : PS) (he : PyCore.kontExc f'.kont = Sem.kontExc f.kont) (hen : EnterSub k f.kont := by esub) :
    ∃ s1 t1 g g', Sem.delName s f fs x k = some s1 ∧ PyCore.execStep I t f' fs' (.del L x) ss = some t1 ∧
      At0 p H s1 t1 g fs g' fs' ∧ g.chain = f.chain ∧ g.kont = k ∧ g'.kont = .seq ss :: f'.kont ∧
      ((g.ctrl = .exec [] ∧ g'.ctrl = .exec []) ∨ ∃ e, g.ctrl = .raise e ∧ g'.ctrl = .raise e) ∧
      Agree (fun _ => False) (rdOf t f') (ownOf t f') (rdOf t1 g') (ownOf t1 g') := by
  have hp := place_eq A.hf hx
  cases hq : Sem.place f x with
  | none =>
    rw [hq] at hp
    refine ⟨_, _, _, _, by unfold Sem.delName; rw [hq]; rfl, by unfold PyCore.execStep; simp only [hp]; rfl,
      A.upd _ k _ (.seq ss :: f'.kont) hen, rfl, rfl, rfl, Or.inr ⟨_, rfl, ?_⟩, Agree.refl _ _ _⟩
    rw [show PyCore.errName = Py.err "NameError" from rfl, raiseNew_top A.hfs (g := f) he]; rfl
  | some q =>
    rw [hq] at hp
    have hs := isSet_eq A hq hx
    cases hset : Sem.isSet s f q with
    | true =>
      obtain ⟨A1, hch, ha⟩ := write0 A hq hx none (.exec []) k (.exec []) (.seq ss :: f'.kont) hen
      refine ⟨_, _, _, _, by unfold Sem.delName; rw [hq]; simp only [hset]; rfl,
        by unfold PyCore.execStep; simp only [hp, Option.map, hs, hset]; rfl, A1, hch, rfl, rfl, Or.inl ⟨rfl, rfl⟩, ha⟩
    | false =>
      refine ⟨_, _, _, _, by unfold Sem.delName; rw [hq]; simp only [hset]; rfl,
        by unfold PyCore.execStep; simp only [hp, Option.map, hs, hset]; rfl,
        A.upd _ k _ (.seq ss :: f'.kont) hen, rfl, rfl, rfl, Or.inr ⟨_, rfl, ?_⟩, Agree.refl _ _ _⟩
      rw [raiseNew_top A.hfs (g := f) he]
      cases q <;> simp only [PyCore.delErr, pl, unboundErr_eq A.hf hx] <;> rfl

/-- Where PyCore's frame keeps a fresh name it binds: the module dictionary (module frame), its
namespace (class body), or its own cell. -/
theorem fok_place (A : At0 p H s t f fs f' fs') {x : Name} (h : FOk f.chain x) :
    (PyCore.place f' x = some (.glob x) ∧ f'.cls x = .glob ∧ f'.kind = .mod) ∨
    (PyCore.place f' x = some (.ns x) ∧ f'.cls x = .loc ∧ f'.kind = .cls) ∨
    (PyCore.place f' x = some (.cell (f'.id, x)) ∧ f'.cls x = .loc ∧ f'.kind ≠ .mod ∧ f'.kind ≠ .cls) := by
  have hc : f'.cls x = PyCore.clsOf (trChain f.chain) x := by rw [A.hf.pcls, A.hf.chain]
  have hk := A.hf.kind
  have hkc := A.hf.kc
  unfold FOk at h
  rw [h] at hc
  cases hch : f.chain with
  | nil =>
    rw [hch] at hc hkc; simp only at hc
    cases hf : f.kind <;> rw [hf] at hkc <;> simp only [KC] at hkc
    have hk' : f'.kind = .mod := by rw [hk, hf]; rfl
    exact .inl ⟨by simp [PyCore.place, hc], hc, hk'⟩
  | cons S C =>
    rw [hch] at hc hkc; simp only at hc
    cases hf : f.kind with
    | mod => rw [hf] at hkc; simp [KC] at hkc
    | cls =>
      have hk' : f'.kind = .cls := by rw [hk, hf]; rfl
      exact .inr (.inl ⟨by simp [PyCore.place, hc, hk'], hc, hk'⟩)
    | fn =>
      have hk' : f'.kind = .fn := by rw [hk, hf]; rfl
      exact .inr (.inr ⟨by simp [PyCore.place, hc, hk'], hc, by simp [hk'], by simp [hk']⟩)
    | gen o =>
      have hk' : f'.kind = .gen o := by rw [hk, hf]; rfl
      exact .inr (.inr ⟨by simp [PyCore.place, hc, hk'], hc, by simp [hk'], by simp [hk']⟩)

/-- PyCore writes (`ov`) a fresh name its frame binds, the top frame's code set to `c'`, `k'`: its readings
of the other fresh names stay, and so do the other frames'. -/
theorem pwrite0 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
    (hfo : FOk f.chain (fresh tag l)) (ov : Option Val) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    ∃ q, PyCore.place f' (fresh tag l) = some q ∧
      At0 p H s { (PyCore.writeAt t f' ov q).1 with
          stack := { (PyCore.writeAt t f' ov q).2 with ctrl := c', kont := k' } :: fs' }
        f fs { (PyCore.writeAt t f' ov q).2 with ctrl := c', kont := k' } fs' ∧
      rdOf (PyCore.writeAt t f' ov q).1 (PyCore.writeAt t f' ov q).2 (fresh tag l) = ov ∧
      Agree (· = l) (rdOf t f') (ownOf t f')
        (rdOf (PyCore.writeAt t f' ov q).1 (PyCore.writeAt t f' ov q).2)
        (ownOf (PyCore.writeAt t f' ov q).1 (PyCore.writeAt t f' ov q).2) := by
  have hd := dot_fresh tag l
  have hP : ∀ tag' l', tagOk tag' = true → ¬ l' = l → ¬ fresh tag' l' = fresh tag l :=
    fun tag' l' ht hl => fresh_ne ht htag hl
  rcases fok_place A hfo with ⟨hq, hc, hk⟩ | ⟨hq, hc, hk⟩ | ⟨hq, hc, hk, hk'⟩
  · refine ⟨_, hq, ?_, ?_, agree_of (P := (· = fresh tag l)) hP (rd_same rfl rfl rfl (fun _ z hz => ?_) (fun _ _ => rfl) fun _ _ _ => rfl)⟩
    · refine A.write A.hs rfl (A.hf.upd f.ctrl f.kont c' k') rfl rfl rfl rfl rfl A.cells (fun z hz => ?_)
        (fun h' hh => agree_of (P := fun _ => False) (fun _ _ _ _ h => h)
          (rd_same rfl rfl rfl (fun hm => absurd hm ((A.below hh).2 hk)) (fun _ _ => rfl) fun _ _ _ => rfl))
        rfl rfl rfl rfl rfl rfl rfl
      simp only [pGlob, PyCore.writeAt, pglob_ins]; rw [ite_ne]; exact A.glob z hz
      rintro rfl; exact hz hd
    · simp only [rdOf, rdAt, PyCore.writeAt, hc, hk, pglob_ins]; simp
    · simp only [PyCore.writeAt, pglob_ins]; rw [ite_ne]; exact fun e => hz e.symm
  · have hf := A.hf
    refine ⟨_, hq, A.write A.hs rfl ⟨hf.id, hf.chain, hf.cls, hf.pcls, hf.kind, hf.kc, hf.κ, hf.κa,
        by simp only [PyCore.writeAt]; rw [drop_nsSet_dot _ hd, hf.ns], hf.kok⟩ rfl rfl rfl rfl rfl A.cells A.glob
        (fun h' _ => Agree.refl _ _ _) rfl rfl rfl rfl rfl rfl rfl, ?_,
      agree_of (P := (· = fresh tag l)) hP (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun _ z hz =>
        lookup_nsSet_ne (x := z) (y := fresh tag l) hz f'.ns ov)⟩
    cases ov with
    | none => simp only [rdOf, rdAt, PyCore.writeAt, hc, hk]; exact lookup_nsSet_none _ _
    | some v => simp only [rdOf, rdAt, PyCore.writeAt, hc, hk]; exact lookup_nsSet _ _ _
  · refine ⟨_, hq, ?_, ?_, agree_of (P := (· = fresh tag l)) hP (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun z hz => ?_) fun _ _ _ => rfl)⟩
    · refine A.write A.hs rfl (A.hf.upd f.ctrl f.kont c' k') rfl rfl rfl rfl rfl (fun b hb => ?_) A.glob
        (fun h' hh => agree_of (P := fun _ => False) (fun _ _ _ _ h => h)
          (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun z _ => ?_) fun _ _ _ => rfl))
        rfl rfl rfl rfl rfl rfl rfl
      · cases ov <;> simp only [pCell, PyCore.writeAt, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase,
          beq_iff_eq] <;> rw [ite_ne] <;> (try exact A.cells b hb) <;> (rintro rfl; exact hb hd)
      · have hne := (A.below hh).1
        cases ov <;> simp only [PyCore.writeAt, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase,
          beq_iff_eq] <;> rw [ite_ne] <;> (intro e; exact hne (congrArg Prod.fst e).symm)
    · cases hk2 : f'.kind <;> simp_all [rdOf, rdAt, PyCore.writeAt] <;> cases ov <;> simp
    · cases ov <;> simp only [PyCore.writeAt, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_erase,
        beq_iff_eq] <;> rw [ite_ne] <;> (intro e; exact hz (congrArg Prod.snd e).symm)

/-- PyCore stores a fresh name its frame binds. -/
theorem pstore0 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
    (hfo : FOk f.chain (fresh tag l)) (v : Val) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    ∃ t1 g', PyCore.store t { f' with kont := k' } fs' (fresh tag l) v c' = some t1 ∧
      At0 p H s t1 f fs g' fs' ∧ g'.ctrl = c' ∧ g'.kont = k' ∧ rdOf t1 g' (fresh tag l) = some v ∧
      Agree (· = l) (rdOf t f') (ownOf t f') (rdOf t1 g') (ownOf t1 g') := by
  obtain ⟨q, hq, A1, hr, ha⟩ := pwrite0 A htag hfo (some v) c' k'
  refine ⟨_, _, ?_, A1, rfl, rfl, hr, ha⟩
  unfold PyCore.store; rw [pplace_kont, hq]; cases q <;> rfl

/-- PyCore unsets a fresh name its frame binds (a handler's exit). -/
theorem punset0 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true)
    (hfo : FOk f.chain (fresh tag l)) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    ∃ t1 g', PyCore.unsetThen t f' fs' (fresh tag l) c' k' = some t1 ∧
      At0 p H s t1 f fs g' fs' ∧ g'.ctrl = c' ∧ g'.kont = k' ∧
      Agree (· = l) (rdOf t f') (ownOf t f') (rdOf t1 g') (ownOf t1 g') := by
  obtain ⟨q, hq, A1, -, ha⟩ := pwrite0 A htag hfo none c' k'
  exact ⟨_, _, by unfold PyCore.unsetThen; rw [hq], A1, rfl, rfl, ha⟩

/-- Unsetting a running handler's name in both runs. -/
theorem unset0 (A : At0 p H s t f fs f' fs') {U : Label → Prop} {x : Option Name} {x' : Name}
    (hx : HOk f.chain U x x') (c : Sem.Ctrl σ) (k : List (Sem.Kont σ)) (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ))
    (hen : EnterSub k f.kont := by esub) :
    ∃ s1 t1 g g', Sem.unsetThen s f fs x c k = some s1 ∧ PyCore.unsetThen t f' fs' x' c' k' = some t1 ∧
      At0 p H s1 t1 g fs g' fs' ∧ g.chain = f.chain ∧ g.ctrl = c ∧ g.kont = k ∧ g'.ctrl = c' ∧ g'.kont = k' ∧
      Agree U (rdOf t f') (ownOf t f') (rdOf t1 g') (ownOf t1 g') := by
  rcases hx with ⟨rfl, hx'⟩ | ⟨rfl, ⟨lh, rfl, hU⟩, hfo⟩
  · have hp := place_eq A.hf hx'
    cases hq : Sem.place f x' with
    | none =>
      rw [hq] at hp
      exact ⟨_, _, _, _, by simp only [Sem.unsetThen, Option.bind, hq]; rfl,
        by unfold PyCore.unsetThen; rw [hp]; rfl, A.upd c k c' k' hen, rfl, rfl, rfl, rfl, rfl, Agree.refl _ _ _⟩
    | some q =>
      rw [hq] at hp
      obtain ⟨A1, hch, ha⟩ := write0 A hq hx' none c k c' k' hen
      exact ⟨_, _, _, _, by simp only [Sem.unsetThen, Option.bind, hq], by unfold PyCore.unsetThen; rw [hp]; cases q <;> rfl,
        A1, hch, rfl, rfl, rfl, rfl, ha.mono fun _ h => h.elim⟩
  · obtain ⟨t1, g', e2, A1, h1, h2, ha⟩ := punset0 A (by decide) hfo c' k'
    exact ⟨_, t1, _, g', by unfold Sem.unsetThen; rfl, e2, A1.updS c k hen, rfl, rfl, rfl, h1, h2,
      ha.mono fun l h => h ▸ hU⟩

/-- PyCore's `$set` of a fresh name: its frame's own cell. -/
theorem pcell0 (A : At0 p H s t f fs f' fs') {tag : String} {l : Label} (htag : tagOk tag = true) (v : Val)
    (c' : PyCore.Ctrl σ) (k' : List (PyCore.Kont σ)) :
    At0 p H s { t with cells := t.cells.insert (f'.id, fresh tag l) v, stack := { f' with ctrl := c', kont := k' } :: fs' }
      f fs { f' with ctrl := c', kont := k' } fs' ∧
    ownOf { t with cells := t.cells.insert (f'.id, fresh tag l) v, stack := { f' with ctrl := c', kont := k' } :: fs' }
      { f' with ctrl := c', kont := k' } (fresh tag l) = some v ∧
    Agree (· = l) (rdOf t f') (ownOf t f')
      (rdOf { t with cells := t.cells.insert (f'.id, fresh tag l) v, stack := { f' with ctrl := c', kont := k' } :: fs' }
        { f' with ctrl := c', kont := k' })
      (ownOf { t with cells := t.cells.insert (f'.id, fresh tag l) v, stack := { f' with ctrl := c', kont := k' } :: fs' }
        { f' with ctrl := c', kont := k' }) := by
  have hd := dot_fresh tag l
  refine ⟨A.write A.hs rfl (A.hf.upd f.ctrl f.kont c' k') rfl rfl rfl rfl rfl (fun b hb => ?_) A.glob
      (fun h' hh => agree_of (P := fun _ => False) (fun _ _ _ _ h => h)
        (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun z _ => ?_) fun _ _ _ => rfl)) rfl rfl rfl rfl rfl rfl rfl,
    by simp [ownOf, ownAt], agree_of (P := (· = fresh tag l)) (fun tag' l' ht hl => fresh_ne ht htag hl)
      (rd_same rfl rfl rfl (fun _ _ _ => rfl) (fun z hz => ?_) fun _ _ _ => rfl)⟩
  · simp only [pCell, Std.HashMap.getElem?_insert, beq_iff_eq]; rw [ite_ne]; exact A.cells b hb
    rintro rfl; exact hb hd
  · have hne := (A.below hh).1
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq]; rw [ite_ne]; intro e; exact hne (congrArg Prod.fst e).symm
  · simp only [Std.HashMap.getElem?_insert, beq_iff_eq]; rw [ite_ne]; intro e; exact hz (congrArg Prod.snd e).symm

/-- PyCore reads a fresh name the relation's reading gives. -/
theorem readName_rd {t : PyCore.Config σ} {f' : PyCore.Frame σ} {x : Name} {v : Val} (h : rdOf t f' x = some v) :
    PyCore.readName I t f' x none = .ok v := by
  simp only [rdOf, rdAt] at h
  simp only [PyCore.readName, PyCore.place]
  cases hc : f'.cls x <;> simp only [hc] at h ⊢
  case glob =>
    cases hk : f'.kind <;> simp only [hk] at h
    case mod => simp [PyCore.lookupGlobal, h]
    all_goals cases h
  case loc => revert h; cases f'.kind <;> intro h <;> simp [h]
  case free => cases h

/-- PyCore's step by the top frame's control, the frame passed whole (so that a frame built from it
keeps `f'.ctrl` unrewritten). -/
theorem pstep_val {v : Val} (ht : t.stack = f' :: fs') (hc : f'.ctrl = .val v) :
    PyCore.step I t = PyCore.valStep I t f' fs' v := by simp only [PyCore.step, ht]; rw [hc]
theorem pstep_done (ht : t.stack = f' :: fs') (hc : f'.ctrl = .exec []) :
    PyCore.step I t = PyCore.doneStep t f' fs' := by simp only [PyCore.step, ht]; rw [hc]
theorem pstep_exec {st : PyCore.Stmt} {ss : PS} (ht : t.stack = f' :: fs') (hc : f'.ctrl = .exec (st :: ss)) :
    PyCore.step I t = PyCore.execStep I t f' fs' st ss := by simp only [PyCore.step, ht]; rw [hc]
theorem pstep_ev {e : PE} (ht : t.stack = f' :: fs') (hc : f'.ctrl = .ev e) :
    PyCore.step I t = PyCore.evalStep I t f' fs' e := by simp only [PyCore.step, ht]; rw [hc]
theorem pstep_raise {v : Val} (ht : t.stack = f' :: fs') (hc : f'.ctrl = .raise v) :
    PyCore.step I t = PyCore.raiseStep t f' fs' v := by simp only [PyCore.step, ht]; rw [hc]
theorem pstep_retv {v : Val} (ht : t.stack = f' :: fs') (hc : f'.ctrl = .retv v) :
    PyCore.step I t = PyCore.retStep t f' fs' v := by simp only [PyCore.step, ht]; rw [hc]
theorem pstep_brk (ht : t.stack = f' :: fs') (hc : f'.ctrl = .brk) :
    PyCore.step I t = PyCore.brkStep t f' fs' := by simp only [PyCore.step, ht]; rw [hc]
theorem pstep_cont (ht : t.stack = f' :: fs') (hc : f'.ctrl = .cont) :
    PyCore.step I t = PyCore.contStep t f' fs' := by simp only [PyCore.step, ht]; rw [hc]

/-- Every node of a PyCore path through configurations evaluating no node is covered. -/
theorem cover_none {zs : List (Sem.Config σ)} {ys : List (PyCore.Config σ)} (h : ∀ y ∈ ys, PyCore.focus y = none) :
    Cover (Touch p) pfocus H zs ys := by
  intro y hy x hx; have := pfocus_le hx; rw [h y hy] at this; cases this

/-- One step on each side, the top frames' code then `c ~ c'`, `k ~ k'` (at the new configurations'
reading), PyCore's step evaluating no node. -/
theorem goal11 {s1 : Sem.Config σ} {t1 : PyCore.Config σ} {g : Sem.Frame σ} {g' : PyCore.Frame σ} {U : Label → Prop}
    {i : Bool} (A1 : At0 p H s1 t1 g fs g' fs') (e1 : Sem.step I s = some s1) (e2 : PyCore.step I t = some t1)
    (hc : CR p g.chain U i g.ctrl g'.ctrl) (hk : KRel (cx p H (rdOf t1 g') (ownOf t1 g') g) U i g.kont g'.kont)
    (hf : PyCore.focus t = none) : Goal I p H s t :=
  goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen (A1.crel hc hk))
    (cover_none fun y hy => by simp at hy; subst hy; exact hf)

end Writes

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem val_walrusK (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v : Val} {y : Name}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .walrusK y :: K0) (hK' : f'.kont = .walrus y :: K0') (hy : ¬ Dot y) (hk : KRel A.x U true K0 K0') :
    Goal I p H s t := by
  obtain ⟨s1, t1, g, g', e1, e2, A1, hch, hgk, hgk', hcc, ha⟩ :=
    store0 A.zero hy v (.val v) K0 (.val v) K0' (by rw [hK, KRel.kexc hk]; rfl)
  refine goal11 A1 (by simp [Sem.step, A.hs, hc, Sem.valStep, hK]; exact e1)
    (by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2) (U := U) (i := true) ?_
    (by rw [hgk, hgk']; exact krel_move hk hch (ha.mono fun _ h => h.elim) fun _ h => h)
    (by simp [PyCore.focus, A.ht, hc'])
  rcases hcc with ⟨h1, h2⟩ | ⟨e, h1, h2⟩ <;> rw [h1, h2] <;> constructor

theorem val_assignN (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v : Val} {y : Name}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .assignN y :: K0) (hK' : f'.kont = .assign y :: K0') (hy : ¬ Dot y) (hk : KRel A.x U false K0 K0') :
    Goal I p H s t := by
  obtain ⟨s1, t1, g, g', e1, e2, A1, hch, hgk, hgk', hcc, ha⟩ :=
    store0 A.zero hy v (.exec []) K0 (.exec []) K0' (by rw [hK, KRel.kexc hk]; rfl)
  refine goal11 A1 (by simp [Sem.step, A.hs, hc, Sem.valStep, hK]; exact e1)
    (by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2) (U := U) (i := false) ?_
    (by rw [hgk, hgk']; exact krel_move hk hch (ha.mono fun _ h => h.elim) fun _ h => h)
    (by simp [PyCore.focus, A.ht, hc'])
  rcases hcc with ⟨h1, h2⟩ | ⟨e, h1, h2⟩ <;> rw [h1, h2]
  · exact .exec (goodB_nil _ U) (by simp)
  · constructor

theorem val_catchT_true (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {ex : Val} {y : Option Name}
    {y' : Name} {hb : List Stmt} {hs : List Handler} {u : List Stmt} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hc : f.ctrl = .val (.bool true)) (hc' : f'.ctrl = .val (.bool true))
    (hK : f.kont = .catchT ex y hb hs u :: K0) (hK' : f'.kont = .catchT ex y' (trB f.chain hb) (trHs f.chain hs) (trB f.chain u) :: K0')
    (hnc : NoCompH f.chain) (h1 : GoodB p f.chain U hb) (h2 : GoodHs p f.chain U hs) (h3 : GoodB p f.chain U u) (hx : XOk f.chain U y y')
    (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  have hf : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  rcases hx with ⟨y0, rfl, rfl, hy⟩ | ⟨rfl, ⟨lh, rfl, hU⟩, hfo⟩
  · obtain ⟨s1, t1, g, g', e1, e2, A1, hch, hgk, hgk', hcc, ha⟩ :=
      store0 A.zero hy ex (.exec hb) (.handler (some (mangle (priv f.chain) y0)) ex :: K0) (.exec (trB f.chain hb))
        (.handler (mangle (priv f.chain) y0) ex :: K0') (by rw [hK]; rfl)
    refine goal11 A1 (by simp [Sem.step, A.hs, hc, Sem.valStep, hK, Sem.mg]; exact e1)
      (by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2) (U := U) (i := false) ?_
      (by rw [hgk, hgk']; exact .core (.handler (by show NoCompH g.chain; rw [hch]; exact hnc)
        (by show HOk g.chain U _ _; rw [hch]; exact .inl ⟨rfl, hy⟩)
        (krel_move hk hch (ha.mono fun _ h => h.elim) fun _ h => h))) hf
    rcases hcc with ⟨h1', h2'⟩ | ⟨e, h1', h2'⟩ <;> rw [h1', h2']
    · rw [hch]; exact .exec h1 fun _ => hnc
    · constructor
  · obtain ⟨t1, g', e2, A1, hgc, hgk, hrd, ha⟩ :=
      pstore0 A.zero (by decide) hfo ex (.exec (trB f.chain hb)) (.handler (fresh "e" lh) ex :: K0')
    refine goal11 (A1.updS (.exec hb) (.handler none ex :: K0))
      (by simp [Sem.step, A.hs, hc, Sem.valStep, hK, Sem.setC]) (by rw [pstep_val A.ht hc']; simp only [PyCore.valStep, hK']; exact e2)
      (U := U) (i := false) (by rw [hgc]; exact .exec h1 fun _ => hnc)
      (by rw [hgk]; exact .core (.handler hnc (.inr ⟨rfl, ⟨lh, rfl, hU⟩, hfo⟩)
        (krel_move hk rfl (ha.mono fun _ h => h ▸ hU) fun _ h => h))) hf

end

/-! ### Entering a call of a core constant on an argument record -/

theorem constVal_args : Py.constVal I "$args" = .data "$args" [] := by simp [Py.constVal, Py.emptyArgs]

/-- PyCore evaluates an argument record's outer `,` nodes down to its start. -/
theorem rec_path (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (r : Label) :
    ∀ (rest : List PE) (init : PE) (K : List (PyCore.Kont σ)),
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with ctrl := .ev (rest.foldl (fun acc e => .bin r "," acc e) init), kont := K } :: fs' }
      { t with stack := { f' with ctrl := .ev init, kont := rest.map (.binL ",") ++ K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = r
  | [], init, K => ⟨[], .nil _, by simp⟩
  | e :: rest, init, K => by
    obtain ⟨ys, py, hy⟩ := rec_path t f' fs' r rest (.bin r "," init e) K
    refine ⟨ys ++ [{ t with stack := { f' with ctrl := .ev (.bin r "," init e), kont := rest.map (.binL ",") ++ K } :: fs' }],
      py.append (.cons (by simp [PyCore.step, PyCore.evalStep, PyCore.top]) (.nil _)), ?_⟩
    intro y hy' x hx
    rcases List.mem_append.1 hy' with hy' | hy'
    · exact hy y hy' x hx
    · simp at hy'; subst hy'; simp [PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm

/-- PyCore enters the call `ccR r g (e :: rest)` of a core constant on an argument record: it
reaches the first argument, the record's other arguments and the constant's call waiting. Every node it
focuses on the way is labelled `r`. -/
theorem cc_enter (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) (r : Label) (g : String)
    (e : PE) (rest : List PE) (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .ev (ccR r g (e :: rest)), kont := K } :: fs' }
      { t with stack := { f' with ctrl := .ev e, kont := recK [] rest (.callA (Py.constVal I g) :: K) } :: fs' } ys ∧
      ys ≠ [] ∧ ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = r := by
  obtain ⟨ys, py, hy⟩ := rec_path (I := I) t f' fs' r rest (.bin r "," (.const r "$args") e)
    (.callA (Py.constVal I g) :: K)
  let c0 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (ccR r g (e :: rest)), kont := K } :: fs' }
  let c1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const r g), kont := .callF (recR r (e :: rest)) :: K } :: fs' }
  let c2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (Py.constVal I g), kont := .callF (recR r (e :: rest)) :: K } :: fs' }
  let K4 : List (PyCore.Kont σ) := rest.map (.binL ",") ++ .callA (Py.constVal I g) :: K
  let c4 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.bin r "," (.const r "$args") e), kont := K4 } :: fs' }
  let c5 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const r "$args"), kont := .binL "," e :: K4 } :: fs' }
  let c6 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" []), kont := .binL "," e :: K4 } :: fs' }
  refine ⟨c0 :: c1 :: c2 :: ys ++ [c4, c5, c6], ?_, by simp, ?_⟩
  · let c3 : PyCore.Config σ := { t with stack := { f' with
        ctrl := .ev (rest.foldl (fun acc e => .bin r "," acc e) (.bin r "," (.const r "$args") e)),
        kont := .callA (Py.constVal I g) :: K } :: fs' }
    refine .cons (a' := c1) (by simp [c0, c1, ccR, PyCore.step, PyCore.evalStep, PyCore.top])
      (.cons (a' := c2) ?_ (.cons (a' := c3) ?_ ?_))
    · simp [c1, c2, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK]
    · simp [c2, c3, PyCore.step, PyCore.valStep, PyCore.top, recR]
    · refine py.append (.cons (a' := c5) (by simp [c4, c5, K4, PyCore.step, PyCore.evalStep, PyCore.top])
        (.cons (a' := c6) (by simp [c5, c6, K4, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args])
          (.cons (by simp [c6, K4, PyCore.step, PyCore.valStep, PyCore.top, recK]) (.nil _))))
  · intro y hy' x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy'
    rcases hy' with (rfl | rfl | rfl | hy') | rfl | rfl | rfl
    · simp [c0, PyCore.focus, ccR, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c1, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c2, PyCore.focus] at hx
    · exact hy y hy' x hx
    · simp [c4, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c5, PyCore.focus, PyCore.Expr.label] at hx; exact hx.symm
    · simp [c6, PyCore.focus] at hx

/-! ### Stores into targets

Surf's `store tg v` and PyCore's code of the target (`trT C src tg`, then `rest`), the source `src`
reading `v` from a fresh name outside the budget (`SrcR`), and the continuation after the target.
The result is one simulation step from the configurations at the store, which a case composes with the
Surf step that reached the store (`SimStep.pre`). -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem touch_store {tg : Expr} {v : Val} (hs : s.stack = f :: fs) (hc : f.ctrl = .store tg v) :
    Touch p s tg.label := .inr (by rw [hs]; simp [TouchF, hc, lbl_eq])

theorem sub_lt_div {lt k : Label} (hk : k < 64) : sub lt k / 64 = lt := sub_div lt k hk

/-- The nodes PyCore focuses on the way, all made for the node `l` that `s` touches. -/
theorem cover_of {ys : List (PyCore.Config σ)} {zs : List (Sem.Config σ)} {l : Label} (hs : s ∈ zs)
    (ht : Touch p s l) (h : ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x / 64 = l) : Cover (Touch p) pfocus H zs ys :=
  fun y hy x hx => .inr ⟨s, hs, by rw [h y hy x (pfocus_le hx)]; exact ht⟩

/-- PyCore evaluates a target's source (`SrcR`) to its value, focusing nodes made for the target only. -/
theorem srcR_eval {x : Cx} (hx : x.rd = rdOf t f') {U : Label → Prop} {lt : Label} {src : PE} {v : Val}
    (hs : SrcR x U lt src v) (K : List (PyCore.Kont σ)) :
    ∃ ys, Path (PyCore.step I) { t with stack := { f' with ctrl := .ev src, kont := K } :: fs' }
      { t with stack := { f' with ctrl := .val v, kont := K } :: fs' } ys ∧ ys ≠ [] ∧
      ∀ y ∈ ys, ∀ z, PyCore.focus y = some z → z / 64 = lt := by
  cases hs with
  | @name k tag l _ hk64 htag hl hv =>
    rw [hx] at hv
    let g1 : PyCore.Frame σ := { f' with ctrl := .ev (.name (sub lt k) (fresh tag l) none), kont := K }
    let t1 : PyCore.Config σ := { t with stack := g1 :: fs' }
    have hr : PyCore.readName I t1 g1 (fresh tag l) none = .ok v := readName_rd hv
    refine ⟨[t1], .cons ?_ (.nil _), by simp, ?_⟩
    · rw [pstep_ev (e := .name (sub lt k) (fresh tag l) none) rfl rfl]
      show PyCore.top t1 fs' { g1 with ctrl := PyCore.resCtrl (g1 :: fs') (PyCore.readName I t1 g1 (fresh tag l) none) } = _
      rw [hr]; rfl
    · intro y hy z hz; simp at hy; subst hy; simp [t1, g1, PyCore.focus, PyCore.Expr.label] at hz
      rw [← hz]; exact sub_div _ _ hk64
  | @item l i ws w hl hv hi =>
    rw [hx] at hv
    obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub lt 59) (Gadget.item i).name
      (.name (sub lt 61) (fresh "u" l) none) [] K
    rw [kc_gad I (.item i) trivial] at pc
    let K1 : List (PyCore.Kont σ) := recK [] [] (.callA (.prim (Gadget.item i).name) :: K)
    let g1 : PyCore.Frame σ := { f' with ctrl := .ev (.name (sub lt 61) (fresh "u" l) none), kont := K1 }
    let t1 : PyCore.Config σ := { t with stack := g1 :: fs' }
    let t2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.tuple ws), kont := K1 } :: fs' }
    let K3 : List (PyCore.Kont σ) := .callA (.prim (Gadget.item i).name) :: K
    let t3 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" [.tuple ws]), kont := K3 } :: fs' }
    have hr : PyCore.readName I t1 g1 (fresh "u" l) none = .ok (.tuple ws) := readName_rd hv
    refine ⟨ys ++ [t1, t2, t3], pc.append (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))), by simp, ?_⟩
    · rw [pstep_ev (e := .name (sub lt 61) (fresh "u" l) none) rfl rfl]
      show PyCore.top t1 fs' { g1 with ctrl := PyCore.resCtrl (g1 :: fs') (PyCore.readName I t1 g1 (fresh "u" l) none) } = _
      rw [hr]; rfl
    · simp [t2, t3, K1, K3, recK, PyCore.step, PyCore.valStep, PyCore.top]
    · simp [t3, K3, PyCore.step, PyCore.valStep, PyCore.callStep, gad_name (.item i) trivial, PyCore.gadgetStep,
        PyCore.argList, hi, PyCore.top]
    · intro y hy z hz
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | rfl | rfl | rfl
      · rw [hfoc y hy z hz]; exact sub_div _ _ (by omega)
      · simp [t1, g1, PyCore.focus, PyCore.Expr.label] at hz; rw [← hz]; exact sub_div _ _ (by omega)
      · simp [t2, PyCore.focus] at hz
      · simp [t3, K3, PyCore.focus] at hz

/-- A name target: stored in both runs (or `NameError` in both). -/
theorem store_name (A : At0 p H s t f fs f' fs') {lt : Label} {y : Name} {v : Val} {src : PE} {rest : PS}
    {U : Label → Prop} (hc : f.ctrl = .store (.name lt y) v)
    (hc' : f'.ctrl = .exec (.assign (sub lt 0) (mangle (priv f.chain) y) src :: rest))
    (hy : ¬ Dot (mangle (priv f.chain) y)) (hs : SrcR (cx p H (rdOf t f') (ownOf t f') f) U lt src v)
    (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U false f.kont (.seq rest :: f'.kont)) : GoalS I p H s t := by
  let y' := mangle (priv f.chain) y
  let K' : List (PyCore.Kont σ) := .assign y' :: .seq rest :: f'.kont
  let t2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val v, kont := K' } :: fs' }
  obtain ⟨ys, pe, hys, hfoc⟩ := srcR_eval (I := I) (t := t) (f' := f') (fs' := fs') rfl hs K'
  have A2 := A.updT (.val v) K'
  obtain ⟨s1, t3, g, g', e1, e2, A3, hch, hgk, hgk', hcc, ha⟩ :=
    store0 A2 hy v (.exec []) f.kont (.exec []) (.seq rest :: f'.kont) (KRel.kexc hk)
  have st1 : PyCore.step I t = some { t with stack := { f' with ctrl := .ev src, kont := K' } :: fs' } := by
    rw [pstep_exec A.ht hc']; rfl
  have st3 : PyCore.step I t2 = some t3 := by rw [pstep_val rfl rfl]; exact e2
  refine goalS_b (.cons (by simp only [Sem.step, A.hs, hc, Sem.storeStep]; exact e1) (.nil _)) (by simp)
    (.cons st1 (pe.append (.cons st3 (.nil _)))) (by simp) (crelI_seen (A3.crel (U := U) (i := false) ?_ ?_))
    (cover_of (l := lt) (by simp) (touch_store A.hs hc) ?_)
  · rcases hcc with ⟨h1, h2⟩ | ⟨e, h1, h2⟩ <;> rw [h1, h2]
    · exact .exec (goodB_nil _ U) (by simp)
    · constructor
  · rw [hgk, hgk']; exact krel_move hk hch (ha.mono fun _ h => h.elim) fun _ h => h
  · intro y hy x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | hy | rfl
    · simp [PyCore.focus, A.ht, hc', PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    · exact hfoc y hy x hx
    · simp [t2, PyCore.focus] at hx

theorem At0.mono_H {H' : Label → Prop} (A : At0 p H s t f fs f' fs') (hH : ∀ l, H l → H' l) :
    At0 p H' s t f fs f' fs' :=
  ⟨A.hs, A.ht, A.hf, fun S C e => hH _ (A.hl S C e), all2_mono (fun _ _ h => h.mono_H hH) A.hfs,
    fun o => optRel_mono (fun _ _ h => h.mono_H hH) (A.objs o), A.cells, A.glob, A.out, A.next, A.res, A.st, A.wait,
    A.ids, A.enter⟩

theorem seen_s {zs : List (Sem.Config σ)} {l : Label} (hs : s ∈ zs) (h : Touch p s l) : Seen (Touch p) H zs l :=
  .inr ⟨s, hs, h⟩

/-- An attribute target `o.a`: the object is evaluated next, the source and `setattr` waiting. -/
theorem store_attr (A : At0 p H s t f fs f' fs') {lt : Label} {o : Expr} {a : Name} {v : Val} {src : PE} {rest : PS}
    {U : Label → Prop} (hc : f.ctrl = .store (.attr lt o a) v)
    (hc' : f'.ctrl = .exec (.expr (sub lt 0) (cc lt 1 ("$op:setattr:" ++ mangle (priv f.chain) a) [trE f.chain o, src]) :: rest))
    (hg : GoodE p f.chain U (.attr lt o a)) (hs : SrcR (cx p H (rdOf t f') (ownOf t f') f) U lt src v)
    (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U false f.kont (.seq rest :: f'.kont))
    (hop : Py.constVal I ("$op:setattr:" ++ mangle (priv f.chain) a) = .op (.setattr (mangle (priv f.chain) a))) :
    GoalS I p H s t := by
  let a' := mangle (priv f.chain) a
  let K' : List (PyCore.Kont σ) := .exprS :: .seq rest :: f'.kont
  obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub lt 1) ("$op:setattr:" ++ a') (trE f.chain o) [src] K'
  rw [hop] at pc
  have st1 : PyCore.step I t = some { t with stack := { f' with
      ctrl := .ev (ccR (sub lt 1) ("$op:setattr:" ++ a') [trE f.chain o, src]), kont := K' } :: fs' } := by
    rw [pstep_exec A.ht hc']; rfl
  have hH : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  have ht := touch_store (p := p) A.hs hc
  refine goalS_b (.cons (by simp [Sem.step, A.hs, hc, Sem.storeStep, Sem.setC]) (.nil _)) (by simp)
    (.cons st1 pc) (by simp) (.inl (((A.upd (.ev o) (.stAttr (Sem.mg f a) v :: f.kont) (.ev (trE f.chain o))
      (recK [] [src] (.callA (.op (.setattr a')) :: K'))).mono_H hH).crel (U := U) (i := true) (.ev (by subg))
      (.asg (.stAttr (lt := lt) (seen_s (by simp) ht) (srcR_ext ⟨hH, Agree.refl _ _ _⟩ hs)
        (KRel.ext ⟨hH, Agree.refl _ _ _⟩ hk)))))
    (cover_of (l := lt) (by simp) ht ?_)
  intro y hy x hx
  rcases List.mem_cons.1 hy with rfl | hy
  · simp [PyCore.focus, A.ht, hc', PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)

/-- A subscript target `o[i]`: the object is evaluated next, the index, the source and `setitem` waiting. -/
theorem store_sub (A : At0 p H s t f fs f' fs') {lt : Label} {o i : Expr} {v : Val} {src : PE} {rest : PS}
    {U : Label → Prop} (hc : f.ctrl = .store (.sub lt o i) v)
    (hc' : f'.ctrl = .exec (.expr (sub lt 0) (cc lt 1 "$op:setitem" [trE f.chain o, trE f.chain i, src]) :: rest))
    (hg : GoodE p f.chain U (.sub lt o i)) (hs : SrcR (cx p H (rdOf t f') (ownOf t f') f) U lt src v)
    (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U false f.kont (.seq rest :: f'.kont))
    (hop : Py.constVal I "$op:setitem" = .op .setitem) : GoalS I p H s t := by
  let K' : List (PyCore.Kont σ) := .exprS :: .seq rest :: f'.kont
  obtain ⟨ys, pc, hys, hfoc⟩ := cc_enter (I := I) t f' fs' (sub lt 1) "$op:setitem" (trE f.chain o) [trE f.chain i, src] K'
  rw [hop] at pc
  have st1 : PyCore.step I t = some { t with stack := { f' with
      ctrl := .ev (ccR (sub lt 1) "$op:setitem" [trE f.chain o, trE f.chain i, src]), kont := K' } :: fs' } := by
    rw [pstep_exec A.ht hc']; rfl
  have hH : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
  have ht := touch_store (p := p) A.hs hc
  refine goalS_b (.cons (by simp [Sem.step, A.hs, hc, Sem.storeStep, Sem.setC]) (.nil _)) (by simp)
    (.cons st1 pc) (by simp) (.inl (((A.upd (.ev o) (.stSubL i v :: f.kont) (.ev (trE f.chain o))
      (recK [] [trE f.chain i, src] (.callA (.op .setitem) :: K'))).mono_H hH).crel (U := U) (i := true) (.ev (by subg))
      (.asg (.stSubL (lt := lt) (seen_s (by simp) ht) (by subg) (srcR_ext ⟨hH, Agree.refl _ _ _⟩ hs)
        (KRel.ext ⟨hH, Agree.refl _ _ _⟩ hk)))))
    (cover_of (l := lt) (by simp) ht ?_)
  intro y hy x hx
  rcases List.mem_cons.1 hy with rfl | hy
  · simp [PyCore.focus, A.ht, hc', PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · rw [hfoc y hy x hx]; exact sub_div _ _ (by omega)

end

/-- No PyCore item is an occurrence of a comparison's fresh name: the final translation keeps it
inside the constants of `$set`/`$get`. Kept as a premise of `fok_of` for its callers. -/
def IsCmp (_ : Label) : Prop := False

/-- A fresh name the code of `p` binds in the scope at the head of `C` is bound there (`FOk`). -/
theorem fok_of (W : WF p) {L : Label} {x : Name} {C : List Scope} (hi : PyCore.Item.occ L x (trChain C) ∈ PI p)
    (hx : IsFresh x) (hL : ¬ IsCmp L) : FOk C x := by
  have hc := fresh_canon p W.nodup W.nodot W.reg L x (trChain C) hi hx
  unfold FOk
  cases C with
  | nil => simp [trChain, PyCore.clsOf]
  | cons S C0 =>
    simp only [trChain, List.map_cons, patB, List.cons.injEq] at hc ⊢
    have h1 := hc.1
    simp only [xf, Prod.mk.injEq] at h1
    obtain ⟨hb, hw, hg, hn⟩ := h1
    have hb' : PyCore.Fact.bind x ∈ (trScope C0 S).facts := by simpa using hb
    have hw' : PyCore.Fact.wal x ∉ (trScope C0 S).facts := by simpa using hw
    have hg' : PyCore.Fact.glob x ∉ (trScope C0 S).facts := by simpa using hg
    have hn' : PyCore.Fact.nonloc x ∉ (trScope C0 S).facts := by simpa using hn
    simp [PyCore.clsOf, PyCore.Scope.declG, PyCore.Scope.declN, PyCore.Scope.walrus, PyCore.Scope.binds, hb', hw',
      hg', hn']

theorem not_cmp (l k : Nat) (_hk : k < 64) (_h1 : k ≠ 49) (_h2 : k ≠ 52) : ¬ IsCmp (sub l k) := id


/-! ## The homomorphic cases on the write infrastructure -/


theorem items_boolChainIn {C : List PyCore.Scope} (l : Label) (o : Bool) :
    ∀ (L : List PE), L ≠ [] → ∀ x, (∃ q ∈ L, x ∈ PyCore.itemsE R0 C q) →
      x ∈ PyCore.itemsE R0 C (boolChainIn l o L)
  | [], h, _, _ => absurd rfl h
  | [q], _, x, ⟨q', hq, hx⟩ => by simp at hq; subst hq; simpa [boolChainIn] using hx
  | q :: q2 :: L, _, x, ⟨q', hq, hx⟩ => by
    simp only [boolChainIn, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact .inl hx
    · exact .inr (items_boolChainIn l o (q2 :: L) (by simp) x ⟨q', hq, hx⟩)

theorem items_boolChain {C : List PyCore.Scope} (l : Label) (o : Bool) :
    ∀ (L : List PE), L ≠ [] → ∀ x, (∃ q ∈ L, x ∈ PyCore.itemsE R0 C q) →
      x ∈ PyCore.itemsE R0 C (boolChain l o L)
  | [], h, _, _ => absurd rfl h
  | [q], _, x, ⟨q', hq, hx⟩ => by simp at hq; subst hq; simpa [boolChain] using hx
  | q :: q2 :: L, _, x, ⟨q', hq, hx⟩ => by
    simp only [boolChain, PyCore.itemsE, r0_e, Option.isSome_none, Bool.false_eq_true, ite_false, List.mem_append]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact .inl hx
    · exact .inr (items_boolChainIn l o (q2 :: L) (by simp) x ⟨q', hq, hx⟩)

theorem mem_trEs {C : List Scope} {e : Expr} : ∀ {es : List Expr}, e ∈ es → trE C e ∈ trEs C es
  | [], h => by simp at h
  | a :: es, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [trEs]
    · simp [trEs, mem_trEs h]

theorem mem_trLs {C : List Scope} {e : Expr} : ∀ {es : List Expr}, e ∈ es → (e.label, trE C e) ∈ trLs C es
  | [], h => by simp at h
  | a :: es, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [trLs]
    · simp [trLs, mem_trLs h]

theorem okEs_mem {e : Expr} : ∀ {es : List Expr}, okEs es = true → e ∈ es → okE e = true
  | [], _, h => by simp at h
  | a :: es, ho, h => by
    simp only [okEs, Bool.and_eq_true] at ho
    rcases List.mem_cons.1 h with rfl | h
    · exact ho.1
    · exact okEs_mem ho.2 h

theorem itemsEs_mem {C : List Scope} {e : Expr} {x : Item} : ∀ {es : List Expr}, e ∈ es → x ∈ itemsE C e → x ∈ itemsEs C es
  | [], h, _ => by simp at h
  | a :: es, h, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [itemsEs, hx]
    · simp [itemsEs, itemsEs_mem h hx]

theorem labelsEs_mem {e : Expr} {l : Label} : ∀ {es : List Expr}, e ∈ es → l ∈ labelsE e → l ∈ labelsEs es
  | [], h, _ => by simp at h
  | a :: es, h, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [labelsEs, hx]
    · simp [labelsEs, labelsEs_mem h hx]

theorem nodup_labelsEs {e : Expr} : ∀ {es : List Expr}, e ∈ es → (labelsEs es).Nodup → (labelsE e).Nodup
  | [], h, _ => by simp at h
  | a :: es, h, hn => by
    simp only [labelsEs, List.nodup_append] at hn
    rcases List.mem_cons.1 h with rfl | h
    · exact hn.1
    · exact nodup_labelsEs h hn.2.1

theorem touchEs_mem {e : Expr} {x : Label × Expr} : ∀ {es : List Expr}, e ∈ es → x ∈ touchE e → x ∈ touchEs es
  | [], h, _ => by simp at h
  | e' :: es, h, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [touchEs, hx]
    · simp [touchEs, touchEs_mem h hx]

theorem touch_unstar {e : Expr} {x : Label × Expr} (h : x ∈ touchE (unstar e)) : x ∈ touchE e := by
  cases e <;> simp_all [unstar, touchE]

theorem goodEs_boolop {C : List Scope} {U : Label → Prop} {l op} {es : List Expr}
    (h : GoodE p C U (.boolop l op es)) : GoodEs p C U es := by
  intro e he
  have hok := h.ok; simp only [okE, Bool.and_eq_true] at hok
  refine ⟨fun x hx => h.s x ?_, fun x hx => h.t x ?_, okEs_mem hok.2 he, fun l' hl => h.u l' ?_, h.pv,
    nodup_labelsEs he (by have := h.nd; simp only [labelsE, List.nodup_cons] at this; exact this.2),
    fun x hx => h.tch x (by simp only [touchE]; exact touchEs_mem he hx)⟩
  · simp only [itemsE]; exact itemsEs_mem he hx
  · simp only [trE]
    exact items_boolChain _ _ _ (by cases es <;> simp_all [trEs]) x ⟨_, mem_trEs he, hx⟩
  · simp only [labelsE, List.mem_cons]; exact .inr (labelsEs_mem he hl)

theorem ev_boolop (l op es) : EvCase I p (.boolop l op es) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have hlen := hg.ok; simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at hlen
  have hes := goodEs_boolop hg
  match es, hlen, hes with
  | a :: b :: rest, _, hes =>
    exact A.go11T (c := .ev a) (k := .boolK (op == "And") (b :: rest) :: f.kont)
      (by simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC])
      (by simp [PyCore.step, A.ht, hc', trE, boolChain, trEs, PyCore.evalStep, PyCore.top])
      (.ev (hes a (by simp))) (.core (.boolK (l := l) (seen_s (s := s) (zs := [s]) (by simp) (.inl (by simp [Sem.focus, A.hs, hc, Sem.Expr.lbl])))
        (fun x hx => hes x (List.mem_cons_of_mem _ hx)) hk.seen))
      (cov_ev A hc hc' (by simp [trE, boolChain, trEs, PyCore.Expr.label, Sem.Expr.lbl, sub_div]))

theorem constVal_none : Py.constVal I "$none" = .none := by simp [Py.constVal]

theorem ev_yield_none (l) : EvCase I p (.yield l none) := by
  intro H s t f fs f' fs' U A W hc hc' hg hk
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .val .none, kont := .yieldK :: f.kont } :: fs } := by
    simp [Sem.step, A.hs, hc, Sem.evalStep, Sem.setC]
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const (sub l 1) "$none"), kont := .yieldS :: f'.kont } :: fs' }
  have e2 : PyCore.step I t = some t1 := by
    rw [pstep_ev A.ht hc']; simp [trE, trO, PyCore.evalStep, PyCore.top, t1]
  have e3 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .val .none, kont := .yieldS :: f'.kont } :: fs' } := by
    simp [t1, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_none]
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.cons e3 (.nil _))) (by simp)
    (crelI_seen ((A.zero.upd _ _ _ _).crel (U := U) (i := true) .val (.core (.yieldK hk)))) ?_
  have ht : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Expr.lbl])
  refine cover_of (l := l) (by simp) ht ?_
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · simp [PyCore.focus, A.ht, hc', trE, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t1, PyCore.focus, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)

theorem exec_pass (l) : ExecCase I p (.pass l) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := .seq ss :: f.kont } :: fs } := by
    simp [Sem.step, A.hs, hc, Sem.execStep, Sem.setC]
  let K' : List (PyCore.Kont σ) := .exprS :: .seq (trB f.chain ss) :: f'.kont
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const (sub l 1) "$none"), kont := K' } :: fs' }
  let t2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val .none, kont := K' } :: fs' }
  have e2 : PyCore.step I t = some t1 := by rw [pstep_exec A.ht (by rw [hc']; rfl)]; rfl
  have e3 : PyCore.step I t1 = some t2 := by
    simp [t1, t2, K', PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_none]
  have e4 : PyCore.step I t2 = some { t with stack := { f' with ctrl := .exec [], kont := .seq (trB f.chain ss) :: f'.kont } :: fs' } := by
    simp [t2, K', PyCore.step, PyCore.valStep, PyCore.top]
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.cons e3 (.cons e4 (.nil _)))) (by simp)
    (crelI_seen ((A.zero.upd _ _ _ _).crel (U := U) (i := false) (.exec (goodB_nil _ U) (by simp))
      (krel_seq (hnc (by simp)) hg.tail hk))) ?_
  have ht : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Stmt.lbl])
  refine cover_of (l := l) (by simp) ht ?_
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl
  · simp [PyCore.focus, A.ht, hc', trB, trS, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t1, PyCore.focus, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t2, PyCore.focus] at hx

theorem exec_ret_none (l) : ExecCase I p (.ret l none) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .val .none, kont := .retS :: .seq ss :: f.kont } :: fs } := by
    simp [Sem.step, A.hs, hc, Sem.execStep, Sem.setC]
  let K' : List (PyCore.Kont σ) := .retS :: .seq (trB f.chain ss) :: f'.kont
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const (sub l 1) "$none"), kont := K' } :: fs' }
  have e2 : PyCore.step I t = some t1 := by rw [pstep_exec A.ht (by rw [hc']; rfl)]; rfl
  have e3 : PyCore.step I t1 = some { t with stack := { f' with ctrl := .val .none, kont := K' } :: fs' } := by
    simp [t1, K', PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_none]
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.cons e3 (.nil _))) (by simp)
    (crelI_seen ((A.zero.upd _ _ _ _).crel (U := U) (i := true) .val
      (.core (.retS (krel_seq (hnc (by simp)) hg.tail hk))))) ?_
  have ht : Touch p s l := .inl (by simp [Sem.focus, A.hs, hc, Sem.Stmt.lbl])
  refine cover_of (l := l) (by simp) ht ?_
  intro y hy x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · simp [PyCore.focus, A.ht, hc', trB, trS, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
  · simp [t1, PyCore.focus, PyCore.Expr.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)

/-- PyCore runs a block of `global` (or `nonlocal`) statements, all labelled `L`. -/
theorem decls_run {t : PyCore.Config σ} {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} (L : Label) (glob : Bool)
    (K : List (PyCore.Kont σ)) :
    ∀ xs : List Name, ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with ctrl := .exec (xs.map fun x => if glob then .glob L x else .nonloc L x), kont := K } :: fs' }
      { t with stack := { f' with ctrl := .exec [], kont := K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → x = L
  | [] => ⟨[], .nil _, by simp⟩
  | x :: xs => by
    obtain ⟨ys, hp, hfy⟩ := decls_run L glob K xs
    have e1 : PyCore.step I { t with stack := { f' with ctrl := .exec ((x :: xs).map fun x => if glob then .glob L x else .nonloc L x), kont := K } :: fs' } =
        some { t with stack := { f' with ctrl := .exec [], kont := .seq (xs.map fun x => if glob then .glob L x else .nonloc L x) :: K } :: fs' } := by
      cases glob <;> simp [PyCore.step, PyCore.execStep, PyCore.top]
    have e2 : PyCore.step I { t with stack := { f' with ctrl := .exec [], kont := .seq (xs.map fun x => if glob then .glob L x else .nonloc L x) :: K } :: fs' } =
        some { t with stack := { f' with ctrl := .exec (xs.map fun x => if glob then .glob L x else .nonloc L x), kont := K } :: fs' } := by
      simp [PyCore.step, PyCore.doneStep, PyCore.top]
    refine ⟨_, .cons e1 (.cons e2 hp), ?_⟩
    intro y hy z hz
    simp only [List.mem_cons] at hy
    rcases hy with rfl | rfl | hy
    · cases glob <;> simp [PyCore.focus, PyCore.Stmt.label] at hz <;> exact hz.symm
    · simp [PyCore.focus] at hz
    · exact hfy y hy z hz

theorem exec_decls (l : Label) (xs : List Name) (glob : Bool) {H : Label → Prop} {s : Sem.Config σ}
    {t : PyCore.Config σ} {f : Sem.Frame σ} {fs} {f' : PyCore.Frame σ} {fs'} {U : Label → Prop} {ss : List Stmt}
    (A : At p H s t f fs f' fs')
    (hc : f.ctrl = .exec ((if glob then Stmt.glob l xs else .nonloc l xs) :: ss))
    (hc' : f'.ctrl = .exec (trB f.chain ((if glob then Stmt.glob l xs else .nonloc l xs) :: ss)))
    (hg : GoodB p f.chain U ((if glob then Stmt.glob l xs else .nonloc l xs) :: ss)) (hnc : NoCompH f.chain)
    (hk : KRel A.x U false f.kont f'.kont) : Goal I p H s t := by
  have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec [], kont := .seq ss :: f.kont } :: fs } := by
    cases glob <;> simp [Sem.step, A.hs, hc, Sem.execStep, Sem.setC]
  let ds : PS := (xs.map (mangle (priv f.chain))).map fun x => if glob then .glob (sub l 1) x else .nonloc (sub l 1) x
  have e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .exec ds, kont := .tryE [] [] :: .seq (trB f.chain ss) :: f'.kont } :: fs' } := by
    rw [pstep_exec (st := trS f.chain (if glob then .glob l xs else .nonloc l xs)) (ss := trB f.chain ss) A.ht
      (by rw [hc']; rfl)]
    cases glob <;> simp [ds, trS, blk, PyCore.execStep, PyCore.top, List.map_map] <;> rfl
  obtain ⟨ys, hp, hfy⟩ := decls_run (I := I) (t := t) (f' := f') (fs' := fs') (sub l 1) glob
    (.tryE [] [] :: .seq (trB f.chain ss) :: f'.kont) (xs.map (mangle (priv f.chain)))
  have e3 : PyCore.step I { t with stack := { f' with ctrl := .exec [], kont := .tryE [] [] :: .seq (trB f.chain ss) :: f'.kont } :: fs' } =
      some { t with stack := { f' with ctrl := .exec [], kont := .seq (trB f.chain ss) :: f'.kont } :: fs' } := by
    simp [PyCore.step, PyCore.doneStep, PyCore.top]
  refine goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (hp.append (.cons e3 (.nil _)))) (by simp)
    (crelI_seen ((A.zero.upd _ _ _ _).crel (U := U) (i := false) (.exec (goodB_nil _ U) (by simp))
      (krel_seq hnc hg.tail hk))) ?_
  have ht : Touch p s l := .inl (by cases glob <;> simp [Sem.focus, A.hs, hc, Sem.Stmt.lbl])
  refine cover_of (l := l) (by simp) ht ?_
  intro y hy x hx
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | hy | rfl
  · cases glob <;> simp [PyCore.focus, A.ht, hc', trB, trS, blk, PyCore.Stmt.label] at hx <;>
      rw [← hx] <;> exact sub_div _ _ (by omega)
  · rw [hfy y hy x hx]; exact sub_div _ _ (by omega)
  · simp [PyCore.focus] at hx

theorem exec_glob (l xs) : ExecCase I p (.glob l xs) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact exec_decls l xs true A hc hc' hg (hnc (by simp)) hk

theorem exec_nonloc (l xs) : ExecCase I p (.nonloc l xs) := by
  intro H s t f fs f' fs' U ss A W hc hc' hg hnc hk
  exact exec_decls l xs false A hc hc' hg (hnc (by simp)) hk




theorem fmtRest_head {C : List Scope} {spec : Option Expr} {K' : List (PyCore.Kont σ)} :
    (fmtRest C spec K').head? = some (.binR "," (.data "$args" [])) := by
  cases spec <;> rfl

/-- A continuation awaiting a value has no class statement on PyCore's side at its top. -/
theorem krel_noClsT {x : Cx} {U : Label → Prop} : ∀ {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)},
    KRel x U true K K' → ∀ y q bs kws ds K0', K' ≠ .clsEnd y q bs kws ds :: K0'
  | [], _, h => by cases h <;> rename_i k <;> cases k
  | k0 :: K, K', h => by
    intro y q bs kws ds K0' he
    cases h with
    | core k =>
      cases k
      case boolNil k => exact krel_noClsT k y q bs kws ds K0' he
      all_goals simp_all
    | misc k =>
      cases k
      case cmpONil k => exact krel_noClsT k y q bs kws ds K0' he
      all_goals simp_all [recK]
    | call k => cases k <;> simp_all [recK]
    | cls k => cases k <;> simp_all [recK]
    | comp k => cases k <;> simp_all [recK, nextK]
    | loop k => cases k <;> simp_all [recK, nextK]
    | asg k => cases k <;> simp_all [recK]
    | acc k =>
      cases k <;> (try simp_all [recK])
      all_goals (try split at he) <;> (have := congrArg List.head? he; simp only [fmtRest_head, List.head?_cons] at this; cases this)

theorem seqs_cons_ne {y : Name} {q : String} {bs : List Val} {kws : List (Name × Val)} {ds : List Val}
    {K0' : List (PyCore.Kont σ)} : ∀ (n : Nat) (k : PyCore.Kont σ) (K : List (PyCore.Kont σ)),
    (∀ K1, k :: K ≠ .clsEnd y q bs kws ds :: K1) → seqs n ++ k :: K ≠ .clsEnd y q bs kws ds :: K0'
  | 0, k, K, h => h K0'
  | n + 1, _, _, _ => by simp [seqs, List.replicate_succ]

theorem delSeg_head {C : List Scope} {ts : List Expr} {Kp K' : List (PyCore.Kont σ)} (h : DelSeg C ts Kp K') :
    ∃ ss K1, Kp = .seq ss :: K1 := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- A continuation whose Surf side is no class statement's has none on PyCore's side either. -/
theorem krel_cls {x : Cx} {U : Label → Prop} {i : Bool} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (h : KRel x U i K K') (hn : ∀ y q bs kws ds K0, K ≠ .clsEnd y q bs kws ds :: K0) :
    ∀ y q bs kws ds K0', K' ≠ .clsEnd y q bs kws ds :: K0' := by
  cases i
  · intro y q bs kws ds K0' he
    cases h with
    | nil => cases he
    | core k =>
      cases k <;> (try simp at he)
      rename_i hp _ _; rcases hp with rfl | rfl | rfl <;> simp at he
    | call k => cases k
    | cls k => cases k; exact hn _ _ _ _ _ _ rfl
    | comp k =>
      cases k <;> (try simp at he)
      exact seqs_cons_ne _ _ _ (by simp [loopK]) he
    | loop k => cases k; simp [loopK] at he
    | asg k =>
      cases k <;> (try simp at he)
      obtain ⟨_, _, rfl⟩ := delSeg_head ‹DelSeg _ _ _ _›; simp at he
    | acc k => cases k
    | misc k => cases k; simp at he
  · exact krel_noClsT h

theorem pval_seqs_loop {c : PyCore.Config σ} {g : PyCore.Frame σ} {gs : List (PyCore.Frame σ)} {v : Val}
    {l : Label} {iv : Name} {b u : PS} {L K : List (PyCore.Kont σ)} :
    ∀ n, g.kont = seqs n ++ loopK l iv b u :: L ++ K → PyCore.valStep I c g gs v = none
  | 0, hg => by simp [PyCore.valStep, hg, seqs, loopK]
  | n + 1, hg => by simp [PyCore.valStep, hg, seqs, List.replicate_succ]

/-- A continuation awaiting no value takes none (both runs are stuck on a value). -/
theorem krel_false_val {x : Cx} {U : Label → Prop} {K : List (Sem.Kont σ)} {K' : List (PyCore.Kont σ)}
    (h : KRel x U false K K') :
    (∀ (c : Sem.Config σ) (g : Sem.Frame σ) gs v, g.kont = K → Sem.valStep I c g gs v = none) ∧
    (∀ (c : PyCore.Config σ) (g : PyCore.Frame σ) gs v, g.kont = K' → PyCore.valStep I c g gs v = none) := by
  cases h with
  | nil => exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => by simp [PyCore.valStep, hg]⟩
  | core k =>
    cases k
    case seq hp _ _ =>
      refine ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => ?_⟩
      rcases hp with rfl | rfl | rfl <;> simp [PyCore.valStep, hg]
    all_goals exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => by simp [PyCore.valStep, hg]⟩
  | call k => cases k
  | cls k =>
    cases k
    exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => by simp [PyCore.valStep, hg]⟩
  | comp k =>
    cases k
    case cLoop =>
      exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => pval_seqs_loop _ hg⟩
    all_goals exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => by simp [PyCore.valStep, hg]⟩
  | loop k =>
    cases k
    exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => by simp [PyCore.valStep, hg, loopK]⟩
  | asg k =>
    cases k
    case delMany =>
      refine ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => ?_⟩
      obtain ⟨_, _, rfl⟩ := delSeg_head ‹DelSeg _ _ _ _›; simp [PyCore.valStep, hg]
    all_goals exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => by simp [PyCore.valStep, hg]⟩
  | acc k => cases k
  | misc k =>
    cases k
    exact ⟨fun c g gs v hg => by simp [Sem.valStep, hg], fun c g gs v hg => by simp [PyCore.valStep, hg]⟩

/-! ## Frames ending -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- The top frame leaves; its caller resumes; the objects change at most at the top frame's id (its
generator, made done or suspended with a generator frame of that id). -/
theorem Ids.pop {t1 : PyCore.Config σ} {g' : PyCore.Frame σ} {gs' : List (PyCore.Frame σ)} {c' : PyCore.Ctrl σ}
    (h : Ids t) (ht : t.stack = f' :: g' :: gs') (ht1 : t1.stack = { g' with ctrl := c' } :: gs')
    (hn : t1.next = t.next)
    (hob : ∀ o b, pObj t1 o = some b → pObj t o = some b ∨
      (o = f'.id ∧ ∀ h, b = .gen (.susp h) → h.id = o ∧ h.kind = .gen o)) : Ids t1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  rw [ht] at h1 h2 h4 h5 h6
  have hmem : ∀ g ∈ t1.stack, ∃ g0 ∈ g' :: gs', g.id = g0.id ∧ g.kind = g0.kind := by
    rw [ht1]; intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨g', List.mem_cons_self, rfl, rfl⟩
    · exact ⟨g, List.mem_cons_of_mem _ hg, rfl, rfl⟩
  have hnf : ∀ g ∈ t1.stack, g.id ≠ f'.id := by
    intro g hg e
    obtain ⟨g0, hg0, he, -⟩ := hmem g hg
    have h1' := h1
    simp only [List.map_cons, List.nodup_cons] at h1'
    apply h1'.1
    have : g0.id ∈ (g' :: gs').map (·.id) := List.mem_map.2 ⟨g0, hg0, rfl⟩
    rw [← he, e] at this; simpa using this
  refine ⟨?_, fun g hg => ?_, fun o b hb => ?_, fun o g ho => ?_, fun g hg o hgo => ?_, fun g hg hm => ?_,
    fun o g ho => ?_⟩
  · rw [ht1]; have := (List.nodup_cons.1 h1).2; simpa using this
  · obtain ⟨g0, hg0, he, -⟩ := hmem g hg; rw [hn, he]; exact h2 g0 (List.mem_cons_of_mem _ hg0)
  · rw [hn]; rcases hob o b hb with hb | ⟨rfl, -⟩
    · exact h3 o b hb
    · exact h2 f' List.mem_cons_self
  · rcases hob o _ ho with ho | ⟨rfl, hh⟩
    · obtain ⟨e, hne⟩ := h4 o g ho
      refine ⟨e, fun h' hh' => ?_⟩
      obtain ⟨g0, hg0, he, -⟩ := hmem h' hh'
      rw [he]; exact hne g0 (List.mem_cons_of_mem _ hg0)
    · exact ⟨(hh g rfl).1, hnf⟩
  · obtain ⟨g0, hg0, he, hk⟩ := hmem g hg; rw [he]; exact h5 g0 (List.mem_cons_of_mem _ hg0) o (hk ▸ hgo)
  · obtain ⟨g0, hg0, he, hk⟩ := hmem g hg; rw [he]; exact h6 g0 (List.mem_cons_of_mem _ hg0) (hk ▸ hm)
  · rcases hob o _ ho with ho | ⟨rfl, hh⟩
    · exact h7 o g ho
    · exact (hh g rfl).2

/-- The top frame leaves; the caller below resumes with `c ~ c'` at the index of its continuation. -/
theorem At.ret (A : At p H s t f fs f' fs') {g : Sem.Frame σ} {gs : List (Sem.Frame σ)} {g' : PyCore.Frame σ}
    {gs' : List (PyCore.Frame σ)} (h1 : fs = g :: gs) (h2 : fs' = g' :: gs') {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {U : Label → Prop} {i : Bool} (hk : KRel (cx p H (rdOf t g') (ownOf t g') g) U i g.kont g'.kont)
    (hc : CR p g.chain U i c c') {O : Std.HashMap Nat (Sem.Obj σ)} {O' : Std.HashMap Nat (PyCore.Obj σ)}
    (ho : ∀ o : Nat, PyCore.OptRel (ORel p H t.glob t.cells) O[o]? O'[o]?)
    (hob : ∀ (o : Nat) b, O'[o]? = some b → t.objs[o]? = some b ∨
      (o = f'.id ∧ ∀ h, b = .gen (.susp h) → h.id = o ∧ h.kind = .gen o))
    (hen : ∀ st, EnterInv s.objs st → EnterInv O st) :
    CRel p H { s with stack := { g with ctrl := c } :: gs, objs := O } { t with stack := { g' with ctrl := c' } :: gs', objs := O' } := by
  have hst := A.stk; rw [h1, h2] at hst
  obtain ⟨-, hg, hgs⟩ := hst
  have hw := A.r.wait; rw [A.hs, h1] at hw
  have hE := A.r.enter; rw [A.hs, h1] at hE
  exact ⟨⟨⟨hg.toFRel0.upd c g.kont c' g'.kont, hg.hl, U, i, hc, hk⟩, hgs⟩, ho, A.r.cells, A.r.glob, A.r.out,
    A.r.next, A.r.res, A.r.st, fun x hx => hw x (by simp at hx ⊢; exact .inr hx),
    A.r.ids.pop (by rw [A.ht, h2]) rfl rfl hob, hen _ (hE.tail.ctrl c)⟩

theorem objs_ins (A : At p H s t f fs f' fs') (o : Nat) {a : Sem.Obj σ} {b : PyCore.Obj σ}
    (h : ORel p H t.glob t.cells a b) :
    ∀ o' : Nat, PyCore.OptRel (ORel p H t.glob t.cells) (s.objs.insert o a)[o']? (t.objs.insert o b)[o']? := by
  intro o'
  simp only [Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases h' : o = o'
  · simp [h', PyCore.OptRel, h]
  · simp only [h', ite_false]; exact A.r.objs o'

theorem hob_ins {o : Nat} {b0 : PyCore.Obj σ} (ho : o = f'.id)
    (hb : ∀ h, b0 = .gen (.susp h) → h.id = o ∧ h.kind = .gen o) :
    ∀ (o' : Nat) b, (t.objs.insert o b0)[o']? = some b → t.objs[o']? = some b ∨
      (o' = f'.id ∧ ∀ h, b = .gen (.susp h) → h.id = o' ∧ h.kind = .gen o') := by
  intro o' b h
  simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at h
  split at h
  · rename_i e; subst e; cases h; exact .inr ⟨ho, hb⟩
  · exact .inl h

/-- The top frame leaves; its caller gets `c ~ c'`. A value reaching a caller whose continuation awaits
no value: both runs are stuck next. -/
theorem ret_goal (A : At p H s t f fs f' fs') {g : Sem.Frame σ} {gs : List (Sem.Frame σ)} {g' : PyCore.Frame σ}
    {gs' : List (PyCore.Frame σ)} (h1 : fs = g :: gs) (h2 : fs' = g' :: gs') {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    (hc : ∀ U i, (i = true ∨ ∀ v, c ≠ .val v) → CR p g.chain U i c c') (hv : ∀ v, c = .val v → c' = .val v)
    {O : Std.HashMap Nat (Sem.Obj σ)} {O' : Std.HashMap Nat (PyCore.Obj σ)}
    (ho : ∀ o : Nat, PyCore.OptRel (ORel p H t.glob t.cells) O[o]? O'[o]?)
    (hob : ∀ (o : Nat) b, O'[o]? = some b → t.objs[o]? = some b ∨
      (o = f'.id ∧ ∀ h, b = .gen (.susp h) → h.id = o ∧ h.kind = .gen o))
    (hen : ∀ st, EnterInv s.objs st → EnterInv O st)
    (e1 : Sem.step I s = some { s with stack := { g with ctrl := c } :: gs, objs := O })
    (e2 : PyCore.step I t = some { t with stack := { g' with ctrl := c' } :: gs', objs := O' })
    (hfoc : PyCore.focus t = none) : Goal I p H s t := by
  have hst := A.stk; rw [h1, h2] at hst
  obtain ⟨U, i, -, hk⟩ := hst.2.1.code
  by_cases hi : i = true ∨ ∀ v, c ≠ .val v
  · exact goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp)
      (crelI_seen (A.ret h1 h2 hk (hc U i hi) ho hob hen)) (cover_none fun y hy => by simp at hy; subst hy; exact hfoc)
  · have hi1 : i = false := by cases i; rfl; exact absurd (.inl rfl) hi
    obtain ⟨v, rfl⟩ : ∃ v, c = .val v := Classical.byContradiction fun h' => hi (.inr fun v e => h' ⟨v, e⟩)
    subst hi1
    have hcv := hv v rfl
    obtain ⟨hs0, hp0⟩ := krel_false_val (I := I) hk
    refine Or.inl ⟨_, _, [s], [t], .cons e1 (.nil _), ?_, .cons e2 (.nil _), ?_, ?_, ?_⟩
    · simp only [Sem.step]; exact hs0 _ _ _ _ rfl
    · rw [pstep_val rfl (show ({ g' with ctrl := c' } : PyCore.Frame σ).ctrl = .val v from hcv)]
      exact hp0 _ _ _ _ rfl
    · simp [Fin, Sem.outcome, PyCore.outcome, OCorr, A.r.out, A.r.st]
    · refine cover_none fun y hy => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · simp [PyCore.focus, hcv]
      · exact hfoc

/-- The module frame ends. -/
theorem mod_end (A : At p H s t f fs f' fs') (r : Except Val Unit)
    (e1 : Sem.step I s = some { s with stack := [], res := some r })
    (e2 : PyCore.step I t = some { t with stack := [], res := some r }) (hfoc : PyCore.focus t = none) :
    Goal I p H s t :=
  goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp)
    (crelI_seen ⟨trivial, A.r.objs, A.r.cells, A.r.glob, A.r.out, A.r.next, rfl, A.r.st, by simp,
      ⟨by simp, by simp, A.r.ids.obj, fun o g ho => ⟨(A.r.ids.susp o g ho).1, by simp⟩, by simp, by simp,
        A.r.ids.sk⟩, ⟨by simp, A.r.enter.2⟩⟩)
    (cover_none fun y hy => by simp at hy; subst hy; exact hfoc)

theorem tail_nil (A : At p H s t f fs f' fs') (h : fs = []) : fs' = [] := by
  have := A.stk; subst h; cases fs' <;> simp_all [PyCore.All2]

theorem tail_cons (A : At p H s t f fs f' fs') {g gs} (h : fs = g :: gs) : ∃ g' gs', fs' = g' :: gs' := by
  have := A.stk; subst h; cases fs' <;> simp_all [PyCore.All2]

theorem tail_rel (A : At p H s t f fs f' fs') :
    PyCore.All2 (fun f f' => FRel p H (rdOf t f') (ownOf t f') f f') fs fs' := (A.stk).2

theorem done_nil (A : At p H s t f fs f' fs') (W : WF p) (hc : f.ctrl = .exec []) (hc' : f'.ctrl = .exec [])
    (hk : f.kont = []) (hk' : f'.kont = []) : Goal I p H s t := by
  have hkd := A.hf.kind
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  cases hkf : f.kind with
  | mod =>
    exact mod_end A (.ok ()) (by simp [Sem.step, A.hs, hc, Sem.doneStep, hk, hkf])
      (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hk', hkd, hkf, fk]) hfoc
  | fn =>
    cases fs with
    | nil =>
      have := tail_nil A rfl; subst this
      exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.doneStep, hk, hkf, Sem.retTo])
        (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hk', hkd, hkf, fk, PyCore.retTo]) (cov_none A hfoc)
    | cons g gs =>
      obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
      exact ret_goal A rfl rfl (c := .val .none) (c' := .val .none) (fun _ _ h => by
          rcases h with rfl | h; exact .val; exact absurd rfl (h _)) (fun _ h => by cases h; rfl)
        A.r.objs (fun _ _ h => .inl h) (fun _ h => h)
        (by simp [Sem.step, A.hs, hc, Sem.doneStep, hk, hkf, Sem.retTo])
        (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hk', hkd, hkf, fk, PyCore.retTo]) hfoc
  | gen o =>
    have hid : f'.id = o := A.r.ids.gk f' (by rw [A.ht]; simp) o (by rw [hkd, hkf]; rfl)
    cases fs with
    | nil =>
      have := tail_nil A rfl; subst this
      exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.doneStep, hk, hkf, Sem.genEnd])
        (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hk', hkd, hkf, fk, PyCore.genEnd]) (cov_none A hfoc)
    | cons g gs =>
      obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
      exact ret_goal A rfl rfl (c := Sem.raiseNew (g :: gs) (Py.stopOf .none))
        (c' := PyCore.raiseNew (g' :: gs') (Py.stopOf .none))
        (fun _ _ _ => by rw [raiseNew_s, raiseNew_t (tail_rel A)]; exact .raise) (fun _ h => by cases h)
        (objs_ins A o (.gen .done)) (hob_ins hid.symm fun _ h => by cases h)
          (fun _ h => h.ins (insOk_gen _) fun _ e => nomatch e)
        (by simp [Sem.step, A.hs, hc, Sem.doneStep, hk, hkf, Sem.genEnd])
        (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hk', hkd, hkf, fk, PyCore.genEnd]) hfoc
  | cls =>
    cases fs with
    | nil =>
      have := tail_nil A rfl; subst this
      exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.doneStep, hk, hkf, Sem.retTo])
        (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hk', hkd, hkf, fk, PyCore.classEnd, PyCore.retTo])
        (cov_none A hfoc)
    | cons g gs =>
      obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
      exact ret_goal A rfl rfl (c := .ns f.ns) (c' := .ns (PyCore.dropReserved f'.ns))
        (fun _ _ _ => by rw [A.hf.ns]; exact .ns) (fun _ h => by cases h)
        A.r.objs (fun _ _ h => .inl h) (fun _ h => h)
        (by simp [Sem.step, A.hs, hc, Sem.doneStep, hk, hkf, Sem.retTo])
        (by simp [PyCore.step, A.ht, hc', PyCore.doneStep, hk', hkd, hkf, fk, PyCore.classEnd, PyCore.retTo]) hfoc

theorem sig_nil {U : Label → Prop} {i : Bool} (A : At p H s t f fs f' fs') (W : WF p)
    (hc : CSig i f.chain U f.ctrl f'.ctrl)
    (hk : f.kont = []) (hk' : f'.kont = []) : Goal I p H s t := by
  have hkd := A.hf.kind
  rcases hc with ⟨v, hc, hc'⟩ | ⟨v, hc, hc'⟩ | ⟨-, hn, hc, hc'⟩ | ⟨-, hn, hc, hc'⟩
  · have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc', hk']
    cases hkf : f.kind
    case mod =>
      exact mod_end A (.error v) (by simp [Sem.step, A.hs, hc, Sem.raiseStep, hk, hkf])
        (by simp [PyCore.step, A.ht, hc', PyCore.raiseStep, hk', hkd, hkf, fk]) hfoc
    case gen o =>
      have hid : f'.id = o := A.r.ids.gk f' (by rw [A.ht]; simp) o (by rw [hkd, hkf]; rfl)
      cases fs with
      | nil =>
        have := tail_nil A rfl; subst this
        exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.raiseStep, hk, hkf, Sem.genEnd])
          (by simp [PyCore.step, A.ht, hc', PyCore.raiseStep, hk', hkd, hkf, fk, PyCore.genEnd]) (cov_none A hfoc)
      | cons g gs =>
        obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
        exact ret_goal A rfl rfl (c := .raise (if Py.isStop v then .exn (Py.err "RuntimeError") v v else v))
          (c' := .raise (if Py.isStop v then .exn (Py.err "RuntimeError") v v else v))
          (fun _ _ _ => .raise) (fun _ h => by cases h)
          (objs_ins A o (.gen .done)) (hob_ins hid.symm fun _ h => by cases h)
          (fun _ h => h.ins (insOk_gen _) fun _ e => nomatch e)
          (by simp [Sem.step, A.hs, hc, Sem.raiseStep, hk, hkf, Sem.genEnd])
          (by simp [PyCore.step, A.ht, hc', PyCore.raiseStep, hk', hkd, hkf, fk, PyCore.genEnd, PyCore.isStop,
            PyCore.errRuntime]; rfl) hfoc
    all_goals
      cases fs with
      | nil =>
        have := tail_nil A rfl; subst this
        exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.raiseStep, hk, hkf, Sem.retTo])
          (by simp [PyCore.step, A.ht, hc', PyCore.raiseStep, hk', hkd, hkf, fk, PyCore.retTo]) (cov_none A hfoc)
      | cons g gs =>
        obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
        exact ret_goal A rfl rfl (c := .raise v) (c' := .raise v) (fun _ _ _ => .raise) (fun _ h => by cases h)
          A.r.objs (fun _ _ h => .inl h) (fun _ h => h)
          (by simp [Sem.step, A.hs, hc, Sem.raiseStep, hk, hkf, Sem.retTo])
          (by simp [PyCore.step, A.ht, hc', PyCore.raiseStep, hk', hkd, hkf, fk, PyCore.retTo]) hfoc
  · have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
    cases hkf : f.kind
    case fn =>
      cases fs with
      | nil =>
        have := tail_nil A rfl; subst this
        exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.retStep, hk, hkf, Sem.retTo])
          (by simp [PyCore.step, A.ht, hc', PyCore.retStep, hk', hkd, hkf, fk, PyCore.retTo]) (cov_none A hfoc)
      | cons g gs =>
        obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
        exact ret_goal A rfl rfl (c := .val v) (c' := .val v) (fun _ _ h => by
            rcases h with rfl | h; exact .val; exact absurd rfl (h _)) (fun _ h => by cases h; rfl)
          A.r.objs (fun _ _ h => .inl h) (fun _ h => h)
          (by simp [Sem.step, A.hs, hc, Sem.retStep, hk, hkf, Sem.retTo])
          (by simp [PyCore.step, A.ht, hc', PyCore.retStep, hk', hkd, hkf, fk, PyCore.retTo]) hfoc
    case gen o =>
      have hid : f'.id = o := A.r.ids.gk f' (by rw [A.ht]; simp) o (by rw [hkd, hkf]; rfl)
      cases fs with
      | nil =>
        have := tail_nil A rfl; subst this
        exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.retStep, hk, hkf, Sem.genEnd])
          (by simp [PyCore.step, A.ht, hc', PyCore.retStep, hk', hkd, hkf, fk, PyCore.genEnd]) (cov_none A hfoc)
      | cons g gs =>
        obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
        exact ret_goal A rfl rfl (c := Sem.raiseNew (g :: gs) (Py.stopOf v))
          (c' := PyCore.raiseNew (g' :: gs') (Py.stopOf v))
          (fun _ _ _ => by rw [raiseNew_s, raiseNew_t (tail_rel A)]; exact .raise) (fun _ h => by cases h)
          (objs_ins A o (.gen .done)) (hob_ins hid.symm fun _ h => by cases h)
          (fun _ h => h.ins (insOk_gen _) fun _ e => nomatch e)
          (by simp [Sem.step, A.hs, hc, Sem.retStep, hk, hkf, Sem.genEnd])
          (by simp [PyCore.step, A.ht, hc', PyCore.retStep, hk', hkd, hkf, fk, PyCore.genEnd]) hfoc
    all_goals
      exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.retStep, hk, hkf])
        (by simp [PyCore.step, A.ht, hc', PyCore.retStep, hk', hkd, hkf, fk]) (cov_none A hfoc)
  · exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.brkStep, hk]) (by simp [PyCore.step, A.ht, hc', PyCore.brkStep, hk'])
      (cov_none A (by simp [PyCore.focus, A.ht, hc']))
  · exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.contStep, hk]) (by simp [PyCore.step, A.ht, hc', PyCore.contStep, hk'])
      (cov_none A (by simp [PyCore.focus, A.ht, hc']))

theorem val_yieldK (A : At p H s t f fs f' fs') (W : WF p) {U : Label → Prop} {v : Val}
    {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hc : f.ctrl = .val v) (hc' : f'.ctrl = .val v)
    (hK : f.kont = .yieldK :: K0) (hK' : f'.kont = .yieldS :: K0') (hk : KRel A.x U true K0 K0') :
    Goal I p H s t := by
  have hkd := A.hf.kind
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  cases hkf : f.kind
  case gen o =>
    have hid : f'.id = o := A.r.ids.gk f' (by rw [A.ht]; simp) o (by rw [hkd, hkf]; rfl)
    cases fs with
    | nil =>
      have := tail_nil A rfl; subst this
      exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.valStep, hK, hkf])
        (by rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', hkd, hkf, fk]) (cov_none A hfoc)
    | cons g gs =>
      obtain ⟨g', gs', rfl⟩ := tail_cons A rfl
      have hgr : ORel p H t.glob t.cells (.gen (.susp { f with ctrl := .val .none, kont := K0 }))
          (.gen (.susp { f' with ctrl := .val .none, kont := K0' })) :=
        .gen (.susp ⟨A.hf.toFRel0.upd _ _ _ _, A.hf.hl, U, true, .val, hk⟩)
      exact ret_goal A rfl rfl (c := .val v) (c' := .val v) (fun _ _ h => by
          rcases h with rfl | h; exact .val; exact absurd rfl (h _)) (fun _ h => by cases h; rfl)
        (objs_ins A o hgr) (hob_ins hid.symm fun h e => by
          cases e; exact ⟨hid, by simp [hkd, hkf, fk]⟩)
        (fun _ h => h.ins (insOk_gen _) fun g e => by
          cases e; have hE := A.r.enter.1 f (by rw [A.hs]; exact List.mem_cons_self)
          exact hE.sub fun o b kx hm => by rw [hK]; exact List.mem_cons_of_mem _ hm)
        (by simp [Sem.step, A.hs, hc, Sem.valStep, hK, hkf])
        (by rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', hkd, hkf, fk]) hfoc
  all_goals
    exact fin_stuck A (by simp [Sem.step, A.hs, hc, Sem.valStep, hK, hkf])
      (by rw [pstep_val A.ht hc']; simp [PyCore.valStep, hK', hkd, hkf, fk]) (cov_none A hfoc)

theorem ns_other {U : Label → Prop} {i : Bool} (A : At p H s t f fs f' fs') (W : WF p) {ns : List (Name × Val)}
    (hc : f.ctrl = .ns ns) (hc' : f'.ctrl = .ns ns) (hk : KRel A.x U i f.kont f'.kont)
    (hn : ∀ x q bs kws ds K0, f.kont ≠ .clsEnd x q bs kws ds :: K0) : Goal I p H s t := by
  have hn' := krel_cls hk hn
  refine fin_stuck A ?_ ?_ (cov_none A (by simp [PyCore.focus, A.ht, hc']))
  · simp only [Sem.step, A.hs, hc, Sem.nsStep]
    try (split; (rename_i x q bs kws ds K0 h; exact absurd h (hn x q bs kws ds K0)); rfl)
  · simp only [PyCore.step, A.ht, hc', PyCore.nsStep]
    try (split; (rename_i x q bs kws ds K0 h; exact absurd h (hn' x q bs kws ds K0)); rfl)

/-! ## Blocks ending, signals passing (the homomorphic items) -/

theorem goodHs_head {C : List Scope} {U : Label → Prop} {lh : Label} {ty : Expr} {x : Option Name}
    {hb : List Stmt} {hs : List Handler} (h : GoodHs p C U (.mk lh (some ty) x hb :: hs)) :
    GoodE p C U ty ∧ GoodB p C U hb ∧ GoodHs p C U hs := by
  obtain ⟨hs1, ht1, hok, hu, hpv, hnd, htc⟩ := h
  have hpv' := hpv (by simp)
  simp only [okHs, okO, Bool.and_eq_true] at hok
  refine ⟨⟨fun z hz => hs1 z ?_, fun z hz => ht1 z ?_, ?_, fun l hl => hu l ?_, hpv', ?_, fun z hz => htc z ?_⟩,
    ⟨fun z hz => hs1 z ?_, fun z hz => ht1 z ?_, ?_, fun l hl => hu l ?_, fun _ => hpv', ?_, fun z hz => htc z ?_⟩,
    ⟨fun z hz => hs1 z ?_, fun z hz => ht1 z ?_, ?_, fun l hl => hu l ?_, fun _ => hpv', ?_, fun z hz => htc z ?_⟩⟩ <;>
    simp_all [itemsHs, itemsO, trHs, PyCore.itemsHs, labelsHs, labelsO, List.nodup_cons, List.nodup_append, touchHs,
      touchO]

theorem xok_head (W : WF p) {C : List Scope} {U : Label → Prop} {lh : Label} {ty : Option Expr} {x : Option Name}
    {hb : List Stmt} {hs : List Handler} (h : GoodHs p C U (.mk lh ty x hb :: hs)) :
    XOk C U x ((x.map (mangle (priv C))).getD (fresh "e" lh)) := by
  cases x with
  | some y => exact .inl ⟨y, rfl, rfl, W.nodot lh _ C (h.s _ (by simp [itemsHs]))⟩
  | none =>
    refine .inr ⟨rfl, ⟨lh, rfl, h.u lh (by simp [labelsHs])⟩, fok_of W (L := sub lh 0) (h.t _ ?_) ⟨_, _, rfl⟩
      (not_cmp _ _ (by omega) (by omega) (by omega))⟩
    simp [trHs, PyCore.itemsHs]

theorem done_core : KCase I p false CoreK CDone := by
  intro H s t f fs f' fs' U A W ⟨hc, hc'⟩ hk
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  have hn0 := cov_none A hfoc
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | @seq _ K0 K0' ss pre hn hp hg k =>
    have e1 : Sem.step I s = some { s with stack := { f with ctrl := .exec ss, kont := K0 } :: fs } := by
      simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC]
    have hr := crelI_seen (H := H) (zs := [s]) (A.set (c := .exec ss) (c' := .exec (trB f.chain ss)) (.exec hg hn) k)
    let tE : List (PyCore.Kont σ) → PyCore.Config σ := fun L => { t with stack := { f' with ctrl := .exec [], kont := L } :: fs' }
    have sk : ∀ k0 L, (k0 = .tryE [] [] ∨ k0 = .seq []) → PyCore.step I (tE (k0 :: L)) = some (tE L) := by
      rintro k0 L (rfl | rfl) <;> simp [tE, PyCore.step, PyCore.doneStep, PyCore.top]
    have sq : PyCore.step I (tE (.seq (trB f.chain ss) :: K0')) =
        some { t with stack := { f' with ctrl := .exec (trB f.chain ss), kont := K0' } :: fs' } := by
      simp [tE, PyCore.step, PyCore.doneStep, PyCore.top]
    have ht0 : t = tE f'.kont := by simp only [tE]; rw [← hc']; exact (t_eta A.ht).symm
    have hfE : ∀ L, PyCore.focus (tE L) = none := fun L => by simp [tE, PyCore.focus]
    rcases hp with rfl | rfl | rfl
    · exact goal_b (.cons e1 (.nil _)) (by simp) (.cons (by rw [ht0, hK']; exact sq) (.nil _)) (by simp) hr
        (cover_none fun y hy => by simp at hy; subst hy; exact hfoc)
    · exact goal_b (.cons e1 (.nil _)) (by simp) (.cons (by rw [ht0, hK']; exact sk _ _ (.inl rfl)) (.cons sq (.nil _)))
        (by simp) hr (cover_none fun y hy => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl <;> simp [hfoc, hfE])
    · exact goal_b (.cons e1 (.nil _)) (by simp)
        (.cons (by rw [ht0, hK']; exact sk _ _ (.inr rfl)) (.cons (sk _ _ (.inl rfl)) (.cons sq (.nil _))))
        (by simp) hr (cover_none fun y hy => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; rcases hy with rfl | rfl | rfl <;> simp [hfoc, hfE])
  | seqNil =>
    have e2 : PyCore.step I t = some { t with stack := { f' with ctrl := .exec [], kont := [] } :: fs' } := by
      simp [PyCore.step, A.ht, hc', hK', PyCore.doneStep, PyCore.top]
    refine Or.inr (Or.inr (Or.inr ⟨_, [t], .cons e2 (.nil _), by simp, ?_, ?_, cover_none fun y hy => by
      simp at hy; subst hy; exact hfoc⟩))
    · have := A.set (c := .exec []) (c' := .exec []) (k := []) (k' := []) (.exec (goodB_nil _ U) (by simp)) .nil
      rw [← hc, ← hK, s_eta A.hs] at this; exact .inl this
    · simp [μ, A.hs, A.ht, hK, hK', hc'] <;> omega
  | @loop _ K0 K0' c b u hn h1 h2 h3 k =>
    exact A.go11 (c := .ev c) (k := .whileS c b u :: K0) (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.doneStep, PyCore.top]) (.ev h1) (.core (.whileS hn h1 h2 h3 k)) hn0
  | @tryE _ K0 K0' hs u hn h1 h2 k =>
    exact A.go11 (c := .exec u) (c' := .exec (trB f.chain u)) (by simp [Sem.step, A.hs, hc, hK, Sem.doneStep, Sem.setC])
      (by simp [PyCore.step, A.ht, hc', hK', PyCore.doneStep, PyCore.top]) (.exec h2 fun _ => hn) k hn0
  | @handler _ K0 K0' y y' ex hn hx k =>
    obtain ⟨s1, t1, g, g', e1, e2, A1, hch, h1, h2, h3, h4, ha⟩ := unset0 A.zero hx (.exec []) K0 (.exec []) K0'
    refine goal11 A1 (by simp only [Sem.step, A.hs, hc, hK, Sem.doneStep]; exact e1)
      (by simp only [PyCore.step, A.ht, hc', hK', PyCore.doneStep]; exact e2) (U := U) (i := false)
      (by rw [h1, h3]; exact .exec (goodB_nil _ U) (by simp))
      (by rw [h2, h4]; exact krel_move k hch ha fun _ h => h) hfoc

end

/-- A signal's control relation at an index `j` (the continuation after the item it passes), `break`
and `continue` only at index `false`. -/
theorem csig_cr {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    (h : CSig i C U c c') {j : Bool} (hij : i = false → j = false) : ∀ U', CR p C U' j c c' := by
  intro U'
  rcases h with ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩ | ⟨hi, hn, rfl, rfl⟩ | ⟨hi, hn, rfl, rfl⟩
  · exact .raise
  · exact .retv
  · rw [hij hi]; exact .brk hn
  · rw [hij hi]; exact .cont hn

theorem csig_foc {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ} (h : CSig i C U c c')
    {t : PyCore.Config σ} {g : PyCore.Frame σ} {gs : List (PyCore.Frame σ)} (ht : t.stack = g :: gs) (hg : g.ctrl = c')
    (hk : ∀ lh e x hb hs u K, g.kont ≠ .tryE (.mk lh e x hb :: hs) u :: K) : PyCore.focus t = none := by
  rcases h with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> simp only [PyCore.focus, ht, hg]
  all_goals try (split; (rename_i lh e x hb hs u K h; exact absurd h (hk lh e x hb hs u K)); rfl)

/-- PyCore's signal passes a block's end (`seq`, or a `try` with no handler). -/
theorem pstep_skip {i : Bool} {C : List Scope} {U : Label → Prop} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    (hs : CSig i C U c c')
    (t : PyCore.Config σ) (g' : PyCore.Frame σ) (gs' : List (PyCore.Frame σ)) {k : PyCore.Kont σ}
    (hk : (∃ ss, k = .seq ss) ∨ k = .tryE [] []) (K : List (PyCore.Kont σ)) :
    PyCore.step I { t with stack := { g' with ctrl := c', kont := k :: K } :: gs' } =
      some { t with stack := { g' with ctrl := c', kont := K } :: gs' } := by
  rcases hs with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> rcases hk with ⟨ss, rfl⟩ | rfl <;>
    simp [PyCore.step, PyCore.raiseStep, PyCore.retStep, PyCore.brkStep, PyCore.contStep, PyCore.top]

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- A signal passes one item on each side. -/
theorem sig_pop {U U' : Label → Prop} {i j : Bool} (A : At p H s t f fs f' fs') (hs : CSig i f.chain U f.ctrl f'.ctrl)
    (hij : i = false → j = false) {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)} (hk : KRel A.x U' j K0 K0')
    (e1 : Sem.step I s = some { s with stack := { f with kont := K0 } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with kont := K0' } :: fs' })
    (hfoc : PyCore.focus t = none) (he : EnterSub K0 f.kont := by esub) : Goal I p H s t :=
  A.go11 (c := f.ctrl) (c' := f'.ctrl) e1 e2 (csig_cr hs hij U') hk (cov_none A hfoc) he

/-- A signal passes a block's end: Surf's `seq`, PyCore's `pre` and `seq`. -/
theorem sig_seq {U : Label → Prop} {i : Bool} (A : At p H s t f fs f' fs') (hs : CSig i f.chain U f.ctrl f'.ctrl)
    {ss : List Stmt} {pre : List (PyCore.Kont σ)} {K0 : List (Sem.Kont σ)} {K0' : List (PyCore.Kont σ)}
    (hp : BlkTail pre) (hK : f.kont = .seq ss :: K0) (hK' : f'.kont = pre ++ .seq (trB f.chain ss) :: K0')
    (hk : KRel A.x U false K0 K0') : Goal I p H s t := by
  have e1 : Sem.step I s = some { s with stack := { f with kont := K0 } :: fs } := by
    rcases hs with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ <;>
      simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC]
  let tE : List (PyCore.Kont σ) → PyCore.Config σ := fun L => { t with stack := { f' with ctrl := f'.ctrl, kont := L } :: fs' }
  have ht0 : t = tE f'.kont := (t_eta A.ht).symm
  have sk := fun (k : PyCore.Kont σ) L (h : (∃ ss, k = .seq ss) ∨ k = .tryE [] []) => pstep_skip (I := I) hs t f' fs' h L
  have hfE : ∀ L, (∀ lh e x hb hs u K, L ≠ .tryE (.mk lh e x hb :: hs) u :: K) → PyCore.focus (tE L) = none :=
    fun L hL => csig_foc hs rfl rfl hL
  have hr := crelI_seen (H := H) (zs := [s]) (A.set (c := f.ctrl) (c' := f'.ctrl) (k := K0) (k' := K0')
    (csig_cr hs (fun _ => rfl) U) hk)
  have hs' : { s with stack := { f with ctrl := f.ctrl, kont := K0 } :: fs } = { s with stack := { f with kont := K0 } :: fs } := rfl
  rw [hs'] at hr
  rcases hp with rfl | rfl | rfl
  · exact goal_b (.cons e1 (.nil _)) (by simp) (.cons (by rw [ht0, hK']; exact sk _ _ (.inl ⟨_, rfl⟩)) (.nil _)) (by simp) hr
      (cover_none fun y hy => by simp at hy; subst hy; rw [ht0, hK']; exact hfE _ (by simp))
  · exact goal_b (.cons e1 (.nil _)) (by simp)
      (.cons (by rw [ht0, hK']; exact sk _ _ (.inr rfl)) (.cons (sk _ _ (.inl ⟨_, rfl⟩)) (.nil _))) (by simp) hr
      (cover_none fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · rw [ht0, hK']; exact hfE _ (by simp)
        · exact hfE _ (by simp))
  · exact goal_b (.cons e1 (.nil _)) (by simp)
      (.cons (by rw [ht0, hK']; exact sk _ _ (.inl ⟨_, rfl⟩)) (.cons (sk _ _ (.inr rfl)) (.cons (sk _ _ (.inl ⟨_, rfl⟩)) (.nil _))))
      (by simp) hr
      (cover_none fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl
        · rw [ht0, hK']; exact hfE _ (by simp)
        all_goals exact hfE _ (by simp))

end

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

set_option hygiene false in
/-- The Surf and PyCore steps of a signal that pops one item. -/
macro "sige" : tactic => `(tactic| (rcases hc with ⟨v, h1, -⟩ | ⟨v, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ <;>
  simp [Sem.step, A.hs, h1, hK, Sem.raiseStep, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC]))
set_option hygiene false in
macro "sigp" : tactic => `(tactic| (rcases hc with ⟨v, -, h2⟩ | ⟨v, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, -, h2⟩ <;>
  simp [PyCore.step, A.ht, h2, hK', PyCore.raiseStep, PyCore.retStep, PyCore.brkStep, PyCore.contStep, PyCore.top]))
set_option hygiene false in
macro "sigpop" : tactic => `(tactic| exact sig_pop A hc (by first | (intro h; cases h) | (intro _; rfl)) ‹KRel _ _ _ _ _› (by sige) (by sigp)
  (csig_foc hc A.ht rfl (by intros; rw [hK']; simp)))

/-- A signal meets the items of the homomorphic fragment (a bare `except` is `raise_bare`'s). -/
theorem sig_core {U : Label → Prop} {i : Bool} (A : At p H s t f fs f' fs') (W : WF p)
    (hc : CSig i f.chain U f.ctrl f'.ctrl) (hb : (∃ v, f.ctrl = .raise v) → ¬ BareAt A.x U i f.kont f'.kont)
    (hk : CoreK A.x U i f.kont f'.kont) : Goal I p H s t := by
  have hcr := fun {j : Bool} (hij : i = false → j = false) => csig_cr (p := p) hc hij
  generalize hK : f.kont = K at hk hb
  generalize hK' : f'.kont = K' at hk hb
  cases hk with
  | exprS k => sigpop
  | binL _ _ k => sigpop
  | binR _ k => sigpop
  | @seq _ K0 K0' ss pre hn hp hg k => exact sig_seq A hc hp hK hK' k
  | seqNil =>
    have e2 : PyCore.step I t = some { t with stack := { f' with kont := [] } :: fs' } := by sigp
    refine Or.inr (Or.inr (Or.inr ⟨_, [t], .cons e2 (.nil _), by simp, ?_, ?_,
      cover_none fun y hy => by simp at hy; subst hy; exact csig_foc hc A.ht rfl (by intros; rw [hK']; simp)⟩))
    · have := A.set (c := f.ctrl) (c' := f'.ctrl) (k := []) (k' := []) (hcr (fun _ => rfl) U) .nil
      rw [← hK, s_eta A.hs] at this; exact .inl this
    · simp [μ, A.hs, A.ht, hK, hK'] <;> omega
  | ifS _ _ _ k => sigpop
  | ifST _ _ _ k => sigpop
  | whileS _ _ _ _ k => sigpop
  | whileT _ _ _ _ k => sigpop
  | @loop _ K0 K0' c b u hn h1 h2 h3 k =>
    rcases hc with ⟨v, h1', h2'⟩ | ⟨v, h1', h2'⟩ | ⟨-, hn', h1', h2'⟩ | ⟨-, hn', h1', h2'⟩
    · exact sig_pop (U := U) (i := false) A (.inl ⟨v, h1', h2'⟩) (fun _ => rfl) k (by simp [Sem.step, A.hs, h1', hK, Sem.raiseStep, Sem.setC])
        (by simp [PyCore.step, A.ht, h2', hK', PyCore.raiseStep, PyCore.top]) (by simp [PyCore.focus, A.ht, h2', hK'])
    · exact sig_pop (U := U) (i := false) A (.inr (.inl ⟨v, h1', h2'⟩)) (fun _ => rfl) k (by simp [Sem.step, A.hs, h1', hK, Sem.retStep, Sem.setC])
        (by simp [PyCore.step, A.ht, h2', hK', PyCore.retStep, PyCore.top]) (by simp [PyCore.focus, A.ht, h2'])
    · exact A.go11 (c := .exec []) (c' := .exec []) (k := K0) (k' := K0')
        (by simp [Sem.step, A.hs, h1', hK, Sem.brkStep, Sem.setC]) (by simp [PyCore.step, A.ht, h2', hK', PyCore.brkStep, PyCore.top])
        (.exec (goodB_nil _ U) (by simp)) k (cov_none A (by simp [PyCore.focus, A.ht, h2']))
    · exact A.go11 (c := .ev c) (c' := .ev (trE f.chain c)) (k := .whileS c b u :: K0)
        (by simp [Sem.step, A.hs, h1', hK, Sem.contStep, Sem.setC]) (by simp [PyCore.step, A.ht, h2', hK', PyCore.contStep, PyCore.top])
        (.ev h1) (.core (.whileS hn h1 h2 h3 k)) (cov_none A (by simp [PyCore.focus, A.ht, h2']))
  | retS k => sigpop
  | @tryE _ K0 K0' hs u hn h1 h2 k =>
    rcases hc with ⟨v, h1', h2'⟩ | hc'
    · cases hs with
      | nil =>
        exact sig_pop (U := U) (i := false) A (.inl ⟨v, h1', h2'⟩) (fun _ => rfl) k
          (by simp [Sem.step, A.hs, h1', hK, Sem.raiseStep, Sem.setC])
          (by simp [PyCore.step, A.ht, h2', hK', PyCore.raiseStep, PyCore.top, trHs])
          (by simp [PyCore.focus, A.ht, h2', hK', trHs])
      | cons h hs0 =>
        obtain ⟨lh, ty, x, hb0⟩ := h
        cases ty with
        | none => exact absurd ⟨lh, x, hb0, hs0, u, K0, K0', rfl, rfl, h1, h2, k⟩ (hb ⟨v, h1'⟩)
        | some ty =>
          obtain ⟨g1, g2, g3⟩ := goodHs_head h1
          exact A.go11 (c := .ev ty) (k := .catchS v x hb0 hs0 u :: K0)
            (by simp [Sem.step, A.hs, h1', hK, Sem.raiseStep, Sem.setC])
            (by simp [PyCore.step, A.ht, h2', hK', PyCore.raiseStep, PyCore.top, trHs]) (.ev g1)
            (.core (.catchS hn g2 g3 h2 (xok_head W h1) k))
            (fun z hz => by
              have hz := pfocus_le hz
              simp [PyCore.focus, A.ht, h2', hK', trHs] at hz
              exact .inl (by simp [Sem.focus, A.hs, h1', hK, Sem.Handler.lbl, ← hz, sub_div]))
    · exact sig_pop (U := U) (i := false) A (.inr hc') (fun _ => rfl) k (by
        rcases hc' with ⟨v, h1, -⟩ | ⟨-, -, h1, -⟩ | ⟨-, -, h1, -⟩ <;>
          simp [Sem.step, A.hs, h1, hK, Sem.retStep, Sem.brkStep, Sem.contStep, Sem.setC])
        (by rcases hc' with ⟨v, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, -, h2⟩ <;>
          simp [PyCore.step, A.ht, h2, hK', PyCore.retStep, PyCore.brkStep, PyCore.contStep, PyCore.top])
        (by rcases hc' with ⟨v, -, h2⟩ | ⟨-, -, -, h2⟩ | ⟨-, -, -, h2⟩ <;> simp [PyCore.focus, A.ht, h2])
  | catchS _ _ _ _ _ k => sigpop
  | catchT _ _ _ _ _ k => sigpop
  | @handler _ K0 K0' y y' ex hn hx k =>
    obtain ⟨s1, t1, g, g', e1, e2, A1, hch, h1, h2, h3, h4, ha⟩ := unset0 A.zero hx f.ctrl K0 f'.ctrl K0'
    refine goal11 A1 (by rw [← e1]; sige) (by rw [← e2]; sigp) (U := U) (i := false)
      (by rw [h1, h3, hch]; exact hcr (fun _ => rfl) U) (by rw [h2, h4]; exact krel_move k hch ha fun _ h => h)
      (csig_foc hc A.ht rfl (by intros; rw [hK']; simp))
  | ifK _ _ k => sigpop
  | ifT _ _ k => sigpop
  | boolK _ k => sigpop
  | boolT _ k => sigpop
  | @boolNil _ K0 _ o k =>
    have e1 : Sem.step I s = some { s with stack := { f with kont := K0 } :: fs } := by sige
    refine Or.inr (Or.inr (Or.inl ⟨_, [s], .cons e1 (.nil _), by simp, ?_, ?_⟩))
    · have := A.set (c := f.ctrl) (c' := f'.ctrl) (k := K0) (k' := f'.kont) (hcr (j := true) (fun h => by cases h) U)
        (by rw [hK']; exact k)
      rw [t_eta A.ht] at this; exact crelI_seen this
    · simp [μ, A.hs, A.ht, hK]
  | walrusK _ k => sigpop
  | yieldK k => sigpop
  | @native _ K0 K0' kk k =>
    rcases hc with ⟨v, h1', h2'⟩ | ⟨v, h1', h2'⟩ | ⟨hi, -⟩ | ⟨hi, -⟩
    · exact A.go11 (c := .kapp kk (.error v)) (c' := .kapp kk (.error v)) (k := K0) (k' := K0')
        (by simp [Sem.step, A.hs, h1', hK, Sem.raiseStep, Sem.setC]) (by simp [PyCore.step, A.ht, h2', hK', PyCore.raiseStep, PyCore.top])
        .kapp k (cov_none A (by simp [PyCore.focus, A.ht, h2', hK']))
    · exact sig_pop (U := U) (i := true) A (.inr (.inl ⟨v, h1', h2'⟩)) (fun h => by cases h) k
        (by simp [Sem.step, A.hs, h1', hK, Sem.retStep, Sem.setC])
        (by simp [PyCore.step, A.ht, h2', hK', PyCore.retStep, PyCore.top]) (by simp [PyCore.focus, A.ht, h2'])
    · cases hi
    · cases hi
  | assignN _ k => sigpop
  | decos k => sigpop

end


theorem val_core : KCase I p true CoreK CVal := by
  intro H s t f fs f' fs' U A W ⟨v, hc, hc'⟩ hk
  have hn := cov_none A (by simp [PyCore.focus, A.ht, hc'])
  generalize hK : f.kont = K at hk
  generalize hK' : f'.kont = K' at hk
  cases hk with
  | exprS k =>
    exact A.go11 (c := .exec []) (c' := .exec (trB f.chain [])) (by sstep) (by simp [trB]; pstep)
      (.exec (goodB_nil _ U) (by simp)) k hn
  | @binL _ _ _ op b hop hb k =>
    exact A.go11 (c := .ev b) (k := .binR op v :: _) (by sstep) (by pstep) (.ev hb) (.core (.binR hop k)) hn
  | @binR _ _ _ op a hop k => exact A.go11 (c := .op (.binop op) [a, v]) (by sstep) (by simp [PyCore.step, A.ht, hc', hK',
      PyCore.valStep, PyCore.top, hop]) .op k hn
  | ifS hnc h1 h2 k => exact val_tst A (v := v) (by sstep) (by pstep) (.core (.ifST hnc h1 h2 k)) (by simp [PyCore.focus, A.ht, hc'])
  | whileS hnc h1 h2 h3 k =>
    exact val_tst A (v := v) (by sstep) (by pstep) (.core (.whileT hnc h1 h2 h3 k)) (by simp [PyCore.focus, A.ht, hc'])
  | ifK h1 h2 k => exact val_tst A (v := v) (by sstep) (by pstep) (.core (.ifT h1 h2 k)) (by simp [PyCore.focus, A.ht, hc'])
  | @boolK _ _ _ l o _ _ hH h1 k =>
    exact val_tst A (v := v) (by sstep) (by pstep) (.core (.boolT (o := o) (v := v) hH h1 k)) (by simp [PyCore.focus, A.ht, hc'])
  | ifST hnc h1 h2 k =>
    cases v
    case bool b =>
      cases b
      · exact A.go11 (c := .exec _) (c' := .exec (trB f.chain _)) (by sstep) (by pstep) (.exec h2 (fun _ => hnc)) k hn
      · exact A.go11 (c := .exec _) (c' := .exec (trB f.chain _)) (by sstep) (by pstep) (.exec h1 (fun _ => hnc)) k hn
    all_goals exact fin_stuck A (by sstep) (by pstep) hn
  | whileT hnc h1 h2 h3 k =>
    cases v
    case bool bb =>
      cases bb
      · exact A.go11 (c := .exec _) (c' := .exec (trB f.chain _)) (by sstep) (by pstep) (.exec h3 (fun _ => hnc)) k hn
      · exact A.go11 (c := .exec _) (c' := .exec (trB f.chain _)) (by sstep) (by pstep)
          (.exec h2 (fun _ => hnc)) (.core (.loop hnc h1 h2 h3 k)) hn
    all_goals exact fin_stuck A (by sstep) (by pstep) hn
  | ifT h1 h2 k =>
    cases v
    case bool bb =>
      cases bb
      · exact A.go11 (c := .ev _) (by sstep) (by pstep) (.ev h2) k hn
      · exact A.go11 (c := .ev _) (by sstep) (by pstep) (.ev h1) k hn
    all_goals exact fin_stuck A (by sstep) (by pstep) hn
  | retS k => exact A.go11 (c := .retv v) (by sstep) (by pstep) .retv k hn
  | @native _ _ _ kk k => exact A.go11 (c := .kapp kk (.ok v)) (by sstep) (by pstep) .kapp k hn
  | @catchS _ _ _ ex y y' hb hs u hnc h1 h2 h3 hx k =>
    exact A.go11 (c := .op .excMatch [ex, v]) (k := .catchT ex y hb hs u :: _) (by sstep) (by pstep) .op (.core (.catchT hnc h1 h2 h3 hx k)) hn
  | @catchT _ _ _ ex y y' hb hs u hnc h1 h2 h3 hx k =>
    cases v
    case bool b =>
      cases b
      · exact A.go11 (c := .raise ex) (k := .tryE hs u :: _) (by sstep) (by pstep) .raise (.core (.tryE hnc h2 h3 k)) hn
      · exact val_catchT_true A W hc hc' hK hK' hnc h1 h2 h3 hx k
    all_goals exact fin_stuck A (by sstep) (by pstep) hn
  | @boolNil _ K0 _ o k =>
    subst hK'
    have e1 : Sem.step I s = some { s with stack := { f with ctrl := .val v, kont := K0 } :: fs } := by sstep
    refine Or.inr (Or.inr (Or.inl ⟨_, [s], .cons e1 (.nil _), by simp, ?_, ?_⟩))
    · have := A.set (c := .val v) (c' := .val v) (k' := f'.kont) .val k
      rw [← hc', t_eta A.ht] at this
      exact crelI_seen this
    · simp [μ, A.hs, A.ht, hK]
  | @boolT _ K0 K0' l o a e rest hH hg k =>
    cases v
    case bool b =>
      by_cases hb : (b == o) = true
      · obtain rfl : b = o := by simpa using hb
        cases rest with
        | nil =>
          exact A.go11 (c := .ev e) (k := .boolK b [] :: _) (c' := .ev (trE f.chain e))
            (by sstep) (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, trEs, boolChainIn])
            (.ev (hg e (by simp))) (.core (.boolNil k)) hn
        | cons e2 r =>
          have e2' : PyCore.step I t = some { t with stack :=
              { f' with ctrl := .ev (boolChainIn l b (trEs f.chain (e :: e2 :: r))), kont := K0' } :: fs' } := by
            simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top]
          have e3 : PyCore.step I { t with stack :=
              { f' with ctrl := .ev (boolChainIn l b (trEs f.chain (e :: e2 :: r))), kont := K0' } :: fs' } =
              some { t with stack := { f' with
                ctrl := .ev (trE f.chain e), kont := .boolK b (boolChainIn l b (trEs f.chain (e2 :: r))) :: K0' } :: fs' } := by
            simp [PyCore.step, PyCore.evalStep, PyCore.top, trEs, boolChainIn]
          have e1 : Sem.step I s = some { s with stack := { f with ctrl := .ev e, kont := .boolK b (e2 :: r) :: K0 } :: fs } := by
            sstep
          refine goal_b (.cons e1 (.nil _)) (by simp) (.cons e2' (.cons e3 (.nil _))) (by simp)
            (crelI_seen (A.set (.ev (hg e (by simp))) (.core (.boolK hH (fun x hx => hg x (List.mem_cons_of_mem _ hx)) k)))) ?_
          intro y hy x hx
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · have := pfocus_le hx; simp [PyCore.focus, A.ht, hc'] at this
          · have := pfocus_le hx
            simp [PyCore.focus, trEs, boolChainIn, PyCore.Expr.label] at this
            refine .inl ?_
            rw [← this, sub_div _ _ (by omega)]; exact hH
      · have hb' : ¬ b = o := by simpa using hb
        exact A.go11 (c := .val a) (by simp [Sem.step, A.hs, hc, hK, Sem.valStep, Sem.setC, hb'])
          (by simp [PyCore.step, A.ht, hc', hK', PyCore.valStep, PyCore.top, hb']) .val k hn
    all_goals exact fin_stuck A (by sstep) (by pstep) hn
  | walrusK hy k => exact val_walrusK A W hc hc' hK hK' hy k
  | yieldK k => exact val_yieldK A W hc hc' hK hK' k
  | assignN hy k => exact val_assignN A W hc hc' hK hK' hy k
  | @decos _ _ _ ds k =>
    cases ds with
    | nil => exact A.go11 (c := .val v) (by sstep) (by pstep) .val k hn
    | cons d ds => exact A.go11 (c := .call d [v] []) (k := .decos ds :: _) (by sstep) (by pstep) .call (.core (.decos k)) hn

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}



theorem wait_sim (A : At p H s t f fs f' fs') (hc : f.ctrl = .wait) (hc' : f'.ctrl = .wait) : Goal I p H s t :=
  fin_stuck A (by simp [Sem.step, A.hs, hc]) (by simp [PyCore.step, A.ht, hc'])
    (cov_none A (by simp [PyCore.focus, A.ht, hc']))

theorem At.setSt (A : At p H s t f fs f' fs') (st' : σ) {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ}
    {c' : PyCore.Ctrl σ} {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)} (hc : CR p f.chain U i c c')
    (hk : KRel A.x U i k k') (he : EnterSub k f.kont := by esub) :
    CRel p H { s with stack := { f with ctrl := c, kont := k } :: fs, st := st' }
      { t with stack := { f' with ctrl := c', kont := k' } :: fs', st := st' } :=
  have h := A.set hc hk he
  ⟨h.stack, h.objs, h.cells, h.glob, h.out, h.next, h.res, rfl, h.wait,
    ⟨h.ids.nodup, h.ids.lt, h.ids.obj, h.ids.susp, h.ids.gk, h.ids.m0, h.ids.sk⟩, h.enter⟩

/-- The interpretation's result `r` handled on both sides. -/
theorem handle_sim (A : At p H s t f fs f' fs') {U : Label → Prop} (r : Py.Res σ) (hk : KRel A.x U true f.kont f'.kont)
    (e1 : Sem.step I s = some (Sem.handle s.objs s.cells s.glob s.next s.res f fs r))
    (e2 : PyCore.step I t = some (PyCore.handle t.objs t.cells t.glob0 t.globW t.out t.next t.res f' fs' r))
    (hfoc : PyCore.focus t = none) : Goal I p H s t := by
  have hcov' : ∀ zs : List (Sem.Config σ), Cover (Touch p) pfocus H zs [t] := by
    intro zs y hy x hx
    rw [List.mem_singleton] at hy
    rw [hy] at hx
    rw [pfocus_le hx] at hfoc; cases hfoc
  cases r with
  | ok st' v =>
    exact goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen (A.setSt st' .val hk)) (hcov' _)
  | raise st' e =>
    have h := A.setSt st' (c := Sem.raiseNew (f :: fs) e) (c' := PyCore.raiseNew (f' :: fs') e)
      (by rw [raiseNew_s, raiseNew_t A.stk]; exact .raise) hk
    exact goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen h) (hcov' _)
  | reraise st' e =>
    exact goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen (A.setSt st' .raise hk)) (hcov' _)
  | call st' g args kws k =>
    exact goal_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp)
      (crelI_seen (A.setSt st' .call (.core (.native hk)))) (hcov' _)

theorem op_sim {U : Label → Prop} (A : At p H s t f fs f' fs') {o : Py.Op} {vs : List Val}
    (hc : f.ctrl = .op o vs) (hc' : f'.ctrl = .op o vs) (hk : KRel A.x U true f.kont f'.kont) : Goal I p H s t := by
  refine handle_sim A (I.op s.st o vs) hk ?_ ?_ (by simp [PyCore.focus, A.ht, hc'])
  · have hs := A.hs
    obtain ⟨stk, objs, cells, glob, st, nx, res⟩ := s
    simp only at hs; subst hs
    simp [Sem.step, hc, Sem.opStep]
  · simp [PyCore.step, A.ht, hc', A.r.st]

theorem kapp_sim {U : Label → Prop} (A : At p H s t f fs f' fs') {k : σ → Except Val Val → Py.Res σ}
    {r : Except Val Val} (hc : f.ctrl = .kapp k r) (hc' : f'.ctrl = .kapp k r)
    (hk : KRel A.x U true f.kont f'.kont) : Goal I p H s t := by
  refine handle_sim A (k s.st r) hk ?_ ?_ (by simp [PyCore.focus, A.ht, hc'])
  · have hs := A.hs
    obtain ⟨stk, objs, cells, glob, st, nx, res⟩ := s
    simp only at hs; subst hs
    simp [Sem.step, hc, Sem.kappStep]
  · simp [PyCore.step, A.ht, hc', A.r.st]






end

/-! ## Comprehensions' kinds; a call held as PyCore's `callA` -/

mutual
theorem yld_E (p p' : Option Name) (st st' : Bool) : ∀ e : Expr, PyCore.Fact.yld ∈ factsE p st e ↔ PyCore.Fact.yld ∈ factsE p' st' e
  | .const .. => by simp [factsE]
  | .name _ x => by cases st <;> cases st' <;> simp [factsE]
  | .bin _ _ a b | .sub _ a b => by simp [factsE, yld_E p p' false false a, yld_E p p' false false b]
  | .unary _ _ a | .attr _ a _ => by simp [factsE, yld_E p p' false false a]
  | .star _ a => by simp [factsE, yld_E p p' st st' a]
  | .list _ es | .tuple _ es => by simp [factsE, yld_Es p p' st st' es]
  | .boolop _ _ es | .set _ es | .fstr _ es => by simp [factsE, yld_Es p p' false false es]
  | .compare _ a _ es => by simp [factsE, yld_E p p' false false a, yld_Es p p' false false es]
  | .ifexp _ c a b => by simp [factsE, yld_E p p' false false c, yld_E p p' false false a, yld_E p p' false false b]
  | .call _ f args kws => by simp [factsE, yld_E p p' false false f, yld_Es p p' false false args, yld_Ks p p' kws]
  | .slice _ a b c => by simp [factsE, yld_O p p' a, yld_O p p' b, yld_O p p' c]
  | .dict _ kvs => by simp [factsE, yld_Ds p p' kvs]
  | .lam _ ps _ => by simp [factsE, yld_Ps p p' ps]
  | .comp _ _ es gs => by simp [factsE, yld_G1 p p' gs, List.mem_filter, PyCore.Fact.isWal]
  | .walrus _ x e => by simp [factsE, yld_E p p' false false e]
  | .yield _ e => by simp [factsE]
  | .yieldFrom _ e => by simp [factsE]
  | .fmt _ e _ s => by simp [factsE, yld_E p p' false false e, yld_O p p' s]
theorem yld_O (p p' : Option Name) : ∀ e : Option Expr, PyCore.Fact.yld ∈ factsO p e ↔ PyCore.Fact.yld ∈ factsO p' e
  | none => by simp [factsO]
  | some e => by simp [factsO, yld_E p p' false false e]
theorem yld_Es (p p' : Option Name) (st st' : Bool) : ∀ es : List Expr, PyCore.Fact.yld ∈ factsEs p st es ↔ PyCore.Fact.yld ∈ factsEs p' st' es
  | [] => by simp [factsEs]
  | e :: es => by simp [factsEs, yld_E p p' st st' e, yld_Es p p' st st' es]
theorem yld_Ks (p p' : Option Name) : ∀ ks : List Kw, PyCore.Fact.yld ∈ factsKs p ks ↔ PyCore.Fact.yld ∈ factsKs p' ks
  | [] => by simp [factsKs]
  | .mk _ _ e :: ks => by simp [factsKs, yld_E p p' false false e, yld_Ks p p' ks]
theorem yld_Ds (p p' : Option Name) : ∀ kvs : List DItem, PyCore.Fact.yld ∈ factsDs p kvs ↔ PyCore.Fact.yld ∈ factsDs p' kvs
  | [] => by simp [factsDs]
  | .mk k v :: kvs => by simp [factsDs, yld_O p p' k, yld_E p p' false false v, yld_Ds p p' kvs]
theorem yld_Ps (p p' : Option Name) : ∀ ps : List Param, PyCore.Fact.yld ∈ factsPs p ps ↔ PyCore.Fact.yld ∈ factsPs p' ps
  | [] => by simp [factsPs]
  | .mk _ _ _ d a :: ps => by simp [factsPs, yld_O p p' d, yld_O p p' a, yld_Ps p p' ps]
theorem yld_G1 (p p' : Option Name) : ∀ gs : List Gen, PyCore.Fact.yld ∈ factsG1 p gs ↔ PyCore.Fact.yld ∈ factsG1 p' gs
  | [] => by simp [factsG1]
  | .mk _ _ i _ :: _ => by simp [factsG1, yld_E p p' false false i]
theorem yld_Gs (p p' : Option Name) (first : Bool) : ∀ gs : List Gen, PyCore.Fact.yld ∈ factsGs p first gs ↔ PyCore.Fact.yld ∈ factsGs p' first gs
  | [] => by simp [factsGs]
  | .mk _ t i ifs :: gs => by
    cases first <;> simp [factsGs, yld_E p p' false false i, yld_E p p' true true t, yld_Es p p' false false ifs,
      yld_Gs p p' false gs]
end

/-- A comprehension of `p` has no `yield` in its own scope: its function is a generator exactly for a
generator expression. -/
theorem comp_kind {C : List Scope} {l : Label} {k : CompKind} {es : List Expr} {gs : List Gen}
    (h : okE (.comp l k es gs) = true) : (Scope.comp l k es gs).kind C = if k = .gen then .gen else .plain := by
  simp only [okE, Bool.and_eq_true, Bool.not_eq_true'] at h
  have h2 : PyCore.Fact.yld ∉ factsGs none true gs ++ factsEs none false es := by
    intro hm; have := h.2; rw [List.contains_iff_mem.2 hm] at this; cases this
  have hy : PyCore.Fact.yld ∉ factsGs (priv (.comp l k es gs :: C)) true gs ++ factsEs (priv (.comp l k es gs :: C)) false es := by
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · exact h2 (by rw [List.mem_append]; exact .inl ((yld_Gs _ _ true gs).1 hm))
    · exact h2 (by rw [List.mem_append]; exact .inr ((yld_Es _ _ false false es).1 hm))
  by_cases hk : k = .gen <;> simp [Scope.kind, Scope.facts, hk, hy]

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore's call of a function object or `next` on the value `v` (a loop's `next`, a comprehension's
function on its iterator) steps as the call control `call g [v] []`. -/
theorem pstep_callA {g v : Py.Val} {K' : List (PyCore.Kont σ)} (hg : (∃ o, g = .fn o) ∨ g = .next)
    (ht : t.stack = f' :: fs') (hc' : f'.ctrl = .val v) (hK' : f'.kont = .callA g :: K') :
    PyCore.step I t = PyCore.step I { t with stack := { f' with ctrl := .call g [v] [], kont := K' } :: fs' } := by
  rw [pstep_val ht hc']
  simp only [PyCore.valStep, hK', PyCore.step, PyCore.callArgs]
  rcases hg with ⟨o, rfl⟩ | rfl
  · rfl
  · rfl

theorem At0.toAt (A : At0 p H s t f fs f' fs') {U : Label → Prop} {i : Bool} (hc : CR p f.chain U i f.ctrl f'.ctrl)
    (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U i f.kont f'.kont) : At p H s t f fs f' fs' := by
  have hr := A.crel hc hk
  exact ⟨hr, A.hs, A.ht, ⟨A.hf, A.hl, U, i, hc, hk⟩⟩

/-- Surf calls `g` on `v` (a function object or `next`) while PyCore holds `v` with the call of `g`
next: a step of the call lemma at PyCore's call control gives the step here. -/
theorem callA_sim (A : At0 p H s t f fs f' fs') {U : Label → Prop} {g v : Py.Val} {K' : List (PyCore.Kont σ)}
    (hg : (∃ o, g = .fn o) ∨ g = .next) (hc : f.ctrl = .call g [v] []) (hc' : f'.ctrl = .val v)
    (hK' : f'.kont = .callA g :: K') (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U true f.kont K')
    (h : At p H s { t with stack := { f' with ctrl := .call g [v] [], kont := K' } :: fs' } f fs
        { f' with ctrl := .call g [v] [], kont := K' } fs' →
      GoalB I p H s { t with stack := { f' with ctrl := .call g [v] [], kont := K' } :: fs' }) : GoalB I p H s t := by
  have A1 := A.updT (.call g [v] []) K'
  have hA := A1.toAt (U := U) (i := true) (by rw [hc]; exact .call) hk
  refine SimStepB.swap (pstep_callA hg A.ht hc' hK') ?_ ?_ ?_ (h hA)
  · simp [pfocus, PyCore.focus, A.ht, hc']
  · simp [μ, A.ht, hK', hc'] <;> omega
  · intro _ a' hf
    simpa [Fin, PyCore.outcome, A.ht] using hf

theorem GoalB.goal {s : Sem.Config σ} {t : PyCore.Config σ} (h : GoalB I p H s t) : Goal I p H s t := h.sim

/-- `goal_b` (both runs step) as a `GoalB`. -/
theorem goalB_b {s s1 : Sem.Config σ} {t t1 : PyCore.Config σ} {xs ys}
    (pa : Path (Sem.step I) s s1 xs) (hxs : xs ≠ []) (pb : Path (PyCore.step I) t t1 ys) (hys : ys ≠ [])
    (hr : CRelI p (Seen (Touch p) H xs) s1 t1) (hc : Cover (Touch p) pfocus H (s1 :: xs) ys) : GoalB I p H s t :=
  .inr (.inl ⟨s1, t1, xs, ys, pa, hxs, pb, hys, hr.mono_H (seen_sub fun z hz => List.mem_cons_of_mem _ hz), hc⟩)

/-- `goal_t` as a `GoalB`. -/
theorem goalB_t {s s1 : Sem.Config σ} {t t1 : PyCore.Config σ} {xs ys}
    (pa : Path (Sem.step I) s s1 xs) (hxs : xs ≠ []) (pb : Path (PyCore.step I) t t1 ys) (hys : ys ≠ [])
    (hr : CRelI p (Seen (Touch p) H (s1 :: xs)) s1 t1) (hc : Cover (Touch p) pfocus H (s1 :: xs) ys) :
    GoalB I p H s t :=
  .inr (.inl ⟨s1, t1, xs, ys, pa, hxs, pb, hys, hr, hc⟩)

/-- `fin_stuck` (both runs stuck) as a `GoalB`. -/
theorem finB_stuck (A : At p H s t f fs f' fs') (h1 : Sem.step I s = none) (h2 : PyCore.step I t = none)
    (hcov : ∀ x, pfocus t = some x → Touch p s (x / 64)) : GoalB I p H s t := by
  refine .inl ⟨s, t, [], [], .nil _, h1, .nil _, h2, ?_, ?_⟩
  · simp [Fin, Sem.outcome, PyCore.outcome, A.hs, A.ht, OCorr, A.r.out, A.r.st]
  · intro y hy x hx; simp at hy; subst hy; exact .inr ⟨s, by simp, hcov x hx⟩

end



/-! ## Distinct labels; helpers of the `yield from` cases -/

theorem labelsGs_app : ∀ (pre post : List Gen), labelsGs (pre ++ post) = labelsGs pre ++ labelsGs post
  | [], _ => rfl
  | .mk _ _ _ _ :: pre, post => by simp [labelsGs, labelsGs_app pre post]

/-- A comprehension's node and a clause's node are distinct, and the clause's node is no node of its
target, iterable, conditions, the other clauses or the elements. -/
theorem comp_lbl {C : List Scope} {U : Label → Prop} {l : Label} {k : CompKind} {es : List Expr}
    {pre rest : List Gen} {lg : Label} {t i : Expr} {ifs : List Expr}
    (h : GoodE p C U (.comp l k es (pre ++ .mk lg t i ifs :: rest))) :
    l ≠ lg ∧ lg ∉ labelsE t ∧ lg ∉ labelsE i ∧ lg ∉ labelsEs ifs ∧ lg ∉ labelsGs rest ∧ lg ∉ labelsGs pre ∧
      lg ∉ labelsEs es := by
  have hn := h.nd
  simp only [labelsE, labelsGs_app] at hn
  obtain ⟨hl, hn⟩ := List.nodup_cons.1 hn
  obtain ⟨-, hn2, hd1⟩ := List.nodup_append.1 hn
  obtain ⟨-, hn3, hd2⟩ := List.nodup_append.1 hn2
  have hg : lg ∈ labelsGs (.mk lg t i ifs :: rest) := by simp [labelsGs]
  simp only [labelsGs] at hn3 hg
  obtain ⟨hlg, -⟩ := List.nodup_cons.1 hn3
  refine ⟨fun e => hl (by subst e; simp [labelsGs]), fun hm => hlg (by simp [hm]), fun hm => hlg (by simp [hm]),
    fun hm => hlg (by simp [hm]), fun hm => hlg (by simp [hm]), fun hm => hd2 lg hm lg (by simp [labelsGs]) rfl,
    fun hm => hd1 lg hm lg (by simp [labelsGs]) rfl⟩

/-- A `for` statement's node is no node of its target or body. -/
theorem for_lbl {C : List Scope} {U : Label → Prop} {l : Label} {tg it : Expr} {b u ss : List Stmt}
    (h : GoodB p C U (.for l tg it b u :: ss)) : l ∉ labelsE tg ∧ l ∉ labelsB b := by
  have hn := h.nd
  simp only [labelsB, labelsS] at hn
  have h1 := (List.nodup_cons.1 (List.nodup_append.1 hn).1).1
  exact ⟨fun hm => h1 (by simp [hm]), fun hm => h1 (by simp [hm])⟩

def isSusp : Option (PyCore.Obj σ) → Bool
  | some (.gen (.susp _)) => true
  | _ => false

/-- The number of suspended generators of a PyCore configuration. -/
def nSusp (t : PyCore.Config σ) : Nat := (List.range t.next).countP fun o => isSusp t.objs[o]?

theorem countP_drop1 {q q' : Nat → Bool} {o : Nat} (h1 : q o = true) (h2 : q' o = false)
    (h : ∀ x, x ≠ o → q' x = q x) : ∀ n, o < n → (List.range n).countP q' < (List.range n).countP q
  | 0, h0 => absurd h0 (Nat.not_lt_zero _)
  | n + 1, h0 => by
    rw [List.range_succ, List.countP_append, List.countP_append]
    by_cases hn : n = o
    · subst hn
      have : (List.range n).countP q' = (List.range n).countP q :=
        List.countP_congr fun x hx => by rw [h x (Nat.ne_of_lt (List.mem_range.1 hx))]
      rw [this]; simp [h1, h2]
    · have := countP_drop1 h1 h2 h n (by omega)
      have e : q' n = q n := h n hn
      simp [e]; omega

theorem nSusp_run {t : PyCore.Config σ} {o : Nat} {g' : PyCore.Frame σ} (ho : t.objs[o]? = some (.gen (.susp g')))
    (hlt : o < t.next) (S : List (PyCore.Frame σ)) :
    nSusp { t with stack := S, objs := t.objs.insert o (.gen .running) } < nSusp t := by
  unfold nSusp
  refine countP_drop1 (o := o) (by simp [isSusp, ho]) (by simp [isSusp]) (fun x hx => ?_) _ hlt
  simp [Std.HashMap.getElem?_insert, Ne.symm hx]


section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- `next` resumes the suspended generator `o` in both runs: its frames are pushed, the callers wait. -/
theorem At0.push (A : At0 p H s t f fs f' fs') {o : Nat} {g : Sem.Frame σ} {g' : PyCore.Frame σ}
    (ho' : pObj t o = some (.gen (.susp g'))) (hg0 : FRel0 g g') (hgl : ∀ S C, g.chain = S :: C → H S.label)
    {Uw : Label → Prop} (kw : List (Sem.Kont σ)) (kw' : List (PyCore.Kont σ))
    (hkw : KRel (cx p H (rdOf t f') (ownOf t f') f) Uw true kw kw')
    (hso : sObj s o = some (.gen (.susp g))) (hen : EnterSub kw f.kont := by esub) :
    At0 p H { s with stack := g :: { f with ctrl := .wait, kont := kw } :: fs, objs := s.objs.insert o (.gen .running) }
      { t with stack := g' :: { f' with ctrl := .wait, kont := kw' } :: fs', objs := t.objs.insert o (.gen .running) }
      g ({ f with ctrl := .wait, kont := kw } :: fs) g' ({ f' with ctrl := .wait, kont := kw' } :: fs') := by
  obtain ⟨hid, hnot⟩ := A.ids.susp o g' ho'
  have hsk := A.ids.sk o g' ho'
  have hob := A.ids.obj o _ ho'
  have hnd := A.ids.nodup
  rw [A.ht] at hnot hnd
  refine ⟨rfl, rfl, hg0, hgl, ⟨⟨A.hf.upd .wait kw .wait kw', A.hl, Uw, true, .wait, hkw⟩, A.hfs⟩, fun o2 => ?_, A.cells,
    A.glob, A.out, A.next, A.res, A.st, ?_, ?_,
    EnterInv.ins ⟨fun x hx => by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact A.enter.2 o _ hso
      · exact (A.enter.1 f List.mem_cons_self).sub hen
      · exact A.enter.1 x (List.mem_cons_of_mem _ hx), A.enter.2⟩ (insOk_gen _) fun _ e => nomatch e⟩
  · by_cases h : o2 = o
    · subst h; simp only [sObj, pObj, Std.HashMap.getElem?_insert_self, PyCore.OptRel]; exact .gen .running
    · have := A.objs o2
      simp only [sObj, pObj, Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm h, ite_false] at this ⊢
      exact this
  · intro g2 hg2
    rcases List.mem_cons.1 hg2 with rfl | hg2
    · rfl
    · exact A.wait g2 hg2
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := A.ids
    rw [A.ht] at h2 h4 h5 h6
    refine ⟨?_, fun g2 hg2 => ?_, fun o2 b hb => ?_, fun o2 g2 ho2 => ?_, fun g2 hg2 o2 hk => ?_, fun g2 hg2 hm => ?_,
      fun o2 g2 ho2 => ?_⟩
    · simp only [List.map_cons, List.nodup_cons] at hnd ⊢
      refine ⟨?_, hnd⟩
      intro hm
      rcases List.mem_cons.1 hm with e | hm
      · exact hnot f' (by simp) (hid ▸ e.symm ▸ rfl)
      · obtain ⟨h', hh', e⟩ := List.mem_map.1 hm
        exact hnot h' (by simp [hh']) (by rw [e, hid])
    · simp only [List.mem_cons] at hg2
      rcases hg2 with rfl | rfl | hg2
      · rw [hid]; exact hob
      · exact h2 f' (by simp)
      · exact h2 _ (by simp [hg2])
    · by_cases h : o2 = o
      · rw [h]; exact hob
      · simp only [pObj, Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm h, ite_false] at hb
        exact h3 o2 b hb
    · have h : o2 ≠ o := by rintro rfl; simp [pObj] at ho2
      simp only [pObj, Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm h, ite_false] at ho2
      obtain ⟨e, hne⟩ := h4 o2 g2 ho2
      refine ⟨e, fun h' hh' => ?_⟩
      simp only [List.mem_cons] at hh'
      rcases hh' with rfl | rfl | hh'
      · rw [hid]; exact Ne.symm h
      · exact hne f' (by simp)
      · exact hne _ (by simp [hh'])
    · simp only [List.mem_cons] at hg2
      rcases hg2 with rfl | rfl | hg2
      · rw [hsk] at hk; cases hk; exact hid
      · exact h5 f' (by simp) o2 hk
      · exact h5 _ (by simp [hg2]) o2 hk
    · simp only [List.mem_cons] at hg2
      rcases hg2 with rfl | rfl | hg2
      · rw [hsk] at hm; cases hm
      · exact h6 f' (by simp) hm
      · exact h6 _ (by simp [hg2]) hm
    · have h : o2 ≠ o := by rintro rfl; simp [pObj] at ho2
      simp only [pObj, Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm h, ite_false] at ho2
      exact h7 o2 g2 ho2


/-- `ret_goal` after a further Surf step (`yield from`'s item, then the `yield`). -/
theorem ret_goal2 (A : At p H s t f fs f' fs') {g : Sem.Frame σ} {gs : List (Sem.Frame σ)} {g' : PyCore.Frame σ}
    {gs' : List (PyCore.Frame σ)} (h1 : fs = g :: gs) (h2 : fs' = g' :: gs') {v : Val}
    {O : Std.HashMap Nat (Sem.Obj σ)} {O' : Std.HashMap Nat (PyCore.Obj σ)}
    (ho : ∀ o : Nat, PyCore.OptRel (ORel p H t.glob t.cells) O[o]? O'[o]?)
    (hob : ∀ (o : Nat) b, O'[o]? = some b → t.objs[o]? = some b ∨
      (o = f'.id ∧ ∀ h, b = .gen (.susp h) → h.id = o ∧ h.kind = .gen o))
    (hen : ∀ st, EnterInv s.objs st → EnterInv O st) {s0 : Sem.Config σ}
    (e0 : Sem.step I s = some s0) (e1 : Sem.step I s0 = some { s with stack := { g with ctrl := .val v } :: gs, objs := O })
    (e2 : PyCore.step I t = some { t with stack := { g' with ctrl := .val v } :: gs', objs := O' })
    (hfoc : PyCore.focus t = none) : Goal I p H s t := by
  have hst := A.stk; rw [h1, h2] at hst
  obtain ⟨U, i, -, hk⟩ := hst.2.1.code
  cases i
  · obtain ⟨hs0, hp0⟩ := krel_false_val (I := I) hk
    refine Or.inl ⟨_, _, [s, s0], [t], .cons e0 (.cons e1 (.nil _)), ?_, .cons e2 (.nil _), ?_, ?_, ?_⟩
    · simp only [Sem.step]; exact hs0 _ _ _ _ rfl
    · rw [pstep_val rfl (show ({ g' with ctrl := .val v } : PyCore.Frame σ).ctrl = .val v from rfl)]
      exact hp0 _ _ _ _ rfl
    · simp [Fin, Sem.outcome, PyCore.outcome, OCorr, A.r.out, A.r.st]
    · refine cover_none fun y hy => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · simp [PyCore.focus]
      · exact hfoc
  · exact goal_b (.cons e0 (.cons e1 (.nil _))) (by simp) (.cons e2 (.nil _)) (by simp)
      (crelI_seen (A.ret h1 h2 hk .val ho hob hen)) (cover_none fun y hy => by simp at hy; subst hy; exact hfoc)


end


/-! ## Pending calls (`PendRel`): a case may end with Surf at the call and PyCore before it -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

theorem At.ofCRel (hr : CRel p H s t) (hs : s.stack = f :: fs) (ht : t.stack = f' :: fs') : At p H s t f fs f' fs' :=
  ⟨hr, hs, ht, by have := hr.stack; rw [hs, ht] at this; exact this.1⟩

/-- Surf calls `g` on `v` (`next`, or a comprehension's function), PyCore holds `v` and the call of `g`:
related (`PendRel`), as the call. -/
theorem pend_callA (A : At0 p H s t f fs f' fs') {U : Label → Prop} {g v : Val} {K' : List (PyCore.Kont σ)}
    (hg : g = .next ∨ ∃ o, g = .fn o)
    (hc : f.ctrl = .call g [v] []) (hc' : f'.ctrl = .val v) (hK' : f'.kont = .callA g :: K')
    (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U true f.kont K') : CRelI p H s t :=
  .inr (.inr ⟨f, fs, f', fs', g, v, K', A.hs, A.ht, hc,
    .inl ⟨hc', hK', hg, (A.updT (.call g [v] []) K').crel (U := U) (i := true) (by rw [hc]; exact .call) hk⟩⟩)

/-- Surf calls `next` on the suspended generator `o` (`yield from`'s delegate), PyCore's `yield from`
asks it: related (`PendRel`), as the call. -/
theorem pend_yf (A : At0 p H s t f fs f' fs') {U : Label → Prop} {o : Nat} {g0 : PyCore.Frame σ}
    {K' : List (PyCore.Kont σ)} (hc : f.ctrl = .call .next [.gen o] []) (hc' : f'.ctrl = .yfStep (.gen o))
    (hK' : f'.kont = K') (ho : pObj t o = some (.gen (.susp g0)))
    (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U true f.kont (.yfGot (.gen o) :: K')) : CRelI p H s t :=
  .inr (.inr ⟨f, fs, f', fs', .next, .gen o, K', A.hs, A.ht, hc,
    .inr ⟨o, g0, rfl, rfl, hc', hK', ho, (A.updT (.call .next [.gen o] []) (.yfGot (.gen o) :: K')).crel (U := U)
      (i := true) (by rw [hc]; exact .call) hk⟩⟩)

/-- `yield from` asks a suspended generator as `next` on it does. -/
theorem pstep_yf {o : Nat} {g0 : PyCore.Frame σ} {K' : List (PyCore.Kont σ)} (ht : t.stack = f' :: fs')
    (hc' : f'.ctrl = .yfStep (.gen o)) (hK' : f'.kont = K') (ho : pObj t o = some (.gen (.susp g0))) :
    PyCore.step I t =
      PyCore.step I { t with stack := { f' with ctrl := .call .next [.gen o] [], kont := .yfGot (.gen o) :: K' } :: fs' } := by
  simp only [pObj] at ho
  simp only [PyCore.step, ht, hc', PyCore.yfStepS, ho, PyCore.callArgs, PyCore.callStep, hK']

end

/-! ## Calls of `next`, operations and other values -/

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- One step on each side changing only the top frames' code, as a `GoalB`. -/
theorem At.go11B (A : At p H s t f fs f' fs') {U : Label → Prop} {i : Bool} {c : Sem.Ctrl σ} {c' : PyCore.Ctrl σ}
    {k : List (Sem.Kont σ)} {k' : List (PyCore.Kont σ)}
    (e1 : Sem.step I s = some { s with stack := { f with ctrl := c, kont := k } :: fs })
    (e2 : PyCore.step I t = some { t with stack := { f' with ctrl := c', kont := k' } :: fs' })
    (hc : CR p f.chain U i c c') (hk : KRel A.x U i k k')
    (hcov : ∀ x, pfocus t = some x → Touch p s (x / 64)) (he : EnterSub k f.kont := by esub) : GoalB I p H s t :=
  goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen (A.set hc hk he))
    (fun y hy x hx => by simp at hy; subst hy; exact .inr ⟨s, by simp, hcov x hx⟩)

/-- A call raising the builtin exception `e` in the caller, on both sides. -/
theorem call_raise (A : At p H s t f fs f' fs') {U : Label → Prop} (hk : KRel A.x U true f.kont f'.kont) (e : Val)
    (e1 : Sem.step I s =
      some { s with stack := { f with ctrl := Sem.raiseNew ({ f with ctrl := .wait } :: fs) e, kont := f.kont } :: fs })
    (e2 : PyCore.step I t =
      some { t with stack := { f' with ctrl := PyCore.raiseNew ({ f' with ctrl := .wait } :: fs') e, kont := f'.kont } :: fs' })
    (hfoc : PyCore.focus t = none) : GoalB I p H s t := by
  have h := raiseNew_top (tail_rel A) (g := { f with ctrl := .wait }) (g' := { f' with ctrl := .wait })
    (by exact KRel.kexc hk) e
  rw [h] at e2
  exact A.go11B e1 e2 .raise hk (cov_none A hfoc)

theorem call_next_susp {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) {o : Nat}
    (hc : f.ctrl = .call .next [.gen o] []) (hc' : f'.ctrl = .call .next [.gen o] [])
    (hk : KRel A.x U true f.kont f'.kont) {g : Sem.Frame σ} {g' : PyCore.Frame σ}
    (ho : sObj s o = some (.gen (.susp g))) (ho' : pObj t o = some (.gen (.susp g')))
    (hg : FRel p H (rdOf t g') (ownOf t g') g g') : GoalB I p H s t := by
  have A1 := A.zero.push ho' hg.toFRel0 hg.hl f.kont f'.kont hk ho
  obtain ⟨U1, i1, hc1, hk1⟩ := hg.code
  have e1 : Sem.step I s =
      some { s with stack := g :: { f with ctrl := .wait, kont := f.kont } :: fs, objs := s.objs.insert o (.gen .running) } := by
    simp only [sObj] at ho
    simp [Sem.step, A.hs, hc, Sem.callStep, ho]
  have e2 : PyCore.step I t =
      some { t with stack := g' :: { f' with ctrl := .wait, kont := f'.kont } :: fs', objs := t.objs.insert o (.gen .running) } := by
    simp only [pObj] at ho'
    simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callStep, ho']
  exact goalB_b (.cons e1 (.nil _)) (by simp) (.cons e2 (.nil _)) (by simp) (crelI_seen (A1.crel hc1 hk1))
    (cover_none fun y hy => by simp at hy; subst hy; simp [PyCore.focus, A.ht, hc'])

set_option hygiene false in
macro "craise" e:term : tactic => `(tactic| exact call_raise A hk $e
  (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.setC, Sem.doOp, ho1])
  (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callStep, PyCore.callFn, PyCore.top, PyCore.errType,
    PyCore.errValue, ho2])
  hfoc)

theorem call_next_other {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) {args : List Val}
    {kws : List (Name × Val)} (hc : f.ctrl = .call .next args kws) (hc' : f'.ctrl = .call .next args kws)
    (hk : KRel A.x U true f.kont f'.kont)
    (hn : ¬ ∃ o g, args = [.gen o] ∧ kws = [] ∧ sObj s o = some (.gen (.susp g))) : GoalB I p H s t := by
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  have ho1 : True := trivial
  have ho2 : True := trivial
  rcases args with _ | ⟨v, _ | ⟨v2, args⟩⟩ <;> rcases kws with _ | ⟨kw, kws⟩
  case cons.nil.nil =>
    by_cases hv : ∃ o, v = .gen o
    · obtain ⟨o, rfl⟩ := hv
      have hr := A.r.objs o
      cases h1 : sObj s o <;> cases h2 : pObj t o <;> rw [h1, h2] at hr <;> simp only [PyCore.OptRel] at hr
      · clear ho1 ho2
        have ho1 : s.objs[o]? = none := h1
        have ho2 : t.objs[o]? = none := h2
        craise (Py.err "TypeError")
      · rename_i a b
        clear ho1 ho2
        have ho1 : s.objs[o]? = some a := h1
        have ho2 : t.objs[o]? = some b := h2
        cases hr with
        | clo => craise (Py.err "TypeError")
        | gen hg =>
          cases hg with
          | susp _ => exact absurd ⟨o, _, rfl, rfl, h1⟩ hn
          | special _ _ _ => exact absurd ⟨o, _, rfl, rfl, h1⟩ hn
          | running => craise (Py.err "ValueError")
          | done => craise (Py.stopOf .none)
    · have hv' : ∀ o, v ≠ .gen o := fun o h => hv ⟨o, h⟩
      exact A.go11B (c := .op .next [v]) (c' := .op .next [v]) (k := f.kont) (k' := f'.kont)
        (by cases v <;> first | exact absurd rfl (hv' _) | simp [Sem.step, A.hs, hc, Sem.callStep, Sem.doOp, Sem.setC])
        (by cases v <;> first | exact absurd rfl (hv' _) | simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.callStep, PyCore.top])
        .op hk (cov_none A hfoc)
  all_goals craise (Py.err "TypeError")

/-- A call of an operation value: the operation (no keywords), or `TypeError`. -/
theorem call_op {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) {o : Py.Op} {args : List Val}
    {kws : List (Name × Val)} (hc : f.ctrl = .call (.op o) args kws) (hc' : f'.ctrl = .call (.op o) args kws)
    (hk : KRel A.x U true f.kont f'.kont) : Goal I p H s t := by
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  have ho1 : True := trivial
  have ho2 : True := trivial
  cases kws with
  | nil =>
    exact A.go11 (c := .op o args) (c' := .op o args) (k := f.kont) (k' := f'.kont)
      (by simp [Sem.step, A.hs, hc, Sem.callStep, Sem.doOp, Sem.setC])
      (by simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.top]) .op hk (cov_none A hfoc)
  | cons kw kws => exact (by craise (Py.err "TypeError") : GoalB I p H s t).sim

/-- A call of what is no function object of the core, `next` or an operation: the interpretation's
(a function object's address with no closure: `TypeError`). -/
theorem call_other {U : Label → Prop} (A : At p H s t f fs f' fs') (W : WF p) {g : Val} {args : List Val}
    {kws : List (Name × Val)} (hc : f.ctrl = .call g args kws) (hc' : f'.ctrl = .call g args kws)
    (hk : KRel A.x U true f.kont f'.kont)
    (h1 : ∀ o S C cl κ kd dflt, g = .fn o → sObj s o ≠ some (.clo S C cl κ kd dflt))
    (h2 : g ≠ .next) (h3 : ∀ o, g ≠ .op o) : GoalB I p H s t := by
  have hfoc : PyCore.focus t = none := by simp [PyCore.focus, A.ht, hc']
  by_cases hfn : ∃ o, g = .fn o
  · obtain ⟨o, rfl⟩ := hfn
    have hr := A.r.objs o
    cases hs1 : sObj s o <;> cases hs2 : pObj t o <;> rw [hs1, hs2] at hr <;> simp only [PyCore.OptRel] at hr
    · have ho1 : s.objs[o]? = none := hs1
      have ho2 : t.objs[o]? = none := hs2
      craise (Py.err "TypeError")
    · rename_i a b
      have ho1 : s.objs[o]? = some a := hs1
      have ho2 : t.objs[o]? = some b := hs2
      cases hr with
      | clo => exact absurd hs1 (h1 o _ _ _ _ _ _ rfl)
      | gen => craise (Py.err "TypeError")
  · have hfn' : ∀ o, g ≠ .fn o := fun o h => hfn ⟨o, h⟩
    exact A.go11B (c := .op (.call (kws.map (·.1))) (g :: args ++ kws.map (·.2))) (k := f.kont) (k' := f'.kont)
      (by cases g <;> first | exact absurd rfl (hfn' _) | exact absurd rfl h2 | exact absurd rfl (h3 _) |
        simp [Sem.step, A.hs, hc, Sem.callStep, Sem.doOp, Sem.setC])
      (by cases g <;> first | exact absurd rfl (hfn' _) | exact absurd rfl h2 | exact absurd rfl (h3 _) |
        simp [PyCore.step, A.ht, hc', PyCore.callArgs, PyCore.top])
      .op hk (cov_none A hfoc)

end


/-! ## Stores into a target

Surf stores `v` into `tg`; PyCore runs the target's code `trT C src tg ⟦tg⟧`, the source reading `v`. -/

/-- A constant's value as a marker. -/
def pval : PE → Val
  | .const _ k => .prim k
  | _ => .none

theorem trMarks_eq : ∀ ts : List Expr, trMarks ts = ts.map starMark
  | [] => rfl
  | t :: ts => by simp [trMarks, trMarks_eq ts]

theorem GoodE.rm {C : List Scope} {U : Label → Prop} {e : Expr} {l : Label} (h : GoodE p C U e)
    (hl : l ∉ labelsE e) : GoodE p C (Rm U l) e :=
  ⟨h.s, h.t, h.ok, fun l' hl' => ⟨h.u l' hl', fun e => hl (e ▸ hl')⟩, h.pv, h.nd, h.tch⟩

theorem mem_trA {C : List Scope} {e : Expr} : ∀ {es : List Expr}, e ∈ es → trE C (unstar e) ∈ trA C es
  | [], h => by simp at h
  | a :: es, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · cases e <;> simp [trA, unstar]
    · have ih := mem_trA (C := C) h'
      cases a <;> simp [trA, ih]

theorem items_fold {C : List PyCore.Scope} {r : Label} : ∀ (es : List PE) (init : PE) (x : PyCore.Item),
    (x ∈ PyCore.itemsE R0 C init ∨ ∃ e ∈ es, x ∈ PyCore.itemsE R0 C e) →
    x ∈ PyCore.itemsE R0 C (es.foldl (fun acc e => .bin r "," acc e) init)
  | [], init, x, h => by
    rcases h with h | ⟨e, he, -⟩
    · exact h
    · simp at he
  | e :: es, init, x, h => by
    apply items_fold es
    rcases h with h | ⟨e', he', hx⟩
    · exact .inl (by simp [PyCore.itemsE, h])
    · rcases List.mem_cons.1 he' with rfl | he'
      · exact .inl (by simp [PyCore.itemsE, hx])
      · exact .inr ⟨e', he', hx⟩

theorem okAs_mem {e : Expr} : ∀ {es : List Expr}, okAs es = true → e ∈ es → okE (unstar e) = true
  | [], _, h => by simp at h
  | a :: es, ho, h => by
    rcases List.mem_cons.1 h with rfl | h'
    · cases e <;> simp_all [okAs, unstar]
    · have ho2 : okAs es = true := by cases a <;> simp only [okAs, Bool.and_eq_true] at ho <;> exact ho.2
      exact okAs_mem ho2 h'

/-- The (unstarred) targets of a tuple or list target, at the budget without its node. -/
theorem goodE_elt {C : List Scope} {U : Label → Prop} {tg : Expr} {l : Label} {es : List Expr}
    (htg : tg = .tuple l es ∨ tg = .list l es) (h : GoodE p C U tg) {e : Expr} (he : e ∈ es) :
    GoodE p C (Rm U l) (unstar e) := by
  have hsub : ∀ x, x ∈ labelsE (unstar e) → x ∈ labelsE e := by
    intro x hx; cases e <;> simp_all [unstar, labelsE]
  have hnd : (labelsE tg).Nodup := h.nd
  have hl : ∀ x, x ∈ labelsE e → x ∈ labelsEs es := fun x hx => labelsEs_mem he hx
  have hlt : labelsE tg = l :: labelsEs es := by rcases htg with rfl | rfl <;> rfl
  rw [hlt, List.nodup_cons] at hnd
  refine ⟨fun x hx => h.s x ?_, fun x hx => h.t x ?_, ?_, fun l' hl' => ⟨h.u l' (by rw [hlt]; exact .tail _ (hl _ (hsub _ hl'))),
    fun e' => hnd.1 (e' ▸ hl _ (hsub _ hl'))⟩, h.pv, ?_,
    fun x hx => h.tch x (by rcases htg with rfl | rfl <;> simp only [touchE] <;> exact touchEs_mem he (touch_unstar hx))⟩
  · have : x ∈ itemsE C e := by cases e <;> simp_all [unstar, itemsE]
    rcases htg with rfl | rfl <;> simp only [itemsE] <;> exact itemsEs_mem he this
  · rcases htg with rfl | rfl <;> simp only [trE, gad, cc, ccR, recR, PyCore.itemsE, r0_e, Option.isSome_none,
      Bool.false_eq_true, ite_false, List.nil_append] <;>
      exact items_fold _ _ x (.inr ⟨_, List.mem_append_left _ (mem_trA he), hx⟩)
  · have := h.ok; rcases htg with rfl | rfl <;> simp only [okE] at this <;> exact okAs_mem this he
  · have h2 := nodup_labelsEs he hnd.2
    cases e <;> simp_all [unstar, labelsE, List.nodup_cons]

section
variable {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
  {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)}

/-- PyCore evaluates the constants `ms` of a record (markers), appended to the values `done`. -/
theorem rec_consts (t : PyCore.Config σ) (f' : PyCore.Frame σ) (fs' : List (PyCore.Frame σ)) :
    ∀ (ms : List PE) (done : List Val) (K : List (PyCore.Kont σ)),
    (∀ m ∈ ms, ∃ r k, m = .const r k ∧ Py.constVal I k = .prim k) →
    ∃ ys, Path (PyCore.step I)
      { t with stack := { f' with ctrl := .val (.data "$args" done), kont := ms.map (.binL ",") ++ K } :: fs' }
      { t with stack := { f' with ctrl := .val (.data "$args" (done ++ ms.map pval)), kont := K } :: fs' } ys ∧
      ∀ y ∈ ys, ∀ x, PyCore.focus y = some x → ∃ m ∈ ms, x = m.label
  | [], done, K, _ => ⟨[], by simpa using Path.nil _, by simp⟩
  | m :: ms, done, K, h => by
    obtain ⟨r, k, rfl, hk⟩ := h m (by simp)
    obtain ⟨ys, py, hfo⟩ := rec_consts t f' fs' ms (done ++ [.prim k]) K (fun m' hm => h m' (by simp [hm]))
    let K1 : List (PyCore.Kont σ) := .binR "," (.data "$args" done) :: ms.map (.binL ",") ++ K
    let K0 : List (PyCore.Kont σ) := (PyCore.Expr.const r k :: ms).map (.binL ",") ++ K
    let c0 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" done), kont := K0 } :: fs' }
    let c1 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev (.const r k), kont := K1 } :: fs' }
    let c2 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.prim k), kont := K1 } :: fs' }
    let K3 : List (PyCore.Kont σ) := ms.map (.binL ",") ++ K
    let c3 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" (done ++ [.prim k])), kont := K3 } :: fs' }
    have e : done ++ (PyCore.Expr.const r k :: ms).map pval = done ++ [.prim k] ++ ms.map pval := by simp [pval]
    rw [e]
    refine ⟨c0 :: c1 :: c2 :: ys, .cons (a' := c1) ?_ (.cons (a' := c2) ?_ (.cons (a' := c3) ?_ ?_)), ?_⟩
    · simp [c0, c1, K0, K1, PyCore.step, PyCore.valStep, PyCore.top]
    · simp [c1, c2, K1, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, hk]
    · simp [c2, c3, K1, K3, PyCore.step, PyCore.valStep, PyCore.top]
    · exact py
    · intro y hy x hx
      simp only [List.mem_cons] at hy
      rcases hy with rfl | rfl | rfl | hy
      · simp [c0, K0, PyCore.focus] at hx
      · simp [c1, PyCore.focus, PyCore.Expr.label] at hx; exact ⟨_, List.mem_cons_self, by simp [PyCore.Expr.label, hx]⟩
      · simp [c2, PyCore.focus] at hx
      · obtain ⟨m', hm', he⟩ := hfo y hy x hx; exact ⟨m', List.mem_cons_of_mem _ hm', he⟩


theorem marks_const (ts : List Expr) : ∀ m ∈ trMarks ts, ∃ r k, m = .const r k ∧ Py.constVal I k = .prim k := by
  rw [trMarks_eq]; intro m hm
  obtain ⟨t, -, rfl⟩ := List.mem_map.1 hm
  cases t <;> first | exact ⟨_, _, rfl, kc_pos I⟩ | exact ⟨_, _, rfl, kc_star I⟩

theorem marks_star (ts : List Expr) : ((trMarks ts).map pval).mapM Py.markStar = some (ts.map isStar) := by
  rw [trMarks_eq]
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.mapM_cons, ih]
    cases t <;> simp [starMark, pval, isStar, Py.markStar]

theorem shape_eq (ts : List Expr) : Py.starShape (ts.map isStar) = splitStar ts := by
  simp only [Py.starShape, splitStar, List.findIdx?_map, List.length_map]
  rfl

theorem stars_count (ts : List Expr) : ((ts.map isStar).filter id).length = (ts.filter isStar).length := by
  simp [List.filter_map]

theorem touch_kid {tg : Expr} {v : Val} (hs : s.stack = f :: fs) (hc : f.ctrl = .store tg v) {l : Label}
    (hl : l ∈ tgtKids tg) : Touch p s l := .inr (by rw [hs]; simp only [TouchF, hc]; exact .inr hl)

/-- A store's simulation step. -/
abbrev StoreCase (I : Py.Interp σ) (p : List Stmt) (tg : Expr) : Prop :=
  ∀ {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {U : Label → Prop} {v : Val} {src : Label → PE} {rest : PS},
    At0 p H s t f fs f' fs' → WF p → f.ctrl = .store tg v →
    f'.ctrl = .exec (trT f.chain src tg (trE f.chain tg) ++ rest) → GoodE p f.chain U tg →
    SubL (PyCore.itemsB R0 (trChain f.chain) (trT f.chain src tg (trE f.chain tg))) (PI p) →
    SrcR (cx p H (rdOf t f') (ownOf t f') f) U tg.label (src tg.label) v →
    KRel (cx p H (rdOf t f') (ownOf t f') f) U false f.kont (.seq rest :: f'.kont) → Goal I p H s t

/-- `StoreCase`, both runs ending or stepping (`GoalS`). -/
abbrev StoreCaseS (I : Py.Interp σ) (p : List Stmt) (tg : Expr) : Prop :=
  ∀ {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {U : Label → Prop} {v : Val} {src : Label → PE} {rest : PS},
    At0 p H s t f fs f' fs' → WF p → f.ctrl = .store tg v →
    f'.ctrl = .exec (trT f.chain src tg (trE f.chain tg) ++ rest) → GoodE p f.chain U tg →
    SubL (PyCore.itemsB R0 (trChain f.chain) (trT f.chain src tg (trE f.chain tg))) (PI p) →
    SrcR (cx p H (rdOf t f') (ownOf t f') f) U tg.label (src tg.label) v →
    KRel (cx p H (rdOf t f') (ownOf t f') f) U false f.kont (.seq rest :: f'.kont) → GoalS I p H s t

/-- `StoreCase` with the source and the continuation related in the history that has the store
configuration's touches (the target's node and its kids, `TouchF`): for an item below that records them. -/
abbrev StoreCaseT (I : Py.Interp σ) (p : List Stmt) (tg : Expr) : Prop :=
  ∀ {H : Label → Prop} {s : Sem.Config σ} {t : PyCore.Config σ} {f : Sem.Frame σ} {fs : List (Sem.Frame σ)}
    {f' : PyCore.Frame σ} {fs' : List (PyCore.Frame σ)} {U : Label → Prop} {v : Val} {src : Label → PE} {rest : PS},
    At0 p H s t f fs f' fs' → WF p → f.ctrl = .store tg v →
    f'.ctrl = .exec (trT f.chain src tg (trE f.chain tg) ++ rest) → GoodE p f.chain U tg →
    SubL (PyCore.itemsB R0 (trChain f.chain) (trT f.chain src tg (trE f.chain tg))) (PI p) →
    SrcR (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U tg.label (src tg.label) v →
    KRel (cx p (Seen (Touch p) H [s]) (rdOf t f') (ownOf t f') f) U false f.kont (.seq rest :: f'.kont) →
    Goal I p H s t

/-- What CPython's parser rejects as a target: Surf is stuck at the store, PyCore at `$stuck`, with the same
outcome. -/
theorem store_stuck (A : At0 p H s t f fs f' fs') {tg : Expr} {v : Val} {rest : PS}
    (hc : f.ctrl = .store tg v) (hc' : f'.ctrl = .exec (stuckAt (sub tg.label 55) :: rest))
    (e0 : Sem.step I s = none) : GoalS I p H s t := by
  let r := sub tg.label 55
  let K : List (PyCore.Kont σ) := .exprS :: .seq rest :: f'.kont
  let mk : PyCore.Ctrl σ → List (PyCore.Kont σ) → PyCore.Config σ :=
    fun c k => { t with stack := { f' with ctrl := c, kont := k } :: fs' }
  let t1 := mk (.ev (.call r (.const r "$stuck") (.const r "$args"))) K
  let t2 := mk (.ev (.const r "$stuck")) (.callF (.const r "$args") :: K)
  let t3 := mk (.val (.prim "$stuck")) (.callF (.const r "$args") :: K)
  let t4 := mk (.ev (.const r "$args")) (.callA (.prim "$stuck") :: K)
  let t5 := mk (.val (.data "$args" [])) (.callA (.prim "$stuck") :: K)
  have s1 : PyCore.step I t = some t1 := by rw [pstep_exec A.ht hc']; rfl
  have s2 : PyCore.step I t1 = some t2 := by simp [t1, t2, mk, PyCore.step, PyCore.evalStep, PyCore.top]
  have s3 : PyCore.step I t2 = some t3 := by
    simp [t2, t3, mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, kc_stuck]
  have s4 : PyCore.step I t3 = some t4 := by simp [t3, t4, mk, PyCore.step, PyCore.valStep, PyCore.top]
  have s5 : PyCore.step I t4 = some t5 := by
    simp [t4, t5, mk, PyCore.step, PyCore.evalStep, PyCore.top, PyCore.constK, constVal_args]
  have s6 : PyCore.step I t5 = none := by
    simp [t5, mk, PyCore.step, PyCore.valStep, PyCore.callStep, gad_stuck', PyCore.gadgetStep]
  refine .inl ⟨s, t5, [], [t, t1, t2, t3, t4], .nil _, e0,
    .cons s1 (.cons s2 (.cons s3 (.cons s4 (.cons s5 (.nil _))))), s6, ?_, ?_⟩
  · simp [Fin, Sem.outcome, PyCore.outcome, A.hs, t5, mk, OCorr, A.out, A.st]
  · refine cover_of (l := tg.label) (by simp) (touch_store A.hs hc) ?_
    intro y hy x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [t5, mk, PyCore.focus] at hx
    · simp [PyCore.focus, A.ht, hc', stuckAt, PyCore.Stmt.label] at hx; rw [← hx]; exact sub_div _ _ (by omega)
    all_goals simp [t1, t2, t3, t4, mk, r, PyCore.focus, PyCore.Expr.label] at hx
    all_goals (rw [← hx]; exact sub_div _ _ (by omega))


/-- A tuple or list target (node `lt`, targets `ts`): PyCore runs its block up to the unpacking Surf
starts with (or both are stuck, for two starred targets). -/
theorem unpack_core (A : At0 p H s t f fs f' fs') {lt : Label} {ts : List Expr} {tg : Expr} {v : Val}
    {src : Label → PE} {rest : PS} {U : Label → Prop}
    (hc : f.ctrl = .store tg v) (htl : tg.label = lt) (hkids : tgtKids tg = ts.map Sem.Expr.lbl)
    (hst : Sem.step I s = if (ts.filter isStar).length > 1 then none else
      some { s with stack := { f with ctrl := .op (.unpack (splitStar ts).1 (splitStar ts).2.1 (splitStar ts).2.2) [v], kont := .stUnpack (ts.map unstar) :: f.kont } :: fs })
    (hc' : f'.ctrl = .exec (blk lt (.assign (sub lt 1) (fresh "u" lt) (gad lt 2 .unpack (src lt :: trMarks ts)) :: trItems f.chain lt 0 ts) :: rest))
    (hU : U lt) (hf : FOk f.chain (fresh "u" lt)) (hts : GoodEs p f.chain (Rm U lt) (ts.map unstar))
    (hI : SubL (PyCore.itemsB R0 (trChain f.chain) (trItems f.chain lt 0 ts)) (PI p))
    (hs : SrcR (cx p H (rdOf t f') (ownOf t f') f) U lt (src lt) v)
    (hk : KRel (cx p H (rdOf t f') (ownOf t f') f) U false f.kont (.seq rest :: f'.kont)) : GoalS I p H s t := by
  let K2 : List (PyCore.Kont σ) := .assign (fresh "u" lt) :: .seq (trItems f.chain lt 0 ts) :: .tryE [] [] :: .seq rest :: f'.kont
  let KR : List (PyCore.Kont σ) := recK [] (trMarks ts) (.callA (.prim Gadget.unpack.name) :: K2)
  let K6 : List (PyCore.Kont σ) := .callA (.prim Gadget.unpack.name) :: K2
  let K5 : List (PyCore.Kont σ) := (trMarks ts).map (.binL ",") ++ K6
  let K1 : List (PyCore.Kont σ) := .tryE [] [] :: .seq rest :: f'.kont
  let SS : PS := .assign (sub lt 1) (fresh "u" lt) (gad lt 2 .unpack (src lt :: trMarks ts)) :: trItems f.chain lt 0 ts
  let E : PE := gad lt 2 .unpack (src lt :: trMarks ts)
  let t1 : PyCore.Config σ := { t with stack := { f' with ctrl := .exec SS, kont := K1 } :: fs' }
  let t2 : PyCore.Config σ := { t with stack := { f' with ctrl := .ev E, kont := K2 } :: fs' }
  let t4 : PyCore.Config σ := { t with stack := { f' with ctrl := .val v, kont := KR } :: fs' }
  let t5 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" [v]), kont := K5 } :: fs' }
  let t6 : PyCore.Config σ := { t with stack := { f' with ctrl := .val (.data "$args" ([v] ++ (trMarks ts).map pval)), kont := K6 } :: fs' }
  have st1 : PyCore.step I t = some t1 := by rw [pstep_exec A.ht hc']; rfl
  have st2 : PyCore.step I t1 = some t2 := by simp [t1, t2, SS, E, K1, K2, PyCore.step, PyCore.execStep, PyCore.top]
  obtain ⟨ys3, p3, -, hf3⟩ := cc_enter (I := I) t f' fs' (sub lt 2) Gadget.unpack.name (src lt) (trMarks ts) K2
  rw [kc_gad I .unpack trivial] at p3
  obtain ⟨ys4, p4, -, hf4⟩ := srcR_eval (I := I) (t := t) (f' := f') (fs' := fs') rfl hs KR
  have st5 : PyCore.step I t4 = some t5 := by simp [t4, t5, KR, K5, K6, recK, PyCore.step, PyCore.valStep, PyCore.top]
  obtain ⟨ys6, p6, hf6⟩ := rec_consts (I := I) t f' fs' (trMarks ts) [v] K6 (marks_const ts)
  have hlen : ((trMarks ts).map pval).length = ts.length := by simp [trMarks_eq]
  have st7 : PyCore.step I t6 = if (ts.filter isStar).length > 1 then none else
      some { t with stack := { f' with ctrl := .op (.unpack (splitStar ts).1 (splitStar ts).2.1 (splitStar ts).2.2) [v], kont := .unpackK ts.length :: K2 } :: fs' } := by
    simp only [t6, K6, PyCore.step, PyCore.valStep, PyCore.callStep, gad_name .unpack trivial, PyCore.gadgetStep,
      PyCore.argList, List.singleton_append, marks_star, stars_count, shape_eq, hlen]
    split <;> rfl
  have pth0 : Path (PyCore.step I) t t6 (t :: t1 :: (ys3 ++ (ys4 ++ t4 :: ys6))) :=
    Path.cons st1 (.cons st2 (p3.append (p4.append (.cons st5 p6))))
  have pth : Path (PyCore.step I) t t6 ([t, t1] ++ ys3 ++ ys4 ++ [t4] ++ ys6) := by
    have e : [t, t1] ++ ys3 ++ ys4 ++ [t4] ++ ys6 = t :: t1 :: (ys3 ++ (ys4 ++ t4 :: ys6)) := by simp
    rw [e]; exact pth0
  have hT : Touch p s lt := htl ▸ touch_store A.hs hc
  have cov : ∀ y ∈ [t, t1] ++ ys3 ++ ys4 ++ [t4] ++ ys6, ∀ x, PyCore.focus y = some x → Touch p s (x / 64) := by
    intro y hy x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with ((((rfl | rfl) | hy) | hy) | rfl) | hy
    · simp [PyCore.focus, A.ht, hc', blk, PyCore.Stmt.label] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hT
    · simp [t1, SS, PyCore.focus, PyCore.Stmt.label] at hx; rw [← hx, sub_div _ _ (by omega)]; exact hT
    · rw [hf3 y hy x hx, sub_div _ _ (by omega)]; exact hT
    · rw [hf4 y hy x hx]; exact hT
    · simp [t4, PyCore.focus] at hx
    · obtain ⟨m, hm, rfl⟩ := hf6 y hy x hx
      rw [trMarks_eq] at hm
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hm
      have hl : PyCore.Expr.label (starMark u) / 64 = Sem.Expr.lbl u := by
        cases u <;> simp [starMark, PyCore.Expr.label, Sem.Expr.lbl, sub_div, lbl_eq, Expr.label]
      rw [hl]; exact touch_kid A.hs hc (by rw [hkids]; exact List.mem_map.2 ⟨u, hu, rfl⟩)
  by_cases hm : (ts.filter isStar).length > 1
  · rw [if_pos hm] at hst st7
    refine .inl ⟨s, t6, [], _, .nil _, hst, pth, st7, ?_, ?_⟩
    · simp [Fin, Sem.outcome, PyCore.outcome, A.hs, t6, OCorr, A.out, A.st]
    · intro y hy x hx
      have hx := pfocus_le hx
      rcases List.mem_cons.1 hy with rfl | hy
      · simp [t6, K6, PyCore.focus] at hx
      · exact .inr ⟨s, by simp, cov y hy x hx⟩
  · rw [if_neg hm] at hst st7
    have hH : ∀ l, H l → Seen (Touch p) H [s] l := fun _ h => .inl h
    refine goalS_b (.cons hst (.nil _)) (by simp) (pth.append (.cons st7 (.nil _))) (by simp)
      (.inl (((A.upd _ _ _ _).mono_H hH).crel (U := U) (i := true) .op
        (.asg (.stUnpack (lt := lt) (seen_s (by simp) hT) hU hf hts hI (KRel.ext ⟨hH, Agree.refl _ _ _⟩ hk))))) ?_
    intro y hy x hx
    have hx := pfocus_le hx
    rcases List.mem_append.1 hy with hy | hy
    · exact .inr ⟨s, by simp, cov y hy x hx⟩
    · simp at hy; subst hy; simp [t6, K6, PyCore.focus] at hx

/-- A tuple or list target. -/
theorem store_unpack (tg : Expr) (h : (∃ lt ts, tg = .tuple lt ts) ∨ (∃ lt ts, tg = .list lt ts)) :
    StoreCaseS I p tg := by
  intro H s t f fs f' fs' U v src rest A W hc hc' hg hT hs hk
  have hts : ∀ {lt ts}, (tg = .tuple lt ts ∨ tg = .list lt ts) → GoodEs p f.chain (Rm U lt) (ts.map unstar) := by
    intro lt ts htg e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
    exact goodE_elt htg hg he0
  have hfo : ∀ {lt}, PyCore.Item.occ (sub lt 1) (fresh "u" lt) (trChain f.chain) ∈
      PyCore.itemsB R0 (trChain f.chain) (trT f.chain src tg (trE f.chain tg)) → FOk f.chain (fresh "u" lt) :=
    fun hi => fok_of W (hT _ hi) ⟨"u", _, rfl⟩ (not_cmp _ 1 (by omega) (by omega) (by omega))
  rcases h with ⟨lt, ts, rfl⟩ | ⟨lt, ts, rfl⟩
  · exact unpack_core (lt := lt) A hc rfl rfl (by simp [Sem.step, A.hs, hc, Sem.storeStep, Sem.doOp, Sem.setC])
      (by rw [hc']; rfl) (hg.u lt (by simp [labelsE]))
      (hfo (lt := lt) (by simp [trT, blk, PyCore.itemsB, PyCore.itemsS, r0_s]))
      (hts (.inl rfl)) (fun x hx => hT x (by simp [trT, blk, PyCore.itemsB, PyCore.itemsS, hx])) hs hk
  · exact unpack_core (lt := lt) A hc rfl rfl (by simp [Sem.step, A.hs, hc, Sem.storeStep, Sem.doOp, Sem.setC])
      (by rw [hc']; rfl) (hg.u lt (by simp [labelsE]))
      (hfo (lt := lt) (by simp [trT, blk, PyCore.itemsB, PyCore.itemsS, r0_s]))
      (hts (.inr rfl)) (fun x hx => hT x (by simp [trT, blk, PyCore.itemsB, PyCore.itemsS, hx])) hs hk

theorem store_simS (tg : Expr) : StoreCaseS I p tg := by
  intro H s t f fs f' fs' U v src rest A W hc hc' hg hT hs hk
  cases tg with
  | name lt y =>
    exact store_name A hc hc' (W.nodot lt _ f.chain (hg.s _ (by simp [itemsE]))) hs hk
  | attr lt o a =>
    have ha : okName a = true := by have := hg.ok; simp only [okE, Bool.and_eq_true] at this; exact this.1
    exact store_attr A hc hc' hg hs hk (kc_setattr I (nc_mangle_pv hg.pv (nc_ok ha)))
  | sub lt o i => exact store_sub A hc hc' hg hs hk (kc_setitem I)
  | tuple lt ts => exact store_unpack _ (.inl ⟨_, _, rfl⟩) A W hc hc' hg hT hs hk
  | list lt ts => exact store_unpack _ (.inr ⟨_, _, rfl⟩) A W hc hc' hg hT hs hk
  | star ls e => exact store_stuck A hc (by rw [hc']; rfl) (by simp [Sem.step, A.hs, hc, Sem.storeStep])
  | _ => exact store_stuck A hc (by rw [hc']; rfl) (by simp [Sem.step, A.hs, hc, Sem.storeStep])

theorem store_sim (tg : Expr) : StoreCase I p tg := fun A W hc hc' hg hT hs hk =>
  (store_simS tg A W hc hc' hg hT hs hk).goal

theorem store_simT (tg : Expr) : StoreCaseT I p tg := fun A W hc hc' hg hT hs hk =>
  (store_simS tg (A.mono_H fun _ => seen_of) W hc hc' hg hT hs hk).unseen.goal

end
end Surf.T2
