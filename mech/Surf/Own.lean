/-
The facts of the translation about fresh names, for `fresh_canon` (`Canon.lean`). Each node of `p`
has an entry `(l, co, ci)`: its label, the chain it is in, and the chain of the scope it
introduces (`ci = co` unless it is a `def`, a lambda or a comprehension). The entries'
labels are the labels of `p` (`ncB_fst`), so with distinct labels a label has one entry. A
fresh name `.tag l` lives in the chain `home tag co ci` of the entry of `l`: the parameter
`.a` of a function, the iterator `.i` and the accumulator `.acc` of a comprehension in the
chain of the scope, every other fresh name in the chain of the node. Every fact of the
translation in a chain `C` about a fresh name is a binding in its home `C` (`trB_fc`).
-/
import Surf.Fresh

namespace Surf
open PyCore (Name Label Fact)

set_option linter.unusedSimpArgs false

/-- Entries of nodes: label, chain, chain of the scope it introduces. -/
abbrev NC := List (Label × List Scope × List Scope)

mutual
def ncE (C : List Scope) : Expr → NC
  | .const l _ | .name l _ => [(l, C, C)]
  | .bin l _ a b | .sub l a b => (l, C, C) :: ncE C a ++ ncE C b
  | .unary l _ a | .attr l a _ | .star l a | .walrus l _ a | .yieldFrom l a => (l, C, C) :: ncE C a
  | .boolop l _ es | .list l es | .tuple l es | .set l es | .fstr l es => (l, C, C) :: ncEs C es
  | .compare l a _ es => (l, C, C) :: ncE C a ++ ncEs C es
  | .ifexp l c a b => (l, C, C) :: ncE C c ++ ncE C a ++ ncE C b
  | .call l f as ks => (l, C, C) :: ncE C f ++ ncEs C as ++ ncKs C ks
  | .slice l a b c => (l, C, C) :: ncO C a ++ ncO C b ++ ncO C c
  | .dict l kvs => (l, C, C) :: ncDs C kvs
  | .lam l ps b => (l, C, .lam l ps b :: C) :: ncPs C (.lam l ps b :: C) ps ++ ncE (.lam l ps b :: C) b
  | .comp l k es gs => (l, C, .comp l k es gs :: C) :: ncEs (.comp l k es gs :: C) es ++
      ncGs C (.comp l k es gs :: C) true gs
  | .yield l e => (l, C, C) :: ncO C e
  | .fmt l e _ s => (l, C, C) :: ncE C e ++ ncO C s
def ncO (C : List Scope) : Option Expr → NC
  | none => []
  | some e => ncE C e
def ncEs (C : List Scope) : List Expr → NC
  | [] => []
  | e :: es => ncE C e ++ ncEs C es
def ncKs (C : List Scope) : List Kw → NC
  | [] => []
  | .mk l _ e :: ks => (l, C, C) :: ncE C e ++ ncKs C ks
def ncDs (C : List Scope) : List DItem → NC
  | [] => []
  | .mk k v :: kvs => ncO C k ++ ncE C v ++ ncDs C kvs
def ncPs (C Ci : List Scope) : List Param → NC
  | [] => []
  | .mk l _ _ d a :: ps => (l, Ci, Ci) :: ncO C d ++ ncO C a ++ ncPs C Ci ps
def ncGs (C Ci : List Scope) (first : Bool) : List Gen → NC
  | [] => []
  | .mk l t i ifs :: gs => (l, Ci, Ci) :: ncE Ci t ++ ncE (if first then C else Ci) i ++
      ncEs Ci ifs ++ ncGs C Ci false gs
end

mutual
def ncS (C : List Scope) : Stmt → NC
  | .expr l e => (l, C, C) :: ncE C e
  | .assign l ts e => (l, C, C) :: ncEs C ts ++ ncE C e
  | .augassign l t _ e => (l, C, C) :: ncE C t ++ ncE C e
  | .annassign l t a v => (l, C, C) :: ncE C t ++ ncE C a ++ ncO C v
  | .del l ts => (l, C, C) :: ncEs C ts
  | .ite l c t u | .while l c t u => (l, C, C) :: ncE C c ++ ncB C t ++ ncB C u
  | .for l t it b u => (l, C, C) :: ncE C t ++ ncE C it ++ ncB C b ++ ncB C u
  | .brk l | .cont l | .pass l | .glob l _ | .nonloc l _ => [(l, C, C)]
  | .ret l e => (l, C, C) :: ncO C e
  | .defn l f ps b ds r => (l, C, .fn l f ps b :: C) :: ncPs C (.fn l f ps b :: C) ps ++
      ncB (.fn l f ps b :: C) b ++ ncEs C ds ++ ncO C r
  | .cls l x bs ks b ds => (l, C, C) :: ncEs C bs ++ ncKs C ks ++ ncB (.cl l x b :: C) b ++ ncEs C ds
  | .tryE l b hs u => (l, C, C) :: ncB C b ++ ncHs C hs ++ ncB C u
  | .raise l e c => (l, C, C) :: ncO C e ++ ncO C c
  | .imp l al | .impFrom l _ al _ => (l, C, C) :: al.map fun a => (a.l, C, C)
  | .assert l t m => (l, C, C) :: ncE C t ++ ncO C m
def ncHs (C : List Scope) : List Handler → NC
  | [] => []
  | .mk l ty _ b :: hs => (l, C, C) :: ncO C ty ++ ncB C b ++ ncHs C hs
def ncB (C : List Scope) : List Stmt → NC
  | [] => []
  | s :: ss => ncS C s ++ ncB C ss
end

/-! ## The entries' labels are the labels (the count lemma) -/

mutual
theorem ncE_fst (C : List Scope) : ∀ e, (ncE C e).map Prod.fst = labelsE e
  | .const .. | .name .. => rfl
  | .bin _ _ a b | .sub _ a b => by simp [ncE, labelsE, ncE_fst C a, ncE_fst C b]
  | .unary _ _ a | .attr _ a _ | .star _ a | .walrus _ _ a | .yieldFrom _ a => by
    simp [ncE, labelsE, ncE_fst C a]
  | .boolop _ _ es | .list _ es | .tuple _ es | .set _ es | .fstr _ es => by
    simp [ncE, labelsE, ncEs_fst C es]
  | .compare _ a _ es => by simp [ncE, labelsE, ncE_fst C a, ncEs_fst C es]
  | .ifexp _ c a b => by simp [ncE, labelsE, ncE_fst C a, ncE_fst C b, ncE_fst C c]
  | .call _ f as ks => by simp [ncE, labelsE, ncE_fst C f, ncEs_fst C as, ncKs_fst C ks]
  | .slice _ a b c => by simp [ncE, labelsE, ncO_fst C a, ncO_fst C b, ncO_fst C c]
  | .dict _ kvs => by simp [ncE, labelsE, ncDs_fst C kvs]
  | .lam l ps b => by simp [ncE, labelsE, ncPs_fst C _ ps, ncE_fst _ b]
  | .comp l k es gs => by simp [ncE, labelsE, ncEs_fst _ es, ncGs_fst C _ true gs]
  | .yield _ e => by simp [ncE, labelsE, ncO_fst C e]
  | .fmt _ e _ s => by simp [ncE, labelsE, ncE_fst C e, ncO_fst C s]
theorem ncO_fst (C : List Scope) : ∀ o, (ncO C o).map Prod.fst = labelsO o
  | none => rfl
  | some e => by simp [ncO, labelsO, ncE_fst C e]
theorem ncEs_fst (C : List Scope) : ∀ es, (ncEs C es).map Prod.fst = labelsEs es
  | [] => rfl
  | e :: es => by simp [ncEs, labelsEs, ncE_fst C e, ncEs_fst C es]
theorem ncKs_fst (C : List Scope) : ∀ ks, (ncKs C ks).map Prod.fst = labelsKs ks
  | [] => rfl
  | .mk _ _ e :: ks => by simp [ncKs, labelsKs, ncE_fst C e, ncKs_fst C ks]
theorem ncDs_fst (C : List Scope) : ∀ kvs, (ncDs C kvs).map Prod.fst = labelsDs kvs
  | [] => rfl
  | .mk k v :: kvs => by simp [ncDs, labelsDs, ncO_fst C k, ncE_fst C v, ncDs_fst C kvs]
theorem ncPs_fst (C Ci : List Scope) : ∀ ps, (ncPs C Ci ps).map Prod.fst = labelsPs ps
  | [] => rfl
  | .mk _ _ _ d a :: ps => by simp [ncPs, labelsPs, ncO_fst C d, ncO_fst C a, ncPs_fst C Ci ps]
theorem ncGs_fst (C Ci : List Scope) : ∀ first gs, (ncGs C Ci first gs).map Prod.fst = labelsGs gs
  | _, [] => rfl
  | first, .mk _ t i ifs :: gs => by
    simp [ncGs, labelsGs, ncE_fst Ci t, ncE_fst (if first then C else Ci) i, ncEs_fst Ci ifs,
      ncGs_fst C Ci false gs]
end

mutual
theorem ncS_fst (C : List Scope) : ∀ s, (ncS C s).map Prod.fst = labelsS s
  | .expr _ e => by simp [ncS, labelsS, ncE_fst C e]
  | .assign _ ts e => by simp [ncS, labelsS, ncE_fst C e, ncEs_fst C ts]
  | .augassign _ t _ e => by simp [ncS, labelsS, ncE_fst C e, ncE_fst C t]
  | .annassign _ t a v => by simp [ncS, labelsS, ncE_fst C t, ncE_fst C a, ncO_fst C v]
  | .del _ ts => by simp [ncS, labelsS, ncEs_fst C ts]
  | .ite _ c t u | .while _ c t u => by simp [ncS, labelsS, ncE_fst C c, ncB_fst C t, ncB_fst C u]
  | .for _ t it b u => by simp [ncS, labelsS, ncE_fst C t, ncE_fst C it, ncB_fst C b, ncB_fst C u]
  | .brk _ | .cont _ | .pass _ | .glob .. | .nonloc .. => rfl
  | .ret _ e => by simp [ncS, labelsS, ncO_fst C e]
  | .defn _ _ ps b ds r => by
    simp [ncS, labelsS, ncPs_fst C _ ps, ncB_fst _ b, ncEs_fst C ds, ncO_fst C r]
  | .cls _ _ bs ks b ds => by simp [ncS, labelsS, ncEs_fst C bs, ncKs_fst C ks, ncB_fst _ b, ncEs_fst C ds]
  | .tryE _ b hs u => by simp [ncS, labelsS, ncB_fst C b, ncHs_fst C hs, ncB_fst C u]
  | .raise _ e c => by simp [ncS, labelsS, ncO_fst C e, ncO_fst C c]
  | .imp _ al | .impFrom _ _ al _ => by simp [ncS, labelsS]
  | .assert _ t m => by simp [ncS, labelsS, ncE_fst C t, ncO_fst C m]
theorem ncHs_fst (C : List Scope) : ∀ hs, (ncHs C hs).map Prod.fst = labelsHs hs
  | [] => rfl
  | .mk _ ty _ b :: hs => by simp [ncHs, labelsHs, ncO_fst C ty, ncB_fst C b, ncHs_fst C hs]
theorem ncB_fst (C : List Scope) : ∀ ss, (ncB C ss).map Prod.fst = labelsB ss
  | [] => rfl
  | s :: ss => by simp [ncB, labelsB, ncS_fst C s, ncB_fst C ss]
end

/-- Every expression's own entry is in the chain around it, and no class statement. -/
theorem root_ncE (C : List Scope) (e : Expr) : ∃ ci, (e.label, C, ci) ∈ ncE C e := by
  cases e <;> simp [ncE, Expr.label]

theorem root_ncEs (C : List Scope) : ∀ es : List Expr, ∀ e ∈ es, ∃ ci, (e.label, C, ci) ∈ ncEs C es
  | [], _, h => by simp at h
  | e :: es, e', h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · obtain ⟨ci, h⟩ := root_ncE C e'; exact ⟨ci, by simp [ncEs, h]⟩
    · obtain ⟨ci, h⟩ := root_ncEs C es e' h; exact ⟨ci, by simp [ncEs, h]⟩


/-! ## What the facts say about fresh names -/

/-- The chain a fresh name `.tag l` lives in, from the entry `(l, co, ci)`. -/
def home (t : String) (co ci : List Scope) : List Scope := if t = "a" ∨ t = "i" ∨ t = "acc" then ci else co

/-- A tag with no digit (all the translation's): fresh names determine tag and label. -/
def NoDig (t : String) : Prop := ∀ c ∈ t.toList, c.isDigit = false

/-- A fact of the translation in the chain `C` about a name: the name is one of `p` (an
occurrence in `B`), or a fresh name bound in its home `C`. -/
def FF (N : NC) (B : List Item) (C : List Scope) : Fact → Prop
  | .bind x => (∃ l C1, Item.occ l x C1 ∈ B) ∨ ∃ t l0 co ci, x = fresh t l0 ∧ NoDig t ∧
      (l0, co, ci) ∈ N ∧ C = home t co ci
  | .wal x | .glob x | .nonloc x => ∃ l C1, Item.occ l x C1 ∈ B
  | .yld => True

def Fc (N : NC) (B : List Item) (C : List Scope) (A : List Fact) : Prop := ∀ f ∈ A, FF N B C f

theorem FF.mono {N N' : NC} {B B' : List Item} {C : List Scope} {f : Fact} (h : FF N B C f)
    (hN : ∀ a ∈ N, a ∈ N') (hB : ∀ j ∈ B, j ∈ B') : FF N' B' C f := by
  cases f with
  | bind x =>
    rcases h with ⟨l, C1, h⟩ | ⟨t, l0, co, ci, h1, h2, h3, h4⟩
    · exact .inl ⟨l, C1, hB _ h⟩
    · exact .inr ⟨t, l0, co, ci, h1, h2, hN _ h3, h4⟩
  | wal x | glob x | nonloc x => obtain ⟨l, C1, h⟩ := h; exact ⟨l, C1, hB _ h⟩
  | yld => trivial

theorem Fc.cat {N1 N2 : NC} {B1 B2 : List Item} {C : List Scope} {A1 A2 : List Fact}
    (h1 : Fc N1 B1 C A1) (h2 : Fc N2 B2 C A2) : Fc (N1 ++ N2) (B1 ++ B2) C (A1 ++ A2) := by
  intro f hf
  rcases List.mem_append.1 hf with h | h
  · exact (h1 f h).mono (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
  · exact (h2 f h).mono (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)

theorem Fc.congr {N N' : NC} {B B' : List Item} {C : List Scope} {A A' : List Fact} (h : Fc N B C A)
    (hA : ∀ f ∈ A', f ∈ A) (hN : ∀ a ∈ N, a ∈ N') (hB : ∀ j ∈ B, j ∈ B') : Fc N' B' C A' :=
  fun f hf => (h f (hA f hf)).mono hN hB

theorem Fc.nil {C : List Scope} : Fc [] [] C [] := by simp [Fc]

/-- A name of `p`. -/
theorem Fc.usr (l : Label) (x : Name) (C1 C : List Scope) :
    Fc [] [.occ l x C1] C [.bind x, .wal x, .glob x, .nonloc x] := by
  intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;> simp [FF]

/-- A fresh name bound in its home. -/
theorem Fc.fr (t : String) (l : Label) (co ci C : List Scope) (ht : NoDig t)
    (hh : C = home t co ci) : Fc [(l, co, ci)] [] C [.bind (fresh t l)] := by
  intro f hf; simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf
  exact .inr ⟨t, l, co, ci, rfl, ht, by simp, hh⟩

theorem Fc.yld {N B C} : Fc N B C [.yld] := by intro f hf; simp at hf; subst hf; trivial

/-- A comprehension passes the walrus targets of its body to the scope around it. -/
theorem Fc.comp {N : NC} {B : List Item} {C : List Scope} {S : Scope} {A : List Fact}
    (h : Fc N B (S :: C) A) : Fc N B C (A.filter Fact.isWal) := by
  intro f hf
  simp only [List.mem_filter] at hf
  obtain ⟨hf, hw⟩ := hf
  have := h f hf
  cases f with
  | wal x => exact this
  | _ => simp [Fact.isWal] at hw

theorem home_co (t : String) (C : List Scope) : C = home t C C := by simp [home]

/-- `Fc.fr` for a node whose entry is `(l, C, C)`. -/
theorem Fc.frc (t : String) (l : Label) (C : List Scope) (ht : NoDig t := by decide) :
    Fc [(l, C, C)] [] C [.bind (fresh t l)] :=
  Fc.fr t l C C C ht (home_co t C)

instance (t : String) : Decidable (NoDig t) := inferInstanceAs (Decidable (∀ c ∈ t.toList, _))

/-- `fccat p₁ … pₙ` appends the `Fc` facts `pᵢ`. -/
syntax "fccat" (ppSpace colGt term:max)+ : term
macro_rules
  | `(fccat $p) => `($p)
  | `(fccat $p $ps*) => `(Fc.cat $p (fccat $ps*))

/-- The simplification of entries and of Surf items. -/
macro "nc_simp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [ncE, ncO, ncEs,
    ncKs, ncDs, ncPs, ncGs, ncS, ncHs, ncB, itemsE, itemsO, itemsEs, itemsKs, itemsDs, itemsPs,
    itemsG1, itemsGs, itemsS, itemsHs, itemsB, paramOccs, List.mem_append, List.mem_cons,
    List.not_mem_nil, List.append_nil, List.nil_append, or_false, false_or, ite_true, ite_false,
    List.mem_map, Option.toList, Option.map, PyCore.classImplicit, List.map_cons, List.map_nil] $[$loc]?)

/-- Close an `Fc` goal from `Fc` facts about its parts. -/
macro "fc" ps:(ppSpace colGt term:max)+ : tactic => `(tactic|
  exact Fc.congr (fccat $ps*) (by intro f hf; (try tr_simp at hf ⊢); all_goals grind)
    (by intro a ha; (try nc_simp at ha ⊢); all_goals grind)
    (by intro j hj; (try nc_simp at hj ⊢); all_goals grind))


/-! ## The facts of the translation -/

mutual
theorem trE_fc (C : List Scope) : ∀ e, Fc (ncE C e) (itemsE C e) C (PyCore.factsE (trE C e))
  | .const l c => by fc Fc.nil
  | .name l x => by fc Fc.nil
  | .bin l op a b => by have h1 := trE_fc C a; have h2 := trE_fc C b; fc h1 h2
  | .unary l op a => by have h1 := trE_fc C a; fc h1
  | .boolop l op es => by have h1 := trEs_fc C es; fc h1
  | .compare l a ops es => by
    have h1 := trE_fc C a; have h2 := trLs_fc C es
    simp only [trE, pfactsE_cmpChain, pfactsE_cmpOps]; fc h1 h2
  | .ifexp l c a b => by
    have h1 := trE_fc C c; have h2 := trE_fc C a; have h3 := trE_fc C b; fc h1 h2 h3
  | .call l f args kws => by
    have h1 := trE_fc C f; have h2 := trA_fc C args; have h3 := trKs_fc C kws; fc h1 h2 h3
  | .attr l e a => by have h1 := trE_fc C e; fc h1
  | .sub l e i => by have h1 := trE_fc C e; have h2 := trE_fc C i; fc h1 h2
  | .slice l a b c => by
    have h1 := trO_fc C l 1 a; have h2 := trO_fc C l 2 b; have h3 := trO_fc C l 3 c; fc h1 h2 h3
  | .star l e => by have h1 := trE_fc C e; fc h1
  | .list l es => by have h1 := trA_fc C es; fc h1
  | .tuple l es => by have h1 := trA_fc C es; fc h1
  | .set l es => by have h1 := trA_fc C es; fc h1
  | .dict l kvs => by have h1 := trKVs_fc C kvs; fc h1
  | .lam l ps b => by
    have h1 := trDfs_fc C (.lam l ps b :: C) ps; have h2 := trAnns_fc C (.lam l ps b :: C) ps; fc h1 h2
  | .comp l k es gs => by
    have h1 := trG1_fc C (.comp l k es gs :: C) gs
    have h2 := trEs_fc (.comp l k es gs :: C) es
    have h3 : Fc (ncEs (.comp l k es gs :: C) es) (itemsEs (.comp l k es gs :: C) es) (.comp l k es gs :: C)
        (PyCore.factsB (compElt l k (trEs (.comp l k es gs :: C) es))) := by
      intro f hf
      by_cases hy : f = .yld
      · subst hy; trivial
      · exact h2 f ((pfactsB_compElt l k _ f hy).1 hf)
    have h4 := trGs_fc (.comp l k es gs :: C) (fresh "i" l) C true gs _ _ _ h3
    have h5 : Fc ((l, C, .comp l k es gs :: C) :: (ncGs C (.comp l k es gs :: C) true gs ++
          ncEs (.comp l k es gs :: C) es))
        (itemsGs (.comp l k es gs :: C) true gs ++ itemsEs (.comp l k es gs :: C) es) (.comp l k es gs :: C)
        (PyCore.factsB (compWrap l k (trGs (.comp l k es gs :: C) (fresh "i" l) true gs
          (compElt l k (trEs (.comp l k es gs :: C) es))))) := by
      have ha := Fc.fr "acc" l C (.comp l k es gs :: C) (.comp l k es gs :: C) (by decide) (by simp [home])
      unfold compWrap; split
      · exact Fc.congr h4 (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h) (fun _ h => h)
      · fc h4 ha
    have h6 := Fc.comp h5
    simp only [trE]
    split <;> fc h1 h6
  | .walrus l x e => by have h1 := trE_fc C e; fc h1 (Fc.usr l (mangle (priv C) x) C C)
  | .yield l e => by have h1 := trO_fc C l 1 e; fc h1 (Fc.yld (N := []) (B := []) (C := C))
  | .yieldFrom l e => by have h1 := trE_fc C e; fc h1 (Fc.yld (N := []) (B := []) (C := C))
  | .fstr l es => by have h1 := trEs_fc C es; fc h1
  | .fmt l e cv sp => by
    have h1 := trE_fc C e
    cases sp with
    | none => simp only [trE]; split <;> fc h1
    | some s => have h2 := trE_fc C s; simp only [trE]; split <;> fc h1 h2
theorem trO_fc (C : List Scope) (l : Label) (k : Nat) : ∀ o,
    Fc (ncO C o) (itemsO C o) C (PyCore.factsE (trO C l k o))
  | none => by fc Fc.nil
  | some e => by have h1 := trE_fc C e; fc h1
theorem trEs_fc (C : List Scope) : ∀ es, Fc (ncEs C es) (itemsEs C es) C ((trEs C es).flatMap PyCore.factsE)
  | [] => by fc Fc.nil
  | e :: es => by have h1 := trE_fc C e; have h2 := trEs_fc C es; fc h1 h2
theorem trA_fc (C : List Scope) : ∀ es, Fc (ncEs C es) (itemsEs C es) C ((trA C es).flatMap PyCore.factsE)
  | [] => by fc Fc.nil
  | e :: es => by
    have h1 := trE_fc C e; have h2 := trA_fc C es
    rw [trA_cons, List.flatMap_cons, pfactsE_unstar]; fc h1 h2
theorem trKs_fc (C : List Scope) : ∀ ks, Fc (ncKs C ks) (itemsKs C ks) C ((trKs C ks).flatMap PyCore.factsE)
  | [] => by fc Fc.nil
  | .mk l x e :: ks => by have h1 := trE_fc C e; have h2 := trKs_fc C ks; fc h1 h2
theorem trLs_fc (C : List Scope) : ∀ es,
    Fc (ncEs C es) (itemsEs C es) C ((trLs C es).flatMap fun x => PyCore.factsE x.2)
  | [] => by fc Fc.nil
  | e :: es => by have h1 := trE_fc C e; have h2 := trLs_fc C es; fc h1 h2
theorem trKVs_fc (C : List Scope) : ∀ kvs, Fc (ncDs C kvs) (itemsDs C kvs) C ((trKVs C kvs).flatMap PyCore.factsE)
  | [] => by fc Fc.nil
  | .mk (some k) v :: kvs => by
    have h1 := trE_fc C k; have h2 := trE_fc C v; have h3 := trKVs_fc C kvs; fc h1 h2 h3
  | .mk none v :: kvs => by have h2 := trE_fc C v; have h3 := trKVs_fc C kvs; fc h2 h3
theorem trDfs_fc (C Ci : List Scope) : ∀ ps, Fc (ncPs C Ci ps) (itemsPs C ps) C ((trDfs C ps).flatMap PyCore.factsE)
  | [] => by fc Fc.nil
  | .mk l _ _ (some d) _ :: ps => by have h1 := trE_fc C d; have h2 := trDfs_fc C Ci ps; fc h1 h2
  | .mk l _ _ none a :: ps => by have h2 := trDfs_fc C Ci ps; fc h2
theorem trAnns_fc (C Ci : List Scope) : ∀ ps, Fc (ncPs C Ci ps) (itemsPs C ps) C ((trAnns C ps).flatMap PyCore.factsE)
  | [] => by fc Fc.nil
  | .mk l _ _ _ (some a) :: ps => by have h1 := trE_fc C a; have h2 := trAnns_fc C Ci ps; fc h1 h2
  | .mk l _ _ d none :: ps => by have h2 := trAnns_fc C Ci ps; fc h2
theorem trG1_fc (C Ci : List Scope) : ∀ gs, Fc (ncGs C Ci true gs) (itemsG1 C gs) C (PyCore.factsE (trG1 C gs))
  | [] => by fc Fc.nil
  | .mk _ _ i _ :: _ => by have h1 := trE_fc C i; fc h1
theorem trGs_fc (C : List Scope) (it : Name) : ∀ (Co : List Scope) (first : Bool) (gs : List Gen)
    (inner : PS) (Ni : NC) (Bi : List Item), Fc Ni Bi C (PyCore.factsB inner) →
    Fc (ncGs Co C first gs ++ Ni) (itemsGs C first gs ++ Bi) C (PyCore.factsB (trGs C it first gs inner))
  | _, _, [], inner, Ni, Bi, h => by simpa [trGs, ncGs, itemsGs] using h
  | Co, first, .mk lg t i ifs :: gs, inner, Ni, Bi, h => by
    have h2 := trT_fc C (forSrc lg) (fun _ => rfl) t (trE_fc C t)
    have h3 := trEs_fc C ifs
    have h4 := trGs_fc C it Co false gs inner Ni Bi h
    cases first
    · have h1 := trE_fc C i
      simp only [trGs, forLoop]
      fc h1 h2 h3 h4 (Fc.frc "j" lg C) (Fc.frc "g" lg C) (Fc.frc "v" lg C) (Fc.frc "s" lg C)
    · simp only [trGs, forLoop]
      fc h2 h3 h4 (Fc.frc "g" lg C) (Fc.frc "v" lg C) (Fc.frc "s" lg C)
theorem trT_fc (C : List Scope) (src : Label → PE) (hs : SrcOk src) : ∀ t,
    Fc (ncE C t) (itemsE C t) C (PyCore.factsE (trE C t)) →
    Fc (ncE C t) (itemsE C t) C (PyCore.factsB (trT C src t (trE C t)))
  | .name lt x, _ => by have := hs lt; fc (Fc.usr lt (mangle (priv C) x) C C)
  | .attr lt o a, _ => by have := hs lt; have h1 := trE_fc C o; fc h1
  | .sub lt o i, _ => by have := hs lt; have h1 := trE_fc C o; have h2 := trE_fc C i; fc h1 h2
  | .tuple lt ts, _ => by have := hs lt; have h1 := trItems_fc C lt 0 ts; fc h1 (Fc.frc "u" lt C)
  | .list lt ts, _ => by have := hs lt; have h1 := trItems_fc C lt 0 ts; fc h1 (Fc.frc "u" lt C)
  | .star ls e, _ => by have h1 := trT_fc C src hs e (trE_fc C e); fc h1
  | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1 | .ifexp .., h1
  | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1 | .comp .., h1
  | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    simp only [trT]; intro f hf; apply h1 f
    simpa [PyCore.factsB, PyCore.factsS] using hf
theorem trItems_fc (C : List Scope) (lt : Label) : ∀ (i : Nat) (ts : List Expr),
    Fc (ncEs C ts) (itemsEs C ts) C (PyCore.factsB (trItems C lt i ts))
  | _, [] => by simp only [trItems]; fc Fc.nil
  | i, t :: ts => by
    have h1 := trT_fc C (itemSrc lt i) (srcOk_item lt i) t (trE_fc C t)
    have h2 := trItems_fc C lt (i + 1) ts
    rw [trItems_cons, pfactsB_append, pfactsB_unstar]; fc h1 h2
end


mutual
theorem trD_fc (C : List Scope) : ∀ t, Fc (ncE C t) (itemsE C t) C (PyCore.factsE (trE C t)) →
    Fc (ncE C t) (itemsE C t) C (PyCore.factsB (trD C t (trT C deadSrc t (trE C t))))
  | .name lt x, _ => by fc (Fc.usr lt (mangle (priv C) x) C C)
  | .attr lt o a, _ => by have h1 := trE_fc C o; fc h1
  | .sub lt o i, _ => by have h1 := trE_fc C o; have h2 := trE_fc C i; fc h1 h2
  | .tuple lt ts, _ => by have h1 := trDs_fc C ts; fc h1
  | .list lt ts, _ => by have h1 := trDs_fc C ts; fc h1
  | .star .., h1 | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1
  | .ifexp .., h1 | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1
  | .comp .., h1 | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    have h2 := trT_fc C deadSrc srcOk_dead _ h1
    simp only [trD]; intro f hf; apply h2 f
    simpa [PyCore.factsB, PyCore.factsS] using hf
theorem trDs_fc (C : List Scope) : ∀ ts, Fc (ncEs C ts) (itemsEs C ts) C (PyCore.factsB (trDs C ts))
  | [] => by simp only [trDs]; fc Fc.nil
  | t :: ts => by
    have h1 := trD_fc C t (trE_fc C t); have h2 := trDs_fc C ts
    simp only [trDs, pfactsB_append]; fc h1 h2
end

theorem trAug_fc (C : List Scope) (l : Label) (t : Expr) :
    Fc ((l, C, C) :: ncE C t) (itemsE C t) C
      (PyCore.factsB (trAug C l t (trT C deadSrc t (trE C t))).1 ++
        PyCore.factsB (trAug C l t (trT C deadSrc t (trE C t))).2) := by
  have h0 := trT_fc C deadSrc srcOk_dead t (trE_fc C t)
  cases t with
  | name lt x =>
    simp only [trAug]; fc (Fc.usr lt (mangle (priv C) x) C C) (Fc.frc "g" l C)
  | attr lt e a =>
    have h2 := trE_fc C e; simp only [trAug]; fc h2 (Fc.frc "o" l C) (Fc.frc "g" l C)
  | sub lt e i =>
    have h2 := trE_fc C e; have h3 := trE_fc C i
    simp only [trAug]; fc h2 h3 (Fc.frc "o" l C) (Fc.frc "k" l C) (Fc.frc "g" l C)
  | _ => simp only [trAug]; fc h0

theorem annBare_fc (C : List Scope) (t : Expr) :
    Fc (ncE C t) (itemsE C t) C (PyCore.factsB (annBare C t (trT C deadSrc t (trE C t))) ++
      PyCore.factsB (annBind C t)) := by
  have h0 := trT_fc C deadSrc srcOk_dead t (trE_fc C t)
  cases t with
  | name lt x => simp only [annBare, annBind]; fc (Fc.usr lt (mangle (priv C) x) C C)
  | attr lt e a => have h2 := trE_fc C e; simp only [annBare, annBind]; fc h2
  | sub lt e i => have h2 := trE_fc C e; have h3 := trE_fc C i; simp only [annBare, annBind]; fc h2 h3
  | _ => simp only [annBare, annBind]; fc h0

theorem fc_aliases (C : List Scope) (g : Alias → PyCore.Stmt) (N : NC)
    (hg : ∀ a, PyCore.factsS (g a) = if a.name == "*" then [] else [.bind (mangle (priv C) a.bound)]) :
    ∀ al : List Alias, Fc N ((bindingAliases al).map fun a => .occ a.l (mangle (priv C) a.bound) C) C
      (PyCore.factsB (al.map g)) := by
  intro al f hf
  have := (alias_facts C g hg f al).1 hf
  simp only [List.mem_map] at this
  obtain ⟨a, ha, rfl⟩ := this
  exact .inl ⟨a.l, C, List.mem_map.mpr ⟨a, ha, rfl⟩⟩

mutual
theorem trS_fc (C : List Scope) : ∀ s, Fc (ncS C s) (itemsS C s) C (PyCore.factsS (trS C s))
  | .expr l e => by have h1 := trE_fc C e; simp only [trS]; fc h1
  | .assign l ts e => by
    have h1 := trE_fc C e
    have h2 : ∀ ts, Fc (ncEs C ts) (itemsEs C ts) C (PyCore.factsB (trTs C (nameSrc "t" l) ts)) := by
      intro ts; induction ts with
      | nil => simp only [trTs]; fc Fc.nil
      | cons t ts ih =>
        have := trT_fc C (nameSrc "t" l) (srcOk_name "t" l) t (trE_fc C t)
        simp only [trTs, pfactsB_append]; fc this ih
    have h3 := h2 ts
    simp only [trS]; fc h1 h3 (Fc.frc "t" l C)
  | .augassign l t op e => by
    have h1 := trAug_fc C l t; have h2 := trE_fc C e
    simp only [trS]; fc h1 h2 (Fc.frc "v" l C)
  | .annassign l t a v => by
    have h1 := trE_fc C a
    have h3 := trT_fc C (nameSrc "t" l) (srcOk_name "t" l) t (trE_fc C t)
    have h4 := annBare_fc C t
    cases v with
    | none => cases hf : isTop C <;> simp only [trS, hf] <;> fc h1 h4 (Fc.frc "n" l C)
    | some v =>
      have h2 := trE_fc C v
      cases hf : isTop C <;> simp only [trS, hf] <;> fc h1 h2 h3 (Fc.frc "t" l C) (Fc.frc "n" l C)
  | .del l ts => by have h1 := trDs_fc C ts; simp only [trS]; fc h1
  | .ite l c t u => by
    have h1 := trE_fc C c; have h2 := trB_fc C t; have h3 := trB_fc C u; simp only [trS]; fc h1 h2 h3
  | .while l c b u => by
    have h1 := trE_fc C c; have h2 := trB_fc C b; have h3 := trB_fc C u; simp only [trS]; fc h1 h2 h3
  | .for l t it b u => by
    have h1 := trE_fc C it
    have h2 := trT_fc C (forSrc l) (srcOk_for l) t (trE_fc C t)
    have h3 := trB_fc C b; have h4 := trB_fc C u
    simp only [trS, forLoop]
    fc h1 h2 h3 h4 (Fc.frc "i" l C) (Fc.frc "g" l C) (Fc.frc "v" l C) (Fc.frc "s" l C)
  | .brk l | .cont l | .pass l => by simp only [trS]; fc Fc.nil
  | .ret l e => by have h1 := trO_fc C l 1 e; simp only [trS]; fc h1
  | .defn l f ps b ds r => by
    have h1 := trEs_fc C ds; have h2 := trDfs_fc C (.fn l f ps b :: C) ps
    have h3 := trAnns_fc C (.fn l f ps b :: C) ps
    have hk : Fc (ncPs C (.fn l f ps b :: C) ps) (itemsPs C ps) C
        ((trAnnK C .pos ps ++ trAnnK C .posonly ps ++ trAnnK C .vararg ps ++ trAnnK C .kwonly ps ++
          trAnnK C .kwarg ps).flatMap PyCore.factsE) :=
      fun g hg => h3 g ((flatMap_mem_iff (trAnnK_all C · ps) g).1 hg)
    cases r with
    | none =>
      simp only [trS]; simp only [List.flatMap_append] at hk
      fc h1 h2 hk (Fc.usr l (mangle (priv C) f) C C)
    | some r =>
      have h4 := trE_fc C r
      simp only [trS]; simp only [List.flatMap_append] at hk
      fc h1 h2 hk h4 (Fc.usr l (mangle (priv C) f) C C)
  | .cls l x bs ks b ds => by
    have h1 := trEs_fc C ds; have h2 := trA_fc C bs; have h3 := trKs_fc C ks
    simp only [trS]; fc h1 h2 h3 (Fc.usr l (mangle (priv C) x) C C)
  | .glob l xs => by
    simp only [trS]; intro g hg
    simp only [blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, pfactsB_map, List.append_nil,
      List.mem_flatMap, List.mem_singleton] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨l, C, by simp [itemsS]; exact ⟨y, hy, rfl⟩⟩
  | .nonloc l xs => by
    simp only [trS]; intro g hg
    simp only [blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, pfactsB_map, List.append_nil,
      List.mem_flatMap, List.mem_singleton] at hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨l, C, by simp [itemsS]; exact ⟨y, hy, rfl⟩⟩
  | .tryE l b hs u => by
    have h1 := trB_fc C b; have h2 := trHs_fc C hs; have h3 := trB_fc C u; simp only [trS]; fc h1 h2 h3
  | .raise l none none => by simp only [trS]; fc Fc.nil
  | .raise l (some e) none => by have h1 := trE_fc C e; simp only [trS]; fc h1
  | .raise l (some e) (some c) => by have h1 := trE_fc C e; have h2 := trE_fc C c; simp only [trS]; fc h1 h2
  | .raise l none (some c) => by have h2 := trE_fc C c; simp only [trS]; fc h2
  | .imp l al => by
    simp only [trS, itemsS, blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, List.append_nil]
    refine fc_aliases C _ _ (fun a => ?_) al
    split <;> simp_all [PyCore.factsS, stuckAt, PyCore.factsE]
  | .impFrom l m al lvl => by
    simp only [trS, itemsS]
    split
    · intro g hg
      simp only [blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, pfactsB_map, PyCore.factsE,
        pfactsE_gad, List.flatMap_nil, List.nil_append, List.append_nil, pfactsS_dead, List.mem_flatMap,
        List.mem_map, List.mem_singleton] at hg
      obtain ⟨a, ha, rfl⟩ := hg
      exact .inl ⟨a.l, C, List.mem_map.mpr ⟨a, ha, rfl⟩⟩
    · have hm := Fc.frc (C := C) "m" l
      intro g hg
      simp only [blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, List.append_nil, PyCore.factsE,
        pfactsE_cc, List.flatMap_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | hg
      · exact (hm _ (by simp)).mono (by simp [ncS]) (by simp)
      · refine fc_aliases C _ (ncS C (.impFrom l m al lvl)) (fun a => ?_) al g hg
        split <;> simp_all [PyCore.factsS, PyCore.factsE, nm]
  | .assert l t m => by
    have h1 := trE_fc C t
    cases m with
    | none => simp only [trS]; fc h1
    | some m => have h2 := trE_fc C m; simp only [trS]; fc h1 h2
theorem trHs_fc (C : List Scope) : ∀ hs, Fc (ncHs C hs) (itemsHs C hs) C (PyCore.factsHs (trHs C hs))
  | [] => by simp only [trHs]; fc Fc.nil
  | .mk l ty x b :: hs => by
    have h2 := trB_fc C b; have h3 := trHs_fc C hs
    have hx : Fc [(l, C, C)] ((x.map fun x => Item.occ l (mangle (priv C) x) C).toList) C
        [.bind ((x.map (mangle (priv C))).getD (fresh "e" l))] := by
      cases x with
      | none => exact Fc.frc "e" l C
      | some x => exact Fc.congr (Fc.usr l (mangle (priv C) x) C C) (by simp) (by simp) (by simp)
    cases ty with
    | none => simp only [trHs]; fc h2 h3 hx
    | some t => have h1 := trE_fc C t; simp only [trHs]; fc h1 h2 h3 hx
theorem trB_fc (C : List Scope) : ∀ ss, Fc (ncB C ss) (itemsB C ss) C (PyCore.factsB (trB C ss))
  | [] => by simp only [trB]; fc Fc.nil
  | s :: ss => by
    have h1 := trS_fc C s; have h2 := trB_fc C ss
    simp only [trB]; fc h1 h2
end

theorem fc_param (C : List Scope) (ps : List Param) :
    Fc [] (paramOccs C ps) C (PyCore.factsB (paramBind C ps)) := by
  rw [pfactsB_paramBind]; intro f hf
  simp only [paramBinds, List.mem_map] at hf
  obtain ⟨q, hq, rfl⟩ := hf
  exact .inl ⟨q.label, C, by simp only [paramOccs, List.mem_map]; exact ⟨q, hq, rfl⟩⟩

theorem fc_scope_fn (C : List Scope) (l : Label) (f : Name) (ps : List Param) (b : List Stmt)
    (ds : List Expr) (r : Option Expr) :
    Fc (ncS C (.defn l f ps b ds r)) (itemsS C (.defn l f ps b ds r)) (.fn l f ps b :: C)
      (trScope C (.fn l f ps b)).facts := by
  have h1 := fc_param (.fn l f ps b :: C) ps; have h2 := trB_fc (.fn l f ps b :: C) b
  simp only [trScope, PyCore.Scope.facts, pfactsB_append]
  fc h1 h2 (Fc.fr "a" l C (.fn l f ps b :: C) _ (by decide) (by simp [home]))

theorem fc_scope_lam (C : List Scope) (l : Label) (ps : List Param) (b : Expr) :
    Fc (ncE C (.lam l ps b)) (itemsE C (.lam l ps b)) (.lam l ps b :: C) (trScope C (.lam l ps b)).facts := by
  have h1 := fc_param (.lam l ps b :: C) ps; have h2 := trE_fc (.lam l ps b :: C) b
  simp only [trScope, PyCore.Scope.facts, pfactsB_append]
  fc h1 h2 (Fc.fr "a" l C (.lam l ps b :: C) _ (by decide) (by simp [home]))

theorem fc_scope_cl (C : List Scope) (l : Label) (x : Name) (bs : List Expr) (ks : List Kw) (b : List Stmt)
    (ds : List Expr) :
    Fc (ncS C (.cls l x bs ks b ds)) (itemsS C (.cls l x bs ks b ds)) (.cl l x b :: C)
      (trScope C (.cl l x b)).facts := by
  have h2 := trB_fc (.cl l x b :: C) b
  simp only [trScope, PyCore.Scope.facts]
  fc h2 (Fc.usr l "__module__" (.cl l x b :: C) (.cl l x b :: C))
    (Fc.usr l "__qualname__" (.cl l x b :: C) (.cl l x b :: C))

theorem fc_scope_comp (C : List Scope) (l : Label) (k : CompKind) (es : List Expr) (gs : List Gen) :
    Fc (ncE C (.comp l k es gs)) (itemsE C (.comp l k es gs)) (.comp l k es gs :: C)
      (trScope C (.comp l k es gs)).facts := by
  have h2 := trEs_fc (.comp l k es gs :: C) es
  have h3 : Fc (ncEs (.comp l k es gs :: C) es) (itemsEs (.comp l k es gs :: C) es) (.comp l k es gs :: C)
      (PyCore.factsB (compElt l k (trEs (.comp l k es gs :: C) es))) := by
    intro f hf
    by_cases hy : f = .yld
    · subst hy; trivial
    · exact h2 f ((pfactsB_compElt l k _ f hy).1 hf)
  have h4 := trGs_fc (.comp l k es gs :: C) (fresh "i" l) C true gs _ _ _ h3
  have ha := Fc.fr "acc" l C (.comp l k es gs :: C) (.comp l k es gs :: C) (by decide) (by simp [home])
  have hi := Fc.fr "i" l C (.comp l k es gs :: C) (.comp l k es gs :: C) (by decide) (by simp [home])
  simp only [trScope, PyCore.Scope.facts]
  unfold compWrap; split
  · fc h4 hi
  · fc h4 ha hi

end Surf
