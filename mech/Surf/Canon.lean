/-
The fresh-name invariant of one translated program (`fresh_canon`), from the facts of
`Own.lean`, and the footprint theorem for ⌊p⌋ and ⌊q⌋ (`footprint_theorem_surf`). Every
occurrence of a fresh name `.tag l` in ⌊p⌋ is in the chain `D ++ C` of its home (`Oc`):
`D` are the scopes inside the block at hand, the name is bound in the head of the chain, and
the facts of every scope of `D` are those of `Fc`. With distinct labels a label has one
entry, so the facts of the scopes around the head say nothing about the name, which is the
pattern of `FreshCanon`.
-/
import Surf.Own

namespace Surf
open PyCore (Name Label Fact)

set_option linter.unusedSimpArgs false

/-- Along the scopes `D` (innermost first) of the chain `D ++ C`, `x` is bound in the head;
`F` holds the binding where `D` is empty. -/
def Bnd (x : Name) (F : List Fact) (C : List Scope) : List Scope → Prop
  | [] => .bind x ∈ F
  | S :: D => .bind x ∈ (trScope (D ++ C) S).facts

/-- The facts of each scope of `D` are those of `Fc`. -/
def Okc (N : NC) (B : List Item) (C : List Scope) : List Scope → Prop
  | [] => True
  | S :: D => Fc N B (S :: D ++ C) (trScope (D ++ C) S).facts ∧ Okc N B C D

/-- An occurrence of `x` in the chain `C'`: `x` is a name of `p`, or a fresh name `.t l0` whose
home is `D ++ C` with `C' = ⌊D ++ C⌋`, bound in the head by `Bnd`. -/
def Good (N : NC) (F : List Fact) (B : List Item) (C : List Scope) (x : Name) (C' : List PyCore.Scope) : Prop :=
  (∃ l C1, Item.occ l x C1 ∈ B) ∨ ∃ t l0 D co ci, x = fresh t l0 ∧ NoDig t ∧
    C' = trChain (D ++ C) ∧ (l0, co, ci) ∈ N ∧ D ++ C = home t co ci ∧ Bnd x F C D ∧ Okc N B C D

def Oc (N : NC) (F : List Fact) (B : List Item) (C : List Scope) (A : List PyCore.Item) : Prop :=
  ∀ L x C', PyCore.Item.occ L x C' ∈ A → Good N F B C x C'

section
variable {N N' Nb : NC} {F F' Fb : List Fact} {B B' Bb : List Item} {C : List Scope}

theorem Bnd.mono {x : Name} (hF : ∀ f ∈ F, f ∈ F') : ∀ D, Bnd x F C D → Bnd x F' C D
  | [], h => hF _ h
  | _ :: _, h => h

theorem Okc.mono (hN : ∀ a ∈ N, a ∈ N') (hB : ∀ j ∈ B, j ∈ B') : ∀ D, Okc N B C D → Okc N' B' C D
  | [], _ => trivial
  | S :: D, h => ⟨fun f hf => (h.1 f hf).mono hN hB, Okc.mono hN hB D h.2⟩

theorem Good.mono {x C'} (h : Good N F B C x C') (hN : ∀ a ∈ N, a ∈ N') (hF : ∀ f ∈ F, f ∈ F')
    (hB : ∀ j ∈ B, j ∈ B') : Good N' F' B' C x C' := by
  rcases h with ⟨l, C1, h⟩ | ⟨t, l0, D, co, ci, h1, h2, h3, h4, h5, h7, h8⟩
  · exact .inl ⟨l, C1, hB _ h⟩
  · exact .inr ⟨t, l0, D, co, ci, h1, h2, h3, hN _ h4, h5, Bnd.mono hF D h7, Okc.mono hN hB D h8⟩

theorem Oc.congr {A A' : List PyCore.Item} (h : Oc N F B C A)
    (hA : ∀ L x C', PyCore.Item.occ L x C' ∈ A' → PyCore.Item.occ L x C' ∈ A)
    (hN : ∀ a ∈ N, a ∈ N') (hF : ∀ f ∈ F, f ∈ F') (hB : ∀ j ∈ B, j ∈ B') : Oc N' F' B' C A' :=
  fun L x C' hi => (h L x C' (hA L x C' hi)).mono hN hF hB

theorem Oc.cat {N2 F2 B2} {A1 A2 : List PyCore.Item} (h1 : Oc N F B C A1) (h2 : Oc N2 F2 B2 C A2) :
    Oc (N ++ N2) (F ++ F2) (B ++ B2) C (A1 ++ A2) := by
  intro L x C' hi
  rcases List.mem_append.1 hi with h | h
  · exact (h1 L x C' h).mono (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)
      (fun _ h => List.mem_append_left _ h)
  · exact (h2 L x C' h).mono (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
      (fun _ h => List.mem_append_right _ h)

theorem Oc.nil : Oc [] [] [] C [] := by simp [Oc]

/-- Items that are no occurrences. -/
theorem Oc.noocc {A : List PyCore.Item} (h : ∀ L x C', PyCore.Item.occ L x C' ∉ A) : Oc [] [] [] C A :=
  fun L x C' hi => absurd hi (h L x C')

/-- A name of `p`. -/
theorem Oc.usr (L : Label) (x : Name) (C' : List PyCore.Scope) (l : Label) (C1 : List Scope) :
    Oc [] [] [.occ l x C1] C [.occ L x C'] := by
  intro L' x' C'' hi; simp at hi; obtain ⟨rfl, rfl, rfl⟩ := hi; exact .inl ⟨l, C1, by simp⟩

/-- A fresh name in its home, bound there. -/
theorem Oc.fr (t : String) (l L : Label) (co ci : List Scope) (ht : NoDig t) (hh : C = home t co ci) :
    Oc [(l, co, ci)] [.bind (fresh t l)] [] C [.occ L (fresh t l) (trChain C)] := by
  intro L x C' hi; simp at hi; obtain ⟨rfl, rfl, rfl⟩ := hi
  exact .inr ⟨t, l, [], co, ci, rfl, ht, by simp, by simp, by simpa using hh, by simp [Bnd], trivial⟩

theorem Oc.frc (t : String) (l L : Label) (ht : NoDig t := by decide) :
    Oc [(l, C, C)] [.bind (fresh t l)] [] C [.occ L (fresh t l) (trChain C)] :=
  Oc.fr t l L C C ht (home_co t C)

/-- The parameter of a function or comprehension, at its node. -/
theorem Oc.par (S : Scope) (t : String) (l : Label) (ht : t = "a" ∨ t = "i")
    (hb : .bind (fresh t l) ∈ (trScope C S).facts) (hS : Fc N B (S :: C) (trScope C S).facts)
    (hN : (l, C, S :: C) ∈ N) :
    Oc N [] B C [.occ (sub l 1) (fresh t l) (trScope C S :: trChain C)] := by
  intro L x C' hi; simp at hi; obtain ⟨rfl, rfl, rfl⟩ := hi
  refine .inr ⟨t, l, [S], C, S :: C, rfl, by rcases ht with rfl | rfl <;> decide, rfl, hN,
    by rcases ht with rfl | rfl <;> simp [home], by simpa [Bnd] using hb, ⟨by simpa using hS, trivial⟩⟩

theorem okc_lift {S : Scope} (hS : Fc N B (S :: C) (trScope C S).facts) (hN : ∀ a ∈ Nb, a ∈ N)
    (hB : ∀ j ∈ Bb, j ∈ B) : ∀ D, Okc Nb Bb (S :: C) D → Okc N B C (D ++ [S])
  | [], _ => by simpa [Okc] using hS
  | S' :: D, h => by
    simp only [Okc, List.cons_append, List.append_assoc, List.singleton_append] at h ⊢
    exact ⟨fun f hf => (h.1 f hf).mono hN hB, okc_lift hS hN hB D h.2⟩

/-- The occurrences in a scope `S` introduced in the block at hand. -/
theorem Oc.scope {S : Scope} {A : List PyCore.Item} (hS : Fc N B (S :: C) (trScope C S).facts)
    (hF : ∀ f ∈ Fb, f ∈ (trScope C S).facts) (hN : ∀ a ∈ Nb, a ∈ N) (hB : ∀ j ∈ Bb, j ∈ B)
    (h : Oc Nb Fb Bb (S :: C) A) : Oc N F B C A := by
  intro L x C' hi
  rcases h L x C' hi with ⟨l, C1, h⟩ | ⟨t, l0, D, co, ci, h1, h2, h3, h4, h5, h7, h8⟩
  · exact .inl ⟨l, C1, hB _ h⟩
  · refine .inr ⟨t, l0, D ++ [S], co, ci, h1, h2, by simpa using h3, hN _ h4, by simpa using h5, ?_,
      okc_lift hS hN hB D h8⟩
    cases D with
    | nil => simpa [Bnd] using hF _ h7
    | cons S' D => simpa [Bnd] using h7

end

/-- `occat p₁ … pₙ` appends the `Oc` facts `pᵢ`. -/
syntax "occat" (ppSpace colGt term:max)+ : term
macro_rules
  | `(occat $p) => `($p)
  | `(occat $p $ps*) => `(Oc.cat $p (occat $ps*))

/-- The simplification of occurrences. -/
macro "oc_simp" loc:(ppSpace Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [trE, trO, trEs,
    trA, trKs, trLs, trKVs, trDfs, trAnns, trG1, trGs, trT, trItems, nameSrc, itemSrc, forSrc, blk, nm, setupS,
    forLoop,
    itemsE, itemsO, itemsEs, itemsKs, itemsDs, itemsPs, itemsG1, itemsGs, trChain, trScope, List.mem_append,
    List.mem_cons, List.not_mem_nil, List.flatMap_cons, List.flatMap_nil, List.flatMap_append, List.append_nil,
    List.nil_append, pitemsB_append, pitemsB_map, PyCore.itemsB, PyCore.itemsS, PyCore.itemsHs,
    PyCore.itemsE, enone_e, enone_s, enone_h, Option.isSome_none, Bool.false_eq_true, ite_false, ite_true,
    or_false, false_or, pitemsE_recR, pitemsE_ccR, pitemsE_cc, pitemsE_gad, pitemsE_starMark,
    pitemsE_kwMark, pitemsE_constMark, pitemsE_constMarks, pitemsE_marks, pitemsE_paramMark,
    pitemsE_boolChain, pitemsE_cmpOps, pitemsB_ifsNest, pitemsS_dead, pitemsS_stuckAt, pitemsS_setupS,
    pitemsE_deadSrc, dflt_mk, ann_mk, List.flatMap_map, List.map_cons, List.map_nil, trMarks_eq,
    constMarks_eq, flatMap_nil_fun, PyCore.Item.occ.injEq, reduceCtorEq] $[$loc]?)

/-- Close an `Oc` goal from `Oc` facts about its parts. -/
macro "oc" ps:(ppSpace colGt term:max)+ : tactic => `(tactic|
  exact Oc.congr (occat $ps*)
    (by intro L x C' hi; (try oc_simp at hi ⊢); all_goals grind)
    (by intro a ha; (try nc_simp at ha ⊢); all_goals grind)
    (by intro f hf; (try simp only [trScope, PyCore.Scope.facts] at hf ⊢); (try tr_simp at hf ⊢);
        all_goals grind)
    (by intro j hj; (try nc_simp at hj ⊢); all_goals grind))


theorem oc_param (D : List Scope) : ∀ ps : List Param,
    Oc [] [] (paramOccs D ps) D (PyCore.itemsB R0 (trChain D) (paramBind D ps))
  | [] => by simp [Oc, paramBind, PyCore.itemsB]
  | q :: ps => by
    have ih := oc_param D ps
    simp only [paramBind, paramOccs, List.map_cons] at ih ⊢
    oc ih (Oc.usr (C := D) (sub q.label 0) (mangle (priv D) q.name) (trChain D) q.label D)

/-- An occurrence of a name of `p`, in any chain. -/
theorem Oc.usr' {C : List Scope} {A : List PyCore.Item} {B : List Item}
    (h : ∀ L x C', PyCore.Item.occ L x C' ∈ A → ∃ l C1, Item.occ l x C1 ∈ B) : Oc [] [] B C A :=
  fun L x C' hi => .inl (h L x C' hi)

theorem pitemsB_compElt (D : List PyCore.Scope) (l : Label) (k : CompKind) (es : List PE) :
    ∀ i ∈ PyCore.itemsB R0 D (compElt l k es),
      (k ≠ .gen ∧ i = .occ (sub l 8) (fresh "acc" l) D) ∨ i ∈ es.flatMap (PyCore.itemsE R0 D) := by
  intro i hi
  have hd : ∀ xs : List PE, PyCore.itemsB R0 D (xs.map (PyCore.Stmt.expr (sub l 11))) = xs.flatMap (PyCore.itemsE R0 D) := by
    intro xs; induction xs <;> simp_all [PyCore.itemsB, PyCore.itemsS]
  cases k <;> rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp [compElt, PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, nm, cc, hd] at hi ⊢ <;> grind

theorem pfactsB_compElt_sup (l : Label) (k : CompKind) (es : List PE) :
    ∀ f ∈ es.flatMap PyCore.factsE, f ∈ PyCore.factsB (compElt l k es) := by
  intro f hf
  by_cases hy : f = .yld
  · subst hy
    unfold compElt; split <;> simp_all [PyCore.factsB, PyCore.factsS, PyCore.factsE, cc, nm, pfactsB_map]
  · exact (pfactsB_compElt l k es f hy).2 hf

theorem pfactsB_trGs_sup (C : List Scope) (it : Name) : ∀ (first : Bool) (gs : List Gen) (inner : PS),
    ∀ f ∈ PyCore.factsB inner, f ∈ PyCore.factsB (trGs C it first gs inner)
  | _, [], inner, f, h => by simpa [trGs] using h
  | first, .mk lg t i ifs :: gs, inner, f, h => by
    have := pfactsB_trGs_sup C it false gs inner f h
    cases first <;> simp [trGs, forLoop, PyCore.factsB, PyCore.factsS, PyCore.factsHs, pfactsB_append, this]

/-! ## The occurrences of the translation -/

mutual
theorem trE_oc (C : List Scope) : ∀ e,
    Oc (ncE C e) (PyCore.factsE (trE C e)) (itemsE C e) C (PyCore.itemsE R0 (trChain C) (trE C e))
  | .const l c => by oc Oc.nil
  | .name l x => by oc (Oc.usr (C := C) (sub l 0) (mangle (priv C) x) (trChain C) l C)
  | .bin l op a b => by have h1 := trE_oc C a; have h2 := trE_oc C b; oc h1 h2
  | .unary l op a => by have h1 := trE_oc C a; oc h1
  | .boolop l op es => by have h1 := trEs_oc C es; oc h1
  | .compare l a ops es => by
    have h1 := trE_oc C a; have h2 := trLs_oc C es
    simp only [trE, pitemsE_cmpChain, pfactsE_cmpChain, pitemsE_cmpOps, pfactsE_cmpOps]; oc h1 h2
  | .ifexp l c a b => by
    have h1 := trE_oc C c; have h2 := trE_oc C a; have h3 := trE_oc C b; oc h1 h2 h3
  | .call l f args kws => by
    have h1 := trE_oc C f; have h2 := trA_oc C args; have h3 := trKs_oc C kws; oc h1 h2 h3
  | .attr l e a => by have h1 := trE_oc C e; oc h1
  | .sub l e i => by have h1 := trE_oc C e; have h2 := trE_oc C i; oc h1 h2
  | .slice l a b c => by
    have h1 := trO_oc C l 1 a; have h2 := trO_oc C l 2 b; have h3 := trO_oc C l 3 c; oc h1 h2 h3
  | .star l e => by have h1 := trE_oc C e; oc h1
  | .list l es => by have h1 := trA_oc C es; oc h1
  | .tuple l es => by have h1 := trA_oc C es; oc h1
  | .set l es => by have h1 := trA_oc C es; oc h1
  | .dict l kvs => by have h1 := trKVs_oc C kvs; oc h1
  | .lam l ps b => by
    have h1 := trDfs_oc C (.lam l ps b :: C) ps; have h2 := trAnns_oc C (.lam l ps b :: C) ps
    have hS := fc_scope_lam C l ps b
    have h3 := oc_param (.lam l ps b :: C) ps
    have h4 := trE_oc (.lam l ps b :: C) b
    have h5 : Oc (ncE C (.lam l ps b)) [] (itemsE C (.lam l ps b)) C
        (PyCore.itemsB R0 (trChain (.lam l ps b :: C))
          (paramBind (.lam l ps b :: C) ps ++ [.ret (sub l 2) (trE (.lam l ps b :: C) b)])) := by
      refine Oc.scope (Fb := PyCore.factsB (paramBind (.lam l ps b :: C) ps) ++
          PyCore.factsE (trE (.lam l ps b :: C) b)) (Nb := [] ++ ncE (.lam l ps b :: C) b)
          (Bb := paramOccs (.lam l ps b :: C) ps ++ itemsE (.lam l ps b :: C) b) hS ?_ ?_ ?_ ?_
      · intro f hf; simp only [trScope, PyCore.Scope.facts, pfactsB_append, PyCore.factsB, PyCore.factsS,
          List.mem_cons, List.mem_append, List.append_nil] at hf ⊢; grind
      · intro a ha; nc_simp at ha ⊢; grind
      · intro j hj; nc_simp at hj ⊢; grind
      · have := Oc.cat h3 h4
        refine Oc.congr this ?_ (by simp) (fun f hf => by simp_all) (by simp)
        intro L x C' hi
        simp only [pitemsB_append, PyCore.itemsB, PyCore.itemsS, enone_s, Option.isSome_none,
          Bool.false_eq_true, ite_false, List.append_nil, List.mem_append] at hi ⊢; exact hi
    have h6 := Oc.par (N := ncE C (.lam l ps b)) (B := itemsE C (.lam l ps b)) (.lam l ps b) "a" l (.inl rfl)
      (by simp [trScope, PyCore.Scope.facts]) hS (by simp [ncE])
    oc h1 h2 h5 h6
  | .comp l k es gs => by
    have hS := fc_scope_comp C l k es gs
    have hE := trEs_oc (.comp l k es gs :: C) es
    have hacc : ∀ L, Oc [(l, C, .comp l k es gs :: C)] [.bind (fresh "acc" l)] [] (.comp l k es gs :: C)
        [.occ L (fresh "acc" l) (trChain (.comp l k es gs :: C))] :=
      fun L => Oc.fr "acc" l L C (.comp l k es gs :: C) (by decide) (by simp [home])
    have hit : ∀ lg, Oc [(l, C, .comp l k es gs :: C)] [.bind (fresh "i" l)] [] (.comp l k es gs :: C)
        [.occ (sub lg 18) (fresh "i" l) (trChain (.comp l k es gs :: C))] :=
      fun lg => Oc.fr "i" l (sub lg 18) C (.comp l k es gs :: C) (by decide) (by simp [home])
    have hel : Oc ([(l, C, .comp l k es gs :: C)] ++ ncEs (.comp l k es gs :: C) es)
        ((if k = .gen then [] else [.bind (fresh "acc" l)]) ++ (trEs (.comp l k es gs :: C) es).flatMap PyCore.factsE)
        ([] ++ itemsEs (.comp l k es gs :: C) es) (.comp l k es gs :: C)
        (PyCore.itemsB R0 (trChain (.comp l k es gs :: C)) (compElt l k (trEs (.comp l k es gs :: C) es))) := by
      intro L x C' hi
      rcases pitemsB_compElt _ l k _ _ hi with ⟨hk, he⟩ | he
      · simp only [PyCore.Item.occ.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
        exact (hacc (sub l 8) (sub l 8) _ _ (by simp)).mono (fun _ h => by simp_all) (fun _ h => by simp_all [hk])
          (fun _ h => by simp_all)
      · exact (hE L x C' he).mono (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)
          (fun _ h => by simpa using h)
    have hg := trGs_oc (.comp l k es gs :: C) (fresh "i" l) C true gs _ _ _ _ _ _ _ hit hel
    have hsc : ∀ f, f ∈ (trScope C (.comp l k es gs)).facts ↔ f = .bind (fresh "i" l) ∨
        f ∈ PyCore.factsB (compWrap l k (trGs (.comp l k es gs :: C) (fresh "i" l) true gs
          (compElt l k (trEs (.comp l k es gs :: C) es)))) := by
      intro f; simp [trScope, PyCore.Scope.facts]
    have hes := pfactsB_compElt_sup l k (trEs (.comp l k es gs :: C) es)
    have hgs := pfactsB_trGs_sup (.comp l k es gs :: C) (fresh "i" l) true gs
      (compElt l k (trEs (.comp l k es gs :: C) es))
    have hwrap : ∀ loops : PS, ∀ f ∈ PyCore.factsB loops, f ∈ PyCore.factsB (compWrap l k loops) := by
      intro loops f hf; unfold compWrap; split
      · exact hf
      · simp [PyCore.factsB, PyCore.factsS, pfactsB_append, hf]
    have hacf : k ≠ .gen → ∀ loops : PS, Fact.bind (fresh "acc" l) ∈ PyCore.factsB (compWrap l k loops) := by
      intro hk loops; unfold compWrap; simp [hk, PyCore.factsB, PyCore.factsS]
    have hbody : Oc (ncE C (.comp l k es gs)) [] (itemsE C (.comp l k es gs)) C
        (PyCore.itemsB R0 (trChain (.comp l k es gs :: C)) (compWrap l k (trGs (.comp l k es gs :: C)
          (fresh "i" l) true gs (compElt l k (trEs (.comp l k es gs :: C) es))))) := by
      refine Oc.scope (Fb := (trScope C (.comp l k es gs)).facts)
          (Nb := (ncGs C (.comp l k es gs :: C) true gs ++ [(l, C, .comp l k es gs :: C)] ++
            ([(l, C, .comp l k es gs :: C)] ++ ncEs (.comp l k es gs :: C) es)) ++ [(l, C, .comp l k es gs :: C)])
          (Bb := (itemsGs (.comp l k es gs :: C) true gs ++ [] ++ ([] ++ itemsEs (.comp l k es gs :: C) es)) ++ [])
          hS (fun _ h => h) ?_ ?_ ?_
      · intro a ha; nc_simp at ha ⊢; grind
      · intro j hj; nc_simp at hj ⊢; grind
      · have hF : ∀ f ∈ PyCore.factsB (trGs (.comp l k es gs :: C) (fresh "i" l) true gs
            (compElt l k (trEs (.comp l k es gs :: C) es))) ++ [.bind (fresh "i" l)] ++
            ((if k = .gen then [] else [.bind (fresh "acc" l)]) ++
              (trEs (.comp l k es gs :: C) es).flatMap PyCore.factsE), f ∈ (trScope C (.comp l k es gs)).facts := by
          intro f hf; rw [hsc]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
          rcases hf with (hf | hf) | hf | hf
          · exact .inr (hwrap _ f hf)
          · exact .inl hf
          · split at hf
            · simp at hf
            · rename_i hk; simp only [List.mem_singleton] at hf; subst hf; exact .inr (hacf hk _)
          · exact .inr (hwrap _ f (hgs f (hes f hf)))
        unfold compWrap; split
        · refine Oc.congr (Oc.cat hg Oc.nil) (fun L x C' h => by simpa using h)
            (fun a h => by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢; grind)
            (fun f h => hF f (by simpa using h)) (fun _ h => by simpa using h)
        · have h := Oc.cat hg (Oc.cat (hacc (sub l 4)) (hacc (sub l 6)))
          refine Oc.congr h ?_ (by intro a ha; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢; grind) ?_
            (by intro j hj; simp only [List.mem_append] at hj ⊢; grind)
          · intro L x C' hi
            simp only [PyCore.itemsB, PyCore.itemsS, PyCore.itemsE, pitemsB_append, enone_s, enone_e,
              Option.isSome_none, Bool.false_eq_true, ite_false, cc, pitemsE_ccR, nm, List.flatMap_nil,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.append_nil,
              PyCore.Item.occ.injEq] at hi ⊢
            grind
          · rename_i hk
            intro f hf
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
            rcases hf with hf | hf | hf
            · exact hF f (by simp only [List.mem_append] at hf ⊢; grind)
            · subst hf; rw [hsc]; exact .inr (hacf hk _)
            · subst hf; rw [hsc]; exact .inr (hacf hk _)
    have h6 := Oc.par (N := ncE C (.comp l k es gs)) (B := itemsE C (.comp l k es gs)) (.comp l k es gs) "i" l
      (.inr rfl) (by simp [trScope, PyCore.Scope.facts]) hS (by simp [ncE])
    simp only [trE]
    split
    · rename_i he; simp only [List.isEmpty_iff] at he; subst he
      simp only [trGs] at hbody ⊢
      oc hbody h6
    · cases gs with
      | nil => simp at *
      | cons g gs' =>
        obtain ⟨lg, tg, ig, ifs⟩ := g
        have h1 := trE_oc C ig
        oc h1 hbody h6
  | .walrus l x e => by have h1 := trE_oc C e; oc h1 (Oc.usr (C := C) (sub l 0) (mangle (priv C) x) (trChain C) l C)
  | .yield l e => by have h1 := trO_oc C l 1 e; oc h1
  | .yieldFrom l e => by have h1 := trE_oc C e; oc h1
  | .fstr l es => by have h1 := trEs_oc C es; oc h1
  | .fmt l e cv sp => by
    have h1 := trE_oc C e
    cases sp with
    | none => simp only [trE]; split <;> oc h1
    | some s => have h2 := trE_oc C s; simp only [trE]; split <;> oc h1 h2
theorem trO_oc (C : List Scope) (l : Label) (k : Nat) : ∀ o,
    Oc (ncO C o) (PyCore.factsE (trO C l k o)) (itemsO C o) C (PyCore.itemsE R0 (trChain C) (trO C l k o))
  | none => by oc Oc.nil
  | some e => by have h1 := trE_oc C e; oc h1
theorem trEs_oc (C : List Scope) : ∀ es, Oc (ncEs C es) ((trEs C es).flatMap PyCore.factsE) (itemsEs C es) C
    ((trEs C es).flatMap (PyCore.itemsE R0 (trChain C)))
  | [] => by oc Oc.nil
  | e :: es => by have h1 := trE_oc C e; have h2 := trEs_oc C es; oc h1 h2
theorem trA_oc (C : List Scope) : ∀ es, Oc (ncEs C es) ((trA C es).flatMap PyCore.factsE) (itemsEs C es) C
    ((trA C es).flatMap (PyCore.itemsE R0 (trChain C)))
  | [] => by oc Oc.nil
  | e :: es => by
    have h1 := trE_oc C e; have h2 := trA_oc C es
    rw [trA_cons, List.flatMap_cons, List.flatMap_cons, pitemsE_unstar, pfactsE_unstar]; oc h1 h2
theorem trKs_oc (C : List Scope) : ∀ ks, Oc (ncKs C ks) ((trKs C ks).flatMap PyCore.factsE) (itemsKs C ks) C
    ((trKs C ks).flatMap (PyCore.itemsE R0 (trChain C)))
  | [] => by oc Oc.nil
  | .mk l x e :: ks => by have h1 := trE_oc C e; have h2 := trKs_oc C ks; oc h1 h2
theorem trLs_oc (C : List Scope) : ∀ es, Oc (ncEs C es) ((trLs C es).flatMap fun x => PyCore.factsE x.2)
    (itemsEs C es) C ((trLs C es).flatMap fun x => PyCore.itemsE R0 (trChain C) x.2)
  | [] => by oc Oc.nil
  | e :: es => by have h1 := trE_oc C e; have h2 := trLs_oc C es; oc h1 h2
theorem trKVs_oc (C : List Scope) : ∀ kvs, Oc (ncDs C kvs) ((trKVs C kvs).flatMap PyCore.factsE) (itemsDs C kvs) C
    ((trKVs C kvs).flatMap (PyCore.itemsE R0 (trChain C)))
  | [] => by oc Oc.nil
  | .mk (some k) v :: kvs => by
    have h1 := trE_oc C k; have h2 := trE_oc C v; have h3 := trKVs_oc C kvs; oc h1 h2 h3
  | .mk none v :: kvs => by have h2 := trE_oc C v; have h3 := trKVs_oc C kvs; oc h2 h3
theorem trDfs_oc (C Ci : List Scope) : ∀ ps, Oc (ncPs C Ci ps) ((trDfs C ps).flatMap PyCore.factsE) (itemsPs C ps) C
    ((trDfs C ps).flatMap (PyCore.itemsE R0 (trChain C)))
  | [] => by oc Oc.nil
  | .mk l _ _ (some d) _ :: ps => by have h1 := trE_oc C d; have h2 := trDfs_oc C Ci ps; oc h1 h2
  | .mk l _ _ none a :: ps => by have h2 := trDfs_oc C Ci ps; oc h2
theorem trAnns_oc (C Ci : List Scope) : ∀ ps, Oc (ncPs C Ci ps) ((trAnns C ps).flatMap PyCore.factsE) (itemsPs C ps) C
    ((trAnns C ps).flatMap (PyCore.itemsE R0 (trChain C)))
  | [] => by oc Oc.nil
  | .mk l _ _ _ (some a) :: ps => by have h1 := trE_oc C a; have h2 := trAnns_oc C Ci ps; oc h1 h2
  | .mk l _ _ d none :: ps => by have h2 := trAnns_oc C Ci ps; oc h2
theorem trGs_oc (C : List Scope) (it : Name) : ∀ (Co : List Scope) (first : Bool) (gs : List Gen)
    (inner : PS) (Ni : NC) (Fi : List Fact) (Bi : List Item) (Nn : NC) (Fn : List Fact) (Bn : List Item),
    (∀ lg, Oc Ni Fi Bi C [.occ (sub lg 18) it (trChain C)]) →
    Oc Nn Fn Bn C (PyCore.itemsB R0 (trChain C) inner) →
    Oc (ncGs Co C first gs ++ Ni ++ Nn) (PyCore.factsB (trGs C it first gs inner) ++ Fi ++ Fn)
      (itemsGs C first gs ++ Bi ++ Bn) C (PyCore.itemsB R0 (trChain C) (trGs C it first gs inner))
  | _, _, [], inner, Ni, Fi, Bi, Nn, Fn, Bn, hit, h => by oc h
  | Co, first, .mk lg t i ifs :: gs, inner, Ni, Fi, Bi, Nn, Fn, Bn, hit, h => by
    have h2 := trT_oc C (forSrc lg) [(lg, C, C)] [.bind (fresh "v" lg)] []
      (fun lt => by simpa [forSrc, PyCore.itemsE] using Oc.frc (C := C) "v" lg (sub lt 63)) t (trE_oc C t)
    have h3 := trEs_oc C ifs
    have h4 := trGs_oc C it Co false gs inner Ni Fi Bi Nn Fn Bn hit h
    have h5 := hit lg
    cases first
    · have h1 := trE_oc C i
      simp only [trGs, itemsGs, forLoop]
      oc h1 h2 h3 h4 (Oc.frc (C := C) "j" lg (sub lg 0)) (Oc.frc (C := C) "j" lg (sub lg 18))
        (Oc.frc (C := C) "g" lg (sub lg 10)) (Oc.frc (C := C) "g" lg (sub lg 13))
        (Oc.frc (C := C) "v" lg (sub lg 15)) (Oc.frc (C := C) "s" lg (sub lg 19))
        (Oc.frc (C := C) "g" lg (sub lg 21))
    · simp only [trGs, itemsGs, forLoop]
      oc h2 h3 h4 h5 (Oc.frc (C := C) "g" lg (sub lg 10)) (Oc.frc (C := C) "g" lg (sub lg 13))
        (Oc.frc (C := C) "v" lg (sub lg 15)) (Oc.frc (C := C) "s" lg (sub lg 19))
        (Oc.frc (C := C) "g" lg (sub lg 21))
theorem trT_oc (C : List Scope) (src : Label → PE) (Ns : NC) (Fs : List Fact) (Bs : List Item)
    (hsrc : ∀ lt, Oc Ns Fs Bs C (PyCore.itemsE R0 (trChain C) (src lt))) : ∀ t,
    Oc (ncE C t) (PyCore.factsE (trE C t)) (itemsE C t) C (PyCore.itemsE R0 (trChain C) (trE C t)) →
    Oc (ncE C t ++ Ns) (PyCore.factsB (trT C src t (trE C t)) ++ Fs) (itemsE C t ++ Bs) C
      (PyCore.itemsB R0 (trChain C) (trT C src t (trE C t)))
  | .name lt x, _ => by have h := hsrc lt; oc h (Oc.usr (C := C) (sub lt 0) (mangle (priv C) x) (trChain C) lt C)
  | .attr lt o a, _ => by have h := hsrc lt; have h1 := trE_oc C o; oc h h1
  | .sub lt o i, _ => by have h := hsrc lt; have h1 := trE_oc C o; have h2 := trE_oc C i; oc h h1 h2
  | .tuple lt ts, _ => by
    have h := hsrc lt; have h1 := trItems_oc C lt 0 ts
    oc h h1 (Oc.frc (C := C) "u" lt (sub lt 1))
  | .list lt ts, _ => by
    have h := hsrc lt; have h1 := trItems_oc C lt 0 ts
    oc h h1 (Oc.frc (C := C) "u" lt (sub lt 1))
  | .star ls e, _ => by have h1 := trT_oc C src Ns Fs Bs hsrc e (trE_oc C e); oc h1
  | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1 | .ifexp .., h1
  | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1 | .comp .., h1
  | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    simp only [trT]; oc h1
theorem trItems_oc (C : List Scope) (lt : Label) : ∀ (i : Nat) (ts : List Expr),
    Oc (ncEs C ts ++ [(lt, C, C)]) (PyCore.factsB (trItems C lt i ts) ++ [.bind (fresh "u" lt)]) (itemsEs C ts) C
      (PyCore.itemsB R0 (trChain C) (trItems C lt i ts))
  | _, [] => by simp only [trItems]; oc Oc.nil
  | i, t :: ts => by
    have h1 := trT_oc C (itemSrc lt i) [(lt, C, C)] [.bind (fresh "u" lt)] []
      (fun lt' => by simpa [itemSrc, PyCore.itemsE] using Oc.frc (C := C) "u" lt (sub lt' 61)) t (trE_oc C t)
    have h2 := trItems_oc C lt (i + 1) ts
    rw [trItems_cons, pitemsB_append, pfactsB_append, pitemsB_unstar, pfactsB_unstar]; oc h1 h2
end


theorem oc_dead (C : List Scope) : ∀ lt, Oc [] [] [] C (PyCore.itemsE R0 (trChain C) (deadSrc lt)) :=
  fun _ L x C' h => by simp at h

mutual
theorem trD_oc (C : List Scope) : ∀ t,
    Oc (ncE C t) (PyCore.factsE (trE C t)) (itemsE C t) C (PyCore.itemsE R0 (trChain C) (trE C t)) →
    Oc (ncE C t) (PyCore.factsB (trD C t (trT C deadSrc t (trE C t)))) (itemsE C t) C
      (PyCore.itemsB R0 (trChain C) (trD C t (trT C deadSrc t (trE C t))))
  | .name lt x, _ => by simp only [trD]; oc (Oc.usr (C := C) (sub lt 0) (mangle (priv C) x) (trChain C) lt C)
  | .attr lt o a, _ => by have h1 := trE_oc C o; simp only [trD]; oc h1
  | .sub lt o i, _ => by have h1 := trE_oc C o; have h2 := trE_oc C i; simp only [trD]; oc h1 h2
  | .tuple lt ts, _ => by have h1 := trDs_oc C ts; simp only [trD]; oc h1
  | .list lt ts, _ => by have h1 := trDs_oc C ts; simp only [trD]; oc h1
  | .star .., h1 | .const .., h1 | .bin .., h1 | .unary .., h1 | .boolop .., h1 | .compare .., h1
  | .ifexp .., h1 | .call .., h1 | .slice .., h1 | .set .., h1 | .dict .., h1 | .lam .., h1
  | .comp .., h1 | .walrus .., h1 | .yield .., h1 | .yieldFrom .., h1 | .fstr .., h1 | .fmt .., h1 => by
    have h2 := trT_oc C deadSrc [] [] [] (oc_dead C) _ h1
    simp only [trD]; oc h2
theorem trDs_oc (C : List Scope) : ∀ ts, Oc (ncEs C ts) (PyCore.factsB (trDs C ts)) (itemsEs C ts) C
    (PyCore.itemsB R0 (trChain C) (trDs C ts))
  | [] => by simp only [trDs]; oc Oc.nil
  | t :: ts => by
    have h1 := trD_oc C t (trE_oc C t); have h2 := trDs_oc C ts
    simp only [trDs, pitemsB_append, pfactsB_append]; oc h1 h2
end

theorem trAug_oc (C : List Scope) (l : Label) (t : Expr) (ht : simpleT t = true) :
    Oc ((l, C, C) :: ncE C t)
      (PyCore.factsB (trAug C l t (trT C deadSrc t (trE C t))).1 ++
        PyCore.factsB (trAug C l t (trT C deadSrc t (trE C t))).2 ++ [.bind (fresh "v" l)]) (itemsE C t) C
      (PyCore.itemsB R0 (trChain C) (trAug C l t (trT C deadSrc t (trE C t))).1 ++
        PyCore.itemsB R0 (trChain C) (trAug C l t (trT C deadSrc t (trE C t))).2) := by
  cases t with
  | name lt x =>
    simp only [trAug]
    oc (Oc.frc (C := C) "g" l (sub lt 0)) (Oc.usr (C := C) (sub lt 1) (mangle (priv C) x) (trChain C) lt C)
      (Oc.usr (C := C) (sub lt 2) (mangle (priv C) x) (trChain C) lt C) (Oc.frc (C := C) "v" l (sub lt 3))
  | attr lt e a =>
    have h2 := trE_oc C e; simp only [trAug]
    oc h2 (Oc.frc (C := C) "o" l (sub lt 4)) (Oc.frc (C := C) "g" l (sub lt 5))
      (Oc.frc (C := C) "o" l (sub lt 7)) (Oc.frc (C := C) "o" l (sub lt 10))
      (Oc.frc (C := C) "v" l (sub lt 11))
  | sub lt e i =>
    have h2 := trE_oc C e; have h3 := trE_oc C i
    simp only [trAug]
    oc h2 h3 (Oc.frc (C := C) "o" l (sub lt 4)) (Oc.frc (C := C) "k" l (sub lt 5))
      (Oc.frc (C := C) "g" l (sub lt 6)) (Oc.frc (C := C) "o" l (sub lt 8))
      (Oc.frc (C := C) "k" l (sub lt 9)) (Oc.frc (C := C) "o" l (sub lt 11))
      (Oc.frc (C := C) "k" l (sub lt 12)) (Oc.frc (C := C) "v" l (sub lt 13))
  | _ => simp [simpleT] at ht

theorem aug_g (C : List Scope) (l : Label) (t : Expr) (ht : simpleT t = true) :
    Fact.bind (fresh "g" l) ∈ PyCore.factsB (trAug C l t (trT C deadSrc t (trE C t))).1 := by
  cases t <;> simp [simpleT, trAug, PyCore.factsS, PyCore.factsB] at ht ⊢

theorem annBare_oc (C : List Scope) (t : Expr) :
    Oc (ncE C t) (PyCore.factsB (annBare C t (trT C deadSrc t (trE C t))) ++ PyCore.factsB (annBind C t))
      (itemsE C t) C (PyCore.itemsB R0 (trChain C) (annBare C t (trT C deadSrc t (trE C t))) ++
        PyCore.itemsB R0 (trChain C) (annBind C t)) := by
  have h0 := trT_oc C deadSrc [] [] [] (oc_dead C) t (trE_oc C t)
  cases t with
  | name lt x => simp only [annBare, annBind]; oc (Oc.usr (C := C) (sub lt 60) (mangle (priv C) x) (trChain C) lt C)
  | attr lt e a => have h2 := trE_oc C e; simp only [annBare, annBind]; oc h2
  | sub lt e i => have h2 := trE_oc C e; have h3 := trE_oc C i; simp only [annBare, annBind]; oc h2 h3
  | _ => simp only [annBare, annBind]; oc h0

theorem annT_oc (C : List Scope) (l : Label) (t : Expr) :
    Oc [(l, C, C)] [.bind (fresh "n" l)] [] C (PyCore.itemsB R0 (trChain C) (annT C l t)) := by
  cases t <;> simp only [annT] <;> oc (Oc.frc (C := C) "n" l (sub l 7))

theorem oc_names (C : List Scope) (l : Label) (f : Name → PyCore.Stmt)
    (hf : ∀ x, PyCore.itemsS R0 (trChain C) (f x) = [.occ (sub l 1) x (trChain C)]) :
    ∀ xs : List Name, Oc [] [] (xs.map fun x => .occ l x C) C (PyCore.itemsB R0 (trChain C) (xs.map f))
  | [] => Oc.nil
  | x :: xs => by
    have ih := oc_names C l f hf xs
    simp only [List.map_cons, PyCore.itemsB, hf]
    oc (Oc.usr (C := C) (sub l 1) x (trChain C) l C) ih


/-- The occurrences of an import's aliases: names of `p`, or the module's fresh name. -/
theorem oc_aliases (C : List Scope) (g : Alias → PyCore.Stmt) (N : NC) (F : List Fact) (Bx : List Item)
    (hg : ∀ a, ∀ L x C', PyCore.Item.occ L x C' ∈ PyCore.itemsS R0 (trChain C) (g a) →
      ((a.name == "*") = false ∧ x = mangle (priv C) a.bound) ∨ Good N F Bx C x C') :
    ∀ al : List Alias, Oc N F (Bx ++ (bindingAliases al).map fun a => .occ a.l (mangle (priv C) a.bound) C) C
      (PyCore.itemsB R0 (trChain C) (al.map g))
  | [] => fun L x C' h => by simp [PyCore.itemsB] at h
  | a :: al => by
    have ih := oc_aliases C g N F Bx hg al
    intro L x C' hi
    simp only [List.map_cons, PyCore.itemsB, List.mem_append] at hi
    rcases hi with hi | hi
    · rcases hg a L x C' hi with ⟨h1, rfl⟩ | h
      · have hn : a.name ≠ "*" := by simpa using h1
        exact .inl ⟨a.l, C, List.mem_append_right _ (by simp [bindingAliases, List.filter_cons, hn])⟩
      · exact h.mono (fun _ h => h) (fun _ h => h) (fun _ h => List.mem_append_left _ h)
    · refine (ih L x C' hi).mono (fun _ h => h) (fun _ h => h) (fun j hj => ?_)
      simp only [List.mem_append, bindingAliases, List.filter_cons] at hj ⊢
      rcases hj with hj | hj
      · exact .inl hj
      · right; split <;> simp_all

mutual
theorem trS_oc (C : List Scope) : ∀ s, regS {} C s = true →
    Oc (ncS C s) (PyCore.factsS (trS C s)) (itemsS C s) C (PyCore.itemsS R0 (trChain C) (trS C s))
  | .expr l e, _ => by have h1 := trE_oc C e; simp only [trS, itemsS]; oc h1
  | .assign l ts e, _ => by
    have h1 := trE_oc C e
    have h2 : ∀ ts, Oc (ncEs C ts ++ [(l, C, C)]) (PyCore.factsB (trTs C (nameSrc "t" l) ts) ++ [.bind (fresh "t" l)])
        (itemsEs C ts) C (PyCore.itemsB R0 (trChain C) (trTs C (nameSrc "t" l) ts)) := by
      intro ts; induction ts with
      | nil => simp only [trTs]; oc Oc.nil
      | cons t ts ih =>
        have := trT_oc C (nameSrc "t" l) [(l, C, C)] [.bind (fresh "t" l)] []
          (fun lt => by simpa [nameSrc, PyCore.itemsE] using Oc.frc (C := C) "t" l (sub lt 63)) t (trE_oc C t)
        simp only [trTs, pitemsB_append, pfactsB_append]; oc this ih
    have h3 := h2 ts
    simp only [trS, itemsS]; oc h1 h3 (Oc.frc (C := C) "t" l (sub l 1))
  | .augassign l t op e, hr => by
    have ht : simpleT t = true := by simpa [regS, augOk] using hr
    have h1 := trAug_oc C l t ht; have h2 := trE_oc C e
    have hg := aug_g C l t ht
    simp only [trS, itemsS]
    oc h1 h2 (Oc.frc (C := C) "v" l (sub l 1)) (Oc.frc (C := C) "g" l (sub l 3))
  | .annassign l t a v, _ => by
    have h1 := trE_oc C a
    have h3 := trT_oc C (nameSrc "t" l) [(l, C, C)] [.bind (fresh "t" l)] []
      (fun lt => by simpa [nameSrc, PyCore.itemsE] using Oc.frc (C := C) "t" l (sub lt 63)) t (trE_oc C t)
    have h4 := annBare_oc C t
    have h5 := annT_oc C l t
    cases v with
    | none =>
      cases hf : isTop C <;> simp only [trS, itemsS, itemsO, hf]
      · oc h1 h4
      · oc h1 h4 h5 (Oc.frc (C := C) "n" l (sub l 6))
    | some v =>
      have h2 := trE_oc C v
      cases hf : isTop C <;> simp only [trS, itemsS, itemsO, hf]
      · oc h1 h2 h3 (Oc.frc (C := C) "t" l (sub l 1))
      · oc h1 h2 h3 h5 (Oc.frc (C := C) "t" l (sub l 1)) (Oc.frc (C := C) "n" l (sub l 6))
  | .del l ts, _ => by have h1 := trDs_oc C ts; simp only [trS, itemsS]; oc h1
  | .ite l c t u, hr => by
    simp only [regS, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
    have h1 := trE_oc C c; have h2 := trB_oc C t hr.1; have h3 := trB_oc C u hr.2
    simp only [trS, itemsS]; oc h1 h2 h3
  | .while l c b u, hr => by
    simp only [regS, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
    have h1 := trE_oc C c; have h2 := trB_oc C b hr.1; have h3 := trB_oc C u hr.2
    simp only [trS, itemsS]; oc h1 h2 h3
  | .for l t it b u, hr => by
    simp only [regS, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
    have h1 := trE_oc C it
    have h2 := trT_oc C (forSrc l) [(l, C, C)] [.bind (fresh "v" l)] []
      (fun lt => by simpa [forSrc, PyCore.itemsE] using Oc.frc (C := C) "v" l (sub lt 63)) t (trE_oc C t)
    have h3 := trB_oc C b hr.1; have h4 := trB_oc C u hr.2
    simp only [trS, itemsS, forLoop]
    oc h1 h2 h3 h4 (Oc.frc (C := C) "i" l (sub l 1)) (Oc.frc (C := C) "i" l (sub l 18))
      (Oc.frc (C := C) "g" l (sub l 10)) (Oc.frc (C := C) "g" l (sub l 13))
      (Oc.frc (C := C) "v" l (sub l 15)) (Oc.frc (C := C) "s" l (sub l 19))
      (Oc.frc (C := C) "g" l (sub l 21))
  | .brk l, _ | .cont l, _ | .pass l, _ => by simp only [trS, itemsS]; oc Oc.nil
  | .ret l e, _ => by have h1 := trO_oc C l 1 e; simp only [trS, itemsS]; oc h1
  | .defn l f ps b ds r, hr => by
    simp only [regS, Option.isSome_none, Bool.false_or] at hr
    have h1 := trEs_oc C ds; have h2 := trDfs_oc C (.fn l f ps b :: C) ps
    have h3 := trAnns_oc C (.fn l f ps b :: C) ps
    have hk : Oc (ncPs C (.fn l f ps b :: C) ps) ((trAnnK C .pos ps ++ trAnnK C .posonly ps ++
          trAnnK C .vararg ps ++ trAnnK C .kwonly ps ++ trAnnK C .kwarg ps).flatMap PyCore.factsE) (itemsPs C ps) C
        ((trAnnK C .pos ps ++ trAnnK C .posonly ps ++ trAnnK C .vararg ps ++ trAnnK C .kwonly ps ++
          trAnnK C .kwarg ps).flatMap (PyCore.itemsE R0 (trChain C))) :=
      Oc.congr h3 (fun L x C' h => (flatMap_mem_iff (trAnnK_all C · ps) _).1 h) (fun _ h => h)
        (fun f h => (flatMap_mem_iff (trAnnK_all C · ps) f).2 h) (fun _ h => h)
    have hS := fc_scope_fn C l f ps b ds r
    have h4 := oc_param (.fn l f ps b :: C) ps
    have h5 := trB_oc (.fn l f ps b :: C) b hr
    have h6 : Oc (ncS C (.defn l f ps b ds r)) [] (itemsS C (.defn l f ps b ds r)) C
        (PyCore.itemsB R0 (trChain (.fn l f ps b :: C))
          (paramBind (.fn l f ps b :: C) ps ++ trB (.fn l f ps b :: C) b)) := by
      refine Oc.scope (Fb := (trScope C (.fn l f ps b)).facts) (Nb := [] ++ ncB (.fn l f ps b :: C) b)
          (Bb := paramOccs (.fn l f ps b :: C) ps ++ itemsB (.fn l f ps b :: C) b) hS (fun _ h => h) ?_ ?_ ?_
      · intro a ha; nc_simp at ha ⊢; grind
      · intro j hj; nc_simp at hj ⊢; grind
      · rw [pitemsB_append]
        refine Oc.congr (Oc.cat h4 h5) (fun _ _ _ h => h) (fun _ h => h) (fun f hf => ?_) (fun _ h => h)
        simp only [trScope, PyCore.Scope.facts, pfactsB_append, List.mem_cons, List.mem_append, List.nil_append] at hf ⊢
        exact .inr (.inr hf)
    have h7 := Oc.par (N := ncS C (.defn l f ps b ds r)) (B := itemsS C (.defn l f ps b ds r)) (.fn l f ps b) "a" l
      (.inl rfl) (by simp [trScope, PyCore.Scope.facts]) hS (by simp [ncS])
    have hu := Oc.usr (C := C) (sub l 0) (mangle (priv C) f) (trChain C) l C
    cases r with
    | none =>
      simp only [trS, itemsS, itemsO]; simp only [List.flatMap_append] at hk
      oc h1 h2 hk h6 h7 hu
    | some r =>
      have h8 := trE_oc C r
      simp only [trS, itemsS, itemsO]; simp only [List.flatMap_append] at hk
      oc h1 h2 hk h8 h6 h7 hu
  | .cls l x bs ks b ds, hr => by
    simp only [regS, Option.isSome_none, Bool.false_or] at hr
    have h1 := trEs_oc C ds; have h2 := trA_oc C bs; have h3 := trKs_oc C ks
    have hS := fc_scope_cl C l x bs ks b ds
    have h5 := trB_oc (.cl l x b :: C) b hr
    have h6 : Oc (ncS C (.cls l x bs ks b ds)) [] (itemsS C (.cls l x bs ks b ds)) C
        (PyCore.itemsB R0 (trChain (.cl l x b :: C)) (setupS l :: trB (.cl l x b :: C) b)) := by
      refine Oc.scope (Fb := (trScope C (.cl l x b)).facts) (Nb := ncB (.cl l x b :: C) b)
          (Bb := itemsB (.cl l x b :: C) b) hS (fun _ h => h) ?_ ?_ ?_
      · intro a ha; nc_simp at ha ⊢; grind
      · intro j hj; nc_simp at hj ⊢; grind
      · refine Oc.congr h5 (fun L y C' h => by simpa [PyCore.itemsB] using h) (fun _ h => h) (fun f hf => ?_)
          (fun _ h => h)
        simp only [trScope, PyCore.Scope.facts, PyCore.factsB, pfactsS_setupS, List.nil_append, List.mem_cons] at hf ⊢
        exact .inr (.inr hf)
    have hu := Oc.usr (C := C) (sub l 1) (mangle (priv C) x) (trChain C) l C
    have hi : Oc [] [] (itemsS C (.cls l x bs ks b ds)) C
        (PyCore.classImplicit.map fun y => .occ (sub l 1) y (trChain (.cl l x b :: C))) :=
      Oc.usr' fun L y C' h => by
        simp only [List.mem_map] at h; obtain ⟨y', hy, h⟩ := h; simp only [PyCore.Item.occ.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨l, .cl l x b :: C, by simp [itemsS, hy]⟩
    simp only [trS, itemsS]
    oc h1 h2 h3 h6 hu hi
  | .glob l xs, _ => by
    have := oc_names C l (fun x => .glob (sub l 1) x) (fun _ => rfl) (xs.map (mangle (priv C)))
    simp only [List.map_map, Function.comp_def] at this
    simp only [trS, itemsS]; oc this
  | .nonloc l xs, _ => by
    have := oc_names C l (fun x => .nonloc (sub l 1) x) (fun _ => rfl) (xs.map (mangle (priv C)))
    simp only [List.map_map, Function.comp_def] at this
    simp only [trS, itemsS]; oc this
  | .tryE l b hz u, hr => by
    simp only [regS, Option.isSome_none, Bool.false_or, Bool.and_eq_true] at hr
    have h1 := trB_oc C b hr.1.1; have h2 := trHs_oc C hz hr.1.2; have h3 := trB_oc C u hr.2
    simp only [trS, itemsS]; oc h1 h2 h3
  | .raise l none none, _ => by simp only [trS, itemsS, itemsO]; oc Oc.nil
  | .raise l (some e) none, _ => by have h1 := trE_oc C e; simp only [trS, itemsS, itemsO]; oc h1
  | .raise l (some e) (some c), _ => by
    have h1 := trE_oc C e; have h2 := trE_oc C c; simp only [trS, itemsS, itemsO]; oc h1 h2
  | .raise l none (some c), _ => by have h2 := trE_oc C c; simp only [trS, itemsS, itemsO]; oc h2
  | .imp l al, _ => by
    simp only [trS, itemsS, blk, PyCore.itemsS, PyCore.itemsHs, PyCore.itemsB, enone_s, Option.isSome_none,
      Bool.false_eq_true, ite_false, List.append_nil]
    refine Oc.congr (N := []) (F := []) (B := [] ++ (bindingAliases al).map fun a => .occ a.l (mangle (priv C) a.bound) C)
      ?_ (fun _ _ _ h => h) (by simp) (by simp) (by simp)
    refine oc_aliases C _ [] [] [] (fun a L x C' h => ?_) al
    split at h
    · simp [PyCore.itemsS, stuckAt] at h
    · rename_i hn; simp [PyCore.itemsS, PyCore.itemsE] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact .inl ⟨by simpa using hn, rfl⟩
  | .impFrom l m al lvl, _ => by
    simp only [trS, itemsS]
    split
    · refine Oc.congr (N := []) (F := []) (Oc.usr' fun L x C' h => ?_) (fun _ _ _ h => h) (by simp) (by simp)
        (fun _ h => h)
      simp only [blk, PyCore.itemsS, PyCore.itemsHs, PyCore.itemsB, enone_s, Option.isSome_none,
        Bool.false_eq_true, ite_false, List.append_nil, PyCore.itemsE, pitemsE_gad, List.flatMap_nil,
        List.nil_append, pitemsS_dead, pitemsB_map, List.mem_flatMap, List.mem_singleton,
        PyCore.Item.occ.injEq] at h
      obtain ⟨a, ha, rfl, rfl, rfl⟩ := h
      exact ⟨a.l, C, List.mem_map.mpr ⟨a, ha, rfl⟩⟩
    · simp only [blk, PyCore.itemsS, PyCore.itemsHs, PyCore.itemsB, enone_s, Option.isSome_none,
        Bool.false_eq_true, ite_false, List.append_nil, PyCore.itemsE, pitemsE_cc, List.flatMap_nil,
        List.nil_append, enone_e]
      have hm := Oc.frc (C := C) "m" l (sub l 1)
      refine Oc.congr (N := [(l, C, C)] ++ [(l, C, C)]) (F := [.bind (fresh "m" l)] ++ [.bind (fresh "m" l)])
        (B := [] ++ ([] ++ (bindingAliases al).map fun a => .occ a.l (mangle (priv C) a.bound) C))
        (Oc.cat hm ?_) (fun _ _ _ h => by simpa using h) (by simp [ncS]) ?_ (by simp)
      · refine oc_aliases C _ [(l, C, C)] [.bind (fresh "m" l)] [] (fun a L x C' h => ?_) al
        split at h
        · simp [PyCore.itemsS, PyCore.itemsE, nm] at h; obtain ⟨rfl, rfl, rfl⟩ := h
          exact .inr ((Oc.frc (C := C) "m" l (sub a.l 3)) (sub a.l 3) _ _ (by simp))
        · rename_i hn; simp [PyCore.itemsS, PyCore.itemsE, nm] at h
          rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
          · exact .inl ⟨by simpa using hn, rfl⟩
          · exact .inr ((Oc.frc (C := C) "m" l (sub a.l 3)) (sub a.l 3) _ _ (by simp))
      · intro f hf; simp only [List.mem_append, List.mem_singleton] at hf
        simp only [blk, PyCore.factsS, PyCore.factsHs, PyCore.factsB, PyCore.factsE, List.mem_append,
          List.mem_cons, List.append_nil]
        rcases hf with rfl | rfl <;> simp
  | .assert l t m, _ => by
    have h1 := trE_oc C t
    cases m with
    | none => simp only [trS, itemsS, itemsO]; oc h1
    | some m => have h2 := trE_oc C m; simp only [trS, itemsS, itemsO]; oc h1 h2
theorem trHs_oc (C : List Scope) : ∀ hs, regHs {} C hs = true →
    Oc (ncHs C hs) (PyCore.factsHs (trHs C hs)) (itemsHs C hs) C (PyCore.itemsHs R0 (trChain C) (trHs C hs))
  | [], _ => by simp only [trHs, itemsHs]; oc Oc.nil
  | .mk l ty x b :: hs, hr => by
    simp only [regHs, Bool.and_eq_true, Option.isSome_none, Bool.false_or] at hr
    have h2 := trB_oc C b hr.1; have h3 := trHs_oc C hs hr.2
    have hx : Oc [(l, C, C)] [.bind ((x.map (mangle (priv C))).getD (fresh "e" l))]
        (x.map fun x => Item.occ l (mangle (priv C) x) C).toList C
        [.occ (sub l 0) ((x.map (mangle (priv C))).getD (fresh "e" l)) (trChain C)] := by
      cases x with
      | none => exact Oc.frc (C := C) "e" l (sub l 0)
      | some x =>
        exact Oc.congr (Oc.usr (C := C) (sub l 0) (mangle (priv C) x) (trChain C) l C) (fun _ _ _ h => h)
          (by simp) (by simp) (by simp)
    cases ty with
    | none => simp only [trHs, itemsHs, itemsO]; oc h2 h3 hx
    | some t => have h1 := trE_oc C t; simp only [trHs, itemsHs, itemsO]; oc h1 h2 h3 hx
theorem trB_oc (C : List Scope) : ∀ ss, regB {} C ss = true →
    Oc (ncB C ss) (PyCore.factsB (trB C ss)) (itemsB C ss) C (PyCore.itemsB R0 (trChain C) (trB C ss))
  | [], _ => by simp only [trB, itemsB]; oc Oc.nil
  | s :: ss, hr => by
    simp only [regB, Bool.and_eq_true] at hr
    have h1 := trS_oc C s hr.1; have h2 := trB_oc C ss hr.2
    simp only [trB, itemsB]; oc h1 h2
end


/-! ## Fresh names determine their tags and labels -/

theorem app_digits : ∀ {A A' D D' : List Char}, (∀ c ∈ A, c.isDigit = false) → (∀ c ∈ A', c.isDigit = false) →
    (∀ c ∈ D, c.isDigit = true) → (∀ c ∈ D', c.isDigit = true) → D ≠ [] → D' ≠ [] →
    A ++ D = A' ++ D' → A = A' ∧ D = D'
  | [], [], _, _, _, _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | [], a' :: A', D, D', _, hA', hD, _, _, _, h => by
    simp only [List.nil_append, List.cons_append] at h
    have := hD a' (by rw [h]; simp)
    simp [hA' a' (by simp)] at this
  | a :: A, [], D, D', hA, _, _, hD', _, _, h => by
    simp only [List.nil_append, List.cons_append] at h
    have := hD' a (by rw [← h]; simp)
    simp [hA a (by simp)] at this
  | a :: A, a' :: A', D, D', hA, hA', hD, hD', hn, hn', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := app_digits (fun c hc => hA c (by simp [hc])) (fun c hc => hA' c (by simp [hc])) hD hD' hn hn' h
    exact ⟨by rw [this.1], this.2⟩

theorem toList_toString (l : Nat) : (toString l).toList = Nat.toDigits 10 l := Nat.toList_repr

/-- Fresh names with tags of no digit (all the translation uses) are distinct for distinct tags
or labels. -/
theorem fresh_inj' {t t' : String} {l l' : Label} (ht : NoDig t) (ht' : NoDig t') (h : fresh t l = fresh t' l') :
    t = t' ∧ l = l' := by
  have h1 := congrArg String.toList h
  simp [fresh, toList_toString] at h1
  have hd : ∀ n : Nat, ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true :=
    fun n c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  obtain ⟨h3, h4⟩ := app_digits ht ht' (hd l) (hd l') Nat.toDigits_ne_nil Nat.toDigits_ne_nil (by simpa using h1)
  refine ⟨String.ext h3, ?_⟩
  rw [← Nat.ofDigitChars_ten_toDigits (n := l), h4, Nat.ofDigitChars_ten_toDigits]

/-! ## Distinct labels: the pattern -/

theorem nc_uniq {N : NC} (hN : (N.map Prod.fst).Nodup) {l : Label} {a b : List Scope × List Scope}
    (ha : (l, a) ∈ N) (hb : (l, b) ∈ N) : a = b := by
  induction N with
  | nil => simp at ha
  | cons c N ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hN
    simp only [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [← ha] at hb; exact (Prod.mk.inj hb).2.symm
    · exact absurd ⟨_, hb, by rw [← ha]⟩ hN.1
    · exact absurd ⟨_, ha, by rw [← hb]⟩ hN.1
    · exact ih hN.2 ha hb

theorem okc_get {N : NC} {B : List Item} {C : List Scope} : ∀ (E : List Scope) (S : Scope) (D2 : List Scope),
    Okc N B C (E ++ S :: D2) → Fc N B (S :: D2 ++ C) (trScope (D2 ++ C) S).facts
  | [], _, _, h => h.1
  | _ :: E, S, D2, h => okc_get E S D2 h.2

theorem mem_trChain : ∀ (D : List Scope) (P : PyCore.Scope), P ∈ trChain D →
    ∃ E S D2, D = E ++ S :: D2 ∧ P = trScope D2 S
  | [], _, h => by simp [trChain] at h
  | S :: D, P, h => by
    simp only [trChain, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[], S, D, rfl, rfl⟩
    · obtain ⟨E, S', D2, rfl, rfl⟩ := mem_trChain D P h; exact ⟨S :: E, S', D2, rfl, rfl⟩

theorem cf {f : Fact} {A : List Fact} (h : f ∉ A) : A.contains f = false :=
  Bool.eq_false_iff.2 fun h' => h (mem_iff_contains.2 h')

/-- The fresh-name invariant of ⌊p⌋, for distinct labels, names of `p` with no dot, and augmented
targets that are names, attributes, or subscripts. -/
theorem fresh_canon (p : List Stmt) (hp : (labelsB p).Nodup) (hd : NoDot p) (hg : regB {} [] p = true) :
    FreshCanon (tr p) := by
  intro L x C' hi hx
  have hN : ((ncB [] p).map Prod.fst).Nodup := by rw [ncB_fst]; exact hp
  have hdot : ∀ l C1, Item.occ l x C1 ∉ itemsB [] p := fun l C1 hj => hd l x C1 hj (fresh_dot hx)
  have hi' : PyCore.Item.occ L x C' ∈ PyCore.itemsB R0 (trChain []) (trB [] p) := by
    simpa [tr, PyCore.itemsB, trChain] using hi
  rcases trB_oc [] p hg L x C' hi' with ⟨l, C1, hj⟩ | ⟨t, l0, D, co, ci, rfl, ht, rfl, he, hh, hb, hk⟩
  · exact absurd hj (hdot l C1)
  simp only [List.append_nil] at hh hb hk ⊢
  have key : ∀ E S D2, D = E ++ S :: D2 →
      (Fact.bind (fresh t l0) ∈ (trScope D2 S).facts → E = []) ∧
      Fact.wal (fresh t l0) ∉ (trScope D2 S).facts ∧
      Fact.glob (fresh t l0) ∉ (trScope D2 S).facts ∧ Fact.nonloc (fresh t l0) ∉ (trScope D2 S).facts := by
    intro E S D2 hD
    have hS := okc_get (C := []) E S D2 (by rw [← hD]; simpa using hk)
    simp only [List.append_nil] at hS
    refine ⟨fun hf => ?_, fun hf => ?_, fun hf => ?_, fun hf => ?_⟩
    · rcases hS _ hf with ⟨l', C1, hj⟩ | ⟨t', l0', co', ci', h1, h2, h3, h4⟩
      · exact absurd hj (hdot l' C1)
      · obtain ⟨rfl, rfl⟩ := fresh_inj' ht h2 h1
        obtain ⟨rfl, rfl⟩ : (co, ci) = (co', ci') := nc_uniq hN he h3
        rw [← hh, hD] at h4
        have := congrArg List.length h4
        simp only [List.length_cons, List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
    · obtain ⟨l', C1, hj⟩ := hS _ hf; exact hdot l' C1 hj
    · obtain ⟨l', C1, hj⟩ := hS _ hf; exact hdot l' C1 hj
    · obtain ⟨l', C1, hj⟩ := hS _ hf; exact hdot l' C1 hj
  cases D with
  | nil => rfl
  | cons S1 D1 =>
    simp only [Bnd, List.append_nil] at hb
    obtain ⟨-, h2, h3, h4⟩ := key [] S1 D1 rfl
    simp only [trChain, List.map_cons, patB]
    congr 1
    · simp only [xf, cf h2, cf h3, cf h4, mem_iff_contains.1 hb]
    · refine List.map_congr_left fun P hP => ?_
      obtain ⟨E, S, D2, rfl, rfl⟩ := mem_trChain D1 P hP
      obtain ⟨h1, h2, h3, h4⟩ := key (S1 :: E) S D2 (by simp)
      have hb' : Fact.bind (fresh t l0) ∉ (trScope D2 S).facts := fun h => by simpa using h1 h
      simp only [xf, cf hb', cf h2, cf h3, cf h4, none4]

/-- Theorem 5 for ⌊p⌋ and ⌊q⌋, `q = editB R p`, with the image of F_surf(p, q): if the run of ⌊p⌋
evaluates no node made for a node of F_surf, ⌊p⌋ and ⌊q⌋ end alike and diverge alike. The
conditions on the edit: the labels of `p` and of `q` are distinct and none of `p`'s is 0 (the
exporter labels from 1), no name of `p` or `q` starts with a dot, every generator expression of
`p` has one element, each expression replacement keeps its site's label, and the augmented targets
of `p` and `q` (`regB {}`), and those outside the sites with their replacements (`regB R`), are
names, attributes, or subscripts: all of which every program CPython parses satisfies. -/
theorem footprint_theorem_surf {S : Type} (I : Py.Interp S) (R : Edit) (p : List Stmt) (σ : Name → Option PyCore.Val) (s : S)
    (hp : (labelsB p).Nodup) (hq : (labelsB (editB R p)).Nodup) (h0 : 0 ∉ labelsB p) (hd : NoDot p)
    (hdq : NoDot (editB R p)) (hg : GenOk p) (hk : KeepsLabels R) (hr : regB R [] p = true)
    (hgp : regB {} [] p = true) (hgq : regB {} [] (editB R p) = true)
    (h : PyCore.NoReach I (imgF R p) (PyCore.init (tr p) σ s)) :
    (∀ o, PyCore.Terminates I (PyCore.init (tr p) σ s) o ↔ PyCore.Terminates I (PyCore.init (tr (editB R p)) σ s) o) ∧
    (PyCore.Diverges I (PyCore.init (tr p) σ s) ↔ PyCore.Diverges I (PyCore.init (tr (editB R p)) σ s)) :=
  footprint_theorem_surf_canon I R p σ s hp h0 hd hg hk hr (fresh_canon p hp hd hgp)
    (fresh_canon (editB R p) hq hdq hgq) h

end Surf
