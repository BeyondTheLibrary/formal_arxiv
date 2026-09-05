import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.Thm94ClosingKnot
import Workspace.ProofLemmas.Thm94ClosingStriation

/-!
# Copying one strip end across every antistrip in 9.4
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm94ClosingCopy

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem mem_iff_of_rev {l l' : List V} (h : l' = l ∨ l' = l.reverse) (v : V) :
    v ∈ l' ↔ v ∈ l := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact List.mem_reverse

private theorem exists_rung {G : SimpleGraph V} {R : Set V × Set V × Set V}
    (h : IsStrip G R) : ∃ p : List V, IsSRung G R p := by
  obtain ⟨A, C, B⟩ := R
  obtain ⟨a, ha⟩ := h.2.2.2.1
  obtain ⟨p, hp, -⟩ := h.2.2.2.2.2 a (Set.mem_union_left _ (Set.mem_union_left _ ha))
  exact ⟨p, hp⟩

private theorem end_eq_of_same_path {G : SimpleGraph V} {p : List V} {a b c d : V}
    (h : IsPathFrom G p a b) (h' : IsPathFrom G p c d) : a = c ∧ b = d := by
  constructor
  · exact Option.some.inj (h.2.1.symm.trans h'.2.1)
  · exact Option.some.inj (h.2.2.symm.trans h'.2.2)

/-- **PAPER (9.4, printed p. 52):** after one nonadjacent pair in `X` is fixed, repeated uses of
9.3.2 show that `f` has the same neighbours on every antistrip as one end of the chosen rung.

The first disjunct is the paper's orientation (`a` is copied).  The second is its reversal. -/
theorem copy_one_end_on_all_antistrips {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {f u w a b : V} {i : Fin m} {j : Fin n} {P Q : List V}
    (hG : Berge G)
    (hnoenl : ¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' φ)
    (hnoovercompl : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' φ)
    (hL : IsStriation G S T) (hfL : f ∉ striationVertices S T)
    (hanti : ∀ (k : Fin n) (R : List V), IsSRung Gᶜ (T k) R →
      ∃ v ∈ R, v ∉ G.neighborSet f ∩ striationVertices S T)
    (hone : ∀ k k' : Fin m,
      ((G.neighborSet f ∩ striationVertices S T) ∩ stripVertices (S k)).Nonempty →
      ((G.neighborSet f ∩ striationVertices S T) ∩ stripVertices (S k')).Nonempty → k = k')
    (hP : IsSRung G (S i) P) (hPab : IsPathFrom G P a b)
    (hQ : IsSRung Gᶜ (T j) Q) (huP : u ∈ P) (hwQ : w ∈ Q)
    (hfu : G.Adj f u) (hfw : G.Adj f w) (huw : ¬ G.Adj u w) :
    ((∃ p ∈ ({v : V | v ∈ P} \ {a} : Set V), G.Adj f p) ∧
      ∀ k : Fin n, ∀ z ∈ stripVertices (T k), (G.Adj f z ↔ G.Adj a z)) ∨
    ((∃ p ∈ ({v : V | v ∈ P} \ {b} : Set V), G.Adj f p) ∧
      ∀ k : Fin n, ∀ z ∈ stripVertices (T k), (G.Adj f z ↔ G.Adj b z)) := by
  classical
  have hXi : ((G.neighborSet f ∩ striationVertices S T) ∩ stripVertices (S i)).Nonempty := by
    refine ⟨u, ⟨hfu, ?_⟩, KnotFromTwist.mem_stripVertices_of_isSRung hP huP⟩
    exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i,
      KnotFromTwist.mem_stripVertices_of_isSRung hP huP⟩)
  have no_second : ∀ {i' : Fin m} (hii' : i ≠ i') {R R' : List V},
      IsSRung G (S i') R → (R' = R ∨ R' = R.reverse) → ∀ z ∈ R', ¬ G.Adj f z := by
    intro i' hii' R R' hR hrev z hz hadj
    have hzR : z ∈ R := (mem_iff_of_rev hrev z).mp hz
    have hzS : z ∈ stripVertices (S i') :=
      KnotFromTwist.mem_stripVertices_of_isSRung hR hzR
    have hzL : z ∈ striationVertices S T :=
      Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i', hzS⟩)
    have hXi' : ((G.neighborSet f ∩ striationVertices S T) ∩
        stripVertices (S i')).Nonempty := ⟨z, ⟨hadj, hzL⟩, hzS⟩
    exact hii' (hone i i' hXi hXi')
  have outside_knot : ∀ {i' : Fin m} {j₁ j₂ : Fin n} {P₂ Q₁ Q₂ P₁' P₂' Q₁' Q₂' : List V},
      IsSRung G (S i') P₂ → IsSRung Gᶜ (T j₁) Q₁ → IsSRung Gᶜ (T j₂) Q₂ →
      (P₁' = P ∨ P₁' = P.reverse) → (P₂' = P₂ ∨ P₂' = P₂.reverse) →
      (Q₁' = Q₁ ∨ Q₁' = Q₁.reverse) → (Q₂' = Q₂ ∨ Q₂' = Q₂.reverse) →
      f ∉ ({v : V | v ∈ P₁'} ∪ {v : V | v ∈ P₂'} ∪ {v : V | v ∈ Q₁'} ∪
        {v : V | v ∈ Q₂'} : Set V) := by
    intro i' j₁ j₂ P₂ Q₁ Q₂ P₁' P₂' Q₁' Q₂' hP₂ hQ₁ hQ₂ rP₁ rP₂ rQ₁ rQ₂ hmem
    apply hfL
    rcases hmem with ((hp | hp) | hq) | hq
    · exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i,
        KnotFromTwist.mem_stripVertices_of_isSRung hP ((mem_iff_of_rev rP₁ f).mp hp)⟩)
    · exact Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i',
        KnotFromTwist.mem_stripVertices_of_isSRung hP₂ ((mem_iff_of_rev rP₂ f).mp hp)⟩)
    · exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j₁,
        KnotFromTwist.mem_stripVertices_of_isSRung hQ₁ ((mem_iff_of_rev rQ₁ f).mp hq)⟩)
    · exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j₂,
        KnotFromTwist.mem_stripVertices_of_isSRung hQ₂ ((mem_iff_of_rev rQ₂ f).mp hq)⟩)
  have normalized_nonneighbor : ∀ {k : Fin n} {R R' : List V},
      IsSRung Gᶜ (T k) R → (R' = R ∨ R' = R.reverse) → ∃ z ∈ R', ¬ G.Adj f z := by
    intro k R R' hR hrev
    obtain ⟨z, hzR, hznot⟩ := hanti k R hR
    refine ⟨z, (mem_iff_of_rev hrev z).mpr hzR, ?_⟩
    intro hadj
    apply hznot
    refine ⟨hadj, Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨k, ?_⟩)⟩
    exact KnotFromTwist.mem_stripVertices_of_isSRung hR hzR
  have hn2 : 2 ≤ n := hL.2.2.2.2.2.2.2.2.1
  obtain ⟨j', hjj'⟩ : ∃ j' : Fin n, j ≠ j' := by
    by_cases hj : (j : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have : (j : ℕ) = 1 := congrArg Fin.val h
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      exact hj (congrArg Fin.val h)
  obtain ⟨Q', hQ'⟩ := exists_rung (hL.2.1 j' : IsStrip Gᶜ (T j'))
  obtain ⟨i', hii', htw⟩ :=
    Thm94ClosingStriation.exists_twist_with_fixed_strip hL i hjj'
  obtain ⟨P₂, hP₂⟩ := exists_rung (hL.1 i')
  obtain ⟨P₁n, P₂n, Q₁n, Q₂n, rP₁, rP₂, rQ₁, rQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hii' hjj' htw hP hP₂ hQ hQ'
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hp₁, hp₂, hq₁, hq₂,
    -, -, -, -, -, -, -, -, -, -, -, -, E11, -, -, -, -, -, -, -⟩ := id hknot
  have hfirst : (a₁ = a ∧ b₁ = b) ∨ (a₁ = b ∧ b₁ = a) := by
    rcases rP₁ with rfl | rfl
    · have h := end_eq_of_same_path hp₁ hPab
      exact Or.inl h
    · have h := end_eq_of_same_path hp₁ (PathBasics.isPathFrom_reverse hPab)
      exact Or.inr h
  have hbadn : ∃ p ∈ P₁n, ∃ q ∈ Q₁n, G.Adj f p ∧ G.Adj f q ∧ ¬ G.Adj p q :=
    ⟨u, (mem_iff_of_rev rP₁ u).mpr huP, w, (mem_iff_of_rev rQ₁ w).mpr hwQ, hfu, hfw, huw⟩
  have hcopy0 := Thm94ClosingKnot.singleton_forces_end_copy hG P₁n P₂n Q₁n Q₂n
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ f hknot hp₁ hp₂ hq₁ hq₂ hnoenl hnoover hnoovercompl
    (outside_knot hP₂ hQ hQ' rP₁ rP₂ rQ₁ rQ₂) hbadn
    (no_second hii' hP₂ rP₂) (normalized_nonneighbor hQ rQ₁)
    (normalized_nonneighbor hQ' rQ₂)
  obtain ⟨side, hside, hnear, hmatchQ, hmatchQ', hsideab⟩ : ∃ side : V,
      (side = a₁ ∨ side = b₁) ∧
      (∃ p ∈ ({v : V | v ∈ P} \ {side} : Set V), G.Adj f p) ∧
      (∀ z ∈ Q, G.Adj f z ↔ G.Adj side z) ∧
      (∀ z ∈ Q', G.Adj f z ↔ G.Adj side z) ∧ (side = a ∨ side = b) := by
    rcases hcopy0 with ⟨hnear, hmatch⟩ | ⟨hnear, hmatch⟩
    · refine ⟨a₁, Or.inl rfl, ?_, ?_, ?_, ?_⟩
      · obtain ⟨p, hp, hadj⟩ := hnear
        exact ⟨p, ⟨(mem_iff_of_rev rP₁ p).mp hp.1, hp.2⟩, hadj⟩
      · intro z hz
        exact hmatch z (Or.inl ((mem_iff_of_rev rQ₁ z).mpr hz))
      · intro z hz
        exact hmatch z (Or.inr ((mem_iff_of_rev rQ₂ z).mpr hz))
      · rcases hfirst with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
    · refine ⟨b₁, Or.inr rfl, ?_, ?_, ?_, ?_⟩
      · obtain ⟨p, hp, hadj⟩ := hnear
        exact ⟨p, ⟨(mem_iff_of_rev rP₁ p).mp hp.1, hp.2⟩, hadj⟩
      · intro z hz
        exact hmatch z (Or.inl ((mem_iff_of_rev rQ₁ z).mpr hz))
      · intro z hz
        exact hmatch z (Or.inr ((mem_iff_of_rev rQ₂ z).mpr hz))
      · rcases hfirst with h | h
        · exact Or.inr h.2
        · exact Or.inl h.2
  have propagate : ∀ {jb jt : Fin n} (hbt : jb ≠ jt) {Qb Qt : List V},
      IsSRung Gᶜ (T jb) Qb → IsSRung Gᶜ (T jt) Qt →
      (∀ z ∈ Qb, G.Adj f z ↔ G.Adj side z) →
      ∀ z ∈ Qt, G.Adj f z ↔ G.Adj side z := by
    intro jb jt hbt Qb Qt hQb hQt hmatchb
    obtain ⟨it, hiit, htwi⟩ :=
      Thm94ClosingStriation.exists_twist_with_fixed_strip hL i hbt
    obtain ⟨Pt, hPt⟩ := exists_rung (hL.1 it)
    obtain ⟨P1, P2, Q1, Q2, rP1, rP2, rQ1, rQ2, hkn⟩ :=
      KnotFromTwist.exists_knot_of_twist hL hiit hbt htwi hP hPt hQb hQt
    obtain ⟨c, d, c2, d2, x, y, x2, y2, hp1', hp2', hq1', hq2',
      -, -, -, -, -, -, lc, -, lx, -, -, -, EE, -, -, -, -, -, -, -⟩ := id hkn
    have hcd : c ≠ d := PathBasics.isPathFrom_ends_ne hp1' lc
    have hxy : x ≠ y := PathBasics.isPathFrom_ends_ne hq1' lx
    have hsidecd : side = c ∨ side = d := by
      rcases rP1 with rfl | rfl
      · have he := end_eq_of_same_path hp1' hPab
        rcases hsideab with rfl | rfl
        · exact Or.inl he.1.symm
        · exact Or.inr he.2.symm
      · have he := end_eq_of_same_path hp1' (PathBasics.isPathFrom_reverse hPab)
        rcases hsideab with rfl | rfl
        · exact Or.inr he.2.symm
        · exact Or.inl he.1.symm
    obtain ⟨p, hpP, hfp⟩ := hnear
    have hpP1 : p ∈ P1 := (mem_iff_of_rev rP1 p).mpr hpP.1
    have hxQ1 : x ∈ Q1 := (PathBasics.isPathFrom_ends_mem hq1').1
    have hyQ1 : y ∈ Q1 := (PathBasics.isPathFrom_ends_mem hq1').2
    have hbad1 : ∃ p ∈ P1, ∃ q ∈ Q1, G.Adj f p ∧ G.Adj f q ∧ ¬ G.Adj p q := by
      rcases hsidecd with hs | hs
      · refine ⟨p, hpP1, x, hxQ1, hfp, ?_, ?_⟩
        · exact (hmatchb x ((mem_iff_of_rev rQ1 x).mp hxQ1)).2
            (hs ▸ (EE c (PathBasics.isPathFrom_ends_mem hp1').1 x (by simp)).2
              (Or.inl ⟨rfl, rfl⟩))
        · intro hadj
          rcases (EE p hpP1 x (by simp)).1 hadj with ⟨hpc, -⟩ | ⟨hpd, hxy'⟩
          · exact hpP.2 (hpc.trans hs.symm)
          · exact hxy hxy'
      · refine ⟨p, hpP1, y, hyQ1, hfp, ?_, ?_⟩
        · exact (hmatchb y ((mem_iff_of_rev rQ1 y).mp hyQ1)).2
            (hs ▸ (EE d (PathBasics.isPathFrom_ends_mem hp1').2 y (by simp)).2
              (Or.inr ⟨rfl, rfl⟩))
        · intro hadj
          rcases (EE p hpP1 y (by simp)).1 hadj with ⟨hpc, hyx⟩ | ⟨hpd, -⟩
          · exact hxy hyx.symm
          · exact hpP.2 (hpd.trans hs.symm)
    have hres := Thm94ClosingKnot.singleton_forces_end_copy hG P1 P2 Q1 Q2
      c d c2 d2 x y x2 y2 f hkn hp1' hp2' hq1' hq2' hnoenl hnoover hnoovercompl
      (outside_knot hPt hQb hQt rP1 rP2 rQ1 rQ2) hbad1
      (no_second hiit hPt rP2) (normalized_nonneighbor hQb rQ1)
      (normalized_nonneighbor hQt rQ2)
    intro z hz
    have hzQ2 : z ∈ Q2 := (mem_iff_of_rev rQ2 z).mpr hz
    rcases hsidecd with hs | hs
    · rcases hres with ⟨-, hm⟩ | ⟨-, hm⟩
      · simpa only [hs] using hm z (Or.inr hzQ2)
      · have hfx : G.Adj f x := (hmatchb x ((mem_iff_of_rev rQ1 x).mp hxQ1)).2
            (hs ▸ (EE c (PathBasics.isPathFrom_ends_mem hp1').1 x (by simp)).2
              (Or.inl ⟨rfl, rfl⟩))
        have hdx : ¬ G.Adj d x := by
          intro hdx
          rcases (EE d (PathBasics.isPathFrom_ends_mem hp1').2 x (by simp)).1 hdx with
            ⟨hdc, -⟩ | ⟨-, hxy'⟩
          · exact hcd hdc.symm
          · exact hxy hxy'
        exact (hdx ((hm x (Or.inl hxQ1)).1 hfx)).elim
    · rcases hres with ⟨-, hm⟩ | ⟨-, hm⟩
      · have hfy : G.Adj f y := (hmatchb y ((mem_iff_of_rev rQ1 y).mp hyQ1)).2
            (hs ▸ (EE d (PathBasics.isPathFrom_ends_mem hp1').2 y (by simp)).2
              (Or.inr ⟨rfl, rfl⟩))
        have hcy : ¬ G.Adj c y := by
          intro hcy
          rcases (EE c (PathBasics.isPathFrom_ends_mem hp1').1 y (by simp)).1 hcy with
            ⟨-, hyx⟩ | ⟨hcd', -⟩
          · exact hxy hyx.symm
          · exact hcd hcd'
        exact (hcy ((hm y (Or.inl hyQ1)).1 hfy)).elim
      · simpa only [hs] using hm z (Or.inr hzQ2)
  have hall : ∀ k : Fin n, ∀ z ∈ stripVertices (T k), G.Adj f z ↔ G.Adj side z := by
    intro k z hz
    obtain ⟨R, hR, hzR⟩ := hL.2.1 k |>.2.2.2.2.2 z hz
    by_cases hkj : k = j
    · subst k
      exact propagate hjj'.symm hQ' hR hmatchQ' z hzR
    · exact propagate (Ne.symm hkj) hQ hR hmatchQ z hzR
  rcases hsideab with hs | hs
  · subst side
    exact Or.inl ⟨hnear, hall⟩
  · subst side
    exact Or.inr ⟨hnear, hall⟩

end Workspace.ProofLemmas.Thm94ClosingCopy
