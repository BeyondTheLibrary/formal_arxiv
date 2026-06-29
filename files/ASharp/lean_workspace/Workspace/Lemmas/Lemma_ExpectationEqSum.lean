import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Workspace.Types.FractionalCover
import Workspace.Definitions.ProbDistributions

open BigOperators
open Workspace.Types.FractionalCover
open Workspace.Definitions.ProbDistributions
open Finset

namespace Workspace.Lemmas.ExpectationEqSum

/-- The expectation of ∑_W w(W) q'^|W| equals ∑_W w(W) q'^|W| by linearity.
    This is a standard fact from linearity of expectation.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
theorem expectation_eq_sum {X : Type} [Fintype X] [DecidableEq X]
    (cov : FractionalCover X (∅ : Set (Finset X))) (q' : ℝ)
    (hq'_pos : 0 ≤ q') (hq'_le_one : q' ≤ 1) :
    (∑ W : Finset X, cov.w W * q' ^ W.card) =
    ∑ W : Finset X, (∑ W' ∈ W.powerset, cov.w W') *
      (q' ^ W.card * (1 - q') ^ (Fintype.card X - W.card)) := by
  -- We prove RHS = LHS, working from the right-hand side.
  symm
  -- Step 1: Distribute the multiplication into the inner sum.
  simp_rw [Finset.sum_mul]
  -- Step 2: Exchange the order of summation.
  rw [Finset.sum_comm' (s := Finset.univ) (t := fun W : Finset X => W.powerset)
      (s' := fun W' : Finset X => Finset.univ.filter (fun W : Finset X => W' ⊆ W))
      (t' := Finset.univ)
      (h := by
        intro W W'
        simp only [Finset.mem_univ, true_and, Finset.mem_powerset, Finset.mem_filter]
        tauto)]
  -- Now goal: ∑ W' ∈ univ, ∑ W ∈ filter (W' ⊆ ·) univ, cov.w W' * (q'^|W| * (1-q')^(|X|-|W|))
  --        = ∑ W : Finset X, cov.w W * q' ^ W.card
  refine Finset.sum_congr rfl ?_
  intro W' _
  -- Pull cov.w W' out of the inner sum
  rw [← Finset.mul_sum]
  -- Now: cov.w W' * (∑_{W ⊇ W'} q'^|W| * (1-q')^(|X|-|W|)) = cov.w W' * q'^|W'|
  congr 1
  -- Inner sum: ∑_{W ⊇ W'} q'^|W| * (1-q')^(|X|-|W|) = q'^|W'|
  -- Bijection W ↔ S where W = W' ∪ S and S ⊆ W'ᶜ
  have key : (∑ W ∈ Finset.univ.filter (fun W : Finset X => W' ⊆ W),
                q' ^ W.card * (1 - q') ^ (Fintype.card X - W.card)) =
             ∑ S ∈ (W'ᶜ : Finset X).powerset,
                q' ^ (W' ∪ S).card * (1 - q') ^ (Fintype.card X - (W' ∪ S).card) := by
    refine Finset.sum_nbij' (i := fun W => W \ W') (j := fun S => W' ∪ S) ?_ ?_ ?_ ?_ ?_
    · -- (W \ W') ∈ (W'ᶜ).powerset
      intro W _
      rw [Finset.mem_powerset]
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      simp only [Finset.mem_compl]
      exact hx.2
    · -- (W' ∪ S) ∈ filter (W' ⊆ ·) univ
      intro S _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.subset_union_left
    · -- left inverse: (W' ∪ (W \ W')) = W when W' ⊆ W
      intro W hW
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (h | h)
        · exact hW h
        · exact h.1
      · intro h
        by_cases h' : x ∈ W'
        · exact Or.inl h'
        · exact Or.inr ⟨h, h'⟩
    · -- right inverse: ((W' ∪ S) \ W') = S when S ⊆ W'ᶜ
      intro S hS
      rw [Finset.mem_powerset] at hS
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 h2
        · exact h1
      · intro h
        have hxnotW' : x ∉ W' := by
          have := hS h
          simp only [Finset.mem_compl] at this
          exact this
        exact ⟨Or.inr h, hxnotW'⟩
    · -- f W = f' (W \ W')
      intro W hW
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
      have hUnion : W' ∪ (W \ W') = W := by
        ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (h | h)
          · exact hW h
          · exact h.1
        · intro h
          by_cases h' : x ∈ W'
          · exact Or.inl h'
          · exact Or.inr ⟨h, h'⟩
      rw [hUnion]
  rw [key]
  -- Now use card and pow manipulation:
  have hcard : ∀ S ∈ (W'ᶜ : Finset X).powerset,
      (W' ∪ S).card = W'.card + S.card := by
    intro S hS
    have hS_sub : S ⊆ W'ᶜ := Finset.mem_powerset.mp hS
    have hdisj : Disjoint W' S :=
      Finset.disjoint_of_subset_right hS_sub disjoint_compl_right
    exact Finset.card_union_of_disjoint hdisj
  have hcard_compl : (W'ᶜ : Finset X).card = Fintype.card X - W'.card :=
    Finset.card_compl W'
  have hW'card : W'.card ≤ Fintype.card X := by
    calc W'.card ≤ (Finset.univ : Finset X).card :=
            Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card X := Finset.card_univ
  -- Rewrite: ∑_{S} q'^|W' ∪ S| · (1-q')^(|X| - |W' ∪ S|)
  --        = ∑_{S} q'^|W'| · (q'^|S| · (1-q')^(|W'ᶜ| - |S|))
  have step : (∑ S ∈ (W'ᶜ : Finset X).powerset,
                q' ^ (W' ∪ S).card * (1 - q') ^ (Fintype.card X - (W' ∪ S).card)) =
              q' ^ W'.card * ∑ S ∈ (W'ᶜ : Finset X).powerset,
                q' ^ S.card * (1 - q') ^ ((W'ᶜ : Finset X).card - S.card) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro S hS
    rw [hcard S hS]
    have hScard : S.card ≤ (W'ᶜ : Finset X).card :=
      Finset.card_le_card (Finset.mem_powerset.mp hS)
    -- q' ^ (|W'| + |S|) * (1 - q') ^ (|X| - (|W'| + |S|))
    -- = q' ^ |W'| * (q' ^ |S| * (1 - q') ^ (|W'ᶜ| - |S|))
    rw [pow_add, mul_assoc]
    have hScard' : S.card ≤ Fintype.card X - W'.card := by
      rw [Finset.card_compl] at hScard
      exact hScard
    -- We have: hW'card : #W' ≤ Fintype.card X
    --          hScard' : #S ≤ Fintype.card X - #W'
    -- Hence #S + #W' ≤ Fintype.card X (using hW'card to avoid nat subtraction issue)
    have hSWcard : S.card + W'.card ≤ Fintype.card X := by
      have hW := hW'card
      have hS := hScard'
      omega
    have hExp : Fintype.card X - (W'.card + S.card) =
                (W'ᶜ : Finset X).card - S.card := by
      rw [hcard_compl]
      omega
    rw [hExp]
  rw [step]
  -- Now ∑ S ∈ W'ᶜ.powerset, q'^|S| * (1-q')^(|W'ᶜ| - |S|) = (q' + (1-q'))^|W'ᶜ| = 1
  rw [Finset.sum_pow_mul_eq_add_pow]
  have hsum : q' + (1 - q') = 1 := by ring
  rw [hsum, one_pow, mul_one]

end Workspace.Lemmas.ExpectationEqSum
