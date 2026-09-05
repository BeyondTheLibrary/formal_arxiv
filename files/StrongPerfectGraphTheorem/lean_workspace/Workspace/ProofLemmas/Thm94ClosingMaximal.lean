import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots

/-!
# Maximality bookkeeping for the closing paragraph of 9.4
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm94ClosingMaximal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem complete_symm {G : SimpleGraph V} {X Y : Set V} (h : Complete G X Y) :
    Complete G Y X := fun y hy x hx => (h x hx y hy).symm

private theorem anticomplete_symm {G : SimpleGraph V} {X Y : Set V} (h : Anticomplete G X Y) :
    Anticomplete G Y X := fun y hy x hx hadj => h x hx y hy hadj.symm

private theorem isTwist_mono {G : SimpleGraph V}
    {S₁ S₂ S₁' S₂' T₁ T₂ : Set V × Set V × Set V}
    (p11 : ParallelStripAntistrip G S₁ T₁ → ParallelStripAntistrip G S₁' T₁)
    (p12 : ParallelStripAntistrip G S₁ T₂ → ParallelStripAntistrip G S₁' T₂)
    (p21 : ParallelStripAntistrip G S₂ T₁ → ParallelStripAntistrip G S₂' T₁)
    (p22 : ParallelStripAntistrip G S₂ T₂ → ParallelStripAntistrip G S₂' T₂)
    (c11 : CoParallel G S₁ T₁ → CoParallel G S₁' T₁)
    (c12 : CoParallel G S₁ T₂ → CoParallel G S₁' T₂)
    (c21 : CoParallel G S₂ T₁ → CoParallel G S₂' T₁)
    (c22 : CoParallel G S₂ T₂ → CoParallel G S₂' T₂)
    (h : IsTwist G S₁ S₂ T₁ T₂) : IsTwist G S₁' S₂' T₁ T₂ := by
  rcases h with ⟨hag, hdis⟩ | ⟨hag, hdis⟩
  · rcases hag with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hdis with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inl ⟨Or.inl ⟨p11 h1, p21 h2⟩, Or.inl ⟨p12 h3, c22 h4⟩⟩
    · exact Or.inl ⟨Or.inl ⟨p11 h1, p21 h2⟩, Or.inr ⟨c12 h3, p22 h4⟩⟩
    · exact Or.inl ⟨Or.inr ⟨c11 h1, c21 h2⟩, Or.inl ⟨p12 h3, c22 h4⟩⟩
    · exact Or.inl ⟨Or.inr ⟨c11 h1, c21 h2⟩, Or.inr ⟨c12 h3, p22 h4⟩⟩
  · rcases hag with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hdis with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Or.inr ⟨Or.inl ⟨p12 h1, p22 h2⟩, Or.inl ⟨p11 h3, c21 h4⟩⟩
    · exact Or.inr ⟨Or.inl ⟨p12 h1, p22 h2⟩, Or.inr ⟨c11 h3, p21 h4⟩⟩
    · exact Or.inr ⟨Or.inr ⟨c12 h1, c22 h2⟩, Or.inl ⟨p11 h3, c21 h4⟩⟩
    · exact Or.inr ⟨Or.inr ⟨c12 h1, c22 h2⟩, Or.inr ⟨c11 h3, p21 h4⟩⟩

/-- Replacing one strip by a larger strip with the same incidence pattern gives a larger
striation.  This is the bookkeeping in the last sentence of 9.4, where maximality supplies the
contradiction. -/
theorem replacement_contradicts_maximality {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hmax : MaximalStriation G S T) {f : V} (hfL : f ∉ striationVertices S T)
    (i : Fin m) (R : Set V × Set V × Set V) (hR : IsStrip G R)
    (hverts : stripVertices R = stripVertices (S i) ∪ {f})
    (hoddR : ∀ p : List V, IsSRung G R p → Odd (pathLength p))
    (hfanti : ∀ k : Fin m, i ≠ k → VertexAnticomplete G f (stripVertices (S k)))
    (hpar : ∀ j : Fin n, ParallelStripAntistrip G (S i) (T j) →
      ParallelStripAntistrip G R (T j))
    (hco : ∀ j : Fin n, CoParallel G (S i) (T j) → CoParallel G R (T j)) : False := by
  classical
  let S' : Fin m → Set V × Set V × Set V := Function.update S i R
  obtain ⟨hstripS, hstripT, hdisjS, hdisjT, hdisjST, hoddS, hoddT, hm, hn,
    hantiS, hcompT, hrel, htwS, htwT⟩ := hmax.1
  have hSi : S' i = R := by simp [S']
  have hSk : ∀ k : Fin m, k ≠ i → S' k = S k := by
    intro k hki
    simp [S', hki]
  have hfnotS : ∀ k : Fin m, f ∉ stripVertices (S k) := by
    intro k hmem
    exact hfL (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨k, hmem⟩))
  have hfnotT : ∀ j : Fin n, f ∉ stripVertices (T j) := by
    intro j hmem
    exact hfL (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, hmem⟩))
  have hRdisjS : ∀ k : Fin m, i ≠ k →
      Disjoint (stripVertices R) (stripVertices (S k)) := by
    intro k hik
    rw [hverts]
    exact Set.disjoint_union_left.mpr
      ⟨hdisjS i k hik, Set.disjoint_singleton_left.mpr (hfnotS k)⟩
  have hRdisjT : ∀ j : Fin n, Disjoint (stripVertices R) (stripVertices (T j)) := by
    intro j
    rw [hverts]
    exact Set.disjoint_union_left.mpr
      ⟨hdisjST i j, Set.disjoint_singleton_left.mpr (hfnotT j)⟩
  have hRantiS : ∀ k : Fin m, i ≠ k →
      Anticomplete G (stripVertices R) (stripVertices (S k)) := by
    intro k hik
    have hold : Anticomplete G (stripVertices (S i)) (stripVertices (S k)) := by
      rcases lt_trichotomy i k with hlt | heq | hgt
      · exact hantiS i k hlt
      · exact absurd heq hik
      · exact anticomplete_symm (hantiS k i hgt)
    rw [hverts]
    intro x hx y hy
    rcases hx with hx | rfl
    · exact hold x hx y hy
    · exact hfanti k hik y hy
  have hPmap : ∀ k : Fin m, ∀ j : Fin n,
      ParallelStripAntistrip G (S k) (T j) → ParallelStripAntistrip G (S' k) (T j) := by
    intro k j h
    by_cases hki : k = i
    · subst k
      rw [hSi]
      exact hpar j h
    · rw [hSk k hki]
      exact h
  have hCmap : ∀ k : Fin m, ∀ j : Fin n,
      CoParallel G (S k) (T j) → CoParallel G (S' k) (T j) := by
    intro k j h
    by_cases hki : k = i
    · subst k
      rw [hSi]
      exact hco j h
    · rw [hSk k hki]
      exact h
  have hnew : IsStriation G S' T := by
    refine ⟨?_, hstripT, ?_, hdisjT, ?_, ?_, hoddT, hm, hn, ?_, hcompT, ?_, ?_, ?_⟩
    · intro k
      by_cases hki : k = i
      · subst k
        rwa [hSi]
      · rw [hSk k hki]
        exact hstripS k
    · intro k k' hkk'
      by_cases hki : k = i
      · subst k
        rw [hSi, hSk k' (Ne.symm hkk')]
        exact hRdisjS k' hkk'
      · by_cases hk'i : k' = i
        · subst k'
          rw [hSk k hki, hSi]
          exact (hRdisjS k (Ne.symm hki)).symm
        · rw [hSk k hki, hSk k' hk'i]
          exact hdisjS k k' hkk'
    · intro k j
      by_cases hki : k = i
      · subst k
        rw [hSi]
        exact hRdisjT j
      · rw [hSk k hki]
        exact hdisjST k j
    · intro k p hp
      by_cases hki : k = i
      · subst k
        apply hoddR p
        rwa [hSi] at hp
      · apply hoddS k p
        rwa [hSk k hki] at hp
    · intro k k' hkk'
      by_cases hki : k = i
      · subst k
        rw [hSi, hSk k' (by omega)]
        exact hRantiS k' (by omega)
      · by_cases hk'i : k' = i
        · subst k'
          rw [hSk k hki, hSi]
          exact anticomplete_symm (hRantiS k (by omega))
        · rw [hSk k hki, hSk k' hk'i]
          exact hantiS k k' hkk'
    · intro k j
      rcases hrel k j with h | h
      · exact Or.inl (hPmap k j h)
      · exact Or.inr (hCmap k j h)
    · intro k k' hkk'
      obtain ⟨j, j', hjj', htw⟩ := htwS k k' hkk'
      exact ⟨j, j', hjj', isTwist_mono (hPmap k j) (hPmap k j')
        (hPmap k' j) (hPmap k' j') (hCmap k j) (hCmap k j')
        (hCmap k' j) (hCmap k' j') htw⟩
    · intro j j' hjj'
      obtain ⟨k, k', hkk', htw⟩ := htwT j j' hjj'
      exact ⟨k, k', hkk', isTwist_mono (hPmap k j) (hPmap k j')
        (hPmap k' j) (hPmap k' j') (hCmap k j) (hCmap k j')
        (hCmap k' j) (hCmap k' j') htw⟩
  have hsub : striationVertices S T ⊆ striationVertices S' T := by
    intro x hx
    rcases hx with hx | hx
    · left
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      by_cases hki : k = i
      · subst k
        exact Set.mem_iUnion.mpr ⟨i, by rw [hSi, hverts]; exact Or.inl hxk⟩
      · exact Set.mem_iUnion.mpr ⟨k, by rwa [hSk k hki]⟩
    · exact Or.inr hx
  have hfnew : f ∈ striationVertices S' T := by
    left
    exact Set.mem_iUnion.mpr ⟨i, by rw [hSi, hverts]; exact Or.inr rfl⟩
  have hproper : striationVertices S T ⊂ striationVertices S' T :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hfL (by rw [heq]; exact hfnew)⟩
  exact hmax.2 ⟨m, n, S', T, hnew, hproper⟩

end Workspace.ProofLemmas.Thm94ClosingMaximal
