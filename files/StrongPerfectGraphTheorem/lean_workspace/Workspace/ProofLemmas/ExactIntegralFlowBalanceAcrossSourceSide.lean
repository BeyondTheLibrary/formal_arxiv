import Mathlib

set_option autoImplicit false

namespace Workspace.ProofLemmas

attribute [local instance] Classical.propDecidable

/-- Exact labelled-arc flow balance across any source side. -/
theorem ExactIntegralFlowBalanceAcrossSourceSide
    {V A : Type*} [Fintype V] [Fintype A]
    (tail head : A → V) (q : A → Nat) (s t : V) (n : Nat)
    (hconservation : ∀ z : V, z ≠ s → z ≠ t →
      (∑ a : A, if tail a = z then q a else 0) =
        ∑ a : A, if head a = z then q a else 0)
    (hsource : (∑ a : A, if tail a = s then q a else 0) =
      (∑ a : A, if head a = s then q a else 0) + n)
    (X : Set V) (hsX : s ∈ X) (htX : t ∉ X) :
    (∑ a : A, if tail a ∈ X ∧ head a ∉ X then q a else 0) =
      (∑ a : A, if tail a ∉ X ∧ head a ∈ X then q a else 0) + n := by
  classical
  let S : Finset V := Finset.univ.filter fun z => z ∈ X
  have hpoint (z : V) (hz : z ∈ S) :
      (∑ a : A, if tail a = z then q a else 0) =
        (∑ a : A, if head a = z then q a else 0) + if z = s then n else 0 := by
    by_cases hzs : z = s
    · simpa [hzs] using hsource
    · have hzt : z ≠ t := by
        intro h
        subst z
        exact htX (by simpa [S] using hz)
      simpa [hzs] using hconservation z hzs hzt
  have hbalance :
      (∑ z ∈ S, ∑ a : A, if tail a = z then q a else 0) =
        (∑ z ∈ S, ∑ a : A, if head a = z then q a else 0) + n := by
    calc
      (∑ z ∈ S, ∑ a : A, if tail a = z then q a else 0) =
          ∑ z ∈ S, ((∑ a : A, if head a = z then q a else 0) +
            if z = s then n else 0) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hpoint z hz
      _ = (∑ z ∈ S, ∑ a : A, if head a = z then q a else 0) + n := by
            simp [Finset.sum_add_distrib, S, hsX]
  have hout :
      (∑ z ∈ S, ∑ a : A, if tail a = z then q a else 0) =
        ∑ a : A, if tail a ∈ X then q a else 0 := by
    simp [S, Finset.sum_comm]
  have hin :
      (∑ z ∈ S, ∑ a : A, if head a = z then q a else 0) =
        ∑ a : A, if head a ∈ X then q a else 0 := by
    simp [S, Finset.sum_comm]
  let internal : Nat := ∑ a : A, if tail a ∈ X ∧ head a ∈ X then q a else 0
  let outgoing : Nat := ∑ a : A, if tail a ∈ X ∧ head a ∉ X then q a else 0
  let incoming : Nat := ∑ a : A, if tail a ∉ X ∧ head a ∈ X then q a else 0
  have houtSplit : (∑ a : A, if tail a ∈ X then q a else 0) = internal + outgoing := by
    dsimp [internal, outgoing]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ht : tail a ∈ X <;> by_cases hh : head a ∈ X <;> simp [ht, hh]
  have hinSplit : (∑ a : A, if head a ∈ X then q a else 0) = internal + incoming := by
    dsimp [internal, incoming]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ht : tail a ∈ X <;> by_cases hh : head a ∈ X <;> simp [ht, hh]
  have htotal : internal + outgoing = internal + incoming + n := by
    rw [← houtSplit, ← hinSplit, ← hout, ← hin]
    exact hbalance
  change outgoing = incoming + n
  omega

end Workspace.ProofLemmas
