import Workspace.ProofLemmas.ExactIntegralFlowBalanceAcrossSourceSide
import Workspace.ProofLemmas.ResidualRouteAugmentsLabelledArcIntegralFlow

set_option autoImplicit false

namespace Workspace.ProofLemmas

attribute [local instance] Classical.propDecidable

/-- A maximal labelled-arc integral flow induces a tight cut consisting of
the vertices reachable from the source in its residual relation. -/
theorem MaximalIntegralFlowHasTightResidualReachabilityCut
    {V A : Type*} [Fintype V] [Fintype A]
    (tail head : A → V) (cap f : A → Nat) (s t : V) (k : Nat)
    (hst : s ≠ t) :
    let flowOut : (A → Nat) → V → Nat := by
      classical
      exact fun q z => ∑ a : A, if tail a = z then q a else 0
    let flowIn : (A → Nat) → V → Nat := by
      classical
      exact fun q z => ∑ a : A, if head a = z then q a else 0
    let feasible : (A → Nat) → Nat → Prop := fun q n =>
      (∀ a : A, q a ≤ cap a) ∧
      (∀ z : V, z ≠ s → z ≠ t → flowOut q z = flowIn q z) ∧
      flowOut q s = flowIn q s + n ∧
      flowIn q t = flowOut q t + n
    let residualStep : V → V → Prop := fun u v =>
      (∃ a : A, tail a = u ∧ head a = v ∧ f a < cap a) ∨
      (∃ a : A, head a = u ∧ tail a = v ∧ 0 < f a)
    let residualReachable : V → V → Prop :=
      Relation.ReflTransGen residualStep
    let R : Set V := {z : V | residualReachable s z}
    feasible f k →
      (∀ (g : A → Nat) (m : Nat), feasible g m → m ≤ k) →
      s ∈ R ∧
      t ∉ R ∧
      (∑ a : A, if tail a ∈ R ∧ head a ∉ R then cap a else 0) = k := by
  classical
  dsimp
  intro hflow hmax
  let step : V → V → Prop := fun u v =>
    (∃ a : A, tail a = u ∧ head a = v ∧ f a < cap a) ∨
    (∃ a : A, head a = u ∧ tail a = v ∧ 0 < f a)
  let R : Set V := {z : V | Relation.ReflTransGen step s z}
  have hsR : s ∈ R := Relation.ReflTransGen.refl
  have htR : t ∉ R := by
    intro ht
    have haugment := ResidualRouteAugmentsLabelledArcIntegralFlow
      tail head cap f s t k hst
    dsimp at haugment
    obtain ⟨f', hf'⟩ := haugment hflow ht
    have hle := hmax f' (k + 1) hf'
    omega
  have hout_sat (a : A) (ha : tail a ∈ R ∧ head a ∉ R) : f a = cap a := by
    have hnotlt : ¬ f a < cap a := by
      intro hlt
      have hstep : step (tail a) (head a) := Or.inl ⟨a, rfl, rfl, hlt⟩
      exact ha.2 (Relation.ReflTransGen.tail ha.1 hstep)
    exact Nat.le_antisymm (hflow.1 a) (Nat.le_of_not_gt hnotlt)
  have hin_zero (a : A) (ha : tail a ∉ R ∧ head a ∈ R) : f a = 0 := by
    by_contra hne
    have hpos : 0 < f a := Nat.pos_of_ne_zero hne
    have hstep : step (head a) (tail a) := Or.inr ⟨a, rfl, rfl, hpos⟩
    exact ha.1 (Relation.ReflTransGen.tail ha.2 hstep)
  have hcap_out :
      (∑ a : A, if tail a ∈ R ∧ head a ∉ R then cap a else 0) =
        ∑ a : A, if tail a ∈ R ∧ head a ∉ R then f a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : tail a ∈ R ∧ head a ∉ R
    · simp [ha, hout_sat a ha]
    · simp [ha]
  have hin_sum :
      (∑ a : A, if tail a ∉ R ∧ head a ∈ R then f a else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : tail a ∉ R ∧ head a ∈ R
    · simp [ha, hin_zero a ha]
    · simp [ha]
  have hbalance := ExactIntegralFlowBalanceAcrossSourceSide
    tail head f s t k hflow.2.1 hflow.2.2.1 R hsR htR
  have hcut :
      (∑ a : A, if tail a ∈ R ∧ head a ∉ R then cap a else 0) = k := by
    calc
      (∑ a : A, if tail a ∈ R ∧ head a ∉ R then cap a else 0) =
          ∑ a : A, if tail a ∈ R ∧ head a ∉ R then f a else 0 := hcap_out
      _ = (∑ a : A, if tail a ∉ R ∧ head a ∈ R then f a else 0) + k := hbalance
      _ = k := by rw [hin_sum]; simp
  exact ⟨hsR, htR, hcut⟩

end Workspace.ProofLemmas
