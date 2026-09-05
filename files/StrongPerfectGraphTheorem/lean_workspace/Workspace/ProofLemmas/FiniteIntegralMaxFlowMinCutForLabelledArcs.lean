import Workspace.ProofLemmas.MaximalIntegralFlowHasTightResidualReachabilityCut

set_option autoImplicit false

namespace Workspace.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs

/-- Total flow on the labelled arcs whose tail is `z`. -/
noncomputable def flowOut {V A : Type*} [Fintype A]
    (tail : A → V) (f : A → Nat) (z : V) : Nat := by
  classical
  exact ∑ a : A, if tail a = z then f a else 0

/-- Total flow on the labelled arcs whose head is `z`. -/
noncomputable def flowIn {V A : Type*} [Fintype A]
    (head : A → V) (f : A → Nat) (z : V) : Nat := by
  classical
  exact ∑ a : A, if head a = z then f a else 0

/-- Capacity of the labelled arcs directed from `X` to its complement. -/
noncomputable def cutCapacity {V A : Type*} [Fintype A]
    (tail head : A → V) (cap : A → Nat) (X : Set V) : Nat := by
  classical
  exact ∑ a : A, if tail a ∈ X ∧ head a ∉ X then cap a else 0

/-- A capacity-respecting integral flow of value `k` from `s` to `t`. -/
def IsFeasibleIntegralFlow {V A : Type*} [Fintype A]
    (tail head : A → V) (cap f : A → Nat) (s t : V) (k : Nat) : Prop :=
  (∀ a : A, f a ≤ cap a) ∧
  (∀ z : V, z ≠ s → z ≠ t → flowOut tail f z = flowIn head f z) ∧
  flowOut tail f s = flowIn head f s + k ∧
  flowIn head f t = flowOut tail f t + k

private theorem feasibleFlow_le_cut
    {V A : Type*} [Fintype V] [Fintype A]
    (tail head : A → V) (cap f : A → Nat) (s t : V) (k : Nat)
    (hf : IsFeasibleIntegralFlow tail head cap f s t k)
    (X : Set V) (hs : s ∈ X) (ht : t ∉ X) :
    k ≤ cutCapacity tail head cap X := by
  classical
  rcases hf with ⟨hcap, hcons, hsource, _⟩
  let S : Finset V := Finset.univ.filter fun z => z ∈ X
  have hpoint (z : V) (hz : z ∈ S) :
      flowOut tail f z = flowIn head f z + if z = s then k else 0 := by
    by_cases hzs : z = s
    · simpa [hzs] using hsource
    · have hzt : z ≠ t := by
        intro h
        subst z
        exact ht (by simpa [S] using hz)
      simpa [hzs] using hcons z hzs hzt
  have hbalance :
      (∑ z ∈ S, flowOut tail f z) = (∑ z ∈ S, flowIn head f z) + k := by
    calc
      (∑ z ∈ S, flowOut tail f z) =
          ∑ z ∈ S, (flowIn head f z + if z = s then k else 0) := by
            apply Finset.sum_congr rfl
            intro z hz
            exact hpoint z hz
      _ = (∑ z ∈ S, flowIn head f z) + k := by
            simp [Finset.sum_add_distrib, S, hs]
  have hout :
      (∑ z ∈ S, flowOut tail f z) =
        ∑ a : A, if tail a ∈ X then f a else 0 := by
    simp [flowOut, S, Finset.sum_comm]
  have hin :
      (∑ z ∈ S, flowIn head f z) =
        ∑ a : A, if head a ∈ X then f a else 0 := by
    simp [flowIn, S, Finset.sum_comm]
  have harc (a : A) :
      (if tail a ∈ X then f a else 0) ≤
        (if head a ∈ X then f a else 0) +
          (if tail a ∈ X ∧ head a ∉ X then cap a else 0) := by
    by_cases htail : tail a ∈ X <;> by_cases hhead : head a ∈ X
    · simp [htail, hhead]
    · simpa [htail, hhead] using hcap a
    · simp [htail, hhead]
    · simp [htail, hhead]
  have hcutbound :
      (∑ a : A, if tail a ∈ X then f a else 0) ≤
        (∑ a : A, if head a ∈ X then f a else 0) +
          cutCapacity tail head cap X := by
    simpa [cutCapacity, Finset.sum_add_distrib] using
      (Finset.sum_le_sum fun a _ => harc a)
  omega

private theorem exists_maximal_feasible_flow
    {V A : Type*} [Fintype V] [Fintype A]
    (tail head : A → V) (cap : A → Nat) (s t : V) (hst : s ≠ t) :
    ∃ (k : Nat) (f : A → Nat),
      IsFeasibleIntegralFlow tail head cap f s t k ∧
      ∀ (g : A → Nat) (m : Nat),
        IsFeasibleIntegralFlow tail head cap g s t m → m ≤ k := by
  classical
  let C := cutCapacity tail head cap ({s} : Set V)
  let P : Nat → Prop := fun n => ∃ f : A → Nat,
    IsFeasibleIntegralFlow tail head cap f s t n
  have hzero : P 0 := by
    refine ⟨fun _ => 0, ?_⟩
    simp [IsFeasibleIntegralFlow, flowOut, flowIn]
  let k := Nat.findGreatest P C
  have hkP : P k := Nat.findGreatest_spec (Nat.zero_le C) hzero
  obtain ⟨f, hf⟩ := hkP
  refine ⟨k, f, hf, ?_⟩
  intro g m hg
  apply Nat.le_findGreatest
  · exact feasibleFlow_le_cut tail head cap g s t m hg ({s} : Set V)
      (by simp) (by simpa using hst.symm)
  · exact ⟨g, hg⟩

/-- Finite integral max-flow/min-cut for networks whose arcs are distinct labels. -/
theorem finiteIntegralMaxFlowMinCutForLabelledArcs
    {V A : Type*} [Fintype V] [Fintype A]
    (tail head : A → V) (cap : A → Nat) (s t : V) (hst : s ≠ t) :
    ∃ (k : Nat) (f : A → Nat) (R : Set V),
      IsFeasibleIntegralFlow tail head cap f s t k ∧
      s ∈ R ∧
      t ∉ R ∧
      cutCapacity tail head cap R = k ∧
      (∀ (g : A → Nat) (m : Nat),
        IsFeasibleIntegralFlow tail head cap g s t m → m ≤ k) ∧
      ∀ X : Set V, s ∈ X → t ∉ X → k ≤ cutCapacity tail head cap X := by
  classical
  obtain ⟨k, f, hf, hmax⟩ := exists_maximal_feasible_flow tail head cap s t hst
  have hR : ∃ R : Set V, s ∈ R ∧ t ∉ R ∧
      cutCapacity tail head cap R = k := by
    refine ⟨{z : V | Relation.ReflTransGen
      (fun u v =>
        (∃ a : A, tail a = u ∧ head a = v ∧ f a < cap a) ∨
        (∃ a : A, head a = u ∧ tail a = v ∧ 0 < f a)) s z}, ?_⟩
    simpa [IsFeasibleIntegralFlow, flowOut, flowIn, cutCapacity] using
      (Workspace.ProofLemmas.MaximalIntegralFlowHasTightResidualReachabilityCut
        tail head cap f s t k hst hf hmax)
  obtain ⟨R, hsR, htR, hcut⟩ := hR
  exact ⟨k, f, R, hf, hsR, htR, hcut, hmax,
    fun X hs ht => feasibleFlow_le_cut tail head cap f s t k hf X hs ht⟩

end Workspace.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs
