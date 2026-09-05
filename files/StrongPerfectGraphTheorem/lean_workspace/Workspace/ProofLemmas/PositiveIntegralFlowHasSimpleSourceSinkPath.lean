import Workspace.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs
import Workspace.ProofLemmas.ShortestLabelledQuiverPath

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs

theorem PositiveIntegralFlowHasSimpleSourceSinkPath
    {V A : Type*}
    [Fintype V] [Fintype A] [DecidableEq A]
    (tail head : A → V) (cap f : A → ℕ) (s t : V) (k : ℕ)
    (hst : s ≠ t)
    (hflow : IsFeasibleIntegralFlow tail head cap f s t k)
    (hk : 0 < k) :
    ∃ ρ : List A,
      ρ ≠ [] ∧
      (∃ a, ρ.head? = some a ∧ tail a = s) ∧
      (∃ a, ρ.getLast? = some a ∧ head a = t) ∧
      (∀ ab ∈ ρ.zip ρ.tail, head ab.1 = tail ab.2) ∧
      (s :: ρ.map head).Nodup ∧
      (∀ a ∈ ρ, 0 < f a) ∧
      ∀ a, ρ.count a ≤ f a := by
  classical
  let step : V → V → Prop := fun u v =>
    ∃ a : A, tail a = u ∧ head a = v ∧ 0 < f a
  let R : Set V := {z : V | Relation.ReflTransGen step s z}
  have hsR : s ∈ R := by
    exact Relation.ReflTransGen.refl
  have htR : t ∈ R := by
    by_contra htR
    have houtzero :
        (∑ a : A, if tail a ∈ R ∧ head a ∉ R then f a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      by_cases ha : tail a ∈ R ∧ head a ∉ R
      · have hfa : f a = 0 := by
          by_contra hne
          have hpos : 0 < f a := Nat.pos_of_ne_zero hne
          have hstep : step (tail a) (head a) := ⟨a, rfl, rfl, hpos⟩
          exact ha.2 (Relation.ReflTransGen.tail ha.1 hstep)
        simp [ha, hfa]
      · simp [ha]
    have hbalance := ExactIntegralFlowBalanceAcrossSourceSide
      tail head f s t k hflow.2.1 hflow.2.2.1 R hsR htR
    have hzeroEq : 0 =
        (∑ a : A, if tail a ∉ R ∧ head a ∈ R then f a else 0) + k :=
      houtzero.symm.trans hbalance
    omega
  letI : Quiver V :=
    ⟨fun u v => {a : A // tail a = u ∧ head a = v ∧ 0 < f a}⟩
  have htReach : Relation.ReflTransGen step s t := htR
  have path_of_reach : ∀ {v : V}, Relation.ReflTransGen step s v →
      Nonempty (Quiver.Path s v) := by
    intro v hv
    induction hv with
    | refl => exact ⟨Quiver.Path.nil⟩
    | @tail u v huv huv' ih =>
        obtain ⟨p⟩ := ih
        obtain ⟨a, htail, hhead, hpos⟩ := huv'
        exact ⟨p.cons ⟨a, htail, hhead, hpos⟩⟩
  have hpath : Nonempty (Quiver.Path s t) := by
    exact path_of_reach htReach
  letI : Nonempty (Quiver.Path s t) := hpath
  let p : Quiver.Path s t :=
    WellFounded.min (measure Quiver.Path.length).wf Set.univ Set.univ_nonempty
  have hpmin : ∀ q : Quiver.Path s t, p.length ≤ q.length := by
    intro q
    exact not_lt.mp
      (WellFounded.not_lt_min (measure Quiver.Path.length).wf Set.univ trivial)
  let lab : Quiver.Labelling V A := fun {_ _} e => e.1
  have htailLab : ∀ {u v : V} (e : u ⟶ v), tail (lab e) = u := by
    intro u v e
    simpa [lab] using e.property.1
  have hheadLab : ∀ {u v : V} (e : u ⟶ v), head (lab e) = v := by
    intro u v e
    simpa [lab] using e.property.2.1
  have hposLab : ∀ {u v : V} (e : u ⟶ v), 0 < f (lab e) := by
    intro u v e
    simpa [lab] using e.property.2.2
  let ρ : List A := ShortestLabelledQuiverPath.labels lab p
  have hρne : ρ ≠ [] := by
    intro hnil
    have hpzero : p.length = 0 := by
      rw [← ShortestLabelledQuiverPath.labels_length lab p]
      simp [ρ, hnil]
    exact hst (Quiver.Path.eq_of_length_zero p hpzero)
  have hρhead : ∃ a, ρ.head? = some a ∧ tail a = s := by
    simpa [ρ] using
      ShortestLabelledQuiverPath.labels_head lab htailLab p (by simpa [ρ] using hρne)
  have hρlast : ∃ a, ρ.getLast? = some a ∧ head a = t := by
    simpa [ρ] using
      ShortestLabelledQuiverPath.labels_last lab hheadLab p (by simpa [ρ] using hρne)
  have hρchain : ρ.IsChain (fun a b => head a = tail b) := by
    simpa [ρ] using
      ShortestLabelledQuiverPath.labels_isChain lab htailLab hheadLab p
  have hρlink : ∀ ab ∈ ρ.zip ρ.tail, head ab.1 = tail ab.2 :=
    ShortestLabelledQuiverPath.forall_zip_tail_of_isChain hρchain
  have hpvertices : p.vertices.Nodup :=
    ShortestLabelledQuiverPath.vertices_nodup_of_length_minimal p hpmin
  have hρvertices : (s :: ρ.map head).Nodup := by
    rw [ShortestLabelledQuiverPath.cons_map_head_labels_eq_vertices lab hheadLab p]
    exact hpvertices
  have hρpositive : ∀ a ∈ ρ, 0 < f a := by
    simpa [ρ] using ShortestLabelledQuiverPath.labels_forall lab hposLab p
  have hρnodup : ρ.Nodup := List.Nodup.of_map head hρvertices.tail
  have hρload : ∀ a, ρ.count a ≤ f a := by
    intro a
    by_cases ha : a ∈ ρ
    · have hcount : ρ.count a = 1 := List.count_eq_one_of_mem hρnodup ha
      rw [hcount]
      exact hρpositive a ha
    · simp [List.count_eq_zero.mpr ha]
  exact ⟨ρ, hρne, hρhead, hρlast, hρlink, hρvertices,
    hρpositive, hρload⟩

end Workspace.ProofLemmas
