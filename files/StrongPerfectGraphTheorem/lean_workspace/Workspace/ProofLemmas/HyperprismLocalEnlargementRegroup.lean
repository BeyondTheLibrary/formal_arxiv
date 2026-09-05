import Workspace.ProofLemmas.HyperprismSplit

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementRegroup

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismSplit

/-- The three rows obtained by putting the first primed strip in row zero, the other
two primed strips in row one, and all three double-primed strips in row two. -/
def regroupA {V : Type*} (A P : Fin 3 → Set V) : Fin 3 → Set V := fun r =>
  if r = 0 then P 0
  else if r = 1 then P 1 ∪ P 2
  else (A 0 \ P 0) ∪ (A 1 \ P 1) ∪ (A 2 \ P 2)

def regroupB {V : Type*} (B Q : Fin 3 → Set V) : Fin 3 → Set V := fun r =>
  if r = 0 then Q 0
  else if r = 1 then Q 1 ∪ Q 2
  else (B 0 \ Q 0) ∪ (B 1 \ Q 1) ∪ (B 2 \ Q 2)

def regroupC {V : Type*} (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V) :
    Fin 3 → Set V := fun r =>
  if r = 0 then Cp G A B C P Q 0
  else if r = 1 then Cp G A B C P Q 1 ∪ Cp G A B C P Q 2
  else Cpp G A B C P Q 0 ∪ Cpp G A B C P Q 1 ∪ Cpp G A B C P Q 2

private theorem mem_regroupA_old
    {V : Type*} {G : SimpleGraph V} {A B C P Q : Fin 3 → Set V}
    (hs : IsRungSplit G A B C P Q) {r : Fin 3} {x : V}
    (hx : x ∈ regroupA A P r) : ∃ i : Fin 3, x ∈ A i := by
  rcases fin3_cases r with rfl | rfl | rfl
  · exact ⟨0, hs.PA 0 (by simpa [regroupA] using hx)⟩
  · simp only [regroupA, if_false, if_true, Set.mem_union] at hx
    rcases hx with hx | hx
    · exact ⟨1, hs.PA 1 hx⟩
    · exact ⟨2, hs.PA 2 hx⟩
  · simp only [regroupA, if_false, Set.mem_union, Set.mem_diff] at hx
    rcases hx with (hx | hx) | hx
    · exact ⟨0, hx.1⟩
    · exact ⟨1, hx.1⟩
    · exact ⟨2, hx.1⟩

private theorem mem_regroupB_old
    {V : Type*} {G : SimpleGraph V} {A B C P Q : Fin 3 → Set V}
    (hs : IsRungSplit G A B C P Q) {r : Fin 3} {x : V}
    (hx : x ∈ regroupB B Q r) : ∃ i : Fin 3, x ∈ B i := by
  rcases fin3_cases r with rfl | rfl | rfl
  · exact ⟨0, hs.QB 0 (by simpa [regroupB] using hx)⟩
  · simp only [regroupB, if_false, if_true, Set.mem_union] at hx
    rcases hx with hx | hx
    · exact ⟨1, hs.QB 1 hx⟩
    · exact ⟨2, hs.QB 2 hx⟩
  · simp only [regroupB, if_false, Set.mem_union, Set.mem_diff] at hx
    rcases hx with (hx | hx) | hx
    · exact ⟨0, hx.1⟩
    · exact ⟨1, hx.1⟩
    · exact ⟨2, hx.1⟩

private theorem mem_regroupC_old
    {V : Type*} {G : SimpleGraph V} {A B C P Q : Fin 3 → Set V}
    {r : Fin 3} {x : V} (hx : x ∈ regroupC G A B C P Q r) :
    ∃ i : Fin 3, x ∈ C i := by
  rcases fin3_cases r with rfl | rfl | rfl
  · exact ⟨0, Cp_subset_C 0 (by simpa [regroupC] using hx)⟩
  · simp only [regroupC, if_false, Fin.reduceFinMk, if_true, Set.mem_union] at hx
    rcases hx with hx | hx
    · exact ⟨1, Cp_subset_C 1 hx⟩
    · exact ⟨2, Cp_subset_C 2 hx⟩
  · simp only [regroupC, if_false, Set.mem_union] at hx
    rcases hx with (hx | hx) | hx
    · exact ⟨0, Cpp_subset_C 0 hx⟩
    · exact ⟨1, Cpp_subset_C 1 hx⟩
    · exact ⟨2, Cpp_subset_C 2 hx⟩

/-- Regrouping only moves old vertices between rows; it does not change their union. -/
theorem hyperVerts_regroup
    {V : Type*} {G : SimpleGraph V} {A B C P Q : Fin 3 → Set V}
    (hH : IsHyperprism G A B C) (hs : IsRungSplit G A B C P Q) :
    hyperVerts (regroupA A P) (regroupB B Q) (regroupC G A B C P Q) =
      hyperVerts A B C := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := mem_hyperVerts_iff.mp hx
    rcases hr with (hr | hr) | hr
    · obtain ⟨i, hi⟩ := mem_regroupA_old hs hr
      exact mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inl hi)⟩
    · obtain ⟨i, hi⟩ := mem_regroupB_old hs hr
      exact mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inr hi)⟩
    · obtain ⟨i, hi⟩ := mem_regroupC_old hr
      exact mem_hyperVerts_iff.mpr ⟨i, Or.inr hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    rcases fin3_cases i with rfl | rfl | rfl
    all_goals rcases hi with (hi | hi) | hi
    · by_cases hp : x ∈ P 0
      · exact mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inl (by simpa [regroupA] using hp))⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inl (by simp [regroupA, hi, hp]))⟩
    · by_cases hq : x ∈ Q 0
      · exact mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inr (by simpa [regroupB] using hq))⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inr (by simp [regroupB, hi, hq]))⟩
    · rw [C_eq hH hs 0] at hi
      rcases hi with hi | hi
      · exact mem_hyperVerts_iff.mpr ⟨0, Or.inr (by simpa [regroupC] using hi)⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inr (by simp [regroupC, hi])⟩
    · by_cases hp : x ∈ P 1
      · exact mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inl (by simp [regroupA, hp]))⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inl (by simp [regroupA, hi, hp]))⟩
    · by_cases hq : x ∈ Q 1
      · exact mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inr (by simp [regroupB, hq]))⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inr (by simp [regroupB, hi, hq]))⟩
    · rw [C_eq hH hs 1] at hi
      rcases hi with hi | hi
      · exact mem_hyperVerts_iff.mpr ⟨1, Or.inr (by simp [regroupC, hi])⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inr (by simp [regroupC, hi])⟩
    · by_cases hp : x ∈ P 2
      · exact mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inl (by simp [regroupA, hp]))⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inl (by simp [regroupA, hi, hp]))⟩
    · by_cases hq : x ∈ Q 2
      · exact mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inr (by simp [regroupB, hq]))⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inl (Or.inr (by simp [regroupB, hi, hq]))⟩
    · rw [C_eq hH hs 2] at hi
      rcases hi with hi | hi
      · exact mem_hyperVerts_iff.mpr ⟨1, Or.inr (by simp [regroupC, hi])⟩
      · exact mem_hyperVerts_iff.mpr ⟨2, Or.inr (by simp [regroupC, hi])⟩

/-- The split-and-regroup operation used in both displayed nine-set constructions in
claim (2).  The two internal completeness hypotheses are precisely the two claims proved
immediately before those displays. -/
theorem regroupIsHyperprism
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C P Q : Fin 3 → Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C)
    (hs : IsRungSplit G A B C P Q)
    (hPA : ∀ i : Fin 3, Complete G (P i) (A i \ P i))
    (hQB : ∀ i : Fin 3, Complete G (Q i) (B i \ Q i))
    (hP0 : (P 0).Nonempty) (hP12 : (P 1 ∪ P 2).Nonempty)
    (hD : ((A 0 \ P 0) ∪ (A 1 \ P 1) ∪ (A 2 \ P 2)).Nonempty) :
    IsHyperprism G (regroupA A P) (regroupB B Q) (regroupC G A B C P Q) := by
  classical
  let A' := regroupA A P
  let B' := regroupB B Q
  let C' := regroupC G A B C P Q
  have hprimeA_doubleA : ∀ {i j : Fin 3} {x : V},
      x ∈ P i → x ∈ A j \ P j → False := by
    intro i j x hpi hdj
    by_cases hij : i = j
    · subst j
      exact hdj.2 hpi
    · exact Set.disjoint_left.mp (hH.2.2.2.2.1 i j hij) (hs.PA i hpi) hdj.1
  have hprimeB_doubleB : ∀ {i j : Fin 3} {x : V},
      x ∈ Q i → x ∈ B j \ Q j → False := by
    intro i j x hqi hdj
    by_cases hij : i = j
    · subst j
      exact hdj.2 hqi
    · exact Set.disjoint_left.mp (hH.2.2.2.2.2.1 i j hij) (hs.QB i hqi) hdj.1
  have hprimeC_doubleC : ∀ {i j : Fin 3} {x : V},
      x ∈ Cp G A B C P Q i → x ∈ Cpp G A B C P Q j → False := by
    intro i j x hpi hdj
    by_cases hij : i = j
    · subst j
      exact Set.disjoint_left.mp (Cp_Cpp_disjoint hH hs i) hpi hdj
    · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 i j hij)
        (Cp_subset_C i hpi) (Cpp_subset_C j hdj)
  have hnonempty : ∀ r : Fin 3, (A' r).Nonempty ∧ (B' r).Nonempty ∧ (C' r).Nonempty := by
    intro r
    rcases fin3_cases r with rfl | rfl | rfl
    · obtain ⟨hQ0, hC0⟩ := nonempty_of_P_nonempty hG hH hs hP0
      simpa [A', B', C', regroupA, regroupB, regroupC] using ⟨hP0, hQ0, hC0⟩
    · obtain ⟨a, ha⟩ := hP12
      rcases ha with ha | ha
      · obtain ⟨hQ, hC⟩ := nonempty_of_P_nonempty hG hH hs ⟨a, ha⟩
        obtain ⟨b, hb⟩ := hQ
        obtain ⟨c, hc⟩ := hC
        exact ⟨⟨a, by simp [A', regroupA, ha]⟩,
          ⟨b, by simp [B', regroupB, hb]⟩, ⟨c, by simp [C', regroupC, hc]⟩⟩
      · obtain ⟨hQ, hC⟩ := nonempty_of_P_nonempty hG hH hs ⟨a, ha⟩
        obtain ⟨b, hb⟩ := hQ
        obtain ⟨c, hc⟩ := hC
        exact ⟨⟨a, by simp [A', regroupA, ha]⟩,
          ⟨b, by simp [B', regroupB, hb]⟩, ⟨c, by simp [C', regroupC, hc]⟩⟩
    · obtain ⟨a, ha⟩ := hD
      rcases ha with (ha | ha) | ha
      · obtain ⟨hB, hC⟩ := nonempty_of_notP_nonempty hG hH hs ⟨a, ha⟩
        obtain ⟨b, hb⟩ := hB
        obtain ⟨c, hc⟩ := hC
        exact ⟨⟨a, by simp [A', regroupA, ha]⟩,
          ⟨b, by simp [B', regroupB, hb]⟩, ⟨c, by simp [C', regroupC, hc]⟩⟩
      · obtain ⟨hB, hC⟩ := nonempty_of_notP_nonempty hG hH hs ⟨a, ha⟩
        obtain ⟨b, hb⟩ := hB
        obtain ⟨c, hc⟩ := hC
        exact ⟨⟨a, by simp [A', regroupA, ha]⟩,
          ⟨b, by simp [B', regroupB, hb]⟩, ⟨c, by simp [C', regroupC, hc]⟩⟩
      · obtain ⟨hB, hC⟩ := nonempty_of_notP_nonempty hG hH hs ⟨a, ha⟩
        obtain ⟨b, hb⟩ := hB
        obtain ⟨c, hc⟩ := hC
        exact ⟨⟨a, by simp [A', regroupA, ha]⟩,
          ⟨b, by simp [B', regroupB, hb]⟩, ⟨c, by simp [C', regroupC, hc]⟩⟩
  have hAB : ∀ r s : Fin 3, Disjoint (A' r) (B' s) := by
    intro r s
    rw [Set.disjoint_left]
    intro x hxA hxB
    obtain ⟨i, hi⟩ := mem_regroupA_old hs hxA
    obtain ⟨j, hj⟩ := mem_regroupB_old hs hxB
    exact Set.disjoint_left.mp (hH.2.1 i j) hi hj
  have hAC : ∀ r s : Fin 3, Disjoint (A' r) (C' s) := by
    intro r s
    rw [Set.disjoint_left]
    intro x hxA hxC
    obtain ⟨i, hi⟩ := mem_regroupA_old hs hxA
    obtain ⟨j, hj⟩ := mem_regroupC_old hxC
    exact Set.disjoint_left.mp (hH.2.2.1 i j) hi hj
  have hBC : ∀ r s : Fin 3, Disjoint (B' r) (C' s) := by
    intro r s
    rw [Set.disjoint_left]
    intro x hxB hxC
    obtain ⟨i, hi⟩ := mem_regroupB_old hs hxB
    obtain ⟨j, hj⟩ := mem_regroupC_old hxC
    exact Set.disjoint_left.mp (hH.2.2.2.1 i j) hi hj
  have hAA : ∀ r s : Fin 3, r ≠ s → Disjoint (A' r) (A' s) := by
    intro r s hrs
    rw [Set.disjoint_left]
    intro x hr hsx
    rcases fin3_cases r with rfl | rfl | rfl <;>
      rcases fin3_cases s with rfl | rfl | rfl
    all_goals try { exact absurd rfl hrs }
    all_goals simp only [A', regroupA, if_true, if_false, Set.mem_union, Set.mem_diff] at hr hsx
    · rcases hsx with hsx | hsx
      · exact Set.disjoint_left.mp (hH.2.2.2.2.1 0 1 (by decide)) (hs.PA 0 hr) (hs.PA 1 hsx)
      · exact Set.disjoint_left.mp (hH.2.2.2.2.1 0 2 (by decide)) (hs.PA 0 hr) (hs.PA 2 hsx)
    · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeA_doubleA hr hsx
    · rcases hr with hr | hr
      · exact Set.disjoint_left.mp (hH.2.2.2.2.1 1 0 (by decide)) (hs.PA 1 hr) (hs.PA 0 hsx)
      · exact Set.disjoint_left.mp (hH.2.2.2.2.1 2 0 (by decide)) (hs.PA 2 hr) (hs.PA 0 hsx)
    · rcases hr with hr | hr
      · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeA_doubleA hr hsx
      · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeA_doubleA hr hsx
    · rcases hr with (hr | hr) | hr <;> exact hprimeA_doubleA hsx hr
    · rcases hr with (hr | hr) | hr
      · rcases hsx with hsx | hsx <;> exact hprimeA_doubleA hsx hr
      · rcases hsx with hsx | hsx <;> exact hprimeA_doubleA hsx hr
      · rcases hsx with hsx | hsx <;> exact hprimeA_doubleA hsx hr
  have hBB : ∀ r s : Fin 3, r ≠ s → Disjoint (B' r) (B' s) := by
    intro r s hrs
    rw [Set.disjoint_left]
    intro x hr hsx
    rcases fin3_cases r with rfl | rfl | rfl <;>
      rcases fin3_cases s with rfl | rfl | rfl
    all_goals try { exact absurd rfl hrs }
    all_goals simp only [B', regroupB, if_true, if_false, Set.mem_union, Set.mem_diff] at hr hsx
    · rcases hsx with hsx | hsx
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.1 0 1 (by decide)) (hs.QB 0 hr) (hs.QB 1 hsx)
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.1 0 2 (by decide)) (hs.QB 0 hr) (hs.QB 2 hsx)
    · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeB_doubleB hr hsx
    · rcases hr with hr | hr
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.1 1 0 (by decide)) (hs.QB 1 hr) (hs.QB 0 hsx)
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.1 2 0 (by decide)) (hs.QB 2 hr) (hs.QB 0 hsx)
    · rcases hr with hr | hr
      · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeB_doubleB hr hsx
      · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeB_doubleB hr hsx
    · rcases hr with (hr | hr) | hr <;> exact hprimeB_doubleB hsx hr
    · rcases hr with (hr | hr) | hr
      · rcases hsx with hsx | hsx <;> exact hprimeB_doubleB hsx hr
      · rcases hsx with hsx | hsx <;> exact hprimeB_doubleB hsx hr
      · rcases hsx with hsx | hsx <;> exact hprimeB_doubleB hsx hr
  have hCC : ∀ r s : Fin 3, r ≠ s → Disjoint (C' r) (C' s) := by
    intro r s hrs
    rw [Set.disjoint_left]
    intro x hr hsx
    rcases fin3_cases r with rfl | rfl | rfl <;>
      rcases fin3_cases s with rfl | rfl | rfl
    all_goals try { exact absurd rfl hrs }
    all_goals simp only [C', regroupC, if_true, if_false, Set.mem_union] at hr hsx
    · rcases hsx with hsx | hsx
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 0 1 (by decide))
          (Cp_subset_C 0 hr) (Cp_subset_C 1 hsx)
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 0 2 (by decide))
          (Cp_subset_C 0 hr) (Cp_subset_C 2 hsx)
    · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeC_doubleC hr hsx
    · rcases hr with hr | hr
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 1 0 (by decide))
          (Cp_subset_C 1 hr) (Cp_subset_C 0 hsx)
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 2 0 (by decide))
          (Cp_subset_C 2 hr) (Cp_subset_C 0 hsx)
    · rcases hr with hr | hr
      · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeC_doubleC hr hsx
      · rcases hsx with (hsx | hsx) | hsx <;> exact hprimeC_doubleC hr hsx
    · rcases hr with (hr | hr) | hr <;> exact hprimeC_doubleC hsx hr
    · rcases hr with (hr | hr) | hr
      · rcases hsx with hsx | hsx <;> exact hprimeC_doubleC hsx hr
      · rcases hsx with hsx | hsx <;> exact hprimeC_doubleC hsx hr
      · rcases hsx with hsx | hsx <;> exact hprimeC_doubleC hsx hr
  have hcompleteA : ∀ r s : Fin 3, r < s → Complete G (A' r) (A' s) := by
    intro r s hrs x hx y hy
    rcases fin3_cases r with rfl | rfl | rfl <;>
      rcases fin3_cases s with rfl | rfl | rfl
    all_goals try omega
    all_goals simp only [A', regroupA, if_true, if_false, Set.mem_union, Set.mem_diff] at hx hy
    · rcases hy with hy | hy
      · exact complete_A hH (show (0 : Fin 3) ≠ 1 by decide) x (hs.PA 0 hx) y (hs.PA 1 hy)
      · exact complete_A hH (show (0 : Fin 3) ≠ 2 by decide) x (hs.PA 0 hx) y (hs.PA 2 hy)
    · rcases hy with (hy | hy) | hy
      · exact hPA 0 x hx y hy
      · exact complete_A hH (show (0 : Fin 3) ≠ 1 by decide) x (hs.PA 0 hx) y hy.1
      · exact complete_A hH (show (0 : Fin 3) ≠ 2 by decide) x (hs.PA 0 hx) y hy.1
    · rcases hx with hx | hx
      · rcases hy with (hy | hy) | hy
        · exact (complete_A hH (show (0 : Fin 3) ≠ 1 by decide) y hy.1 x (hs.PA 1 hx)).symm
        · exact hPA 1 x hx y hy
        · exact complete_A hH (show (1 : Fin 3) ≠ 2 by decide) x (hs.PA 1 hx) y hy.1
      · rcases hy with (hy | hy) | hy
        · exact (complete_A hH (show (0 : Fin 3) ≠ 2 by decide) y hy.1 x (hs.PA 2 hx)).symm
        · exact (complete_A hH (show (1 : Fin 3) ≠ 2 by decide) y hy.1 x (hs.PA 2 hx)).symm
        · exact hPA 2 x hx y hy
  have hcompleteB : ∀ r s : Fin 3, r < s → Complete G (B' r) (B' s) := by
    intro r s hrs x hx y hy
    rcases fin3_cases r with rfl | rfl | rfl <;>
      rcases fin3_cases s with rfl | rfl | rfl
    all_goals try omega
    all_goals simp only [B', regroupB, if_true, if_false, Set.mem_union, Set.mem_diff] at hx hy
    · rcases hy with hy | hy
      · exact complete_B hH (show (0 : Fin 3) ≠ 1 by decide) x (hs.QB 0 hx) y (hs.QB 1 hy)
      · exact complete_B hH (show (0 : Fin 3) ≠ 2 by decide) x (hs.QB 0 hx) y (hs.QB 2 hy)
    · rcases hy with (hy | hy) | hy
      · exact hQB 0 x hx y hy
      · exact complete_B hH (show (0 : Fin 3) ≠ 1 by decide) x (hs.QB 0 hx) y hy.1
      · exact complete_B hH (show (0 : Fin 3) ≠ 2 by decide) x (hs.QB 0 hx) y hy.1
    · rcases hx with hx | hx
      · rcases hy with (hy | hy) | hy
        · exact (complete_B hH (show (0 : Fin 3) ≠ 1 by decide) y hy.1 x (hs.QB 1 hx)).symm
        · exact hQB 1 x hx y hy
        · exact complete_B hH (show (1 : Fin 3) ≠ 2 by decide) x (hs.QB 1 hx) y hy.1
      · rcases hy with (hy | hy) | hy
        · exact (complete_B hH (show (0 : Fin 3) ≠ 2 by decide) y hy.1 x (hs.QB 2 hx)).symm
        · exact (complete_B hH (show (1 : Fin 3) ≠ 2 by decide) y hy.1 x (hs.QB 2 hx)).symm
        · exact hQB 2 x hx y hy
  have hcrossPP : ∀ {i j : Fin 3} {x y : V}, i ≠ j →
      x ∈ P i ∪ Q i ∪ Cp G A B C P Q i →
      y ∈ P j ∪ Q j ∪ Cp G A B C P Q j → G.Adj x y →
      (x ∈ P i ∧ y ∈ P j) ∨ (x ∈ Q i ∧ y ∈ Q j) := by
    intro i j x y hij hx hy hadj
    have hxold : x ∈ A i ∪ B i ∪ C i := by
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl (hs.PA i hx))
      · exact Or.inl (Or.inr (hs.QB i hx))
      · exact Or.inr (Cp_subset_C i hx)
    have hyold : y ∈ A j ∪ B j ∪ C j := by
      rcases hy with (hy | hy) | hy
      · exact Or.inl (Or.inl (hs.PA j hy))
      · exact Or.inl (Or.inr (hs.QB j hy))
      · exact Or.inr (Cp_subset_C j hy)
    rcases cross hH hij hxold hyold hadj with haa | hbb
    · left
      constructor
      · rcases hx with (hx | hx) | hx
        · exact hx
        · exact absurd (Set.disjoint_left.mp (hH.2.1 i i) haa.1 (hs.QB i hx)) False.elim
        · exact absurd (Set.disjoint_left.mp (hH.2.2.1 i i) haa.1 (Cp_subset_C i hx)) False.elim
      · rcases hy with (hy | hy) | hy
        · exact hy
        · exact absurd (Set.disjoint_left.mp (hH.2.1 j j) haa.2 (hs.QB j hy)) False.elim
        · exact absurd (Set.disjoint_left.mp (hH.2.2.1 j j) haa.2 (Cp_subset_C j hy)) False.elim
    · right
      constructor
      · rcases hx with (hx | hx) | hx
        · exact absurd (Set.disjoint_left.mp (hH.2.1 i i) (hs.PA i hx) hbb.1) False.elim
        · exact hx
        · exact absurd (Set.disjoint_left.mp (hH.2.2.2.1 i i) hbb.1 (Cp_subset_C i hx)) False.elim
      · rcases hy with (hy | hy) | hy
        · exact absurd (Set.disjoint_left.mp (hH.2.1 j j) (hs.PA j hy) hbb.2) False.elim
        · exact hy
        · exact absurd (Set.disjoint_left.mp (hH.2.2.2.1 j j) hbb.2 (Cp_subset_C j hy)) False.elim
  have hcrossPD : ∀ {i j : Fin 3} {x y : V},
      x ∈ P i ∪ Q i ∪ Cp G A B C P Q i →
      y ∈ (A j \ P j) ∪ (B j \ Q j) ∪ Cpp G A B C P Q j → G.Adj x y →
      (x ∈ P i ∧ y ∈ A j \ P j) ∨ (x ∈ Q i ∧ y ∈ B j \ Q j) := by
    intro i j x y hx hy hadj
    rcases hx with (hxP | hxQ) | hxC <;> rcases hy with (hyA | hyB) | hyC
    · exact Or.inl ⟨hxP, hyA⟩
    · exfalso
      by_cases hij : i = j
      · subst j
        exact no_edge_prime_dprime hH hs i (Or.inl hxP) (Or.inr hyB) hadj
      · rcases cross hH hij (Or.inl (Or.inl (hs.PA i hxP)))
            (Or.inl (Or.inr hyB.1)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.1 j j) h.2 hyB.1
        · exact Set.disjoint_left.mp (hH.2.1 i i) (hs.PA i hxP) h.1
    · exfalso
      by_cases hij : i = j
      · subst j
        exact no_edge_prime_dprime hH hs i (Or.inl hxP) (Or.inl hyC) hadj
      · rcases cross hH hij (Or.inl (Or.inl (hs.PA i hxP)))
            (Or.inr (Cpp_subset_C j hyC)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.2.1 j j) h.2 (Cpp_subset_C j hyC)
        · exact Set.disjoint_left.mp (hH.2.1 i i) (hs.PA i hxP) h.1
    · exfalso
      by_cases hij : i = j
      · subst j
        exact no_edge_dprime_prime hH hs i (Or.inl hyA) (Or.inr hxQ) hadj.symm
      · rcases cross hH hij (Or.inl (Or.inr (hs.QB i hxQ)))
            (Or.inl (Or.inl hyA.1)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.1 i i) h.1 (hs.QB i hxQ)
        · exact Set.disjoint_left.mp (hH.2.1 j j) hyA.1 h.2
    · exact Or.inr ⟨hxQ, hyB⟩
    · exfalso
      by_cases hij : i = j
      · subst j
        exact no_edge_dprime_prime hH hs i (Or.inr hyC) (Or.inr hxQ) hadj.symm
      · rcases cross hH hij (Or.inl (Or.inr (hs.QB i hxQ)))
            (Or.inr (Cpp_subset_C j hyC)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.1 i i) h.1 (hs.QB i hxQ)
        · exact Set.disjoint_left.mp (hH.2.2.2.1 j j) h.2 (Cpp_subset_C j hyC)
    · exfalso
      by_cases hij : i = j
      · subst j
        exact no_edge_dprime_prime hH hs i (Or.inl hyA) (Or.inl hxC) hadj.symm
      · rcases cross hH hij (Or.inr (Cp_subset_C i hxC))
            (Or.inl (Or.inl hyA.1)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.2.1 i i) h.1 (Cp_subset_C i hxC)
        · exact Set.disjoint_left.mp (hH.2.2.2.1 i i) h.1 (Cp_subset_C i hxC)
    · exfalso
      by_cases hij : i = j
      · subst j
        exact no_edge_prime_dprime hH hs i (Or.inr hxC) (Or.inr hyB) hadj
      · rcases cross hH hij (Or.inr (Cp_subset_C i hxC))
            (Or.inl (Or.inr hyB.1)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.2.1 i i) h.1 (Cp_subset_C i hxC)
        · exact Set.disjoint_left.mp (hH.2.2.2.1 i i) h.1 (Cp_subset_C i hxC)
    · exfalso
      by_cases hij : i = j
      · subst j
        exact no_edge_prime_dprime hH hs i (Or.inr hxC) (Or.inl hyC) hadj
      · rcases cross hH hij (Or.inr (Cp_subset_C i hxC))
            (Or.inr (Cpp_subset_C j hyC)) hadj with h | h
        · exact Set.disjoint_left.mp (hH.2.2.1 i i) h.1 (Cp_subset_C i hxC)
        · exact Set.disjoint_left.mp (hH.2.2.2.1 i i) h.1 (Cp_subset_C i hxC)
  have hprimeData : ∀ {r : Fin 3} {x : V}, r ≠ 2 →
      x ∈ A' r ∪ B' r ∪ C' r →
      ∃ i : Fin 3, x ∈ P i ∪ Q i ∪ Cp G A B C P Q i ∧
        (∀ z ∈ P i, z ∈ A' r) ∧ (∀ z ∈ Q i, z ∈ B' r) ∧
        (∀ z ∈ Cp G A B C P Q i, z ∈ C' r) := by
    intro r x hr hx
    rcases fin3_cases r with rfl | rfl | rfl
    · simp only [A', B', C', regroupA, regroupB, regroupC, if_true, Set.mem_union] at hx ⊢
      exact ⟨0, hx, fun _ h => h, fun _ h => h, fun _ h => h⟩
    · simp only [A', B', C', regroupA, regroupB, regroupC, if_false, if_true,
        Set.mem_union] at hx ⊢
      rcases hx with ((hx | hx) | (hx | hx)) | (hx | hx)
      · exact ⟨1, Or.inl (Or.inl hx), fun _ h => Or.inl h, fun _ h => Or.inl h,
          fun _ h => Or.inl h⟩
      · exact ⟨2, Or.inl (Or.inl hx), fun _ h => Or.inr h, fun _ h => Or.inr h,
          fun _ h => Or.inr h⟩
      · exact ⟨1, Or.inl (Or.inr hx), fun _ h => Or.inl h, fun _ h => Or.inl h,
          fun _ h => Or.inl h⟩
      · exact ⟨2, Or.inl (Or.inr hx), fun _ h => Or.inr h, fun _ h => Or.inr h,
          fun _ h => Or.inr h⟩
      · exact ⟨1, Or.inr hx, fun _ h => Or.inl h, fun _ h => Or.inl h,
          fun _ h => Or.inl h⟩
      · exact ⟨2, Or.inr hx, fun _ h => Or.inr h, fun _ h => Or.inr h,
          fun _ h => Or.inr h⟩
    · exact absurd rfl hr
  have hdoubleData : ∀ {y : V}, y ∈ A' 2 ∪ B' 2 ∪ C' 2 →
      ∃ j : Fin 3, y ∈ (A j \ P j) ∪ (B j \ Q j) ∪ Cpp G A B C P Q j ∧
        (∀ z ∈ A j \ P j, z ∈ A' 2) ∧ (∀ z ∈ B j \ Q j, z ∈ B' 2) ∧
        (∀ z ∈ Cpp G A B C P Q j, z ∈ C' 2) := by
    intro y hy
    simp only [A', B', C', regroupA, regroupB, regroupC, if_false, Set.mem_union] at hy ⊢
    rcases hy with (((hy | hy) | hy) | ((hy | hy) | hy)) | ((hy | hy) | hy)
    · exact ⟨0, Or.inl (Or.inl hy), fun _ h => Or.inl (Or.inl h), fun _ h => Or.inl (Or.inl h),
        fun _ h => Or.inl (Or.inl h)⟩
    · exact ⟨1, Or.inl (Or.inl hy), fun _ h => Or.inl (Or.inr h), fun _ h => Or.inl (Or.inr h),
        fun _ h => Or.inl (Or.inr h)⟩
    · exact ⟨2, Or.inl (Or.inl hy), fun _ h => Or.inr h, fun _ h => Or.inr h,
        fun _ h => Or.inr h⟩
    · exact ⟨0, Or.inl (Or.inr hy), fun _ h => Or.inl (Or.inl h), fun _ h => Or.inl (Or.inl h),
        fun _ h => Or.inl (Or.inl h)⟩
    · exact ⟨1, Or.inl (Or.inr hy), fun _ h => Or.inl (Or.inr h), fun _ h => Or.inl (Or.inr h),
        fun _ h => Or.inl (Or.inr h)⟩
    · exact ⟨2, Or.inl (Or.inr hy), fun _ h => Or.inr h, fun _ h => Or.inr h,
        fun _ h => Or.inr h⟩
    · exact ⟨0, Or.inr hy, fun _ h => Or.inl (Or.inl h), fun _ h => Or.inl (Or.inl h),
        fun _ h => Or.inl (Or.inl h)⟩
    · exact ⟨1, Or.inr hy, fun _ h => Or.inl (Or.inr h), fun _ h => Or.inl (Or.inr h),
        fun _ h => Or.inl (Or.inr h)⟩
    · exact ⟨2, Or.inr hy, fun _ h => Or.inr h, fun _ h => Or.inr h,
        fun _ h => Or.inr h⟩
  have hprimeCover : ∀ {i : Fin 3} {x : V},
      x ∈ P i ∪ Q i ∪ Cp G A B C P Q i →
      ∃ (p : List V) (a b : V), IsRungFrom G A B C i p a b ∧
        a ∈ P i ∧ b ∈ Q i ∧ x ∈ p := by
    intro i x hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨p, b, hp, hb⟩ := exists_rung_prime_of_mem_P hH hs hx
      exact ⟨p, x, b, hp, hx, hb, PathBasics.head_mem hp.2.2.1.2.1⟩
    · obtain ⟨p, a, hp, ha⟩ := exists_rung_prime_of_mem_Q hH hs hx
      exact ⟨p, a, x, hp, ha, hx, PathBasics.getLast_mem hp.2.2.1.2.2⟩
    · obtain ⟨p, a, b, hp, ha, hb, hxp⟩ := hx
      exact ⟨p, a, b, hp, ha, hb, PathBasics.interior_subset hxp⟩
  have hdoubleCover : ∀ {i : Fin 3} {x : V},
      x ∈ (A i \ P i) ∪ (B i \ Q i) ∪ Cpp G A B C P Q i →
      ∃ (p : List V) (a b : V), IsRungFrom G A B C i p a b ∧
        a ∈ A i \ P i ∧ b ∈ B i \ Q i ∧ x ∈ p := by
    intro i x hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨p, b, hp, hb⟩ := exists_rung_dprime_of_notMem_P hH hs hx.1 hx.2
      exact ⟨p, x, b, hp, hx, ⟨hp.2.1, hb⟩, PathBasics.head_mem hp.2.2.1.2.1⟩
    · obtain ⟨p, a, hp, ha⟩ := exists_rung_dprime_of_notMem_Q hH hs hx.1 hx.2
      exact ⟨p, a, x, hp, ⟨hp.1, ha⟩, hx, PathBasics.getLast_mem hp.2.2.1.2.2⟩
    · obtain ⟨p, a, b, hp, ha, hb, hxp⟩ := hx
      exact ⟨p, a, b, hp, ⟨hp.1, ha⟩, ⟨hp.2.1, hb⟩, PathBasics.interior_subset hxp⟩
  have hbetween : ∀ r s : Fin 3, r < s →
      Complete G (A' r) (A' s) ∧ Complete G (B' r) (B' s) ∧
      ∀ x ∈ A' r ∪ B' r ∪ C' r, ∀ y ∈ A' s ∪ B' s ∪ C' s,
        G.Adj x y → (x ∈ A' r ∧ y ∈ A' s) ∨ (x ∈ B' r ∧ y ∈ B' s) := by
    intro r s hrs
    refine ⟨hcompleteA r s hrs, hcompleteB r s hrs, ?_⟩
    intro x hx y hy hadj
    rcases fin3_cases r with rfl | rfl | rfl <;>
      rcases fin3_cases s with rfl | rfl | rfl
    all_goals try omega
    · simp only [A', B', C', regroupA, regroupB, regroupC, if_true, if_false,
        Set.mem_union] at hx hy ⊢
      rcases hy with ((hyA | hyA) | (hyB | hyB)) | (hyC | hyC)
      · rcases hcrossPP (i := 0) (j := 1) (by decide) hx
            (Or.inl (Or.inl hyA)) hadj with h | h
        · exact Or.inl ⟨h.1, Or.inl h.2⟩
        · exact Or.inr ⟨h.1, Or.inl h.2⟩
      · rcases hcrossPP (i := 0) (j := 2) (by decide) hx
            (Or.inl (Or.inl hyA)) hadj with h | h
        · exact Or.inl ⟨h.1, Or.inr h.2⟩
        · exact Or.inr ⟨h.1, Or.inr h.2⟩
      · rcases hcrossPP (i := 0) (j := 1) (by decide) hx
            (Or.inl (Or.inr hyB)) hadj with h | h
        · exact Or.inl ⟨h.1, Or.inl h.2⟩
        · exact Or.inr ⟨h.1, Or.inl h.2⟩
      · rcases hcrossPP (i := 0) (j := 2) (by decide) hx
            (Or.inl (Or.inr hyB)) hadj with h | h
        · exact Or.inl ⟨h.1, Or.inr h.2⟩
        · exact Or.inr ⟨h.1, Or.inr h.2⟩
      · rcases hcrossPP (i := 0) (j := 1) (by decide) hx (Or.inr hyC) hadj with h | h
        · exact Or.inl ⟨h.1, Or.inl h.2⟩
        · exact Or.inr ⟨h.1, Or.inl h.2⟩
      · rcases hcrossPP (i := 0) (j := 2) (by decide) hx (Or.inr hyC) hadj with h | h
        · exact Or.inl ⟨h.1, Or.inr h.2⟩
        · exact Or.inr ⟨h.1, Or.inr h.2⟩
    · obtain ⟨i, hxi, hiA, hiB, -⟩ := hprimeData (show (0 : Fin 3) ≠ 2 by decide) hx
      obtain ⟨j, hyj, hjA, hjB, -⟩ := hdoubleData hy
      rcases hcrossPD hxi hyj hadj with h | h
      · exact Or.inl ⟨hiA _ h.1, hjA _ h.2⟩
      · exact Or.inr ⟨hiB _ h.1, hjB _ h.2⟩
    · obtain ⟨i, hxi, hiA, hiB, -⟩ := hprimeData (show (1 : Fin 3) ≠ 2 by decide) hx
      obtain ⟨j, hyj, hjA, hjB, -⟩ := hdoubleData hy
      rcases hcrossPD hxi hyj hadj with h | h
      · exact Or.inl ⟨hiA _ h.1, hjA _ h.2⟩
      · exact Or.inr ⟨hiB _ h.1, hjB _ h.2⟩
  have hcover : ∀ r : Fin 3, ∀ x ∈ A' r ∪ B' r ∪ C' r,
      ∃ p : List V, IsRungOfHyperprism G A' B' C' r p ∧ x ∈ p := by
    intro r x hx
    by_cases hr : r = 2
    · subst r
      obtain ⟨i, hxi, hiA, hiB, hiC⟩ := hdoubleData hx
      obtain ⟨p, a, b, hp, ha, hb, hxp⟩ := hdoubleCover hxi
      refine ⟨p, ⟨a, b, hiA _ ha, hiB _ hb, hp.2.2.1, ?_⟩, hxp⟩
      intro z hz
      exact hiC z ⟨p, a, b, hp, ha.2, hb.2, hz⟩
    · obtain ⟨i, hxi, hiA, hiB, hiC⟩ := hprimeData hr hx
      obtain ⟨p, a, b, hp, ha, hb, hxp⟩ := hprimeCover hxi
      refine ⟨p, ⟨a, b, hiA _ ha, hiB _ hb, hp.2.2.1, ?_⟩, hxp⟩
      intro z hz
      exact hiC z ⟨p, a, b, hp, ha, hb, hz⟩
  have heven : ∃ p : List V,
      IsRungOfHyperprism G A' B' C' 0 p ∧ Even (pathLength p) := by
    obtain ⟨a, ha⟩ := hP0
    obtain ⟨p, b, hp, hb⟩ := exists_rung_prime_of_mem_P hH hs ha
    refine ⟨p, ⟨a, b, ?_, ?_, hp.2.2.1, ?_⟩, rung_even hG hH hp⟩
    · simpa [A', regroupA] using ha
    · simpa [B', regroupB] using hb
    · intro z hz
      change z ∈ Cp G A B C P Q 0
      exact ⟨p, a, b, hp, ha, hb, hz⟩
  exact ⟨hnonempty, hAB, hAC, hBC, hAA, hBB, hCC, hbetween, hcover, heven⟩

end Workspace.ProofLemmas.HyperprismLocalEnlargementRegroup
