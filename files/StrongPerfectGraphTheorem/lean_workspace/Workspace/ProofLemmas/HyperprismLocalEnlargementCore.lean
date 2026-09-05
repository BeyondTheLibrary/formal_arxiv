import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementCore

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup

/-- The elementary enlargement used in the first block of claim (2), and in the easy
subcase of the even block.  A path outside the old hyperprism is put into the first strip:
its first vertex is added to `A 0` and all its other vertices are added to `C 0`.

The hypotheses separate the two facts supplied by the paper.  The first new vertex is
complete to the other two `A`-sets, while the only edges from the new path to another strip
are those allowed edges.  The last hypothesis supplies one new rung containing the path. -/
theorem leftExtensionAtZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V)
    (hH : IsHyperprism G A B C) (p : List V) (u : V)
    (hup : u ∈ p) (hpNodup : p.Nodup)
    (hpOut : ∀ z ∈ p, z ∉ hyperVerts A B C)
    (huComplete : ∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A k, G.Adj u a)
    (hcross : ∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
      ∀ y ∈ A k ∪ B k ∪ C k, G.Adj z y → z = u ∧ y ∈ A k)
    (hnewRung :
      let A' := fun k : Fin 3 => if k = 0 then A k ∪ {u} else A k
      let C' := fun k : Fin 3 => if k = 0 then C k ∪ {z : V | z ∈ p ∧ z ≠ u} else C k
      ∃ q : List V, IsRungOfHyperprism G A' B C' 0 q ∧ ∀ z ∈ p, z ∈ q) :
    BiggerHyperprism G A B C := by
  classical
  let T : Set V := {z : V | z ∈ p ∧ z ≠ u}
  let A' : Fin 3 → Set V := fun k => if k = 0 then A k ∪ {u} else A k
  let C' : Fin 3 → Set V := fun k => if k = 0 then C k ∪ T else C k
  have hAold : ∀ k : Fin 3, A k ⊆ A' k := by
    intro k x hx
    by_cases hk : k = 0
    · subst k
      change x ∈ A 0 ∪ {u}
      exact Or.inl hx
    · simpa [A', hk] using hx
  have hCold : ∀ k : Fin 3, C k ⊆ C' k := by
    intro k x hx
    by_cases hk : k = 0
    · subst k
      change x ∈ C 0 ∪ T
      exact Or.inl hx
    · simpa [C', hk] using hx
  have houtA : ∀ {z : V}, z ∈ p → ∀ k : Fin 3, z ∉ A k := by
    intro z hz k hza
    exact hpOut z hz (mem_hyperVerts_iff.mpr ⟨k, Or.inl (Or.inl hza)⟩)
  have houtB : ∀ {z : V}, z ∈ p → ∀ k : Fin 3, z ∉ B k := by
    intro z hz k hzb
    exact hpOut z hz (mem_hyperVerts_iff.mpr ⟨k, Or.inl (Or.inr hzb)⟩)
  have houtC : ∀ {z : V}, z ∈ p → ∀ k : Fin 3, z ∉ C k := by
    intro z hz k hzc
    exact hpOut z hz (mem_hyperVerts_iff.mpr ⟨k, Or.inr hzc⟩)
  have hAprimeB : ∀ i j : Fin 3, Disjoint (A' i) (B j) := by
    intro i j
    rw [Set.disjoint_left]
    intro x hxA hxB
    by_cases hi : i = 0
    · subst i
      simp only [A', if_pos, Set.mem_union, Set.mem_singleton_iff] at hxA
      rcases hxA with hxA | hxu
      · exact Set.disjoint_left.mp (hH.2.1 0 j) hxA hxB
      · subst x
        exact houtB hup j hxB
    · have hxA0 : x ∈ A i := by simpa [A', hi] using hxA
      exact Set.disjoint_left.mp (hH.2.1 i j) hxA0 hxB
  have hAprimeC : ∀ i j : Fin 3, Disjoint (A' i) (C' j) := by
    intro i j
    rw [Set.disjoint_left]
    intro x hxA hxC
    by_cases hi : i = 0
    · subst i
      simp only [A', if_pos, Set.mem_union, Set.mem_singleton_iff] at hxA
      rcases hxA with hxA | hxu
      · by_cases hj : j = 0
        · subst j
          simp only [C', if_pos, Set.mem_union] at hxC
          rcases hxC with hxC | hxT
          · exact Set.disjoint_left.mp (hH.2.2.1 0 0) hxA hxC
          · exact houtA hxT.1 0 hxA
        · have hxC0 : x ∈ C j := by simpa [C', hj] using hxC
          exact Set.disjoint_left.mp (hH.2.2.1 0 j) hxA hxC0
      · by_cases hj : j = 0
        · subst j
          simp only [C', if_pos, Set.mem_union] at hxC
          rcases hxC with hxC | hxT
          · exact houtC hup 0 (hxu ▸ hxC)
          · exact hxT.2 hxu
        · have hxC0 : u ∈ C j := by simpa [C', hj, hxu] using hxC
          exact houtC hup j hxC0
    · have hxA0 : x ∈ A i := by simpa [A', hi] using hxA
      by_cases hj : j = 0
      · subst j
        simp only [C', if_pos, Set.mem_union] at hxC
        rcases hxC with hxC | hxT
        · exact Set.disjoint_left.mp (hH.2.2.1 i 0) hxA0 hxC
        · exact houtA hxT.1 i hxA0
      · have hxC0 : x ∈ C j := by simpa [C', hj] using hxC
        exact Set.disjoint_left.mp (hH.2.2.1 i j) hxA0 hxC0
  have hBCprime : ∀ i j : Fin 3, Disjoint (B i) (C' j) := by
    intro i j
    rw [Set.disjoint_left]
    intro x hxB hxC
    by_cases hj : j = 0
    · subst j
      simp only [C', if_pos, Set.mem_union] at hxC
      rcases hxC with hxC | hxT
      · exact Set.disjoint_left.mp (hH.2.2.2.1 i 0) hxB hxC
      · exact houtB hxT.1 i hxB
    · have hxC0 : x ∈ C j := by simpa [C', hj] using hxC
      exact Set.disjoint_left.mp (hH.2.2.2.1 i j) hxB hxC0
  have hAprimeAprime : ∀ i j : Fin 3, i ≠ j → Disjoint (A' i) (A' j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := fun h => hij h.symm
      simp only [A', if_pos, Set.mem_union, Set.mem_singleton_iff] at hxi
      have hxj0 : x ∈ A j := by simpa [A', hj] using hxj
      rcases hxi with hxi | hxu
      · exact Set.disjoint_left.mp (hH.2.2.2.2.1 0 j hij) hxi hxj0
      · subst x
        exact houtA hup j hxj0
    · by_cases hj : j = 0
      · have hxi0 : x ∈ A i := by simpa [A', hi] using hxi
        subst j
        simp only [A', if_pos, Set.mem_union, Set.mem_singleton_iff] at hxj
        rcases hxj with hxj | hxu
        · exact Set.disjoint_left.mp (hH.2.2.2.2.1 i 0 hij) hxi0 hxj
        · subst x
          exact houtA hup i hxi0
      · have hxi0 : x ∈ A i := by simpa [A', hi] using hxi
        have hxj0 : x ∈ A j := by simpa [A', hj] using hxj
        exact Set.disjoint_left.mp (hH.2.2.2.2.1 i j hij) hxi0 hxj0
  have hCprimeCprime : ∀ i j : Fin 3, i ≠ j → Disjoint (C' i) (C' j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := fun h => hij h.symm
      simp only [C', if_pos, Set.mem_union] at hxi
      have hxj0 : x ∈ C j := by simpa [C', hj] using hxj
      rcases hxi with hxi | hxT
      · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 0 j hij) hxi hxj0
      · exact houtC hxT.1 j hxj0
    · by_cases hj : j = 0
      · have hxi0 : x ∈ C i := by simpa [C', hi] using hxi
        subst j
        simp only [C', if_pos, Set.mem_union] at hxj
        rcases hxj with hxj | hxT
        · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 i 0 hij) hxi0 hxj
        · exact houtC hxT.1 i hxi0
      · have hxi0 : x ∈ C i := by simpa [C', hi] using hxi
        have hxj0 : x ∈ C j := by simpa [C', hj] using hxj
        exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 i j hij) hxi0 hxj0
  have hbetween : ∀ i j : Fin 3, i < j →
      Complete G (A' i) (A' j) ∧ Complete G (B i) (B j) ∧
        ∀ x ∈ A' i ∪ B i ∪ C' i, ∀ y ∈ A' j ∪ B j ∪ C' j,
          G.Adj x y → (x ∈ A' i ∧ y ∈ A' j) ∨ (x ∈ B i ∧ y ∈ B j) := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    have hj0 : j ≠ 0 := by omega
    refine ⟨?_, complete_B hH hne, ?_⟩
    · intro x hx y hy
      have hy0 : y ∈ A j := by simpa [A', hj0] using hy
      by_cases hi0 : i = 0
      · subst i
        simp only [A', if_pos, Set.mem_union, Set.mem_singleton_iff] at hx
        rcases hx with hx | hxu
        · exact complete_A hH hne x hx y hy0
        · subst x
          exact huComplete j hj0 y hy0
      · exact complete_A hH hne x (by simpa [A', hi0] using hx) y hy0
    · intro x hx y hy hadj
      have hyOld : y ∈ A j ∪ B j ∪ C j := by
        simpa [A', C', hj0] using hy
      by_cases hi0 : i = 0
      · subst i
        simp only [A', C', if_pos, Set.mem_union, Set.mem_singleton_iff] at hx
        rcases hx with ((hxA | hxu) | hxB) | (hxC | hxT)
        · have hold := cross hH hne (Or.inl (Or.inl hxA)) hyOld hadj
          rcases hold with h | h
          · exact Or.inl ⟨by simp [A', h.1], by simpa [A', hj0] using h.2⟩
          · exact Or.inr ⟨h.1, h.2⟩
        · subst x
          have hh := hcross u hup j hj0 y hyOld hadj
          exact Or.inl ⟨by simp [A'], by simpa [A', hj0] using hh.2⟩
        · have hold := cross hH hne (Or.inl (Or.inr hxB)) hyOld hadj
          rcases hold with h | h
          · exact Or.inl ⟨by simp [A', h.1], by simpa [A', hj0] using h.2⟩
          · exact Or.inr ⟨h.1, h.2⟩
        · have hold := cross hH hne (Or.inr hxC) hyOld hadj
          rcases hold with h | h
          · exact Or.inl ⟨by simp [A', h.1], by simpa [A', hj0] using h.2⟩
          · exact Or.inr ⟨h.1, h.2⟩
        · have hh := hcross x hxT.1 j hj0 y hyOld hadj
          exact absurd hh.1 hxT.2
      · have hxOld : x ∈ A i ∪ B i ∪ C i := by simpa [A', C', hi0] using hx
        rcases cross hH hne hxOld hyOld hadj with h | h
        · exact Or.inl ⟨by simpa [A', hi0] using h.1, by simpa [A', hj0] using h.2⟩
        · exact Or.inr h
  have hcover : ∀ i : Fin 3, ∀ x ∈ A' i ∪ B i ∪ C' i,
      ∃ q : List V, IsRungOfHyperprism G A' B C' i q ∧ x ∈ q := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      simp only [A', C', if_pos, Set.mem_union, Set.mem_singleton_iff] at hx
      rcases hx with ((hxA | hxu) | hxB) | (hxC | hxT)
      · obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hxq⟩ :=
          hH.2.2.2.2.2.2.2.2.1 0 x (Or.inl (Or.inl hxA))
        exact ⟨q, ⟨a, b, by simp [A', ha], hb, hq,
          fun z hz => by simp [C', hqC z hz]⟩, hxq⟩
      · obtain ⟨q, hq, hqp⟩ := hnewRung
        exact ⟨q, hq, hqp x (hxu ▸ hup)⟩
      · obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hxq⟩ :=
          hH.2.2.2.2.2.2.2.2.1 0 x (Or.inl (Or.inr hxB))
        exact ⟨q, ⟨a, b, by simp [A', ha], hb, hq,
          fun z hz => by simp [C', hqC z hz]⟩, hxq⟩
      · obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hxq⟩ :=
          hH.2.2.2.2.2.2.2.2.1 0 x (Or.inr hxC)
        exact ⟨q, ⟨a, b, by simp [A', ha], hb, hq,
          fun z hz => by simp [C', hqC z hz]⟩, hxq⟩
      · obtain ⟨q, hq, hqp⟩ := hnewRung
        exact ⟨q, hq, hqp x hxT.1⟩
    · have hxOld : x ∈ A i ∪ B i ∪ C i := by simpa [A', C', hi] using hx
      obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hxq⟩ :=
        hH.2.2.2.2.2.2.2.2.1 i x hxOld
      exact ⟨q, ⟨a, b, by simpa [A', hi] using ha, hb, hq,
        fun z hz => by simpa [C', hi] using hqC z hz⟩, hxq⟩
  have heven : ∃ q : List V, IsRungOfHyperprism G A' B C' 0 q ∧ Even (pathLength q) := by
    obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hev⟩ := hH.2.2.2.2.2.2.2.2.2
    exact ⟨q, ⟨a, b, by simp [A', ha], hb, hq,
      fun z hz => by simp [C', hqC z hz]⟩, hev⟩
  have hH' : IsHyperprism G A' B C' :=
    ⟨fun i => ⟨(Set.Nonempty.mono (hAold i) (hH.1 i).1), (hH.1 i).2.1,
        Set.Nonempty.mono (hCold i) (hH.1 i).2.2⟩,
      hAprimeB, hAprimeC, hBCprime, hAprimeAprime, hH.2.2.2.2.2.1,
      hCprimeCprime, hbetween, hcover, heven⟩
  refine ⟨A', B, C', hH', ?_⟩
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    exact mem_hyperVerts_iff.mpr ⟨i, by
      rcases hi with (hi | hi) | hi
      · exact Or.inl (Or.inl (hAold i hi))
      · exact Or.inl (Or.inr hi)
      · exact Or.inr (hCold i hi)⟩
  · intro heq
    have huNew : u ∈ hyperVerts A' B C' :=
      mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inl (by simp [A']))⟩
    have huOld : u ∈ hyperVerts A B C := heq.symm ▸ huNew
    exact hpOut u hup huOld

end Workspace.ProofLemmas.HyperprismLocalEnlargementCore
