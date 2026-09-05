import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementTwoEnded

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup

/-- PAPER (10.6, odd case, printed p. 62): *"But then [the displayed nine sets]
is a hyperprism."*

This is the clause-by-clause constructor behind that sentence.  Both ends of an outside
path are added to the two end sets of row zero, and its other vertices are added to the
middle set.  The hypotheses state exactly the permitted cross edges and supply the new
row-zero rung. -/
theorem twoEndedExtensionAtZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V)
    (hH : IsHyperprism G A B C) (p : List V) (u v : V)
    (hup : u ∈ p) (hvp : v ∈ p) (huv : u ≠ v) (hnd : p.Nodup)
    (hout : ∀ z ∈ p, z ∉ hyperVerts A B C)
    (huComplete : ∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A k, G.Adj u a)
    (hvComplete : ∀ (k : Fin 3), k ≠ 0 → ∀ b ∈ B k, G.Adj v b)
    (hcross : ∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
      ∀ y ∈ A k ∪ B k ∪ C k, G.Adj z y →
        (z = u ∧ y ∈ A k) ∨ (z = v ∧ y ∈ B k))
    (hnewRung :
      let A' := fun k : Fin 3 => if k = 0 then A k ∪ {u} else A k
      let B' := fun k : Fin 3 => if k = 0 then B k ∪ {v} else B k
      let C' := fun k : Fin 3 =>
        if k = 0 then C k ∪ {z : V | z ∈ p ∧ z ≠ u ∧ z ≠ v} else C k
      ∃ q : List V, IsRungOfHyperprism G A' B' C' 0 q ∧ ∀ z ∈ p, z ∈ q) :
    BiggerHyperprism G A B C := by
  classical
  let T : Set V := {z : V | z ∈ p ∧ z ≠ u ∧ z ≠ v}
  let A' : Fin 3 → Set V := fun k => if k = 0 then A k ∪ {u} else A k
  let B' : Fin 3 → Set V := fun k => if k = 0 then B k ∪ {v} else B k
  let C' : Fin 3 → Set V := fun k => if k = 0 then C k ∪ T else C k
  have houtA : ∀ {z : V}, z ∈ p → ∀ k : Fin 3, z ∉ A k := by
    intro z hz k hza
    exact hout z hz (mem_hyperVerts_iff.mpr ⟨k, Or.inl (Or.inl hza)⟩)
  have houtB : ∀ {z : V}, z ∈ p → ∀ k : Fin 3, z ∉ B k := by
    intro z hz k hzb
    exact hout z hz (mem_hyperVerts_iff.mpr ⟨k, Or.inl (Or.inr hzb)⟩)
  have houtC : ∀ {z : V}, z ∈ p → ∀ k : Fin 3, z ∉ C k := by
    intro z hz k hzc
    exact hout z hz (mem_hyperVerts_iff.mpr ⟨k, Or.inr hzc⟩)
  have hmemA : ∀ {k : Fin 3} {x : V}, x ∈ A' k → x ∈ A k ∨ (k = 0 ∧ x = u) := by
    intro k x hx
    by_cases hk : k = 0
    · subst k
      change x ∈ A 0 ∪ {u} at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨rfl, hx⟩
    · exact Or.inl (by simpa [A', hk] using hx)
  have hmemB : ∀ {k : Fin 3} {x : V}, x ∈ B' k → x ∈ B k ∨ (k = 0 ∧ x = v) := by
    intro k x hx
    by_cases hk : k = 0
    · subst k
      change x ∈ B 0 ∪ {v} at hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr ⟨rfl, hx⟩
    · exact Or.inl (by simpa [B', hk] using hx)
  have hmemC : ∀ {k : Fin 3} {x : V}, x ∈ C' k → x ∈ C k ∨ (k = 0 ∧ x ∈ T) := by
    intro k x hx
    by_cases hk : k = 0
    · subst k
      simpa [C'] using hx
    · exact Or.inl (by simpa [C', hk] using hx)
  have hAold : ∀ k : Fin 3, A k ⊆ A' k := by
    intro k x hx
    by_cases hk : k = 0
    · subst k; exact Or.inl hx
    · simpa [A', hk] using hx
  have hBold : ∀ k : Fin 3, B k ⊆ B' k := by
    intro k x hx
    by_cases hk : k = 0
    · subst k; exact Or.inl hx
    · simpa [B', hk] using hx
  have hCold : ∀ k : Fin 3, C k ⊆ C' k := by
    intro k x hx
    by_cases hk : k = 0
    · subst k; exact Or.inl hx
    · simpa [C', hk] using hx
  have hAB : ∀ i j : Fin 3, Disjoint (A' i) (B' j) := by
    intro i j
    rw [Set.disjoint_left]
    intro x hxa hxb
    rcases hmemA hxa with hxa | ⟨rfl, rfl⟩ <;>
      rcases hmemB hxb with hxb | ⟨rfl, hxv⟩
    · exact Set.disjoint_left.mp (hH.2.1 i j) hxa hxb
    · subst x; exact houtA hvp i hxa
    · exact houtB hup j hxb
    · exact huv hxv
  have hAC : ∀ i j : Fin 3, Disjoint (A' i) (C' j) := by
    intro i j
    rw [Set.disjoint_left]
    intro x hxa hxc
    rcases hmemA hxa with hxa | ⟨rfl, rfl⟩ <;>
      rcases hmemC hxc with hxc | ⟨rfl, hxt⟩
    · exact Set.disjoint_left.mp (hH.2.2.1 i j) hxa hxc
    · exact houtA hxt.1 i hxa
    · exact houtC hup j hxc
    · exact hxt.2.1 rfl
  have hBC : ∀ i j : Fin 3, Disjoint (B' i) (C' j) := by
    intro i j
    rw [Set.disjoint_left]
    intro x hxb hxc
    rcases hmemB hxb with hxb | ⟨rfl, rfl⟩ <;>
      rcases hmemC hxc with hxc | ⟨rfl, hxt⟩
    · exact Set.disjoint_left.mp (hH.2.2.2.1 i j) hxb hxc
    · exact houtB hxt.1 i hxb
    · exact houtC hvp j hxc
    · exact hxt.2.2 rfl
  have hAA : ∀ i j : Fin 3, i ≠ j → Disjoint (A' i) (A' j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases hmemA hxi with hxi | ⟨hi, hxu⟩ <;>
      rcases hmemA hxj with hxj | ⟨hj, hxu'⟩
    · exact Set.disjoint_left.mp (hH.2.2.2.2.1 i j hij) hxi hxj
    · exact houtA hup i (hxu' ▸ hxi)
    · exact houtA hup j (hxu ▸ hxj)
    · exact hij (hi.trans hj.symm)
  have hBB : ∀ i j : Fin 3, i ≠ j → Disjoint (B' i) (B' j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases hmemB hxi with hxi | ⟨hi, hxv⟩ <;>
      rcases hmemB hxj with hxj | ⟨hj, hxv'⟩
    · exact Set.disjoint_left.mp (hH.2.2.2.2.2.1 i j hij) hxi hxj
    · exact houtB hvp i (hxv' ▸ hxi)
    · exact houtB hvp j (hxv ▸ hxj)
    · exact hij (hi.trans hj.symm)
  have hCC : ∀ i j : Fin 3, i ≠ j → Disjoint (C' i) (C' j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases hmemC hxi with hxi | ⟨hi, hxi⟩ <;>
      rcases hmemC hxj with hxj | ⟨hj, hxj⟩
    · exact Set.disjoint_left.mp (hH.2.2.2.2.2.2.1 i j hij) hxi hxj
    · exact houtC hxj.1 i hxi
    · exact houtC hxi.1 j hxj
    · exact hij (hi.trans hj.symm)
  have hbetween : ∀ i j : Fin 3, i < j →
      Complete G (A' i) (A' j) ∧ Complete G (B' i) (B' j) ∧
      ∀ x ∈ A' i ∪ B' i ∪ C' i, ∀ y ∈ A' j ∪ B' j ∪ C' j,
        G.Adj x y → (x ∈ A' i ∧ y ∈ A' j) ∨ (x ∈ B' i ∧ y ∈ B' j) := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    have hj0 : j ≠ 0 := by omega
    have hAj : A' j = A j := by simp [A', hj0]
    have hBj : B' j = B j := by simp [B', hj0]
    have hCj : C' j = C j := by simp [C', hj0]
    refine ⟨?_, ?_, ?_⟩
    · intro x hx y hy
      rw [hAj] at hy
      rcases hmemA hx with hx | ⟨hi0, rfl⟩
      · exact complete_A hH hne x hx y hy
      · exact huComplete j hj0 y hy
    · intro x hx y hy
      rw [hBj] at hy
      rcases hmemB hx with hx | ⟨hi0, rfl⟩
      · exact complete_B hH hne x hx y hy
      · exact hvComplete j hj0 y hy
    · intro x hx y hy hadj
      rw [hAj, hBj, hCj] at hy
      have hyOld : y ∈ A j ∪ B j ∪ C j := hy
      rcases hx with (hxA | hxB) | hxC
      · rcases hmemA hxA with hxAold | ⟨hi0, hxu⟩
        · rcases cross hH hne (Or.inl (Or.inl hxAold)) hyOld hadj with h | h
          · exact Or.inl ⟨hAold i h.1, hAj.symm ▸ h.2⟩
          · exact Or.inr ⟨hBold i h.1, hBj.symm ▸ h.2⟩
        · have hxp : x ∈ p := hxu ▸ hup
          rcases hcross x hxp j hj0 y hyOld hadj with h | h
          · exact Or.inl ⟨hxA, hAj.symm ▸ h.2⟩
          · exact absurd (hxu.symm.trans h.1) huv
      · rcases hmemB hxB with hxBold | ⟨hi0, hxv⟩
        · rcases cross hH hne (Or.inl (Or.inr hxBold)) hyOld hadj with h | h
          · exact Or.inl ⟨hAold i h.1, hAj.symm ▸ h.2⟩
          · exact Or.inr ⟨hBold i h.1, hBj.symm ▸ h.2⟩
        · have hxp : x ∈ p := hxv ▸ hvp
          rcases hcross x hxp j hj0 y hyOld hadj with h | h
          · exact absurd (h.1.symm.trans hxv) huv
          · exact Or.inr ⟨hxB, hBj.symm ▸ h.2⟩
      · rcases hmemC hxC with hxC | ⟨hi0, hxT⟩
        · rcases cross hH hne (Or.inr hxC) hyOld hadj with h | h
          · exact Or.inl ⟨hAold i h.1, hAj.symm ▸ h.2⟩
          · exact Or.inr ⟨hBold i h.1, hBj.symm ▸ h.2⟩
        · rcases hcross x hxT.1 j hj0 y hyOld hadj with h | h
          · exact absurd h.1 hxT.2.1
          · exact absurd h.1 hxT.2.2
  have hcover : ∀ i : Fin 3, ∀ x ∈ A' i ∪ B' i ∪ C' i,
      ∃ q : List V, IsRungOfHyperprism G A' B' C' i q ∧ x ∈ q := by
    intro i x hx
    rcases hx with (hxA | hxB) | hxC
    · rcases hmemA hxA with hxA | ⟨hi, hxu⟩
      · obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hxq⟩ :=
          hH.2.2.2.2.2.2.2.2.1 i x (Or.inl (Or.inl hxA))
        exact ⟨q, ⟨a, b, hAold i ha, hBold i hb, hq, fun z hz => hCold i (hqC z hz)⟩, hxq⟩
      · subst i
        obtain ⟨q, hq, hqp⟩ := hnewRung
        exact ⟨q, hq, hqp x (hxu ▸ hup)⟩
    · rcases hmemB hxB with hxB | ⟨hi, hxv⟩
      · obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hxq⟩ :=
          hH.2.2.2.2.2.2.2.2.1 i x (Or.inl (Or.inr hxB))
        exact ⟨q, ⟨a, b, hAold i ha, hBold i hb, hq, fun z hz => hCold i (hqC z hz)⟩, hxq⟩
      · subst i
        obtain ⟨q, hq, hqp⟩ := hnewRung
        exact ⟨q, hq, hqp x (hxv ▸ hvp)⟩
    · rcases hmemC hxC with hxC | ⟨hi, hxT⟩
      · obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hxq⟩ :=
          hH.2.2.2.2.2.2.2.2.1 i x (Or.inr hxC)
        exact ⟨q, ⟨a, b, hAold i ha, hBold i hb, hq, fun z hz => hCold i (hqC z hz)⟩, hxq⟩
      · subst i
        obtain ⟨q, hq, hqp⟩ := hnewRung
        exact ⟨q, hq, hqp x hxT.1⟩
  have heven : ∃ q : List V, IsRungOfHyperprism G A' B' C' 0 q ∧ Even (pathLength q) := by
    obtain ⟨q, ⟨a, b, ha, hb, hq, hqC⟩, hev⟩ := hH.2.2.2.2.2.2.2.2.2
    exact ⟨q, ⟨a, b, hAold 0 ha, hBold 0 hb, hq, fun z hz => hCold 0 (hqC z hz)⟩, hev⟩
  have hH' : IsHyperprism G A' B' C' :=
    ⟨fun i => ⟨Set.Nonempty.mono (hAold i) (hH.1 i).1,
        Set.Nonempty.mono (hBold i) (hH.1 i).2.1,
        Set.Nonempty.mono (hCold i) (hH.1 i).2.2⟩,
      hAB, hAC, hBC, hAA, hBB, hCC, hbetween, hcover, heven⟩
  refine ⟨A', B', C', hH', ?_⟩
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    exact mem_hyperVerts_iff.mpr ⟨i, by
      rcases hi with (hi | hi) | hi
      · exact Or.inl (Or.inl (hAold i hi))
      · exact Or.inl (Or.inr (hBold i hi))
      · exact Or.inr (hCold i hi)⟩
  · intro heq
    have huNew : u ∈ hyperVerts A' B' C' :=
      mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inl (by simp [A']))⟩
    exact hout u hup (heq.symm ▸ huNew)

end Workspace.ProofLemmas.HyperprismLocalEnlargementTwoEnded
