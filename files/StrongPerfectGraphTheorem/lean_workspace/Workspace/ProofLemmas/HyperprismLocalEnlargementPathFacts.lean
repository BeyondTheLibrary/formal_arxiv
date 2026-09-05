import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.ProofLemmas.PathGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementPathFacts

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup

private theorem outside_rung
    {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}
    {f R : List V} {a b : V} {k : Fin 3}
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hR : IsRungFrom G A B C k R a b) : ∀ z ∈ f, z ∉ R := by
  intro z hzf hzR
  exact hfout z hzf (rung_subset_hyperVerts hR z hzR)

/-- The parity test used at the start of the even block.  The path has attachments in
`A 0` and `B 1`.  For a rung of the third strip, exactly one of its `A`-end seeing the
first path vertex and its `B`-end seeing the last path vertex occurs.

This is the pair of paper sentences saying that the long displayed cycle is not an odd
hole, and that if both edges occurred the shorter displayed cycle would be an odd hole. -/
theorem thirdRungXor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (hG : Berge G)
    (hH : IsHyperprism G A B C)
    (f : List V) (f₁ fn xA xB : V)
    (hf : IsPathFrom G f f₁ fn)
    (hfull : IsPathFrom G (xA :: (f ++ [xB])) xA xB)
    (hEven : Even f.length)
    (hxAA : xA ∈ A 0) (hxBB : xB ∈ B 1)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hAonly : ∀ z ∈ f, ∀ a ∈ A 2, G.Adj z a → z = f₁)
    (hBonly : ∀ z ∈ f, ∀ b ∈ B 2, G.Adj z b → z = fn)
    (hCnone : ∀ z ∈ f, ∀ (m : Fin 3) (c : V), c ∈ C m → ¬ G.Adj z c)
    {R : List V} {a b : V} (hR : IsRungFrom G A B C 2 R a b) :
    (G.Adj f₁ a ∨ G.Adj fn b) ∧ ¬ (G.Adj f₁ a ∧ G.Adj fn b) := by
  have hRrev : IsPathFrom G R.reverse b a := PathBasics.isPathFrom_reverse hR.2.2.1
  have hdisjFull : ∀ z ∈ xA :: (f ++ [xB]), z ∉ R.reverse := by
    intro z hz hzR
    rw [List.mem_reverse] at hzR
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
    rcases hz with hzx | hzf | hzx
    · subst z
      exact notMem_S hH (show (0 : Fin 3) ≠ 2 by decide)
        (Or.inl (Or.inl hxAA)) (rung_mem_S hR xA hzR)
    · exact outside_rung hfout hR z hzf hzR
    · subst z
      exact notMem_S hH (show (1 : Fin 3) ≠ 2 by decide)
        (Or.inl (Or.inr hxBB)) (rung_mem_S hR xB hzR)
  have hdisjf : ∀ z ∈ f, z ∉ R.reverse := by
    intro z hz hzR
    rw [List.mem_reverse] at hzR
    exact outside_rung hfout hR z hz hzR
  have hxABne : xA ≠ xB := by
    intro h
    exact Set.disjoint_left.mp (hH.2.1 0 1) hxAA (h.symm ▸ hxBB)
  have hxA_cross : ∀ y ∈ R, G.Adj xA y ↔ y = a := by
    intro y hy
    constructor
    · intro hadj
      rcases cross hH (show (0 : Fin 3) ≠ 2 by decide) (Or.inl (Or.inl hxAA))
          (rung_mem_S hR y hy) hadj with h | h
      · exact rung_eq_A hH hR hy h.2
      · exact absurd h.1 (Set.disjoint_left.mp (hH.2.1 0 0) hxAA)
    · intro hya
      rw [hya]
      exact complete_A hH (show (0 : Fin 3) ≠ 2 by decide) xA hxAA a hR.1
  have hxB_cross : ∀ y ∈ R, G.Adj xB y ↔ y = b := by
    intro y hy
    constructor
    · intro hadj
      rcases cross hH (show (1 : Fin 3) ≠ 2 by decide) (Or.inl (Or.inr hxBB))
          (rung_mem_S hR y hy) hadj with h | h
      · exact (Set.disjoint_left.mp (hH.2.1 1 1) h.1 hxBB).elim
      · exact rung_eq_B hH hR hy h.2
    · intro hyb
      rw [hyb]
      exact complete_B hH (show (1 : Fin 3) ≠ 2 by decide) xB hxBB b hR.2.1
  have f_cross (hna : ¬ G.Adj f₁ a) (hnb : ¬ G.Adj fn b) :
      ∀ z ∈ f, ∀ y ∈ R, ¬ G.Adj z y := by
    intro z hzf y hy hadj
    rcases rung_mem_S hR y hy with (hyA | hyB) | hyC
    · have hz := hAonly z hzf y hyA hadj
      have hya := rung_eq_A hH hR hy hyA
      exact hna (hz ▸ hya ▸ hadj)
    · have hz := hBonly z hzf y hyB hadj
      have hyb := rung_eq_B hH hR hy hyB
      exact hnb (hz ▸ hyb ▸ hadj)
    · exact hCnone z hzf 2 y hyC hadj
  constructor
  · by_contra hneither
    simp only [not_or] at hneither
    have hcrossFull : ∀ z ∈ xA :: (f ++ [xB]), ∀ y ∈ R.reverse,
        G.Adj z y ↔ (z = xB ∧ y = b) ∨ (z = xA ∧ y = a) := by
      intro z hz y hy
      rw [List.mem_reverse] at hy
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz
      rcases hz with hzx | hzf | hzx
      · subst z
        rw [hxA_cross y hy]
        constructor
        · intro hya
          exact Or.inr ⟨rfl, hya⟩
        · intro hor
          rcases hor with h | h
          · exact (hxABne h.1).elim
          · exact h.2
      · have hn := f_cross hneither.1 hneither.2 z hzf y hy
        exact iff_of_false hn (by
          rintro (⟨hzx, -⟩ | ⟨hzx, -⟩) <;> subst z
          · exact hfout xB hzf (mem_hyperVerts_iff.mpr ⟨1, Or.inl (Or.inr hxBB)⟩)
          · exact hfout xA hzf (mem_hyperVerts_iff.mpr ⟨0, Or.inl (Or.inl hxAA)⟩))
      · subst z
        rw [hxB_cross y hy]
        constructor
        · intro hyb
          exact Or.inl ⟨rfl, hyb⟩
        · intro hor
          rcases hor with h | h
          · exact h.2
          · exact (hxABne h.1.symm).elim
    have hhole := PathGlue.glue_hole hfull hRrev hdisjFull hcrossFull (by
      have hfpos := PathBasics.path_length_pos hf.1
      have hRlen := rung_two_le_length hH hR
      simp only [List.length_cons, List.length_append, List.length_nil, List.length_reverse]
      omega)
    have hevenHole := hG.1 _ hhole
    have hRevLen : R.reverse.length = pathLength R + 1 := by
      rw [List.length_reverse]
      exact PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
    rw [holeLength, List.length_append, hRevLen, Nat.even_iff] at hevenHole
    rw [Nat.even_iff] at hEven
    have hReven := rung_even hG hH hR
    rw [Nat.even_iff] at hReven
    simp only [List.length_cons, List.length_append, List.length_nil] at hevenHole
    omega
  · rintro ⟨hfa, hfb⟩
    have hflen2 : 2 ≤ f.length := by
      have hpos := PathBasics.path_length_pos hf.1
      have hev := hEven
      rw [Nat.even_iff] at hev
      omega
    have hcrossShort : ∀ z ∈ f, ∀ y ∈ R.reverse,
        G.Adj z y ↔ (z = fn ∧ y = b) ∨ (z = f₁ ∧ y = a) := by
      intro z hzf y hy
      rw [List.mem_reverse] at hy
      constructor
      · intro hadj
        rcases rung_mem_S hR y hy with (hyA | hyB) | hyC
        · exact Or.inr ⟨hAonly z hzf y hyA hadj, rung_eq_A hH hR hy hyA⟩
        · exact Or.inl ⟨hBonly z hzf y hyB hadj, rung_eq_B hH hR hy hyB⟩
        · exact absurd hadj (hCnone z hzf 2 y hyC)
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hfb
        · exact hfa
    have hhole := PathGlue.glue_hole hf hRrev hdisjf hcrossShort (by
      have hfpos := PathBasics.path_length_pos hf.1
      have hRlen := rung_two_le_length hH hR
      rw [List.length_reverse]
      omega)
    have hevenHole := hG.1 _ hhole
    have hRlen : R.length = pathLength R + 1 :=
      PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
    rw [holeLength, List.length_append, List.length_reverse, hRlen, Nat.even_iff] at hevenHole
    rw [Nat.even_iff] at hEven
    have hReven := rung_even hG hH hR
    rw [Nat.even_iff] at hReven
    omega

/-- `thirdRungXor` with arbitrary names for the three distinct strips. -/
theorem rungXor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (hG : Berge G)
    (hH : IsHyperprism G A B C)
    (f : List V) (f₁ fn xA xB : V)
    (hf : IsPathFrom G f f₁ fn)
    (hfull : IsPathFrom G (xA :: (f ++ [xB])) xA xB)
    (hEven : Even f.length)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hxAA : xA ∈ A i) (hxBB : xB ∈ B j)
    (hfout : ∀ z ∈ f, z ∉ hyperVerts A B C)
    (hAonly : ∀ z ∈ f, ∀ a ∈ A k, G.Adj z a → z = f₁)
    (hBonly : ∀ z ∈ f, ∀ b ∈ B k, G.Adj z b → z = fn)
    (hCnone : ∀ z ∈ f, ∀ (m : Fin 3) (c : V), c ∈ C m → ¬ G.Adj z c)
    {R : List V} {a b : V} (hR : IsRungFrom G A B C k R a b) :
    (G.Adj f₁ a ∨ G.Adj fn b) ∧ ¬ (G.Adj f₁ a ∧ G.Adj fn b) := by
  have perm_of_three : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j ∧ σ 2 = k := by decide
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := perm_of_three i j k hij hik hjk
  have hH' := HyperprismTwoAttachments.isHyperprism_perm hG hH σ
  have hfout' : ∀ z ∈ f,
      z ∉ hyperVerts (fun m => A (σ m)) (fun m => B (σ m)) (fun m => C (σ m)) := by
    intro z hz hmem
    exact hfout z hz (by rwa [hyperVerts_perm] at hmem)
  have hR' : IsRungFrom G (fun m => A (σ m)) (fun m => B (σ m))
      (fun m => C (σ m)) 2 R a b := by
    simpa only [IsRungFrom, hσ2] using hR
  exact thirdRungXor G (fun m => A (σ m)) (fun m => B (σ m)) (fun m => C (σ m))
    hG hH' f f₁ fn xA xB hf hfull hEven (by simpa only [hσ0] using hxAA)
    (by simpa only [hσ1] using hxBB) hfout'
    (by simpa only [hσ2] using hAonly) (by simpa only [hσ2] using hBonly)
    (fun z hz m c hc => hCnone z hz (σ m) c hc) hR'

end Workspace.ProofLemmas.HyperprismLocalEnlargementPathFacts
