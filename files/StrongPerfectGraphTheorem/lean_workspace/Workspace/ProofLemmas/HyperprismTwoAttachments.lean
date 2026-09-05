import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HyperprismBasics

/-!
# Hyperprism symmetries, and the non-local pair (P4 of the 10.6 decomposition)

Two separate jobs, both feeding claim (2) of the proof of **10.6**.

## (a) The symmetries the printed proof keeps invoking

The proof of 10.6 says *"we may assume"* five times, and every one of them is one of two
symmetries of a hyperprism:

* *"By exchanging `S₂` and `S₃` …"*, *"by exchanging `S₁` and `S₂` …"*, *"We may assume that
  `x₁ ∈ A₁` and `x₂ ∈ B₂`"* — permuting the three strips: `isHyperprism_perm`.
  This needs `Berge G`, because the last clause of `IsHyperprism` singles out index `0`
  (*"some path between `A₁` and `B₁` … is even"*); once claim (1)
  (`HyperprismBasics.rung_even`) is available every index satisfies it, so the clause
  transports.
* *"up to the symmetry between `A` and `B`"*, *"and the same for `B`"* — swapping the two
  ends: `isHyperprism_swap`, which reverses every rung and needs no hypothesis.

## (b) The non-local pair

> *"We claim there is a 2-element subset of `X` which is also not local.  For we may assume
> `X ∩ A₁ ≠ ∅`; and hence if `X` meets `B₂` or `B₃` our claim holds.  If not, then it meets
> `B₁` (since it is not a subset of `A`) and meets `A₂ ∪ A₃` (since it is not a subset of
> `S₁`), and again the claim holds.  So there is a subset `{x₁,x₂}` of `X` which is not
> local."*  (printed p. 61)

`exists_nonlocal_pair` produces the pair directly, as `x₁ ∈ X ∩ Aᵢ` and `x₂ ∈ X ∩ Bⱼ` with
`i ≠ j` (the paper's `wlog i = 1, j = 2` is then `isHyperprism_perm`), and
`not_local_pair` records that such a pair is indeed non-local.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismTwoAttachments

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

/-! ### (a) Permuting the three strips -/

/-- *"By exchanging `S₂` and `S₃` it follows that …"* (printed p. 61, and four more times):
a hyperprism may be relabelled by any permutation of `{1,2,3}`.

`Berge G` is genuinely needed: the last clause of `IsHyperprism` asks for an **even** rung at
index `0` specifically, and after a permutation the witness sits at index `σ 0`.  Claim (1)
(`HyperprismBasics.rung_even`) supplies it. -/
theorem isHyperprism_perm (hG : Berge G) (hH : IsHyperprism G A B C) (σ : Equiv.Perm (Fin 3)) :
    IsHyperprism G (fun i => A (σ i)) (fun i => B (σ i)) (fun i => C (σ i)) := by
  refine ⟨fun i => hH.1 (σ i), fun i j => hH.2.1 (σ i) (σ j),
    fun i j => hH.2.2.1 (σ i) (σ j), fun i j => hH.2.2.2.1 (σ i) (σ j),
    fun i j hij => hH.2.2.2.2.1 (σ i) (σ j) (fun h => hij (σ.injective h)),
    fun i j hij => hH.2.2.2.2.2.1 (σ i) (σ j) (fun h => hij (σ.injective h)),
    fun i j hij => hH.2.2.2.2.2.2.1 (σ i) (σ j) (fun h => hij (σ.injective h)), ?_, ?_, ?_⟩
  · intro i j hij
    have hne : σ i ≠ σ j := fun h => (ne_of_lt hij) (σ.injective h)
    exact ⟨complete_A hH hne, complete_B hH hne, fun u hu v hv hadj => cross hH hne hu hv hadj⟩
  · intro i v hv
    exact hH.2.2.2.2.2.2.2.2.1 (σ i) v hv
  · obtain ⟨p, x, y, hp⟩ := exists_rung hH (σ 0)
    exact ⟨p, ⟨x, y, hp⟩, rung_even hG hH hp⟩

/-! ### (a′) Swapping the two ends -/

/-- *"up to the symmetry between `A` and `B`"* (printed p. 58, and *"and the same for `B`"*,
p. 62): the triple `(B, A, C)` is again a hyperprism.  Every rung is simply reversed. -/
theorem isHyperprism_swap (hH : IsHyperprism G A B C) : IsHyperprism G B A C := by
  have hSmem : ∀ (i : Fin 3) (v : V), v ∈ B i ∪ A i ∪ C i → v ∈ A i ∪ B i ∪ C i := by
    rintro i v ((h | h) | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  -- reversing a rung swaps its ends
  have hrev : ∀ (i : Fin 3) (p : List V), IsRungOfHyperprism G A B C i p →
      IsRungOfHyperprism G B A C i p.reverse := by
    rintro i p ⟨x, y, hx, hy, hpath, hint⟩
    refine ⟨y, x, hy, hx, PathBasics.isPathFrom_reverse hpath, ?_⟩
    intro w hw
    exact hint w (PathBasics.mem_interior_reverse.mp hw)
  refine ⟨fun i => ⟨(hH.1 i).2.1, (hH.1 i).1, (hH.1 i).2.2⟩,
    fun i j => (hH.2.1 j i).symm, fun i j => hH.2.2.2.1 i j, fun i j => hH.2.2.1 i j,
    fun i j hij => hH.2.2.2.2.2.1 i j hij, fun i j hij => hH.2.2.2.2.1 i j hij,
    fun i j hij => hH.2.2.2.2.2.2.1 i j hij, ?_, ?_, ?_⟩
  · intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    refine ⟨complete_B hH hne, complete_A hH hne, fun u hu v hv hadj => ?_⟩
    rcases cross hH hne (hSmem i u hu) (hSmem j v hv) hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
  · intro i v hv
    obtain ⟨p, hp, hvp⟩ := hH.2.2.2.2.2.2.2.2.1 i v (hSmem i v hv)
    exact ⟨p.reverse, hrev i p hp, List.mem_reverse.mpr hvp⟩
  · obtain ⟨p, hp, hev⟩ := hH.2.2.2.2.2.2.2.2.2
    refine ⟨p.reverse, hrev 0 p hp, ?_⟩
    rwa [PathBasics.pathLength_reverse]

/-! ### (b) The non-local pair -/

/-- A pair consisting of a vertex of `Aᵢ` and a vertex of `Bⱼ` with `i ≠ j` is never local. -/
theorem not_local_pair (hH : IsHyperprism G A B C) {i j : Fin 3} (hij : i ≠ j) {x₁ x₂ : V}
    (hx₁ : x₁ ∈ A i) (hx₂ : x₂ ∈ B j) :
    ¬ LocalForHyperprism A B C ({x₁, x₂} : Set V) := by
  have hx₁mem : x₁ ∈ ({x₁, x₂} : Set V) := Or.inl rfl
  have hx₂mem : x₂ ∈ ({x₁, x₂} : Set V) := Or.inr rfl
  have hSi : ∀ k : Fin 3, x₁ ∈ A k ∪ B k ∪ C k → k = i := by
    intro k hk
    by_contra hne
    exact notMem_S hH (fun h => hne h.symm) (Or.inl (Or.inl hx₁)) hk
  have hSj : ∀ k : Fin 3, x₂ ∈ A k ∪ B k ∪ C k → k = j := by
    intro k hk
    by_contra hne
    exact notMem_S hH (fun h => hne h.symm) (Or.inl (Or.inr hx₂)) hk
  have hx₁nB : ∀ k : Fin 3, x₁ ∉ B k := fun k => Set.disjoint_left.mp (hH.2.1 i k) hx₁
  have hx₂nA : ∀ k : Fin 3, x₂ ∉ A k := fun k hk =>
    Set.disjoint_left.mp (hH.2.1 k j) hk hx₂
  rintro (h | h | h | h | h)
  · exact hij ((hSi 0 (h hx₁mem)).symm.trans (hSj 0 (h hx₂mem)))
  · exact hij ((hSi 1 (h hx₁mem)).symm.trans (hSj 1 (h hx₂mem)))
  · exact hij ((hSi 2 (h hx₁mem)).symm.trans (hSj 2 (h hx₂mem)))
  · -- `{x₁,x₂} ⊆ A`, but `x₂ ∈ B j`
    rcases h hx₂mem with (a | a) | a
    · exact hx₂nA 0 a
    · exact hx₂nA 1 a
    · exact hx₂nA 2 a
  · -- `{x₁,x₂} ⊆ B`, but `x₁ ∈ A i`
    rcases h hx₁mem with (a | a) | a
    · exact hx₁nB 0 a
    · exact hx₁nB 1 a
    · exact hx₁nB 2 a

/-- **The non-local pair** (printed p. 61).  A non-local set `X` contained in `A ∪ B` has a
vertex in some `Aᵢ` and a vertex in some `Bⱼ` with `i ≠ j`; by `not_local_pair` that pair is
itself non-local, and `isHyperprism_perm` normalises `(i,j)` to the paper's `(1,2)`. -/
theorem exists_nonlocal_pair {A B C : Fin 3 → Set V} {X : Set V}
    (hXAB : ∀ v ∈ X, (∃ k : Fin 3, v ∈ A k) ∨ (∃ k : Fin 3, v ∈ B k))
    (hnl : ¬ LocalForHyperprism A B C X) :
    ∃ (i j : Fin 3) (x₁ x₂ : V), i ≠ j ∧ x₁ ∈ X ∧ x₂ ∈ X ∧ x₁ ∈ A i ∧ x₂ ∈ B j := by
  rw [LocalForHyperprism] at hnl
  push Not at hnl
  obtain ⟨h0, h1, h2, hA, hB⟩ := hnl
  have hbigA : ∀ (k : Fin 3) (v : V), v ∈ A k → v ∈ A 0 ∪ A 1 ∪ A 2 := by
    intro k v hv
    rcases fin3_cases k with rfl | rfl | rfl
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  have hbigB : ∀ (k : Fin 3) (v : V), v ∈ B k → v ∈ B 0 ∪ B 1 ∪ B 2 := by
    intro k v hv
    rcases fin3_cases k with rfl | rfl | rfl
    · exact Or.inl (Or.inl hv)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  -- `X ⊄ B`, so `X` meets some `Aᵢ`.
  obtain ⟨a, haX, haB⟩ := Set.not_subset.mp hB
  obtain ⟨i₀, hi₀⟩ : ∃ k : Fin 3, a ∈ A k := by
    rcases hXAB a haX with h | ⟨k, hk⟩
    · exact h
    · exact absurd (hbigB k a hk) haB
  -- `X ⊄ A`, so `X` meets some `Bⱼ`.
  obtain ⟨b, hbX, hbA⟩ := Set.not_subset.mp hA
  obtain ⟨j₀, hj₀⟩ : ∃ k : Fin 3, b ∈ B k := by
    rcases hXAB b hbX with ⟨k, hk⟩ | h
    · exact absurd (hbigA k b hk) hbA
    · exact h
  by_cases hne : i₀ = j₀
  · -- the two witnesses sit in the same strip; use `X ⊄ Sᵢ₀` to find a third one
    subst hne
    obtain ⟨c, hcX, hcS⟩ : ∃ c ∈ X, c ∉ A i₀ ∪ B i₀ ∪ C i₀ := by
      rcases fin3_cases i₀ with rfl | rfl | rfl
      · exact Set.not_subset.mp h0
      · exact Set.not_subset.mp h1
      · exact Set.not_subset.mp h2
    rcases hXAB c hcX with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m, i₀, c, b, fun e => hcS (e ▸ Or.inl (Or.inl hm)), hcX, hbX, hm, hj₀⟩
    · exact ⟨i₀, m, a, c, fun e => hcS (e ▸ Or.inl (Or.inr hm)), haX, hcX, hi₀, hm⟩
  · exact ⟨i₀, j₀, a, b, hne, haX, hbX, hi₀, hj₀⟩

end Workspace.ProofLemmas.HyperprismTwoAttachments
