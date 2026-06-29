import Mathlib
import Workspace.Types.ZeroCount

/-!
# `SublemmaAddGaussianTailRegionNoZeros` — region-partition encard glue

Moitra–Valiant §6.1 ("Now add the k-th Gaussian").  The perturbed function
`h(x) = g x + a_k · N(μ_k, v, x)` has its zeros counted by partitioning the
real line into three regions:

* **Region (a)** — the two tails `x < b`, `x > b'`: the Gaussian envelope
  dominates the perturbation, so `h` has NO zeros there; every zero lies in
  `Icc b b'`.  (Proved in `HurwitzGaussianPerturbationTailDominance` as
  `zeroSet h ⊆ Icc b b'`.)
* **Region (b)** — `Icc b b' \ Ioo (μ_k − δ) (μ_k + δ)`: near the simple zeros
  of `g`, sign-preservation keeps the zero count at most `N`.
* **Region (c)** — the central window `Ioo (μ_k − δ) (μ_k + δ)`: the unimodal
  Gaussian perturbation contributes at most two zeros.

This file provides the **pure `Set.encard` arithmetic glue** that combines those
three regional bounds into the final `N + 2` count: it is Mathlib-only and makes
no analytic claims of its own.  Concretely, if a set `Z` is contained in
`Icc b b'`, and `Z`'s part outside the central window has `encard ≤ N`, and
`Z`'s part inside the central window has `encard ≤ 2`, then `Z.encard ≤ N + 2`.

The two analytic inputs (regions (b) and (c)) are the genuinely hard remaining
content; this lemma is the deterministic bookkeeping that turns them, together
with the already-proved tail-dominance region (a), into the Proposition 7 bound.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.ZeroCount
open Set

/-- **Region-partition encard glue.**  If every zero of a perturbed function lies
in `Icc b b'` (region (a): tails contribute nothing), and the zeros outside the
central window `Ioo (μ_k − δ) (μ_k + δ)` number at most `N` (region (b)), and the
zeros inside the central window number at most `2` (region (c)), then the total
number of zeros is at most `N + 2`. -/
theorem SublemmaAddGaussianTailRegionNoZeros
    (h : ℝ → ℝ) (b b' μ_k δ : ℝ) (N : ℕ)
    (h_tail : zeroSet h ⊆ Set.Icc b b')
    (h_outer : (zeroSet h ∩ (Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ))).encard
        ≤ (N : ℕ∞))
    (h_inner : (zeroSet h ∩ Set.Ioo (μ_k - δ) (μ_k + δ)).encard ≤ (2 : ℕ∞)) :
    Workspace.Types.ZeroCount.hasAtMostNZeros h (N + 2) := by
  rw [hasAtMostNZeros_def, zeroCount_def]
  -- Abbreviations for the central window and its set.
  set W : Set ℝ := Set.Ioo (μ_k - δ) (μ_k + δ) with hW_def
  -- Decompose `zeroSet h` along membership in the window `W`.
  -- Since `zeroSet h ⊆ Icc b b'`, the part outside `W` equals
  -- `zeroSet h ∩ (Icc b b' \ W)`.
  have hsplit :
      zeroSet h = (zeroSet h ∩ (Set.Icc b b' \ W)) ∪ (zeroSet h ∩ W) := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      have hxIcc : x ∈ Set.Icc b b' := h_tail hx
      by_cases hxW : x ∈ W
      · exact Or.inr ⟨hx, hxW⟩
      · exact Or.inl ⟨hx, hxIcc, hxW⟩
    · rintro x (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  -- Bound the encard of the union by the sum of the two regional encards.
  rw [hsplit]
  calc ((zeroSet h ∩ (Set.Icc b b' \ W)) ∪ (zeroSet h ∩ W)).encard
      ≤ (zeroSet h ∩ (Set.Icc b b' \ W)).encard + (zeroSet h ∩ W).encard :=
        Set.encard_union_le _ _
    _ ≤ (N : ℕ∞) + (2 : ℕ∞) :=
        add_le_add h_outer h_inner
    _ = ((N + 2 : ℕ) : ℕ∞) := by push_cast; ring

end Workspace.ProofLemmas
