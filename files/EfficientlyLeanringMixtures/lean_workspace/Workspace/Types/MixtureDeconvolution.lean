import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.SignedGaussianCombination

set_option maxHeartbeats 400000

namespace Workspace.Types.MixtureDeconvolution

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.SignedGaussianCombination

/-!
# Mixture Deconvolution — the `F_α` operator (Definition 2 of Moitra–Valiant)

This module formalises Definition 2 of Moitra–Valiant:

> Let `F(x) = Σᵢ wᵢ · N(μᵢ, σᵢ², x)`. For any `α < minᵢ σᵢ²`,
>   `F_α(F)(x) = Σᵢ wᵢ · N(μᵢ, σᵢ² − α, x)`.

i.e. `F_α` decrements every component's variance by `α`. The mean and weight
fields are untouched, so this is a purely variance-level operation.

The paper explicitly allows `α` to be negative — in that case `F_α` is
*convolution* by `N(0, |α|)` rather than deconvolution. Hence our hypothesis
is `α < minᵢ σᵢ²`, not `0 ≤ α < minᵢ σᵢ²`.

We expose two flavours:

* `deconvMixture2 F α h` — for two-component probability mixtures.
* `deconvSigned   S α h` — for arbitrary signed Gaussian combinations.

For each we also expose parameter-level accessor lemmas showing that the
weights / means are unchanged and that each variance is exactly `σᵢ² − α`.
-/

/-! ## Auxiliary: shifting a single Gaussian's variance by `-α`. -/

/-- Decrement the variance of a single `GaussianPDF` by `α`, keeping the
mean fixed. Requires `α < G.varSq` (strict) so the new variance is still
positive — `GaussianPDF` only admits strictly positive variances. -/
noncomputable def shiftGaussian
    (G : GaussianPDF) (α : ℝ) (h : α < G.varSq) : GaussianPDF where
  mean := G.mean
  varSq := G.varSq - α
  varSq_pos := sub_pos.mpr h

@[simp] theorem shiftGaussian_mean
    (G : GaussianPDF) (α : ℝ) (h : α < G.varSq) :
    (shiftGaussian G α h).mean = G.mean := rfl

@[simp] theorem shiftGaussian_varSq
    (G : GaussianPDF) (α : ℝ) (h : α < G.varSq) :
    (shiftGaussian G α h).varSq = G.varSq - α := rfl

/-! ## `F_α` on two-component probability mixtures. -/

/-- The deconvolution operator `F_α` applied to a two-component Gaussian
mixture: every component's variance is decremented by `α`. The weights and
means are unchanged. The hypothesis `α < min F.comp1.varSq F.comp2.varSq`
ensures both new variances are strictly positive. -/
noncomputable def deconvMixture2
    (F : GaussianMixture2) (α : ℝ)
    (h : α < min F.comp1.varSq F.comp2.varSq) : GaussianMixture2 where
  weight1 := F.weight1
  weight2 := F.weight2
  comp1 := shiftGaussian F.comp1 α (lt_of_lt_of_le h (min_le_left _ _))
  comp2 := shiftGaussian F.comp2 α (lt_of_lt_of_le h (min_le_right _ _))
  weight1_nonneg := F.weight1_nonneg
  weight2_nonneg := F.weight2_nonneg
  weights_sum_one := F.weights_sum_one

/-! ### Parameter-level accessor lemmas for `deconvMixture2`. -/

@[simp] theorem deconvMixture2_weight1
    (F : GaussianMixture2) (α : ℝ)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    (deconvMixture2 F α h).weight1 = F.weight1 := rfl

@[simp] theorem deconvMixture2_weight2
    (F : GaussianMixture2) (α : ℝ)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    (deconvMixture2 F α h).weight2 = F.weight2 := rfl

@[simp] theorem deconvMixture2_comp1_mean
    (F : GaussianMixture2) (α : ℝ)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    (deconvMixture2 F α h).comp1.mean = F.comp1.mean := rfl

@[simp] theorem deconvMixture2_comp1_varSq
    (F : GaussianMixture2) (α : ℝ)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    (deconvMixture2 F α h).comp1.varSq = F.comp1.varSq - α := rfl

@[simp] theorem deconvMixture2_comp2_mean
    (F : GaussianMixture2) (α : ℝ)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    (deconvMixture2 F α h).comp2.mean = F.comp2.mean := rfl

@[simp] theorem deconvMixture2_comp2_varSq
    (F : GaussianMixture2) (α : ℝ)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    (deconvMixture2 F α h).comp2.varSq = F.comp2.varSq - α := rfl

/-! ## `F_α` on signed Gaussian combinations. -/

/-- The deconvolution operator on a signed Gaussian combination: shift every
component's variance by `-α`. Requires, for each pair `p` in `S.components`,
that `α < p.snd.varSq`, so each new variance is strictly positive. The list
of coefficients (and their order) is preserved. -/
noncomputable def deconvSigned
    (S : SignedGaussianCombination) (α : ℝ)
    (h : ∀ p ∈ S.components, α < p.snd.varSq) : SignedGaussianCombination where
  components :=
    S.components.attach.map
      (fun p => (p.val.1, shiftGaussian p.val.2 α (h p.val p.property)))

/-! ### Length / structural sanity for `deconvSigned`. -/

@[simp] theorem deconvSigned_components_length
    (S : SignedGaussianCombination) (α : ℝ)
    (h : ∀ p ∈ S.components, α < p.snd.varSq) :
    (deconvSigned S α h).components.length = S.components.length := by
  simp [deconvSigned]

/-- Reading off the i-th coefficient of `deconvSigned S α h` recovers the
i-th coefficient of `S`. -/
theorem deconvSigned_coeff_get
    (S : SignedGaussianCombination) (α : ℝ)
    (h : ∀ p ∈ S.components, α < p.snd.varSq)
    (i : ℕ) (hi : i < S.components.length) :
    ((deconvSigned S α h).components.get
        ⟨i, by simpa [deconvSigned] using hi⟩).1
      = (S.components.get ⟨i, hi⟩).1 := by
  simp [deconvSigned]

/-- Reading off the i-th component's mean of `deconvSigned S α h` recovers
the i-th component's mean of `S`. -/
theorem deconvSigned_mean_get
    (S : SignedGaussianCombination) (α : ℝ)
    (h : ∀ p ∈ S.components, α < p.snd.varSq)
    (i : ℕ) (hi : i < S.components.length) :
    ((deconvSigned S α h).components.get
        ⟨i, by simpa [deconvSigned] using hi⟩).2.mean
      = (S.components.get ⟨i, hi⟩).2.mean := by
  simp [deconvSigned, shiftGaussian]

/-- Reading off the i-th component's variance of `deconvSigned S α h`
recovers the i-th component's variance of `S` minus `α`. -/
theorem deconvSigned_varSq_get
    (S : SignedGaussianCombination) (α : ℝ)
    (h : ∀ p ∈ S.components, α < p.snd.varSq)
    (i : ℕ) (hi : i < S.components.length) :
    ((deconvSigned S α h).components.get
        ⟨i, by simpa [deconvSigned] using hi⟩).2.varSq
      = (S.components.get ⟨i, hi⟩).2.varSq - α := by
  simp [deconvSigned, shiftGaussian]

end Workspace.Types.MixtureDeconvolution
