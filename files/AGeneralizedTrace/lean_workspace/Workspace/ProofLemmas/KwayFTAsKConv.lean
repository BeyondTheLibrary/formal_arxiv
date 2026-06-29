import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.KwayFactorSummable

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# The parent `T4`'s Fourier transform is the k-fold circular convolution (Lemma 7, step i+ii)

This file wires the *abstract* `KFoldConvolutionTheorem.kFoldConvolutionTheorem`
to the **exact** `T4` of `SublemmaFourierKway`, sorry-free.

The parent proof works with
`T4 r = ∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r`  (the ℝ-valued k-way product),
and its discrete Fourier transform is
`∑' r : ℤ, (T4 r : ℂ) · e^{-iξr}`.

We choose the abstract factor sequence `f := KwayFactorSummable.fcx n k ℓ`
(`f j r = (factor n (ℓ j) r : ℂ)` for `j < k`, `0` otherwise) and prove:

* `partialProdCx_eq_T4` — `partialProd f k r = ((T4 r : ℝ) : ℂ)` for every `r`,
  i.e. the abstract partial product over the first `k` factors is the ℂ-cast of
  the parent's k-way product. (Uses `Fin.prod_univ_eq_prod_range`.)

* `FT_T4_eq_kConv` — for `k ≥ 1`, the parent's Fourier sum equals
  `KFoldConvolutionTheorem.kConv f k ξ`, the `k`-fold *circular* convolution of the
  per-factor Fourier transforms.  This discharges the summability side-conditions
  of `kFoldConvolutionTheorem` via `KwayFactorSummable.fcx_summable` and
  `KwayFactorSummable.partialProdCx_summable`.

This is the precise step-(i)+(ii) hook the parent bridge needs: it turns the
left-hand `‖∑' r, (T4 r) e^{-iξr}‖` into `‖kConv f k ξ‖`, on which the iterated
modulus-triangle (G3) and periodisation (G4) steps then operate.  Everything here
is sorry-free.
-/

namespace KwayFTAsKConv

open KFoldConvolutionTheorem
open KwayFactorSummable

/-- The abstract factor sequence used to instantiate `kFoldConvolutionTheorem`. -/
noncomputable def fseq (n k : ℕ) (ℓ : Fin k → ℕ) : ℕ → (ℤ → ℂ) :=
  fun j => fcx n k ℓ j

/-- For `r : ℤ`, the abstract partial product over the first `k` factors equals the
ℂ-cast of the parent's k-way product `∏ j : Fin k, factor n (ℓ j) r`. -/
theorem partialProdCx_eq_T4 (n k : ℕ) (ℓ : Fin k → ℕ) (r : ℤ) :
    partialProd (fseq n k ℓ) k r
      = (((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ)) : ℂ) := by
  unfold partialProd fseq
  -- ∏ j ∈ range k, fcx n k ℓ j r = ∏ i : Fin k, fcx n k ℓ i.val r
  rw [Finset.prod_range fun j => fcx n k ℓ j r]
  -- now both sides are products over Fin k; cast the ℝ product into ℂ
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  -- fcx n k ℓ i.val r = ((factor n (ℓ i) r : ℝ) : ℂ)  (since i.val < k)
  simp only [fcx, dif_pos i.isLt]

/-- **Fourier transform of the parent `T4` as a k-fold circular convolution.**
For `k ≥ 1`, the parent's discrete Fourier sum of the ℂ-cast k-way product equals
`kConv (fseq n k ℓ) k ξ`, the `k`-fold circular convolution of the per-factor
Fourier transforms.  All summability side-conditions are discharged from
`KwayFactorSummable`. -/
theorem FT_T4_eq_kConv (n k : ℕ) (ℓ : Fin k → ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    (∑' r : ℤ,
        (((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ)) : ℂ)
          * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = kConv (fseq n k ℓ) k ξ := by
  -- Each abstract factor is ℓ¹.
  have hf_sum : ∀ j : ℕ, Summable (fun r : ℤ => ‖fseq n k ℓ j r‖) := by
    intro j
    exact fcx_summable n k ℓ j
  -- Each non-empty partial product is ℓ¹.
  have hpp_sum : ∀ m : ℕ, 1 ≤ m → Summable (fun r : ℤ => ‖partialProd (fseq n k ℓ) m r‖) := by
    intro m hm
    -- partialProd (fseq …) m = partialProdCx n k ℓ m (defeq).
    have heq : (fun r : ℤ => ‖partialProd (fseq n k ℓ) m r‖)
        = (fun r : ℤ => ‖partialProdCx n k ℓ m r‖) := by
      funext r
      rfl
    rw [heq]
    exact partialProdCx_summable n k ℓ m hm
  -- Apply the k-fold convolution theorem.
  have hmain := kFoldConvolutionTheorem (fseq n k ℓ) hf_sum hpp_sum k hk ξ
  -- hmain : FT (partialProd (fseq n k ℓ) k) ξ = kConv (fseq n k ℓ) k ξ.
  -- Rewrite the LHS Fourier sum to FT (partialProd …) ξ via partialProdCx_eq_T4.
  rw [← hmain]
  unfold FT
  apply tsum_congr
  intro r
  rw [partialProdCx_eq_T4 n k ℓ r]

end KwayFTAsKConv
