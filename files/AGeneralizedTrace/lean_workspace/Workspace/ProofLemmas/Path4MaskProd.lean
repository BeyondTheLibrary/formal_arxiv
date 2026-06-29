import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.QFactorBounds
import Workspace.ProofLemmas.Path4Envelope

/-!
# Path4MaskProd

Bound the sum over all middle-window masks `m : BinVec (n/2)` of the product of
`ellFactor`s over the `true`-bits of `m` by `exp(2α) = exp(O(√n))`.

The proof:

1. **Subset-sum identity.** Pushing the `BinVec (n/2) ≃ Finset (Fin (n/2))`
   bijection through, the mask-sum equals `∑_{S} ∏_{j ∈ S} x_j = ∏_j (1 + x_j)`
   (`Finset.prod_one_add`), where `x_j := ellFactor n α r j`.
2. **Per-factor bound.** `0 ≤ x_j` and `x_j ≤ 2α · binPMFInt n (1/2) (r + n/4 + j)`,
   because `x_j = αX/(1 - αX)` with `αX ≤ 1/2` (so `1 - αX ≥ 1/2`).
3. **`∏ (1 + x_j) ≤ exp(∑ x_j)`** by `1 + x ≤ exp x` per factor and `Real.exp_sum`.
4. **`∑ x_j ≤ 2α`** via the per-factor bound and `window_bin_subsum_le_one`.
5. Combine.
-/

namespace Workspace.ProofLemmas.Path4MaskProd

open Workspace.Types.AlternatingSumExpression
open Workspace.Types.BinVec
open scoped BigOperators

/-- `α · X ≤ 1/2` for `X = binPMFInt n (1/2) idx` and
`α = (1/(4·e²·√(2π)))·√n`.  Re-derived from the public `BinomialPmfMaxBound`
plus the constant slack (`4·e²·√(2π) ≥ 2`). -/
private lemma alphaX_le_half (n : ℕ) (hn1 : 1 ≤ n) (idx : ℤ) :
    (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n * binPMFInt n (1/2) idx ≤ 1/2 := by
  set α : ℝ := (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n with hα
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hsqrt2pi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hdenpos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  have hα_nn : 0 ≤ α := by rw [hα]; positivity
  -- bound X by C(n, idx.toNat)·2⁻ⁿ (it equals that in range, is 0 out of range)
  have hX_le : binPMFInt n (1/2) idx ≤ (Nat.choose n idx.toNat : ℝ) * (2 ^ n : ℝ)⁻¹ := by
    unfold binPMFInt
    split_ifs with hcase
    · unfold binPMF
      split_ifs with hcase2
      · have hpow : ((1 : ℝ) / 2) ^ idx.toNat * (1 - 1 / 2) ^ (n - idx.toNat)
            = (2 ^ n : ℝ)⁻¹ := by
          rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring]
          rw [show ((1 : ℝ) / 2) ^ idx.toNat * (1 / 2) ^ (n - idx.toNat)
                = (1 / 2) ^ (idx.toNat + (n - idx.toNat)) from by rw [← pow_add]]
          rw [Nat.add_sub_of_le hcase2]
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by ring, inv_pow]
        rw [show (Nat.choose n idx.toNat : ℝ) * (1 / 2) ^ idx.toNat * (1 - 1 / 2) ^ (n - idx.toNat)
              = (Nat.choose n idx.toNat : ℝ) * (((1:ℝ)/2)^idx.toNat * (1-1/2)^(n-idx.toNat)) from by ring,
            hpow]
      · positivity
    · positivity
  -- now α·X ≤ α·(C·2⁻ⁿ) ≤ 1/2
  have hstep : α * binPMFInt n (1/2) idx
      ≤ α * ((Nat.choose n idx.toNat : ℝ) * (2 ^ n : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hX_le hα_nn
  refine le_trans hstep ?_
  -- α·B ≤ 1/2: same analytic argument as alphaB_le_half
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'
  have hαeq : α = c' * Real.sqrt n := by rw [hα, hc']
  have hc'pos : (0 : ℝ) < c' := by rw [hc']; positivity
  have hB : ((Nat.choose n idx.toNat : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ Real.sqrt (2 / (Real.pi * n)) :=
    BinomialPmfMaxBound n hn1 idx.toNat
  have hcoef_nn : (0 : ℝ) ≤ c' * Real.sqrt n := by positivity
  rw [hαeq]
  have hstep2 : c' * Real.sqrt n * ((Nat.choose n idx.toNat : ℝ) * (2 ^ n : ℝ)⁻¹)
      ≤ c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) :=
    mul_le_mul_of_nonneg_left hB hcoef_nn
  refine le_trans hstep2 ?_
  have hmul : Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) = Real.sqrt (2 / Real.pi) := by
    rw [← Real.sqrt_mul (le_of_lt hnpos)]; congr 1; field_simp
  have hrew : c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) = c' * Real.sqrt (2 / Real.pi) := by
    rw [mul_assoc, hmul]
  rw [hrew, hc', one_div, inv_mul_le_iff₀ hdenpos]
  have h1 : Real.sqrt (2 / Real.pi) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_one hpi]; linarith [Real.pi_gt_d2]
  have h2 : (2 : ℝ) ≤ 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
    have he : (1 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt; nlinarith [Real.pi_gt_d2]
    nlinarith [hs, he, Real.exp_pos 2, hsqrt2pi]
  nlinarith [h1, h2]

/-- `ellFactor n α r j ≤ 2 · α · binPMFInt n (1/2) (r + n/4 + j)`. -/
private lemma ellFactor_le_two_alpha_bin (n : ℕ) (hn1 : 1 ≤ n) (r : ℤ) (j : ℕ) :
    ellFactor n ((1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n) r j
    ≤ 2 * ((1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n)
        * binPMFInt n (1/2) (r + (n / 4 : ℤ) + (j : ℤ)) := by
  unfold ellFactor
  simp only
  set α : ℝ := (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n with hα
  set idx : ℤ := r + (n / 4 : ℤ) + (j : ℤ) with hidx
  set X : ℝ := binPMFInt n (1/2) idx with hX
  have hX_nn : 0 ≤ X := by
    rw [hX]
    exact LightAtypicalZTailProof.binPMFInt_nonneg' n (1/2)
      (by norm_num) (by norm_num) idx
  have hα_nn : 0 ≤ α := by rw [hα]; positivity
  have hhalf : α * X ≤ 1/2 := by rw [hα, hX]; exact alphaX_le_half n hn1 idx
  have hden_pos : 0 < 1 - α * X := by linarith
  -- αX/(1-αX) ≤ 2αX  ⟺  αX ≤ 2αX·(1-αX)  (mult by (1-αX) > 0)
  rw [div_le_iff₀ hden_pos]
  -- goal: α * X ≤ 2 * α * X * (1 - α * X)
  nlinarith [mul_nonneg hα_nn hX_nn, hhalf, hden_pos]

/-- The map `m ↦ univ.filter (m.bit · = true)` is an equivalence
`BinVec (n/2) ≃ Finset (Fin (n/2))`. -/
private def maskEquiv (n : ℕ) : BinVec (n/2) ≃ Finset (Fin (n/2)) where
  toFun m := (Finset.univ : Finset (Fin (n/2))).filter (fun j => m.bit j = true)
  invFun S := ⟨fun j => decide (j ∈ S)⟩
  left_inv m := by
    cases m with
    | mk b =>
      simp only [BinVec.mk.injEq]
      funext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases hbj : b j <;> simp
  right_inv S := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]

/-- **Subset-sum identity.**
`∑_{m : BinVec (n/2)} ∏_{j : m.bit j = true} x_j = ∏_j (1 + x_j)`. -/
private lemma mask_sum_eq_prod_one_add (n : ℕ) (x : Fin (n/2) → ℝ) :
    (∑ m : BinVec (n/2),
        ∏ j ∈ (Finset.univ : Finset (Fin (n/2))).filter (fun j => m.bit j = true), x j)
      = ∏ j : Fin (n/2), (1 + x j) := by
  -- LHS: the filter set on `m` is exactly `maskEquiv n m`, so the mask-sum is
  -- `∑ m, g (maskEquiv n m)` with `g S := ∏ i ∈ S, x i`; reindex via `Equiv.sum_comp`.
  have hLHS : (∑ m : BinVec (n/2),
        ∏ j ∈ (Finset.univ : Finset (Fin (n/2))).filter (fun j => m.bit j = true), x j)
      = ∑ S : Finset (Fin (n/2)), ∏ j ∈ S, x j := by
    rw [← Equiv.sum_comp (maskEquiv n) (fun S => ∏ j ∈ S, x j)]
    rfl
  rw [hLHS]
  -- RHS: `∏ (1 + x j) = ∑ t ∈ univ.powerset, ∏ i ∈ t, x i = ∑ t : Finset, ∏ i ∈ t, x i`.
  rw [show (∏ j : Fin (n/2), (1 + x j)) = ∏ j ∈ (Finset.univ : Finset (Fin (n/2))), (1 + x j) from rfl,
      Finset.prod_one_add (Finset.univ : Finset (Fin (n/2))) (f := x), Finset.powerset_univ]

/-- **Main lemma.**  The sum over all middle-window masks of the product of
`ellFactor`s over the `true`-bits is bounded by `exp(2α)`. -/
theorem mask_ellfactor_product_sum (n : ℕ) (hn : 1 ≤ n) (r : ℤ) :
    let α := (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n
    ∑ m : Workspace.Types.BinVec.BinVec (n / 2),
        (∏ j ∈ (Finset.univ : Finset (Fin (n/2))).filter (fun j => m.bit j = true),
            Workspace.Types.AlternatingSumExpression.ellFactor n α r (j:ℕ))
      ≤ Real.exp (2 * ((1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n)) := by
  intro α
  set x : Fin (n/2) → ℝ := fun j => ellFactor n α r (j:ℕ) with hx
  -- Step 1: subset-sum identity.
  have hsum_eq : (∑ m : BinVec (n/2),
        ∏ j ∈ (Finset.univ : Finset (Fin (n/2))).filter (fun j => m.bit j = true), x j)
      = ∏ j : Fin (n/2), (1 + x j) := mask_sum_eq_prod_one_add n x
  rw [hsum_eq]
  -- per-factor facts.
  have hx_nn : ∀ j : Fin (n/2), 0 ≤ x j := by
    intro j; rw [hx]; exact (Workspace.ProofLemmas.Path4Envelope.ellFactor_le_one n hn r (j:ℕ)).1
  -- Step 3: ∏ (1 + x_j) ≤ ∏ exp(x_j) = exp(∑ x_j).
  have hstep3 : (∏ j : Fin (n/2), (1 + x j)) ≤ ∏ j : Fin (n/2), Real.exp (x j) := by
    apply Finset.prod_le_prod
    · intro j _; linarith [hx_nn j]
    · intro j _; rw [add_comm]; exact Real.add_one_le_exp (x j)
  have hexp_prod : (∏ j : Fin (n/2), Real.exp (x j)) = Real.exp (∑ j : Fin (n/2), x j) := by
    rw [← Real.exp_sum]
  -- Step 4: ∑ x_j ≤ 2α.
  have hsum_x_le : (∑ j : Fin (n/2), x j) ≤ 2 * α := by
    -- x_j ≤ 2α·binPMFInt n (1/2) (r + n/4 + j)
    have hxbound : ∀ j : Fin (n/2),
        x j ≤ 2 * α * binPMFInt n (1/2) (r + (n / 4 : ℤ) + (j : ℤ)) := by
      intro j; rw [hx]; exact ellFactor_le_two_alpha_bin n hn r (j:ℕ)
    calc (∑ j : Fin (n/2), x j)
        ≤ ∑ j : Fin (n/2), 2 * α * binPMFInt n (1/2) (r + (n / 4 : ℤ) + (j : ℤ)) :=
          Finset.sum_le_sum (fun j _ => hxbound j)
      _ = 2 * α * ∑ j : Fin (n/2), binPMFInt n (1/2) (r + (n / 4 : ℤ) + (j : ℤ)) := by
          rw [Finset.mul_sum]
      _ = 2 * α * ∑ j ∈ (Finset.univ : Finset (Fin (n/2))),
            binPMFInt n (1/2) ((n/4:ℤ) + r + (j:ℕ)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          ring
      _ ≤ 2 * α * 1 := by
          have hα_nn : 0 ≤ α := by rw [show α = (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n from rfl]; positivity
          have hwin := Workspace.ProofLemmas.Path4Envelope.window_bin_subsum_le_one n hn r
          nlinarith [hwin, hα_nn]
      _ = 2 * α := by ring
  -- Step 5: combine.
  calc (∏ j : Fin (n/2), (1 + x j))
      ≤ ∏ j : Fin (n/2), Real.exp (x j) := hstep3
    _ = Real.exp (∑ j : Fin (n/2), x j) := hexp_prod
    _ ≤ Real.exp (2 * α) := Real.exp_le_exp.mpr hsum_x_le

end Workspace.ProofLemmas.Path4MaskProd
