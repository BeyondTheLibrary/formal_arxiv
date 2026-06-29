import Mathlib
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.Types.DelProb
import Workspace.ProofLemmas.QFactorBounds
import Workspace.ProofLemmas.OffsetWeightSumOne
import Workspace.ProofLemmas.LightAtypicalZTail

/-!
# Path4Envelope

Two small "envelope" lemmas used in Path 4 of the Lemma-6 analysis:

* `window_bin_subsum_le_one` — a `Fin (n/2)`-window sub-sum of the `Bin(n, 1/2)`
  PMF (over integer indices) is `≤ 1`, because the indices are distinct and the
  full integer sum of `binPMFInt n (1/2) ·` is `1`.

* `ellFactor_le_one` — the rational factor `α·X/(1 - α·X)` lies in `[0, 1]`,
  since `α·X ≤ 1/2`.

* `stuff_l1_poly_bound` — the offset-weighted sum of products of `ellFactor`s
  over `r ∈ Icc(-(n/4))(n/4)` is `≤ 1`, because each product is in `[0,1]` and
  `∑_r (offsetWeight n r).toReal ≤ 1`.
-/

namespace Workspace.ProofLemmas.Path4Envelope

open Workspace.Types.AlternatingSumExpression
open Workspace.Types.PartialDeletionProcess
open scoped BigOperators

/-! ## Lemma 1: window sub-sum of the binomial PMF is `≤ 1`. -/

/-- The full integer sum of `binPMFInt n p ·` equals `1` for `p ∈ [0,1]`.
It is supported on `{0, …, n}` and there sums to `(p + (1-p))^n = 1`. -/
theorem binPMFInt_tsum_eq_one (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑' z : ℤ, binPMFInt n p z = 1 := by
  -- Reindex to the finite support: the image of `range (n+1)` under `(· : ℤ)`.
  rw [tsum_eq_sum (s := (Finset.range (n + 1)).map Nat.castEmbedding)]
  · rw [Finset.sum_map]
    -- On `range (n+1)`, `binPMFInt n p (k:ℤ) = binPMF n p k`.
    have hcongr : ∀ k ∈ Finset.range (n + 1),
        binPMFInt n p ((Nat.castEmbedding : ℕ ↪ ℤ) k)
          = (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      simp only [Nat.castEmbedding_apply]
      unfold binPMFInt binPMF
      have h0 : (0 : ℤ) ≤ (k : ℤ) := Int.ofNat_nonneg k
      have h1 : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast (by omega : k ≤ n)
      rw [if_pos ⟨h0, h1⟩, Int.toNat_natCast, if_pos (by omega)]
    rw [Finset.sum_congr rfl hcongr]
    have hbinom : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
        = (p + (1 - p)) ^ n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k _; ring
    rw [hbinom, show p + (1 - p) = 1 by ring, one_pow]
  · -- Terms outside the image vanish.
    intro z hz
    unfold binPMFInt
    rw [if_neg ?_]
    intro hmem
    apply hz
    rw [Finset.mem_map]
    refine ⟨z.toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have := hmem.2; have := hmem.1; omega
    · simp only [Nat.castEmbedding_apply]
      exact Int.toNat_of_nonneg hmem.1

/-- Helper: the integer map `j ↦ a + (j : ℤ)` on `Fin N` is injective. -/
private lemma window_inj (a : ℤ) (N : ℕ) :
    Function.Injective (fun j : Fin N => a + (j : ℤ)) := by
  intro i j hij
  simp only at hij
  have : (i : ℤ) = (j : ℤ) := by omega
  have : (i : ℕ) = (j : ℕ) := by exact_mod_cast this
  exact Fin.ext this

theorem window_bin_subsum_le_one (n : ℕ) (hn : 1 ≤ n) (r : ℤ) :
    ∑ j ∈ (Finset.univ : Finset (Fin (n / 2))),
        Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2) ((n/4:ℤ) + r + (j:ℕ))
      ≤ 1 := by
  set a : ℤ := (n/4:ℤ) + r with ha
  -- nonnegativity of binPMFInt n (1/2)
  have hnn : ∀ z : ℤ, 0 ≤ binPMFInt n (1/2) z := fun z =>
    LightAtypicalZTailProof.binPMFInt_nonneg' n (1/2) (by norm_num) (by norm_num) z
  -- rewrite the index `a + (j:ℕ)` as `a + (j:ℤ)`
  have hreindex : ∑ j ∈ (Finset.univ : Finset (Fin (n / 2))),
        binPMFInt n (1/2) (a + (j:ℕ))
      = ∑ z ∈ (Finset.univ : Finset (Fin (n / 2))).image (fun j : Fin (n/2) => a + (j:ℤ)),
          binPMFInt n (1/2) z := by
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact window_inj a (n/2) hxy
  rw [hreindex]
  -- `binPMFInt n (1/2)` has finite support (inside `Icc 0 n`), hence summable.
  have hsupp : (Function.support (fun z : ℤ => binPMFInt n (1/2) z)).Finite := by
    apply Set.Finite.subset (Finset.Icc (0:ℤ) (n:ℤ)).finite_toSet
    intro z hz
    simp only [Function.mem_support] at hz
    rw [Finset.mem_coe, Finset.mem_Icc]
    by_contra hc
    push_neg at hc
    apply hz
    unfold binPMFInt
    rw [if_neg (by push_neg; intro h0; omega)]
  have hsummable : Summable (fun z : ℤ => binPMFInt n (1/2) z) :=
    summable_of_finite_support hsupp
  -- the finite image-sum is bounded by the full integer tsum, which equals 1.
  have hsum_le_tsum :
      ∑ z ∈ (Finset.univ : Finset (Fin (n / 2))).image (fun j : Fin (n/2) => a + (j:ℤ)),
          binPMFInt n (1/2) z
      ≤ ∑' z : ℤ, binPMFInt n (1/2) z :=
    hsummable.sum_le_tsum _ (fun z _ => hnn z)
  calc _ ≤ ∑' z : ℤ, binPMFInt n (1/2) z := hsum_le_tsum
    _ = 1 := binPMFInt_tsum_eq_one n (1/2) (by norm_num) (by norm_num)

/-! ## Lemma 2: `ellFactor ∈ [0,1]` and the offset-weighted poly bound. -/

/-- The witness scaling constant. -/
private noncomputable def αval (n : ℕ) : ℝ :=
  (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n

/-- `α · (C(n,k)·2⁻ⁿ) ≤ 1/2` — a strengthening of `QFactorBounds.alphaB_le_one`,
exploiting the huge constant slack (`4·e²·√(2π) ≥ 2`). -/
private lemma alphaB_le_half (n : ℕ) (hn1 : 1 ≤ n) (k : ℕ) :
    αval n * ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1/2 := by
  unfold αval
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hsqrt2pi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hdenpos : (0 : ℝ) < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
  have hc'pos : (0 : ℝ) < c' := by rw [hc']; positivity
  have hB : ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ Real.sqrt (2 / (Real.pi * n)) :=
    BinomialPmfMaxBound n hn1 k
  have hcoef_nn : (0 : ℝ) ≤ c' * Real.sqrt n := by positivity
  have hstep : c' * Real.sqrt n * ((Nat.choose n k : ℝ) * (2 ^ n : ℝ)⁻¹)
      ≤ c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) :=
    mul_le_mul_of_nonneg_left hB hcoef_nn
  refine le_trans hstep ?_
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
  -- goal: √(2/π) ≤ (4·e²·√(2π)) · (1/2)
  nlinarith [h1, h2]

/-- `0 ≤ α·X ≤ 1/2` for `X = binPMFInt n (1/2) idx` and `α = αval n`. -/
private lemma alphaX_mem (n : ℕ) (hn : 1 ≤ n) (idx : ℤ) :
    0 ≤ αval n * binPMFInt n (1/2) idx ∧ αval n * binPMFInt n (1/2) idx ≤ 1/2 := by
  have hX_nn : 0 ≤ binPMFInt n (1/2) idx :=
    LightAtypicalZTailProof.binPMFInt_nonneg' n (1/2) (by norm_num) (by norm_num) idx
  have hα_nn : 0 ≤ αval n := by unfold αval; positivity
  refine ⟨mul_nonneg hα_nn hX_nn, ?_⟩
  -- bound X by C(n,idx.toNat)·2⁻ⁿ (equal in range, X=0 out of range).
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
  calc αval n * binPMFInt n (1/2) idx
      ≤ αval n * ((Nat.choose n idx.toNat : ℝ) * (2 ^ n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hX_le hα_nn
    _ ≤ 1/2 := alphaB_le_half n hn idx.toNat

theorem ellFactor_le_one (n : ℕ) (hn : 1 ≤ n) (r : ℤ) (j : ℕ) :
    0 ≤ Workspace.Types.AlternatingSumExpression.ellFactor n
          ((1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n) r j
    ∧ Workspace.Types.AlternatingSumExpression.ellFactor n
          ((1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n) r j ≤ 1 := by
  -- unfold ellFactor to the `αX/(1-αX)` form.
  unfold Workspace.Types.AlternatingSumExpression.ellFactor
  simp only
  set idx : ℤ := r + (n / 4 : ℤ) + (j : ℤ) with hidx
  have hmem := alphaX_mem n hn idx
  -- α here equals αval n
  have hαeq : (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n = αval n := by unfold αval; rfl
  rw [hαeq]
  set X : ℝ := binPMFInt n (1/2) idx with hX
  set α : ℝ := αval n with hαv
  obtain ⟨h_nn, h_half⟩ := hmem
  have hden_pos : 0 < 1 - α * X := by linarith
  constructor
  · exact div_nonneg h_nn (le_of_lt hden_pos)
  · rw [div_le_one hden_pos]; linarith

/-- `offsetWeight n r` is always finite (never `⊤`). -/
private lemma offsetWeight_ne_top (n : ℕ) (r : ℤ) : offsetWeight n r ≠ ⊤ := by
  unfold offsetWeight
  simp only
  split_ifs
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · exact ENNReal.zero_ne_top

/-- `∑_{r ∈ Icc(-(n/4))(n/4)} (offsetWeight n r).toReal ≤ 1`. -/
private lemma offsetWeight_finsum_toReal_le_one (n : ℕ) :
    ∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)), (offsetWeight n r).toReal ≤ 1 := by
  -- Move toReal outside the finite sum.
  have hsum_toReal : ∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)), (offsetWeight n r).toReal
      = (∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)), offsetWeight n r).toReal := by
    rw [ENNReal.toReal_sum]
    intro r _; exact offsetWeight_ne_top n r
  rw [hsum_toReal]
  -- The finite ENNReal sum is ≤ the tsum = 1.
  have hle : (∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)), offsetWeight n r)
      ≤ ∑' r : ℤ, offsetWeight n r := ENNReal.sum_le_tsum _
  rw [OffsetWeightSumOne.offsetWeight_tsum_eq_one n] at hle
  calc (∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)), offsetWeight n r).toReal
      ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) hle
    _ = 1 := by simp

theorem stuff_l1_poly_bound (n : ℕ) (hn : (10^12:ℕ) ≤ n)
    (δ : Workspace.Types.DelProb.DelProb)
    (zMinus zPlus : ℕ) (ℓ : Finset (Fin (n/2))) :
    let α := (1/(4*Real.exp 2*Real.sqrt (2*Real.pi)))*Real.sqrt n
    ∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)),
        (Workspace.Types.PartialDeletionProcess.offsetWeight n r).toReal *
          (∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j:ℕ))
      ≤ 1 := by
  intro α
  have hn1 : 1 ≤ n := by omega
  -- each summand ≤ (offsetWeight n r).toReal, since the product ∈ [0,1].
  have hsummand_le : ∀ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)),
      (Workspace.Types.PartialDeletionProcess.offsetWeight n r).toReal *
        (∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j:ℕ))
      ≤ (Workspace.Types.PartialDeletionProcess.offsetWeight n r).toReal := by
    intro r _
    have hprod_nn : 0 ≤ ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j:ℕ) := by
      apply Finset.prod_nonneg
      intro j _; exact (ellFactor_le_one n hn1 r (j:ℕ)).1
    have hprod_le_one : ∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j:ℕ) ≤ 1 := by
      apply Finset.prod_le_one
      · intro j _; exact (ellFactor_le_one n hn1 r (j:ℕ)).1
      · intro j _; exact (ellFactor_le_one n hn1 r (j:ℕ)).2
    calc (offsetWeight n r).toReal * (∏ j ∈ ℓ, _)
        ≤ (offsetWeight n r).toReal * 1 :=
          mul_le_mul_of_nonneg_left hprod_le_one ENNReal.toReal_nonneg
      _ = (offsetWeight n r).toReal := by ring
  calc ∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)),
          (offsetWeight n r).toReal * (∏ j ∈ ℓ, Workspace.Types.AlternatingSumExpression.ellFactor n α r (j:ℕ))
      ≤ ∑ r ∈ Finset.Icc (-(n/4:ℤ)) ((n/4:ℤ)), (offsetWeight n r).toReal :=
        Finset.sum_le_sum hsummand_le
    _ ≤ 1 := offsetWeight_finsum_toReal_le_one n

end Workspace.ProofLemmas.Path4Envelope
