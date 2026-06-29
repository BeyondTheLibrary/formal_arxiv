import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.MixtureRawMoments
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian

open scoped BigOperators
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1200000

/-- Bridge: the raw moment defined via density integral equals the integral under the
`gaussianReal` measure. -/
private lemma rawMoment_eq_integral_gaussianReal
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (i : ℕ) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G i
      = ∫ x, x ^ i ∂(gaussianReal G.mean ⟨G.varSq, le_of_lt G.varSq_pos⟩) := by
  classical
  set v : NNReal := ⟨G.varSq, le_of_lt G.varSq_pos⟩ with hv_def
  have hv_pos : (0 : ℝ) < (v : ℝ) := G.varSq_pos
  have hv_ne : v ≠ 0 := by
    intro h
    have : (v : ℝ) = 0 := by rw [h]; rfl
    linarith
  have hgr_eq : gaussianReal G.mean v
      = MeasureTheory.volume.withDensity (gaussianPDF G.mean v) :=
    gaussianReal_of_var_ne_zero G.mean hv_ne
  rw [hgr_eq]
  have h_meas : Measurable (gaussianPDF G.mean v) := measurable_gaussianPDF G.mean v
  have h_lt_top : ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ),
      gaussianPDF G.mean v x < ⊤ := by
    filter_upwards with x using gaussianPDF_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul h_meas h_lt_top]
  -- Now goal: rawMoment_ofGaussian G i = ∫ x, (gaussianPDF G.mean v x).toReal • x^i ∂volume
  rw [Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian_def]
  apply integral_congr_ae
  filter_upwards with x
  rw [smul_eq_mul, toReal_gaussianPDF]
  -- Goal: x^i * G.density x = gaussianPDFReal G.mean v x * x^i
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal]
  ring

/-- Integrability of `x ↦ x^i` w.r.t. `gaussianReal`. -/
private lemma integrable_pow_gaussianReal
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (i : ℕ) :
    Integrable (fun x : ℝ => x ^ i)
      (gaussianReal G.mean ⟨G.varSq, le_of_lt G.varSq_pos⟩) := by
  classical
  set v : NNReal := ⟨G.varSq, le_of_lt G.varSq_pos⟩ with hv_def
  have hv_pos : (0 : ℝ) < (v : ℝ) := G.varSq_pos
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    simp only [pow_zero]
    exact integrable_const 1
  · -- Use MemLp.integrable_norm_pow
    have h_memLp : MemLp (id : ℝ → ℝ) ((i : ℕ) : ENNReal) (gaussianReal G.mean v) := by
      apply memLp_id_gaussianReal' ((i : ℕ) : ENNReal)
      exact ENNReal.natCast_ne_top i
    have h_norm_pow : Integrable (fun x : ℝ => ‖(id : ℝ → ℝ) x‖ ^ i)
        (gaussianReal G.mean v) := h_memLp.integrable_norm_pow hi.ne'
    have h_abs : Integrable (fun x : ℝ => |x| ^ i) (gaussianReal G.mean v) := by
      have : (fun x : ℝ => |x| ^ i) = (fun x : ℝ => ‖(id : ℝ → ℝ) x‖ ^ i) := by
        funext x
        simp [Real.norm_eq_abs]
      rw [this]
      exact h_norm_pow
    refine (integrable_norm_iff ?_).mp ?_
    · exact (Continuous.aestronglyMeasurable (by continuity))
    · convert h_abs using 1
      funext x
      rw [Real.norm_eq_abs, abs_pow]

/--
For two independent Gaussians `X ∼ N(μ_X, σ_X²)` and `Z ∼ N(μ_Z, σ_Z²)`, the `i`-th
raw moment of the sum `X + Z` (whose distribution is `N(μ_X + μ_Z, σ_X² + σ_Z²)`)
equals the binomial convolution of the marginal raw moments:

  `M_i(X + Z) = Σ_{j=0}^{i} C(i, j) · M_{i-j}(X) · M_j(Z)`.
-/
theorem SublemmaMomentOfSumOfIndependents
    (G_X G_Z : Workspace.Types.GaussianPDF.GaussianPDF) (i : ℕ) :
    let G_sum : Workspace.Types.GaussianPDF.GaussianPDF :=
      ⟨G_X.mean + G_Z.mean, G_X.varSq + G_Z.varSq,
       add_pos G_X.varSq_pos G_Z.varSq_pos⟩
    Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_sum i
      = (Finset.range (i + 1)).sum (fun j =>
          (Nat.choose i j : ℝ)
            * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_X (i - j)
            * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_Z j) := by
  classical
  -- Introduce G_sum
  intro G_sum
  -- Variances as NNReal
  set vX : NNReal := ⟨G_X.varSq, le_of_lt G_X.varSq_pos⟩ with hvX_def
  set vZ : NNReal := ⟨G_Z.varSq, le_of_lt G_Z.varSq_pos⟩ with hvZ_def
  set vSum : NNReal := ⟨G_X.varSq + G_Z.varSq, le_of_lt (add_pos G_X.varSq_pos G_Z.varSq_pos)⟩
    with hvSum_def
  -- Compute vX + vZ = vSum as NNReal
  have hv_add : vX + vZ = vSum := by
    apply NNReal.eq
    show (vX : ℝ) + (vZ : ℝ) = (vSum : ℝ)
    rfl
  -- Use bridge lemma
  rw [rawMoment_eq_integral_gaussianReal G_sum i]
  -- Goal: ∫ x, x^i ∂(gaussianReal (G_X.mean + G_Z.mean) vSum) = Σ ...
  -- Use gaussianReal_conv_gaussianReal
  have h_conv :
      (gaussianReal G_X.mean vX).conv (gaussianReal G_Z.mean vZ)
        = gaussianReal (G_X.mean + G_Z.mean) vSum := by
    rw [gaussianReal_conv_gaussianReal, hv_add]
  rw [show (gaussianReal G_sum.mean ⟨G_sum.varSq, le_of_lt G_sum.varSq_pos⟩
        : Measure ℝ) = gaussianReal (G_X.mean + G_Z.mean) vSum from rfl]
  rw [← h_conv]
  -- Goal: ∫ x, x^i ∂((gaussianReal G_X.mean vX).conv (gaussianReal G_Z.mean vZ)) = Σ ...
  -- Apply integral_conv
  have h_integrable_sum : Integrable (fun x : ℝ => x ^ i)
      ((gaussianReal G_X.mean vX).conv (gaussianReal G_Z.mean vZ)) := by
    rw [h_conv]
    exact integrable_pow_gaussianReal G_sum i
  rw [integral_conv h_integrable_sum]
  -- Goal: ∫ x, ∫ y, (x + y)^i ∂(gaussianReal G_Z.mean vZ) ∂(gaussianReal G_X.mean vX) = Σ ...
  -- Expand (x+y)^i via add_pow
  have h_expand : ∀ x y : ℝ,
      (x + y) ^ i = ∑ m ∈ Finset.range (i + 1),
        x ^ m * y ^ (i - m) * (Nat.choose i m : ℝ) := by
    intro x y
    exact add_pow x y i
  -- Apply h_expand pointwise inside the integrals
  have h_inner : ∀ x : ℝ,
      ∫ y, (x + y) ^ i ∂(gaussianReal G_Z.mean vZ)
        = ∑ m ∈ Finset.range (i + 1),
            x ^ m * (Nat.choose i m : ℝ)
              * ∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ) := by
    intro x
    -- Rewrite (x+y)^i via h_expand
    have h_cong : (fun y => (x + y) ^ i)
        = (fun y => ∑ m ∈ Finset.range (i + 1),
            x ^ m * y ^ (i - m) * (Nat.choose i m : ℝ)) := by
      funext y
      exact h_expand x y
    rw [h_cong]
    -- Integral of a finite sum = sum of integrals
    rw [integral_finset_sum]
    · -- Now pull constants out
      apply Finset.sum_congr rfl
      intro m hm
      -- ∫ y, x^m * y^(i-m) * C(i,m) ∂μ = x^m * C(i,m) * ∫ y, y^(i-m) ∂μ
      rw [show (fun y : ℝ => x ^ m * y ^ (i - m) * (Nat.choose i m : ℝ))
            = (fun y : ℝ => (x ^ m * (Nat.choose i m : ℝ)) * y ^ (i - m)) by
            funext y; ring]
      rw [integral_const_mul]
    · -- Integrability of each summand
      intro m hm
      have h_int : Integrable (fun y : ℝ => y ^ (i - m))
          (gaussianReal G_Z.mean vZ) := integrable_pow_gaussianReal G_Z (i - m)
      have : (fun y : ℝ => x ^ m * y ^ (i - m) * (Nat.choose i m : ℝ))
          = (fun y : ℝ => (x ^ m * (Nat.choose i m : ℝ)) * y ^ (i - m)) := by
        funext y; ring
      rw [this]
      exact h_int.const_mul _
  -- Now apply h_inner inside the outer integral
  have h_outer_eq :
      ∫ x, ∫ y, (x + y) ^ i ∂(gaussianReal G_Z.mean vZ) ∂(gaussianReal G_X.mean vX)
        = ∫ x, ∑ m ∈ Finset.range (i + 1),
            x ^ m * (Nat.choose i m : ℝ)
              * ∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ)
            ∂(gaussianReal G_X.mean vX) := by
    apply integral_congr_ae
    filter_upwards with x using h_inner x
  rw [h_outer_eq]
  -- Now distribute the outer integral over the sum
  rw [integral_finset_sum]
  swap
  · -- Integrability of each summand
    intro m hm
    have h_int_x : Integrable (fun x : ℝ => x ^ m) (gaussianReal G_X.mean vX) :=
      integrable_pow_gaussianReal G_X m
    have : (fun x : ℝ => x ^ m * (Nat.choose i m : ℝ)
              * ∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ))
        = (fun x : ℝ => ((Nat.choose i m : ℝ)
              * ∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ)) * x ^ m) := by
      funext x; ring
    rw [this]
    exact h_int_x.const_mul _
  -- Goal: Σ m, ∫ x, x^m * C(i,m) * M_{i-m}(Z) ∂(gaussianReal X) = Σ j, C(i,j) * M_{i-j}(X) * M_j(Z)
  -- Pull constants out of each integral
  have h_lhs : (∑ m ∈ Finset.range (i + 1),
      ∫ x, x ^ m * (Nat.choose i m : ℝ)
        * ∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ) ∂(gaussianReal G_X.mean vX))
      = ∑ m ∈ Finset.range (i + 1),
          (Nat.choose i m : ℝ)
            * (∫ x, x ^ m ∂(gaussianReal G_X.mean vX))
            * (∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ)) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [show (fun x : ℝ => x ^ m * (Nat.choose i m : ℝ)
              * ∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ))
            = (fun x : ℝ => ((Nat.choose i m : ℝ)
                * ∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ)) * x ^ m) by
        funext x; ring]
    rw [integral_const_mul]
    ring
  rw [h_lhs]
  -- Now bridge back using rawMoment_eq_integral_gaussianReal
  have h_rhs_X : ∀ m : ℕ,
      (∫ x, x ^ m ∂(gaussianReal G_X.mean vX))
        = Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_X m := by
    intro m
    rw [rawMoment_eq_integral_gaussianReal G_X m]
  have h_rhs_Z : ∀ m : ℕ,
      (∫ y, y ^ m ∂(gaussianReal G_Z.mean vZ))
        = Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_Z m := by
    intro m
    rw [rawMoment_eq_integral_gaussianReal G_Z m]
  -- Rewrite each integral
  have h_step : (∑ m ∈ Finset.range (i + 1),
        (Nat.choose i m : ℝ)
          * (∫ x, x ^ m ∂(gaussianReal G_X.mean vX))
          * (∫ y, y ^ (i - m) ∂(gaussianReal G_Z.mean vZ)))
      = (∑ m ∈ Finset.range (i + 1),
          (Nat.choose i m : ℝ)
            * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_X m
            * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_Z (i - m)) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [h_rhs_X m, h_rhs_Z (i - m)]
  rw [h_step]
  -- Now we need: Σ m, C(i,m) * M_m(X) * M_{i-m}(Z) = Σ j, C(i,j) * M_{i-j}(X) * M_j(Z)
  -- Reverse the index: j = i - m, m = i - j
  rw [← Finset.sum_range_reflect (fun m =>
        (Nat.choose i m : ℝ)
          * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_X m
          * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G_Z (i - m))
        (i + 1)]
  -- After reflection: index k ↦ i + 1 - 1 - k = i - k
  apply Finset.sum_congr rfl
  intro j hj
  have hj_le : j ≤ i := by
    rw [Finset.mem_range] at hj
    omega
  have h2 : i + 1 - 1 - j = i - j := by omega
  rw [h2]
  have h3 : i - (i - j) = j := by omega
  rw [h3]
  rw [Nat.choose_symm hj_le]
