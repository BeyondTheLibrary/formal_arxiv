import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.MixtureRawMoments
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian

set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas

open MeasureTheory ProbabilityTheory

/-- Helper: NNReal coercion ≠ 0 from positivity. -/
private lemma nnreal_mk_ne_zero (τSq : ℝ) (hτ : 0 < τSq) :
    (⟨τSq, le_of_lt hτ⟩ : NNReal) ≠ 0 := by
  intro h
  have h2 : ((⟨τSq, le_of_lt hτ⟩ : NNReal) : ℝ) = ((0 : NNReal) : ℝ) := by
    exact_mod_cast congrArg (Subtype.val : NNReal → ℝ) h
  simp at h2
  linarith

/-- m₀ of N(0, τ²) is 1 (probability normalization). -/
private lemma m0_eq_one (τSq : ℝ) (hτ : 0 < τSq) :
    ∫ x, ((Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x)
        ∂MeasureTheory.volume = 1 := by
  set v : NNReal := ⟨τSq, le_of_lt hτ⟩ with hv_def
  have hv_ne : v ≠ 0 := nnreal_mk_ne_zero τSq hτ
  have hdens : (fun x : ℝ =>
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x) =
      fun x => gaussianPDFReal 0 v x := by
    funext x
    exact Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal _ x
  rw [hdens]
  exact integral_gaussianPDFReal_eq_one 0 hv_ne

/-- m₁ of N(0, τ²) is 0. -/
private lemma m1_eq_zero (τSq : ℝ) (hτ : 0 < τSq) :
    ∫ x, x * ((Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x)
        ∂MeasureTheory.volume = 0 := by
  set v : NNReal := ⟨τSq, le_of_lt hτ⟩ with hv_def
  have hv_ne : v ≠ 0 := nnreal_mk_ne_zero τSq hτ
  have h1 : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  have h2 := integral_gaussianReal_eq_integral_smul (μ := 0) (v := v) (f := fun x : ℝ => x) hv_ne
  rw [h2] at h1
  have hgdens : (fun x : ℝ => x *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x) =
      (fun x : ℝ => gaussianPDFReal 0 v x • x) := by
    funext x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal]
    show x * gaussianPDFReal 0 v x = gaussianPDFReal 0 v x • x
    rw [smul_eq_mul, mul_comm]
  rw [hgdens]
  exact h1

/-- Integrability of `x^j · density` for the centered Gaussian. -/
private lemma int_xpow_density (τSq : ℝ) (hτ : 0 < τSq) (j : ℕ) :
    Integrable (fun x : ℝ => x ^ j *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x) volume :=
  Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian _ j

/-- Derivative of the centered Gaussian density: d/dx N(0, τ², x) = -(x/τ²) · N(0, τ², x). -/
private lemma density_hasDerivAt (τSq : ℝ) (hτ : 0 < τSq) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density y)
      ((-(x / τSq)) * (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x) x := by
  set C : ℝ := 1 / Real.sqrt (2 * Real.pi * τSq) with hC_def
  have h_inner : HasDerivAt (fun y : ℝ => -(y - 0)^2 / (2 * τSq))
      (-(2 * (x - 0)) / (2 * τSq)) x := by
    have h_sq : HasDerivAt (fun y : ℝ => (y - 0)^2) (2 * (x - 0)) x := by
      simpa using ((hasDerivAt_id x).sub_const 0).pow 2
    exact (h_sq.neg).div_const (2 * τSq)
  have h_exp : HasDerivAt (fun y : ℝ => Real.exp (-(y - 0)^2 / (2 * τSq)))
      (Real.exp (-(x - 0)^2 / (2 * τSq)) * (-(2 * (x - 0)) / (2 * τSq))) x :=
    h_inner.exp
  have h_dens : HasDerivAt
      (fun y : ℝ => (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density y)
      (C * (Real.exp (-(x - 0)^2 / (2 * τSq)) * (-(2 * (x - 0)) / (2 * τSq)))) x := by
    show HasDerivAt (fun y =>
      (1 / Real.sqrt (2 * Real.pi * τSq)) * Real.exp (-(y - 0)^2 / (2 * τSq))) _ x
    exact h_exp.const_mul _
  convert h_dens using 1
  show (-(x / τSq)) * (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x =
       C * (Real.exp (-(x - 0)^2 / (2 * τSq)) * (-(2 * (x - 0)) / (2 * τSq)))
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  show (-(x / τSq)) *
       ((1 / Real.sqrt (2 * Real.pi * τSq)) * Real.exp (-(x - 0)^2 / (2 * τSq))) =
       C * (Real.exp (-(x - 0)^2 / (2 * τSq)) * (-(2 * (x - 0)) / (2 * τSq)))
  have hτ_ne : τSq ≠ 0 := ne_of_gt hτ
  have hsqrt_ne : Real.sqrt (2 * Real.pi * τSq) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  rw [hC_def]
  field_simp
  ring

/-- For continuous functions vanishing at infinity (Gaussian density times any polynomial),
    we use the `_of_integrable` IBP form. The hypotheses require differentiability
    on `tsupport`, which is all of ℝ for both u and v (the polynomial * density). -/
private lemma moment_recurrence (τSq : ℝ) (hτ : 0 < τSq) (j : ℕ) :
    ∫ x, x ^ (j + 2) *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume
    = (j + 1 : ℝ) * τSq * ∫ x, x ^ j *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume := by
  -- u(x) = x^(j+1), v(x) = -τSq * density(x).
  -- u'(x) = (j+1) * x^j, v'(x) = x * density(x).
  -- u * v' = x^(j+2) * density, u' * v = -(j+1)τSq * (x^j * density), u * v = -τSq * (x^(j+1) * density).
  -- IBP: ∫ u v' = -∫ u' v.
  let G : Workspace.Types.GaussianPDF.GaussianPDF := ⟨0, τSq, hτ⟩
  let u : ℝ → ℝ := fun x => x ^ (j + 1)
  let u' : ℝ → ℝ := fun x => (j + 1 : ℝ) * x ^ j
  let v : ℝ → ℝ := fun x => -τSq * G.density x
  let v' : ℝ → ℝ := fun x => x * G.density x
  have hu_deriv : ∀ x, HasDerivAt u (u' x) x := by
    intro x
    show HasDerivAt (fun y => y ^ (j + 1)) ((j + 1 : ℝ) * x ^ j) x
    have h := hasDerivAt_pow (j + 1) x
    simpa using h
  have hv_deriv : ∀ x, HasDerivAt v (v' x) x := by
    intro x
    show HasDerivAt (fun y => -τSq * G.density y) (x * G.density x) x
    have hd := density_hasDerivAt τSq hτ x
    have h := hd.const_mul (-τSq)
    convert h using 1
    show x * G.density x = -τSq * (-(x / τSq) * G.density x)
    have hτ_ne : τSq ≠ 0 := ne_of_gt hτ
    field_simp
  -- u * v' as a fun equality
  have huv'_eq : (fun x => u x * v' x) = fun x => x ^ (j + 2) * G.density x := by
    funext x
    show x ^ (j + 1) * (x * G.density x) = x ^ (j + 2) * G.density x
    ring
  have hu'v_eq : (fun x => u' x * v x) = fun x => -((j + 1 : ℝ) * τSq) * (x ^ j * G.density x) := by
    funext x
    show (j + 1 : ℝ) * x ^ j * (-τSq * G.density x) =
         -((j + 1 : ℝ) * τSq) * (x ^ j * G.density x)
    ring
  have huv_eq : (fun x => u x * v x) = fun x => -τSq * (x ^ (j + 1) * G.density x) := by
    funext x
    show x ^ (j + 1) * (-τSq * G.density x) = -τSq * (x ^ (j + 1) * G.density x)
    ring
  -- Integrability of u * v', u' * v, u * v
  have h_int_uv' : Integrable (fun x => u x * v' x) volume := by
    rw [huv'_eq]
    exact int_xpow_density τSq hτ (j + 2)
  have h_int_u'v : Integrable (fun x => u' x * v x) volume := by
    rw [hu'v_eq]
    exact (int_xpow_density τSq hτ j).const_mul (-((j + 1 : ℝ) * τSq))
  have h_int_uv : Integrable (fun x => u x * v x) volume := by
    rw [huv_eq]
    exact (int_xpow_density τSq hτ (j + 1)).const_mul (-τSq)
  -- IBP requires Integrable on `u * v'`, `u' * v`, `u * v` (not curried)
  have h_int_uv'_curr : Integrable (u * v') volume := h_int_uv'
  have h_int_u'v_curr : Integrable (u' * v) volume := h_int_u'v
  have h_int_uv_curr : Integrable (u * v) volume := h_int_uv
  -- Apply IBP. The `tsupport`-restricted hypothesis is satisfied by the universal hu_deriv.
  have h_ibp : ∫ x, u x * v' x = -∫ x, u' x * v x :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := u) (v := v) (u' := u') (v' := v')
      (fun x _ => hu_deriv x) (fun x _ => hv_deriv x)
      h_int_uv'_curr h_int_u'v_curr h_int_uv_curr
  -- LHS: ∫ u x * v' x = ∫ x^(j+2) * G.density x
  have h_lhs : ∫ x, u x * v' x = ∫ x, x ^ (j + 2) * G.density x := by
    exact congrArg (fun f => ∫ x, f x) huv'_eq
  -- RHS: ∫ u' x * v x = ∫ -((j+1)*τSq) * (x^j * G.density x)
  have h_rhs : ∫ x, u' x * v x = ∫ x, -((j + 1 : ℝ) * τSq) * (x ^ j * G.density x) := by
    exact congrArg (fun f => ∫ x, f x) hu'v_eq
  rw [h_lhs] at h_ibp
  rw [h_rhs] at h_ibp
  rw [h_ibp]
  rw [integral_const_mul]
  ring

/-- Even case: ∫ x^(2k) · density = (2k-1)!! · √τSq^(2k). -/
private lemma moment_even (τSq : ℝ) (hτ : 0 < τSq) :
    ∀ k : ℕ, ∫ x, x ^ (2 * k) *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume
      = (Nat.doubleFactorial (2 * k - 1) : ℝ) * Real.sqrt τSq ^ (2 * k) := by
  intro k
  induction k with
  | zero =>
    show ∫ x, x ^ (2 * 0) *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume
      = (Nat.doubleFactorial (2 * 0 - 1) : ℝ) * Real.sqrt τSq ^ (2 * 0)
    simp only [Nat.mul_zero, pow_zero, one_mul,
               Nat.doubleFactorial, Nat.cast_one]
    have h := m0_eq_one τSq hτ
    linarith [h]
  | succ k ih =>
    have hrec := moment_recurrence τSq hτ (2 * k)
    have hidx : 2 * k + 2 = 2 * (k + 1) := by ring
    rw [hidx] at hrec
    rw [hrec, ih]
    have hτSq_nn : (0 : ℝ) ≤ τSq := le_of_lt hτ
    have hsqrt_sq : Real.sqrt τSq ^ 2 = τSq := Real.sq_sqrt hτSq_nn
    have hp : Real.sqrt τSq ^ (2 * (k + 1)) =
              Real.sqrt τSq ^ (2 * k) * τSq := by
      have h_idx : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [h_idx, pow_add, hsqrt_sq]
    rw [hp]
    have hdf : ((2 * (k + 1) - 1).doubleFactorial : ℝ) =
               (2 * k + 1) * ((2 * k - 1).doubleFactorial : ℝ) := by
      rcases k with _ | k'
      · simp [Nat.doubleFactorial]
      · have h_idx1 : 2 * (k' + 1 + 1) - 1 = 2 * k' + 1 + 2 := by omega
        have h_idx2 : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
        rw [h_idx1, h_idx2, Nat.doubleFactorial_add_two]
        push_cast
        ring
    push_cast
    rw [hdf]
    ring

/-- Odd case: ∫ x^(2k+1) · density = 0. -/
private lemma moment_odd (τSq : ℝ) (hτ : 0 < τSq) :
    ∀ k : ℕ, ∫ x, x ^ (2 * k + 1) *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume = 0 := by
  intro k
  induction k with
  | zero =>
    show ∫ x, x ^ (2 * 0 + 1) *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume = 0
    simp only [Nat.mul_zero, zero_add, pow_one]
    exact m1_eq_zero τSq hτ
  | succ k ih =>
    have hrec := moment_recurrence τSq hτ (2 * k + 1)
    have hidx : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by ring
    rw [hidx] at hrec
    rw [hrec, ih]
    ring

theorem SublemmaCentralMomentN0Tau :
    ∀ (τSq : ℝ) (hτ : 0 < τSq) (j : ℕ),
      let G : Workspace.Types.GaussianPDF.GaussianPDF := ⟨0, τSq, hτ⟩
      (Odd j → Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G j = 0)
      ∧ (Even j →
          Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian G j
            = (Nat.doubleFactorial (j - 1) : ℝ) * Real.sqrt τSq ^ j) := by
  intro τSq hτ j
  show (Odd j → ∫ x, x ^ j *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume = 0)
    ∧ (Even j → ∫ x, x ^ j *
      (Workspace.Types.GaussianPDF.GaussianPDF.mk 0 τSq hτ).density x ∂volume =
        (Nat.doubleFactorial (j - 1) : ℝ) * Real.sqrt τSq ^ j)
  refine ⟨?_, ?_⟩
  · intro hodd
    obtain ⟨k, hk⟩ := hodd
    have hj : j = 2 * k + 1 := hk
    rw [hj]
    exact moment_odd τSq hτ k
  · intro heven
    obtain ⟨k, hk⟩ := heven
    have hj : j = 2 * k := by omega
    rw [hj]
    exact moment_even τSq hτ k

end Workspace.ProofLemmas
