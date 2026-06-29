import Mathlib
import Workspace.ProofLemmas.CircConvInfra
import Workspace.ProofLemmas.PeriodicCircConvPeriodisation
import Workspace.ProofLemmas.PeriodicBaseKfoldPeriodisation

open scoped Real
open MeasureTheory intervalIntegral CircConvInfra PeriodicCircConvPeriodisation
  PeriodicBaseKfoldPeriodisation

set_option maxHeartbeats 4000000

namespace CircPowMultiplicity

/-! ## Linear (whole-line) convolution algebra -/

/-- Linear (whole-line) convolution of two real functions:
`linConv f g ξ = ∫ η, f η * g (ξ - η)`. -/
noncomputable def linConv (f g : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ η, f η * g (ξ - η)

/-- `linConv` matches Mathlib's `convolution` with `lsmul ℝ ℝ`. -/
theorem linConv_eq_convolution (f g : ℝ → ℝ) :
    linConv f g =
      MeasureTheory.convolution f g (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume := by
  funext ξ
  rw [MeasureTheory.convolution_lsmul]
  simp [linConv, smul_eq_mul]

/-- The scalar-multiplication bilinear map is symmetric: `(lsmul ℝ ℝ).flip = lsmul ℝ ℝ`. -/
theorem lsmul_flip_self : ((ContinuousLinearMap.lsmul ℝ ℝ).flip) = ContinuousLinearMap.lsmul ℝ ℝ := by
  refine ContinuousLinearMap.ext (fun a => ContinuousLinearMap.ext (fun b => ?_))
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_comm b a

/-- **Commutativity of linear convolution.** No integrability needed. -/
theorem linConv_comm (f g : ℝ → ℝ) : linConv f g = linConv g f := by
  rw [linConv_eq_convolution, linConv_eq_convolution]
  have h := MeasureTheory.convolution_flip (𝕜 := ℝ) (μ := (MeasureTheory.volume : Measure ℝ))
    (f := g) (g := f) (ContinuousLinearMap.lsmul ℝ ℝ)
  rw [lsmul_flip_self] at h
  exact h

/-! ## "Good" functions: continuous with compact support.

For functions in this class every convolution-existence side condition holds
*everywhere*, which lets us close the associativity side goals of
`MeasureTheory.convolution_assoc` cleanly, and the class is closed under
`linConv`. -/

/-- A function is `Good` if it is continuous and has compact support. -/
def Good (f : ℝ → ℝ) : Prop := Continuous f ∧ HasCompactSupport f

theorem Good.continuous {f : ℝ → ℝ} (hf : Good f) : Continuous f := hf.1
theorem Good.hasCompactSupport {f : ℝ → ℝ} (hf : Good f) : HasCompactSupport f := hf.2

theorem Good.integrable {f : ℝ → ℝ} (hf : Good f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hf.hasCompactSupport

theorem Good.locallyIntegrable {f : ℝ → ℝ} (hf : Good f) :
    MeasureTheory.LocallyIntegrable f :=
  hf.continuous.locallyIntegrable

/-- The norm of a `Good` function is `Good`. -/
theorem Good.norm {f : ℝ → ℝ} (hf : Good f) : Good (fun x => ‖f x‖) :=
  ⟨hf.continuous.norm, hf.hasCompactSupport.norm⟩

/-- `linConv` of two `Good` functions is `Good`. -/
theorem Good.linConv {f g : ℝ → ℝ} (hf : Good f) (hg : Good g) : Good (linConv f g) := by
  rw [linConv_eq_convolution]
  refine ⟨?_, ?_⟩
  · exact HasCompactSupport.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      hf.hasCompactSupport hf.continuous hg.locallyIntegrable
  · exact HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      hf.hasCompactSupport hg.hasCompactSupport

/-- **Associativity of linear convolution for `Good` functions.** -/
theorem linConv_assoc {f g h : ℝ → ℝ} (hf : Good f) (hg : Good g) (hh : Good h) :
    linConv f (linConv g h) = linConv (linConv f g) h := by
  simp only [linConv_eq_convolution]
  funext x
  rw [MeasureTheory.convolution_assoc (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.lsmul ℝ ℝ)
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (by intro a b c; simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]; ring)
    hf.continuous.aestronglyMeasurable hg.continuous.aestronglyMeasurable
    hh.continuous.aestronglyMeasurable]
  · -- ∀ᵐ y, ConvolutionExistsAt f g y lsmul
    exact Filter.Eventually.of_forall
      (HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
        hf.hasCompactSupport hf.continuous hg.locallyIntegrable)
  · -- ∀ᵐ x, ConvolutionExistsAt ‖g‖ ‖h‖ x mul
    exact Filter.Eventually.of_forall
      (HasCompactSupport.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ)
        hg.norm.hasCompactSupport hg.norm.continuous hh.norm.locallyIntegrable)
  · -- ConvolutionExistsAt ‖f‖ (‖g‖ ⋆ ‖h‖) x mul
    have hgh_cont : Continuous
        (MeasureTheory.convolution (fun x => ‖g x‖) (fun x => ‖h x‖)
          (ContinuousLinearMap.mul ℝ ℝ) volume) :=
      HasCompactSupport.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
        hg.norm.hasCompactSupport hg.norm.continuous hh.norm.locallyIntegrable
    exact HasCompactSupport.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ)
      hf.norm.hasCompactSupport hf.norm.continuous hgh_cont.locallyIntegrable x

/-! ## Linear power-additivity -/

/-- For `m ≥ 1`, the linear self-convolution step is exactly `linConv`. -/
theorem linPow_succ_eq_linConv (g0 : ℝ → ℝ) (m : ℕ) (hm : 1 ≤ m) :
    linPow g0 (m + 1) = linConv (linPow g0 m) g0 := by
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  rw [show m' + 1 + 1 = m' + 2 from rfl, linPow_succ_succ]
  rfl

/-- Each `linPow g0 m` (`m ≥ 1`) is `Good` when `g0` is. -/
theorem Good.linPow {g0 : ℝ → ℝ} (hg0 : Good g0) :
    ∀ m : ℕ, 1 ≤ m → Good (linPow g0 m) := by
  intro m hm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  clear hm
  induction m' with
  | zero => rwa [linPow_one]
  | succ k ih =>
    rw [linPow_succ_eq_linConv g0 (k + 1) (Nat.succ_le_succ (Nat.zero_le _))]
    exact ih.linConv hg0

/-- **Linear power-additivity.** For `a, b ≥ 1` and `Good` base `g0`,
`linConv (linPow g0 a) (linPow g0 b) = linPow g0 (a + b)`.
Proof by induction on `b` using `linConv_assoc` and `linConv_comm`. -/
theorem linPow_add {g0 : ℝ → ℝ} (hg0 : Good g0) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      linConv (linPow g0 a) (linPow g0 b) = linPow g0 (a + b) := by
  intro a b ha hb
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb)
  clear hb
  induction b' with
  | zero =>
    -- linConv (linPow g0 a) (linPow g0 1) = linConv (linPow g0 a) g0 = linPow g0 (a+1)
    rw [linPow_one, ← linPow_succ_eq_linConv g0 a ha]
  | succ k ih =>
    -- linPow g0 (k+1+1) = linConv (linPow g0 (k+1)) g0
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    rw [linPow_succ_eq_linConv g0 (k + 1) hk1]
    -- linConv (linPow g0 a) (linConv (linPow g0 (k+1)) g0)
    --   = linConv (linConv (linPow g0 a) (linPow g0 (k+1))) g0   (assoc)
    --   = linConv (linPow g0 (a + (k+1))) g0                     (IH)
    --   = linPow g0 (a + (k+1) + 1) = linPow g0 (a + (k+1+1))
    rw [linConv_assoc (hg0.linPow a ha) (hg0.linPow (k + 1) hk1) hg0]
    rw [ih]
    rw [← linPow_succ_eq_linConv g0 (a + (k + 1)) (le_trans ha (Nat.le_add_right a (k + 1)))]
    congr 1

/-! ## Circular convolution algebra (for `2π`-periodic functions) -/

/-- **Commutativity of circular convolution** for `2π`-periodic functions. -/
theorem circConvR_comm {f g : ℝ → ℝ}
    (hf : ∀ x, f (x + 2 * Real.pi) = f x) (hg : ∀ x, g (x + 2 * Real.pi) = g x) :
    circConvR f g = circConvR g f := by
  funext ξ
  unfold circConvR
  congr 1
  -- ∫_{-π}^π f η * g(ξ-η) = ∫_{-π}^π g η * f(ξ-η)
  have hstep1 : (∫ η in (-Real.pi)..Real.pi, f η * g (ξ - η))
      = ∫ u in (ξ - Real.pi)..(ξ + Real.pi), f (ξ - u) * g u := by
    have := intervalIntegral.integral_comp_sub_left
      (fun u => f (ξ - u) * g u) ξ (a := -Real.pi) (b := Real.pi)
    simp only [sub_sub_cancel] at this
    rw [this]
    congr 1
    ring
  -- periodic-window shift: ξ-π .. ξ+π  →  -π .. π
  have hper : Function.Periodic (fun u => f (ξ - u) * g u) (2 * Real.pi) := by
    intro u
    simp only
    have e1 : ξ - (u + 2 * Real.pi) = (ξ - u) - 2 * Real.pi := by ring
    rw [e1]
    have hfper : f ((ξ - u) - 2 * Real.pi) = f (ξ - u) := by
      have := hf ((ξ - u) - 2 * Real.pi); rw [sub_add_cancel] at this; exact this.symm
    rw [hfper, hg u]
  have hshift : (∫ u in (ξ - Real.pi)..(ξ + Real.pi), f (ξ - u) * g u)
      = ∫ u in (-Real.pi)..Real.pi, f (ξ - u) * g u := by
    have h := hper.intervalIntegral_add_eq (t := ξ - Real.pi) (s := -Real.pi)
    have e2 : ξ - Real.pi + 2 * Real.pi = ξ + Real.pi := by ring
    have e3 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [e2, e3] at h
    exact h
  have hstep2 : (∫ u in (-Real.pi)..Real.pi, f (ξ - u) * g u)
      = ∫ η in (-Real.pi)..Real.pi, g η * f (ξ - η) := by
    rw [show (fun u => f (ξ - u) * g u) = (fun u => g u * f (ξ - u)) by
      funext u; ring]
  rw [hstep1, hshift, hstep2]

/-- A function is `GoodP` if it is continuous and `2π`-periodic. -/
def GoodP (f : ℝ → ℝ) : Prop := Continuous f ∧ (∀ x, f (x + 2 * Real.pi) = f x)

theorem GoodP.continuous {f : ℝ → ℝ} (hf : GoodP f) : Continuous f := hf.1
theorem GoodP.periodic {f : ℝ → ℝ} (hf : GoodP f) : ∀ x, f (x + 2 * Real.pi) = f x := hf.2

/-- `circConvR` of two `GoodP` functions is `GoodP`. -/
theorem GoodP.circConvR {f g : ℝ → ℝ} (hf : GoodP f) (hg : GoodP g) :
    GoodP (circConvR f g) :=
  ⟨circConvR_continuous f g hf.continuous hg.continuous,
   circConvR_periodic f g hg.periodic⟩

/-- Pull the inner `circConvR`'s `(1/2π)` constant out of the outer integral (left arg). -/
theorem circConvR_assoc_lhs_expand (f g h : ℝ → ℝ) (ξ : ℝ) :
    circConvR f (circConvR g h) ξ
      = (1 / (2 * Real.pi)) ^ 2 *
          ∫ η in (-Real.pi)..Real.pi, ∫ τ in (-Real.pi)..Real.pi,
            f η * (g τ * h (ξ - η - τ)) := by
  unfold circConvR
  rw [sq, mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  rw [intervalIntegral.integral_const_mul]
  ring

theorem circConvR_assoc_rhs_expand (f g h : ℝ → ℝ) (ξ : ℝ) :
    circConvR (circConvR f g) h ξ
      = (1 / (2 * Real.pi)) ^ 2 *
          ∫ η in (-Real.pi)..Real.pi, ∫ σ in (-Real.pi)..Real.pi,
            f σ * (g (η - σ) * h (ξ - η)) := by
  unfold circConvR
  rw [sq, mul_assoc]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro η _
  simp only
  rw [show (fun σ => f σ * (g (η - σ) * h (ξ - η)))
      = (fun σ => (f σ * g (η - σ)) * h (ξ - η)) by funext σ; ring]
  rw [intervalIntegral.integral_mul_const]
  ring

/-- **Inner substitution + periodic window shift.** For `2π`-periodic `g, h` and any `σ`,
`∫_{-π}^π g(η - σ) h(ξ - η) dη = ∫_{-π}^π g(τ) h(ξ - σ - τ) dτ`.
(Change of variables `η = σ + τ`, then shift the `2π`-periodic integrand's window.) -/
theorem inner_shift {g h : ℝ → ℝ}
    (hg : ∀ x, g (x + 2 * Real.pi) = g x) (hh : ∀ x, h (x + 2 * Real.pi) = h x)
    (ξ σ : ℝ) :
    (∫ η in (-Real.pi)..Real.pi, g (η - σ) * h (ξ - η))
      = ∫ τ in (-Real.pi)..Real.pi, g τ * h (ξ - σ - τ) := by
  -- substitute η = τ + σ
  have hsub : (∫ η in (-Real.pi)..Real.pi, g (η - σ) * h (ξ - η))
      = ∫ τ in (-Real.pi - σ)..(Real.pi - σ), g τ * h (ξ - (τ + σ)) := by
    have := intervalIntegral.integral_comp_add_right
      (fun η => g (η - σ) * h (ξ - η)) σ (a := -Real.pi - σ) (b := Real.pi - σ)
    simp only [sub_add_cancel] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [add_sub_cancel_right]
  -- periodic window shift: (-π-σ) .. (π-σ)  →  -π .. π
  have hper : Function.Periodic (fun τ => g τ * h (ξ - (τ + σ))) (2 * Real.pi) := by
    intro τ
    simp only
    rw [hg τ]
    congr 1
    have e1 : ξ - (τ + 2 * Real.pi + σ) = (ξ - (τ + σ)) - 2 * Real.pi := by ring
    rw [e1]
    have := hh ((ξ - (τ + σ)) - 2 * Real.pi)
    rw [sub_add_cancel] at this
    exact this.symm
  have hshift : (∫ τ in (-Real.pi - σ)..(Real.pi - σ), g τ * h (ξ - (τ + σ)))
      = ∫ τ in (-Real.pi)..Real.pi, g τ * h (ξ - (τ + σ)) := by
    have h := hper.intervalIntegral_add_eq (t := -Real.pi - σ) (s := -Real.pi)
    have e2 : -Real.pi - σ + 2 * Real.pi = Real.pi - σ := by ring
    have e3 : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [e2, e3] at h
    exact h
  rw [hsub, hshift]
  apply intervalIntegral.integral_congr
  intro τ _
  simp only
  congr 2
  ring

/-- Fubini swap of the double interval integral over the `[-π,π]²` box, for a
continuous integrand. -/
theorem double_integral_swap {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) :
    (∫ η in (-Real.pi)..Real.pi, ∫ σ in (-Real.pi)..Real.pi, F η σ)
      = ∫ σ in (-Real.pi)..Real.pi, ∫ η in (-Real.pi)..Real.pi, F η σ := by
  have hπ : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  -- convert both interval integrals to set integrals over Ioc
  simp only [intervalIntegral.integral_of_le hπ]
  -- now: ∫_η ∂(restrict Ioc) ∫_σ ∂(restrict Ioc) F η σ = swapped
  haveI hfact : Fact (MeasureTheory.volume (Set.Ioc (-Real.pi) Real.pi) < ⊤) :=
    ⟨by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  set μ : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-Real.pi) Real.pi) with hμ
  haveI hfin : MeasureTheory.IsFiniteMeasure μ := by
    rw [hμ]; infer_instance
  have hint : MeasureTheory.Integrable (Function.uncurry fun η σ => F η σ) (μ.prod μ) := by
    rw [hμ, MeasureTheory.Measure.prod_restrict]
    have hcpt : IsCompact (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi) :=
      isCompact_Icc.prod isCompact_Icc
    have hIO : MeasureTheory.IntegrableOn (Function.uncurry fun η σ => F η σ)
        (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi)
        (MeasureTheory.volume.prod MeasureTheory.volume) := by
      rw [← MeasureTheory.Measure.volume_eq_prod]
      exact hF.continuousOn.integrableOn_compact hcpt
    have hsub : (Set.Ioc (-Real.pi) Real.pi ×ˢ Set.Ioc (-Real.pi) Real.pi)
        ⊆ (Set.Icc (-Real.pi) Real.pi ×ˢ Set.Icc (-Real.pi) Real.pi) :=
      Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
    exact hIO.mono_set hsub
  rw [MeasureTheory.integral_integral_swap hint]

/-- **Associativity of circular convolution** for `GoodP` (continuous + `2π`-periodic)
functions. -/
theorem circConvR_assoc {f g h : ℝ → ℝ} (hf : GoodP f) (hg : GoodP g) (hh : GoodP h) :
    circConvR f (circConvR g h) = circConvR (circConvR f g) h := by
  funext ξ
  rw [circConvR_assoc_lhs_expand, circConvR_assoc_rhs_expand]
  congr 1
  -- RHS double integral: swap order via Fubini
  have hswap := double_integral_swap (F := fun η σ => f σ * (g (η - σ) * h (ξ - η)))
    (by
      apply Continuous.mul
      · exact hf.continuous.comp continuous_snd
      · apply Continuous.mul
        · exact hg.continuous.comp (continuous_fst.sub continuous_snd)
        · exact hh.continuous.comp (continuous_const.sub continuous_fst))
  rw [hswap]
  -- now: ∫_σ ∫_η f σ * (g(η-σ)*h(ξ-η)) dη dσ  =  ∫_η ∫_τ f η * (g τ * h(ξ-η-τ)) dτ dη
  apply intervalIntegral.integral_congr
  intro σ _
  simp only
  -- LHS: ∫_τ f σ * (g τ * h(ξ-σ-τ))   RHS: ∫_η f σ * (g(η-σ)*h(ξ-η))
  conv_lhs => rw [intervalIntegral.integral_const_mul]
  conv_rhs => rw [intervalIntegral.integral_const_mul]
  congr 1
  exact (inner_shift hg.periodic hh.periodic ξ σ).symm

/-! ## Circular power-additivity -/

/-- Each `circPowR g m` (`m ≥ 1`) is `GoodP` when `g` is. -/
theorem GoodP.circPowR {g : ℝ → ℝ} (hg : GoodP g) :
    ∀ m : ℕ, 1 ≤ m → GoodP (circPowR g m) := by
  intro m hm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  clear hm
  induction m' with
  | zero => rwa [circPowR_one]
  | succ k ih =>
    rw [circPowR_succ_of_pos g (k + 1) (Nat.succ_le_succ (Nat.zero_le _))]
    exact ih.circConvR hg

/-- **Circular power-additivity.** For `a, b ≥ 1` and `GoodP` base `g`,
`circConvR (circPowR g a) (circPowR g b) = circPowR g (a + b)`.
Proof by induction on `b` using `circConvR_assoc`. -/
theorem circPowR_add {g : ℝ → ℝ} (hg : GoodP g) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      circConvR (circPowR g a) (circPowR g b) = circPowR g (a + b) := by
  intro a b ha hb
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hb)
  clear hb
  induction b' with
  | zero =>
    rw [circPowR_one]
    rw [show a + Nat.succ 0 = a + 1 from rfl, circPowR_succ_of_pos g a ha]
  | succ k ih =>
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le _)
    rw [circPowR_succ_of_pos g (k + 1) hk1]
    rw [circConvR_assoc (hg.circPowR a ha) (hg.circPowR (k + 1) hk1) hg]
    rw [ih]
    rw [show a + (k + 1).succ = (a + (k + 1)) + 1 by omega,
      circPowR_succ_of_pos g (a + (k + 1)) (le_trans ha (Nat.le_add_right a (k + 1)))]

end CircPowMultiplicity
