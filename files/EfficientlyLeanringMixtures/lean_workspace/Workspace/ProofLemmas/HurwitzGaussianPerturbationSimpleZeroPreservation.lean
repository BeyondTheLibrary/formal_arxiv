import Mathlib
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianPDF
import Workspace.ProofLemmas.SublemmaSmallPerturbationOnZeroNbhds
import Workspace.ProofLemmas.SublemmaSmallPerturbationDerivOnZeroNbhds
import Workspace.ProofLemmas.SublemmaGLowerBoundOnA

namespace Workspace.ProofLemmas

open Workspace.Types.ZeroCount
open Workspace.Types.GaussianPDF
open Set

set_option maxHeartbeats 1600000

/-- Localized R3 (perturbation deriv bound only on the closed nbhd): a C¹ function
`g` with a nonzero derivative at `x_j` and `|deriv g| ≥ |deriv g x_j|/2` on the
closed ε₂-neighbourhood stays strictly monotone after a C¹ perturbation `p` whose
derivative is `< |deriv g x_j|/2` *on that neighbourhood*, hence has ≤1 zero there.

This is the on-neighbourhood variant of `SublemmaR3OneZeroPerNeighbourhood` (which
demands a *global* derivative bound on `p`); the perturbation-derivative decay we
have is only uniform on the compact region, so the local form is what is needed. -/
private theorem hgp_R3Local
    (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
    (x_j : ℝ) (h_simple : deriv g x_j ≠ 0)
    (ε₂ : ℝ) (hε₂ : 0 < ε₂)
    (h_deriv_bound : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂),
        |deriv g x_j| / 2 ≤ |deriv g x|) :
    ∀ (p : ℝ → ℝ), ContDiff ℝ 1 p →
      (∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), |deriv p x| < |deriv g x_j| / 2) →
      ∀ x₁ x₂ : ℝ,
        x₁ ∈ Set.Icc (x_j - ε₂) (x_j + ε₂) →
        x₂ ∈ Set.Icc (x_j - ε₂) (x_j + ε₂) →
        g x₁ + p x₁ = 0 → g x₂ + p x₂ = 0 →
        x₁ = x₂ := by
  set M : ℝ := |deriv g x_j| / 2 with hM_def
  have hM_pos : 0 < M := by
    have : 0 < |deriv g x_j| := abs_pos.mpr h_simple
    simpa [hM_def] using half_pos this
  have hg_diff : Differentiable ℝ g := hg.differentiable_one
  have hderivg_cont : Continuous (deriv g) := hg.continuous_deriv_one
  intro p hp hp_bd x₁ x₂ hx₁ hx₂ hz₁ hz₂
  have hp_diff : Differentiable ℝ p := hp.differentiable_one
  let f : ℝ → ℝ := fun x => g x + p x
  have hf_diff : Differentiable ℝ f := hg_diff.add hp_diff
  have hf_deriv : ∀ x, deriv f x = deriv g x + deriv p x := by
    intro x
    have hg' : DifferentiableAt ℝ g x := hg_diff.differentiableAt
    have hp' : DifferentiableAt ℝ p x := hp_diff.differentiableAt
    simpa [f] using deriv_add hg' hp'
  rcases lt_or_gt_of_ne h_simple with h_neg | h_pos
  · have hderiv_g_neg : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), deriv g x < 0 := by
      intro x hx
      have h_lb : M ≤ |deriv g x| := h_deriv_bound x hx
      by_contra h_nonneg
      push_neg at h_nonneg
      have hxj_mem : x_j ∈ Set.Icc (x_j - ε₂) (x_j + ε₂) := ⟨by linarith, by linarith⟩
      have hseg : Set.uIcc x_j x ⊆ Set.Icc (x_j - ε₂) (x_j + ε₂) := by
        intro y hy
        rcases le_total x_j x with hle | hle
        · rw [Set.uIcc_of_le hle] at hy
          exact ⟨le_trans hxj_mem.1 hy.1, le_trans hy.2 hx.2⟩
        · rw [Set.uIcc_of_ge hle] at hy
          exact ⟨le_trans hx.1 hy.1, le_trans hy.2 hxj_mem.2⟩
      have h_ivt : Set.uIcc (deriv g x_j) (deriv g x) ⊆ deriv g '' Set.uIcc x_j x :=
        intermediate_value_uIcc hderivg_cont.continuousOn
      have h_zero_in_uIcc : (0 : ℝ) ∈ Set.uIcc (deriv g x_j) (deriv g x) := by
        rw [Set.uIcc_of_le (le_trans (le_of_lt h_neg) h_nonneg)]
        exact ⟨le_of_lt h_neg, h_nonneg⟩
      obtain ⟨y, hy_mem, hy_eq⟩ := h_ivt h_zero_in_uIcc
      have hy_in : y ∈ Set.Icc (x_j - ε₂) (x_j + ε₂) := hseg hy_mem
      have : M ≤ |deriv g y| := h_deriv_bound y hy_in
      rw [hy_eq] at this; simp at this; linarith
    have hderiv_g_le : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), deriv g x ≤ -M := by
      intro x hx
      have h_neg_x : deriv g x < 0 := hderiv_g_neg x hx
      have h_lb : M ≤ |deriv g x| := h_deriv_bound x hx
      have : |deriv g x| = -(deriv g x) := abs_of_neg h_neg_x
      linarith [this]
    have hderiv_f_neg : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), deriv f x < 0 := by
      intro x hx
      have h_g_le : deriv g x ≤ -M := hderiv_g_le x hx
      have h_p_lt' : deriv p x < M := lt_of_abs_lt (hp_bd x hx)
      have : deriv f x = deriv g x + deriv p x := hf_deriv x
      linarith
    have h_strict_anti : StrictAntiOn f (Set.Icc (x_j - ε₂) (x_j + ε₂)) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hf_diff.continuous.continuousOn
      intro x hx; exact hderiv_f_neg x (interior_subset hx)
    exact h_strict_anti.injOn hx₁ hx₂ (by rw [show f x₁ = 0 from hz₁, show f x₂ = 0 from hz₂])
  · have hderiv_g_pos : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), 0 < deriv g x := by
      intro x hx
      have h_lb : M ≤ |deriv g x| := h_deriv_bound x hx
      by_contra h_nonpos
      push_neg at h_nonpos
      have hxj_mem : x_j ∈ Set.Icc (x_j - ε₂) (x_j + ε₂) := ⟨by linarith, by linarith⟩
      have hseg : Set.uIcc x_j x ⊆ Set.Icc (x_j - ε₂) (x_j + ε₂) := by
        intro y hy
        rcases le_total x_j x with hle | hle
        · rw [Set.uIcc_of_le hle] at hy
          exact ⟨le_trans hxj_mem.1 hy.1, le_trans hy.2 hx.2⟩
        · rw [Set.uIcc_of_ge hle] at hy
          exact ⟨le_trans hx.1 hy.1, le_trans hy.2 hxj_mem.2⟩
      have h_ivt : Set.uIcc (deriv g x_j) (deriv g x) ⊆ deriv g '' Set.uIcc x_j x :=
        intermediate_value_uIcc hderivg_cont.continuousOn
      have h_zero_in_uIcc : (0 : ℝ) ∈ Set.uIcc (deriv g x_j) (deriv g x) := by
        rw [Set.uIcc_of_ge (le_trans h_nonpos (le_of_lt h_pos))]
        exact ⟨h_nonpos, le_of_lt h_pos⟩
      obtain ⟨y, hy_mem, hy_eq⟩ := h_ivt h_zero_in_uIcc
      have hy_in : y ∈ Set.Icc (x_j - ε₂) (x_j + ε₂) := hseg hy_mem
      have : M ≤ |deriv g y| := h_deriv_bound y hy_in
      rw [hy_eq] at this; simp at this; linarith
    have hderiv_g_ge : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), M ≤ deriv g x := by
      intro x hx
      have h_pos_x : 0 < deriv g x := hderiv_g_pos x hx
      have h_lb : M ≤ |deriv g x| := h_deriv_bound x hx
      have : |deriv g x| = deriv g x := abs_of_pos h_pos_x
      linarith [this]
    have hderiv_f_pos : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), 0 < deriv f x := by
      intro x hx
      have h_g_ge : M ≤ deriv g x := hderiv_g_ge x hx
      have h_p_gt : -M < deriv p x := neg_lt_of_abs_lt (hp_bd x hx)
      have : deriv f x = deriv g x + deriv p x := hf_deriv x
      linarith
    have h_strict_mono : StrictMonoOn f (Set.Icc (x_j - ε₂) (x_j + ε₂)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf_diff.continuous.continuousOn
      intro x hx; exact hderiv_f_pos x (interior_subset hx)
    exact h_strict_mono.injOn hx₁ hx₂ (by rw [show f x₁ = 0 from hz₁, show f x₂ = 0 from hz₂])

/-- Helper: explicit derivative formula for the Gaussian density. -/
private theorem hgp_density_deriv_eq (G : GaussianPDF) (x : ℝ) :
    deriv G.density x
      = (1 / Real.sqrt (2 * Real.pi * G.varSq)) *
          Real.exp (-(x - G.mean)^2 / (2 * G.varSq)) * (-(x - G.mean) / G.varSq) := by
  set V := G.varSq with hV_def
  set μ := G.mean with hμ_def
  have hV_pos : 0 < V := G.varSq_pos
  have h2V_pos : 0 < 2 * V := by linarith
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * V) := by positivity
  have h_sq_deriv : HasDerivAt (fun x : ℝ => (x - μ)^2) (2 * (x - μ)) x := by
    simpa using ((hasDerivAt_id x).sub_const μ).pow 2
  have h_inner_deriv : HasDerivAt (fun x : ℝ => -(x - μ)^2 / (2 * V))
      (-(2 * (x - μ)) / (2 * V)) x :=
    (h_sq_deriv.neg).div_const (2 * V)
  have h_exp_deriv : HasDerivAt (fun x : ℝ => Real.exp (-(x - μ)^2 / (2 * V)))
      (Real.exp (-(x - μ)^2 / (2 * V)) * (-(2 * (x - μ)) / (2 * V))) x :=
    h_inner_deriv.exp
  have h_dens_deriv : HasDerivAt G.density
      ((1 / Real.sqrt (2 * Real.pi * V)) *
        (Real.exp (-(x - μ)^2 / (2 * V)) * (-(2 * (x - μ)) / (2 * V)))) x := by
    show HasDerivAt (fun x =>
      (1 / Real.sqrt (2 * Real.pi * V)) * Real.exp (-(x - μ)^2 / (2 * V))) _ x
    exact h_exp_deriv.const_mul _
  rw [h_dens_deriv.deriv]
  have hV_ne : V ≠ 0 := ne_of_gt hV_pos
  have h2V_ne : (2:ℝ) * V ≠ 0 := ne_of_gt h2V_pos
  field_simp

private theorem hgp_density_contDiff (G : GaussianPDF) : ContDiff ℝ 1 G.density := by
  show ContDiff ℝ 1 (fun x => (1 / Real.sqrt (2 * Real.pi * G.varSq))
    * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq)))
  fun_prop

private theorem hgp_density_differentiable (G : GaussianPDF) : Differentiable ℝ G.density := by
  show Differentiable ℝ (fun x => (1 / Real.sqrt (2 * Real.pi * G.varSq))
    * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq)))
  fun_prop

/-- Finite-min of a positive per-element choice over a nonempty Finset. -/
private theorem hgp_finset_min_choice (Z : Finset ℝ) (hZ : Z.Nonempty)
    (ρfun : (x : ℝ) → x ∈ Z → ℝ) (hpos : ∀ x (hx : x ∈ Z), 0 < ρfun x hx) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x (hx : x ∈ Z), ε ≤ ρfun x hx := by
  classical
  let img : Finset ℝ := Z.attach.image (fun p => ρfun p.1 p.2)
  have hne : img.Nonempty := by
    rcases hZ with ⟨x, hx⟩
    exact ⟨ρfun x hx, Finset.mem_image.mpr ⟨⟨x,hx⟩, Finset.mem_attach _ _, rfl⟩⟩
  refine ⟨img.min' hne, ?_, ?_⟩
  · have hm := Finset.min'_mem img hne
    rcases Finset.mem_image.mp hm with ⟨⟨x,hx⟩, _, hval⟩
    rw [← hval]; exact hpos x hx
  · intro x hx
    have hmem : ρfun x hx ∈ img :=
      Finset.mem_image.mpr ⟨⟨x,hx⟩, Finset.mem_attach _ _, rfl⟩
    exact Finset.min'_le img (ρfun x hx) hmem

/-- Region (b) of Moitra–Valiant §6.1 ("add the k-th Gaussian"): sign-preservation
near the simple zeros of `g`.  Genuine ProofLemmas replacement for the prior-work
axiom `Workspace.PriorWork.HurwitzGaussianPerturbationSimpleZeroPreservation`
(same signature, so it is a drop-in replacement).

Let `g : ℝ → ℝ` be real-analytic with at most `N` zeros, all simple.  Fix a
bounded interval `[b, b']`, a centre `μ_k`, a buffer `δ > 0`, and `a_k ≠ 0`.
Then there is `v₀ > 0` such that for every `v ∈ (0, v₀]` the perturbed function
`h(x) = g x + a_k · N(μ_k, v, x)` has at most `N` distinct zeros in
`[b, b'] \ (μ_k − δ, μ_k + δ)`. -/
theorem HurwitzGaussianPerturbationSimpleZeroPreservation :
    ∀ (g : ℝ → ℝ),
      AnalyticOnNhd ℝ g Set.univ →
      ∀ (N : ℕ),
        Workspace.Types.ZeroCount.hasAtMostNZeros g N →
        (∀ x : ℝ, g x = 0 → deriv g x ≠ 0) →
        ∀ (b b' : ℝ), b < b' →
        ∀ (a_k : ℝ), a_k ≠ 0 →
        ∀ (μ_k : ℝ),
        ∀ (δ : ℝ), 0 < δ →
          ∃ v₀ : ℝ, 0 < v₀ ∧
            ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
              (Workspace.Types.ZeroCount.zeroSet
                  (fun x => g x +
                    a_k *
                      Workspace.Types.GaussianPDF.GaussianPDF.density
                        ⟨μ_k, v, hv⟩ x)
                ∩ (Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ))).encard
                ≤ (N : ℕ∞) := by
  intro g hg_an N hN h_simple b b' hbb' a_k hak μ_k δ hδ
  -- g is C¹ and its deriv is continuous (analytic ⇒ smooth).
  have hg_cont : Continuous g := hg_an.continuous
  have hg_C1 : ContDiff ℝ 1 g := by
    have h := hg_an.contDiff (n := (1 : ℕ∞))
    exact h
  have hderivg_cont : Continuous (deriv g) := hg_C1.continuous_deriv_one
  -- The region K.
  set K : Set ℝ := Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ) with hK_def
  have hK_compact : IsCompact K := (isCompact_Icc).diff isOpen_Ioo
  -- Zeros of g form a finite set.
  have hZg_fin : (zeroSet g).Finite := by
    have : (zeroSet g).encard ≤ (N : ℕ∞) := hN
    exact Set.finite_of_encard_le_coe this
  set Zgf : Finset ℝ := hZg_fin.toFinset with hZgf_def
  have hZgf_mem : ∀ x, x ∈ Zgf ↔ g x = 0 := by
    intro x; rw [hZgf_def, Set.Finite.mem_toFinset]; rfl
  have hZgf_card : Zgf.card ≤ N := by
    have hh : (zeroSet g).encard ≤ (N : ℕ∞) := hN
    have he : (zeroSet g).encard = (Zgf.card : ℕ∞) := by
      rw [hZgf_def, Set.Finite.encard_eq_coe_toFinset_card hZg_fin]
    rw [he] at hh
    exact_mod_cast hh
  classical
  -- Case split on whether g has any zeros.
  by_cases hZne : Zgf.Nonempty
  · -- Main case: g has zeros.
    have pointwise : ∀ x ∈ Zgf, ∃ ρ : ℝ, 0 < ρ ∧
        ∀ y ∈ Set.Icc (x - ρ) (x + ρ), |deriv g x| / 2 ≤ |deriv g y| := by
      intro x hx
      have hsx : deriv g x ≠ 0 := h_simple x ((hZgf_mem x).mp hx)
      have hpos : (0:ℝ) < |deriv g x| / 2 := by have := abs_pos.mpr hsx; linarith
      have hc : ContinuousAt (fun y => |deriv g y|) x :=
        (continuous_abs.comp hderivg_cont).continuousAt
      rcases Metric.continuousAt_iff.mp hc (|deriv g x|/2) hpos with ⟨ρ, hρ, hspec⟩
      refine ⟨ρ/2, by linarith, ?_⟩
      intro y hy
      simp only [Set.mem_Icc] at hy
      have hd : dist y x < ρ := by
        rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy.1, hy.2]
      have hs := hspec hd
      rw [Real.dist_eq] at hs
      have hb := abs_lt.mp hs
      linarith [hb.1]
    choose ρfun ρfun_pos ρfun_spec using pointwise
    obtain ⟨ρ₀, hρ₀_pos, hρ₀_le⟩ := hgp_finset_min_choice Zgf hZne ρfun ρfun_pos
    obtain ⟨ε₁, hε₁_pos, hε₁_le⟩ :=
      hgp_finset_min_choice Zgf hZne (fun x _ => |deriv g x|)
        (fun x hx => abs_pos.mpr (h_simple x ((hZgf_mem x).mp hx)))
    set ε₂ : ℝ := min ρ₀ (min (δ/8) 1) with hε₂_def
    have hε₂_pos : 0 < ε₂ := lt_min hρ₀_pos (lt_min (by linarith) (by norm_num))
    have hε₂_le_ρ₀ : ε₂ ≤ ρ₀ := min_le_left _ _
    have hε₂_le_δ8 : ε₂ ≤ δ/8 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hε₂_le_1 : ε₂ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
    have hderiv_lb : ∀ x_j ∈ Zgf, ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂),
        |deriv g x_j| / 2 ≤ |deriv g x| := by
      intro x_j hx_j x hx
      apply ρfun_spec x_j hx_j
      have hρ := hρ₀_le x_j hx_j
      simp only [Set.mem_Icc] at hx ⊢
      constructor <;> [linarith [hx.1, hε₂_le_ρ₀]; linarith [hx.2, hε₂_le_ρ₀]]
    set Kbig : Set ℝ := Set.Icc (b - δ) (b' + δ) \ Set.Ioo (μ_k - δ/2) (μ_k + δ/2) with hKbig_def
    have hKbig_compact : IsCompact Kbig := (isCompact_Icc).diff isOpen_Ioo
    have hμ_notin_Kbig : μ_k ∉ Kbig := by
      rw [hKbig_def]; intro hc; exact hc.2 ⟨by linarith, by linarith⟩
    set A : Set ℝ := K \ (⋃ x_j ∈ Zgf, Set.Ioo (x_j - ε₂) (x_j + ε₂)) with hA_def
    have hA_compact : IsCompact A := by
      rw [hA_def]
      refine hK_compact.diff ?_
      exact isOpen_biUnion (fun x_j _ => isOpen_Ioo)
    have hA_no_zeros : ∀ x ∈ A, g x ≠ 0 := by
      intro x hx hgx
      have hxZ : x ∈ Zgf := (hZgf_mem x).mpr hgx
      apply hx.2
      refine Set.mem_biUnion hxZ ?_
      exact ⟨by linarith [hε₂_pos], by linarith [hε₂_pos]⟩
    obtain ⟨g_lb, hg_lb_pos, hg_lb_spec⟩ :
        ∃ g_lb : ℝ, 0 < g_lb ∧ ∀ x ∈ A, g_lb ≤ |g x| := by
      by_cases hAne : A.Nonempty
      · exact SublemmaGLowerBoundOnA g hg_cont A hA_compact hAne hA_no_zeros
      · exact ⟨1, by norm_num, fun x hx => absurd ⟨x, hx⟩ hAne⟩
    obtain ⟨v_th1, hv_th1_pos, hv_th1_spec⟩ :=
      SublemmaSmallPerturbationDerivOnZeroNbhds μ_k a_k hak Kbig hKbig_compact hμ_notin_Kbig
        (ε₁/2) (by linarith)
    obtain ⟨v_th2, hv_th2_pos, hv_th2_spec⟩ :=
      SublemmaSmallPerturbationOnZeroNbhds μ_k a_k hak Kbig hKbig_compact hμ_notin_Kbig
        g_lb hg_lb_pos
    refine ⟨min v_th1 v_th2, lt_min hv_th1_pos hv_th2_pos, ?_⟩
    intro v hv hv_le
    have hv_le1 : v ≤ v_th1 := le_trans hv_le (min_le_left _ _)
    have hv_le2 : v ≤ v_th2 := le_trans hv_le (min_le_right _ _)
    set G : GaussianPDF := ⟨μ_k, v, hv⟩ with hG_def
    set p : ℝ → ℝ := fun x => a_k * G.density x with hp_def
    set h : ℝ → ℝ := fun x => g x + p x with hh_def
    have hp_C1 : ContDiff ℝ 1 p := by
      rw [hp_def]
      show ContDiff ℝ 1 (fun x => a_k * ((1 / Real.sqrt (2 * Real.pi * G.varSq))
        * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))))
      fun_prop
    have hderiv_p_eq : ∀ x, deriv p x =
        a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) * (-(x - μ_k) / v) := by
      intro x
      have hdac : deriv p x = a_k * deriv G.density x := by
        rw [hp_def]; exact deriv_const_mul a_k ((hgp_density_differentiable G) x)
      rw [hdac, hgp_density_deriv_eq G]
      show a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) * (-(x - μ_k) / v)) = _
      ring
    have hderiv_p_bd : ∀ x ∈ Kbig, |deriv p x| < ε₁ / 2 := by
      intro x hx
      rw [hderiv_p_eq x]
      exact hv_th1_spec v hv hv_le1 x hx
    have hp_bd : ∀ x ∈ Kbig, |p x| < g_lb := by
      intro x hx
      have hspec : |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
              Real.exp (-(x - μ_k)^2 / (2 * v))| < g_lb := hv_th2_spec v hv hv_le2 x hx
      have heq : p x
          = a_k * (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v)) := by
        rw [hp_def]
        show a_k * G.density x = _
        rw [GaussianPDF.density_eq]
        show a_k * ((1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v))) = _
        ring
      rw [heq]; exact hspec
    have hnbhd_sub_Kbig : ∀ x_j : ℝ, ∀ w ∈ K, |w - x_j| ≤ ε₂ →
        Set.Icc (x_j - ε₂) (x_j + ε₂) ⊆ Kbig := by
      intro x_j w hwK hw z hz
      simp only [Set.mem_Icc] at hz
      obtain ⟨hwb1, hwb2⟩ := hwK.1
      have hwμ : w ≤ μ_k - δ ∨ μ_k + δ ≤ w := by
        have hnot : ¬ (μ_k - δ < w ∧ w < μ_k + δ) := by
          intro hc; exact hwK.2 (Set.mem_Ioo.mpr hc)
        push_neg at hnot
        rcases le_or_gt w (μ_k - δ) with h | h
        · exact Or.inl h
        · exact Or.inr (hnot h)
      have hwx : |w - x_j| ≤ ε₂ := hw
      rw [abs_le] at hwx
      have hz_w_lo : w - 2*ε₂ ≤ z := by linarith [hz.1, hwx.1, hwx.2]
      have hz_w_hi : z ≤ w + 2*ε₂ := by linarith [hz.2, hwx.1, hwx.2]
      have h2ε : 2 * ε₂ ≤ δ/4 := by linarith [hε₂_le_δ8]
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      simp only [Set.mem_Ioo, not_and, not_lt]
      intro _
      rcases hwμ with hlo | hhi
      · linarith
      · linarith
    have hK_sub_Kbig : K ⊆ Kbig := by
      intro w hwK
      obtain ⟨hwb1, hwb2⟩ := hwK.1
      have hwμ : w ≤ μ_k - δ ∨ μ_k + δ ≤ w := by
        have hnot : ¬ (μ_k - δ < w ∧ w < μ_k + δ) := fun hc => hwK.2 (Set.mem_Ioo.mpr hc)
        push_neg at hnot
        rcases le_or_gt w (μ_k - δ) with hh | hh
        · exact Or.inl hh
        · exact Or.inr (hnot hh)
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      simp only [Set.mem_Ioo, not_and, not_lt]
      intro _
      rcases hwμ with hlo | hhi <;> linarith
    have hA_sub_Kbig : A ⊆ Kbig := fun x hx => hK_sub_Kbig hx.1
    set S : Set ℝ := zeroSet h ∩ K with hS_def
    have hgoal : S.encard ≤ (N : ℕ∞) := by
      have hcover : S ⊆ ⋃ x_j ∈ Zgf, Set.Icc (x_j - ε₂) (x_j + ε₂) := by
        intro y hy
        have hyh : h y = 0 := hy.1
        have hyK : y ∈ K := hy.2
        by_contra hcon
        have hyA : y ∈ A := by
          refine ⟨hyK, ?_⟩
          intro hmem
          rw [Set.mem_iUnion₂] at hmem
          obtain ⟨x_j, hx_j, hyx⟩ := hmem
          apply hcon
          rw [Set.mem_iUnion₂]
          exact ⟨x_j, hx_j, Set.Ioo_subset_Icc_self hyx⟩
        have hglb : g_lb ≤ |g y| := hg_lb_spec y hyA
        have hpb : |p y| < g_lb := hp_bd y (hA_sub_Kbig hyA)
        have : g y = - p y := by
          have : g y + p y = 0 := hyh
          linarith
        rw [this, abs_neg] at hglb
        linarith
      have hsub : ∀ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂)).Subsingleton := by
        intro x_j hx_j y₁ hy₁ y₂ hy₂
        obtain ⟨⟨hy1h, hy1K⟩, hy1I⟩ := hy₁
        obtain ⟨⟨hy2h, hy2K⟩, hy2I⟩ := hy₂
        have hy1x : |y₁ - x_j| ≤ ε₂ := by
          rw [abs_le]; simp only [Set.mem_Icc] at hy1I
          exact ⟨by linarith [hy1I.1], by linarith [hy1I.2]⟩
        have hI_sub : Set.Icc (x_j - ε₂) (x_j + ε₂) ⊆ Kbig :=
          hnbhd_sub_Kbig x_j y₁ hy1K hy1x
        have hsimple_xj : deriv g x_j ≠ 0 := h_simple x_j ((hZgf_mem x_j).mp hx_j)
        have hε1_le : ε₁ ≤ |deriv g x_j| := hε₁_le x_j hx_j
        have hdb : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂),
            |deriv g x_j| / 2 ≤ |deriv g x| := hderiv_lb x_j hx_j
        have hpdb : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), |deriv p x| < |deriv g x_j| / 2 := by
          intro x hx
          have h1 : |deriv p x| < ε₁ / 2 := hderiv_p_bd x (hI_sub hx)
          linarith
        exact hgp_R3Local g hg_C1 x_j hsimple_xj ε₂ hε₂_pos hdb p hp_C1 hpdb
          y₁ y₂ hy1I hy2I hy1h hy2h
      have hSeq : S = ⋃ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂)) := by
        rw [← Set.inter_iUnion₂]; exact (Set.inter_eq_left.mpr hcover).symm
      rw [hSeq]
      calc (⋃ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂))).encard
          ≤ ∑ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂)).encard :=
            Finset.set_encard_biUnion_le Zgf _
        _ ≤ ∑ _x_j ∈ Zgf, (1 : ℕ∞) :=
            Finset.sum_le_sum (fun x_j hx_j =>
              Set.encard_le_one_iff_subsingleton.mpr (hsub x_j hx_j))
        _ = (Zgf.card : ℕ∞) := by simp
        _ ≤ (N : ℕ∞) := by exact_mod_cast hZgf_card
    exact hgoal
  · -- g has no zeros: |g| ≥ g_lb on K, perturbation small ⇒ no h-zeros.
    rw [Finset.not_nonempty_iff_eq_empty] at hZne
    have hg_nozero : ∀ x : ℝ, g x ≠ 0 := by
      intro x hgx
      have : x ∈ Zgf := (hZgf_mem x).mpr hgx
      rw [hZne] at this; exact absurd this (Finset.notMem_empty x)
    have hμ_notin_K : μ_k ∉ K := by
      rw [hK_def]; intro hc; exact hc.2 ⟨by linarith, by linarith⟩
    obtain ⟨g_lb, hg_lb_pos, hg_lb_spec⟩ :
        ∃ g_lb : ℝ, 0 < g_lb ∧ ∀ x ∈ K, g_lb ≤ |g x| := by
      by_cases hKne : K.Nonempty
      · exact SublemmaGLowerBoundOnA g hg_cont K hK_compact hKne (fun x _ => hg_nozero x)
      · exact ⟨1, by norm_num, fun x hx => absurd ⟨x, hx⟩ hKne⟩
    obtain ⟨v_th2, hv_th2_pos, hv_th2_spec⟩ :=
      SublemmaSmallPerturbationOnZeroNbhds μ_k a_k hak K hK_compact hμ_notin_K g_lb hg_lb_pos
    refine ⟨v_th2, hv_th2_pos, ?_⟩
    intro v hv hv_le
    set G : GaussianPDF := ⟨μ_k, v, hv⟩ with hG_def
    have hSempty : (zeroSet (fun x => g x + a_k * G.density x) ∩ K) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro y hy
      obtain ⟨hyh, hyK⟩ := hy
      have hyh0 : g y + a_k * G.density y = 0 := hyh
      have hglb : g_lb ≤ |g y| := hg_lb_spec y hyK
      have hpb : |a_k * G.density y| < g_lb := by
        have hspec : |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
              Real.exp (-(y - μ_k)^2 / (2 * v))| < g_lb := hv_th2_spec v hv hv_le y hyK
        have heq : a_k * G.density y
            = a_k * (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(y - μ_k)^2 / (2 * v)) := by
          rw [GaussianPDF.density_eq]
          show a_k * ((1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(y - μ_k)^2 / (2 * v))) = _
          ring
        rw [heq]; exact hspec
      have : g y = - (a_k * G.density y) := by linarith
      rw [this, abs_neg] at hglb
      linarith
    rw [hSempty, Set.encard_empty]
    exact zero_le _

/-- **Parametrized region (b)** (route (ii)): the same conclusion as
`HurwitzGaussianPerturbationSimpleZeroPreservation`, but with every floor / region /
threshold supplied EXTERNALLY rather than computed internally.  This exposes a
`c`-independent threshold `min v_th1 v_th2` so that a band-uniform caller can feed
banked uniform floors and obtain a single threshold valid for the whole band.

The combinatorial core (zero-cover + `hgp_R3Local` machinery) is `c`-independent given:

* `Kbig` — the outer perturbation region `Icc (b-δ) (b'+δ) \ Ioo (μ_k-δ/2) (μ_k+δ/2)`
  (supplied as `hKbig_eq`);
* `ε₂` — the cover radius for the zero neighbourhoods, with `ε₂ ≤ δ/8`, `ε₂ ≤ 1`, and the
  derivative-continuity fact `hderiv_lb` (`|deriv g x_j|/2 ≤ |deriv g x|` on each
  `Icc (x_j - ε₂) (x_j + ε₂)`), all of which depend only on `g` (not on any band slice);
* the external derivative floor `ε₁` with `hε₁_le : ε₁ ≤ |deriv g x_j|` at every zero;
* the external value floor `g_lb` with `hg_lb_spec` on the zero-free part
  `(Icc b b' \ Ioo (μ_k-δ) (μ_k+δ)) \ ⋃_{g x_j = 0} Ioo (x_j-ε₂) (x_j+ε₂)`;
* the two perturbation-decay thresholds `v_th1, v_th2` (from
  `SublemmaSmallPerturbationDerivOnZeroNbhds` with floor `ε₁/2` and
  `SublemmaSmallPerturbationOnZeroNbhds` with floor `g_lb`), supplied with their specs.

The returned threshold is exactly `min v_th1 v_th2`, built from the EXTERNAL floors. -/
theorem HurwitzGaussianPerturbationSimpleZeroPreservation_param
    (g : ℝ → ℝ)
    (hg_an : AnalyticOnNhd ℝ g Set.univ)
    (N : ℕ)
    (hN : Workspace.Types.ZeroCount.hasAtMostNZeros g N)
    (h_simple : ∀ x : ℝ, g x = 0 → deriv g x ≠ 0)
    (b b' : ℝ) (hbb' : b < b')
    (a_k : ℝ) (hak : a_k ≠ 0)
    (μ_k : ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    -- external outer region
    (Kbig : Set ℝ)
    (hKbig_eq : Kbig = Set.Icc (b - δ) (b' + δ) \ Set.Ioo (μ_k - δ/2) (μ_k + δ/2))
    -- external cover radius for the zero neighbourhoods
    (ε₂ : ℝ) (hε₂_pos : 0 < ε₂) (hε₂_le_δ8 : ε₂ ≤ δ/8) (hε₂_le_1 : ε₂ ≤ 1)
    (hderiv_lb : ∀ x_j : ℝ, g x_j = 0 →
        ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), |deriv g x_j| / 2 ≤ |deriv g x|)
    -- external derivative floor at the zeros
    (ε₁ : ℝ) (hε₁_pos : 0 < ε₁)
    (hε₁_le : ∀ x_j : ℝ, g x_j = 0 → ε₁ ≤ |deriv g x_j|)
    -- external value floor on the zero-free part of the region
    (g_lb : ℝ) (hg_lb_pos : 0 < g_lb)
    (hg_lb_spec : ∀ x ∈ (Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ)) \
        (⋃ x_j ∈ {y : ℝ | g y = 0}, Set.Ioo (x_j - ε₂) (x_j + ε₂)), g_lb ≤ |g x|)
    -- the two externally-supplied perturbation-decay thresholds
    (v_th1 : ℝ) (hv_th1_pos : 0 < v_th1)
    (hv_th1_spec : ∀ v : ℝ, 0 < v → v ≤ v_th1 → ∀ x ∈ Kbig,
        |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) * (-(x - μ_k) / v)| < ε₁ / 2)
    (v_th2 : ℝ) (hv_th2_pos : 0 < v_th2)
    (hv_th2_spec : ∀ v : ℝ, 0 < v → v ≤ v_th2 → ∀ x ∈ Kbig,
        |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v))| < g_lb) :
    ∀ (v : ℝ) (hv : 0 < v), v ≤ min v_th1 v_th2 →
      (Workspace.Types.ZeroCount.zeroSet
          (fun x => g x +
            a_k *
              Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x)
        ∩ (Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ))).encard
        ≤ (N : ℕ∞) := by
  -- g is C¹ and its deriv is continuous (analytic ⇒ smooth).
  have hg_cont : Continuous g := hg_an.continuous
  have hg_C1 : ContDiff ℝ 1 g := by
    have h := hg_an.contDiff (n := (1 : ℕ∞))
    exact h
  have hderivg_cont : Continuous (deriv g) := hg_C1.continuous_deriv_one
  -- The region K.
  set K : Set ℝ := Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ) with hK_def
  have hK_compact : IsCompact K := (isCompact_Icc).diff isOpen_Ioo
  -- Zeros of g form a finite set.
  have hZg_fin : (zeroSet g).Finite := by
    have : (zeroSet g).encard ≤ (N : ℕ∞) := hN
    exact Set.finite_of_encard_le_coe this
  set Zgf : Finset ℝ := hZg_fin.toFinset with hZgf_def
  have hZgf_mem : ∀ x, x ∈ Zgf ↔ g x = 0 := by
    intro x; rw [hZgf_def, Set.Finite.mem_toFinset]; rfl
  have hZgf_card : Zgf.card ≤ N := by
    have hh : (zeroSet g).encard ≤ (N : ℕ∞) := hN
    have he : (zeroSet g).encard = (Zgf.card : ℕ∞) := by
      rw [hZgf_def, Set.Finite.encard_eq_coe_toFinset_card hZg_fin]
    rw [he] at hh
    exact_mod_cast hh
  classical
  -- Properties of the external region `Kbig`.
  have hKbig_compact : IsCompact Kbig := by
    rw [hKbig_eq]; exact (isCompact_Icc).diff isOpen_Ioo
  have hμ_notin_Kbig : μ_k ∉ Kbig := by
    rw [hKbig_eq]; intro hc; exact hc.2 ⟨by linarith, by linarith⟩
  -- `hderiv_lb` restated over the zero Finset.
  have hderiv_lb' : ∀ x_j ∈ Zgf, ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂),
      |deriv g x_j| / 2 ≤ |deriv g x| := by
    intro x_j hx_j x hx
    exact hderiv_lb x_j ((hZgf_mem x_j).mp hx_j) x hx
  -- `hε₁_le` restated over the zero Finset.
  have hε₁_le' : ∀ x_j ∈ Zgf, ε₁ ≤ |deriv g x_j| := by
    intro x_j hx_j; exact hε₁_le x_j ((hZgf_mem x_j).mp hx_j)
  -- The zero-free region `A`.
  set A : Set ℝ := K \ (⋃ x_j ∈ Zgf, Set.Ioo (x_j - ε₂) (x_j + ε₂)) with hA_def
  -- `hg_lb_spec` restated over `A` (the external floor uses the zero-set predicate, while
  -- `A` excludes neighbourhoods over the zero Finset; these agree by `hZgf_mem`).
  have hg_lb_specA : ∀ x ∈ A, g_lb ≤ |g x| := by
    intro x hx
    apply hg_lb_spec
    refine ⟨hx.1, ?_⟩
    intro hmem
    apply hx.2
    rw [Set.mem_iUnion₂] at hmem ⊢
    obtain ⟨x_j, hx_j_pred, hxmem⟩ := hmem
    exact ⟨x_j, (hZgf_mem x_j).mpr hx_j_pred, hxmem⟩
  -- The genuine band-uniform threshold (built from the EXTERNAL floors).
  intro v hv hv_le
  have hv_le1 : v ≤ v_th1 := le_trans hv_le (min_le_left _ _)
  have hv_le2 : v ≤ v_th2 := le_trans hv_le (min_le_right _ _)
  set G : GaussianPDF := ⟨μ_k, v, hv⟩ with hG_def
  set p : ℝ → ℝ := fun x => a_k * G.density x with hp_def
  set h : ℝ → ℝ := fun x => g x + p x with hh_def
  have hp_C1 : ContDiff ℝ 1 p := by
    rw [hp_def]
    show ContDiff ℝ 1 (fun x => a_k * ((1 / Real.sqrt (2 * Real.pi * G.varSq))
      * Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq))))
    fun_prop
  have hderiv_p_eq : ∀ x, deriv p x =
      a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
        Real.exp (-(x - μ_k)^2 / (2 * v)) * (-(x - μ_k) / v) := by
    intro x
    have hdac : deriv p x = a_k * deriv G.density x := by
      rw [hp_def]; exact deriv_const_mul a_k ((hgp_density_differentiable G) x)
    rw [hdac, hgp_density_deriv_eq G]
    show a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
        Real.exp (-(x - μ_k)^2 / (2 * v)) * (-(x - μ_k) / v)) = _
    ring
  have hderiv_p_bd : ∀ x ∈ Kbig, |deriv p x| < ε₁ / 2 := by
    intro x hx
    rw [hderiv_p_eq x]
    exact hv_th1_spec v hv hv_le1 x hx
  have hp_bd : ∀ x ∈ Kbig, |p x| < g_lb := by
    intro x hx
    have hspec : |a_k * (1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(x - μ_k)^2 / (2 * v))| < g_lb := hv_th2_spec v hv hv_le2 x hx
    have heq : p x
        = a_k * (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v)) := by
      rw [hp_def]
      show a_k * G.density x = _
      rw [GaussianPDF.density_eq]
      show a_k * ((1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v))) = _
      ring
    rw [heq]; exact hspec
  have hnbhd_sub_Kbig : ∀ x_j : ℝ, ∀ w ∈ K, |w - x_j| ≤ ε₂ →
      Set.Icc (x_j - ε₂) (x_j + ε₂) ⊆ Kbig := by
    intro x_j w hwK hw z hz
    rw [hKbig_eq]
    simp only [Set.mem_Icc] at hz
    obtain ⟨hwb1, hwb2⟩ := hwK.1
    have hwμ : w ≤ μ_k - δ ∨ μ_k + δ ≤ w := by
      have hnot : ¬ (μ_k - δ < w ∧ w < μ_k + δ) := by
        intro hc; exact hwK.2 (Set.mem_Ioo.mpr hc)
      push_neg at hnot
      rcases le_or_gt w (μ_k - δ) with h | h
      · exact Or.inl h
      · exact Or.inr (hnot h)
    have hwx : |w - x_j| ≤ ε₂ := hw
    rw [abs_le] at hwx
    have hz_w_lo : w - 2*ε₂ ≤ z := by linarith [hz.1, hwx.1, hwx.2]
    have hz_w_hi : z ≤ w + 2*ε₂ := by linarith [hz.2, hwx.1, hwx.2]
    have h2ε : 2 * ε₂ ≤ δ/4 := by linarith [hε₂_le_δ8]
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    simp only [Set.mem_Ioo, not_and, not_lt]
    intro _
    rcases hwμ with hlo | hhi
    · linarith
    · linarith
  have hK_sub_Kbig : K ⊆ Kbig := by
    intro w hwK
    rw [hKbig_eq]
    obtain ⟨hwb1, hwb2⟩ := hwK.1
    have hwμ : w ≤ μ_k - δ ∨ μ_k + δ ≤ w := by
      have hnot : ¬ (μ_k - δ < w ∧ w < μ_k + δ) := fun hc => hwK.2 (Set.mem_Ioo.mpr hc)
      push_neg at hnot
      rcases le_or_gt w (μ_k - δ) with hh | hh
      · exact Or.inl hh
      · exact Or.inr (hnot hh)
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    simp only [Set.mem_Ioo, not_and, not_lt]
    intro _
    rcases hwμ with hlo | hhi <;> linarith
  have hA_sub_Kbig : A ⊆ Kbig := fun x hx => hK_sub_Kbig hx.1
  set S : Set ℝ := zeroSet h ∩ K with hS_def
  have hgoal : S.encard ≤ (N : ℕ∞) := by
    have hcover : S ⊆ ⋃ x_j ∈ Zgf, Set.Icc (x_j - ε₂) (x_j + ε₂) := by
      intro y hy
      have hyh : h y = 0 := hy.1
      have hyK : y ∈ K := hy.2
      by_contra hcon
      have hyA : y ∈ A := by
        refine ⟨hyK, ?_⟩
        intro hmem
        rw [Set.mem_iUnion₂] at hmem
        obtain ⟨x_j, hx_j, hyx⟩ := hmem
        apply hcon
        rw [Set.mem_iUnion₂]
        exact ⟨x_j, hx_j, Set.Ioo_subset_Icc_self hyx⟩
      have hglb : g_lb ≤ |g y| := hg_lb_specA y hyA
      have hpb : |p y| < g_lb := hp_bd y (hA_sub_Kbig hyA)
      have : g y = - p y := by
        have : g y + p y = 0 := hyh
        linarith
      rw [this, abs_neg] at hglb
      linarith
    have hsub : ∀ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂)).Subsingleton := by
      intro x_j hx_j y₁ hy₁ y₂ hy₂
      obtain ⟨⟨hy1h, hy1K⟩, hy1I⟩ := hy₁
      obtain ⟨⟨hy2h, hy2K⟩, hy2I⟩ := hy₂
      have hy1x : |y₁ - x_j| ≤ ε₂ := by
        rw [abs_le]; simp only [Set.mem_Icc] at hy1I
        exact ⟨by linarith [hy1I.1], by linarith [hy1I.2]⟩
      have hI_sub : Set.Icc (x_j - ε₂) (x_j + ε₂) ⊆ Kbig :=
        hnbhd_sub_Kbig x_j y₁ hy1K hy1x
      have hsimple_xj : deriv g x_j ≠ 0 := h_simple x_j ((hZgf_mem x_j).mp hx_j)
      have hε1_le : ε₁ ≤ |deriv g x_j| := hε₁_le' x_j hx_j
      have hdb : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂),
          |deriv g x_j| / 2 ≤ |deriv g x| := hderiv_lb' x_j hx_j
      have hpdb : ∀ x ∈ Set.Icc (x_j - ε₂) (x_j + ε₂), |deriv p x| < |deriv g x_j| / 2 := by
        intro x hx
        have h1 : |deriv p x| < ε₁ / 2 := hderiv_p_bd x (hI_sub hx)
        linarith
      exact hgp_R3Local g hg_C1 x_j hsimple_xj ε₂ hε₂_pos hdb p hp_C1 hpdb
        y₁ y₂ hy1I hy2I hy1h hy2h
    have hSeq : S = ⋃ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂)) := by
      rw [← Set.inter_iUnion₂]; exact (Set.inter_eq_left.mpr hcover).symm
    rw [hSeq]
    calc (⋃ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂))).encard
        ≤ ∑ x_j ∈ Zgf, (S ∩ Set.Icc (x_j - ε₂) (x_j + ε₂)).encard :=
          Finset.set_encard_biUnion_le Zgf _
      _ ≤ ∑ _x_j ∈ Zgf, (1 : ℕ∞) :=
          Finset.sum_le_sum (fun x_j hx_j =>
            Set.encard_le_one_iff_subsingleton.mpr (hsub x_j hx_j))
      _ = (Zgf.card : ℕ∞) := by simp
      _ ≤ (N : ℕ∞) := by exact_mod_cast hZgf_card
  exact hgoal

end Workspace.ProofLemmas
