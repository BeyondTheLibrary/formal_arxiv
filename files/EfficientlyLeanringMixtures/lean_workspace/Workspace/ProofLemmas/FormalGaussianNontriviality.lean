import Mathlib
import Workspace.Types.ZeroCount

/-!
# FormalGaussianNontriviality

Step 0 (Moitra–Valiant §6.1) — nontriviality of a distinct-variance formal
Gaussian sum.

Let `k ≥ 1` and `a μ τ : Fin k → ℝ` with `τ i ≠ 0` for all `i`, the `τ i`
pairwise distinct, and some `a i₀ ≠ 0`. Then the bare-exponential formal
Gaussian sum
`g x = Σ_i a i · exp(-(x - μ i)² / (2 · τ i))`
is not identically zero.
-/

namespace Workspace.ProofLemmas

open Filter Asymptotics
open scoped Topology

/-- General two-term tail dominance: a single (mean-shifted) Gaussian term with
leading quadratic coefficient `-1/(2·τ₂)` is little-o (at `atTop`) of another
whose leading coefficient `-1/(2·τ₁)` is strictly larger.  Works for arbitrary
nonzero variances `τ₁ τ₂` (no positivity assumed). -/
private theorem gaussTerm_littleO_atTop
    (μ₁ μ₂ τ₁ τ₂ : ℝ) (hτ₁ : τ₁ ≠ 0) (hτ₂ : τ₂ ≠ 0)
    (hlead : -1 / (2 * τ₂) < -1 / (2 * τ₁)) :
    (fun x : ℝ => Real.exp (-(x - μ₂)^2 / (2 * τ₂))) =o[Filter.atTop]
      (fun x : ℝ => Real.exp (-(x - μ₁)^2 / (2 * τ₁))) := by
  set A : ℝ := (-1 / (2 * τ₂)) - (-1 / (2 * τ₁)) with hA
  have hA_neg : A < 0 := by rw [hA]; linarith
  have h2τ₁ : (2 * τ₁) ≠ 0 := by positivity
  have h2τ₂ : (2 * τ₂) ≠ 0 := by positivity
  -- The ratio equals exp of a quadratic with leading coefficient A < 0.
  set B : ℝ := μ₂ / τ₂ - μ₁ / τ₁ with hB
  set C : ℝ := -μ₂^2 / (2 * τ₂) + μ₁^2 / (2 * τ₁) with hC
  have ratio_eq : ∀ x : ℝ,
      Real.exp (-(x - μ₂)^2 / (2 * τ₂)) / Real.exp (-(x - μ₁)^2 / (2 * τ₁))
        = Real.exp (A * x^2 + B * x + C) := by
    intro x
    rw [← Real.exp_sub]
    congr 1
    rw [hA, hB, hC]
    field_simp
    ring
  -- The quadratic tends to -∞ at atTop (leading coeff A < 0).
  have h_atTop : Tendsto (fun x : ℝ => A * x^2 + B * x + C) atTop atBot := by
    have h1 : Tendsto (fun x : ℝ => A * x + B) atTop atBot :=
      (Filter.tendsto_id.const_mul_atTop_of_neg hA_neg).atBot_add tendsto_const_nhds
    have h2 : Tendsto (fun x : ℝ => x * (A * x + B)) atTop atBot :=
      Filter.tendsto_id.atTop_mul_atBot₀ h1
    have h3 : Tendsto (fun x : ℝ => x * (A * x + B) + C) atTop atBot :=
      h2.atBot_add tendsto_const_nhds
    apply h3.congr; intro x; ring
  have h_exp : Tendsto (fun x : ℝ => Real.exp (A * x^2 + B * x + C)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_atTop
  have hne : ∀ x : ℝ, Real.exp (-(x - μ₁)^2 / (2 * τ₁)) = 0 →
      Real.exp (-(x - μ₂)^2 / (2 * τ₂)) = 0 := fun x hx =>
    absurd hx (ne_of_gt (Real.exp_pos _))
  rw [Asymptotics.isLittleO_iff_tendsto hne]
  refine h_exp.congr ?_
  intro x; exact (ratio_eq x).symm

theorem FormalGaussianNontriviality
    (k : ℕ) (hk : 1 ≤ k)
    (a : Fin k → ℝ)
    (μ : Fin k → ℝ)
    (τ_sq : Fin k → ℝ)
    (h_τ_nonzero : ∀ i : Fin k, τ_sq i ≠ 0)
    (h_τ_distinct : ∀ i j : Fin k, i ≠ j → τ_sq i ≠ τ_sq j)
    (h_a_nonzero : ∃ i : Fin k, a i ≠ 0) :
    ∃ x : ℝ,
      (Finset.univ : Finset (Fin k)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) ≠ 0 := by
  classical
  -- The leading quadratic coefficient of term i.
  set α : Fin k → ℝ := fun i => -1 / (2 * τ_sq i) with hα
  -- α is injective: distinct τ ⇒ distinct α.
  have hα_inj : ∀ i j : Fin k, α i = α j → i = j := by
    intro i j hij
    by_contra hne
    have h2i : (2 * τ_sq i) ≠ 0 := by
      have := h_τ_nonzero i; positivity
    have h2j : (2 * τ_sq j) ≠ 0 := by
      have := h_τ_nonzero j; positivity
    have : τ_sq i = τ_sq j := by
      have hij' : (-1 : ℝ) / (2 * τ_sq i) = -1 / (2 * τ_sq j) := hij
      rw [div_eq_div_iff h2i h2j] at hij'
      -- hij' : -1 * (2 * τ_sq j) = -1 * (2 * τ_sq i)
      linarith
    exact h_τ_distinct i j hne this
  -- Index set with nonzero coefficients (nonempty).
  set T : Finset (Fin k) := Finset.univ.filter (fun i => a i ≠ 0) with hT
  have hT_ne : T.Nonempty := by
    obtain ⟨i, hi⟩ := h_a_nonzero
    exact ⟨i, by simp [hT, hi]⟩
  -- Pick i₀ ∈ T maximizing α.
  obtain ⟨i₀, hi₀_mem, hi₀_max⟩ := T.exists_max_image α hT_ne
  have ha₀ : a i₀ ≠ 0 := by
    have := hi₀_mem; rw [hT, Finset.mem_filter] at this; exact this.2
  -- Dominant term.
  set D : ℝ → ℝ := fun x => Real.exp (-(x - μ i₀)^2 / (2 * τ_sq i₀)) with hD
  have hD_pos : ∀ x, 0 < D x := fun x => Real.exp_pos _
  -- For every i ≠ i₀, the i-th term is o(D) at atTop.
  have h_term_o : ∀ i ∈ (Finset.univ.erase i₀),
      (fun x => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) =o[atTop] D := by
    intro i hi
    have hi_ne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    by_cases hai : a i = 0
    · simp only [hai, zero_mul]
      exact Asymptotics.isLittleO_zero _ _
    · -- a i ≠ 0 ⇒ i ∈ T ⇒ α i ≤ α i₀, and strict since i ≠ i₀.
      have hi_T : i ∈ T := by rw [hT, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hai⟩
      have hle : α i ≤ α i₀ := hi₀_max i hi_T
      have hlt : α i < α i₀ := lt_of_le_of_ne hle (fun h => hi_ne (hα_inj i i₀ h))
      -- gaussTerm dominance, then const-mul.
      have hdom : (fun x : ℝ => Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) =o[atTop] D :=
        gaussTerm_littleO_atTop (μ i₀) (μ i) (τ_sq i₀) (τ_sq i)
          (h_τ_nonzero i₀) (h_τ_nonzero i) hlt
      exact hdom.const_mul_left (a i)
  -- Sum minus dominant term = sum over erase, which is o(D).
  have h_rest_o :
      (fun x => (Finset.univ : Finset (Fin k)).sum
          (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i)))
        - a i₀ * D x) =o[atTop] D := by
    have hsum_split : ∀ x,
        (Finset.univ : Finset (Fin k)).sum
            (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i)))
          - a i₀ * D x
        = (Finset.univ.erase i₀).sum
            (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) := by
      intro x
      rw [← Finset.add_sum_erase Finset.univ
            (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) (Finset.mem_univ i₀)]
      simp [hD]
    refine (Asymptotics.IsLittleO.sum h_term_o).congr' ?_ (by rfl)
    filter_upwards with x
    exact (hsum_split x).symm
  -- Eventually |sum - a₀·D| ≤ (|a₀|/2)·D, hence sum ≠ 0.
  have ha₀_pos : 0 < |a i₀| / 2 := by positivity
  have h_bound := h_rest_o.def ha₀_pos
  have h_event : ∀ᶠ x in atTop,
      (Finset.univ : Finset (Fin k)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) ≠ 0 := by
    filter_upwards [h_bound] with x hx
    have hDx : 0 < D x := hD_pos x
    -- hx : ‖sum - a₀ D‖ ≤ (|a₀|/2) * ‖D‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hDx] at hx
    set S : ℝ := (Finset.univ : Finset (Fin k)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) with hS
    -- |a₀ D| - |S| ≤ |S - a₀ D| ... use reverse triangle.
    have htri : |a i₀ * D x| - |S| ≤ |S - a i₀ * D x| := by
      have := abs_sub_abs_le_abs_sub (a i₀ * D x) S
      rw [abs_sub_comm (a i₀ * D x) S] at this
      linarith [this]
    have habs_aD : |a i₀ * D x| = |a i₀| * D x := by
      rw [abs_mul, abs_of_pos hDx]
    intro hS0
    rw [hS0, abs_zero] at htri
    rw [hS0] at hx
    -- hx : |0 - a₀ D| ≤ (|a₀|/2) D ; |0 - a₀ D| = |a₀| D
    rw [zero_sub, abs_neg, habs_aD] at hx
    have : |a i₀| * D x ≤ |a i₀| / 2 * D x := hx
    have hcontra : |a i₀| ≤ |a i₀| / 2 :=
      le_of_mul_le_mul_right (by linarith [this]) hDx
    have : (0:ℝ) < |a i₀| := abs_pos.mpr ha₀
    linarith
  obtain ⟨x, hx⟩ := h_event.exists
  exact ⟨x, hx⟩

end Workspace.ProofLemmas
