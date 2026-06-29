import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope

/-!
# Band-uniform Gaussian-tail envelope for the normalized convolution family

This file closes "piece (1)" of region (a) of the §6.1 add-Gaussian step: a SINGLE
two-sided Gaussian-tail envelope `(b, b', a, a', s, s')` that dominates EVERY slice
`fFamU S c` of the normalized convolution family uniformly over the band
`c ∈ (0, c_max]`.

The per-slice fact `SublemmaTailDominationSound (heatShift S c)` already gives, for
each `c`, an envelope — but with thresholds chosen per-slice (`exists_forall_of_atTop`),
hence not uniform in `c`. Here we re-run the dominant-component construction of
`SublemmaTailDominationSoundCore` while keeping the constants UNIFORM:

* The dominant Gaussian `Gdom` of the *base* `S` is selected once. Adding the same `c`
  to every variance preserves the lexicographic `(varSq, mean)` order, so the dominant
  of every slice `heatShift S c` is `shiftVarG Gdom c` (variance `Gdom.varSq + c`, same
  mean), and the dominant-group coefficient sum `A := topCoeffSum Gdom S` is `c`-stable
  (heat flow maps the identical-Gaussian top group to an identical-Gaussian group with
  the same coefficients).
* The envelope variance `s := Gdom.varSq / 2` is fixed and strictly below every slice's
  dominant variance `Gdom.varSq + c` (`c > 0`), so the envelope decays strictly faster
  than the dominant term of every slice.
* Uniformity in `c` comes from the fact that the ratio
  `exp(-x²/(2s)) / exp(-(x-μ)²/(2(V+c)))` is `exp` of a quadratic whose leading
  coefficient `-1/(2s) + 1/(2(V+c)) ≤ -1/(2V) < 0` is bounded away from `0` UNIFORMLY
  over `c ∈ [0, c_max]` (and the same holds for each strictly-below residual term vs.
  the dominant). A quadratic with uniformly-negative leading coefficient and bounded
  lower-order terms is eventually small with a SINGLE threshold.

The headline result is `convFamilyUniformEnvelope`, matching the shape of
`convFamily_uniform_envelope_on_band` in `ConvSmallPreservesSimpleAndEnvelope.lean`.
-/

namespace Workspace.ProofLemmas

open Filter Asymptotics
open scoped Topology
open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution

set_option maxHeartbeats 4000000

/-! ## Uniform quadratic-tail lemma

A quadratic `α x² + β x + γ` whose leading coefficient is `≤ -q < 0` and whose
lower-order coefficients are bounded (`|β| ≤ B`, `|γ| ≤ C`) is, for `x` beyond a
single threshold depending only on `(q, B, C)`, bounded above by any prescribed
negative target. We use a clean explicit threshold. -/

/-- For `x ≥ T` with `T ≥ 1` large enough, a quadratic with leading coeff `≤ -q < 0`,
`|β| ≤ B`, `|γ| ≤ C` is `≤ -M`. Concretely we show: if `0 < q`, `0 ≤ B`, `0 ≤ C`,
`0 ≤ M`, then for `x ≥ (B + C + M + 1) / q + 1` (and `x ≥ 1`) the bound holds. -/
private theorem quad_le_neg_of_large
    (α β γ q B C M : ℝ)
    (hα : α ≤ -q) (hq : 0 < q) (hβ : |β| ≤ B) (hγ : |γ| ≤ C)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (x : ℝ) (hx1 : 1 ≤ x) (hxT : (B + C + M + 1) / q + 1 ≤ x) :
    α * x ^ 2 + β * x + γ ≤ -M := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) hβ
  -- bound the linear and constant parts
  have hβx : β * x ≤ B * x := by
    have : β ≤ B := le_trans (le_abs_self _) hβ
    nlinarith [hx1]
  have hγle : γ ≤ C := le_trans (le_abs_self _) hγ
  -- α x² ≤ -q x²
  have hαx : α * x ^ 2 ≤ -q * x ^ 2 := by
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg _
    nlinarith [hα, hx2]
  -- so the quadratic ≤ -q x² + B x + C
  have hstep : α * x ^ 2 + β * x + γ ≤ -q * x ^ 2 + B * x + C := by
    linarith [hαx, hβx, hγle]
  -- now show -q x² + B x + C ≤ -M for x ≥ T
  -- x ≥ (B+C+M+1)/q + 1, so q*x ≥ B+C+M+1 + q ≥ B+C+M+1
  have hqx : B + C + M + 1 ≤ q * x := by
    have hT : (B + C + M + 1) / q ≤ x - 1 := by linarith [hxT]
    have := (div_le_iff₀ hq).mp hT
    nlinarith [this, hq]
  -- q x² = (q x) * x ≥ (B+C+M+1) * x ≥ B*x + (C+M+1) (since x ≥ 1)
  have hqx2 : (B + C + M + 1) * x ≤ q * x ^ 2 := by
    have hxnn : 0 ≤ x := by linarith
    nlinarith [hqx, hxnn]
  -- (B+C+M+1)*x ≥ B*x + (C+M+1) since (C+M+1)*x ≥ C+M+1 (x≥1, C+M+1≥0)
  have hlow : B * x + (C + M + 1) ≤ (B + C + M + 1) * x := by
    have : (C + M + 1) ≤ (C + M + 1) * x := by nlinarith [hx1, hC, hM]
    nlinarith [this]
  nlinarith [hstep, hqx2, hlow]

/-- Linear-leading analogue: `β x + γ ≤ -M` for `x` beyond a single threshold, when
`β ≤ -q < 0` and `|γ| ≤ C`. -/
private theorem lin_le_neg_of_large
    (β γ q C M : ℝ)
    (hβ : β ≤ -q) (hq : 0 < q) (hγ : |γ| ≤ C)
    (hC : 0 ≤ C) (hM : 0 ≤ M)
    (x : ℝ) (hx1 : 1 ≤ x) (hxT : (C + M + 1) / q + 1 ≤ x) :
    β * x + γ ≤ -M := by
  have hγle : γ ≤ C := le_trans (le_abs_self _) hγ
  have hβx : β * x ≤ -q * x := by
    have hxnn : 0 ≤ x := by linarith
    nlinarith [hβ, hxnn]
  have hqx : C + M + 1 ≤ q * x := by
    have hT : (C + M + 1) / q ≤ x - 1 := by linarith [hxT]
    have := (div_le_iff₀ hq).mp hT
    nlinarith [this, hq]
  nlinarith [hβx, hγle, hqx]

/-! ## The c-shifted normalizing/exponential factors

We work directly with the base combination `S` and a chosen dominant Gaussian `Gdom`.
For `c > 0`, `fFamU S c x = (heatShift S c).density x`, which is the sum over the
*shifted* components `(a_i, shiftVarG G_i c)`. We re-derive — uniformly in `c` — the
split into the dominant identical-Gaussian group and a strictly-below residual. -/

/-- The exponential factor of the `c`-shifted Gaussian with base `G`. -/
private noncomputable def sgexp (G : GaussianPDF) (c x : ℝ) : ℝ :=
  Real.exp (-(x - G.mean) ^ 2 / (2 * (G.varSq + c)))

/-- The normalizing constant of the `c`-shifted Gaussian with base `G`. -/
private noncomputable def snorm (G : GaussianPDF) (c : ℝ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi * (G.varSq + c))

private theorem sgexp_pos (G : GaussianPDF) (c x : ℝ) : 0 < sgexp G c x :=
  Real.exp_pos _

private theorem snorm_pos (G : GaussianPDF) {c : ℝ} (hc : 0 ≤ c) : 0 < snorm G c := by
  unfold snorm
  have hv : 0 < G.varSq + c := by have := G.varSq_pos; linarith
  have := Real.pi_pos
  positivity

/-- The density of the `c`-shifted component `(a, G)` is `a · snorm · sgexp`. -/
private theorem shifted_density_eq (G : GaussianPDF) (c x : ℝ) (hc : 0 < c) :
    (shiftVarG G c hc).density x = snorm G c * sgexp G c x := by
  rw [GaussianPDF.density_eq]
  unfold shiftVarG snorm sgexp
  rfl

/-- `fFamU S c x` for `c > 0` written as a base-component list sum of shifted terms. -/
private theorem fFamU_eq_baseSum (S : SignedGaussianCombination) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    fFamU S c x =
      (S.components.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum := by
  rw [fFamU_eq_heatShift S c hc x]
  unfold heatShift
  rw [SignedGaussianCombination.density_eq, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  rw [shifted_density_eq p.2 c x hc]

/-! ## Dominant group / residual split (base-level, `c`-uniform) -/

/-- A base component is "top" w.r.t. `Gdom` if it has the same base variance AND mean. -/
private def isTopB (Gdom : GaussianPDF) (p : ℝ × GaussianPDF) : Prop :=
  p.2.varSq = Gdom.varSq ∧ p.2.mean = Gdom.mean

private noncomputable instance (Gdom : GaussianPDF) : DecidablePred (isTopB Gdom) := fun p =>
  Classical.propDecidable _

/-- A base component is strictly below `Gdom` in the right-tail lex order. -/
private def belowB (Gdom : GaussianPDF) (p : ℝ × GaussianPDF) : Prop :=
  p.2.varSq < Gdom.varSq ∨ (p.2.varSq = Gdom.varSq ∧ p.2.mean < Gdom.mean)

/-- A base component is strictly below `Gdom` in the left-tail lex order. -/
private def belowBL (Gdom : GaussianPDF) (p : ℝ × GaussianPDF) : Prop :=
  p.2.varSq < Gdom.varSq ∨ (p.2.varSq = Gdom.varSq ∧ Gdom.mean < p.2.mean)

/-- The dominant-group coefficient sum (base-level, `c`-independent). -/
private noncomputable def topCoeffSumB (Gdom : GaussianPDF) (S : SignedGaussianCombination) : ℝ :=
  ((S.components.filter (fun p => decide (isTopB Gdom p))).map (fun p => p.1)).sum

/-- A "top" base component's shifted term equals `coeff · snorm Gdom c · sgexp Gdom c x`. -/
private theorem shifted_term_of_isTopB {Gdom : GaussianPDF} {p : ℝ × GaussianPDF}
    (h : isTopB Gdom p) (c x : ℝ) :
    p.1 * (snorm p.2 c * sgexp p.2 c x) = p.1 * (snorm Gdom c * sgexp Gdom c x) := by
  obtain ⟨hv, hm⟩ := h
  unfold snorm sgexp
  rw [hv, hm]

/-- The residual list (non-top base components). -/
private noncomputable def restB (Gdom : GaussianPDF) (S : SignedGaussianCombination) :
    List (ℝ × GaussianPDF) :=
  S.components.filter (fun p => decide ¬ isTopB Gdom p)

/-- **`c`-uniform density split.** For `c > 0`,
`fFamU S c x = A · (snorm Gdom c · sgexp Gdom c x) + Σ_{rest} a_i · snorm_i · sgexp_i x`,
with `A = topCoeffSumB Gdom S` (the `c`-independent top-group coefficient sum). -/
private theorem fFamU_split (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    (c : ℝ) (hc : 0 < c) (x : ℝ) :
    fFamU S c x
      = topCoeffSumB Gdom S * (snorm Gdom c * sgexp Gdom c x)
        + ((restB Gdom S).map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum := by
  classical
  rw [fFamU_eq_baseSum S c hc x]
  set top := S.components.filter (fun p => decide (isTopB Gdom p)) with htop_def
  have hpart := List.sum_map_filter_add_sum_map_filter_not (isTopB Gdom)
    (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x)) S.components
  have htop_sum : (top.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum
      = topCoeffSumB Gdom S * (snorm Gdom c * sgexp Gdom c x) := by
    have hmap_eq : top.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))
        = top.map (fun p => p.1 * (snorm Gdom c * sgexp Gdom c x)) := by
      apply List.map_congr_left
      intro p hp
      have hp_top : isTopB Gdom p := by
        have := (List.mem_filter.mp hp).2
        simpa using this
      exact shifted_term_of_isTopB hp_top c x
    rw [hmap_eq, List.sum_map_mul_right top (fun p => p.1) (snorm Gdom c * sgexp Gdom c x)]
    rfl
  rw [← hpart, htop_sum]
  rfl

/-! ## Uniform exponential-ratio tail comparison (the crux)

For a "below" base variance `v_lo ≤ V` (strictly below in lex order), the shifted
exponential ratio `sgexp_lo c x / sgexp_dom c x = exp(diff c x)` has, beyond a SINGLE
threshold (independent of `c ∈ [0, c_max]`), `diff c x ≤ -M`, i.e. the ratio
`≤ exp(-M)`. This is the only genuinely-uniform analytic step. -/

/-- The exponent difference `diff = log(sgexp_lo / sgexp_dom)` written as an explicit
quadratic in `x` with `c`-dependent coefficients. -/
private theorem diff_quadratic_identity
    (v_lo μ1 V μ2 c x : ℝ) (hvl : 0 < v_lo + c) (hvd : 0 < V + c) :
    (-(x - μ1) ^ 2 / (2 * (v_lo + c))) - (-(x - μ2) ^ 2 / (2 * (V + c)))
      = (1 / (2 * (V + c)) - 1 / (2 * (v_lo + c))) * x ^ 2
        + (μ1 / (v_lo + c) - μ2 / (V + c)) * x
        + (μ2 ^ 2 / (2 * (V + c)) - μ1 ^ 2 / (2 * (v_lo + c))) := by
  have h1 : (2 * (v_lo + c)) ≠ 0 := by positivity
  have h2 : (2 * (V + c)) ≠ 0 := by positivity
  field_simp
  ring

/-- **Uniform right-tail exponential-ratio bound.** Given a strictly-below base
variance/mean, for any target `M ≥ 0` there is a single threshold `T` such that for
all `c ∈ [0, c_max]` and `x ≥ T`,
`sgexp ⟨μ1, v_lo, ·⟩ c x ≤ exp(-M) · sgexp ⟨μ2, V, ·⟩ c x`. -/
private theorem uniform_exp_ratio_right
    (v_lo μ1 V μ2 : ℝ) (hvl : 0 < v_lo) (hV : 0 < V) (hle : v_lo ≤ V)
    (hbelow : v_lo < V ∨ (v_lo = V ∧ μ1 < μ2))
    (c_max : ℝ) (hc_max : 0 < c_max) (M : ℝ) (hM : 0 ≤ M) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, T ≤ x →
      Real.exp (-(x - μ1) ^ 2 / (2 * (v_lo + c)))
        ≤ Real.exp (-M) * Real.exp (-(x - μ2) ^ 2 / (2 * (V + c))) := by
  -- uniform bounds on the lower-order coefficients
  set B : ℝ := |μ1| / v_lo + |μ2| / V with hB_def
  set C : ℝ := μ1 ^ 2 / (2 * v_lo) + μ2 ^ 2 / (2 * V) with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
  -- We produce, depending on the case, either a quadratic or linear uniform bound.
  rcases hbelow with hlt | ⟨hveq, hmu⟩
  · -- strict variance case: uniformly-negative leading coefficient
    set q : ℝ := (V - v_lo) / (2 * (V + c_max) * (v_lo + c_max)) with hq_def
    have hq_pos : 0 < q := by
      rw [hq_def]; apply div_pos (by linarith) (by positivity)
    refine ⟨max 1 ((B + C + M + 1) / q + 1), ?_⟩
    intro c hc0 hccmax x hxT
    have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hxT
    have hxT' : (B + C + M + 1) / q + 1 ≤ x := le_trans (le_max_right _ _) hxT
    have hxnn : 0 ≤ x := by linarith
    have hvl' : 0 < v_lo + c := by linarith
    have hvd' : 0 < V + c := by linarith
    -- the exponent difference as a quadratic
    set α : ℝ := 1 / (2 * (V + c)) - 1 / (2 * (v_lo + c)) with hα_def
    set β : ℝ := μ1 / (v_lo + c) - μ2 / (V + c) with hβ_def
    set γ : ℝ := μ2 ^ 2 / (2 * (V + c)) - μ1 ^ 2 / (2 * (v_lo + c)) with hγ_def
    have hdiff := diff_quadratic_identity v_lo μ1 V μ2 c x hvl' hvd'
    -- α ≤ -q
    have hα_le : α ≤ -q := by
      rw [hα_def, hq_def]
      have hα_eq : 1 / (2 * (V + c)) - 1 / (2 * (v_lo + c))
          = (v_lo - V) / (2 * (V + c) * (v_lo + c)) := by
        field_simp; ring
      have hnegq_eq : -((V - v_lo) / (2 * (V + c_max) * (v_lo + c_max)))
          = (v_lo - V) / (2 * (V + c_max) * (v_lo + c_max)) := by
        rw [← neg_div]; ring_nf
      rw [hα_eq, hnegq_eq]
      -- (v_lo - V)/d1 ≤ (v_lo - V)/d2 with d1 ≤ d2 (well, denom small ⇒ neg more neg)
      have hd1 : 0 < 2 * (V + c) * (v_lo + c) := by positivity
      have hd2 : 0 < 2 * (V + c_max) * (v_lo + c_max) := by positivity
      have hdle : 2 * (V + c) * (v_lo + c) ≤ 2 * (V + c_max) * (v_lo + c_max) := by
        have h1 : V + c ≤ V + c_max := by linarith
        have h2 : v_lo + c ≤ v_lo + c_max := by linarith
        nlinarith [hvl', hvd', h1, h2, hc0]
      rw [div_le_div_iff₀ hd1 hd2]
      nlinarith [hle, hdle, hd1, hd2]
    -- uniform bounds on β and γ
    have hβ_abs : |β| ≤ B := by
      rw [hβ_def, hB_def]
      calc |μ1 / (v_lo + c) - μ2 / (V + c)|
          ≤ |μ1 / (v_lo + c)| + |μ2 / (V + c)| := abs_sub _ _
        _ = |μ1| / (v_lo + c) + |μ2| / (V + c) := by
            rw [abs_div, abs_div, abs_of_pos hvl', abs_of_pos hvd']
        _ ≤ |μ1| / v_lo + |μ2| / V := by
            apply add_le_add
            · exact div_le_div_of_nonneg_left (abs_nonneg _) hvl (by linarith)
            · exact div_le_div_of_nonneg_left (abs_nonneg _) hV (by linarith)
    have hγ_abs : |γ| ≤ C := by
      rw [hγ_def, hC_def]
      calc |μ2 ^ 2 / (2 * (V + c)) - μ1 ^ 2 / (2 * (v_lo + c))|
          ≤ |μ2 ^ 2 / (2 * (V + c))| + |μ1 ^ 2 / (2 * (v_lo + c))| := abs_sub _ _
        _ = μ2 ^ 2 / (2 * (V + c)) + μ1 ^ 2 / (2 * (v_lo + c)) := by
            rw [abs_div, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ μ2 ^ 2),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ μ1 ^ 2),
              abs_of_pos (by positivity : (0:ℝ) < 2 * (V + c)),
              abs_of_pos (by positivity : (0:ℝ) < 2 * (v_lo + c))]
        _ ≤ μ1 ^ 2 / (2 * v_lo) + μ2 ^ 2 / (2 * V) := by
            rw [add_comm]
            apply add_le_add
            · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
            · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    -- assemble: diff ≤ α x² + β x + γ ≤ -M
    have hquad : α * x ^ 2 + β * x + γ ≤ -M :=
      quad_le_neg_of_large α β γ q B C M hα_le hq_pos hβ_abs hγ_abs hC_nn hM x hx1 hxT'
    -- convert to the exp statement
    have hdiff_le : (-(x - μ1) ^ 2 / (2 * (v_lo + c)))
        - (-(x - μ2) ^ 2 / (2 * (V + c))) ≤ -M := by
      rw [hdiff]; rw [← hα_def, ← hβ_def, ← hγ_def] at *; exact hquad
    -- exp monotone
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hdiff_le]
  · -- equal-variance tie case: α = 0, linear with uniformly-negative slope
    subst hveq
    set q : ℝ := (μ2 - μ1) / (v_lo + c_max) with hq_def
    have hq_pos : 0 < q := by
      rw [hq_def]; apply div_pos (by linarith) (by linarith)
    refine ⟨max 1 ((C + M + 1) / q + 1), ?_⟩
    intro c hc0 hccmax x hxT
    have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hxT
    have hxT' : (C + M + 1) / q + 1 ≤ x := le_trans (le_max_right _ _) hxT
    have hxnn : 0 ≤ x := by linarith
    have hvl' : 0 < v_lo + c := by linarith
    set β : ℝ := μ1 / (v_lo + c) - μ2 / (v_lo + c) with hβ_def
    set γ : ℝ := μ2 ^ 2 / (2 * (v_lo + c)) - μ1 ^ 2 / (2 * (v_lo + c)) with hγ_def
    have hdiff := diff_quadratic_identity v_lo μ1 v_lo μ2 c x hvl' hvl'
    -- the x² coefficient vanishes
    have hα0 : (1 / (2 * (v_lo + c)) - 1 / (2 * (v_lo + c))) = 0 := by ring
    -- β ≤ -q
    have hβ_le : β ≤ -q := by
      rw [hβ_def, hq_def]
      have hβ_eq : μ1 / (v_lo + c) - μ2 / (v_lo + c) = (μ1 - μ2) / (v_lo + c) := by
        rw [div_sub_div_same]
      rw [hβ_eq]
      have hnegq : -((μ2 - μ1) / (v_lo + c_max)) = (μ1 - μ2) / (v_lo + c_max) := by
        rw [← neg_div]; ring_nf
      rw [hnegq]
      have hd1 : 0 < v_lo + c := hvl'
      have hd2 : 0 < v_lo + c_max := by linarith
      rw [div_le_div_iff₀ hd1 hd2]
      nlinarith [hmu, hd1, hd2, hc0, hccmax]
    -- γ bound
    have hγ_abs : |γ| ≤ C := by
      rw [hγ_def, hC_def]
      calc |μ2 ^ 2 / (2 * (v_lo + c)) - μ1 ^ 2 / (2 * (v_lo + c))|
          ≤ |μ2 ^ 2 / (2 * (v_lo + c))| + |μ1 ^ 2 / (2 * (v_lo + c))| := abs_sub _ _
        _ = μ2 ^ 2 / (2 * (v_lo + c)) + μ1 ^ 2 / (2 * (v_lo + c)) := by
            rw [abs_div, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ μ2 ^ 2),
              abs_of_nonneg (by positivity : (0:ℝ) ≤ μ1 ^ 2),
              abs_of_pos (by positivity : (0:ℝ) < 2 * (v_lo + c))]
        _ ≤ μ1 ^ 2 / (2 * v_lo) + μ2 ^ 2 / (2 * v_lo) := by
            rw [add_comm]
            apply add_le_add
            · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
            · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have hlin : β * x + γ ≤ -M :=
      lin_le_neg_of_large β γ q C M hβ_le hq_pos hγ_abs hC_nn hM x hx1 hxT'
    have hdiff_le : (-(x - μ1) ^ 2 / (2 * (v_lo + c)))
        - (-(x - μ2) ^ 2 / (2 * (v_lo + c))) ≤ -M := by
      rw [hdiff, hα0, zero_mul, zero_add]
      rw [← hβ_def, ← hγ_def]; exact hlin
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hdiff_le]

/-- **Uniform left-tail exponential-ratio bound** (reflection of the right version). -/
private theorem uniform_exp_ratio_left
    (v_lo μ1 V μ2 : ℝ) (hvl : 0 < v_lo) (hV : 0 < V) (hle : v_lo ≤ V)
    (hbelow : v_lo < V ∨ (v_lo = V ∧ μ2 < μ1))
    (c_max : ℝ) (hc_max : 0 < c_max) (M : ℝ) (hM : 0 ≤ M) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, x ≤ T →
      Real.exp (-(x - μ1) ^ 2 / (2 * (v_lo + c)))
        ≤ Real.exp (-M) * Real.exp (-(x - μ2) ^ 2 / (2 * (V + c))) := by
  have hbelow' : v_lo < V ∨ (v_lo = V ∧ -μ1 < -μ2) := by
    rcases hbelow with h | ⟨he, hm⟩
    · exact Or.inl h
    · exact Or.inr ⟨he, by linarith⟩
  obtain ⟨T, hT⟩ := uniform_exp_ratio_right v_lo (-μ1) V (-μ2) hvl hV hle hbelow' c_max hc_max M hM
  refine ⟨-T, ?_⟩
  intro c hc0 hccmax x hxT
  have hyT : T ≤ -x := by linarith
  have := hT c hc0 hccmax (-x) hyT
  -- rewrite (-x - (-μ))² = (x - μ)²
  have e1 : -(-x - -μ1) ^ 2 / (2 * (v_lo + c)) = -(x - μ1) ^ 2 / (2 * (v_lo + c)) := by
    congr 2; ring
  have e2 : -(-x - -μ2) ^ 2 / (2 * (V + c)) = -(x - μ2) ^ 2 / (2 * (V + c)) := by
    congr 2; ring
  rw [e1, e2] at this
  exact this

/-! ## Uniform `snorm` ratio bound -/

/-- The shifted normalizing constant `snorm G c` is bounded by a `c`-independent multiple
of `snorm Gdom c`, uniformly over `c ∈ [0, c_max]`, when `G.varSq ≤ Gdom.varSq`. -/
private theorem snorm_le_uniform (G Gdom : GaussianPDF) (c_max : ℝ) (hc_max : 0 < c_max)
    (hle : G.varSq ≤ Gdom.varSq) :
    ∃ Csn : ℝ, 0 ≤ Csn ∧ ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
      snorm G c ≤ Csn * snorm Gdom c := by
  have hGv : 0 < G.varSq := G.varSq_pos
  have hDv : 0 < Gdom.varSq := Gdom.varSq_pos
  -- Csn := √((Gdom.varSq + c_max) / G.varSq)
  refine ⟨Real.sqrt ((Gdom.varSq + c_max) / G.varSq), Real.sqrt_nonneg _, ?_⟩
  intro c hc0 hccmax
  have hGc : 0 < G.varSq + c := by linarith
  have hDc : 0 < Gdom.varSq + c := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  set Csn := Real.sqrt ((Gdom.varSq + c_max) / G.varSq) with hCsn_def
  have hsG : 0 < Real.sqrt (2 * Real.pi * (G.varSq + c)) := by positivity
  have hsD : 0 < Real.sqrt (2 * Real.pi * (Gdom.varSq + c)) := by positivity
  -- key sqrt inequality: √(2π(Gdom+c)) ≤ Csn * √(2π(G+c))
  have hkey : Real.sqrt (2 * Real.pi * (Gdom.varSq + c))
      ≤ Csn * Real.sqrt (2 * Real.pi * (G.varSq + c)) := by
    rw [hCsn_def, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div, le_div_iff₀ hGv]
    have hcc : 0 ≤ c_max - c := by linarith
    have hGG : 0 ≤ Gdom.varSq - G.varSq := by linarith
    -- bracket inequality: (Gdom+c)·G ≤ (Gdom+c_max)·(G+c)
    have hbracket : (Gdom.varSq + c) * G.varSq
        ≤ (Gdom.varSq + c_max) * (G.varSq + c) := by
      nlinarith [mul_nonneg hc0 hGG, mul_nonneg hcc (le_of_lt hGv),
        mul_nonneg hcc hc0, hGv, hDv]
    -- multiply by 2π
    have h2pi : (0:ℝ) ≤ 2 * Real.pi := by positivity
    calc 2 * Real.pi * (Gdom.varSq + c) * G.varSq
        = 2 * Real.pi * ((Gdom.varSq + c) * G.varSq) := by ring
      _ ≤ 2 * Real.pi * ((Gdom.varSq + c_max) * (G.varSq + c)) :=
          mul_le_mul_of_nonneg_left hbracket h2pi
      _ = (Gdom.varSq + c_max) * (2 * Real.pi * (G.varSq + c)) := by ring
  -- transfer to reciprocals
  unfold snorm
  rw [div_le_iff₀ hsG]
  have hrhs : Csn * (1 / Real.sqrt (2 * Real.pi * (Gdom.varSq + c)))
      * Real.sqrt (2 * Real.pi * (G.varSq + c))
      = Csn * Real.sqrt (2 * Real.pi * (G.varSq + c))
        / Real.sqrt (2 * Real.pi * (Gdom.varSq + c)) := by
    field_simp
  rw [hrhs, le_div_iff₀ hsD, one_mul]
  linarith [hkey]

/-! ## Per-component and residual-sum uniform bounds -/

/-- **Per-component uniform tail bound.** For a base component `(a, G)` strictly below
`Gdom` in the right-tail lex order, and any prescribed `κ > 0`, there is a single
threshold `T` such that for all `c ∈ [0, c_max]` and `x ≥ T`,
`|a · snorm G c · sgexp G c x| ≤ κ · (snorm Gdom c · sgexp Gdom c x)`. -/
private theorem component_uniform_bound_right
    (a : ℝ) (G Gdom : GaussianPDF) (c_max : ℝ) (hc_max : 0 < c_max)
    (hbelow : belowB Gdom (a, G)) (κ : ℝ) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, T ≤ x →
      |a * (snorm G c * sgexp G c x)| ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
  have hGv : 0 < G.varSq := G.varSq_pos
  have hDv : 0 < Gdom.varSq := Gdom.varSq_pos
  have hle : G.varSq ≤ Gdom.varSq := by
    rcases hbelow with h | ⟨he, _⟩ <;> [exact le_of_lt h; exact le_of_eq he]
  obtain ⟨Csn, hCsn_nn, hCsn⟩ := snorm_le_uniform G Gdom c_max hc_max hle
  -- choose M with |a| * Csn * exp(-M) ≤ κ, i.e. exp(-M) ≤ κ / (|a|Csn + 1)
  set D : ℝ := |a| * Csn + 1 with hD_def
  have hD_pos : 0 < D := by rw [hD_def]; positivity
  -- M := log (D / κ) ⊔ 0 ; we need exp(-M) ≤ κ/D
  set M : ℝ := max (Real.log (D / κ)) 0 with hM_def
  have hM_nn : 0 ≤ M := le_max_right _ _
  have hexpM : Real.exp (-M) ≤ κ / D := by
    have hMge : Real.log (D / κ) ≤ M := le_max_left _ _
    have hpos : 0 < D / κ := by positivity
    -- exp(-M) ≤ exp(-log(D/κ)) = κ/D
    have hstep : Real.exp (-M) ≤ Real.exp (-(Real.log (D / κ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(Real.log (D / κ))) = κ / D := by
      rw [Real.exp_neg, Real.exp_log hpos, inv_div]
    rwa [hval] at hstep
  -- exp ratio threshold
  have hbelow' : G.varSq < Gdom.varSq ∨ (G.varSq = Gdom.varSq ∧ G.mean < Gdom.mean) := hbelow
  obtain ⟨T, hT⟩ := uniform_exp_ratio_right G.varSq G.mean Gdom.varSq Gdom.mean
    hGv hDv hle hbelow' c_max hc_max M hM_nn
  refine ⟨T, ?_⟩
  intro c hc0 hccmax x hxT
  have hc0' := hc0
  have hsnG_pos : 0 < snorm G c := snorm_pos G hc0
  have hsnD_pos : 0 < snorm Gdom c := snorm_pos Gdom hc0
  have hgG_pos : 0 < sgexp G c x := sgexp_pos G c x
  have hgD_pos : 0 < sgexp Gdom c x := sgexp_pos Gdom c x
  -- the exp ratio bound: sgexp G c x ≤ exp(-M) * sgexp Gdom c x
  have hexpr : sgexp G c x ≤ Real.exp (-M) * sgexp Gdom c x := by
    have := hT c hc0 hccmax x hxT
    unfold sgexp
    exact this
  -- snorm bound
  have hsnr : snorm G c ≤ Csn * snorm Gdom c := hCsn c hc0 hccmax
  -- combine
  rw [abs_mul, abs_of_pos (mul_pos hsnG_pos hgG_pos)]
  calc |a| * (snorm G c * sgexp G c x)
      ≤ |a| * ((Csn * snorm Gdom c) * (Real.exp (-M) * sgexp Gdom c x)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
        apply mul_le_mul hsnr hexpr (le_of_lt hgG_pos)
        exact mul_nonneg hCsn_nn (le_of_lt hsnD_pos)
    _ = (|a| * Csn * Real.exp (-M)) * (snorm Gdom c * sgexp Gdom c x) := by ring
    _ ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (mul_pos hsnD_pos hgD_pos))
        -- |a| Csn exp(-M) ≤ κ
        have h1 : |a| * Csn * Real.exp (-M) ≤ D * Real.exp (-M) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
          rw [hD_def]; linarith [abs_nonneg a, hCsn_nn]
        have h2 : D * Real.exp (-M) ≤ D * (κ / D) :=
          mul_le_mul_of_nonneg_left hexpM (le_of_lt hD_pos)
        have h3 : D * (κ / D) = κ := by field_simp
        linarith [h1, h2, h3]

/-- **Per-component uniform tail bound, left tail.** Mirror of
`component_uniform_bound_right` using the left-tail lex order and `x ≤ T`. -/
private theorem component_uniform_bound_left
    (a : ℝ) (G Gdom : GaussianPDF) (c_max : ℝ) (hc_max : 0 < c_max)
    (hbelow : belowBL Gdom (a, G)) (κ : ℝ) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, x ≤ T →
      |a * (snorm G c * sgexp G c x)| ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
  have hGv : 0 < G.varSq := G.varSq_pos
  have hDv : 0 < Gdom.varSq := Gdom.varSq_pos
  have hle : G.varSq ≤ Gdom.varSq := by
    rcases hbelow with h | ⟨he, _⟩ <;> [exact le_of_lt h; exact le_of_eq he]
  obtain ⟨Csn, hCsn_nn, hCsn⟩ := snorm_le_uniform G Gdom c_max hc_max hle
  set D : ℝ := |a| * Csn + 1 with hD_def
  have hD_pos : 0 < D := by rw [hD_def]; positivity
  set M : ℝ := max (Real.log (D / κ)) 0 with hM_def
  have hM_nn : 0 ≤ M := le_max_right _ _
  have hexpM : Real.exp (-M) ≤ κ / D := by
    have hMge : Real.log (D / κ) ≤ M := le_max_left _ _
    have hpos : 0 < D / κ := by positivity
    have hstep : Real.exp (-M) ≤ Real.exp (-(Real.log (D / κ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(Real.log (D / κ))) = κ / D := by
      rw [Real.exp_neg, Real.exp_log hpos, inv_div]
    rwa [hval] at hstep
  have hbelow' : G.varSq < Gdom.varSq ∨ (G.varSq = Gdom.varSq ∧ Gdom.mean < G.mean) := hbelow
  obtain ⟨T, hT⟩ := uniform_exp_ratio_left G.varSq G.mean Gdom.varSq Gdom.mean
    hGv hDv hle hbelow' c_max hc_max M hM_nn
  refine ⟨T, ?_⟩
  intro c hc0 hccmax x hxT
  have hsnG_pos : 0 < snorm G c := snorm_pos G hc0
  have hsnD_pos : 0 < snorm Gdom c := snorm_pos Gdom hc0
  have hgG_pos : 0 < sgexp G c x := sgexp_pos G c x
  have hgD_pos : 0 < sgexp Gdom c x := sgexp_pos Gdom c x
  have hexpr : sgexp G c x ≤ Real.exp (-M) * sgexp Gdom c x := by
    have := hT c hc0 hccmax x hxT
    unfold sgexp
    exact this
  have hsnr : snorm G c ≤ Csn * snorm Gdom c := hCsn c hc0 hccmax
  rw [abs_mul, abs_of_pos (mul_pos hsnG_pos hgG_pos)]
  calc |a| * (snorm G c * sgexp G c x)
      ≤ |a| * ((Csn * snorm Gdom c) * (Real.exp (-M) * sgexp Gdom c x)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
        apply mul_le_mul hsnr hexpr (le_of_lt hgG_pos)
        exact mul_nonneg hCsn_nn (le_of_lt hsnD_pos)
    _ = (|a| * Csn * Real.exp (-M)) * (snorm Gdom c * sgexp Gdom c x) := by ring
    _ ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt (mul_pos hsnD_pos hgD_pos))
        have h1 : |a| * Csn * Real.exp (-M) ≤ D * Real.exp (-M) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
          rw [hD_def]; linarith [abs_nonneg a, hCsn_nn]
        have h2 : D * Real.exp (-M) ≤ D * (κ / D) :=
          mul_le_mul_of_nonneg_left hexpM (le_of_lt hD_pos)
        have h3 : D * (κ / D) = κ := by field_simp
        linarith [h1, h2, h3]

/-! ## Residual-sum uniform bounds (list induction) -/

/-- **Right-tail residual-sum uniform bound.** For a list `L` of base components each
of which is either zero-coefficient or strictly below `Gdom` in the right-tail lex order,
and any prescribed `κ > 0`, there is a single threshold `T` such that for all
`c ∈ [0, c_max]` and `x ≥ T`,
`|Σ_{p ∈ L} a_p · snorm_p c · sgexp_p c x| ≤ κ · (snorm Gdom c · sgexp Gdom c x)`. -/
private theorem listSum_uniform_bound_right
    (Gdom : GaussianPDF) (c_max : ℝ) (hc_max : 0 < c_max)
    (L : List (ℝ × GaussianPDF))
    (hcov : ∀ p ∈ L, p.1 = 0 ∨ belowB Gdom p) (κ : ℝ) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, T ≤ x →
      |(L.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum|
        ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
  induction L generalizing κ with
  | nil =>
      refine ⟨0, ?_⟩
      intro c hc0 hccmax x hxT
      simp only [List.map_nil, List.sum_nil, abs_zero]
      have := mul_pos (snorm_pos Gdom hc0) (sgexp_pos Gdom c x)
      positivity
  | cons hd tl ih =>
      have hhd := hcov hd (List.mem_cons_self)
      have htl : ∀ p ∈ tl, p.1 = 0 ∨ belowB Gdom p := fun p hp =>
        hcov p (List.mem_cons_of_mem _ hp)
      -- head threshold (κ/2)
      have hhd_bound : ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, T ≤ x →
          |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)| ≤ (κ / 2) * (snorm Gdom c * sgexp Gdom c x) := by
        rcases hhd with h0 | hbelow
        · refine ⟨0, ?_⟩
          intro c hc0 hccmax x hxT
          rw [h0, zero_mul, abs_zero]
          have := mul_pos (snorm_pos Gdom hc0) (sgexp_pos Gdom c x)
          positivity
        · have := component_uniform_bound_right hd.1 hd.2 Gdom c_max hc_max
            (by rcases hd with ⟨a, G⟩; exact hbelow) (κ / 2) (by linarith)
          obtain ⟨T, hT⟩ := this
          exact ⟨T, hT⟩
      obtain ⟨Thd, hThd⟩ := hhd_bound
      obtain ⟨Ttl, hTtl⟩ := ih htl (κ / 2) (by linarith)
      refine ⟨max Thd Ttl, ?_⟩
      intro c hc0 hccmax x hxT
      have hxhd : Thd ≤ x := le_trans (le_max_left _ _) hxT
      have hxtl : Ttl ≤ x := le_trans (le_max_right _ _) hxT
      simp only [List.map_cons, List.sum_cons]
      have htri : |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)
            + (tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum|
          ≤ |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)|
            + |(tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum| :=
        abs_add_le _ _
      have hb1 := hThd c hc0 hccmax x hxhd
      have hb2 := hTtl c hc0 hccmax x hxtl
      calc |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)
            + (tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum|
          ≤ |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)|
            + |(tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum| := htri
        _ ≤ (κ / 2) * (snorm Gdom c * sgexp Gdom c x)
            + (κ / 2) * (snorm Gdom c * sgexp Gdom c x) := by linarith [hb1, hb2]
        _ = κ * (snorm Gdom c * sgexp Gdom c x) := by ring

/-- **Left-tail residual-sum uniform bound.** Mirror of `listSum_uniform_bound_right`. -/
private theorem listSum_uniform_bound_left
    (Gdom : GaussianPDF) (c_max : ℝ) (hc_max : 0 < c_max)
    (L : List (ℝ × GaussianPDF))
    (hcov : ∀ p ∈ L, p.1 = 0 ∨ belowBL Gdom p) (κ : ℝ) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, x ≤ T →
      |(L.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum|
        ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
  induction L generalizing κ with
  | nil =>
      refine ⟨0, ?_⟩
      intro c hc0 hccmax x hxT
      simp only [List.map_nil, List.sum_nil, abs_zero]
      have := mul_pos (snorm_pos Gdom hc0) (sgexp_pos Gdom c x)
      positivity
  | cons hd tl ih =>
      have hhd := hcov hd (List.mem_cons_self)
      have htl : ∀ p ∈ tl, p.1 = 0 ∨ belowBL Gdom p := fun p hp =>
        hcov p (List.mem_cons_of_mem _ hp)
      have hhd_bound : ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, x ≤ T →
          |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)| ≤ (κ / 2) * (snorm Gdom c * sgexp Gdom c x) := by
        rcases hhd with h0 | hbelow
        · refine ⟨0, ?_⟩
          intro c hc0 hccmax x hxT
          rw [h0, zero_mul, abs_zero]
          have := mul_pos (snorm_pos Gdom hc0) (sgexp_pos Gdom c x)
          positivity
        · have := component_uniform_bound_left hd.1 hd.2 Gdom c_max hc_max
            (by rcases hd with ⟨a, G⟩; exact hbelow) (κ / 2) (by linarith)
          obtain ⟨T, hT⟩ := this
          exact ⟨T, hT⟩
      obtain ⟨Thd, hThd⟩ := hhd_bound
      obtain ⟨Ttl, hTtl⟩ := ih htl (κ / 2) (by linarith)
      refine ⟨min Thd Ttl, ?_⟩
      intro c hc0 hccmax x hxT
      have hxhd : x ≤ Thd := le_trans hxT (min_le_left _ _)
      have hxtl : x ≤ Ttl := le_trans hxT (min_le_right _ _)
      simp only [List.map_cons, List.sum_cons]
      have htri : |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)
            + (tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum|
          ≤ |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)|
            + |(tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum| :=
        abs_add_le _ _
      have hb1 := hThd c hc0 hccmax x hxhd
      have hb2 := hTtl c hc0 hccmax x hxtl
      calc |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)
            + (tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum|
          ≤ |hd.1 * (snorm hd.2 c * sgexp hd.2 c x)|
            + |(tl.map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum| := htri
        _ ≤ (κ / 2) * (snorm Gdom c * sgexp Gdom c x)
            + (κ / 2) * (snorm Gdom c * sgexp Gdom c x) := by linarith [hb1, hb2]
        _ = κ * (snorm Gdom c * sgexp Gdom c x) := by ring

/-! ## Cancelling-top-group reduction (preserves `fFamU`, base level)

We must pick a dominant `Gdom` whose top-group coefficient sum is nonzero. The lex-max
nonzero component may sit in a same-(varSq,mean) group whose coefficients cancel; in
that case dropping the whole group preserves `fFamU S c` (the shifted group still has a
single shifted Gaussian, coefficient sum 0) and strictly shortens the component list. -/

/-- The combination with the `Gdom`-top group deleted. -/
private noncomputable def dropTopB (Gdom : GaussianPDF) (S : SignedGaussianCombination) :
    SignedGaussianCombination :=
  ⟨S.components.filter (fun p => decide ¬ isTopB Gdom p)⟩

/-- `restB Gdom S` is exactly the component list of `dropTopB Gdom S`. -/
private theorem restB_eq_dropTopB (Gdom : GaussianPDF) (S : SignedGaussianCombination) :
    restB Gdom S = (dropTopB Gdom S).components := rfl

/-- For `c > 0`, dropping a cancelling top group (coefficient sum zero) preserves `fFamU`. -/
private theorem dropTopB_fFamU_eq (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    (c : ℝ) (hc : 0 < c) (hzero : topCoeffSumB Gdom S = 0) (x : ℝ) :
    fFamU (dropTopB Gdom S) c x = fFamU S c x := by
  rw [fFamU_split S Gdom c hc x, hzero, zero_mul, zero_add]
  rw [fFamU_eq_baseSum (dropTopB Gdom S) c hc x]
  rw [restB_eq_dropTopB]

/-- Dropping a top group containing the nonzero component `(a, Gdom)` strictly shortens. -/
private theorem dropTopB_length_lt (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    {a : ℝ} (hmem : (a, Gdom) ∈ S.components) :
    (dropTopB Gdom S).components.length < S.components.length := by
  classical
  have hp_top : isTopB Gdom (a, Gdom) := ⟨rfl, rfl⟩
  have hp_false : ¬ (decide ¬ isTopB Gdom (a, Gdom)) = true := by simp [hp_top]
  have hlt : (S.components.filter (fun p => decide ¬ isTopB Gdom p)).length
      < S.components.length := by
    have hle := List.length_filter_le (fun p => decide ¬ isTopB Gdom p) S.components
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hall : ∀ p ∈ S.components, (fun p => decide ¬ isTopB Gdom p) p = true :=
        (List.length_filter_eq_length_iff).mp h
      exact hp_false (hall (a, Gdom) hmem)
  simpa [dropTopB] using hlt

/-- If every coefficient is zero the density is zero (used for termination). -/
private theorem density_zero_of_all_coeff_zero (S : SignedGaussianCombination)
    (h : ∀ p ∈ S.components, p.1 = 0) (x : ℝ) : S.density x = 0 := by
  rw [SignedGaussianCombination.density_eq]
  apply List.sum_eq_zero
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [h p hp, zero_mul]

private theorem exists_nonzero_coeff_of_density_ne (S : SignedGaussianCombination)
    (hS : ∃ x, S.density x ≠ 0) : ∃ p ∈ S.components, p.1 ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx⟩ := hS
  exact hx (density_zero_of_all_coeff_zero S h x)

/-- Bridge: a right-tail lex-max dominant `G` gives the residual-cover hypothesis. -/
private theorem coverB_right_of_lexMax (S : SignedGaussianCombination) (G : GaussianPDF)
    (hmax : ∀ p ∈ S.components, p.1 ≠ 0 →
        p.2.varSq < G.varSq ∨ (p.2.varSq = G.varSq ∧ p.2.mean ≤ G.mean)) :
    ∀ p ∈ restB G S, p.1 = 0 ∨ belowB G p := by
  intro p hp
  have hp_comp : p ∈ S.components := (List.mem_filter.mp hp).1
  have hp_not : ¬ isTopB G p := by
    have := (List.mem_filter.mp hp).2; simpa using this
  by_cases h0 : p.1 = 0
  · exact Or.inl h0
  · rcases hmax p hp_comp h0 with hlt | ⟨heq, hle⟩
    · exact Or.inr (Or.inl hlt)
    · rcases lt_or_eq_of_le hle with hmlt | hmeq
      · exact Or.inr (Or.inr ⟨heq, hmlt⟩)
      · exact absurd ⟨heq, hmeq⟩ hp_not

private theorem coverB_left_of_lexMax (S : SignedGaussianCombination) (G : GaussianPDF)
    (hmax : ∀ p ∈ S.components, p.1 ≠ 0 →
        p.2.varSq < G.varSq ∨ (p.2.varSq = G.varSq ∧ G.mean ≤ p.2.mean)) :
    ∀ p ∈ restB G S, p.1 = 0 ∨ belowBL G p := by
  intro p hp
  have hp_comp : p ∈ S.components := (List.mem_filter.mp hp).1
  have hp_not : ¬ isTopB G p := by
    have := (List.mem_filter.mp hp).2; simpa using this
  by_cases h0 : p.1 = 0
  · exact Or.inl h0
  · rcases hmax p hp_comp h0 with hlt | ⟨heq, hle⟩
    · exact Or.inr (Or.inl hlt)
    · rcases lt_or_eq_of_le hle with hmlt | hmeq
      · exact Or.inr (Or.inr ⟨heq, hmlt⟩)
      · exact absurd ⟨heq, hmeq.symm⟩ hp_not

/-- **Right-tail reduction.** From a somewhere-nonzero density, produce a reduced
combination `S'` (same `fFamU` slices and same density) with a dominant `G` whose top
group sum is nonzero, covering `S'` in the right-tail order. -/
private theorem exists_reducedB_right :
    ∀ (n : ℕ) (S : SignedGaussianCombination),
      S.components.length ≤ n → (∃ x, S.density x ≠ 0) →
      ∃ (S' : SignedGaussianCombination) (G : GaussianPDF),
        (∀ (c : ℝ), 0 < c → ∀ x, fFamU S' c x = fFamU S c x) ∧
        (∀ p ∈ restB G S', p.1 = 0 ∨ belowB G p) ∧
        topCoeffSumB G S' ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro S hlen hS
      have hnil : S.components = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      exfalso
      obtain ⟨x, hx⟩ := hS
      apply hx
      apply density_zero_of_all_coeff_zero
      intro p hp; rw [hnil] at hp; exact absurd hp (List.not_mem_nil)
  | succ n ih =>
      intro S hlen hS
      obtain ⟨a, G, hmem, hc, hmax⟩ :=
        exists_lexMax_component_right S (exists_nonzero_coeff_of_density_ne S hS)
      have hcov := coverB_right_of_lexMax S G hmax
      by_cases hA : topCoeffSumB G S = 0
      · have hlt := dropTopB_length_lt S G hmem
        have hlen' : (dropTopB G S).components.length ≤ n := by omega
        have hS' : ∃ x, (dropTopB G S).density x ≠ 0 := by
          obtain ⟨x, hx⟩ := hS
          -- dropTopB preserves density (cancelling top group); reuse fFamU at any c>0 not needed
          refine ⟨x, ?_⟩
          -- use the density-level split via the core's reasoning: here directly from fFamU? density is c=0.
          -- We instead show (dropTopB G S).density x = S.density x.
          have hdens : (dropTopB G S).density x = S.density x := by
            -- density = fFamU at c→0; reuse the algebraic split at the density level
            rw [SignedGaussianCombination.density_eq, SignedGaussianCombination.density_eq]
            -- (dropTopB G S).components = filter ¬isTopB; relate to S via filter partition
            have hpart := List.sum_map_filter_add_sum_map_filter_not (isTopB G)
              (fun p => p.1 * p.2.density x) S.components
            have htopsum : ((S.components.filter (fun p => decide (isTopB G p))).map
                  (fun p => p.1 * p.2.density x)).sum = 0 := by
              have hmap_eq : (S.components.filter (fun p => decide (isTopB G p))).map
                    (fun p => p.1 * p.2.density x)
                  = (S.components.filter (fun p => decide (isTopB G p))).map
                    (fun p => p.1 * G.density x) := by
                apply List.map_congr_left
                intro p hp
                have hp_top : isTopB G p := by
                  have := (List.mem_filter.mp hp).2; simpa using this
                obtain ⟨hv, hm⟩ := hp_top
                rw [GaussianPDF.density_eq, GaussianPDF.density_eq, hv, hm]
              rw [hmap_eq, List.sum_map_mul_right, ← topCoeffSumB, hA, zero_mul]
            show ((dropTopB G S).components.map (fun p => p.1 * p.2.density x)).sum
              = (S.components.map (fun p => p.1 * p.2.density x)).sum
            rw [show (dropTopB G S).components
                  = S.components.filter (fun p => decide ¬ isTopB G p) from rfl]
            linarith [hpart, htopsum]
          rw [hdens]; exact hx
        obtain ⟨S', G', hfam', hcov', hA'⟩ := ih (dropTopB G S) hlen' hS'
        refine ⟨S', G', ?_, hcov', hA'⟩
        intro c hcpos x
        rw [hfam' c hcpos x, dropTopB_fFamU_eq S G c hcpos hA x]
      · exact ⟨S, G, fun c hcpos x => rfl, hcov, hA⟩

/-- **Left-tail reduction.** Mirror of `exists_reducedB_right`. -/
private theorem exists_reducedB_left :
    ∀ (n : ℕ) (S : SignedGaussianCombination),
      S.components.length ≤ n → (∃ x, S.density x ≠ 0) →
      ∃ (S' : SignedGaussianCombination) (G : GaussianPDF),
        (∀ (c : ℝ), 0 < c → ∀ x, fFamU S' c x = fFamU S c x) ∧
        (∀ p ∈ restB G S', p.1 = 0 ∨ belowBL G p) ∧
        topCoeffSumB G S' ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro S hlen hS
      have hnil : S.components = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      exfalso
      obtain ⟨x, hx⟩ := hS
      apply hx
      apply density_zero_of_all_coeff_zero
      intro p hp; rw [hnil] at hp; exact absurd hp (List.not_mem_nil)
  | succ n ih =>
      intro S hlen hS
      obtain ⟨a, G, hmem, hc, hmax⟩ :=
        exists_lexMax_component_left S (exists_nonzero_coeff_of_density_ne S hS)
      have hcov := coverB_left_of_lexMax S G hmax
      by_cases hA : topCoeffSumB G S = 0
      · have hlt := dropTopB_length_lt S G hmem
        have hlen' : (dropTopB G S).components.length ≤ n := by omega
        have hS' : ∃ x, (dropTopB G S).density x ≠ 0 := by
          obtain ⟨x, hx⟩ := hS
          refine ⟨x, ?_⟩
          have hdens : (dropTopB G S).density x = S.density x := by
            rw [SignedGaussianCombination.density_eq, SignedGaussianCombination.density_eq]
            have hpart := List.sum_map_filter_add_sum_map_filter_not (isTopB G)
              (fun p => p.1 * p.2.density x) S.components
            have htopsum : ((S.components.filter (fun p => decide (isTopB G p))).map
                  (fun p => p.1 * p.2.density x)).sum = 0 := by
              have hmap_eq : (S.components.filter (fun p => decide (isTopB G p))).map
                    (fun p => p.1 * p.2.density x)
                  = (S.components.filter (fun p => decide (isTopB G p))).map
                    (fun p => p.1 * G.density x) := by
                apply List.map_congr_left
                intro p hp
                have hp_top : isTopB G p := by
                  have := (List.mem_filter.mp hp).2; simpa using this
                obtain ⟨hv, hm⟩ := hp_top
                rw [GaussianPDF.density_eq, GaussianPDF.density_eq, hv, hm]
              rw [hmap_eq, List.sum_map_mul_right, ← topCoeffSumB, hA, zero_mul]
            show ((dropTopB G S).components.map (fun p => p.1 * p.2.density x)).sum
              = (S.components.map (fun p => p.1 * p.2.density x)).sum
            rw [show (dropTopB G S).components
                  = S.components.filter (fun p => decide ¬ isTopB G p) from rfl]
            linarith [hpart, htopsum]
          rw [hdens]; exact hx
        obtain ⟨S', G', hfam', hcov', hA'⟩ := ih (dropTopB G S) hlen' hS'
        refine ⟨S', G', ?_, hcov', hA'⟩
        intro c hcpos x
        rw [hfam' c hcpos x, dropTopB_fFamU_eq S G c hcpos hA x]
      · exact ⟨S, G, fun c hcpos x => rfl, hcov, hA⟩

/-! ## Fixed-envelope uniform bound vs the dominant slice term

The envelope `(1/√(2π s)) · exp(-x²/(2s))` with `s = Gdom.varSq/2` is `c`-independent;
it decays strictly faster than every slice's dominant term (whose variance is
`Gdom.varSq + c ≥ Gdom.varSq > s`). We bound it uniformly by any prescribed multiple of
the dominant term. -/

/-- Uniform lower bound on the dominant slice normalizing constant. -/
private theorem snorm_dom_ge (Gdom : GaussianPDF) (c_max : ℝ) (hc_max : 0 < c_max)
    {c : ℝ} (hc0 : 0 ≤ c) (hccmax : c ≤ c_max) :
    1 / Real.sqrt (2 * Real.pi * (Gdom.varSq + c_max)) ≤ snorm Gdom c := by
  unfold snorm
  have hpi := Real.pi_pos
  have hDv := Gdom.varSq_pos
  apply one_div_le_one_div_of_le
  · positivity
  · apply Real.sqrt_le_sqrt; nlinarith [hpi, hDv, hc0, hccmax, hDv.le]

/-- **Right-tail fixed-envelope uniform bound.** For `s = Gdom.varSq/2` and prescribed
`κ > 0`, there is a single `T` with `(1/√(2π s)) exp(-x²/(2s)) ≤ κ · (snorm Gdom c ·
sgexp Gdom c x)` for all `c ∈ [0, c_max]` and `x ≥ T`. -/
private theorem envelope_uniform_bound_right (Gdom : GaussianPDF)
    (c_max : ℝ) (hc_max : 0 < c_max) (κ : ℝ) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, T ≤ x →
      (1 / Real.sqrt (2 * Real.pi * (Gdom.varSq / 2)))
          * Real.exp (-x ^ 2 / (2 * (Gdom.varSq / 2)))
        ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
  have hDv : 0 < Gdom.varSq := Gdom.varSq_pos
  set s : ℝ := Gdom.varSq / 2 with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; linarith
  set Knv : ℝ := 1 / Real.sqrt (2 * Real.pi * s) with hKnv_def
  have hKnv_pos : 0 < Knv := by rw [hKnv_def]; have := Real.pi_pos; positivity
  set snmin : ℝ := 1 / Real.sqrt (2 * Real.pi * (Gdom.varSq + c_max)) with hsnmin_def
  have hsnmin_pos : 0 < snmin := by rw [hsnmin_def]; have := Real.pi_pos; positivity
  set ρ : ℝ := κ * snmin / Knv with hρ_def
  have hρ_pos : 0 < ρ := by rw [hρ_def]; positivity
  set M : ℝ := max (Real.log (1 / ρ)) 0 with hM_def
  have hM_nn : 0 ≤ M := le_max_right _ _
  have hexpM : Real.exp (-M) ≤ ρ := by
    have hMge : Real.log (1 / ρ) ≤ M := le_max_left _ _
    have hpos : 0 < 1 / ρ := by positivity
    have hstep : Real.exp (-M) ≤ Real.exp (-(Real.log (1 / ρ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(Real.log (1 / ρ))) = ρ := by
      rw [Real.exp_neg, Real.exp_log hpos, one_div, inv_inv]
    rwa [hval] at hstep
  set q : ℝ := 1 / (4 * Gdom.varSq) with hq_def
  have hq_pos : 0 < q := by rw [hq_def]; positivity
  set B : ℝ := |Gdom.mean| / Gdom.varSq with hB_def
  set C : ℝ := Gdom.mean ^ 2 / (2 * Gdom.varSq) with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
  refine ⟨max 1 ((B + C + M + 1) / q + 1), ?_⟩
  intro c hc0 hccmax x hxT
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hxT
  have hxT' : (B + C + M + 1) / q + 1 ≤ x := le_trans (le_max_right _ _) hxT
  have hvd' : 0 < Gdom.varSq + c := by linarith
  have hsnorm_pos : 0 < snorm Gdom c := snorm_pos Gdom hc0
  have hsgexp_pos : 0 < sgexp Gdom c x := sgexp_pos Gdom c x
  have hdiff : (-x ^ 2 / (2 * s)) - (-(x - Gdom.mean) ^ 2 / (2 * (Gdom.varSq + c)))
      = (1 / (2 * (Gdom.varSq + c)) - 1 / (2 * s)) * x ^ 2
        + (- Gdom.mean / (Gdom.varSq + c)) * x
        + (Gdom.mean ^ 2 / (2 * (Gdom.varSq + c))) := by
    have h1 : (2 * s) ≠ 0 := by positivity
    have h2 : (2 * (Gdom.varSq + c)) ≠ 0 := by positivity
    field_simp
    ring
  set α : ℝ := 1 / (2 * (Gdom.varSq + c)) - 1 / (2 * s) with hα_def
  set β : ℝ := - Gdom.mean / (Gdom.varSq + c) with hβ_def
  set γ : ℝ := Gdom.mean ^ 2 / (2 * (Gdom.varSq + c)) with hγ_def
  have hα_le : α ≤ -q := by
    rw [hα_def, hq_def]
    have ha1 : 1 / (2 * (Gdom.varSq + c)) ≤ 1 / (2 * Gdom.varSq) := by
      apply one_div_le_one_div_of_le (by positivity); linarith
    have ha2 : 1 / (2 * s) = 1 / Gdom.varSq := by
      rw [hs_def]; rw [show 2 * (Gdom.varSq / 2) = Gdom.varSq by ring]
    rw [ha2]
    have hVne : Gdom.varSq ≠ 0 := ne_of_gt hDv
    have h3 : 1 / (2 * Gdom.varSq) - 1 / Gdom.varSq = - (1 / (2 * Gdom.varSq)) := by
      field_simp
      ring
    have hle1 : 1 / (2 * (Gdom.varSq + c)) - 1 / Gdom.varSq
        ≤ -(1 / (4 * Gdom.varSq)) := by
      have hstep2 : 1 / (2 * (Gdom.varSq + c)) - 1 / Gdom.varSq
          ≤ 1 / (2 * Gdom.varSq) - 1 / Gdom.varSq := by linarith [ha1]
      rw [h3] at hstep2
      have hmono : -(1 / (2 * Gdom.varSq)) ≤ -(1 / (4 * Gdom.varSq)) := by
        apply neg_le_neg
        apply one_div_le_one_div_of_le (by positivity); linarith
      linarith [hstep2, hmono]
    linarith [hle1]
  have hβ_abs : |β| ≤ B := by
    rw [hβ_def, hB_def, abs_div, abs_neg, abs_of_pos hvd']
    apply div_le_div_of_nonneg_left (abs_nonneg _) hDv; linarith
  have hγ_abs : |γ| ≤ C := by
    rw [hγ_def, hC_def, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity); linarith
  have hquad : α * x ^ 2 + β * x + γ ≤ -M :=
    quad_le_neg_of_large α β γ q B C M hα_le hq_pos hβ_abs hγ_abs hC_nn hM_nn x hx1 hxT'
  have hdiff_le : (-x ^ 2 / (2 * s))
      - (-(x - Gdom.mean) ^ 2 / (2 * (Gdom.varSq + c))) ≤ -M := by
    rw [hdiff]; exact hquad
  have hexp_le : Real.exp (-x ^ 2 / (2 * s)) ≤ Real.exp (-M) * sgexp Gdom c x := by
    unfold sgexp
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hdiff_le]
  have hsnlb : snmin ≤ snorm Gdom c := snorm_dom_ge Gdom c_max hc_max hc0 hccmax
  show Knv * Real.exp (-x ^ 2 / (2 * s)) ≤ κ * (snorm Gdom c * sgexp Gdom c x)
  calc Knv * Real.exp (-x ^ 2 / (2 * s))
      ≤ Knv * (Real.exp (-M) * sgexp Gdom c x) :=
        mul_le_mul_of_nonneg_left hexp_le (le_of_lt hKnv_pos)
    _ ≤ Knv * (ρ * sgexp Gdom c x) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hKnv_pos)
        exact mul_le_mul_of_nonneg_right hexpM (le_of_lt hsgexp_pos)
    _ = (κ * snmin) * sgexp Gdom c x := by
        have hKnv_ne : Knv ≠ 0 := ne_of_gt hKnv_pos
        rw [hρ_def]
        field_simp
    _ ≤ (κ * snorm Gdom c) * sgexp Gdom c x := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hsgexp_pos)
        exact mul_le_mul_of_nonneg_left hsnlb (le_of_lt hκ)
    _ = κ * (snorm Gdom c * sgexp Gdom c x) := by ring

/-- **Left-tail fixed-envelope uniform bound** (reflection). -/
private theorem envelope_uniform_bound_left (Gdom : GaussianPDF)
    (c_max : ℝ) (hc_max : 0 < c_max) (κ : ℝ) (hκ : 0 < κ) :
    ∃ T : ℝ, ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x : ℝ, x ≤ T →
      (1 / Real.sqrt (2 * Real.pi * (Gdom.varSq / 2)))
          * Real.exp (-x ^ 2 / (2 * (Gdom.varSq / 2)))
        ≤ κ * (snorm Gdom c * sgexp Gdom c x) := by
  -- reflect Gdom's mean
  set Gref : GaussianPDF := ⟨-Gdom.mean, Gdom.varSq, Gdom.varSq_pos⟩ with hGref_def
  obtain ⟨T, hT⟩ := envelope_uniform_bound_right Gref c_max hc_max κ hκ
  refine ⟨-T, ?_⟩
  intro c hc0 hccmax x hxT
  have hyT : T ≤ -x := by linarith
  have := hT c hc0 hccmax (-x) hyT
  -- rewrite Gref.varSq = Gdom.varSq, and sgexp/snorm under reflection
  have hsnref : snorm Gref c = snorm Gdom c := by unfold snorm; rw [hGref_def]
  have hsgref : sgexp Gref c (-x) = sgexp Gdom c x := by
    unfold sgexp; rw [hGref_def]; congr 2; ring
  have hvar : Gref.varSq = Gdom.varSq := by rw [hGref_def]
  have hxsq : (-x) ^ 2 = x ^ 2 := by ring
  rw [hsnref, hsgref, hvar, hxsq] at this
  exact this

/-! ## Per-tail uniform envelope (reduced combination) -/

/-- **Right-tail uniform envelope for a reduced combination.** Given a dominant `G`
covering the right-tail residual of `S'` with nonzero top-group sum `A`, there is a
single threshold `b'` such that for all `c ∈ (0, c_max]` and `x > b'`, `fFamU S' c x`
is sign-aligned with `A` and strictly dominates the `(G.varSq/2)`-envelope with
coefficient `A`. -/
private theorem reduced_envelope_right (S' : SignedGaussianCombination) (G : GaussianPDF)
    (c_max : ℝ) (hc_max : 0 < c_max)
    (hcov : ∀ p ∈ restB G S', p.1 = 0 ∨ belowB G p)
    (hA : topCoeffSumB G S' ≠ 0) :
    ∃ b' : ℝ, ∀ c : ℝ, 0 < c → c ≤ c_max → ∀ x : ℝ, x > b' →
      (fFamU S' c x).sign = (topCoeffSumB G S').sign ∧
      |topCoeffSumB G S'| * (1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
          * Real.exp (-x ^ 2 / (2 * (G.varSq / 2))) < |fFamU S' c x| := by
  set A := topCoeffSumB G S' with hA_def
  have hAabs : 0 < |A| := abs_pos.mpr hA
  obtain ⟨Tr, hTr⟩ := listSum_uniform_bound_right G c_max hc_max (restB G S') hcov
    (|A| / 4) (by positivity)
  obtain ⟨Te, hTe⟩ := envelope_uniform_bound_right G c_max hc_max (1 / 2) (by norm_num)
  refine ⟨max Tr Te, ?_⟩
  intro c hcpos hccmax x hxgt
  have hc0 : 0 ≤ c := le_of_lt hcpos
  have hxr : Tr ≤ x := le_trans (le_max_left _ _) (le_of_lt hxgt)
  have hxe : Te ≤ x := le_trans (le_max_right _ _) (le_of_lt hxgt)
  -- abbreviations
  set Dom : ℝ := snorm G c * sgexp G c x with hDom_def
  have hDom_pos : 0 < Dom := mul_pos (snorm_pos G hc0) (sgexp_pos G c x)
  -- the split
  have hsplit : fFamU S' c x = A * Dom
      + ((restB G S').map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum := by
    rw [fFamU_split S' G c hcpos x, hDom_def, hA_def]
  set R : ℝ := ((restB G S').map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum with hR_def
  have hRbound : |R| ≤ (|A| / 4) * Dom := by
    have := hTr c hc0 hccmax x hxr
    rw [hDom_def]; exact this
  -- |fFamU| ≥ (3/4)|A| Dom
  have hfabs_lb : (3 / 4) * (|A| * Dom) ≤ |fFamU S' c x| := by
    have h1 : |A * Dom| - |R| ≤ |fFamU S' c x| := by
      have htri := abs_sub_abs_le_abs_sub (A * Dom) (A * Dom - fFamU S' c x)
      have hrw : A * Dom - (A * Dom - fFamU S' c x) = fFamU S' c x := by ring
      rw [hrw] at htri
      have hAD_minus : A * Dom - fFamU S' c x = -R := by rw [hsplit]; ring
      rw [hAD_minus, abs_neg] at htri
      exact htri
    have hADabs : |A * Dom| = |A| * Dom := by
      rw [abs_mul, abs_of_pos hDom_pos]
    rw [hADabs] at h1
    nlinarith [h1, hRbound, hAabs, hDom_pos]
  -- sign
  have hsign : (fFamU S' c x).sign = A.sign := by
    have hRlt : |R| < |A| * Dom := by nlinarith [hRbound, hAabs, hDom_pos]
    rcases lt_trichotomy A 0 with hAneg | hAzero | hApos
    · have hsd_neg : fFamU S' c x < 0 := by
        have hADneg : A * Dom < 0 := mul_neg_of_neg_of_pos hAneg hDom_pos
        have hR2 : |R| < -(A * Dom) := by
          rw [abs_of_neg hAneg] at hRlt; nlinarith [hRlt, hDom_pos]
        have := abs_lt.mp hR2
        rw [hsplit]; linarith [this.2]
      rw [Real.sign_of_neg hsd_neg, Real.sign_of_neg hAneg]
    · exact absurd hAzero hA
    · have hsd_pos : 0 < fFamU S' c x := by
        have hADpos : 0 < A * Dom := mul_pos hApos hDom_pos
        have hR2 : |R| < A * Dom := by
          rw [abs_of_pos hApos] at hRlt; nlinarith [hRlt, hDom_pos]
        have := abs_lt.mp hR2
        rw [hsplit]; linarith [this.1]
      rw [Real.sign_of_pos hsd_pos, Real.sign_of_pos hApos]
  refine ⟨hsign, ?_⟩
  -- magnitude
  have hEnv : (1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
      * Real.exp (-x ^ 2 / (2 * (G.varSq / 2))) ≤ (1 / 2) * Dom := by
    have := hTe c hc0 hccmax x hxe
    rw [hDom_def]; exact this
  have hmag : |A| * ((1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
        * Real.exp (-x ^ 2 / (2 * (G.varSq / 2))))
      ≤ |A| * ((1 / 2) * Dom) :=
    mul_le_mul_of_nonneg_left hEnv (le_of_lt hAabs)
  have hchain : |A| * ((1 / 2) * Dom) < (3 / 4) * (|A| * Dom) := by
    nlinarith [hAabs, hDom_pos]
  calc |A| * (1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
        * Real.exp (-x ^ 2 / (2 * (G.varSq / 2)))
      = |A| * ((1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
          * Real.exp (-x ^ 2 / (2 * (G.varSq / 2)))) := by ring
    _ ≤ |A| * ((1 / 2) * Dom) := hmag
    _ < (3 / 4) * (|A| * Dom) := hchain
    _ ≤ |fFamU S' c x| := hfabs_lb

/-- **Left-tail uniform envelope for a reduced combination.** Mirror of
`reduced_envelope_right`. -/
private theorem reduced_envelope_left (S' : SignedGaussianCombination) (G : GaussianPDF)
    (c_max : ℝ) (hc_max : 0 < c_max)
    (hcov : ∀ p ∈ restB G S', p.1 = 0 ∨ belowBL G p)
    (hA : topCoeffSumB G S' ≠ 0) :
    ∃ b : ℝ, ∀ c : ℝ, 0 < c → c ≤ c_max → ∀ x : ℝ, x < b →
      (fFamU S' c x).sign = (topCoeffSumB G S').sign ∧
      |topCoeffSumB G S'| * (1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
          * Real.exp (-x ^ 2 / (2 * (G.varSq / 2))) < |fFamU S' c x| := by
  set A := topCoeffSumB G S' with hA_def
  have hAabs : 0 < |A| := abs_pos.mpr hA
  obtain ⟨Tr, hTr⟩ := listSum_uniform_bound_left G c_max hc_max (restB G S') hcov
    (|A| / 4) (by positivity)
  obtain ⟨Te, hTe⟩ := envelope_uniform_bound_left G c_max hc_max (1 / 2) (by norm_num)
  refine ⟨min Tr Te, ?_⟩
  intro c hcpos hccmax x hxlt
  have hc0 : 0 ≤ c := le_of_lt hcpos
  have hxr : x ≤ Tr := le_trans (le_of_lt hxlt) (min_le_left _ _)
  have hxe : x ≤ Te := le_trans (le_of_lt hxlt) (min_le_right _ _)
  set Dom : ℝ := snorm G c * sgexp G c x with hDom_def
  have hDom_pos : 0 < Dom := mul_pos (snorm_pos G hc0) (sgexp_pos G c x)
  have hsplit : fFamU S' c x = A * Dom
      + ((restB G S').map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum := by
    rw [fFamU_split S' G c hcpos x, hDom_def, hA_def]
  set R : ℝ := ((restB G S').map (fun p => p.1 * (snorm p.2 c * sgexp p.2 c x))).sum with hR_def
  have hRbound : |R| ≤ (|A| / 4) * Dom := by
    have := hTr c hc0 hccmax x hxr
    rw [hDom_def]; exact this
  have hfabs_lb : (3 / 4) * (|A| * Dom) ≤ |fFamU S' c x| := by
    have h1 : |A * Dom| - |R| ≤ |fFamU S' c x| := by
      have htri := abs_sub_abs_le_abs_sub (A * Dom) (A * Dom - fFamU S' c x)
      have hrw : A * Dom - (A * Dom - fFamU S' c x) = fFamU S' c x := by ring
      rw [hrw] at htri
      have hAD_minus : A * Dom - fFamU S' c x = -R := by rw [hsplit]; ring
      rw [hAD_minus, abs_neg] at htri
      exact htri
    have hADabs : |A * Dom| = |A| * Dom := by
      rw [abs_mul, abs_of_pos hDom_pos]
    rw [hADabs] at h1
    nlinarith [h1, hRbound, hAabs, hDom_pos]
  have hsign : (fFamU S' c x).sign = A.sign := by
    have hRlt : |R| < |A| * Dom := by nlinarith [hRbound, hAabs, hDom_pos]
    rcases lt_trichotomy A 0 with hAneg | hAzero | hApos
    · have hsd_neg : fFamU S' c x < 0 := by
        have hADneg : A * Dom < 0 := mul_neg_of_neg_of_pos hAneg hDom_pos
        have hR2 : |R| < -(A * Dom) := by
          rw [abs_of_neg hAneg] at hRlt; nlinarith [hRlt, hDom_pos]
        have := abs_lt.mp hR2
        rw [hsplit]; linarith [this.2]
      rw [Real.sign_of_neg hsd_neg, Real.sign_of_neg hAneg]
    · exact absurd hAzero hA
    · have hsd_pos : 0 < fFamU S' c x := by
        have hADpos : 0 < A * Dom := mul_pos hApos hDom_pos
        have hR2 : |R| < A * Dom := by
          rw [abs_of_pos hApos] at hRlt; nlinarith [hRlt, hDom_pos]
        have := abs_lt.mp hR2
        rw [hsplit]; linarith [this.1]
      rw [Real.sign_of_pos hsd_pos, Real.sign_of_pos hApos]
  refine ⟨hsign, ?_⟩
  have hEnv : (1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
      * Real.exp (-x ^ 2 / (2 * (G.varSq / 2))) ≤ (1 / 2) * Dom := by
    have := hTe c hc0 hccmax x hxe
    rw [hDom_def]; exact this
  have hmag : |A| * ((1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
        * Real.exp (-x ^ 2 / (2 * (G.varSq / 2))))
      ≤ |A| * ((1 / 2) * Dom) :=
    mul_le_mul_of_nonneg_left hEnv (le_of_lt hAabs)
  have hchain : |A| * ((1 / 2) * Dom) < (3 / 4) * (|A| * Dom) := by
    nlinarith [hAabs, hDom_pos]
  calc |A| * (1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
        * Real.exp (-x ^ 2 / (2 * (G.varSq / 2)))
      = |A| * ((1 / Real.sqrt (2 * Real.pi * (G.varSq / 2)))
          * Real.exp (-x ^ 2 / (2 * (G.varSq / 2)))) := by ring
    _ ≤ |A| * ((1 / 2) * Dom) := hmag
    _ < (3 / 4) * (|A| * Dom) := hchain
    _ ≤ |fFamU S' c x| := hfabs_lb

/-! ## Headline: band-uniform two-sided envelope -/

/-- **Band-uniform Gaussian-tail envelope for the normalized convolution family.**
For `S` with somewhere-nonzero density and any band width `c_max > 0`, there is a SINGLE
envelope tuple `(b, b', a, a', s, s')` with `b < b'`, `a, a' ≠ 0`, `s, s' > 0` such that
for ALL `c ∈ (0, c_max]` the slice `fFamU S c` is sign-aligned with `a` and dominates the
`s`-envelope on the left tail `x < b`, and sign-aligned with `a'` and dominates the
`s'`-envelope on the right tail `x > b'`. -/
theorem convFamilyUniformEnvelope
    (S : SignedGaussianCombination)
    (hS_ne : ∃ x, S.density x ≠ 0)
    (c_max : ℝ) (hc_max : 0 < c_max) :
    ∃ b b' a a' s s' : ℝ, b < b' ∧ a ≠ 0 ∧ a' ≠ 0 ∧ 0 < s ∧ 0 < s' ∧
      ∀ c : ℝ, 0 < c → c ≤ c_max →
        (∀ x : ℝ, x < b →
            (fFamU S c x).sign = a.sign ∧
            |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x ^ 2 / (2 * s)) <
              |fFamU S c x|) ∧
        (∀ x : ℝ, x > b' →
            (fFamU S c x).sign = a'.sign ∧
            |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x ^ 2 / (2 * s')) <
              |fFamU S c x|) := by
  -- Reductions to combinations with nonzero top-group sum (same fFamU slices).
  obtain ⟨SL, Gl, hfamL, hcovL, hAL⟩ :=
    exists_reducedB_left S.components.length S le_rfl hS_ne
  obtain ⟨SR, Gr, hfamR, hcovR, hAR⟩ :=
    exists_reducedB_right S.components.length S le_rfl hS_ne
  obtain ⟨bL, hbL⟩ := reduced_envelope_left SL Gl c_max hc_max hcovL hAL
  obtain ⟨bR, hbR⟩ := reduced_envelope_right SR Gr c_max hc_max hcovR hAR
  have hGLpos := Gl.varSq_pos
  have hGRpos := Gr.varSq_pos
  have hbb : min bL bR - 1 < max bL bR + 1 := by
    have : min bL bR ≤ max bL bR := min_le_max
    linarith
  refine ⟨min bL bR - 1, max bL bR + 1,
    topCoeffSumB Gl SL, topCoeffSumB Gr SR, Gl.varSq / 2, Gr.varSq / 2,
    hbb, hAL, hAR, by linarith, by linarith, ?_⟩
  intro c hcpos hccmax
  refine ⟨?_, ?_⟩
  · intro x hx
    have hxbL : x < bL := by
      have : min bL bR ≤ bL := min_le_left _ _; linarith
    have hres := hbL c hcpos hccmax x hxbL
    rw [hfamL c hcpos x] at hres
    exact hres
  · intro x hx
    have hxbR : x > bR := by
      have : bR ≤ max bL bR := le_max_right _ _; linarith
    have hres := hbR c hcpos hccmax x hxbR
    rw [hfamR c hcpos x] at hres
    exact hres

end Workspace.ProofLemmas
