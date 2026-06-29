import Mathlib
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianPDF

/-!
# `HurwitzGaussianPerturbationTailDominance` — genuine proof (region (a))

This replaces the prior-work axiom of the same name by a real proof.

Paper §6.1, tail conditions (page 19, lines 253–254):
  - For `x < b`:  `|a · N(0,s,x)| > |a_k · N(μ_k,v,x)|`
  - For `x > b'`: `|a' · N(0,s',x)| > |a_k · N(μ_k,v,x)|`
once `v` is small enough.  Combined with the envelope hypotheses
`|a·N(0,s,x)| < |g x|` (resp. `|a'·N(0,s',x)| < |g x|`), this forces
`|a_k·N(μ_k,v,x)| < |g x|` on the tails, so `g + a_k·N(μ_k,v,·)` cannot
vanish there; every zero lies in `[b,b']`.

FULLY PROVED (Mathlib-only axioms).  The structural reduction (envelope
domination ⇒ no tail zero ⇒ zeroSet ⊆ [b,b']) plus the two analytic
Gaussian-ratio tail-comparison bounds (`tail_left_dom`, `tail_right_dom`,
each built from the SOS `exponent_bound` and the elementary `exp_decay_over_sqrt`).

SOUNDNESS NOTE: this theorem adds the hypotheses `b < μ_k < b'` (μ_k strictly
inside [b,b']), which the prior-work axiom of the same name omitted.  They are
mathematically necessary — see the per-theorem note below.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.ZeroCount
open Workspace.Types.GaussianPDF

set_option maxHeartbeats 1000000

/-- Elementary decay: `exp(-(c/v))/√v ≤ 2v²/c²/√v` for `c,v > 0`.
Uses `(c/v)²/2 ≤ exp(c/v)` (`Real.pow_div_factorial_le_exp` with `n = 2`). -/
private lemma exp_decay_over_sqrt (c : ℝ) (hc : 0 < c) (v : ℝ) (hv : 0 < v) :
    Real.exp (-(c / v)) / Real.sqrt v ≤ 2 * v ^ 2 / c ^ 2 / Real.sqrt v := by
  have ht : 0 ≤ c / v := le_of_lt (div_pos hc hv)
  have hkey : (c / v) ^ 2 / (Nat.factorial 2) ≤ Real.exp (c / v) :=
    Real.pow_div_factorial_le_exp (c / v) ht 2
  have hfact : (Nat.factorial 2 : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hfact] at hkey
  have hexp_pos : 0 < Real.exp (c / v) := Real.exp_pos _
  have hexp_neg : Real.exp (-(c / v)) = 1 / Real.exp (c / v) := by
    rw [Real.exp_neg]; ring
  have hbound : Real.exp (-(c / v)) ≤ 2 * v ^ 2 / c ^ 2 := by
    rw [hexp_neg]
    have hcvsq : (c / v) ^ 2 = c ^ 2 / v ^ 2 := by ring
    rw [hcvsq] at hkey
    have hlb : c ^ 2 / (2 * v ^ 2) ≤ Real.exp (c / v) := by
      have : c ^ 2 / v ^ 2 / 2 = c ^ 2 / (2 * v ^ 2) := by ring
      rwa [this] at hkey
    have hcvpos : 0 < c ^ 2 / (2 * v ^ 2) := by positivity
    have hinv : 1 / Real.exp (c / v) ≤ 1 / (c ^ 2 / (2 * v ^ 2)) :=
      one_div_le_one_div_of_le hcvpos hlb
    have heq : 1 / (c ^ 2 / (2 * v ^ 2)) = 2 * v ^ 2 / c ^ 2 := by rw [one_div_div]
    rwa [heq] at hinv
  have hsv : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  gcongr

/-- Pointwise exponent bound: for `v ≤ s/2` and `μ_k - x ≥ d > 0`,
`x²/(2s) - (x-μ_k)²/(2v) ≤ 3μ_k²/(2s) - d²/(8v)`.  Proved by the exact SOS
identity `(s-v)·P = 8v(s-v)(μ_k+(μ_k-x)/2)² + 2(s-v)(2s-3v)(μ_k-x)² - sd²(s-v)`. -/
private lemma exponent_bound (s : ℝ) (hs : 0 < s) (μ_k d v x : ℝ)
    (hd : 0 < d) (hv : 0 < v) (hv2 : v ≤ s / 2) (hu : d ≤ μ_k - x) :
    x ^ 2 / (2 * s) - (x - μ_k) ^ 2 / (2 * v)
      ≤ 3 * μ_k ^ 2 / (2 * s) - d ^ 2 / (8 * v) := by
  have hu_pos : 0 < μ_k - x := lt_of_lt_of_le hd hu
  have hu_ge : d ^ 2 ≤ (μ_k - x) ^ 2 := by nlinarith [hu_pos, hd]
  have hvpos : 0 < v := hv
  have hsv : 0 < s - v := by linarith
  have hud : 0 ≤ (μ_k - x) - d := by linarith
  have hP2s3v : 0 < 2 * s - 3 * v := by linarith
  have hsP :
      0 ≤ (s - v) * (12 * μ_k ^ 2 * v + 4 * s * (x - μ_k) ^ 2 - 4 * v * x ^ 2 - s * d ^ 2) := by
    have hA : 0 ≤ 2 * v * (s - v) * (2 * μ_k + (μ_k - x)) ^ 2 := by positivity
    have hB : 0 ≤ 2 * (s - v) * (2 * s - 3 * v) * ((μ_k - x) ^ 2 - d ^ 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hu_ge)
    have hC : 0 ≤ (s - v) * d ^ 2 * (3 * s - 6 * v) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [hA, hB, hC]
  have hcleared :
      0 ≤ 12 * μ_k ^ 2 * v + 4 * s * (x - μ_k) ^ 2 - 4 * v * x ^ 2 - s * d ^ 2 :=
    nonneg_of_mul_nonneg_right hsP hsv
  rw [sub_le_sub_iff,
      div_add_div _ _ (by positivity : (2*s) ≠ 0) (by positivity : (8*v) ≠ 0),
      div_add_div _ _ (by positivity : (2*s) ≠ 0) (by positivity : (2*v) ≠ 0),
      div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hcleared, mul_pos hvpos hs, mul_pos hs hs, mul_pos hvpos hvpos,
    mul_pos (mul_pos hvpos hs) (mul_pos hvpos hs)]

/-- The Gaussian-ratio tail-comparison bound on the LEFT tail.
For `v` small enough, `|a_k| · N(μ_k,v,x) ≤ |a| · N(0,s,x)` for all `x < b`.
The hypothesis `b < μ_k` is ESSENTIAL: at `x = μ_k` the perturbation Gaussian
peaks at height `1/√(2πv) → ∞`, beating any fixed envelope. -/
private lemma tail_left_dom
    (b a s : ℝ) (ha : a ≠ 0) (hs : 0 < s)
    (a_k : ℝ) (μ_k : ℝ) (hbμ : b < μ_k) :
    ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ ≤ s ∧
      ∀ v : ℝ, 0 < v → v ≤ v₀ →
        ∀ x : ℝ, x < b →
          |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v))
            ≤ |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) := by
  set d := μ_k - b with hd_def
  have hd_pos : 0 < d := by rw [hd_def]; linarith
  set M : ℝ := 3 * μ_k ^ 2 / (2 * s) with hM_def
  set c : ℝ := d ^ 2 / 8 with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  have habs_a : 0 < |a| := abs_pos.mpr ha
  have hsqs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  set Kbig : ℝ := 128 * (|a_k| + 1) * Real.exp M * Real.sqrt s / d ^ 4 with hK_def
  have hKbig_pos : 0 < Kbig := by rw [hK_def]; positivity
  set v₀ : ℝ := min (min (s / 2) 1) (|a| / Kbig) with hv0_def
  have hv0_pos : 0 < v₀ := by
    rw [hv0_def]
    apply lt_min (lt_min (by linarith) (by norm_num))
    exact div_pos habs_a hKbig_pos
  refine ⟨v₀, hv0_pos, ?_, ?_⟩
  · rw [hv0_def]
    calc min (min (s / 2) 1) (|a| / Kbig) ≤ min (s / 2) 1 := min_le_left _ _
      _ ≤ s / 2 := min_le_left _ _
      _ ≤ s := by linarith
  intro v hv hv_le x hx
  have hv_le_s2 : v ≤ s / 2 := le_trans hv_le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hv_le_1 : v ≤ 1 := le_trans hv_le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hv_le_K : v ≤ |a| / Kbig := le_trans hv_le (min_le_right _ _)
  have hud : d ≤ μ_k - x := by rw [hd_def]; linarith
  have hexp_le : x ^ 2 / (2 * s) - (x - μ_k) ^ 2 / (2 * v) ≤ M - d ^ 2 / (8 * v) := by
    rw [hM_def]; exact exponent_bound s hs μ_k d v x hd_pos hv hv_le_s2 hud
  have hexp_le2 : -(x - μ_k) ^ 2 / (2 * v) ≤ M - d ^ 2 / (8 * v) - x ^ 2 / (2 * s) := by
    have : -(x - μ_k) ^ 2 / (2 * v)
        = (x ^ 2 / (2 * s) - (x - μ_k) ^ 2 / (2 * v)) - x ^ 2 / (2 * s) := by ring
    rw [this]; linarith [hexp_le]
  have hExp : Real.exp (-(x - μ_k) ^ 2 / (2 * v))
      ≤ Real.exp M * Real.exp (-(d ^ 2 / (8 * v))) * Real.exp (-x ^ 2 / (2 * s)) := by
    have := Real.exp_le_exp_of_le hexp_le2
    rw [show M - d ^ 2 / (8 * v) - x ^ 2 / (2 * s)
          = M + (-(d ^ 2 / (8 * v))) + (-x ^ 2 / (2 * s)) by ring,
        Real.exp_add, Real.exp_add] at this
    convert this using 2
  have hcv : c / v = d ^ 2 / (8 * v) := by rw [hc_def]; field_simp
  have hdecay : Real.exp (-(d ^ 2 / (8 * v))) / Real.sqrt v ≤ 2 * v ^ 2 / c ^ 2 / Real.sqrt v := by
    have := exp_decay_over_sqrt c hc_pos v hv
    rwa [hcv] at this
  have hsqv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hexpM_pos : 0 < Real.exp M := Real.exp_pos _
  have habs_ak : 0 ≤ |a_k| := abs_nonneg _
  have h2pi_nn : (0:ℝ) ≤ 2 * Real.pi := by positivity
  have hsplit_v : Real.sqrt (2 * Real.pi * v) = Real.sqrt (2 * Real.pi) * Real.sqrt v :=
    Real.sqrt_mul h2pi_nn v
  have hsplit_s : Real.sqrt (2 * Real.pi * s) = Real.sqrt (2 * Real.pi) * Real.sqrt s :=
    Real.sqrt_mul h2pi_nn s
  have hsqrt2pi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hv32 : 2 * v ^ 2 / c ^ 2 / Real.sqrt v ≤ 2 * v / c ^ 2 := by
    have hvsqrt : v ^ 2 / Real.sqrt v = v * Real.sqrt v := by
      rw [div_eq_iff (ne_of_gt hsqv), mul_assoc, Real.mul_self_sqrt hv.le, sq]
    have hstep : 2 * v ^ 2 / c ^ 2 / Real.sqrt v = (2 / c ^ 2) * (v * Real.sqrt v) := by
      rw [← hvsqrt]; field_simp
    rw [hstep]
    have hsqrt_le : Real.sqrt v ≤ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hv_le_1
    have h2c : 0 < 2 / c ^ 2 := by positivity
    calc (2 / c ^ 2) * (v * Real.sqrt v) ≤ (2 / c ^ 2) * (v * 1) := by
            apply mul_le_mul_of_nonneg_left _ h2c.le
            exact mul_le_mul_of_nonneg_left hsqrt_le hv.le
      _ = 2 * v / c ^ 2 := by ring
  have hdecay2 : Real.exp (-(d ^ 2 / (8 * v))) / Real.sqrt v ≤ 2 * v / c ^ 2 :=
    le_trans hdecay hv32
  have hc2 : c ^ 2 = d ^ 4 / 64 := by rw [hc_def]; ring
  have hd4_pos : 0 < d ^ 4 := by positivity
  have hKey : |a_k| * Real.exp M * (Real.exp (-(d ^ 2 / (8 * v))) / Real.sqrt v)
      ≤ |a| / Real.sqrt s := by
    have hstep1 : |a_k| * Real.exp M * (Real.exp (-(d ^ 2 / (8 * v))) / Real.sqrt v)
        ≤ |a_k| * Real.exp M * (2 * v / c ^ 2) := by
      apply mul_le_mul_of_nonneg_left hdecay2; positivity
    refine le_trans hstep1 ?_
    rw [hc2, le_div_iff₀ hsqs]
    have hvK : v * Kbig ≤ |a| := by
      rw [le_div_iff₀ hKbig_pos] at hv_le_K; linarith [hv_le_K]
    have hvK' : v * (128 * (|a_k| + 1) * Real.exp M * Real.sqrt s) ≤ |a| * d ^ 4 := by
      rw [hK_def] at hvK
      have hrw : v * (128 * (|a_k| + 1) * Real.exp M * Real.sqrt s / d ^ 4)
          = (v * (128 * (|a_k| + 1) * Real.exp M * Real.sqrt s)) / d ^ 4 := by ring
      rw [hrw, div_le_iff₀ hd4_pos] at hvK; exact hvK
    have hLrw : |a_k| * Real.exp M * (2 * v / (d ^ 4 / 64)) * Real.sqrt s
        = (v * (128 * |a_k| * Real.exp M * Real.sqrt s)) / d ^ 4 := by field_simp; ring
    rw [hLrw, div_le_iff₀ hd4_pos]
    nlinarith [hvK', hexpM_pos, hsqs, hv, habs_ak,
      mul_nonneg (mul_nonneg hv.le hexpM_pos.le) hsqs.le]
  rw [hsplit_v, hsplit_s]
  have hLHS_le : |a_k| * (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt v)) *
        Real.exp (-(x - μ_k) ^ 2 / (2 * v))
      ≤ |a_k| * (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt v)) *
        (Real.exp M * Real.exp (-(d ^ 2 / (8 * v))) * Real.exp (-x ^ 2 / (2 * s))) := by
    apply mul_le_mul_of_nonneg_left hExp; positivity
  refine le_trans hLHS_le ?_
  set C : ℝ := (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-x ^ 2 / (2 * s)) with hC_def
  have hC_pos : 0 < C := by rw [hC_def]; positivity
  have hmid : |a_k| * (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt v)) *
        (Real.exp M * Real.exp (-(d ^ 2 / (8 * v))) * Real.exp (-x ^ 2 / (2 * s)))
      = C * (|a_k| * Real.exp M * (Real.exp (-(d ^ 2 / (8 * v))) / Real.sqrt v)) := by
    rw [hC_def]; field_simp
  have hmid2 : |a| * (1 / (Real.sqrt (2 * Real.pi) * Real.sqrt s)) *
        Real.exp (-x ^ 2 / (2 * s)) = C * (|a| / Real.sqrt s) := by
    rw [hC_def]; field_simp
  rw [hmid, hmid2]
  exact mul_le_mul_of_nonneg_left hKey hC_pos.le

/-- The Gaussian-ratio tail-comparison bound on the RIGHT tail (by reflection `x ↦ -x`).
The hypothesis `μ_k < b'` is ESSENTIAL (symmetric to the left tail). -/
private lemma tail_right_dom
    (b' a' s' : ℝ) (ha' : a' ≠ 0) (hs' : 0 < s')
    (a_k : ℝ) (μ_k : ℝ) (hμb' : μ_k < b') :
    ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ ≤ s' ∧
      ∀ v : ℝ, 0 < v → v ≤ v₀ →
        ∀ x : ℝ, x > b' →
          |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v))
            ≤ |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) := by
  obtain ⟨v₀, hv0_pos, hv0_le, hbound⟩ :=
    tail_left_dom (-b') a' s' ha' hs' a_k (-μ_k) (by linarith)
  refine ⟨v₀, hv0_pos, hv0_le, ?_⟩
  intro v hv hv_le x hx
  have hyx : -x < -b' := by linarith
  have hb := hbound v hv hv_le (-x) hyx
  have h1 : (-x - -μ_k) ^ 2 = (x - μ_k) ^ 2 := by ring
  have h2 : (-x) ^ 2 = x ^ 2 := by ring
  rw [h1, h2] at hb
  exact hb

/-- **Region (a): tail-Gaussian dominance** (Moitra–Valiant §6.1, page 19).

NOTE — soundness fix relative to the prior-work axiom of the same name:
this theorem carries the additional hypotheses `b < μ_k` and `μ_k < b'`
(`μ_k` strictly inside the bounded interval `[b,b']`).  These are
ESSENTIAL: the perturbation Gaussian `a_k·N(μ_k,v,·)` peaks at `μ_k` with
height `→ ∞` as `v → 0`, so on any tail region CONTAINING `μ_k` it cannot be
dominated by a fixed envelope.  The paper guarantees `b < μ_k < b'`
("Pick constants … and `b < μ_k < b'`", page 19 line 246), so this is the
faithful hypothesis.  The bare-`b<b'` axiom is false as stated. -/
theorem HurwitzGaussianPerturbationTailDominance :
    ∀ (g : ℝ → ℝ)
      (b b' a a' s s' : ℝ),
        b < b' → a ≠ 0 → a' ≠ 0 → 0 < s → 0 < s' →
        ∀ (μ_k : ℝ), b < μ_k → μ_k < b' →
        (∀ x : ℝ, x < b →
            (g x).sign = a.sign ∧
            |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) < |g x|) →
        (∀ x : ℝ, x > b' →
            (g x).sign = a'.sign ∧
            |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) < |g x|) →
        ∀ (a_k : ℝ), a_k ≠ 0 →
          ∃ v₀ : ℝ, 0 < v₀ ∧
            ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
              Workspace.Types.ZeroCount.zeroSet
                  (fun x => g x +
                    a_k *
                      Workspace.Types.GaussianPDF.GaussianPDF.density
                        ⟨μ_k, v, hv⟩ x)
                ⊆ Set.Icc b b' := by
  intro g b b' a a' s s' hbb' ha ha' hs hs' μ_k hbμ hμb' hL hR a_k ha_k
  -- Obtain the two tail-comparison thresholds.
  obtain ⟨vL, hvL_pos, _hvL_le, hvL⟩ := tail_left_dom b a s ha hs a_k μ_k hbμ
  obtain ⟨vR, hvR_pos, _hvR_le, hvR⟩ := tail_right_dom b' a' s' ha' hs' a_k μ_k hμb'
  refine ⟨min vL vR, lt_min hvL_pos hvR_pos, ?_⟩
  intro v hv hv_le
  have hv_le_L : v ≤ vL := hv_le.trans (min_le_left _ _)
  have hv_le_R : v ≤ vR := hv_le.trans (min_le_right _ _)
  -- The perturbed function.
  intro x hx
  -- `hx : (fun x => g x + a_k * N(μ_k,v,x)) x = 0`, i.e. x ∈ zeroSet.
  simp only [zeroSet, Set.mem_setOf_eq] at hx
  -- Density unfolds to the explicit Gaussian formula.
  have hdens : (GaussianPDF.density ⟨μ_k, v, hv⟩ x)
      = (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v)) := by
    rw [GaussianPDF.density_eq]
  rw [hdens] at hx
  -- Show x ∈ [b, b'] by contradiction: if x < b or x > b' then |perturbation| < |g x| = perturbation.
  rw [Set.mem_Icc]
  constructor
  · -- b ≤ x
    by_contra hxlt
    push_neg at hxlt          -- hxlt : x < b
    -- envelope at x
    obtain ⟨_hsign, hgx⟩ := hL x hxlt
    -- tail domination of perturbation by envelope
    have hpert_le : |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v))
        ≤ |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) :=
      hvL v hv hv_le_L x hxlt
    -- so |a_k * N| < |g x|
    have habs_pert : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))|
        = |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by
      have hnn : (0 : ℝ) ≤ (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by positivity
      rw [abs_mul, abs_of_nonneg hnn, ← mul_assoc]
    have hpert_lt_g : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))| < |g x| := by
      rw [habs_pert]
      calc |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
              Real.exp (-(x - μ_k)^2 / (2 * v))
          ≤ |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) := hpert_le
        _ < |g x| := hgx
    -- but g x = - a_k * N, so |g x| = |a_k * N|, contradiction with strict <.
    have hgeq : g x = - (a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))) := by linarith [hx]
    rw [hgeq, abs_neg] at hpert_lt_g
    exact lt_irrefl _ hpert_lt_g
  · -- x ≤ b'
    by_contra hxgt
    push_neg at hxgt          -- hxgt : b' < x
    obtain ⟨_hsign, hgx⟩ := hR x hxgt
    have hpert_le : |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v))
        ≤ |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) :=
      hvR v hv hv_le_R x hxgt
    have habs_pert : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))|
        = |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by
      have hnn : (0 : ℝ) ≤ (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by positivity
      rw [abs_mul, abs_of_nonneg hnn, ← mul_assoc]
    have hpert_lt_g : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))| < |g x| := by
      rw [habs_pert]
      calc |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
              Real.exp (-(x - μ_k)^2 / (2 * v))
          ≤ |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) := hpert_le
        _ < |g x| := hgx
    have hgeq : g x = - (a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))) := by linarith [hx]
    rw [hgeq, abs_neg] at hpert_lt_g
    exact lt_irrefl _ hpert_lt_g

/-- **Uniform-threshold tail dominance.**  The tail-comparison thresholds `vL, vR`
returned by `tail_left_dom`/`tail_right_dom` depend ONLY on the envelope scalars
`(b, b', a, a', s, s', a_k, μ_k)`, not on the function `g`.  So a SINGLE threshold
`v₀ = min vL vR > 0` works for EVERY `g` sharing the envelope: this exposes that
uniformity by quantifying `g` (and its per-`g` envelope clauses `hL`, `hR`) INSIDE the
existential.  This is the band-uniform region-(a) tail containment consumed by the
diagonal assembly. -/
theorem HurwitzGaussianPerturbationTailDominance_uniform
    (b b' a a' s s' : ℝ)
    (hbb' : b < b') (ha : a ≠ 0) (ha' : a' ≠ 0) (hs : 0 < s) (hs' : 0 < s')
    (μ_k : ℝ) (hbμ : b < μ_k) (hμb' : μ_k < b')
    (a_k : ℝ) (ha_k : a_k ≠ 0) :
    ∃ v₀ : ℝ, 0 < v₀ ∧
      ∀ (g : ℝ → ℝ),
        (∀ x : ℝ, x < b →
            (g x).sign = a.sign ∧
            |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) < |g x|) →
        (∀ x : ℝ, x > b' →
            (g x).sign = a'.sign ∧
            |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) < |g x|) →
        ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
          Workspace.Types.ZeroCount.zeroSet
              (fun x => g x +
                a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x)
            ⊆ Set.Icc b b' := by
  obtain ⟨vL, hvL_pos, _hvL_le, hvL⟩ := tail_left_dom b a s ha hs a_k μ_k hbμ
  obtain ⟨vR, hvR_pos, _hvR_le, hvR⟩ := tail_right_dom b' a' s' ha' hs' a_k μ_k hμb'
  refine ⟨min vL vR, lt_min hvL_pos hvR_pos, ?_⟩
  intro g hL hR v hv hv_le
  have hv_le_L : v ≤ vL := hv_le.trans (min_le_left _ _)
  have hv_le_R : v ≤ vR := hv_le.trans (min_le_right _ _)
  intro x hx
  simp only [zeroSet, Set.mem_setOf_eq] at hx
  have hdens : (GaussianPDF.density ⟨μ_k, v, hv⟩ x)
      = (1 / Real.sqrt (2 * Real.pi * v)) * Real.exp (-(x - μ_k)^2 / (2 * v)) := by
    rw [GaussianPDF.density_eq]
  rw [hdens] at hx
  rw [Set.mem_Icc]
  constructor
  · by_contra hxlt
    push_neg at hxlt
    obtain ⟨_hsign, hgx⟩ := hL x hxlt
    have hpert_le : |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v))
        ≤ |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) :=
      hvL v hv hv_le_L x hxlt
    have habs_pert : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))|
        = |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by
      have hnn : (0 : ℝ) ≤ (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by positivity
      rw [abs_mul, abs_of_nonneg hnn, ← mul_assoc]
    have hpert_lt_g : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))| < |g x| := by
      rw [habs_pert]
      calc |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
              Real.exp (-(x - μ_k)^2 / (2 * v))
          ≤ |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x^2 / (2 * s)) := hpert_le
        _ < |g x| := hgx
    have hgeq : g x = - (a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))) := by linarith [hx]
    rw [hgeq, abs_neg] at hpert_lt_g
    exact lt_irrefl _ hpert_lt_g
  · by_contra hxgt
    push_neg at hxgt
    obtain ⟨_hsign, hgx⟩ := hR x hxgt
    have hpert_le : |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v))
        ≤ |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) :=
      hvR v hv hv_le_R x hxgt
    have habs_pert : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))|
        = |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by
      have hnn : (0 : ℝ) ≤ (1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)) := by positivity
      rw [abs_mul, abs_of_nonneg hnn, ← mul_assoc]
    have hpert_lt_g : |a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))| < |g x| := by
      rw [habs_pert]
      calc |a_k| * (1 / Real.sqrt (2 * Real.pi * v)) *
              Real.exp (-(x - μ_k)^2 / (2 * v))
          ≤ |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x^2 / (2 * s')) := hpert_le
        _ < |g x| := hgx
    have hgeq : g x = - (a_k * ((1 / Real.sqrt (2 * Real.pi * v)) *
          Real.exp (-(x - μ_k)^2 / (2 * v)))) := by linarith [hx]
    rw [hgeq, abs_neg] at hpert_lt_g
    exact lt_irrefl _ hpert_lt_g

end Workspace.ProofLemmas
