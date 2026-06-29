import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FinitenessOfSignedGaussianZeros

/-!
# Sub-lemma (Step 2.5) — Moitra–Valiant §6.1 tangency splitting

Perturbing a single nonzero coefficient `a_{i₀} ↦ a_{i₀} - ε` of `S` (so
`S_ε.density = S.density - ε·N(μ_{i₀}, σ_{i₀}², ·)`) does not decrease the number
of distinct real zeros, for a suitable sign of `ε` and all small `|ε|` for which
`S_ε` has only simple zeros: odd-order (sign-changing) zeros persist as nearby
simple zeros, and each even-order tangential zero splits into two nearby simple
zeros.

This is the genuinely hard piece (the existing simple-source coefficient-
perturbation lemmas assume `S` is already simple, the wrong direction here).
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.ZeroCount

open Set Filter Topology

set_option maxHeartbeats 1000000

/-! ## Section 0: a Gaussian density is everywhere strictly positive. -/

/-- A `GaussianPDF` density is strictly positive everywhere. -/
private lemma gaussian_density_pos (G : Workspace.Types.GaussianPDF.GaussianPDF) (x : ℝ) :
    0 < G.density x := by
  rw [GaussianPDF.density_eq]
  apply mul_pos
  · rw [one_div]
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    have h2pi : 0 < 2 * Real.pi := by positivity
    have := G.varSq_pos
    positivity
  · exact Real.exp_pos _

/-- Perturb the coefficient at 0-based index `i₀` of `S` by subtracting `ε`,
leaving the corresponding Gaussian unchanged. The means/variances and all other
coefficients are preserved, so
`(coeffPerturbSub S i₀ ε).density x = S.density x - ε·(component i₀'s Gaussian).density x`. -/
noncomputable def coeffPerturbSub
    (S : SignedGaussianCombination) (i₀ : Fin S.components.length) (ε : ℝ) :
    SignedGaussianCombination :=
  ⟨S.components.set i₀.val
      ((S.components.get i₀).1 - ε, (S.components.get i₀).2)⟩

/-! ## Section 1: local normal form and sign control at a zero.

`OrderZeroSignControl`: an analytic `f` with `f x₀ = 0` that is not locally zero
factors as `f x = (x - x₀)^m · g x` with `g` continuous at `x₀`, `g x₀ = c ≠ 0`,
and on a small punctured ball `g` keeps the sign of `c` and `|g| ≥ |c|/2`. -/

private lemma OrderZeroSignControl
    (f : ℝ → ℝ) (x₀ : ℝ) (hf : AnalyticAt ℝ f x₀)
    (hfz : f x₀ = 0) (hne : ¬ (∀ᶠ x in 𝓝 x₀, f x = 0)) :
    ∃ (m : ℕ) (c : ℝ) (g : ℝ → ℝ) (ρ : ℝ),
      1 ≤ m ∧ c ≠ 0 ∧ 0 < ρ ∧
      (∀ x : ℝ, |x - x₀| ≤ ρ → f x = (x - x₀) ^ m * g x) ∧
      (∀ x : ℝ, |x - x₀| ≤ ρ → |c| / 2 ≤ |g x| ∧ 0 < c * g x) := by
  -- factorization from Mathlib
  obtain ⟨m, g, hg_an, hg_ne, hg_eq⟩ :=
    (hf.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hne
  set c := g x₀ with hc_def
  have hc_ne : c ≠ 0 := hg_ne
  -- m ≥ 1
  have hm1 : 1 ≤ m := by
    by_contra h
    push_neg at h
    interval_cases m
    · -- m = 0: f x = g x near x₀, so f x₀ = g x₀ = c ≠ 0, contradiction
      have : f x₀ = g x₀ := by
        have := hg_eq.self_of_nhds
        simpa using this
      rw [hfz] at this
      exact hc_ne this.symm
  -- g continuous at x₀
  have hg_cont : ContinuousAt g x₀ := hg_an.continuousAt
  -- punctured-ball control on g: |g - c| < |c|/2
  have hcpos : 0 < |c| := abs_pos.mpr hc_ne
  have hball : ∀ᶠ x in 𝓝 x₀, |g x - c| < |c| / 2 := by
    have : Tendsto g (𝓝 x₀) (𝓝 c) := hg_cont
    have h2 : {y : ℝ | |y - c| < |c| / 2} ∈ 𝓝 c := by
      apply IsOpen.mem_nhds
      · exact isOpen_lt (by fun_prop) continuous_const
      · simp [hcpos]
    exact this h2
  -- combine the eventually-eq and the ball into a metric ball of radius ρ
  rw [Metric.eventually_nhds_iff] at hball
  obtain ⟨ρ₁, hρ₁, hball'⟩ := hball
  rw [Metric.eventually_nhds_iff] at hg_eq
  obtain ⟨ρ₂, hρ₂, hg_eq'⟩ := hg_eq
  refine ⟨m, c, g, min ρ₁ ρ₂ / 2, hm1, hc_ne, by positivity, ?_, ?_⟩
  · intro x hx
    have hd : dist x x₀ < ρ₂ := by
      rw [Real.dist_eq]; calc |x - x₀| ≤ min ρ₁ ρ₂ / 2 := hx
        _ < min ρ₁ ρ₂ := by have := lt_min hρ₁ hρ₂; linarith
        _ ≤ ρ₂ := min_le_right _ _
    have := hg_eq' hd
    simpa using this
  · intro x hx
    have hd : dist x x₀ < ρ₁ := by
      rw [Real.dist_eq]; calc |x - x₀| ≤ min ρ₁ ρ₂ / 2 := hx
        _ < min ρ₁ ρ₂ := by have := lt_min hρ₁ hρ₂; linarith
        _ ≤ ρ₁ := min_le_left _ _
    have hgc := hball' hd
    -- |g x - c| < |c|/2 ⇒ |g x| ≥ |c|/2 and c * g x > 0
    constructor
    · have := abs_sub_abs_le_abs_sub (g x) c
      have h2 : |c| - |g x| ≤ |g x - c| := by
        rw [abs_sub_comm] at this ⊢; linarith [abs_sub_abs_le_abs_sub c (g x)]
      linarith
    · -- sign: |g x - c| < |c|/2 means g x same sign as c
      rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos'
      · have : g x < 0 := by
          have : g x - c < |c| / 2 := lt_of_le_of_lt (le_abs_self _) hgc
          rw [abs_of_neg hcneg] at this; linarith
        exact mul_pos_of_neg_of_neg hcneg this
      · exact absurd hc0 hc_ne
      · have : 0 < g x := by
          have h1 : -(|c| / 2) < g x - c := neg_lt_of_abs_lt hgc
          rw [abs_of_pos hcpos'] at h1; linarith
        exact mul_pos hcpos' this

/-! ## Section 2: IVT helper — straddling signs give an interior zero. -/

/-- Abstract endpoint-sign data extracted from `OrderZeroSignControl` at radius `r`.
`SignData f x₀ m c g r` bundles the factorization and sign/magnitude control on the
closed ball of radius `r`. -/
private structure SignData (f : ℝ → ℝ) (x₀ : ℝ) (m : ℕ) (c : ℝ) (g : ℝ → ℝ) (r : ℝ) : Prop where
  hm1 : 1 ≤ m
  hc_ne : c ≠ 0
  hr_pos : 0 < r
  hfac : ∀ x : ℝ, |x - x₀| ≤ r → f x = (x - x₀) ^ m * g x
  hctrl : ∀ x : ℝ, |x - x₀| ≤ r → |c| / 2 ≤ |g x| ∧ 0 < c * g x

/-- If `h` is continuous on `[a,b]`, `a < b`, `h a < 0 < h b` (or symmetric),
then `h` has a zero in the OPEN interval `(a,b)`. -/
private lemma ivt_open_zero
    (h : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hcont : ContinuousOn h (Set.Icc a b))
    (hsign : (h a < 0 ∧ 0 < h b) ∨ (h b < 0 ∧ 0 < h a)) :
    ∃ y ∈ Set.Ioo a b, h y = 0 := by
  rcases hsign with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · have h0 : (0 : ℝ) ∈ Set.Ioo (h a) (h b) := ⟨ha, hb⟩
    have := intermediate_value_Ioo hab.le hcont h0
    obtain ⟨y, hy, hy0⟩ := this
    exact ⟨y, hy, hy0⟩
  · have h0 : (0 : ℝ) ∈ Set.Ioo (h b) (h a) := ⟨hb, ha⟩
    have := intermediate_value_Ioo' hab.le hcont h0
    obtain ⟨y, hy, hy0⟩ := this
    exact ⟨y, hy, hy0⟩

/-- Shrinking the radius preserves the sign-control data. -/
private lemma SignData.mono {f : ℝ → ℝ} {x₀ : ℝ} {m : ℕ} {c : ℝ} {g : ℝ → ℝ} {ρ : ℝ}
    (sd : SignData f x₀ m c g ρ) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) :
    SignData f x₀ m c g r where
  hm1 := sd.hm1
  hc_ne := sd.hc_ne
  hr_pos := hr
  hfac := fun x hx => sd.hfac x (le_trans hx hrρ)
  hctrl := fun x hx => sd.hctrl x (le_trans hx hrρ)

/-- Package `OrderZeroSignControl` as a `SignData`. -/
private lemma exists_signData
    (f : ℝ → ℝ) (x₀ : ℝ) (hf : AnalyticAt ℝ f x₀)
    (hfz : f x₀ = 0) (hne : ¬ (∀ᶠ x in 𝓝 x₀, f x = 0)) :
    ∃ (m : ℕ) (c : ℝ) (g : ℝ → ℝ) (ρ : ℝ), 0 < ρ ∧ SignData f x₀ m c g ρ := by
  obtain ⟨m, c, g, ρ, hm1, hc_ne, hρ, hfac, hctrl⟩ := OrderZeroSignControl f x₀ hf hfz hne
  exact ⟨m, c, g, ρ, hρ, ⟨hm1, hc_ne, hρ, hfac, hctrl⟩⟩

/-- Lower magnitude bound for `f` at any point of the ball: `|f x| ≥ (|c|/2)|x-x₀|^m`. -/
private lemma SignData.abs_lb {f : ℝ → ℝ} {x₀ : ℝ} {m : ℕ} {c : ℝ} {g : ℝ → ℝ} {r : ℝ}
    (sd : SignData f x₀ m c g r) {x : ℝ} (hx : |x - x₀| ≤ r) :
    (|c| / 2) * |x - x₀| ^ m ≤ |f x| := by
  rw [sd.hfac x hx, abs_mul, abs_pow]
  have h1 := (sd.hctrl x hx).1
  have h2 : (0 : ℝ) ≤ |x - x₀| ^ m := by positivity
  calc (|c| / 2) * |x - x₀| ^ m = |x - x₀| ^ m * (|c| / 2) := by ring
    _ ≤ |x - x₀| ^ m * |g x| := by apply mul_le_mul_of_nonneg_left h1 h2
    _ = |x - x₀| ^ m * |g x| := rfl

/-- Sign of `f` at a ball point: `0 < c * (x-x₀)^m * f x` ... more precisely
`f x = (x-x₀)^m * g x` and `g x` has the sign of `c`, so `c * f x` has the sign of
`c² * (x-x₀)^m`, i.e. `0 ≤ c * f x` iff `0 ≤ (x-x₀)^m`. We record the product sign. -/
private lemma SignData.sign_mul {f : ℝ → ℝ} {x₀ : ℝ} {m : ℕ} {c : ℝ} {g : ℝ → ℝ} {r : ℝ}
    (sd : SignData f x₀ m c g r) {x : ℝ} (hx : |x - x₀| ≤ r) :
    c * f x = (x - x₀) ^ m * (c * g x) := by
  rw [sd.hfac x hx]; ring

/-! ## Section 3: per-zero persistence and splitting under the bump. -/

/-- Endpoint sign-preservation: at a point `x` of the ball, when the bump is
dominated (`ε · G x < (|c|/2)·|x-x₀|^m`), the perturbed value `f x - s·ε·G x`
keeps the sign of `c · f x` (and is strictly nonzero), for `s = ±1`. -/
private lemma SignData.perturbed_endpoint_sign
    {f : ℝ → ℝ} {x₀ : ℝ} {m : ℕ} {c : ℝ} {g : ℝ → ℝ} {r : ℝ}
    (sd : SignData f x₀ m c g r) {G : ℝ → ℝ} (hG : ∀ y, 0 < G y)
    {s ε : ℝ} (hs : s = 1 ∨ s = -1) (hε : 0 < ε)
    {x : ℝ} (hx : |x - x₀| ≤ r)
    (hbump : ε * G x < (|c| / 2) * |x - x₀| ^ m) :
    (0 < c * f x → 0 < c * (f x - s * ε * G x)) ∧
    (c * f x < 0 → c * (f x - s * ε * G x) < 0) := by
  have habs : |s| = 1 := by rcases hs with h | h <;> simp [h]
  -- |c·(s·ε·G x)| < |c·f x|
  have hcpos : 0 < |c| := abs_pos.mpr sd.hc_ne
  have hbb : |c * (s * ε * G x)| < |c| * ((|c| / 2) * |x - x₀| ^ m) := by
    rw [show c * (s * ε * G x) = (c * s) * (ε * G x) by ring, abs_mul, abs_mul, habs]
    have hεG : |ε * G x| = ε * G x := abs_of_pos (mul_pos hε (hG x))
    rw [hεG, mul_one]
    exact mul_lt_mul_of_pos_left hbump hcpos
  have hflb : |c| * ((|c| / 2) * |x - x₀| ^ m) ≤ |c * f x| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (sd.abs_lb hx) (le_of_lt hcpos)
  have hkey : |c * (s * ε * G x)| < |c * f x| := lt_of_lt_of_le hbb hflb
  -- now |b| < |a| ⇒ a - b keeps sign of a
  set a := c * f x
  set b := c * (s * ε * G x)
  have heq : c * (f x - s * ε * G x) = a - b := by simp only [a, b]; ring
  rw [heq]
  constructor
  · intro ha
    have hb := abs_lt.mp hkey
    have : |a| = a := abs_of_pos ha
    rw [this] at hb; linarith [hb.2]
  · intro ha
    have hb := abs_lt.mp hkey
    have : |a| = -a := abs_of_neg ha
    rw [this] at hb; linarith [hb.1]

/-- **OddOrderZeroPersists.** If `m` is odd, the perturbed function
`P x = f x - s·ε·G x` has a zero in the open interval `(x₀-r, x₀+r)`. -/
private lemma OddOrderZeroPersists
    {f : ℝ → ℝ} {x₀ : ℝ} {m : ℕ} {c : ℝ} {g : ℝ → ℝ} {r : ℝ}
    (sd : SignData f x₀ m c g r) (hodd : Odd m)
    {G : ℝ → ℝ} (hG : ∀ y, 0 < G y)
    {s ε : ℝ} (hs : s = 1 ∨ s = -1) (hε : 0 < ε)
    (hPcont : ContinuousOn (fun x => f x - s * ε * G x) (Set.Icc (x₀ - r) (x₀ + r)))
    (hbump : ∀ x, |x - x₀| ≤ r → ε * G x < (|c| / 2) * r ^ m) :
    ∃ y ∈ Set.Ioo (x₀ - r) (x₀ + r), f y - s * ε * G y = 0 := by
  set P := fun x => f x - s * ε * G x with hP
  have hcpos : 0 < |c| := abs_pos.mpr sd.hc_ne
  -- endpoints
  have hxL : |(x₀ - r) - x₀| ≤ r := by rw [show (x₀ - r) - x₀ = -r by ring, abs_neg, abs_of_pos sd.hr_pos]
  have hxR : |(x₀ + r) - x₀| ≤ r := by rw [show (x₀ + r) - x₀ = r by ring, abs_of_pos sd.hr_pos]
  -- bump bounds at the two endpoints (|x-x₀|^m = r^m there)
  have hbL : ε * G (x₀ - r) < (|c| / 2) * |(x₀ - r) - x₀| ^ m := by
    rw [show (x₀ - r) - x₀ = -r by ring, abs_neg, abs_of_pos sd.hr_pos]; exact hbump _ hxL
  have hbR : ε * G (x₀ + r) < (|c| / 2) * |(x₀ + r) - x₀| ^ m := by
    rw [show (x₀ + r) - x₀ = r by ring, abs_of_pos sd.hr_pos]; exact hbump _ hxR
  -- sign of c·f at endpoints
  have hcfL : c * f (x₀ - r) < 0 := by
    rw [sd.sign_mul hxL]
    rw [show (x₀ - r) - x₀ = -r by ring]
    have hrm : (-r) ^ m < 0 := Odd.pow_neg hodd (by linarith [sd.hr_pos])
    exact mul_neg_of_neg_of_pos hrm (sd.hctrl _ hxL).2
  have hcfR : 0 < c * f (x₀ + r) := by
    rw [sd.sign_mul hxR]
    rw [show (x₀ + r) - x₀ = r by ring]
    exact mul_pos (pow_pos sd.hr_pos m) (sd.hctrl _ hxR).2
  -- transfer to perturbed via sign-preservation
  have hPL := (sd.perturbed_endpoint_sign hG hs hε hxL hbL).2 hcfL
  have hPR := (sd.perturbed_endpoint_sign hG hs hε hxR hbR).1 hcfR
  -- c·P(x₀-r) < 0, c·P(x₀+r) > 0. Convert to signs of P depending on sign of c.
  have hlt : x₀ - r < x₀ + r := by linarith [sd.hr_pos]
  have hsign : (P (x₀ - r) < 0 ∧ 0 < P (x₀ + r)) ∨ (P (x₀ + r) < 0 ∧ 0 < P (x₀ - r)) := by
    rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos'
    · right; constructor
      · nlinarith [hPR, hcneg]
      · nlinarith [hPL, hcneg]
    · exact absurd hc0 sd.hc_ne
    · left; constructor
      · nlinarith [hPL, hcpos']
      · nlinarith [hPR, hcpos']
  exact ivt_open_zero P (x₀ - r) (x₀ + r) hlt hPcont hsign

/-- **EvenOrderZeroSplitsInTwo.** If `m` is even, `f x₀ = 0`, and the sign is
favourable (`0 < s·c`), then the perturbed function has two distinct zeros
`y₁ < x₀ < y₂`, one in `(x₀-r, x₀)` and one in `(x₀, x₀+r)`. -/
private lemma EvenOrderZeroSplitsInTwo
    {f : ℝ → ℝ} {x₀ : ℝ} {m : ℕ} {c : ℝ} {g : ℝ → ℝ} {r : ℝ}
    (sd : SignData f x₀ m c g r) (heven : Even m) (hf0 : f x₀ = 0)
    {G : ℝ → ℝ} (hG : ∀ y, 0 < G y)
    {s ε : ℝ} (hs : s = 1 ∨ s = -1) (hε : 0 < ε) (hfav : 0 < s * c)
    (hPcont : ContinuousOn (fun x => f x - s * ε * G x) (Set.Icc (x₀ - r) (x₀ + r)))
    (hbump : ∀ x, |x - x₀| ≤ r → ε * G x < (|c| / 2) * r ^ m) :
    ∃ y₁ ∈ Set.Ioo (x₀ - r) x₀, ∃ y₂ ∈ Set.Ioo x₀ (x₀ + r),
      f y₁ - s * ε * G y₁ = 0 ∧ f y₂ - s * ε * G y₂ = 0 := by
  set P := fun x => f x - s * ε * G x with hP
  have hcpos : 0 < |c| := abs_pos.mpr sd.hc_ne
  have hxL : |(x₀ - r) - x₀| ≤ r := by rw [show (x₀ - r) - x₀ = -r by ring, abs_neg, abs_of_pos sd.hr_pos]
  have hxR : |(x₀ + r) - x₀| ≤ r := by rw [show (x₀ + r) - x₀ = r by ring, abs_of_pos sd.hr_pos]
  have hx0 : |x₀ - x₀| ≤ r := by simp [sd.hr_pos.le]
  have hbL : ε * G (x₀ - r) < (|c| / 2) * |(x₀ - r) - x₀| ^ m := by
    rw [show (x₀ - r) - x₀ = -r by ring, abs_neg, abs_of_pos sd.hr_pos]; exact hbump _ hxL
  have hbR : ε * G (x₀ + r) < (|c| / 2) * |(x₀ + r) - x₀| ^ m := by
    rw [show (x₀ + r) - x₀ = r by ring, abs_of_pos sd.hr_pos]; exact hbump _ hxR
  -- endpoint signs: both c·f(x₀±r) > 0 (m even)
  have hcfL : 0 < c * f (x₀ - r) := by
    rw [sd.sign_mul hxL, show (x₀ - r) - x₀ = -r by ring]
    have : (0:ℝ) < (-r) ^ m := by
      rw [heven.neg_pow]; exact pow_pos sd.hr_pos m
    exact mul_pos this (sd.hctrl _ hxL).2
  have hcfR : 0 < c * f (x₀ + r) := by
    rw [sd.sign_mul hxR, show (x₀ + r) - x₀ = r by ring]
    exact mul_pos (pow_pos sd.hr_pos m) (sd.hctrl _ hxR).2
  have hPL := (sd.perturbed_endpoint_sign hG hs hε hxL hbL).1 hcfL
  have hPR := (sd.perturbed_endpoint_sign hG hs hε hxR hbR).1 hcfR
  -- center: c·P(x₀) < 0
  have hPc : c * P (x₀) < 0 := by
    have : P x₀ = - (s * ε * G x₀) := by simp only [hP]; rw [hf0]; ring
    rw [this]
    have : c * (-(s * ε * G x₀)) = -((s * c) * (ε * G x₀)) := by ring
    rw [this]
    have : 0 < (s * c) * (ε * G x₀) := mul_pos hfav (mul_pos hε (hG x₀))
    linarith
  -- two IVT applications
  have hlL : x₀ - r < x₀ := by linarith [sd.hr_pos]
  have hlR : x₀ < x₀ + r := by linarith [sd.hr_pos]
  have hcontL : ContinuousOn P (Set.Icc (x₀ - r) x₀) :=
    hPcont.mono (Set.Icc_subset_Icc le_rfl (by linarith [sd.hr_pos]))
  have hcontR : ContinuousOn P (Set.Icc x₀ (x₀ + r)) :=
    hPcont.mono (Set.Icc_subset_Icc (by linarith [sd.hr_pos]) le_rfl)
  -- sign disjuncts on each half (depend on sign of c)
  have hsignL : (P (x₀ - r) < 0 ∧ 0 < P x₀) ∨ (P x₀ < 0 ∧ 0 < P (x₀ - r)) := by
    rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos'
    · left; exact ⟨by nlinarith [hPL, hcneg], by nlinarith [hPc, hcneg]⟩
    · exact absurd hc0 sd.hc_ne
    · right; exact ⟨by nlinarith [hPc, hcpos'], by nlinarith [hPL, hcpos']⟩
  have hsignR : (P x₀ < 0 ∧ 0 < P (x₀ + r)) ∨ (P (x₀ + r) < 0 ∧ 0 < P x₀) := by
    rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos'
    · right; exact ⟨by nlinarith [hPR, hcneg], by nlinarith [hPc, hcneg]⟩
    · exact absurd hc0 sd.hc_ne
    · left; exact ⟨by nlinarith [hPc, hcpos'], by nlinarith [hPR, hcpos']⟩
  obtain ⟨y₁, hy₁, hy₁0⟩ := ivt_open_zero P (x₀ - r) x₀ hlL hcontL hsignL
  obtain ⟨y₂, hy₂, hy₂0⟩ := ivt_open_zero P x₀ (x₀ + r) hlR hcontR hsignR
  exact ⟨y₁, hy₁, y₂, hy₂, hy₁0, hy₂0⟩

/-- The perturbation identity (★): subtracting `ε` from the `i₀`-th coefficient
subtracts `ε · G_{i₀}.density x` from the density. -/
private lemma coeffPerturbSub_density
    (S : SignedGaussianCombination) (i₀ : Fin S.components.length) (ε : ℝ) (x : ℝ) :
    (coeffPerturbSub S i₀ ε).density x
      = S.density x - ε * (S.components.get i₀).2.density x := by
  unfold coeffPerturbSub
  rw [SignedGaussianCombination.density_eq, SignedGaussianCombination.density_eq]
  simp only [List.map_set]
  rw [List.sum_set']
  have hlen : i₀.val < (S.components.map (fun p => p.1 * p.2.density x)).length := by
    simp [i₀.isLt]
  rw [dif_pos hlen]
  have hget : (S.components.map (fun p => p.1 * p.2.density x))[i₀.val] =
      (S.components.get i₀).1 * (S.components.get i₀).2.density x := by
    simp [List.getElem_map, List.get_eq_getElem]
  rw [hget]
  ring

/-! ## Section 4: general count-non-decrease assembly.

For an analytic `f` with finitely many zeros and a positive continuous bump `G`,
there is a sign `s` and threshold so `f - s·ε·G` has at least as many zeros. -/

/-- A finite zero set of an analytic function is not locally zero at any of its
points (since the set of zeros is finite, hence isolated). -/
private lemma not_eventually_zero_of_finite
    {f : ℝ → ℝ} {x₀ : ℝ} (hZfin : (zeroSet f).Finite) :
    ¬ (∀ᶠ x in 𝓝 x₀, f x = 0) := by
  intro hev
  have hmem : zeroSet f ∈ 𝓝 x₀ := hev
  exact (infinite_of_mem_nhds x₀ hmem) hZfin

/-- **General count-non-decrease.** For `f` analytic everywhere with finitely many
zeros and `G` a positive continuous bump, there is a sign `s ∈ {±1}` and a
threshold `ε₀ > 0` so that for all `ε ∈ (0, ε₀)`, the perturbed function
`f - s·ε·G` has at least as many distinct zeros as `f`. -/
private lemma general_count_nondecrease
    (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f Set.univ)
    (G : ℝ → ℝ) (hGcont : Continuous G) (hGpos : ∀ x, 0 < G x)
    (hZfin : (zeroSet f).Finite) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (zeroSet f).encard ≤ (zeroSet (fun x => f x - s * ε * G x)).encard := by
  classical
  set Z := zeroSet f with hZ_def
  -- Case: Z empty → trivial.
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · refine ⟨1, Or.inl rfl, 1, one_pos, ?_⟩
    intro ε _ _
    rw [hZe]; simp
  -- Z nonempty and finite.
  obtain ⟨z₀, hz₀⟩ := hZne
  set Zf := hZfin.toFinset with hZf_def
  have hZf_ne : Zf.Nonempty := by
    rw [hZf_def]; exact ⟨z₀, by rw [Set.Finite.mem_toFinset]; exact hz₀⟩
  have hmemZ : ∀ x, x ∈ Zf ↔ x ∈ Z := by
    intro x; rw [hZf_def, Set.Finite.mem_toFinset]
  -- per-zero sign data
  have hdata : ∀ x₀ ∈ Z, ∃ (m : ℕ) (c : ℝ) (g : ℝ → ℝ) (ρ : ℝ), 0 < ρ ∧ SignData f x₀ m c g ρ := by
    intro x₀ hx₀
    have hfz : f x₀ = 0 := hx₀
    have hAt : AnalyticAt ℝ f x₀ := hf x₀ (Set.mem_univ _)
    exact exists_signData f x₀ hAt hfz (not_eventually_zero_of_finite hZfin)
  choose! mm cc gg ρρ hρpos hsd using hdata
  -- Finite zero set as a Finset.
  have hZf_pos : ∀ x ∈ Zf, 0 < ρρ x := fun x hx => hρpos x ((hmemZ x).mp hx)
  have hZf_sd : ∀ x ∈ Zf, SignData f x (mm x) (cc x) (gg x) (ρρ x) :=
    fun x hx => hsd x ((hmemZ x).mp hx)
  -- (A) A single positive radius `r` making the closed `r`-balls pairwise disjoint
  -- and shrinking inside every per-zero control radius `ρρ x`.
  -- min over Zf of ρρ
  have hρ_choice : ∃ ρmin : ℝ, 0 < ρmin ∧ ∀ x ∈ Zf, ρmin ≤ ρρ x := by
    refine ⟨(Zf.attach.image (fun x => ρρ x.1)).min' ?_, ?_, ?_⟩
    · exact ⟨ρρ z₀, Finset.mem_image.mpr ⟨⟨z₀, by rw [hZf_def, Set.Finite.mem_toFinset]; exact hz₀⟩,
        Finset.mem_attach _ _, rfl⟩⟩
    · rcases Finset.mem_image.mp (Finset.min'_mem (Zf.attach.image (fun x => ρρ x.1)) _) with
        ⟨⟨x, hx⟩, _, hval⟩
      rw [← hval]; exact hZf_pos x hx
    · intro x hx
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
  obtain ⟨ρmin, hρmin_pos, hρmin_le⟩ := hρ_choice
  -- spacing: 4*spc ≤ |x - x'| for distinct zeros
  have hspc_choice : ∃ spc : ℝ, 0 < spc ∧ ∀ x ∈ Zf, ∀ x' ∈ Zf, x ≠ x' → 4 * spc ≤ |x - x'| := by
    classical
    let pair_image : Finset ℝ :=
      ((Zf ×ˢ Zf).filter (fun p => p.1 ≠ p.2)).image (fun p => |p.1 - p.2|)
    by_cases hp : pair_image.Nonempty
    · have hd_pos : 0 < pair_image.min' hp := by
        rcases Finset.mem_image.mp (Finset.min'_mem pair_image hp) with ⟨⟨a, b⟩, hab, hval⟩
        simp only [pair_image, Finset.mem_filter, Finset.mem_product] at hab
        rw [← hval]; exact abs_pos.mpr (sub_ne_zero.mpr hab.2)
      refine ⟨pair_image.min' hp / 4, by linarith, ?_⟩
      intro x hx x' hx' hne
      have h1 : pair_image.min' hp ≤ |x - x'| := by
        apply Finset.min'_le
        refine Finset.mem_image.mpr ⟨(x, x'), ?_, rfl⟩
        simp only [pair_image, Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hx, hx'⟩, hne⟩
      linarith
    · refine ⟨1, by norm_num, ?_⟩
      intro x hx x' hx' hne
      exfalso
      apply hp
      refine ⟨|x - x'|, Finset.mem_image.mpr ⟨(x, x'), ?_, rfl⟩⟩
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hx, hx'⟩, hne⟩
  obtain ⟨spc, hspc_pos, hspc_le⟩ := hspc_choice
  set r : ℝ := min ρmin spc with hr_def
  have hr_pos : 0 < r := lt_min hρmin_pos hspc_pos
  have hr_le_ρ : ∀ x ∈ Zf, r ≤ ρρ x := fun x hx => le_trans (min_le_left _ _) (hρmin_le x hx)
  have hr_le_spc : r ≤ spc := min_le_right _ _
  -- shrunk sign-data at radius r
  have hsdr : ∀ x ∈ Zf, SignData f x (mm x) (cc x) (gg x) r :=
    fun x hx => (hZf_sd x hx).mono hr_pos (hr_le_ρ x hx)
  -- disjointness of the closed r-balls (in fact the open r-intervals)
  have hdisj : ∀ x ∈ Zf, ∀ x' ∈ Zf, x ≠ x' →
      Disjoint (Set.Ioo (x - r) (x + r)) (Set.Ioo (x' - r) (x' + r)) := by
    intro x hx x' hx' hne
    have hgap : 4 * spc ≤ |x - x'| := hspc_le x hx x' hx' hne
    have hr4 : 2 * r < |x - x'| := by
      have : 2 * r ≤ 2 * spc := by linarith [hr_le_spc]
      have h4 : 2 * spc < 4 * spc := by linarith [hspc_pos]
      linarith
    rw [Set.disjoint_left]
    intro y hy1 hy2
    simp only [Set.mem_Ioo] at hy1 hy2
    rcases abs_cases (x - x') with ⟨he, _⟩ | ⟨he, _⟩ <;>
      (rw [he] at hr4; nlinarith [hy1.1, hy1.2, hy2.1, hy2.2])
  -- (B) A single positive threshold `ε₀`.
  -- Global compact `K` containing every `[x - r, x + r]`, x ∈ Zf, and the global max of G on K.
  have hG_int : ∀ x ∈ Zf, ∃ M : ℝ, ∀ y : ℝ, |y - x| ≤ r → G y ≤ M ∧ 0 < M := by
    intro x hx
    have hxmem : x ∈ Set.Icc (x - r) (x + r) := by
      simp only [Set.mem_Icc]; constructor <;> linarith [hr_pos]
    obtain ⟨y₀, hy₀mem, hy₀max⟩ :=
      (isCompact_Icc (a := x - r) (b := x + r)).exists_isMaxOn
        ⟨x, hxmem⟩ hGcont.continuousOn
    refine ⟨G y₀, ?_⟩
    intro y hy
    refine ⟨?_, hGpos _⟩
    apply hy₀max
    simp only [Set.mem_Icc]; rw [abs_le] at hy; constructor <;> linarith [hy.1, hy.2]
  choose! GM hGM using hG_int
  -- ρ'min := min over Zf of (|cc x|/2) * r^(mm x)  (positive)
  have hz₀mem : z₀ ∈ Zf := by rw [hZf_def, Set.Finite.mem_toFinset]; exact hz₀
  have hρp_choice : ∃ ρp : ℝ, 0 < ρp ∧ ∀ x ∈ Zf, ρp ≤ (|cc x| / 2) * r ^ (mm x) := by
    set img : Finset ℝ := Zf.attach.image (fun x => (|cc x.1| / 2) * r ^ (mm x.1)) with himg_def
    have hne : img.Nonempty :=
      ⟨_, Finset.mem_image.mpr ⟨⟨z₀, hz₀mem⟩, Finset.mem_attach _ _, rfl⟩⟩
    refine ⟨img.min' hne, ?_, ?_⟩
    · rcases Finset.mem_image.mp (Finset.min'_mem img hne) with ⟨⟨x, hx⟩, _, hval⟩
      rw [← hval]
      have : 0 < |cc x| := abs_pos.mpr (hZf_sd x hx).hc_ne
      positivity
    · intro x hx
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
  obtain ⟨ρp, hρp_pos, hρp_le⟩ := hρp_choice
  -- GMmax := max over Zf of GM x  (positive)
  have hGM_choice : ∃ GMmax : ℝ, 0 < GMmax ∧ ∀ x ∈ Zf, GM x ≤ GMmax := by
    set img : Finset ℝ := Zf.attach.image (fun x => GM x.1) with himg_def
    have hne : img.Nonempty :=
      ⟨_, Finset.mem_image.mpr ⟨⟨z₀, hz₀mem⟩, Finset.mem_attach _ _, rfl⟩⟩
    refine ⟨img.max' hne, ?_, ?_⟩
    · have hGz₀ : 0 < GM z₀ := (hGM z₀ hz₀mem z₀ (by simp [hr_pos.le])).2
      calc (0:ℝ) < GM z₀ := hGz₀
        _ ≤ _ := Finset.le_max' img _ (Finset.mem_image.mpr ⟨⟨z₀, hz₀mem⟩, Finset.mem_attach _ _, rfl⟩)
    · intro x hx
      apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
  obtain ⟨GMmax, hGMmax_pos, hGMmax_le⟩ := hGM_choice
  set ε₀ : ℝ := ρp / (GMmax + 1) with hε₀_def
  have hε₀_pos : 0 < ε₀ := by rw [hε₀_def]; positivity
  -- bump bound: for ε < ε₀ and x ∈ Zf, all y in the r-ball satisfy ε*G y < (|cc x|/2)*r^(mm x)
  have hbump_all : ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x ∈ Zf, ∀ y : ℝ, |y - x| ≤ r →
      ε * G y < (|cc x| / 2) * r ^ (mm x) := by
    intro ε hεpos hεlt x hx y hy
    have hGyM : G y ≤ GM x := (hGM x hx y hy).1
    have hGMmax : GM x ≤ GMmax := hGMmax_le x hx
    have hGy_le : G y ≤ GMmax := le_trans hGyM hGMmax
    have hρpx : ρp ≤ (|cc x| / 2) * r ^ (mm x) := hρp_le x hx
    have hkey : ε * G y < ρp := by
      have h1 : ε * G y ≤ ε * GMmax := by
        apply mul_le_mul_of_nonneg_left hGy_le hεpos.le
      have h2 : ε * GMmax < ε₀ * (GMmax + 1) := by
        have : ε * GMmax ≤ ε * (GMmax + 1) := by nlinarith [hGMmax_pos, hεpos.le]
        have h3 : ε * (GMmax + 1) < ε₀ * (GMmax + 1) := by
          apply mul_lt_mul_of_pos_right hεlt (by linarith [hGMmax_pos])
        linarith
      have h4 : ε₀ * (GMmax + 1) = ρp := by
        rw [hε₀_def]; field_simp
      linarith
    linarith
  -- (C) Sign choice making |E_lost| ≤ |E_split|.
  classical
  -- partition predicates (parametrised by the chosen sign s)
  set Epos : Finset ℝ := Zf.filter (fun x => Even (mm x) ∧ 0 < cc x) with hEpos_def
  set Eneg : Finset ℝ := Zf.filter (fun x => Even (mm x) ∧ cc x < 0) with hEneg_def
  -- choose the sign
  obtain ⟨s, hs, hsplit_ge⟩ :
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        (Zf.filter (fun x => Even (mm x) ∧ ¬ (0 < s * cc x))).card ≤
        (Zf.filter (fun x => Even (mm x) ∧ 0 < s * cc x)).card := by
    by_cases hcmp : Eneg.card ≤ Epos.card
    · refine ⟨1, Or.inl rfl, ?_⟩
      have e1 : Zf.filter (fun x => Even (mm x) ∧ 0 < (1:ℝ) * cc x) = Epos := by
        rw [hEpos_def]; apply Finset.filter_congr; intro x _; simp
      have e2 : Zf.filter (fun x => Even (mm x) ∧ ¬ (0 < (1:ℝ) * cc x)) = Eneg := by
        rw [hEneg_def]; apply Finset.filter_congr; intro x hx
        simp only [one_mul]
        constructor
        · rintro ⟨he, hnp⟩
          exact ⟨he, lt_of_le_of_ne (not_lt.mp hnp) (hZf_sd x hx).hc_ne⟩
        · rintro ⟨he, hlt⟩; exact ⟨he, not_lt.mpr hlt.le⟩
      rw [e1, e2]; exact hcmp
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [not_le] at hcmp
      have e1 : Zf.filter (fun x => Even (mm x) ∧ 0 < (-1:ℝ) * cc x) = Eneg := by
        rw [hEneg_def]; apply Finset.filter_congr; intro x _
        constructor
        · rintro ⟨he, h⟩; exact ⟨he, by nlinarith [h]⟩
        · rintro ⟨he, h⟩; exact ⟨he, by nlinarith [h]⟩
      have e2 : Zf.filter (fun x => Even (mm x) ∧ ¬ (0 < (-1:ℝ) * cc x)) = Epos := by
        rw [hEpos_def]; apply Finset.filter_congr; intro x hx
        constructor
        · rintro ⟨he, hnp⟩
          have hle : 0 ≤ cc x := by nlinarith [not_lt.mp hnp]
          exact ⟨he, lt_of_le_of_ne hle (Ne.symm (hZf_sd x hx).hc_ne)⟩
        · rintro ⟨he, hlt⟩; exact ⟨he, by nlinarith [hlt]⟩
      rw [e1, e2]; exact hcmp.le
  refine ⟨s, hs, ε₀, hε₀_pos, ?_⟩
  intro ε hεpos hεlt
  -- The perturbed function.
  set P : ℝ → ℝ := fun x => f x - s * ε * G x with hP_def
  have hPcont : Continuous P := by
    rw [hP_def]
    exact hf.continuous.sub (continuous_const.mul hGcont)
  -- partition Zf into O (odd) / Esp (split even) / Elost (lost even)
  set O : Finset ℝ := Zf.filter (fun x => Odd (mm x)) with hO_def
  set Esp : Finset ℝ := Zf.filter (fun x => Even (mm x) ∧ 0 < s * cc x) with hEsp_def
  set Elost : Finset ℝ := Zf.filter (fun x => Even (mm x) ∧ ¬ (0 < s * cc x)) with hElost_def
  -- card accounting
  have hcardZ : Zf.card = O.card + (Esp.card + Elost.card) := by
    have h1 : (Zf.filter (fun x => Even (mm x))).card = Esp.card + Elost.card := by
      have hEsp_eq : Esp = (Zf.filter (fun x => Even (mm x))).filter (fun x => 0 < s * cc x) := by
        rw [hEsp_def, Finset.filter_filter]
      have hElost_eq : Elost =
          (Zf.filter (fun x => Even (mm x))).filter (fun x => ¬ (0 < s * cc x)) := by
        rw [hElost_def, Finset.filter_filter]
      rw [hEsp_eq, hElost_eq]
      exact (Finset.filter_card_add_filter_neg_card_eq_card
        (s := Zf.filter (fun x => Even (mm x))) (p := fun x => 0 < s * cc x)).symm
    have h2 : O.card + (Zf.filter (fun x => Even (mm x))).card = Zf.card := by
      rw [hO_def]
      have : (Zf.filter (fun x => Even (mm x))) = Zf.filter (fun x => ¬ Odd (mm x)) := by
        apply Finset.filter_congr; intro x _; rw [Nat.not_odd_iff_even]
      rw [this]
      exact Finset.filter_card_add_filter_neg_card_eq_card _
    rw [← h2, h1]
  -- |Elost| ≤ |Esp|
  have hElost_le : Elost.card ≤ Esp.card := by rw [hEsp_def, hElost_def]; exact hsplit_ge
  -- witnesses: odd zeros persist; split even zeros split into two.
  -- odd
  have hOdd_wit : ∀ x ∈ O, ∃ y ∈ Set.Ioo (x - r) (x + r), P y = 0 := by
    intro x hxO
    rw [hO_def, Finset.mem_filter] at hxO
    obtain ⟨hxZ, hodd⟩ := hxO
    have hPconton : ContinuousOn (fun z => f z - s * ε * G z) (Set.Icc (x - r) (x + r)) :=
      hPcont.continuousOn
    have hbump : ∀ z, |z - x| ≤ r → ε * G z < (|cc x| / 2) * r ^ (mm x) :=
      fun z hz => hbump_all ε hεpos hεlt x hxZ z hz
    obtain ⟨y, hy, hy0⟩ := OddOrderZeroPersists (hsdr x hxZ) hodd hGpos hs hεpos hPconton hbump
    exact ⟨y, hy, hy0⟩
  -- split even
  have hEsp_wit : ∀ x ∈ Esp, ∃ y₁ ∈ Set.Ioo (x - r) x, ∃ y₂ ∈ Set.Ioo x (x + r),
      P y₁ = 0 ∧ P y₂ = 0 := by
    intro x hxE
    rw [hEsp_def, Finset.mem_filter] at hxE
    obtain ⟨hxZ, heven, hfav⟩ := hxE
    have hfz : f x = 0 := (hmemZ x).mp hxZ
    have hPconton : ContinuousOn (fun z => f z - s * ε * G z) (Set.Icc (x - r) (x + r)) :=
      hPcont.continuousOn
    have hbump : ∀ z, |z - x| ≤ r → ε * G z < (|cc x| / 2) * r ^ (mm x) :=
      fun z hz => hbump_all ε hεpos hεlt x hxZ z hz
    obtain ⟨y₁, hy₁, y₂, hy₂, hy₁0, hy₂0⟩ :=
      EvenOrderZeroSplitsInTwo (hsdr x hxZ) heven hfz hGpos hs hεpos hfav hPconton hbump
    exact ⟨y₁, hy₁, y₂, hy₂, hy₁0, hy₂0⟩
  choose! pz hpz_mem hpz_zero using hOdd_wit
  choose! yl hyl_mem yr hyr_mem hyz using hEsp_wit
  have hyl_zero : ∀ x ∈ Esp, P (yl x) = 0 := fun x hx => (hyz x hx).1
  have hyr_zero : ∀ x ∈ Esp, P (yr x) = 0 := fun x hx => (hyz x hx).2
  -- build the three guaranteed-zero sets
  set Wo : Set ℝ := pz '' (O : Set ℝ) with hWo_def
  set Wl : Set ℝ := yl '' (Esp : Set ℝ) with hWl_def
  set Wr : Set ℝ := yr '' (Esp : Set ℝ) with hWr_def
  -- containment in zeroSet P
  have hWo_sub : Wo ⊆ zeroSet P := by
    rintro _ ⟨x, hx, rfl⟩
    rw [zeroSet, Set.mem_setOf_eq]; exact hpz_zero x hx
  have hWl_sub : Wl ⊆ zeroSet P := by
    rintro _ ⟨x, hx, rfl⟩
    rw [zeroSet, Set.mem_setOf_eq]; exact hyl_zero x hx
  have hWr_sub : Wr ⊆ zeroSet P := by
    rintro _ ⟨x, hx, rfl⟩
    rw [zeroSet, Set.mem_setOf_eq]; exact hyr_zero x hx
  have hW_sub : Wo ∪ Wl ∪ Wr ⊆ zeroSet P := by
    apply Set.union_subset (Set.union_subset hWo_sub hWl_sub) hWr_sub
  -- localisation lemmas: each witness lives in the open r-interval of its source zero
  have hpz_loc : ∀ x ∈ O, pz x ∈ Set.Ioo (x - r) (x + r) := hpz_mem
  have hyl_loc : ∀ x ∈ Esp, yl x ∈ Set.Ioo (x - r) x := hyl_mem
  have hyr_loc : ∀ x ∈ Esp, yr x ∈ Set.Ioo x (x + r) := hyr_mem
  -- helper: membership of Finset coercion ↔ Finset membership, and ⊆ Zf
  have hO_subZf : ∀ x ∈ (O : Set ℝ), x ∈ Zf := by
    intro x hx; rw [Finset.mem_coe, hO_def, Finset.mem_filter] at hx; exact hx.1
  have hEsp_subZf : ∀ x ∈ (Esp : Set ℝ), x ∈ Zf := by
    intro x hx; rw [Finset.mem_coe, hEsp_def, Finset.mem_filter] at hx; exact hx.1
  -- InjOn of pz, yl, yr (distinct sources → disjoint intervals → distinct witnesses)
  have hpz_inj : Set.InjOn pz (O : Set ℝ) := by
    intro a ha b hb hab
    by_contra hne
    have hda := hpz_loc a (Finset.mem_coe.mp ha)
    have hdb := hpz_loc b (Finset.mem_coe.mp hb)
    have hdisjab := hdisj a (hO_subZf a ha) b (hO_subZf b hb) hne
    rw [Set.disjoint_left] at hdisjab
    exact hdisjab hda (hab ▸ hdb)
  have hyl_inj : Set.InjOn yl (Esp : Set ℝ) := by
    intro a ha b hb hab
    by_contra hne
    have hda := hyl_loc a (Finset.mem_coe.mp ha)
    have hdb := hyl_loc b (Finset.mem_coe.mp hb)
    have hda' : yl a ∈ Set.Ioo (a - r) (a + r) :=
      ⟨hda.1, lt_trans hda.2 (by linarith [hr_pos])⟩
    have hdb' : yl b ∈ Set.Ioo (b - r) (b + r) :=
      ⟨hdb.1, lt_trans hdb.2 (by linarith [hr_pos])⟩
    have hdisjab := hdisj a (hEsp_subZf a ha) b (hEsp_subZf b hb) hne
    rw [Set.disjoint_left] at hdisjab
    exact hdisjab hda' (hab ▸ hdb')
  have hyr_inj : Set.InjOn yr (Esp : Set ℝ) := by
    intro a ha b hb hab
    by_contra hne
    have hda := hyr_loc a (Finset.mem_coe.mp ha)
    have hdb := hyr_loc b (Finset.mem_coe.mp hb)
    have hda' : yr a ∈ Set.Ioo (a - r) (a + r) :=
      ⟨lt_trans (by linarith [hr_pos]) hda.1, hda.2⟩
    have hdb' : yr b ∈ Set.Ioo (b - r) (b + r) :=
      ⟨lt_trans (by linarith [hr_pos]) hdb.1, hdb.2⟩
    have hdisjab := hdisj a (hEsp_subZf a ha) b (hEsp_subZf b hb) hne
    rw [Set.disjoint_left] at hdisjab
    exact hdisjab hda' (hab ▸ hdb')
  -- pairwise disjointness of Wo, Wl, Wr
  -- A witness in Wo lies in the r-interval of its (odd) source; one in Wl/Wr in a (split-even) source.
  -- Since odd and split-even sources are different points (O, Esp disjoint as filters),
  -- and within an Esp source yl < x < yr, all three sets are pairwise disjoint.
  have hO_Esp_disj : Disjoint O Esp := by
    rw [hO_def, hEsp_def, Finset.disjoint_filter]
    intro x _ hodd; rintro ⟨heven, _⟩
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hWo_Wl_disj : Disjoint Wo Wl := by
    rw [Set.disjoint_left]
    rintro w ⟨a, ha, rfl⟩ ⟨b, hb, hwb⟩
    have haZf := hO_subZf a ha
    have hbZf := hEsp_subZf b hb
    have hab_ne : a ≠ b := by
      intro h; subst h
      exact (Finset.disjoint_left.mp hO_Esp_disj) (Finset.mem_coe.mp ha) (Finset.mem_coe.mp hb)
    have hpa := hpz_loc a (Finset.mem_coe.mp ha)
    have hlb := hyl_loc b (Finset.mem_coe.mp hb)
    have hlb' : yl b ∈ Set.Ioo (b - r) (b + r) := ⟨hlb.1, lt_trans hlb.2 (by linarith [hr_pos])⟩
    have hdisjab := hdisj a haZf b hbZf hab_ne
    rw [Set.disjoint_left] at hdisjab
    exact hdisjab hpa (hwb ▸ hlb')
  have hWo_Wr_disj : Disjoint Wo Wr := by
    rw [Set.disjoint_left]
    rintro w ⟨a, ha, rfl⟩ ⟨b, hb, hwb⟩
    have haZf := hO_subZf a ha
    have hbZf := hEsp_subZf b hb
    have hab_ne : a ≠ b := by
      intro h; subst h
      exact (Finset.disjoint_left.mp hO_Esp_disj) (Finset.mem_coe.mp ha) (Finset.mem_coe.mp hb)
    have hpa := hpz_loc a (Finset.mem_coe.mp ha)
    have hrb := hyr_loc b (Finset.mem_coe.mp hb)
    have hrb' : yr b ∈ Set.Ioo (b - r) (b + r) := ⟨lt_trans (by linarith [hr_pos]) hrb.1, hrb.2⟩
    have hdisjab := hdisj a haZf b hbZf hab_ne
    rw [Set.disjoint_left] at hdisjab
    exact hdisjab hpa (hwb ▸ hrb')
  have hWl_Wr_disj : Disjoint Wl Wr := by
    rw [Set.disjoint_left]
    rintro w ⟨a, ha, rfl⟩ ⟨b, hb, hwb⟩
    have haZf := hEsp_subZf a ha
    have hbZf := hEsp_subZf b hb
    by_cases hab : a = b
    · subst hab
      have hla := hyl_loc a (Finset.mem_coe.mp ha)
      have hra := hyr_loc a (Finset.mem_coe.mp hb)
      -- yl a < a < yr a, but hwb : yl a = yr a
      have : yl a < yr a := lt_trans hla.2 hra.1
      rw [hwb] at this; exact lt_irrefl _ this
    · have hla := hyl_loc a (Finset.mem_coe.mp ha)
      have hra := hyr_loc b (Finset.mem_coe.mp hb)
      have hla' : yl a ∈ Set.Ioo (a - r) (a + r) := ⟨hla.1, lt_trans hla.2 (by linarith [hr_pos])⟩
      have hra' : yr b ∈ Set.Ioo (b - r) (b + r) := ⟨lt_trans (by linarith [hr_pos]) hra.1, hra.2⟩
      have hdisjab := hdisj a haZf b hbZf hab
      rw [Set.disjoint_left] at hdisjab
      exact hdisjab hla' (hwb ▸ hra')
  -- cardinality of the union
  have hWo_card : Wo.encard = (O.card : ℕ∞) := by
    rw [hWo_def, hpz_inj.encard_image, Set.encard_coe_eq_coe_finsetCard]
  have hWl_card : Wl.encard = (Esp.card : ℕ∞) := by
    rw [hWl_def, hyl_inj.encard_image, Set.encard_coe_eq_coe_finsetCard]
  have hWr_card : Wr.encard = (Esp.card : ℕ∞) := by
    rw [hWr_def, hyr_inj.encard_image, Set.encard_coe_eq_coe_finsetCard]
  have hWunion_card : (Wo ∪ Wl ∪ Wr).encard = (O.card : ℕ∞) + (Esp.card : ℕ∞) + (Esp.card : ℕ∞) := by
    rw [Set.encard_union_eq (Disjoint.union_left hWo_Wr_disj hWl_Wr_disj),
        Set.encard_union_eq hWo_Wl_disj, hWo_card, hWl_card, hWr_card]
  -- final inequality
  have hZenc : Z.encard = (Zf.card : ℕ∞) := by
    rw [hZf_def, Set.Finite.encard_eq_coe_toFinset_card hZfin]
  -- n = |Z| ≤ |O| + 2|Esp| = |W| ≤ encard (zeroSet P)
  have hcount_nat : Zf.card ≤ O.card + Esp.card + Esp.card := by
    rw [hcardZ]; omega
  calc Z.encard = (Zf.card : ℕ∞) := hZenc
    _ ≤ ((O.card + Esp.card + Esp.card : ℕ) : ℕ∞) := by exact_mod_cast hcount_nat
    _ = (O.card : ℕ∞) + (Esp.card : ℕ∞) + (Esp.card : ℕ∞) := by push_cast; ring
    _ = (Wo ∪ Wl ∪ Wr).encard := hWunion_card.symm
    _ ≤ (zeroSet P).encard := Set.encard_mono hW_sub

/-- **First reduction, count non-decrease under a single-coefficient
perturbation.**

Let `S` have `k ≥ 1` components, a nonzero coefficient, `S.density ≢ 0` and
finitely many real zeros, and fix an index `i₀` with `a_{i₀} ≠ 0`. Then there is
a sign `s ∈ {+1, -1}` and a threshold `ε₀ > 0` such that for every `ε ∈ (0, ε₀)`,
if all zeros of `S_ε := coeffPerturbSub S i₀ (s·ε)` are simple, then the number of
distinct real zeros does not decrease:
`zeroCount S.density ≤ zeroCount (coeffPerturbSub S i₀ (s·ε)).density`. -/
theorem FirstReductionCountNonDecrease
    (S : SignedGaussianCombination)
    (hk : 1 ≤ S.components.length)
    (hne : ∃ x : ℝ, S.density x ≠ 0)
    (i₀ : Fin S.components.length)
    (ha : (S.components.get i₀).1 ≠ 0) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∀ x : ℝ, (coeffPerturbSub S i₀ (s * ε)).density x = 0 →
            deriv (coeffPerturbSub S i₀ (s * ε)).density x ≠ 0) →
        zeroCount S.density ≤ zeroCount (coeffPerturbSub S i₀ (s * ε)).density := by
  -- Set up f and G
  set f := S.density with hf_def
  set G := (S.components.get i₀).2.density with hG_def
  -- analyticity, positivity, finiteness
  have hf_an : AnalyticOnNhd ℝ f Set.univ := SublemmaSGCDensityIsAnalytic S
  have hGcont : Continuous G := by
    rw [hG_def, GaussianPDF.density_def]
    fun_prop
  have hGpos : ∀ x, 0 < G x := fun x => gaussian_density_pos _ x
  have hZfin : (zeroSet f).Finite := (FinitenessOfSignedGaussianZeros S hne).1
  -- apply the general lemma
  obtain ⟨s, hs, ε₀, hε₀, hmain⟩ := general_count_nondecrease f hf_an G hGcont hGpos hZfin
  refine ⟨s, hs, ε₀, hε₀, ?_⟩
  intro ε hεpos hεlt _hsimple
  -- rewrite the perturbed density via (★)
  have hpert : (fun x => f x - s * ε * G x)
      = (coeffPerturbSub S i₀ (s * ε)).density := by
    funext x
    rw [coeffPerturbSub_density S i₀ (s * ε) x]
  have := hmain ε hεpos hεlt
  rw [hpert] at this
  -- zeroCount = encard, definitionally
  rw [zeroCount_def, zeroCount_def]
  exact this

end Workspace.ProofLemmas
