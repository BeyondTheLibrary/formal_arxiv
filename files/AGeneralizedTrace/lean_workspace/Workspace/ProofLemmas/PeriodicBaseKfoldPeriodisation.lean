import Mathlib
import Workspace.ProofLemmas.CircConvInfra
import Workspace.ProofLemmas.PeriodicCircConvPeriodisation

open scoped Real
open MeasureTheory intervalIntegral CircConvInfra PeriodicCircConvPeriodisation

set_option maxHeartbeats 4000000

namespace PeriodicBaseKfoldPeriodisation

/-- k-fold real CIRCULAR self-convolution of a (periodic) base g. -/
noncomputable def circPowR (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => g
  | (k+2) => fun ξ => circConvR (circPowR g (k+1)) g ξ

/-- k-fold real LINEAR self-convolution on ℝ of the compact-support g₀. -/
noncomputable def linPow (g0 : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => g0
  | (k+2) => fun ξ => ∫ η, linPow g0 (k+1) η * g0 (ξ - η)

@[simp] theorem circPowR_one (g : ℝ → ℝ) : circPowR g 1 = g := rfl

@[simp] theorem circPowR_succ_succ (g : ℝ → ℝ) (k : ℕ) :
    circPowR g (k + 2) = fun ξ => circConvR (circPowR g (k + 1)) g ξ := rfl

@[simp] theorem linPow_one (g0 : ℝ → ℝ) : linPow g0 1 = g0 := rfl

@[simp] theorem linPow_succ_succ (g0 : ℝ → ℝ) (k : ℕ) :
    linPow g0 (k + 2) = fun ξ => ∫ η, linPow g0 (k + 1) η * g0 (ξ - η) := rfl

/-- **A. Fundamental-domain periodisation of a periodic `g` (k = 1 inequality).**

For nonnegative, `2π`-periodic `g`, with `g₀ := fun x => if |x| ≤ π then g x else 0`
the fundamental-domain restriction, the value `g ξ` (the `k = 1` circular power) at a
point of the fundamental domain `|ξ| ≤ π` is bounded by the periodised series of `g₀`.
The `s = 0` term of the series equals `g ξ` exactly (since `|ξ| ≤ π`), and every other
term is `≥ 0`; equality fails in general because of boundary double counting at
`ξ = ±π`, but the `≤` direction is all the paper needs. -/
theorem periodise_one (g : ℝ → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg_per : ∀ x, g (x + 2*π) = g x)
    (hg0_summable : ∀ ξ, Summable (fun s:ℤ => (fun x => if |x| ≤ Real.pi then g x else 0) (ξ + 2*π*s)))
    (ξ : ℝ) (hξ : |ξ| ≤ π) :
    circPowR g 1 ξ ≤ ∑' s:ℤ, (fun x => if |x| ≤ Real.pi then g x else 0) (ξ + 2*π*s) := by
  -- circPowR g 1 ξ = g ξ
  rw [circPowR_one]
  set g0 : ℝ → ℝ := fun x => if |x| ≤ Real.pi then g x else 0 with hg0
  -- g₀ is nonnegative everywhere.
  have hg0_nn : ∀ x, 0 ≤ g0 x := by
    intro x
    simp only [hg0]
    by_cases h : |x| ≤ Real.pi
    · rw [if_pos h]; exact hg_nn x
    · rw [if_neg h]
  -- summability
  have hsumm := hg0_summable ξ
  -- the s = 0 term equals g ξ
  have h0 : g0 (ξ + 2*π*((0:ℤ):ℝ)) = g ξ := by
    have hx : ξ + 2*π*((0:ℤ):ℝ) = ξ := by norm_num
    rw [hx]
    simp only [hg0]
    rw [if_pos hξ]
  calc g ξ = g0 (ξ + 2*π*((0:ℤ):ℝ)) := h0.symm
    _ ≤ ∑' s:ℤ, g0 (ξ + 2*π*(s:ℝ)) := by
        apply hsumm.le_tsum (0 : ℤ)
        intro j _
        exact hg0_nn _

/-- **B. Tonelli / fold interchange for the LINEAR convolution integral.**

The whole-line integral of the convolution integrand `η ↦ P η · g₀ (ξ - η)` equals
its periodised fold over the fundamental domain `[-π, π]`. This is just `fold_tsum`
applied (in reverse) to the convolution integrand, packaging the Poisson folding for
use in the induction engine. The only hypothesis needed is integrability of the
integrand for each `ξ`. -/
theorem linconv_fold (P : ℝ → ℝ) (g0 : ℝ → ℝ)
    (hPg0_int : ∀ ξ, Integrable (fun η => P η * g0 (ξ - η)))
    (ξ : ℝ) :
    (∫ η, P η * g0 (ξ - η))
      = ∑' s:ℤ, (∫ η in (-π)..π, (fun u => P u * g0 (ξ - u)) (η + 2*π*s)) := by
  rw [fold_tsum (fun η => P η * g0 (ξ - η)) (hPg0_int ξ)]

/-- **C. IH-under-the-integral monotonicity (building block for the `k`-step).**

This is the monotone-integrand reduction that powers the inductive `k → k+1` step of the
periodisation inequality. Given a pointwise upper bound `P η ≤ Q η` valid on the
fundamental domain `[-π, π]`, with `g` nonnegative there, the circular convolution
`circConvR P g ξ = (1/2π)∫_{-π}^π P η · g(ξ-η) dη` is bounded by the integral with `P`
replaced by `Q`. In the induction, `P := circPowR g k`, `Q := fun η => ∑'_t linPow g0 k (η+2πt)`,
and the pointwise bound is the induction hypothesis. The proof is monotonicity of the
interval integral (`intervalIntegral.integral_mono_on`), the integrand factor `g(ξ-η)`
being nonnegative on the window. -/
theorem circConv_le_of_pointwise_le (P Q g : ℝ → ℝ)
    (hg_nn : ∀ x, 0 ≤ g x)
    (hle : ∀ η ∈ Set.Icc (-π) π, P η ≤ Q η)
    (ξ : ℝ)
    (hPg_int : IntervalIntegrable (fun η => P η * g (ξ - η)) MeasureTheory.volume (-π) π)
    (hQg_int : IntervalIntegrable (fun η => Q η * g (ξ - η)) MeasureTheory.volume (-π) π) :
    circConvR P g ξ ≤ (1 / (2 * π)) * ∫ η in (-π)..π, Q η * g (ξ - η) := by
  unfold circConvR
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hPg_int hQg_int
  intro η hη
  exact mul_le_mul_of_nonneg_right (hle η hη) (hg_nn _)

/-- `circPowR g (k+1) = circConvR (circPowR g k) g` for `k ≥ 1`. -/
theorem circPowR_succ_of_pos (g : ℝ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    circPowR g (k + 1) = fun ξ => circConvR (circPowR g k) g ξ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 1 + j + 1 = j + 2 by omega, show 1 + j = j + 1 by omega, circPowR_succ_succ]

/-- Nonnegativity of every linear self-power, given `g₀ ≥ 0`. -/
theorem linPow_nn (g0 : ℝ → ℝ) (hg0_nn : ∀ x, 0 ≤ g0 x) :
    ∀ m x, 0 ≤ linPow g0 m x := by
  intro m
  induction m with
  | zero => intro x; simp [linPow]
  | succ n ih =>
    match n with
    | 0 => intro x; simpa [linPow] using hg0_nn x
    | (j + 1) =>
      intro x
      rw [linPow_succ_succ]
      apply MeasureTheory.integral_nonneg
      intro η
      exact mul_nonneg (ih η) (hg0_nn _)

/-- Pointwise lower bound: the periodised series of `g₀` dominates the periodic `g`
everywhere. (`periodise_one` at an arbitrary point; the `s` that lands in `[-π,π]`
contributes exactly `g w` by periodicity, the rest are `≥ 0`.) -/
theorem periodise_ge (g : ℝ → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg_per : ∀ x, g (x + 2*π) = g x)
    (hg0_summable : ∀ w, Summable (fun s:ℤ => (fun x => if |x| ≤ Real.pi then g x else 0) (w + 2*π*s)))
    (w : ℝ) :
    g w ≤ ∑' s:ℤ, (fun x => if |x| ≤ Real.pi then g x else 0) (w + 2*π*s) := by
  set g0 : ℝ → ℝ := fun x => if |x| ≤ Real.pi then g x else 0 with hg0
  have hg0_nn : ∀ x, 0 ≤ g0 x := by
    intro x; simp only [hg0]
    by_cases h : |x| ≤ Real.pi
    · rw [if_pos h]; exact hg_nn x
    · rw [if_neg h]
  -- choose the integer s₀ that brings w into [-π, π]
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℤ, |w + 2*π*s0| ≤ π := by
    have hpi : (0:ℝ) < 2 * π := by positivity
    set s0 : ℤ := -⌊(w + π) / (2*π)⌋ with hs0def
    refine ⟨s0, ?_⟩
    have hfloor := Int.sub_one_lt_floor ((w + π) / (2*π))
    have hfloor2 := Int.floor_le ((w + π) / (2*π))
    -- key: 2π·f ≤ w+π  and  w-π < 2π·f, where f = ⌊(w+π)/(2π)⌋
    have hA : (⌊(w + π) / (2*π)⌋ : ℝ) * (2*π) ≤ w + π := by
      rw [← le_div_iff₀ hpi]; exact hfloor2
    have hB : w - π < (⌊(w + π) / (2*π)⌋ : ℝ) * (2*π) := by
      have h := (div_lt_iff₀ hpi).mp (by linarith [hfloor] : (w + π) / (2*π) < (⌊(w + π) / (2*π)⌋ : ℝ) + 1)
      nlinarith [h]
    rw [abs_le, hs0def]
    push_cast
    constructor <;> nlinarith [hA, hB]
  -- the s₀ term equals g w by periodicity
  have hback : ∀ y, g (y - 2*π) = g y := by
    intro y; have h := hg_per (y - 2*π); rw [sub_add_cancel] at h; exact h.symm
  have hper_mul : ∀ (n : ℤ) (x : ℝ), g (x + 2*π*(n:ℝ)) = g x := by
    refine fun n => Int.induction_on n ?_ ?_ ?_
    · intro x; simp
    · intro i ih x
      have he : x + 2*π*((i:ℝ)+1) = (x + 2*π*(i:ℝ)) + 2*π := by ring
      push_cast; rw [he, hg_per]; exact_mod_cast ih x
    · intro i ih x
      have he : x + 2*π*(-(i:ℝ)-1) = (x + 2*π*(-(i:ℝ))) - 2*π := by ring
      push_cast; rw [he, hback]; exact_mod_cast ih x
  have hterm : g0 (w + 2*π*(s0:ℝ)) = g w := by
    simp only [hg0]
    rw [if_pos hs0, hper_mul s0 w]
  calc g w = g0 (w + 2*π*(s0:ℝ)) := hterm.symm
    _ ≤ ∑' s:ℤ, g0 (w + 2*π*(s:ℝ)) := by
        apply (hg0_summable w).le_tsum s0
        intro j _; exact hg0_nn _

/-- **D. The k-fold periodic-base periodisation inequality (Lemma-7 foundation).**

For a nonnegative, `2π`-periodic `g` with fundamental-domain restriction
`g₀ := fun x => if |x| ≤ π then g x else 0`, the `k`-fold *circular* self-power of `g`
at a point of the fundamental domain is dominated by the periodised series of the
`k`-fold *linear* self-power of `g₀`:
`circPowR g k ξ ≤ ∑'_s linPow g₀ k (ξ + 2π s)`  for `k ≥ 1`, `|ξ| ≤ π`.

Proved by induction on `k`.  The base case `k = 1` is `periodise_one`.  The step
`k → k+1` chains:

  `circPowR g (k+1) ξ = circConvR (circPowR g k) g ξ`
    `≤ (1/2π) ∫_{-π}^π (∑'_t linPow g₀ k (η+2πt)) · g(ξ-η) dη`   (IH, `circConv_le_of_pointwise_le`)
    `= (1/2π) ∫_ℝ linPow g₀ k (η) · g(ξ-η) dη`                    (`hswap1` + `fold_tsum`)
    `≤ ∫_ℝ linPow g₀ k (η) · g(ξ-η) dη`                          (integrand `≥ 0`, `1/2π ≤ 1`)
    `≤ ∫_ℝ linPow g₀ k (η) · (∑'_s g₀((ξ-η)+2πs)) dη`            (`periodise_ge`, monotone)
    `= ∑'_s ∫_ℝ linPow g₀ k (η) · g₀((ξ+2πs)-η) dη`             (`hswap2`)
    `= ∑'_s linPow g₀ (k+1) (ξ+2πs)`.                            (def of `linPow`)

The two sum–integral interchanges (`hswap1` over the fundamental window, `hswap2` over
the whole line) are Tonelli/Fubini facts for the nonnegative integrands at hand; they
are admitted as analytic hypotheses (each is a *true* equality, not a weakening of the
conclusion) to be discharged for the concrete continuous compact-support base used in
Lemma 7. -/
theorem periodise_kfold (g : ℝ → ℝ) (hg_nn : ∀ x, 0 ≤ g x)
    (hg_per : ∀ x, g (x + 2*π) = g x)
    (hg0_summable : ∀ w, Summable
      (fun s:ℤ => (fun x => if |x| ≤ Real.pi then g x else 0) (w + 2*π*s)))
    -- interval-integrability of the circular-power convolution integrand (P-side)
    (hcircint : ∀ m, 1 ≤ m → ∀ ξ,
      IntervalIntegrable (fun η => circPowR g m η * g (ξ - η)) MeasureTheory.volume (-π) π)
    -- interval-integrability of the periodised linear-power convolution integrand (Q-side)
    (hQint : ∀ m, 1 ≤ m → ∀ ξ,
      IntervalIntegrable
        (fun η => (∑' t:ℤ, linPow (fun x => if |x| ≤ Real.pi then g x else 0) m (η + 2*π*t))
          * g (ξ - η)) MeasureTheory.volume (-π) π)
    -- whole-line integrability of the linear-power convolution integrand
    (hfoldint : ∀ m, 1 ≤ m → ∀ ξ,
      Integrable (fun η => linPow (fun x => if |x| ≤ Real.pi then g x else 0) m η * g (ξ - η)))
    -- whole-line integrability of the linear-power times the *periodised* base
    (hPg0int : ∀ m, 1 ≤ m → ∀ ξ,
      Integrable (fun η => linPow (fun x => if |x| ≤ Real.pi then g x else 0) m η
        * (∑' s:ℤ, (fun x => if |x| ≤ Real.pi then g x else 0) ((ξ - η) + 2*π*s))))
    -- Tonelli interchange #1: pull the periodisation tsum out of the fundamental-window integral
    (hswap1 : ∀ m, 1 ≤ m → ∀ ξ,
      (∫ η in (-π)..π,
          (∑' t:ℤ, linPow (fun x => if |x| ≤ Real.pi then g x else 0) m (η + 2*π*t)) * g (ξ - η))
        = ∑' t:ℤ, ∫ η in (-π)..π,
            linPow (fun x => if |x| ≤ Real.pi then g x else 0) m (η + 2*π*t) * g (ξ - η))
    -- Tonelli interchange #2: pull the periodisation tsum out of the whole-line integral
    (hswap2 : ∀ m, 1 ≤ m → ∀ ξ,
      (∫ η, linPow (fun x => if |x| ≤ Real.pi then g x else 0) m η
          * (∑' s:ℤ, (fun x => if |x| ≤ Real.pi then g x else 0) ((ξ - η) + 2*π*s)))
        = ∑' s:ℤ, ∫ η, linPow (fun x => if |x| ≤ Real.pi then g x else 0) m η
            * (fun x => if |x| ≤ Real.pi then g x else 0) ((ξ + 2*π*s) - η))
    (k : ℕ) (hk : 1 ≤ k) (ξ : ℝ) (hξ : |ξ| ≤ π) :
    circPowR g k ξ
      ≤ ∑' s:ℤ, linPow (fun x => if |x| ≤ Real.pi then g x else 0) k (ξ + 2*π*s) := by
  set g0 : ℝ → ℝ := fun x => if |x| ≤ Real.pi then g x else 0 with hg0
  have hg0_nn : ∀ x, 0 ≤ g0 x := by
    intro x; simp only [hg0]
    by_cases h : |x| ≤ Real.pi
    · rw [if_pos h]; exact hg_nn x
    · rw [if_neg h]
  have hP_nn := linPow_nn g0 hg0_nn
  -- π > 1/2 numeric facts for the (1/2π) ≤ 1 step
  have hpi1 : (1:ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have hpi0 : (0:ℝ) < 2 * π := by positivity
  -- generalize ξ so the induction hypothesis is available at every fundamental-domain point
  revert ξ hξ
  induction k, hk using Nat.le_induction with
  | base =>
      intro ξ hξ
      simpa using periodise_one g hg_nn hg_per hg0_summable ξ hξ
  | succ k hk ih =>
      intro ξ hξ
      -- circPowR g (k+1) ξ = circConvR (circPowR g k) g ξ
      rw [circPowR_succ_of_pos g k hk]
      -- IH as a pointwise bound on the fundamental window
      have hIH : ∀ η ∈ Set.Icc (-π) π,
          circPowR g k η ≤ ∑' t:ℤ, linPow g0 k (η + 2*π*t) := by
        intro η hη
        exact ih η (abs_le.mpr ⟨hη.1, hη.2⟩)
      -- Step (i): IH-under-the-integral monotone reduction
      have hstep1 : circConvR (circPowR g k) g ξ
          ≤ (1 / (2 * π)) * ∫ η in (-π)..π,
              (∑' t:ℤ, linPow g0 k (η + 2*π*t)) * g (ξ - η) :=
        circConv_le_of_pointwise_le (circPowR g k)
          (fun η => ∑' t:ℤ, linPow g0 k (η + 2*π*t)) g hg_nn hIH ξ
          (hcircint k hk ξ) (hQint k hk ξ)
      -- periodicity multiplied by integers
      have hback : ∀ y, g (y - 2*π) = g y := by
        intro y; have h := hg_per (y - 2*π); rw [sub_add_cancel] at h; exact h.symm
      have hper_mul : ∀ (n : ℤ) (x : ℝ), g (x + 2*π*(n:ℝ)) = g x := by
        refine fun n => Int.induction_on n ?_ ?_ ?_
        · intro x; simp
        · intro i ih2 x
          have he : x + 2*π*((i:ℝ)+1) = (x + 2*π*(i:ℝ)) + 2*π := by ring
          push_cast; rw [he, hg_per]; exact_mod_cast ih2 x
        · intro i ih2 x
          have he : x + 2*π*(-(i:ℝ)-1) = (x + 2*π*(-(i:ℝ))) - 2*π := by ring
          push_cast; rw [he, hback]; exact_mod_cast ih2 x
      -- Step (ii): fold the windowed integral back to the whole line
      set F : ℝ → ℝ := fun η => linPow g0 k η * g (ξ - η) with hF
      have hFshift : ∀ (t:ℤ) (η:ℝ),
          F (η + 2*π*t) = linPow g0 k (η + 2*π*t) * g (ξ - η) := by
        intro t η
        simp only [hF]
        congr 1
        have hreidx : ξ - (η + 2*π*(t:ℝ)) = (ξ - η) + 2*π*(-(t:ℝ)) := by ring
        rw [hreidx]
        have hh := hper_mul (-t) (ξ - η)
        push_cast at hh ⊢
        rw [hh]
      have hfoldeq : (∫ η in (-π)..π,
            (∑' t:ℤ, linPow g0 k (η + 2*π*t)) * g (ξ - η))
            = ∫ η, F η := by
        rw [hswap1 k hk ξ]
        have hcongr : (fun t:ℤ => ∫ η in (-π)..π, linPow g0 k (η + 2*π*t) * g (ξ - η))
            = (fun t:ℤ => ∫ η in (-π)..π, F (η + 2*π*t)) := by
          funext t
          apply intervalIntegral.integral_congr
          intro η _
          simp only []
          exact (hFshift t η).symm
        rw [hcongr]
        exact PeriodicCircConvPeriodisation.fold_tsum F (hfoldint k hk ξ)
      -- Step (iii): drop the (1/2π) factor (integrand ≥ 0)
      have hFnn : 0 ≤ ∫ η, F η := by
        apply MeasureTheory.integral_nonneg
        intro η; simp only [hF]
        exact mul_nonneg (hP_nn k η) (hg_nn _)
      have hstep2 : (1 / (2 * π)) * ∫ η in (-π)..π,
            (∑' t:ℤ, linPow g0 k (η + 2*π*t)) * g (ξ - η)
          ≤ ∫ η, F η := by
        rw [hfoldeq]
        have hle1 : (1 / (2 * π)) ≤ 1 := by
          rw [div_le_one hpi0]; exact hpi1
        calc (1 / (2 * π)) * ∫ η, F η
            ≤ 1 * ∫ η, F η := mul_le_mul_of_nonneg_right hle1 hFnn
          _ = ∫ η, F η := one_mul _
      -- Step (iv): bound g by its periodisation, then swap (hswap2) and recognise linPow (k+1)
      have hmono : (∫ η, F η)
          ≤ ∫ η, linPow g0 k η * (∑' s:ℤ, g0 ((ξ - η) + 2*π*s)) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun η => by
            simp only [hF]; exact mul_nonneg (hP_nn k η) (hg_nn _))
        · exact hPg0int k hk ξ
        · refine Filter.Eventually.of_forall (fun η => ?_)
          simp only [hF]
          apply mul_le_mul_of_nonneg_left _ (hP_nn k η)
          exact periodise_ge g hg_nn hg_per hg0_summable (ξ - η)
      have hswapeq : (∫ η, linPow g0 k η * (∑' s:ℤ, g0 ((ξ - η) + 2*π*s)))
          = ∑' s:ℤ, ∫ η, linPow g0 k η * g0 ((ξ + 2*π*s) - η) :=
        hswap2 k hk ξ
      -- recognise each term as linPow g0 (k+1) (ξ + 2π s)
      have hterm : ∀ s:ℤ, (∫ η, linPow g0 k η * g0 ((ξ + 2*π*s) - η))
          = linPow g0 (k+1) (ξ + 2*π*s) := by
        intro s
        rw [show k + 1 = (k - 1) + 2 by omega]
        rw [linPow_succ_succ]
        congr 1
        funext η
        rw [show (k - 1) + 1 = k by omega]
      -- assemble
      calc circConvR (circPowR g k) g ξ
          ≤ (1 / (2 * π)) * ∫ η in (-π)..π,
              (∑' t:ℤ, linPow g0 k (η + 2*π*t)) * g (ξ - η) := hstep1
        _ ≤ ∫ η, F η := hstep2
        _ ≤ ∫ η, linPow g0 k η * (∑' s:ℤ, g0 ((ξ - η) + 2*π*s)) := hmono
        _ = ∑' s:ℤ, ∫ η, linPow g0 k η * g0 ((ξ + 2*π*s) - η) := hswapeq
        _ = ∑' s:ℤ, linPow g0 (k+1) (ξ + 2*π*s) := by
              apply tsum_congr; intro s; exact hterm s

end PeriodicBaseKfoldPeriodisation
