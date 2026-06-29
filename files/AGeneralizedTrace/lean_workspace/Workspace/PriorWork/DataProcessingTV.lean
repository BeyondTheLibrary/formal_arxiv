-- Source: the classical data-processing / information-processing inequality for
-- statistical (total-variation) distance. The paper invokes it BY NAME ("by the
-- information processing inequality") at deletion.tex:289 (and again ~line 412)
-- WITHOUT giving any textbook citation. It is genuinely classical. We give a full
-- self-contained proof below (the TV contraction under a Markov kernel), so this
-- is no longer admitted as an axiom.
-- Paper label: "the information processing inequality" (deletion.tex:289)
-- NL statement: Let X, Y be countable spaces, K : X → PMF(Y) a Markov kernel, and μ, ν ∈ PMF(X). Then the pushforward PMFs K_*μ, K_*ν ∈ PMF(Y) defined by (K_*μ)(y) = ∑_x μ(x) K(x)(y) satisfy d_TV(K_*μ, K_*ν) ≤ d_TV(μ, ν), where d_TV(ρ, σ) := (1/2) ∑_y |ρ(y) - σ(y)|.
import Mathlib

open scoped ENNReal

namespace Workspace.PriorWork.DataProcessingTVns

/-- `(p.bind K) y` in `ℝ`, as a `tsum` over `x`. -/
private lemma bind_toReal
    {α : Type*} {β : Type*} [Countable α] [Countable β]
    (K : α → PMF β) (p : PMF α) (y : β) :
    ((p.bind K) y).toReal = ∑' x : α, (p x).toReal * (K x y).toReal := by
  rw [PMF.bind_apply]
  rw [ENNReal.tsum_toReal_eq
    (fun x => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  simp [ENNReal.toReal_mul]

/-- `x ↦ (p x).toReal * (K x y).toReal` is summable. -/
private lemma summable_mul_toReal
    {α : Type*} {β : Type*} [Countable α] [Countable β]
    (K : α → PMF β) (p : PMF α) (y : β) :
    Summable (fun x : α => (p x).toReal * (K x y).toReal) := by
  have hp : Summable (fun x : α => (p x).toReal) :=
    (ENNReal.hasSum_toReal (PMF.tsum_coe_ne_top p)).summable
  apply Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) hp
  have hK : (K x y).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one (K x) y)
  nlinarith [ENNReal.toReal_nonneg (a := p x), ENNReal.toReal_nonneg (a := K x y)]

/-- The signed real difference of the two pushforwards at `y`, written as a single
`tsum` over `x` in `ℝ`. -/
private lemma bind_diff_toReal
    {α : Type*} {β : Type*} [Countable α] [Countable β]
    (K : α → PMF β) (μ ν : PMF α) (y : β) :
    ((μ.bind K) y).toReal - ((ν.bind K) y).toReal
      = ∑' x : α, ((μ x).toReal - (ν x).toReal) * (K x y).toReal := by
  rw [bind_toReal, bind_toReal,
    ← Summable.tsum_sub (summable_mul_toReal K μ y) (summable_mul_toReal K ν y)]
  congr 1
  ext x
  ring

/-- Abbreviation for the per-coordinate TV summand in `ℝ`. -/
private noncomputable def D {α : Type*} (μ ν : PMF α) (x : α) : ℝ :=
  |(μ x).toReal - (ν x).toReal|

private lemma D_nonneg {α : Type*} (μ ν : PMF α) (x : α) : 0 ≤ D μ ν x :=
  abs_nonneg _

/-- Per-`y` bound in `ℝ≥0∞`. -/
private lemma per_y_bound
    {α : Type*} {β : Type*} [Countable α] [Countable β]
    (K : α → PMF β) (μ ν : PMF α) (y : β) :
    ENNReal.ofReal |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|
      ≤ ∑' x : α, ENNReal.ofReal (D μ ν x) * K x y := by
  -- First, the real-valued per-y bound.
  -- Summability of the signed family `x ↦ (μx-νx).toReal * (Kxy).toReal`.
  have hsumsigned : Summable (fun x : α =>
      ((μ x).toReal - (ν x).toReal) * (K x y).toReal) := by
    have h1 := summable_mul_toReal K μ y
    have h2 := summable_mul_toReal K ν y
    have := h1.sub h2
    refine this.congr (fun x => ?_)
    ring
  -- Summability of the absolute-value family, equal to `D μ ν x * (Kxy).toReal`.
  have hsummabs : Summable (fun x : α => D μ ν x * (K x y).toReal) := by
    refine (hsumsigned.abs).congr (fun x => ?_)
    rw [D, abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg (a := K x y))]
  have hreal : |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|
      ≤ ∑' x : α, D μ ν x * (K x y).toReal := by
    rw [bind_diff_toReal]
    calc |∑' x : α, ((μ x).toReal - (ν x).toReal) * (K x y).toReal|
        ≤ ∑' x : α, |((μ x).toReal - (ν x).toReal) * (K x y).toReal| := by
          have hnorm := norm_tsum_le_tsum_norm
            (f := fun x : α => ((μ x).toReal - (ν x).toReal) * (K x y).toReal)
            (by simpa [Real.norm_eq_abs] using hsumsigned.abs)
          simpa [Real.norm_eq_abs] using hnorm
      _ = ∑' x : α, D μ ν x * (K x y).toReal := by
          congr 1; ext x
          rw [D, abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg (a := K x y))]
  -- Lift to ENNReal.
  calc ENNReal.ofReal |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|
      ≤ ENNReal.ofReal (∑' x : α, D μ ν x * (K x y).toReal) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ∑' x : α, ENNReal.ofReal (D μ ν x * (K x y).toReal) :=
        ENNReal.ofReal_tsum_of_nonneg
          (fun x => by have := D_nonneg μ ν x; positivity) hsummabs
    _ = ∑' x : α, ENNReal.ofReal (D μ ν x) * K x y := by
        congr 1; ext x
        rw [ENNReal.ofReal_mul (D_nonneg μ ν x), ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

theorem DataProcessingTV
    {α : Type*} {β : Type*} [Countable α] [Countable β]
    (K : α → PMF β) (μ ν : PMF α) :
  (1 / 2 : ℝ) * ∑' y : β, |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|
    ≤ (1 / 2 : ℝ) * ∑' x : α, |(μ x).toReal - (ν x).toReal| := by
  -- Core inequality in `ℝ≥0∞`.
  have key :
      (∑' y : β, ENNReal.ofReal |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|)
        ≤ ∑' x : α, ENNReal.ofReal (D μ ν x) := by
    calc (∑' y : β, ENNReal.ofReal |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|)
        ≤ ∑' y : β, ∑' x : α, ENNReal.ofReal (D μ ν x) * K x y :=
          ENNReal.tsum_le_tsum (fun y => per_y_bound K μ ν y)
      _ = ∑' x : α, ∑' y : β, ENNReal.ofReal (D μ ν x) * K x y := ENNReal.tsum_comm
      _ = ∑' x : α, ENNReal.ofReal (D μ ν x) := by
          congr 1; ext x
          rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  -- The RHS in `ℝ≥0∞` is finite (bounded by 2).
  have hRHSfin : (∑' x : α, ENNReal.ofReal (D μ ν x)) ≠ ⊤ := by
    have hbound : ∀ x : α, ENNReal.ofReal (D μ ν x) ≤ μ x + ν x := by
      intro x
      have hle : D μ ν x ≤ (μ x).toReal + (ν x).toReal := by
        rw [D, abs_le]
        constructor <;> nlinarith [ENNReal.toReal_nonneg (a := μ x),
          ENNReal.toReal_nonneg (a := ν x)]
      calc ENNReal.ofReal (D μ ν x)
          ≤ ENNReal.ofReal ((μ x).toReal + (ν x).toReal) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (μ x).toReal + ENNReal.ofReal (ν x).toReal :=
            ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        _ = μ x + ν x := by
            rw [ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
              ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
    have : (∑' x : α, ENNReal.ofReal (D μ ν x)) ≤ ∑' x : α, (μ x + ν x) :=
      ENNReal.tsum_le_tsum hbound
    have hsum2 : (∑' x : α, (μ x + ν x)) = 2 := by
      rw [ENNReal.tsum_add, PMF.tsum_coe, PMF.tsum_coe]
      norm_num
    rw [hsum2] at this
    exact ne_top_of_le_ne_top (by norm_num) this
  -- Convert `key` to `ℝ`.
  have hLHStoReal :
      (∑' y : β, ENNReal.ofReal |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|).toReal
        = ∑' y : β, |((μ.bind K) y).toReal - ((ν.bind K) y).toReal| := by
    rw [ENNReal.tsum_toReal_eq (fun y => ENNReal.ofReal_ne_top)]
    congr 1; ext y
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  have hRHStoReal :
      (∑' x : α, ENNReal.ofReal (D μ ν x)).toReal = ∑' x : α, D μ ν x := by
    rw [ENNReal.tsum_toReal_eq (fun x => ENNReal.ofReal_ne_top)]
    congr 1; ext x
    rw [ENNReal.toReal_ofReal (D_nonneg μ ν x)]
  have hreal :
      (∑' y : β, |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|)
        ≤ ∑' x : α, D μ ν x := by
    rw [← hLHStoReal, ← hRHStoReal]
    exact ENNReal.toReal_mono hRHSfin key
  -- Multiply both sides by 1/2.
  have heq : ∑' x : α, D μ ν x = ∑' x : α, |(μ x).toReal - (ν x).toReal| := rfl
  rw [heq] at hreal
  linarith [hreal]

end Workspace.PriorWork.DataProcessingTVns

/-- Re-export at the top level with the exact required signature. -/
theorem DataProcessingTV
    {α : Type*} {β : Type*} [Countable α] [Countable β]
    (K : α → PMF β) (μ ν : PMF α) :
  (1 / 2 : ℝ) * ∑' y : β, |((μ.bind K) y).toReal - ((ν.bind K) y).toReal|
    ≤ (1 / 2 : ℝ) * ∑' x : α, |(μ x).toReal - (ν x).toReal| :=
  Workspace.PriorWork.DataProcessingTVns.DataProcessingTV K μ ν
