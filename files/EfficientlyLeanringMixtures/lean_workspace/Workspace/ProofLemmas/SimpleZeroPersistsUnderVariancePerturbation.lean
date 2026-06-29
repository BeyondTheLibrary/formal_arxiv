import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.VariancePerturbFamily
import Workspace.PriorWork.AnalyticIFTSimpleZeroBranch

/-!
# Sub-lemma E (Step 5, Simple-zero persistence under variance perturbation)

Let `S` have only simple real zeros. For any finite set of distinct simple zeros
`x₁ < ⋯ < x_r` of `S.density`, the variance-perturbed `S_δ.density` (family
`variancePerturb`) retains, for all small `δ > 0`, at least `r` distinct real
zeros — one in a small pairwise-disjoint neighborhood of each `x_j`.

Faithful encoding of "at least `r` distinct zeros near the given ones": there is
`ε > 0` whose `ε`-neighborhoods around the `x_j` are pairwise disjoint, together
with an injection `z : Fin r → ℝ` sending each `j` to a zero of `S_δ.density`
within `ε` of `x_j`. Injectivity of `z` plus the disjoint neighborhoods makes the
`z j` genuinely distinct, so `S_δ.density` has at least `r` distinct zeros.

## Proof route

We package the variance-perturbed densities as an explicit one-parameter family
`fFam S c x` (the normalized Gaussian sum with variance
`perturbVarSq σᵢ² c i k = σᵢ² + c·(i+1)/k`), which for `c ≥ 0` is definitionally
`(variancePerturb S c _).density x`. On the open parameter neighbourhood
`goodSet` of `0` (where every perturbed variance stays positive), `fFam` and its
`x`-derivative are jointly continuous; at `c = 0` each `x_j` is a simple zero.
The real-analytic Implicit Function Theorem
(`Workspace.PriorWork.AnalyticIFTSimpleZeroBranch`, which also supplies local
uniqueness) then yields, for each `j`, a continuous branch `φ_j(c)` of zeros with
`φ_j(0) = x_j`. Taking `δ_pers` the minimum of the per-zero radii and `ε` half
the minimal consecutive gap (shrunk so each `φ_j(δ)` stays within `ε` of `x_j`),
the pairwise-disjoint neighbourhoods force `z := fun j => φ_j δ` to be injective.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.ZeroCount

set_option maxHeartbeats 2000000

/-! ## The explicit one-parameter family -/

/-- The variance-perturbed normalized Gaussian family as a function of `(c, x)`.
The variance of the `i`-th component (0-based, `k = S.components.length`) is
`perturbVarSq σᵢ² c i k = σᵢ² + c·(i+1)/k`. This is a *total* function of `c`
(for `c` making some variance non-positive the term degenerates via
`Real.sqrt`-of-nonpositive `= 0`, but we only use it on `goodSet`). -/
noncomputable def fFam (S : SignedGaussianCombination) : ℝ → ℝ → ℝ :=
  fun c x =>
    ((List.finRange S.components.length).map
      (fun i =>
        let p := S.components.get i
        p.1 *
          ((1 / Real.sqrt (2 * Real.pi * (perturbVarSq p.2.varSq c i.val S.components.length)))
            * Real.exp (-(x - p.2.mean) ^ 2 /
                (2 * (perturbVarSq p.2.varSq c i.val S.components.length)))))).sum

/-- For `0 ≤ c`, the family value equals the perturbed-combination density. -/
theorem fFam_eq_density (S : SignedGaussianCombination) (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    fFam S c x = (variancePerturb S c hc).density x := by
  rw [SignedGaussianCombination.density_eq]
  unfold fFam variancePerturb
  simp only [List.map_map]
  apply congrArg
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, GaussianPDF.density_eq]

/-! ## The good parameter set where every perturbed variance is positive -/

/-- The open set of parameters `c` for which every perturbed variance stays
strictly positive. Contains all `c ≥ 0`, in particular `0`. -/
def goodSet (S : SignedGaussianCombination) : Set ℝ :=
  {c : ℝ | ∀ i : Fin S.components.length,
      0 < perturbVarSq (S.components.get i).2.varSq c i.val S.components.length}

theorem goodSet_isOpen (S : SignedGaussianCombination) : IsOpen (goodSet S) := by
  unfold goodSet perturbVarSq
  rw [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  have hcont : Continuous (fun c : ℝ =>
      (S.components.get i).2.varSq + c * (i.val + 1) / S.components.length) := by
    fun_prop
  simpa using (isOpen_lt continuous_const hcont)

theorem goodSet_of_nonneg (S : SignedGaussianCombination) {c : ℝ} (hc : 0 ≤ c) :
    c ∈ goodSet S := by
  intro i
  exact perturbVarSq_pos (S.components.get i).2.varSq_pos hc i.val S.components.length
    (by have := i.pos; omega)

theorem goodSet_zero_mem (S : SignedGaussianCombination) : (0 : ℝ) ∈ goodSet S :=
  goodSet_of_nonneg S le_rfl

/-! ## Values of the family at the base parameter `c = 0` -/

/-- At parameter `c = 0` the family reduces to the unperturbed density: every
perturbed variance `σᵢ² + 0·(i+1)/k = σᵢ²`. -/
theorem fFam_zero (S : SignedGaussianCombination) (x : ℝ) :
    fFam S 0 x = S.density x := by
  rw [SignedGaussianCombination.density_eq]
  conv_rhs => rw [← List.map_get_finRange S.components, List.map_map]
  unfold fFam
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, GaussianPDF.density_eq, perturbVarSq]
  norm_num

/-- As a function of `x`, the `c = 0` slice of the family is exactly `S.density`. -/
theorem fFam_zero_fun (S : SignedGaussianCombination) :
    (fun y => fFam S 0 y) = S.density := by
  funext y; exact fFam_zero S y

/-! ## Joint continuity of the family and its `x`-derivative on `goodSet`

The variance-perturbed Gaussian family `fFam S` and its `x`-derivative are NOT
globally jointly continuous on `ℝ × ℝ` — a perturbed variance
`σᵢ² + c·(i+1)/k` can hit `0`, where Lean's `_/0 = 0` makes the family jump.
They ARE jointly continuous on the open region `goodSet S × ℝ` where every
perturbed variance stays strictly positive. We prove this directly (the family
is a finite sum of Gaussian terms whose denominators are nonzero on `goodSet`,
hence each term, the value, and the `x`-derivative are continuous there). The
global-continuity hypothesis demanded by the IFT axiom is then recovered for the
*clamped* family (see `clampR` / `ift_branch` below), which agrees with `fFam`
for `|c|` small and is globally continuous because the clamp lands inside the
positive-variance region. This is the clamp-globalization trick mirroring
`Workspace.PriorWork.AnalyticDerivOpenCondition`. -/

/-- The explicit `x`-derivative of the `i`-th Gaussian term of `fFam S c · ` at
`x`, valid wherever the perturbed variance `v_i = σᵢ² + c·(i+1)/k` is nonzero:
`a_i · (1/√(2π v_i)) · (exp(-(x-μ_i)²/(2 v_i)) · (-(2(x-μ_i))/(2 v_i)))`. -/
noncomputable def termDeriv
    (S : SignedGaussianCombination) (c x : ℝ) (i : Fin S.components.length) : ℝ :=
  let p := S.components.get i
  let v := perturbVarSq p.2.varSq c i.val S.components.length
  p.1 * ((1 / Real.sqrt (2 * Real.pi * v)) *
    (Real.exp (-(x - p.2.mean) ^ 2 / (2 * v)) * (-(2 * (x - p.2.mean)) / (2 * v))))

/-- The `i`-th Gaussian term of `fFam S c · ` has `x`-derivative `termDeriv S c x i`
at every `x` (no positivity needed: the derivative formula holds for any `v`,
since `_/0 = 0` is differentiable). -/
private theorem term_hasDerivAt
    (S : SignedGaussianCombination) (c x : ℝ) (i : Fin S.components.length) :
    HasDerivAt (fun y =>
      (S.components.get i).1 *
        ((1 / Real.sqrt (2 * Real.pi *
            (perturbVarSq (S.components.get i).2.varSq c i.val S.components.length)))
          * Real.exp (-(y - (S.components.get i).2.mean) ^ 2 /
              (2 * (perturbVarSq (S.components.get i).2.varSq c i.val S.components.length)))))
      (termDeriv S c x i) x := by
  set μ := (S.components.get i).2.mean
  set v := perturbVarSq (S.components.get i).2.varSq c i.val S.components.length
  set a := (S.components.get i).1
  have h0 : HasDerivAt (fun y : ℝ => y - μ) 1 x := (hasDerivAt_id x).sub_const μ
  have h1 : HasDerivAt (fun y : ℝ => (y - μ) ^ 2) (2 * (x - μ)) x := by simpa using h0.pow 2
  have hg : HasDerivAt (fun y => -(y - μ) ^ 2 / (2 * v)) (-(2 * (x - μ)) / (2 * v)) x := by
    simpa using (h1.neg).div_const (2 * v)
  have he := (Real.hasDerivAt_exp (-(x - μ) ^ 2 / (2 * v))).comp x hg
  have hfull := he.const_mul (a * (1 / Real.sqrt (2 * Real.pi * v)))
  have heq :
      (fun y => a * (1 / Real.sqrt (2 * Real.pi * v)) *
          (Real.exp ∘ fun y => -(y - μ) ^ 2 / (2 * v)) y)
        = (fun y => a * ((1 / Real.sqrt (2 * Real.pi * v)) *
            Real.exp (-(y - μ) ^ 2 / (2 * v)))) := by
    funext y; simp only [Function.comp_apply]; ring
  rw [heq] at hfull
  show HasDerivAt _ (termDeriv S c x i) x
  unfold termDeriv
  convert hfull using 1
  ring

/-- `fFam S c · ` has `x`-derivative `∑ i, termDeriv S c x i` at every `x`. -/
private theorem fFam_hasDerivAt (S : SignedGaussianCombination) (c x : ℝ) :
    HasDerivAt (fun y => fFam S c y)
      (∑ i : Fin S.components.length, termDeriv S c x i) x := by
  have hfun : (fun y => fFam S c y) = (fun y => ∑ i : Fin S.components.length,
      (S.components.get i).1 *
        ((1 / Real.sqrt (2 * Real.pi *
            (perturbVarSq (S.components.get i).2.varSq c i.val S.components.length)))
          * Real.exp (-(y - (S.components.get i).2.mean) ^ 2 /
              (2 * (perturbVarSq (S.components.get i).2.varSq c i.val S.components.length))))) := by
    funext y; rfl
  rw [hfun]
  have hsum := HasDerivAt.sum (u := Finset.univ) (A := fun i (y : ℝ) =>
      (S.components.get i).1 *
        ((1 / Real.sqrt (2 * Real.pi *
            (perturbVarSq (S.components.get i).2.varSq c i.val S.components.length)))
          * Real.exp (-(y - (S.components.get i).2.mean) ^ 2 /
              (2 * (perturbVarSq (S.components.get i).2.varSq c i.val S.components.length)))))
      (A' := fun i => termDeriv S c x i)
      (fun i _ => term_hasDerivAt S c x i)
  rw [Finset.sum_fn] at hsum
  exact hsum

/-- The `x`-derivative of `fFam S c` equals the explicit `∑ termDeriv` formula. -/
private theorem fFam_deriv_eq_sum (S : SignedGaussianCombination) (c x : ℝ) :
    deriv (fun y => fFam S c y) x = ∑ i : Fin S.components.length, termDeriv S c x i :=
  (fFam_hasDerivAt S c x).deriv

/-- Joint continuity of the `i`-th derivative term on `goodSet S × ℝ` (the
denominators `√(2π v_i)` and `2 v_i` are nonzero where `v_i > 0`). -/
private theorem termDeriv_contOn (S : SignedGaussianCombination) (i : Fin S.components.length) :
    ContinuousOn (fun p : ℝ × ℝ => termDeriv S p.1 p.2 i)
      (goodSet S ×ˢ (Set.univ : Set ℝ)) := by
  unfold termDeriv
  simp only [perturbVarSq]
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.mul
  · apply ContinuousOn.div continuousOn_const
    · apply Continuous.continuousOn; fun_prop
    · intro p hp
      have hv : 0 < perturbVarSq (S.components.get i).2.varSq p.1 i.val S.components.length :=
        hp.1 i
      rw [perturbVarSq] at hv
      have : 0 < Real.sqrt (2 * Real.pi *
          ((S.components.get i).2.varSq + p.1 * (↑↑i + 1) / ↑S.components.length)) := by
        apply Real.sqrt_pos.mpr; have := Real.pi_pos; positivity
      exact ne_of_gt this
  · apply ContinuousOn.mul
    · apply ContinuousOn.rexp
      apply ContinuousOn.div
      · apply Continuous.continuousOn; fun_prop
      · apply Continuous.continuousOn; fun_prop
      · intro p hp
        have hv : 0 < perturbVarSq (S.components.get i).2.varSq p.1 i.val S.components.length :=
          hp.1 i
        rw [perturbVarSq] at hv; positivity
    · apply ContinuousOn.div
      · apply Continuous.continuousOn; fun_prop
      · apply Continuous.continuousOn; fun_prop
      · intro p hp
        have hv : 0 < perturbVarSq (S.components.get i).2.varSq p.1 i.val S.components.length :=
          hp.1 i
        rw [perturbVarSq] at hv; positivity

/-- The family value `(c, x) ↦ fFam S c x` is jointly continuous on `goodSet S × ℝ`. -/
private theorem fFam_value_contOn (S : SignedGaussianCombination) :
    ContinuousOn (fun p : ℝ × ℝ => fFam S p.1 p.2) (goodSet S ×ˢ (Set.univ : Set ℝ)) := by
  have heq : (fun p : ℝ × ℝ => fFam S p.1 p.2) =
      (fun p : ℝ × ℝ => ∑ i : Fin S.components.length,
        (S.components.get i).1 *
          ((1 / Real.sqrt (2 * Real.pi *
              (perturbVarSq (S.components.get i).2.varSq p.1 i.val S.components.length)))
            * Real.exp (-(p.2 - (S.components.get i).2.mean) ^ 2 /
                (2 * (perturbVarSq (S.components.get i).2.varSq p.1 i.val S.components.length))))) := by
    funext p; rfl
  rw [heq]
  apply continuousOn_finset_sum
  intro i _
  simp only [perturbVarSq]
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.mul
  · apply ContinuousOn.div continuousOn_const
    · apply Continuous.continuousOn; fun_prop
    · intro p hp
      have hv : 0 < perturbVarSq (S.components.get i).2.varSq p.1 i.val S.components.length :=
        hp.1 i
      rw [perturbVarSq] at hv
      have : 0 < Real.sqrt (2 * Real.pi *
          ((S.components.get i).2.varSq + p.1 * (↑↑i + 1) / ↑S.components.length)) := by
        apply Real.sqrt_pos.mpr; have := Real.pi_pos; positivity
      exact ne_of_gt this
  · apply ContinuousOn.rexp
    apply ContinuousOn.div
    · apply Continuous.continuousOn; fun_prop
    · apply Continuous.continuousOn; fun_prop
    · intro p hp
      have hv : 0 < perturbVarSq (S.components.get i).2.varSq p.1 i.val S.components.length :=
        hp.1 i
      rw [perturbVarSq] at hv; positivity

/-- The family `x`-derivative `(c, x) ↦ deriv (fFam S c) x` is jointly continuous on
`goodSet S × ℝ` (rewrite `deriv` as `∑ termDeriv` then use `termDeriv_contOn`). -/
private theorem fFam_deriv_contOn (S : SignedGaussianCombination) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => fFam S p.1 y) p.2)
      (goodSet S ×ˢ (Set.univ : Set ℝ)) := by
  have heq : Set.EqOn (fun p : ℝ × ℝ => deriv (fun y => fFam S p.1 y) p.2)
      (fun p : ℝ × ℝ => ∑ i : Fin S.components.length, termDeriv S p.1 p.2 i)
      (goodSet S ×ˢ (Set.univ : Set ℝ)) := fun p _ => fFam_deriv_eq_sum S p.1 p.2
  apply ContinuousOn.congr _ heq
  apply continuousOn_finset_sum
  intro i _
  exact termDeriv_contOn S i

/-! ## Clamp-globalization: a globally-continuous representative -/

/-- A continuous clamp of `c` into `[-r, r]`: equals `c` when `|c| ≤ r`, and
always lands in `[-r, r]`. Used to build a globally continuous representative of
`fFam` whose local behaviour at `c = 0` is unchanged. -/
noncomputable def clampR (r : ℝ) : ℝ → ℝ := fun c => max (-r) (min r c)

private theorem clampR_continuous (r : ℝ) : Continuous (clampR r) := by
  unfold clampR; fun_prop

private theorem clampR_eq_self {r c : ℝ} (h : |c| ≤ r) : clampR r c = c := by
  unfold clampR; rw [abs_le] at h; rw [min_eq_right h.2, max_eq_right h.1]

private theorem clampR_mem_Icc {r c : ℝ} (hr : 0 ≤ r) : clampR r c ∈ Set.Icc (-r) r := by
  unfold clampR
  refine ⟨le_max_left _ _, ?_⟩
  rw [max_le_iff]; exact ⟨by linarith, min_le_left _ _⟩

/-- **Per-zero analytic IFT branch via clamp-globalization.** From a simple zero
`x₀` of `fFam S 0`, produce a continuous branch `φ` of zeros of `fFam S c` for
`|c| < δ`, with `φ 0 = x₀`, simple-zero preservation, and local uniqueness.

The IFT axiom requires GLOBAL joint continuity of the family and its derivative,
but `fFam S` is only continuous on `goodSet S × ℝ`. We pick `r > 0` with
`Icc (-r) r ⊆ goodSet S` (possible since `goodSet S` is open and contains `0`),
clamp the parameter via `clampR r`, and apply the IFT to the globally-continuous
clamped family `(c, x) ↦ fFam S (clampR r c) x`. The branch is then restricted to
`|c| < min δ r`, where `clampR r c = c`, recovering the genuine `fFam`-branch. -/
private theorem ift_branch
    (S : SignedGaussianCombination)
    (x₀ : ℝ) (hzero : fFam S 0 x₀ = 0)
    (hsimple : deriv (fun y => fFam S 0 y) x₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δ) δ) ∧ φ 0 = x₀ ∧
      (∀ c : ℝ, |c| < δ → fFam S c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δ → deriv (fun y => fFam S c y) (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δ → ∀ y : ℝ,
        fFam S c y = 0 → |y - x₀| < ε → y = φ c) := by
  -- Closed ball `Icc (-r) r ⊆ goodSet S`.
  obtain ⟨r, hr_pos, hr_sub⟩ : ∃ r : ℝ, 0 < r ∧ Set.Icc (-r) r ⊆ goodSet S := by
    have hopen := goodSet_isOpen S
    rw [Metric.isOpen_iff] at hopen
    obtain ⟨ρ, hρ_pos, hρ_ball⟩ := hopen 0 (goodSet_zero_mem S)
    refine ⟨ρ / 2, by linarith, ?_⟩
    intro y hy; apply hρ_ball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    rcases hy with ⟨hy1, hy2⟩; rw [abs_lt]; constructor <;> linarith
  -- The clamp `ρf := clampR r`: globally continuous, lands in `goodSet`, fixes `0`.
  set ρf : ℝ → ℝ := clampR r with hρf_def
  have hρf_cont : Continuous ρf := clampR_continuous r
  have hρf_mem : ∀ c : ℝ, ρf c ∈ goodSet S := fun c => hr_sub (clampR_mem_Icc hr_pos.le)
  have hρf0 : ρf 0 = 0 := clampR_eq_self (by simpa using hr_pos.le)
  -- The graph map `(c, x) ↦ (ρf c, x)` lands in `goodSet S × ℝ` and is continuous.
  have hmap : ∀ p : ℝ × ℝ, ((ρf p.1, p.2) : ℝ × ℝ) ∈ goodSet S ×ˢ (Set.univ : Set ℝ) :=
    fun p => ⟨hρf_mem p.1, Set.mem_univ _⟩
  have hmap_cont : Continuous (fun p : ℝ × ℝ => ((ρf p.1, p.2) : ℝ × ℝ)) :=
    (hρf_cont.comp continuous_fst).prodMk continuous_snd
  -- Global continuity of the clamped value and derivative families.
  have hgt_cont : Continuous (fun p : ℝ × ℝ => fFam S (ρf p.1) p.2) := by
    have := (fFam_value_contOn S).comp_continuous hmap_cont hmap; simpa using this
  have hDt_cont : Continuous (fun p : ℝ × ℝ => deriv (fun y => fFam S (ρf p.1) y) p.2) := by
    have := (fFam_deriv_contOn S).comp_continuous hmap_cont hmap; simpa using this
  -- Apply the real-analytic IFT axiom to the clamped family.
  obtain ⟨δ, hδ_pos, φ, hφ_cont, hφ0, hφ_zero, hφ_simple, hφ_uniq⟩ :=
    Workspace.PriorWork.AnalyticIFTSimpleZeroBranch
      (fun c y => fFam S (ρf c) y)
      (fun c y => deriv (fun y => fFam S (ρf c) y) y)
      hgt_cont hDt_cont (fun c y => rfl)
      x₀ (by simp only []; rw [hρf0]; exact hzero)
      (by simp only []; rw [hρf0]; exact hsimple)
  -- Restrict to `|c| < δ' = min δ r`, where `ρf c = c`.
  set δ' : ℝ := min δ r with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min hδ_pos hr_pos
  refine ⟨δ', hδ'_pos, φ, ?_, hφ0, ?_, ?_, ?_⟩
  · apply hφ_cont.mono; intro c hc; rcases hc with ⟨hc1, hc2⟩
    have : δ' ≤ δ := min_le_left δ r; exact ⟨by linarith, by linarith⟩
  · intro c hc
    have habs : |c| < δ := by
      rw [abs_lt]; have : δ' ≤ δ := min_le_left δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hρc : ρf c = c := by
      apply clampR_eq_self; rw [abs_le]
      have : δ' ≤ r := min_le_right δ r; rw [abs_lt] at hc; constructor <;> linarith
    have := hφ_zero c habs; rwa [hρc] at this
  · intro c hc
    have habs : |c| < δ := by
      rw [abs_lt]; have : δ' ≤ δ := min_le_left δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hρc : ρf c = c := by
      apply clampR_eq_self; rw [abs_le]
      have : δ' ≤ r := min_le_right δ r; rw [abs_lt] at hc; constructor <;> linarith
    have := hφ_simple c habs; rwa [hρc] at this
  · obtain ⟨ε, hε_pos, hε_uniq⟩ := hφ_uniq
    refine ⟨ε, hε_pos, ?_⟩
    intro c hc y hyzero hynear
    have habs : |c| < δ := by
      rw [abs_lt]; have : δ' ≤ δ := min_le_left δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hρc : ρf c = c := by
      apply clampR_eq_self; rw [abs_le]
      have : δ' ≤ r := min_le_right δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hgt : fFam S (ρf c) y = 0 := by rw [hρc]; exact hyzero
    exact hε_uniq c habs y hgt hynear

/-! ## Main lemma: persistence of simple zeros under variance perturbation -/

/--
**Sub-lemma E (Step 5).** Let `S` be a `SignedGaussianCombination` all of whose
real zeros are simple. For any finite family of distinct simple zeros
`x₁ < ⋯ < x_r` of `S.density`, there is a persistence radius `δ_pers > 0` such
that for every `δ ∈ (0, δ_pers)` the variance-perturbed density
`(variancePerturb S δ _).density` has at least `r` distinct real zeros — one in a
small pairwise-disjoint neighbourhood of each `x_j`. Faithfully: there is `ε > 0`
whose `ε`-neighbourhoods about the `x_j` are pairwise disjoint (`ε ≤ |xᵢ-xⱼ|/2`),
together with an injection `z : Fin r → ℝ` sending each `j` to a zero of the
perturbed density within `ε` of `x_j`.
-/
theorem SimpleZeroPersistsUnderVariancePerturbation
    (S : SignedGaussianCombination)
    (hsimple : ∀ x, S.density x = 0 → deriv S.density x ≠ 0)
    (r : ℕ) (x : Fin r → ℝ) (hx_mono : StrictMono x)
    (hx_zero : ∀ j, S.density (x j) = 0) :
    ∃ δ_pers, 0 < δ_pers ∧ ∀ δ, ∀ hδ : 0 < δ, δ < δ_pers →
      ∃ ε, 0 < ε ∧ (∀ i j, i ≠ j → ε ≤ |x i - x j| / 2) ∧
        ∃ z : Fin r → ℝ, Function.Injective z ∧
          (∀ j, (variancePerturb S δ (le_of_lt hδ)).density (z j) = 0) ∧
          (∀ j, |z j - x j| < ε) := by
  classical
  -- The family `f := fFam S` and its `x`-derivative `D`. (Global joint continuity
  -- of `f`/`D` is FALSE — variances can hit `0` — so we do NOT use it directly;
  -- the per-zero IFT branch is produced by `ift_branch` via clamp-globalization,
  -- which only needs joint continuity on the positive-variance region `goodSet`.)
  set f : ℝ → ℝ → ℝ := fun c y => fFam S c y with hf_def
  set D : ℝ → ℝ → ℝ := fun c y => deriv (fun y => fFam S c y) y with hD_def
  -- At `c = 0`, each `x j` is a simple zero of `f`.
  have hf0_zero : ∀ j : Fin r, fFam S 0 (x j) = 0 := by
    intro j; rw [fFam_zero]; exact hx_zero j
  have hD0_ne : ∀ j : Fin r, deriv (fun y => fFam S 0 y) (x j) ≠ 0 := by
    intro j
    rw [fFam_zero_fun]
    exact hsimple (x j) (hx_zero j)
  -- Per-zero analytic IFT branch (with local uniqueness), via clamp-globalization.
  have hIFT : ∀ j : Fin r, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δ) δ) ∧ φ 0 = x j ∧
      (∀ c : ℝ, |c| < δ → f c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δ → D c (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δ → ∀ y : ℝ,
        f c y = 0 → |y - x j| < ε → y = φ c) := by
    intro j
    simp only [hf_def, hD_def]
    exact ift_branch S (x j) (hf0_zero j) (hD0_ne j)
  choose δf hδf_pos φ hφ_contOn hφ_zero hφ_root _hφ_deriv _hφ_uniq using hIFT
  -- Pairwise separation radius from the strictly-monotone zeros.
  -- `gap j = |x j - x (j+1)|`-style minimal separation; we take half the minimum
  -- over all distinct pairs. Build a positive lower bound on all `|x i - x j|`.
  -- Define ε₀ as the (positive) minimal half-distance between distinct zeros.
  set pairs : Finset (Fin r × Fin r) :=
    (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 ≠ p.2) with hpairs_def
  -- The candidate separation value.
  set ε₀ : ℝ :=
    if hne : pairs.Nonempty then
      pairs.inf' hne (fun p => |x p.1 - x p.2| / 2)
    else 1 with hε₀_def
  have hε₀_pos : 0 < ε₀ := by
    rw [hε₀_def]
    split
    · rename_i hne
      rw [Finset.lt_inf'_iff]
      intro p hp
      rw [hpairs_def, Finset.mem_filter] at hp
      have hne_p : p.1 ≠ p.2 := hp.2
      have hxne : x p.1 ≠ x p.2 := fun h => hne_p (hx_mono.injective h)
      have hpos : 0 < |x p.1 - x p.2| := abs_pos.mpr (sub_ne_zero.mpr hxne)
      linarith
    · norm_num
  have hε₀_sep : ∀ i j : Fin r, i ≠ j → ε₀ ≤ |x i - x j| / 2 := by
    intro i j hij
    have hmem : (i, j) ∈ pairs := by
      rw [hpairs_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩
    have hne : pairs.Nonempty := ⟨(i, j), hmem⟩
    rw [hε₀_def]
    rw [dif_pos hne]
    exact Finset.inf'_le _ hmem
  -- For each `j`, continuity of `φ_j` at `0` (from the right) yields a radius
  -- `ρ_j ≤ δ_j` within which `|φ_j c - x_j| < ε₀`.
  have hclose : ∀ j : Fin r, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δf j ∧
      ∀ c : ℝ, 0 ≤ c → c < ρ → |φ j c - x j| < ε₀ := by
    intro j
    -- φ_j is continuous on Ioo (-δf j) (δf j) and φ_j 0 = x j.
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-(δf j)) (δf j) :=
      ⟨by linarith [hδf_pos j], hδf_pos j⟩
    have hcontAt : ContinuousWithinAt (φ j) (Set.Ioo (-(δf j)) (δf j)) 0 :=
      (hφ_contOn j) 0 h0mem
    -- Tendsto along nhdsWithin 0 of the Ioo to φ_j 0 = x j.
    have htend : Filter.Tendsto (φ j) (nhdsWithin 0 (Set.Ioo (-(δf j)) (δf j)))
        (nhds (x j)) := by
      have := hcontAt
      rw [ContinuousWithinAt, hφ_zero j] at this
      exact this
    -- The target neighbourhood {y | |y - x j| < ε₀}.
    have hball : {y : ℝ | |y - x j| < ε₀} ∈ nhds (x j) := by
      have : Metric.ball (x j) ε₀ ∈ nhds (x j) := Metric.ball_mem_nhds _ hε₀_pos
      apply Filter.mem_of_superset this
      intro y hy
      rw [Metric.mem_ball, Real.dist_eq] at hy
      exact hy
    have hpre := htend hball
    rw [Filter.mem_map, mem_nhdsWithin] at hpre
    obtain ⟨U, hU_open, hU_mem, hU_sub⟩ := hpre
    -- U is an open set containing 0; get a ball radius around 0 inside U ∩ Ioo.
    have hU_nhds : U ∈ nhds (0 : ℝ) := hU_open.mem_nhds hU_mem
    rw [Metric.mem_nhds_iff] at hU_nhds
    obtain ⟨t, ht_pos, ht_sub⟩ := hU_nhds
    refine ⟨min t (δf j), lt_min ht_pos (hδf_pos j), min_le_right _ _, ?_⟩
    intro c hc_nn hc_lt
    have hc_t : c < t := lt_of_lt_of_le hc_lt (min_le_left _ _)
    have hc_δ : c < δf j := lt_of_lt_of_le hc_lt (min_le_right _ _)
    have hc_mem_ball : c ∈ Metric.ball (0 : ℝ) t := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hc_nn]; exact hc_t
    have hc_U : c ∈ U := ht_sub hc_mem_ball
    have hc_Ioo : c ∈ Set.Ioo (-(δf j)) (δf j) :=
      ⟨by linarith [hδf_pos j], hc_δ⟩
    have : c ∈ U ∩ Set.Ioo (-(δf j)) (δf j) := ⟨hc_U, hc_Ioo⟩
    have := hU_sub this
    simpa using this
  choose ρ hρ_pos hρ_le hρ_close using hclose
  -- δ_pers : minimum over j of ρ_j (positive on Fin r; with r = 0 default 1).
  set δ_pers : ℝ :=
    if hne : (Finset.univ : Finset (Fin r)).Nonempty then
      (Finset.univ : Finset (Fin r)).inf' hne ρ
    else 1 with hδpers_def
  have hδpers_pos : 0 < δ_pers := by
    rw [hδpers_def]
    split
    · rename_i hne
      rw [Finset.lt_inf'_iff]
      intro j _; exact hρ_pos j
    · norm_num
  have hδpers_le : ∀ j : Fin r, δ_pers ≤ ρ j := by
    intro j
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j, Finset.mem_univ _⟩
    rw [hδpers_def, dif_pos hne]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  refine ⟨δ_pers, hδpers_pos, ?_⟩
  intro δ hδ hδ_lt
  refine ⟨ε₀, hε₀_pos, hε₀_sep, ?_⟩
  -- The injected zeros: z j = φ_j δ.
  refine ⟨fun j => φ j δ, ?_, ?_, ?_⟩
  · -- Injectivity from disjoint ε₀-neighbourhoods.
    intro i j hij
    by_contra hne
    -- closeness of both endpoints
    have hclose_i : |φ i δ - x i| < ε₀ :=
      hρ_close i δ (le_of_lt hδ) (lt_of_lt_of_le hδ_lt (hδpers_le i))
    have hclose_j : |φ j δ - x j| < ε₀ :=
      hρ_close j δ (le_of_lt hδ) (lt_of_lt_of_le hδ_lt (hδpers_le j))
    have hsep : ε₀ ≤ |x i - x j| / 2 := hε₀_sep i j hne
    -- φ i δ = φ j δ from hij
    have heq : φ i δ = φ j δ := hij
    have : |x i - x j| < 2 * ε₀ := by
      have h1 : |x i - x j| ≤ |x i - φ i δ| + |φ i δ - x j| := abs_sub_le _ _ _
      have h2 : |φ i δ - x j| ≤ |φ i δ - φ j δ| + |φ j δ - x j| := abs_sub_le _ _ _
      have h3 : |φ i δ - φ j δ| = 0 := by rw [heq]; simp
      have h4 : |x i - φ i δ| = |φ i δ - x i| := abs_sub_comm _ _
      rw [h4] at h1
      calc |x i - x j| ≤ |φ i δ - x i| + |φ i δ - x j| := h1
        _ ≤ |φ i δ - x i| + (|φ i δ - φ j δ| + |φ j δ - x j|) := by linarith [h2]
        _ = |φ i δ - x i| + |φ j δ - x j| := by rw [h3]; ring
        _ < ε₀ + ε₀ := by linarith [hclose_i, hclose_j]
        _ = 2 * ε₀ := by ring
    linarith [hsep, this]
  · -- Each z j is a zero of the perturbed density.
    intro j
    have hroot : f δ (φ j δ) = 0 := by
      apply hφ_root j
      rw [abs_of_nonneg (le_of_lt hδ)]
      exact lt_of_lt_of_le (lt_of_lt_of_le hδ_lt (hδpers_le j)) (hρ_le j)
    -- f δ y = fFam S δ y = (variancePerturb S δ _).density y for δ ≥ 0.
    have heq : fFam S δ (φ j δ) = (variancePerturb S δ (le_of_lt hδ)).density (φ j δ) :=
      fFam_eq_density S δ (le_of_lt hδ) (φ j δ)
    simp only [hf_def] at hroot
    rw [heq] at hroot
    exact hroot
  · -- Each z j is within ε₀ of x j.
    intro j
    exact hρ_close j δ (le_of_lt hδ) (lt_of_lt_of_le hδ_lt (hδpers_le j))

end Workspace.ProofLemmas
