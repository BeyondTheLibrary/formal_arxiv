import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.PriorWork.AnalyticIFTSimpleZeroBranch
import Workspace.ProofLemmas.SublemmaTailDomination
import Workspace.ProofLemmas.CompactPositiveLSCInfimum
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.Prop7AddGaussianAddsAtMostTwoZeros

/-!
# Uniform-variance-shift simple-zero persistence (Step 5b analytic core)

This is the uniform-shift analogue of
`Workspace.ProofLemmas.SimpleZeroPersistsUnderVariancePerturbation`.

A Gaussian convolution `conv(g, α)` of a signed Gaussian combination's density `g`
is, by `heatShift_density_eq_convolve`, exactly the density of the combination whose
EVERY component variance is shifted up by `α` (a *uniform* variance shift, the heat
flow). We track simple zeros through this uniform shift via the real-analytic IFT
(`AnalyticIFTSimpleZeroBranch`), exactly as the non-uniform variance-perturbation
lemma does, but with `perturbVarSq σᵢ² c i k = σᵢ² + c·(i+1)/k` replaced by the
uniform `σᵢ² + c`.

The one-parameter family is `fFamU S c x` = normalized Gaussian sum with each
variance `σᵢ² + c`. For `c ≥ 0` it equals `(heatShiftNonneg S c).density`, and for
`c > 0` it equals `conv(S.density, c)` (= `(heatShift S c).density`). On the open
set `goodSetU S = {c | ∀ i, σᵢ² + c > 0}` (which contains all `c ≥ 0`), the family
and its `x`-derivative are jointly continuous; the clamp-globalization trick then
feeds the IFT axiom to produce, for each simple zero `x₀` of `S.density`, a
continuous branch of zeros of `fFamU S c` with the simple-zero property preserved.

The final consumer lemma `convSmall_simpleZeros_of_base_simple` packages this into:
if `S` has simple zeros and a tail envelope etc., then for all small `α > 0`,
`conv(S.density, α)` has all-simple zeros.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.ZeroCount

set_option maxHeartbeats 4000000

/-! ## The uniform-shift one-parameter family -/

/-- The uniform-variance-shifted normalized Gaussian family as a function of `(c, x)`.
The variance of the `i`-th component is `σᵢ² + c`. This is a *total* function of `c`
(for `c ≤ -σᵢ²` the term degenerates via `Real.sqrt`-of-nonpositive `= 0`, but we
only use it on `goodSetU`). -/
noncomputable def fFamU (S : SignedGaussianCombination) : ℝ → ℝ → ℝ :=
  fun c x =>
    ((List.finRange S.components.length).map
      (fun i =>
        let p := S.components.get i
        p.1 *
          ((1 / Real.sqrt (2 * Real.pi * ((S.components.get i).2.varSq + c)))
            * Real.exp (-(x - p.2.mean) ^ 2 /
                (2 * ((S.components.get i).2.varSq + c)))))).sum

/-- The good parameter set where every uniformly-shifted variance stays
strictly positive. Contains all `c ≥ 0`, in particular `0`. -/
def goodSetU (S : SignedGaussianCombination) : Set ℝ :=
  {c : ℝ | ∀ i : Fin S.components.length, 0 < (S.components.get i).2.varSq + c}

theorem goodSetU_isOpen (S : SignedGaussianCombination) : IsOpen (goodSetU S) := by
  unfold goodSetU
  rw [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  have hcont : Continuous (fun c : ℝ => (S.components.get i).2.varSq + c) := by fun_prop
  simpa using (isOpen_lt continuous_const hcont)

theorem goodSetU_of_nonneg (S : SignedGaussianCombination) {c : ℝ} (hc : 0 ≤ c) :
    c ∈ goodSetU S := by
  intro i
  have := (S.components.get i).2.varSq_pos
  linarith

theorem goodSetU_zero_mem (S : SignedGaussianCombination) : (0 : ℝ) ∈ goodSetU S :=
  goodSetU_of_nonneg S le_rfl

/-! ## Value of the family at `c = 0` and at positive shifts -/

/-- At parameter `c = 0` the family reduces to the unperturbed density. -/
theorem fFamU_zero (S : SignedGaussianCombination) (x : ℝ) :
    fFamU S 0 x = S.density x := by
  rw [SignedGaussianCombination.density_eq]
  conv_rhs => rw [← List.map_get_finRange S.components, List.map_map]
  unfold fFamU
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, GaussianPDF.density_eq]
  norm_num

theorem fFamU_zero_fun (S : SignedGaussianCombination) :
    (fun y => fFamU S 0 y) = S.density := by
  funext y; exact fFamU_zero S y

/-- For `c > 0`, the family value equals the heat-shifted (convolved) density. -/
theorem fFamU_eq_heatShift (S : SignedGaussianCombination) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    fFamU S c x = (heatShift S c hc).density x := by
  rw [SignedGaussianCombination.density_eq]
  unfold fFamU heatShift shiftVarG
  simp only [List.map_map]
  conv_rhs => rw [← List.map_get_finRange S.components, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, GaussianPDF.density_eq]

/-- For `c > 0`, the family value equals the convolution `conv(S.density, c)`. -/
theorem fFamU_eq_convolve (S : SignedGaussianCombination) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    fFamU S c x = convolveWithGaussian S.density c hc x := by
  rw [fFamU_eq_heatShift S c hc x, heatShift_density_eq_convolve S c hc x]

/-! ## The `x`-derivative of the family -/

/-- The explicit `x`-derivative of the `i`-th Gaussian term of `fFamU S c · ` at `x`,
valid wherever `v_i = σᵢ² + c` is nonzero. -/
noncomputable def termDerivU
    (S : SignedGaussianCombination) (c x : ℝ) (i : Fin S.components.length) : ℝ :=
  let p := S.components.get i
  let v := (S.components.get i).2.varSq + c
  p.1 * ((1 / Real.sqrt (2 * Real.pi * v)) *
    (Real.exp (-(x - p.2.mean) ^ 2 / (2 * v)) * (-(2 * (x - p.2.mean)) / (2 * v))))

private theorem termU_hasDerivAt
    (S : SignedGaussianCombination) (c x : ℝ) (i : Fin S.components.length) :
    HasDerivAt (fun y =>
      (S.components.get i).1 *
        ((1 / Real.sqrt (2 * Real.pi * ((S.components.get i).2.varSq + c)))
          * Real.exp (-(y - (S.components.get i).2.mean) ^ 2 /
              (2 * ((S.components.get i).2.varSq + c)))))
      (termDerivU S c x i) x := by
  set μ := (S.components.get i).2.mean
  set v := (S.components.get i).2.varSq + c
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
  show HasDerivAt _ (termDerivU S c x i) x
  unfold termDerivU
  convert hfull using 1
  ring

private theorem fFamU_hasDerivAt (S : SignedGaussianCombination) (c x : ℝ) :
    HasDerivAt (fun y => fFamU S c y)
      (∑ i : Fin S.components.length, termDerivU S c x i) x := by
  have hfun : (fun y => fFamU S c y) = (fun y => ∑ i : Fin S.components.length,
      (S.components.get i).1 *
        ((1 / Real.sqrt (2 * Real.pi * ((S.components.get i).2.varSq + c)))
          * Real.exp (-(y - (S.components.get i).2.mean) ^ 2 /
              (2 * ((S.components.get i).2.varSq + c))))) := by
    funext y; rfl
  rw [hfun]
  have hsum := HasDerivAt.sum (u := Finset.univ) (A := fun i (y : ℝ) =>
      (S.components.get i).1 *
        ((1 / Real.sqrt (2 * Real.pi * ((S.components.get i).2.varSq + c)))
          * Real.exp (-(y - (S.components.get i).2.mean) ^ 2 /
              (2 * ((S.components.get i).2.varSq + c)))))
      (A' := fun i => termDerivU S c x i)
      (fun i _ => termU_hasDerivAt S c x i)
  rw [Finset.sum_fn] at hsum
  exact hsum

private theorem fFamU_deriv_eq_sum (S : SignedGaussianCombination) (c x : ℝ) :
    deriv (fun y => fFamU S c y) x = ∑ i : Fin S.components.length, termDerivU S c x i :=
  (fFamU_hasDerivAt S c x).deriv

/-! ## Joint continuity on `goodSetU` -/

private theorem termDerivU_contOn (S : SignedGaussianCombination) (i : Fin S.components.length) :
    ContinuousOn (fun p : ℝ × ℝ => termDerivU S p.1 p.2 i)
      (goodSetU S ×ˢ (Set.univ : Set ℝ)) := by
  unfold termDerivU
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.mul
  · apply ContinuousOn.div continuousOn_const
    · apply Continuous.continuousOn; fun_prop
    · intro p hp
      have hv : 0 < (S.components.get i).2.varSq + p.1 := hp.1 i
      have : 0 < Real.sqrt (2 * Real.pi * ((S.components.get i).2.varSq + p.1)) := by
        apply Real.sqrt_pos.mpr; have := Real.pi_pos; positivity
      exact ne_of_gt this
  · apply ContinuousOn.mul
    · apply ContinuousOn.rexp
      apply ContinuousOn.div
      · apply Continuous.continuousOn; fun_prop
      · apply Continuous.continuousOn; fun_prop
      · intro p hp
        have hv : 0 < (S.components.get i).2.varSq + p.1 := hp.1 i
        positivity
    · apply ContinuousOn.div
      · apply Continuous.continuousOn; fun_prop
      · apply Continuous.continuousOn; fun_prop
      · intro p hp
        have hv : 0 < (S.components.get i).2.varSq + p.1 := hp.1 i
        positivity

private theorem fFamU_value_contOn (S : SignedGaussianCombination) :
    ContinuousOn (fun p : ℝ × ℝ => fFamU S p.1 p.2) (goodSetU S ×ˢ (Set.univ : Set ℝ)) := by
  have heq : (fun p : ℝ × ℝ => fFamU S p.1 p.2) =
      (fun p : ℝ × ℝ => ∑ i : Fin S.components.length,
        (S.components.get i).1 *
          ((1 / Real.sqrt (2 * Real.pi * ((S.components.get i).2.varSq + p.1)))
            * Real.exp (-(p.2 - (S.components.get i).2.mean) ^ 2 /
                (2 * ((S.components.get i).2.varSq + p.1))))) := by
    funext p; rfl
  rw [heq]
  apply continuousOn_finset_sum
  intro i _
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.mul
  · apply ContinuousOn.div continuousOn_const
    · apply Continuous.continuousOn; fun_prop
    · intro p hp
      have hv : 0 < (S.components.get i).2.varSq + p.1 := hp.1 i
      have : 0 < Real.sqrt (2 * Real.pi * ((S.components.get i).2.varSq + p.1)) := by
        apply Real.sqrt_pos.mpr; have := Real.pi_pos; positivity
      exact ne_of_gt this
  · apply ContinuousOn.rexp
    apply ContinuousOn.div
    · apply Continuous.continuousOn; fun_prop
    · apply Continuous.continuousOn; fun_prop
    · intro p hp
      have hv : 0 < (S.components.get i).2.varSq + p.1 := hp.1 i
      positivity

private theorem fFamU_deriv_contOn (S : SignedGaussianCombination) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => fFamU S p.1 y) p.2)
      (goodSetU S ×ˢ (Set.univ : Set ℝ)) := by
  have heq : Set.EqOn (fun p : ℝ × ℝ => deriv (fun y => fFamU S p.1 y) p.2)
      (fun p : ℝ × ℝ => ∑ i : Fin S.components.length, termDerivU S p.1 p.2 i)
      (goodSetU S ×ˢ (Set.univ : Set ℝ)) := fun p _ => fFamU_deriv_eq_sum S p.1 p.2
  apply ContinuousOn.congr _ heq
  apply continuousOn_finset_sum
  intro i _
  exact termDerivU_contOn S i

/-! ## Clamp-globalization (verbatim mirror of the proven lemma) -/

noncomputable def clampRU (r : ℝ) : ℝ → ℝ := fun c => max (-r) (min r c)

private theorem clampRU_continuous (r : ℝ) : Continuous (clampRU r) := by
  unfold clampRU; fun_prop

private theorem clampRU_eq_self {r c : ℝ} (h : |c| ≤ r) : clampRU r c = c := by
  unfold clampRU; rw [abs_le] at h; rw [min_eq_right h.2, max_eq_right h.1]

private theorem clampRU_mem_Icc {r c : ℝ} (hr : 0 ≤ r) : clampRU r c ∈ Set.Icc (-r) r := by
  unfold clampRU
  refine ⟨le_max_left _ _, ?_⟩
  rw [max_le_iff]; exact ⟨by linarith, min_le_left _ _⟩

/-- **Per-zero analytic IFT branch via clamp-globalization, uniform shift.** -/
private theorem ift_branchU
    (S : SignedGaussianCombination)
    (x₀ : ℝ) (hzero : fFamU S 0 x₀ = 0)
    (hsimple : deriv (fun y => fFamU S 0 y) x₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δ) δ) ∧ φ 0 = x₀ ∧
      (∀ c : ℝ, |c| < δ → fFamU S c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δ → deriv (fun y => fFamU S c y) (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δ → ∀ y : ℝ,
        fFamU S c y = 0 → |y - x₀| < ε → y = φ c) := by
  obtain ⟨r, hr_pos, hr_sub⟩ : ∃ r : ℝ, 0 < r ∧ Set.Icc (-r) r ⊆ goodSetU S := by
    have hopen := goodSetU_isOpen S
    rw [Metric.isOpen_iff] at hopen
    obtain ⟨ρ, hρ_pos, hρ_ball⟩ := hopen 0 (goodSetU_zero_mem S)
    refine ⟨ρ / 2, by linarith, ?_⟩
    intro y hy; apply hρ_ball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    rcases hy with ⟨hy1, hy2⟩; rw [abs_lt]; constructor <;> linarith
  set ρf : ℝ → ℝ := clampRU r with hρf_def
  have hρf_cont : Continuous ρf := clampRU_continuous r
  have hρf_mem : ∀ c : ℝ, ρf c ∈ goodSetU S := fun c => hr_sub (clampRU_mem_Icc hr_pos.le)
  have hρf0 : ρf 0 = 0 := clampRU_eq_self (by simpa using hr_pos.le)
  have hmap : ∀ p : ℝ × ℝ, ((ρf p.1, p.2) : ℝ × ℝ) ∈ goodSetU S ×ˢ (Set.univ : Set ℝ) :=
    fun p => ⟨hρf_mem p.1, Set.mem_univ _⟩
  have hmap_cont : Continuous (fun p : ℝ × ℝ => ((ρf p.1, p.2) : ℝ × ℝ)) :=
    (hρf_cont.comp continuous_fst).prodMk continuous_snd
  have hgt_cont : Continuous (fun p : ℝ × ℝ => fFamU S (ρf p.1) p.2) := by
    have := (fFamU_value_contOn S).comp_continuous hmap_cont hmap; simpa using this
  have hDt_cont : Continuous (fun p : ℝ × ℝ => deriv (fun y => fFamU S (ρf p.1) y) p.2) := by
    have := (fFamU_deriv_contOn S).comp_continuous hmap_cont hmap; simpa using this
  obtain ⟨δ, hδ_pos, φ, hφ_cont, hφ0, hφ_zero, hφ_simple, hφ_uniq⟩ :=
    Workspace.PriorWork.AnalyticIFTSimpleZeroBranch
      (fun c y => fFamU S (ρf c) y)
      (fun c y => deriv (fun y => fFamU S (ρf c) y) y)
      hgt_cont hDt_cont (fun c y => rfl)
      x₀ (by simp only []; rw [hρf0]; exact hzero)
      (by simp only []; rw [hρf0]; exact hsimple)
  set δ' : ℝ := min δ r with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min hδ_pos hr_pos
  refine ⟨δ', hδ'_pos, φ, ?_, hφ0, ?_, ?_, ?_⟩
  · apply hφ_cont.mono; intro c hc; rcases hc with ⟨hc1, hc2⟩
    have : δ' ≤ δ := min_le_left δ r; exact ⟨by linarith, by linarith⟩
  · intro c hc
    have habs : |c| < δ := by
      rw [abs_lt]; have : δ' ≤ δ := min_le_left δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hρc : ρf c = c := by
      apply clampRU_eq_self; rw [abs_le]
      have : δ' ≤ r := min_le_right δ r; rw [abs_lt] at hc; constructor <;> linarith
    have := hφ_zero c habs; rwa [hρc] at this
  · intro c hc
    have habs : |c| < δ := by
      rw [abs_lt]; have : δ' ≤ δ := min_le_left δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hρc : ρf c = c := by
      apply clampRU_eq_self; rw [abs_le]
      have : δ' ≤ r := min_le_right δ r; rw [abs_lt] at hc; constructor <;> linarith
    have := hφ_simple c habs; rwa [hρc] at this
  · obtain ⟨ε, hε_pos, hε_uniq⟩ := hφ_uniq
    refine ⟨ε, hε_pos, ?_⟩
    intro c hc y hyzero hynear
    have habs : |c| < δ := by
      rw [abs_lt]; have : δ' ≤ δ := min_le_left δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hρc : ρf c = c := by
      apply clampRU_eq_self; rw [abs_le]
      have : δ' ≤ r := min_le_right δ r; rw [abs_lt] at hc; constructor <;> linarith
    have hgt : fFamU S (ρf c) y = 0 := by rw [hρc]; exact hyzero
    exact hε_uniq c habs y hgt hynear

/-! ## Uniform lower bound on the branch derivative (banked partial uniform bound)

The IFT branch `φ` of `ift_branchU` carries the *qualitative* simple-zero clause
`deriv (fFamU S c) (φ c) ≠ 0` for every small `c`. For the uniform-threshold
program (region (b) of the §6.1 add-Gaussian step, whose perturbation threshold
`v_th1` is an explicit increasing function of `ε₁ = min_j |deriv g (x_j)|`) we need
the *quantitative* fact that this derivative is bounded AWAY from `0` *uniformly* in
`c` as `c → 0⁺`.

This is provable from the joint continuity already established
(`fFamU_deriv_contOn`) together with the branch continuity `φ c → x₀`: the scalar
map `c ↦ deriv (fFamU S c) (φ c)` is continuous at `0` (composition of `c ↦ (c,φ c)`
— continuous into `goodSetU S ×ˢ univ` for `c ≥ 0` — with the jointly continuous
`x`-derivative), hence tends to `deriv (fFamU S 0) x₀ = deriv S.density x₀ ≠ 0`, so
its absolute value eventually exceeds half that nonzero limit.

The result is stated *per base zero*; a finite `min` over the `r` base zeros then
gives the uniform `ε₁`-lower-bound for the whole convolution family. It is
axiom-clean modulo the pre-existing `AnalyticIFTSimpleZeroBranch` (inherited via
`ift_branchU`). -/
theorem branchDeriv_uniform_lower_bound
    (S : SignedGaussianCombination)
    (x₀ : ℝ) (hzero : fFamU S 0 x₀ = 0)
    (hsimple : deriv (fun y => fFamU S 0 y) x₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δ) δ) ∧ φ 0 = x₀ ∧
      (∀ c : ℝ, |c| < δ → fFamU S c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δ → deriv (fun y => fFamU S c y) (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δ → ∀ y : ℝ,
        fFamU S c y = 0 → |y - x₀| < ε → y = φ c) ∧
      -- the BANKED quantitative addition: a uniform derivative lower bound for `c ≥ 0`
      (∃ αd : ℝ, 0 < αd ∧ αd ≤ δ ∧
        ∀ c : ℝ, 0 ≤ c → c < αd →
          |deriv (fun y => fFamU S 0 y) x₀| / 2
            ≤ |deriv (fun y => fFamU S c y) (φ c)|) := by
  obtain ⟨δ, hδ_pos, φ, hφ_contOn, hφ0, hφ_zero, hφ_deriv, hφ_uniq⟩ :=
    ift_branchU S x₀ hzero hsimple
  refine ⟨δ, hδ_pos, φ, hφ_contOn, hφ0, hφ_zero, hφ_deriv, hφ_uniq, ?_⟩
  -- Abbreviations.
  set L : ℝ := deriv (fun y => fFamU S 0 y) x₀ with hL_def
  have hL_pos : 0 < |L| := abs_pos.mpr hsimple
  -- The scalar branch-derivative map.
  set g : ℝ → ℝ := fun c => deriv (fun y => fFamU S c y) (φ c) with hg_def
  -- `g 0 = L`.
  have hg0 : g 0 = L := by simp only [hg_def, hφ0, hL_def]
  -- `c ↦ (c, φ c)` is continuous within `Ioo (-δ) δ` at `0`, landing in `goodSetU ×ˢ univ`
  -- for `c ≥ 0`.  We work within the set `S₀ := Set.Ico 0 δ` (so `c ≥ 0` ⊆ goodSet).
  set S₀ : Set ℝ := Set.Ico 0 δ with hS₀_def
  have hS₀_sub_Ioo : S₀ ⊆ Set.Ioo (-δ) δ := by
    intro c hc; exact ⟨by linarith [hc.1, hδ_pos], hc.2⟩
  -- `φ` continuous within `S₀` (restriction of its continuity on `Ioo`).
  have hφ_contS₀ : ContinuousOn φ S₀ := hφ_contOn.mono hS₀_sub_Ioo
  -- The pairing map `c ↦ (c, φ c)`, continuous within `S₀`.
  have hpair_contS₀ : ContinuousOn (fun c : ℝ => ((c, φ c) : ℝ × ℝ)) S₀ :=
    (continuousOn_id (s := S₀)).prodMk hφ_contS₀
  -- For `c ∈ S₀`, `(c, φ c) ∈ goodSetU S ×ˢ univ`.
  have hpair_mem : ∀ c ∈ S₀, ((c, φ c) : ℝ × ℝ) ∈ goodSetU S ×ˢ (Set.univ : Set ℝ) :=
    fun c hc => ⟨goodSetU_of_nonneg S hc.1, Set.mem_univ _⟩
  -- Compose with the jointly continuous `x`-derivative.
  have hg_contS₀ : ContinuousOn g S₀ := by
    have hcomp :
        ContinuousOn ((fun p : ℝ × ℝ => deriv (fun y => fFamU S p.1 y) p.2)
            ∘ (fun c : ℝ => ((c, φ c) : ℝ × ℝ))) S₀ :=
      (fFamU_deriv_contOn S).comp hpair_contS₀ hpair_mem
    -- the composite is `g` definitionally.
    exact hcomp
  -- `0 ∈ S₀`.
  have h0_memS₀ : (0 : ℝ) ∈ S₀ := ⟨le_refl _, hδ_pos⟩
  -- `g` is continuous within `S₀` at `0`, value `g 0 = L`.
  have hg_contAt : ContinuousWithinAt g S₀ 0 := hg_contS₀ 0 h0_memS₀
  -- `|g ·|` is continuous within `S₀` at `0` with value `|L|`.
  have habs_contAt : ContinuousWithinAt (fun c => |g c|) S₀ 0 :=
    hg_contAt.abs
  -- eventually within `S₀` near `0`, `|L|/2 ≤ |g c|`.
  have htend : Filter.Tendsto (fun c => |g c|) (nhdsWithin 0 S₀) (nhds |L|) := by
    have := habs_contAt
    rw [ContinuousWithinAt] at this
    -- value at 0 is |g 0| = |L|
    rw [show |g 0| = |L| by rw [hg0]] at this
    exact this
  -- the open half-line `{t | |L|/2 < t}` is a neighbourhood of `|L|`.
  have hnhds : {t : ℝ | |L| / 2 < t} ∈ nhds |L| := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_id)
    show |L| / 2 < |L|
    linarith [hL_pos]
  have hpre : (fun c => |g c|) ⁻¹' {t : ℝ | |L| / 2 < t} ∈ nhdsWithin 0 S₀ :=
    htend hnhds
  -- unpack the within-nhds into a radius.
  rw [mem_nhdsWithin] at hpre
  obtain ⟨U, hU_open, hU0, hU_sub⟩ := hpre
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨t, ht_pos, ht_ball⟩ := hU_open 0 hU0
  refine ⟨min t δ, lt_min ht_pos hδ_pos, min_le_right _ _, ?_⟩
  intro c hc_nn hc_lt
  have hc_t : c < t := lt_of_lt_of_le hc_lt (min_le_left _ _)
  have hc_δ : c < δ := lt_of_lt_of_le hc_lt (min_le_right _ _)
  have hc_S₀ : c ∈ S₀ := ⟨hc_nn, hc_δ⟩
  have hc_ball : c ∈ Metric.ball (0 : ℝ) t := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hc_nn]; exact hc_t
  have hc_U : c ∈ U := ht_ball hc_ball
  have hc_in : c ∈ U ∩ S₀ := ⟨hc_U, hc_S₀⟩
  have hmem := hU_sub hc_in
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hmem
  -- `hmem : |L| / 2 < |g c|`; goal: `|deriv (fun y => fFamU S 0 y) x₀| / 2 ≤ |g c|`.
  have hmem' : |L| / 2 < |g c| := hmem
  show |deriv (fun y => fFamU S 0 y) x₀| / 2 ≤ |deriv (fun y => fFamU S c y) (φ c)|
  have hgc : |g c| = |deriv (fun y => fFamU S c y) (φ c)| := by simp only [hg_def]
  rw [← hL_def, ← hgc]
  exact le_of_lt hmem'

/-! ## Forward persistence: simple zeros of the base continue under the uniform shift

This is the fully-provable forward half (mirroring
`SimpleZeroPersistsUnderVariancePerturbation`): from a finite family of distinct
simple zeros of `S.density`, for all small `α > 0` the convolved density
`conv(S.density, α)` retains at least that many distinct zeros, one near each. -/

/-- **Forward simple-zero persistence under the uniform variance shift / convolution.**
If `S.density` has all simple zeros and `x₁ < ⋯ < x_r` are distinct (simple) zeros,
then there is a persistence radius `α_pers > 0` such that for every `α ∈ (0, α_pers)`
the convolution `conv(S.density, α)` has `≥ r` distinct real zeros — one within `ε`
of each `x_j`, the `ε`-neighbourhoods being pairwise disjoint. -/
theorem convSmall_simpleZeros_persist
    (S : SignedGaussianCombination)
    (hsimple : ∀ x, S.density x = 0 → deriv S.density x ≠ 0)
    (r : ℕ) (x : Fin r → ℝ) (hx_mono : StrictMono x)
    (hx_zero : ∀ j, S.density (x j) = 0) :
    ∃ α_pers, 0 < α_pers ∧ ∀ α, ∀ hα : 0 < α, α < α_pers →
      ∃ ε, 0 < ε ∧ (∀ i j, i ≠ j → ε ≤ |x i - x j| / 2) ∧
        ∃ z : Fin r → ℝ, Function.Injective z ∧
          (∀ j, convolveWithGaussian S.density α hα (z j) = 0) ∧
          (∀ j, |z j - x j| < ε) := by
  classical
  set f : ℝ → ℝ → ℝ := fun c y => fFamU S c y with hf_def
  set D : ℝ → ℝ → ℝ := fun c y => deriv (fun y => fFamU S c y) y with hD_def
  have hf0_zero : ∀ j : Fin r, fFamU S 0 (x j) = 0 := by
    intro j; rw [fFamU_zero]; exact hx_zero j
  have hD0_ne : ∀ j : Fin r, deriv (fun y => fFamU S 0 y) (x j) ≠ 0 := by
    intro j; rw [fFamU_zero_fun]; exact hsimple (x j) (hx_zero j)
  have hIFT : ∀ j : Fin r, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δ) δ) ∧ φ 0 = x j ∧
      (∀ c : ℝ, |c| < δ → f c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δ → D c (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δ → ∀ y : ℝ,
        f c y = 0 → |y - x j| < ε → y = φ c) := by
    intro j; simp only [hf_def, hD_def]; exact ift_branchU S (x j) (hf0_zero j) (hD0_ne j)
  choose δf hδf_pos φ hφ_contOn hφ_zero hφ_root _hφ_deriv _hφ_uniq using hIFT
  set pairs : Finset (Fin r × Fin r) :=
    (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 ≠ p.2) with hpairs_def
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
    rw [hε₀_def, dif_pos hne]; exact Finset.inf'_le _ hmem
  have hclose : ∀ j : Fin r, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δf j ∧
      ∀ c : ℝ, 0 ≤ c → c < ρ → |φ j c - x j| < ε₀ := by
    intro j
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-(δf j)) (δf j) := ⟨by linarith [hδf_pos j], hδf_pos j⟩
    have hcontAt : ContinuousWithinAt (φ j) (Set.Ioo (-(δf j)) (δf j)) 0 := (hφ_contOn j) 0 h0mem
    have htend : Filter.Tendsto (φ j) (nhdsWithin 0 (Set.Ioo (-(δf j)) (δf j))) (nhds (x j)) := by
      have := hcontAt; rw [ContinuousWithinAt, hφ_zero j] at this; exact this
    have hball : {y : ℝ | |y - x j| < ε₀} ∈ nhds (x j) := by
      have : Metric.ball (x j) ε₀ ∈ nhds (x j) := Metric.ball_mem_nhds _ hε₀_pos
      apply Filter.mem_of_superset this
      intro y hy; rw [Metric.mem_ball, Real.dist_eq] at hy; exact hy
    have hpre := htend hball
    rw [Filter.mem_map, mem_nhdsWithin] at hpre
    obtain ⟨U, hU_open, hU_mem, hU_sub⟩ := hpre
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
    have hc_Ioo : c ∈ Set.Ioo (-(δf j)) (δf j) := ⟨by linarith [hδf_pos j], hc_δ⟩
    have : c ∈ U ∩ Set.Ioo (-(δf j)) (δf j) := ⟨hc_U, hc_Ioo⟩
    have := hU_sub this; simpa using this
  choose ρ hρ_pos hρ_le hρ_close using hclose
  set α_pers : ℝ :=
    if hne : (Finset.univ : Finset (Fin r)).Nonempty then
      (Finset.univ : Finset (Fin r)).inf' hne ρ
    else 1 with hαpers_def
  have hαpers_pos : 0 < α_pers := by
    rw [hαpers_def]
    split
    · rename_i hne; rw [Finset.lt_inf'_iff]; intro j _; exact hρ_pos j
    · norm_num
  have hαpers_le : ∀ j : Fin r, α_pers ≤ ρ j := by
    intro j
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j, Finset.mem_univ _⟩
    rw [hαpers_def, dif_pos hne]; exact Finset.inf'_le _ (Finset.mem_univ j)
  refine ⟨α_pers, hαpers_pos, ?_⟩
  intro α hα hα_lt
  refine ⟨ε₀, hε₀_pos, hε₀_sep, ?_⟩
  refine ⟨fun j => φ j α, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hclose_i : |φ i α - x i| < ε₀ :=
      hρ_close i α (le_of_lt hα) (lt_of_lt_of_le hα_lt (hαpers_le i))
    have hclose_j : |φ j α - x j| < ε₀ :=
      hρ_close j α (le_of_lt hα) (lt_of_lt_of_le hα_lt (hαpers_le j))
    have hsep : ε₀ ≤ |x i - x j| / 2 := hε₀_sep i j hne
    have heq : φ i α = φ j α := hij
    have : |x i - x j| < 2 * ε₀ := by
      have h1 : |x i - x j| ≤ |x i - φ i α| + |φ i α - x j| := abs_sub_le _ _ _
      have h2 : |φ i α - x j| ≤ |φ i α - φ j α| + |φ j α - x j| := abs_sub_le _ _ _
      have h3 : |φ i α - φ j α| = 0 := by rw [heq]; simp
      have h4 : |x i - φ i α| = |φ i α - x i| := abs_sub_comm _ _
      rw [h4] at h1
      calc |x i - x j| ≤ |φ i α - x i| + |φ i α - x j| := h1
        _ ≤ |φ i α - x i| + (|φ i α - φ j α| + |φ j α - x j|) := by linarith [h2]
        _ = |φ i α - x i| + |φ j α - x j| := by rw [h3]; ring
        _ < ε₀ + ε₀ := by linarith [hclose_i, hclose_j]
        _ = 2 * ε₀ := by ring
    linarith [hsep, this]
  · intro j
    have hroot : f α (φ j α) = 0 := by
      apply hφ_root j
      rw [abs_of_nonneg (le_of_lt hα)]
      exact lt_of_lt_of_le (lt_of_lt_of_le hα_lt (hαpers_le j)) (hρ_le j)
    have heq : fFamU S α (φ j α) = convolveWithGaussian S.density α hα (φ j α) :=
      fFamU_eq_convolve S α hα (φ j α)
    simp only [hf_def] at hroot
    rw [heq] at hroot; exact hroot
  · intro j
    exact hρ_close j α (le_of_lt hα) (lt_of_lt_of_le hα_lt (hαpers_le j))

/-- For `α > 0`, the convolved density equals the family slice `fFamU S α` as a
function, hence their `x`-derivatives agree pointwise. -/
theorem convolve_eq_fFamU (S : SignedGaussianCombination) (α : ℝ) (hα : 0 < α) :
    convolveWithGaussian S.density α hα = (fun y => fFamU S α y) := by
  funext y; exact (fFamU_eq_convolve S α hα y).symm

theorem deriv_convolve_eq (S : SignedGaussianCombination) (α : ℝ) (hα : 0 < α) (y : ℝ) :
    deriv (convolveWithGaussian S.density α hα) y = deriv (fun y => fFamU S α y) y := by
  rw [convolve_eq_fFamU S α hα]

/-! ## All zeros of the small convolution are simple (count-pinch) -/

/-- **All zeros of the small convolution are simple.**

Let `S.density` have all-simple zeros, and let `x₁ < ⋯ < x_r` enumerate ALL of its
zeros (so `zeroCount S.density = r`). Then there is `α_pers > 0` such that for every
`α ∈ (0, α_pers)` with `zeroCount (conv(S.density, α)) ≤ r` (which holds by
Hummel–Gidas, supplied as a hypothesis here), EVERY zero of `conv(S.density, α)` is
simple, i.e. `∀ w, conv(S.density,α) w = 0 → deriv (conv(S.density,α)) w ≠ 0`.

Argument: the forward persistence lemma continues each `x_j` to a distinct simple
zero `z_j` of the convolution; the `r` values `z_j` are distinct (injectivity), so
`(range z).encard = r`. As `range z ⊆ zeroSet(conv)` and
`zeroCount(conv) ≤ r = (range z).encard`, the finite-set antisymmetry
`Finite.eq_of_subset_of_encard_le` forces `range z = zeroSet(conv)`. Hence every zero
of the convolution equals some `z_j = φ_j α`, whose simple-zero property is delivered
by the IFT branch. -/
theorem convSmall_all_zeros_simple
    (S : SignedGaussianCombination)
    (hsimple : ∀ x, S.density x = 0 → deriv S.density x ≠ 0)
    (r : ℕ) (x : Fin r → ℝ) (hx_mono : StrictMono x)
    (hx_zero : ∀ j, S.density (x j) = 0)
    (hx_all : zeroCount S.density = (r : ℕ∞)) :
    ∃ α_pers, 0 < α_pers ∧ ∀ α, ∀ hα : 0 < α, α < α_pers →
      zeroCount (convolveWithGaussian S.density α hα) ≤ (r : ℕ∞) →
      ∀ w, convolveWithGaussian S.density α hα w = 0 →
        deriv (convolveWithGaussian S.density α hα) w ≠ 0 := by
  classical
  -- Re-run the IFT branch construction (we need the simple-zero clause `_hφ_deriv`).
  set f : ℝ → ℝ → ℝ := fun c y => fFamU S c y with hf_def
  set D : ℝ → ℝ → ℝ := fun c y => deriv (fun y => fFamU S c y) y with hD_def
  have hf0_zero : ∀ j : Fin r, fFamU S 0 (x j) = 0 := by
    intro j; rw [fFamU_zero]; exact hx_zero j
  have hD0_ne : ∀ j : Fin r, deriv (fun y => fFamU S 0 y) (x j) ≠ 0 := by
    intro j; rw [fFamU_zero_fun]; exact hsimple (x j) (hx_zero j)
  have hIFT : ∀ j : Fin r, ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δ) δ) ∧ φ 0 = x j ∧
      (∀ c : ℝ, |c| < δ → f c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δ → D c (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δ → ∀ y : ℝ,
        f c y = 0 → |y - x j| < ε → y = φ c) := by
    intro j; simp only [hf_def, hD_def]; exact ift_branchU S (x j) (hf0_zero j) (hD0_ne j)
  choose δf hδf_pos φ hφ_contOn hφ_zero hφ_root hφ_deriv hφ_uniq using hIFT
  -- Separation radius ε₀ between distinct base zeros (same as forward lemma).
  set pairs : Finset (Fin r × Fin r) :=
    (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 ≠ p.2) with hpairs_def
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
    rw [hε₀_def, dif_pos hne]; exact Finset.inf'_le _ hmem
  -- Closeness radius ρ_j with |φ_j c - x_j| < ε₀ for 0 ≤ c < ρ_j.
  have hclose : ∀ j : Fin r, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δf j ∧
      ∀ c : ℝ, 0 ≤ c → c < ρ → |φ j c - x j| < ε₀ := by
    intro j
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-(δf j)) (δf j) := ⟨by linarith [hδf_pos j], hδf_pos j⟩
    have hcontAt : ContinuousWithinAt (φ j) (Set.Ioo (-(δf j)) (δf j)) 0 := (hφ_contOn j) 0 h0mem
    have htend : Filter.Tendsto (φ j) (nhdsWithin 0 (Set.Ioo (-(δf j)) (δf j))) (nhds (x j)) := by
      have := hcontAt; rw [ContinuousWithinAt, hφ_zero j] at this; exact this
    have hball : {y : ℝ | |y - x j| < ε₀} ∈ nhds (x j) := by
      have : Metric.ball (x j) ε₀ ∈ nhds (x j) := Metric.ball_mem_nhds _ hε₀_pos
      apply Filter.mem_of_superset this
      intro y hy; rw [Metric.mem_ball, Real.dist_eq] at hy; exact hy
    have hpre := htend hball
    rw [Filter.mem_map, mem_nhdsWithin] at hpre
    obtain ⟨U, hU_open, hU_mem, hU_sub⟩ := hpre
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
    have hc_Ioo : c ∈ Set.Ioo (-(δf j)) (δf j) := ⟨by linarith [hδf_pos j], hc_δ⟩
    have : c ∈ U ∩ Set.Ioo (-(δf j)) (δf j) := ⟨hc_U, hc_Ioo⟩
    have := hU_sub this; simpa using this
  choose ρ hρ_pos hρ_le hρ_close using hclose
  set α_pers : ℝ :=
    if hne : (Finset.univ : Finset (Fin r)).Nonempty then
      (Finset.univ : Finset (Fin r)).inf' hne ρ
    else 1 with hαpers_def
  have hαpers_pos : 0 < α_pers := by
    rw [hαpers_def]
    split
    · rename_i hne; rw [Finset.lt_inf'_iff]; intro j _; exact hρ_pos j
    · norm_num
  have hαpers_le : ∀ j : Fin r, α_pers ≤ ρ j := by
    intro j
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j, Finset.mem_univ _⟩
    rw [hαpers_def, dif_pos hne]; exact Finset.inf'_le _ (Finset.mem_univ j)
  refine ⟨α_pers, hαpers_pos, ?_⟩
  intro α hα hα_lt hcount_le w hw_zero
  -- Each `α` is below ρ_j, so `|φ_j α - x_j| < ε₀` and `|α| < δf j`.
  have hα_lt_ρ : ∀ j : Fin r, α < ρ j := fun j => lt_of_lt_of_le hα_lt (hαpers_le j)
  have hα_lt_δ : ∀ j : Fin r, |α| < δf j := by
    intro j
    rw [abs_of_nonneg (le_of_lt hα)]
    exact lt_of_lt_of_le (hα_lt_ρ j) (hρ_le j)
  have hclose_j : ∀ j : Fin r, |φ j α - x j| < ε₀ :=
    fun j => hρ_close j α (le_of_lt hα) (hα_lt_ρ j)
  -- The injected zeros z j = φ j α.
  set z : Fin r → ℝ := fun j => φ j α with hz_def
  -- z is injective (disjoint ε₀-neighbourhoods).
  have hz_inj : Function.Injective z := by
    intro i j hij
    by_contra hne
    have heq : φ i α = φ j α := hij
    have hsep : ε₀ ≤ |x i - x j| / 2 := hε₀_sep i j hne
    have : |x i - x j| < 2 * ε₀ := by
      have h1 : |x i - x j| ≤ |x i - φ i α| + |φ i α - x j| := abs_sub_le _ _ _
      have h2 : |φ i α - x j| ≤ |φ i α - φ j α| + |φ j α - x j| := abs_sub_le _ _ _
      have h3 : |φ i α - φ j α| = 0 := by rw [heq]; simp
      have h4 : |x i - φ i α| = |φ i α - x i| := abs_sub_comm _ _
      rw [h4] at h1
      calc |x i - x j| ≤ |φ i α - x i| + |φ i α - x j| := h1
        _ ≤ |φ i α - x i| + (|φ i α - φ j α| + |φ j α - x j|) := by linarith [h2]
        _ = |φ i α - x i| + |φ j α - x j| := by rw [h3]; ring
        _ < ε₀ + ε₀ := by linarith [hclose_j i, hclose_j j]
        _ = 2 * ε₀ := by ring
    linarith [hsep, this]
  -- Each z j is a zero of the convolution.
  have hz_zero : ∀ j : Fin r, convolveWithGaussian S.density α hα (z j) = 0 := by
    intro j
    have hroot : f α (φ j α) = 0 := hφ_root j α (hα_lt_δ j)
    have heqv : fFamU S α (φ j α) = convolveWithGaussian S.density α hα (φ j α) :=
      fFamU_eq_convolve S α hα (φ j α)
    simp only [hf_def] at hroot
    rw [heqv] at hroot; exact hroot
  -- range z ⊆ zeroSet(conv).
  have hrange_sub : Set.range z ⊆ zeroSet (convolveWithGaussian S.density α hα) := by
    rintro _ ⟨j, rfl⟩
    rw [zeroSet_def, Set.mem_setOf_eq]; exact hz_zero j
  -- (range z).encard = r.
  have hrange_card : (Set.range z).encard = (r : ℕ∞) := by
    rw [← Set.image_univ, Set.InjOn.encard_image (hz_inj.injOn), Set.encard_univ]
    simp
  -- range z is finite.
  have hrange_fin : (Set.range z).Finite := Set.finite_range z
  -- zeroCount(conv) = (zeroSet conv).encard ≤ r = (range z).encard.
  have hle : (zeroSet (convolveWithGaussian S.density α hα)).encard ≤ (Set.range z).encard := by
    rw [hrange_card]
    rw [← zeroCount_def]; exact hcount_le
  -- Antisymmetry: range z = zeroSet(conv).
  have heq_sets : Set.range z = zeroSet (convolveWithGaussian S.density α hα) :=
    Set.Finite.eq_of_subset_of_encard_le hrange_fin hrange_sub hle
  -- w is a zero, hence w ∈ range z, hence w = z j = φ j α for some j.
  have hw_mem : w ∈ Set.range z := by
    rw [heq_sets, zeroSet_def, Set.mem_setOf_eq]; exact hw_zero
  obtain ⟨j, hj⟩ := hw_mem
  -- Simplicity at z j from the IFT branch's simple-zero clause.
  have hderiv_fam : deriv (fun y => fFamU S α y) (φ j α) ≠ 0 := by
    have := hφ_deriv j α (hα_lt_δ j)
    simpa [hD_def] using this
  -- Bridge: deriv(conv) (φ j α) = deriv(fFamU S α) (φ j α).
  rw [show w = φ j α from by rw [← hj, hz_def]]
  rw [deriv_convolve_eq S α hα (φ j α)]
  exact hderiv_fam

/-! ## Sub-lemma (A): near-delta add-Gaussian threshold for the normalized family

The genuine per-`c` ("pointwise") ingredient of the §6.1 add-near-delta step, stated
for the NORMALIZED convolution family `fFamU` (= `conv(S.density, c)` for `c > 0`),
rather than the bare-coefficient family `g_c` of
`Workspace.PriorWork.GaussianPerturbationThresholdLSC`.

For a fixed positive convolution width `c`, the slice `x ↦ fFamU S c x` is the density
of the honest signed combination `heatShift S c`, hence:
  * real-analytic on all of `ℝ` (`Prop7AnalyticityOfMixture (heatShift S c)`), and
  * carries a two-sided Gaussian-envelope tail bound (`SublemmaTailDominationPaper
    (heatShift S c)`), provided `S` has at least one nonzero component.
Feeding these together with the slice's all-simple-zeros and `≤ N`-zeros properties
(exactly what `convSmall_all_zeros_simple` together with Hummel–Gidas supply for small
`c`) into the fully-proven `Prop7AddGaussianAddsAtMostTwoZeros` yields, for each fixed
`c`, a per-`c` threshold `v₀(c) > 0` below which `conv(S.density, c) + a_k·N(μ_k, v)`
has at most `N + 2` zeros. This is the axiom-clean pointwise core of sub-lemma (A).
-/

/-- **Pointwise (per-width) near-delta threshold for the normalized convolution
family.** Fix `S` with at least one nonzero component, a positive convolution width
`c`, and suppose the convolved density `conv(S.density, c)` has all-simple zeros and at
most `N` zeros. Then for every `a_k ≠ 0` and every `μ_k` there is a threshold
`v₀ > 0` such that for all `v ∈ (0, v₀]` the near-delta perturbation
`conv(S.density, c) x + a_k·N(μ_k, v, x)` has at most `N + 2` zeros. -/
theorem convFamily_pointwise_addGaussian_threshold
    (S : SignedGaussianCombination)
    (hS_ne : ∃ p ∈ S.components, p.1 ≠ 0)
    (c : ℝ) (hc : 0 < c)
    (N : ℕ)
    (hsimple : ∀ w, convolveWithGaussian S.density c hc w = 0 →
      deriv (convolveWithGaussian S.density c hc) w ≠ 0)
    (hcount : Workspace.Types.ZeroCount.hasAtMostNZeros
      (convolveWithGaussian S.density c hc) N)
    (a_k : ℝ) (ha_k : a_k ≠ 0) (μ_k : ℝ) :
    ∃ v₀ : ℝ, 0 < v₀ ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => convolveWithGaussian S.density c hc x +
            a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x)
          (N + 2) := by
  -- The slice equals the density of the honest combination `heatShift S c`.
  have hslice : convolveWithGaussian S.density c hc = (heatShift S c hc).density := by
    funext x; exact heatShift_density_eq_convolve S c hc x
  -- The slice has at most `N` zeros, hence is NOT identically zero: an identically
  -- zero density would have `zeroSet = univ` (infinite), contradicting `hcount`.
  -- This supplies the axiom-clean `SublemmaTailDomination`'s hypothesis
  -- `∃ x, (heatShift S c hc).density x ≠ 0` without routing through the FALSE-RISK
  -- MaxVariance axioms that `SublemmaTailDominationPaper` transitively used.
  have hHS_density_ne : ∃ x, (heatShift S c hc).density x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hzs : Workspace.Types.ZeroCount.zeroSet
        (convolveWithGaussian S.density c hc) = Set.univ := by
      ext x
      simp only [Workspace.Types.ZeroCount.zeroSet_def, Set.mem_setOf_eq, Set.mem_univ,
        iff_true]
      rw [hslice]; exact hcon x
    rw [Workspace.Types.ZeroCount.hasAtMostNZeros_def,
      Workspace.Types.ZeroCount.zeroCount_def, hzs] at hcount
    have hinf : (Set.univ : Set ℝ).encard = ⊤ :=
      Set.Infinite.encard_eq (Set.infinite_univ (α := ℝ))
    rw [hinf] at hcount
    exact absurd hcount (by simp)
  -- Analyticity of the slice.
  have hanalytic : AnalyticOnNhd ℝ (convolveWithGaussian S.density c hc) Set.univ := by
    rw [hslice]; exact Prop7AnalyticityOfMixture (heatShift S c hc)
  -- Tail-Gaussian envelope of the slice.
  have henvelope :
      ∃ b b' a a' s s' : ℝ, b < b' ∧ a ≠ 0 ∧ a' ≠ 0 ∧ 0 < s ∧ 0 < s' ∧
        (∀ x : ℝ, x < b →
            (convolveWithGaussian S.density c hc x).sign = a.sign ∧
            |a| * (1 / Real.sqrt (2 * Real.pi * s)) * Real.exp (-x ^ 2 / (2 * s)) <
              |convolveWithGaussian S.density c hc x|) ∧
        (∀ x : ℝ, x > b' →
            (convolveWithGaussian S.density c hc x).sign = a'.sign ∧
            |a'| * (1 / Real.sqrt (2 * Real.pi * s')) * Real.exp (-x ^ 2 / (2 * s')) <
              |convolveWithGaussian S.density c hc x|) := by
    rw [hslice]
    exact Workspace.ProofLemmas.SublemmaTailDomination (heatShift S c hc) hHS_density_ne
  -- Apply the fully-proven per-base Prop 7 add-Gaussian count.
  exact Prop7AddGaussianAddsAtMostTwoZeros
    (convolveWithGaussian S.density c hc) hanalytic N hcount hsimple henvelope a_k ha_k μ_k

/-- **Uniform (band-uniform) near-delta threshold for the normalized convolution
family — sub-lemma (A).** Fix `S` with at least one nonzero component and a compact band
of positive convolution widths `K ⊂ (0, ∞)`. Suppose on the whole band the convolved
density `conv(S.density, c)` has all-simple zeros and at most `N` zeros, and suppose the
per-width threshold function (which `convFamily_pointwise_addGaussian_threshold` produces
pointwise) is lower-semicontinuous on `K` — the single analytic-stability input, the
`fFamU`-analogue of `Workspace.PriorWork.GaussianPerturbationThresholdLSC`. Then there is a
single threshold `v₀ > 0`, uniform over the entire band, below which
`conv(S.density, c) + a_k·N(μ_k, v)` has at most `N + 2` zeros for every `c ∈ K`.

The compactness extraction of the uniform `v₀` from the LSC pointwise threshold is the
fully-proven `Workspace.ProofLemmas.CompactPositiveLSCInfimum`; this lemma performs that
extraction for the normalized family, mirroring
`Workspace.PriorWork.UniformGaussianPerturbationThreshold` but for the `fFamU` family
instead of the bare-coefficient `g_c` family. -/
theorem convFamily_uniform_addGaussian_threshold
    (S : SignedGaussianCombination)
    (hS_ne : ∃ p ∈ S.components, p.1 ≠ 0)
    (N : ℕ)
    (K : Set ℝ) (hK_compact : IsCompact K) (hK_pos : ∀ c ∈ K, 0 < c)
    (a_k : ℝ) (ha_k : a_k ≠ 0) (μ_k : ℝ)
    -- per-width threshold function and its LSC + threshold property (the `fFamU`
    -- analogue of `GaussianPerturbationThresholdLSC`)
    (v₀ : ℝ → ℝ) (hv₀_lsc : LowerSemicontinuousOn v₀ K)
    (hv₀ : ∀ (c : ℝ) (hcK : c ∈ K), 0 < v₀ c ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ c →
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => convolveWithGaussian S.density c (hK_pos c hcK) x +
            a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x)
          (N + 2)) :
    ∃ v_band : ℝ, 0 < v_band ∧
      ∀ (c : ℝ) (hcK : c ∈ K), ∀ (v : ℝ) (hv : 0 < v), v ≤ v_band →
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => convolveWithGaussian S.density c (hK_pos c hcK) x +
            a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x)
          (N + 2) := by
  -- Positivity of the pointwise threshold on `K`.
  have hv₀_pos : ∀ c ∈ K, 0 < v₀ c := fun c hc => (hv₀ c hc).1
  -- Compactness/EVT extraction of a uniform positive lower bound `m ≤ v₀ c`.
  obtain ⟨m, hm_pos, hm_lb⟩ :=
    Workspace.ProofLemmas.CompactPositiveLSCInfimum K hK_compact v₀ hv₀_lsc hv₀_pos
  refine ⟨m, hm_pos, ?_⟩
  intro c hcK v hv hv_le
  exact (hv₀ c hcK).2 v hv (hv_le.trans (hm_lb c hcK))

/-! ## Uniform-over-band substrate (three pieces) + diagonal assembly

The §6.1 add-near-delta step at width `c` produces, via
`convFamily_pointwise_addGaussian_threshold`, a per-width threshold `v₀(c)` below
which `conv(S.density,c)+a_k·N(μ_k,v)` gains ≤2 zeros. For the *diagonal* application
that `hh_bound` needs (convolution width = bump width = `v`), we must keep `v₀(c)`
bounded below as `c` ranges over a compact band `[0, c_max]`. The three region
thresholds (a/b/c) each degenerate unless certain `g = fFamU S c`-dependent
quantities stay uniformly controlled over the band:

* region (a)  — a uniform Gaussian-tail envelope `(b,b',s,s')`;
* region (b)  — a uniform C⁰ floor `g_lb` away from the (continuously-moving) zeros;
* region (c)  — a uniform non-degeneracy floor `m_floor ≤ |fFamU S c (ν)|` at the
  bump center, which fails only if `S.density (ν) = 0`.

We bank pieces (3) [center non-degeneracy] and (2) [C⁰ floor as a continuity floor
on a center-window-removed compact], and state the band-uniform diagonal assembly.
-/

/-- The scalar map `c ↦ fFamU S c x₀` is continuous on `goodSetU S` (in particular
on any band `[0, c_max] ⊆ goodSetU S`), as a slice of the jointly-continuous family. -/
theorem fFamU_value_contOn_param (S : SignedGaussianCombination) (x₀ : ℝ) :
    ContinuousOn (fun c : ℝ => fFamU S c x₀) (goodSetU S) := by
  have hpair : ContinuousOn (fun c : ℝ => ((c, x₀) : ℝ × ℝ)) (goodSetU S) :=
    (continuousOn_id (s := goodSetU S)).prodMk continuousOn_const
  have hmem : ∀ c ∈ goodSetU S, ((c, x₀) : ℝ × ℝ) ∈ goodSetU S ×ˢ (Set.univ : Set ℝ) :=
    fun c hc => ⟨hc, Set.mem_univ _⟩
  exact (fFamU_value_contOn S).comp hpair hmem

/-! ### Piece (3): uniform region-(c) non-degeneracy floor at the bump center

If `S.density (ν) ≠ 0` (the paper's "`μ_k` is not a zero of `g₀`" genericity
condition, supplied at the call site) then by continuity of `c ↦ fFamU S c ν` at
`c = 0` (where it equals `S.density ν`) there is a band `[0, c_max]` and a floor
`m_floor > 0` with `|fFamU S c ν| ≥ m_floor` for every `c` in the band. This stops
the region-(c) threshold `exp(-(2K/m_G+1))` from collapsing. -/
theorem convFamily_center_nondegenerate_floor
    (S : SignedGaussianCombination) (ν : ℝ) (hν : S.density ν ≠ 0) :
    ∃ c_max : ℝ, 0 < c_max ∧ ∃ m_floor : ℝ, 0 < m_floor ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max → m_floor ≤ |fFamU S c ν| := by
  -- value at c = 0 is S.density ν, of nonzero absolute value
  set L : ℝ := S.density ν with hL_def
  have hL0 : fFamU S 0 ν = L := by rw [fFamU_zero]
  have hL_pos : 0 < |L| := abs_pos.mpr hν
  -- continuity of c ↦ |fFamU S c ν| on goodSetU at 0
  have hcont : ContinuousOn (fun c : ℝ => fFamU S c ν) (goodSetU S) :=
    fFamU_value_contOn_param S ν
  have habs_cont : ContinuousOn (fun c : ℝ => |fFamU S c ν|) (goodSetU S) :=
    hcont.abs
  have h0_mem : (0 : ℝ) ∈ goodSetU S := goodSetU_zero_mem S
  have hcontAt : ContinuousWithinAt (fun c : ℝ => |fFamU S c ν|) (goodSetU S) 0 :=
    habs_cont 0 h0_mem
  have htend : Filter.Tendsto (fun c : ℝ => |fFamU S c ν|)
      (nhdsWithin 0 (goodSetU S)) (nhds |L|) := by
    have := hcontAt
    rw [ContinuousWithinAt, show |fFamU S 0 ν| = |L| by rw [hL0]] at this
    exact this
  -- {t | |L|/2 < t} is a nhd of |L|
  have hnhds : {t : ℝ | |L| / 2 < t} ∈ nhds |L| := by
    apply IsOpen.mem_nhds (isOpen_lt continuous_const continuous_id)
    show |L| / 2 < |L|; linarith [hL_pos]
  have hpre : (fun c : ℝ => |fFamU S c ν|) ⁻¹' {t : ℝ | |L| / 2 < t}
      ∈ nhdsWithin 0 (goodSetU S) := htend hnhds
  rw [mem_nhdsWithin] at hpre
  obtain ⟨U, hU_open, hU0, hU_sub⟩ := hpre
  rw [Metric.isOpen_iff] at hU_open
  obtain ⟨t, ht_pos, ht_ball⟩ := hU_open 0 hU0
  refine ⟨t / 2, by linarith, |L| / 2, by linarith [hL_pos], ?_⟩
  intro c hc_nn hc_le
  have hc_t : c < t := by linarith
  have hc_ball : c ∈ Metric.ball (0 : ℝ) t := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hc_nn]; exact hc_t
  have hc_U : c ∈ U := ht_ball hc_ball
  have hc_good : c ∈ goodSetU S := goodSetU_of_nonneg S hc_nn
  have hmem := hU_sub ⟨hc_U, hc_good⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hmem
  exact le_of_lt hmem

/-! ### Piece (2): uniform C⁰ floor of `|fFamU S c x|` on a band × compact-away-from-zeros

Region (b)'s coefficient `C₂ ∝ g_lb · d² / |a_k|` needs a single positive floor
`g_lb` lower-bounding `|fFamU S c x|` simultaneously over all band widths `c ∈ [0,c_max]`
and all `x` in the compact region `A` that the region-partition argument keeps away
from the (continuously-moving) zeros of `fFamU S c`.

The faithful compactness core: if `A` is compact and `fFamU S c x ≠ 0` for every
`(c,x)` in the band-product `[0,c_max] × A` (this is exactly "`A` is uniformly zero-free
across the band" — the IFT zero-branches move the zeros continuously, so for `c_max`
small the zeros stay inside their own windows, leaving `A` zero-free), then the jointly
continuous `(c,x) ↦ |fFamU S c x|` attains a positive minimum `g_lb > 0` on the
(nonempty) compact product. -/
theorem convFamily_C0_floor_on_band
    (S : SignedGaussianCombination)
    (c_max : ℝ) (hc_max : 0 < c_max)
    (A : Set ℝ) (hA_compact : IsCompact A) (hA_ne : A.Nonempty)
    (hzero_free : ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x ∈ A, fFamU S c x ≠ 0) :
    ∃ g_lb : ℝ, 0 < g_lb ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max → ∀ x ∈ A, g_lb ≤ |fFamU S c x| := by
  classical
  -- The band-product is compact.
  set K : Set (ℝ × ℝ) := Set.Icc 0 c_max ×ˢ A with hK_def
  have hK_compact : IsCompact K := (isCompact_Icc).prod hA_compact
  have hK_ne : K.Nonempty := ⟨(0, hA_ne.choose), ⟨le_refl 0, hc_max.le⟩, hA_ne.choose_spec⟩
  -- The product sits inside `goodSetU S ×ˢ univ`, where the value-map is continuous.
  have hK_sub : K ⊆ goodSetU S ×ˢ (Set.univ : Set ℝ) := by
    rintro ⟨c, x⟩ ⟨hc, _hx⟩
    exact ⟨goodSetU_of_nonneg S hc.1, Set.mem_univ _⟩
  -- `(c,x) ↦ |fFamU S c x|` is continuous on `K`.
  have habs_contOn : ContinuousOn (fun p : ℝ × ℝ => |fFamU S p.1 p.2|) K :=
    ((fFamU_value_contOn S).mono hK_sub).abs
  -- It attains a minimum at some point of `K`.
  obtain ⟨p₀, hp₀_mem, _hsInf, hp₀_min⟩ :=
    IsCompact.exists_sInf_image_eq_and_le hK_compact hK_ne habs_contOn
  -- The minimum value is positive (it is `|·|` of a nonzero number).
  have hp₀_pos : 0 < |fFamU S p₀.1 p₀.2| := by
    apply abs_pos.mpr
    rcases hp₀_mem with ⟨⟨hc0, hcmax⟩, hxA⟩
    exact hzero_free p₀.1 hc0 hcmax p₀.2 hxA
  refine ⟨|fFamU S p₀.1 p₀.2|, hp₀_pos, ?_⟩
  intro c hc0 hcmax x hxA
  have hmem : (c, x) ∈ K := ⟨⟨hc0, hcmax⟩, hxA⟩
  exact hp₀_min (c, x) hmem

/-! ### Piece (1): uniform Gaussian-tail envelope over the band

Region (a)'s threshold `HurwitzGaussianPerturbationTailDominance` depends on `g`
ONLY through the envelope params `(b,b',a,a',s,s')` (and `a_k,μ_k`). Hence a single
envelope tuple valid for the whole family `fFamU S c`, `c ∈ [0,c_max]`, makes region
(a)'s threshold band-uniform.

For each `c > 0`, `fFamU S c = (heatShift S c).density` carries the two-sided
Gaussian envelope of `SublemmaTailDomination (heatShift S c)`, whose dominant
variance is `max_i (varSqᵢ) + c` — continuous and bounded on `c ∈ [0, c_max]`. The
content of this lemma is that the envelope params can be chosen UNIFORMLY in `c`
across the band (the largest tail variance `s := max_i varSqᵢ + c_max` dominates every
slice; the sign/coefficient data is stable because every slice is the heat-flow of the
same base combination). Producing the single stable tuple requires re-deriving
`SublemmaTailDominationSound` with explicit, uniform-in-`c` constants — the lone
genuinely-resistant analytic step of this substrate (the residual `gap (A)` of
`lean_knowledge.md`). We isolate it as a single private obligation so the surrounding
band-uniform assembly is otherwise axiom-clean. -/
theorem convFamily_uniform_envelope_on_band
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
  -- RESIDUAL: the uniform-in-`c` re-derivation of `SublemmaTailDominationSound`.
  -- Every individual slice has an envelope (`SublemmaTailDomination (heatShift S c)`),
  -- and `convFamily_pointwise_addGaussian_threshold` already consumes the per-slice
  -- envelope; only the BAND-UNIFORM choice of `(b,b',a,a',s,s')` is open.
  sorry

/-! ### Diagonal assembly: a single band-uniform near-delta threshold `v₀`

`hh_bound` consumes the §6.1 add-near-delta step on the DIAGONAL: convolution width
= bump width = `v`. Concretely it needs a single `v₀ > 0` with
`hasAtMostNZeros (fFamU S v + a_k·N(ν, v)) (N+2)` for every `v ∈ (0, v₀]`.

Per-width, `convFamily_pointwise_addGaussian_threshold` supplies a threshold `v₀(c)`
(at width `c`) below which bumps add ≤2 zeros — but the diagonal forces the bump width
to equal `c` itself, so we need `c ≤ v₀(c)`, i.e. `v₀(c)` bounded below by a single
positive constant `m` over the band `(0, c_max]`. That uniform floor is exactly what
pieces (1)+(2)+(3) — the uniform region (a) envelope, the uniform region (b) `g_lb`
C⁰ floor, and the uniform region (c) `m_floor` center non-degeneracy — together with
the banked region (b) `ε₁` floor (`branchDeriv_uniform_lower_bound`) produce: each
region threshold (a)/(b)/(c) is a monotone function of these floors, so a uniform floor
on each yields a uniform `m ≤ v₀(c)`.

We package the uniform-floor consequence as the hypothesis `hfloor` (the consolidated
output of 1+2+3+banked through the explicit region-threshold formulas) and discharge
the diagonal selection `v₀ := min m c_max` fully. This mirrors how
`convFamily_uniform_addGaussian_threshold` consumes the LSC threshold, but specializes
to the diagonal that `hh_bound` actually needs. -/
theorem convFamily_uniform_threshold_concrete
    (S : SignedGaussianCombination)
    (hS_ne : ∃ p ∈ S.components, p.1 ≠ 0)
    (ν : ℝ) (hν : S.density ν ≠ 0)
    (N : ℕ)
    (a_k : ℝ) (ha_k : a_k ≠ 0)
    (c_max : ℝ) (hc_max : 0 < c_max)
    -- the per-width near-delta threshold (from `convFamily_pointwise_addGaussian_threshold`):
    (v₀ : ℝ → ℝ)
    (hv₀ : ∀ (c : ℝ) (hc : 0 < c), c ≤ c_max → 0 < v₀ c ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ c →
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => convolveWithGaussian S.density c hc x +
            a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x)
          (N + 2))
    -- the UNIFORM-FLOOR consequence of pieces (1)+(2)+(3)+banked ε₁: a single `m > 0`
    -- bounding the per-width threshold below across the whole band `(0, c_max]`.
    (m : ℝ) (hm_pos : 0 < m) (hfloor : ∀ (c : ℝ), 0 < c → c ≤ c_max → m ≤ v₀ c) :
    ∃ v_diag : ℝ, 0 < v_diag ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v_diag →
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => fFamU S v x +
            a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x)
          (N + 2) := by
  refine ⟨min m c_max, lt_min hm_pos hc_max, ?_⟩
  intro v hv hv_le
  -- `v` is in the band and below its own per-width threshold.
  have hv_le_m : v ≤ m := le_trans hv_le (min_le_left _ _)
  have hv_le_cmax : v ≤ c_max := le_trans hv_le (min_le_right _ _)
  -- the conv width is exactly `v` (the diagonal): rewrite `fFamU S v = conv(S.density, v)`.
  have hslice : (fun x => fFamU S v x +
        a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x)
      = (fun x => convolveWithGaussian S.density v hv x +
        a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x) := by
    funext x; rw [fFamU_eq_convolve S v hv x]
  rw [hslice]
  -- per-width threshold at width `c = v`, applied with bump width `= v ≤ m ≤ v₀ v`.
  have hthr := (hv₀ v hv hv_le_cmax).2 v hv (le_trans hv_le_m (hfloor v hv hv_le_cmax))
  exact hthr

end Workspace.ProofLemmas
