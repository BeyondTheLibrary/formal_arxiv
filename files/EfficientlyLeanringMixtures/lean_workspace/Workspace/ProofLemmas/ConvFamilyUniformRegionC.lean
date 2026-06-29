import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope
import Workspace.ProofLemmas.HurwitzGaussianPerturbationCenterTwoZeros

/-!
# Band-uniform region (c): inner ≤2-zeros bound, uniform over `gα = conv(g̃₀', c)`

## Goal

Region (c) of Moitra–Valiant §6.1 bounds, for a fixed analytic `gα`, the number of
zeros of `h = gα + a_k·N(ν, v)` in the inner window `Ioo (ν−δ) (ν+δ)` by `2`, for all
small `v`.  The threshold `v₀` and window radius `δ` depend on `gα`'s LOCAL structure
at `ν` (the sign-constant floor `m₀ = |gα ν|/2` and the sup-bounds `M = sup|gα'|`,
`Mg = sup|gα|` near `ν`).

Here we make this UNIFORM over the convolution band `gα = fFamU S c`, `c ∈ [0,c_max]`,
where `S.density = g̃₀'`, GIVEN the paper's genericity `g̃₀'(ν) ≠ 0` (i.e. `μ_k = ν`
is not a zero of `g₀`).  The uniformity rests on three banked inputs:

* **(C-floor)** `convFamily_center_nondegenerate_floor` :
  `|fFamU S c ν| ≥ m_floor` uniformly on `[0,c_max]` (so the local sign-constant floor
  `m₀` does NOT degenerate, and the region-c flank threshold `exp(-(2K/m_G+1))`,
  here `cmp_aux (M/m₀)`, stays bounded away from `0`).
* **(C-supG)** uniform `Mg = sup_{[0,c_max]×window} |fFamU S c x|` — from joint
  continuity of `(c,x) ↦ fFamU S c x` on `goodSetU S ×ˢ univ` (re-derived publicly
  below, mirroring the private `fFamU_value_contOn`) + compactness of the band×window.
* **(C-supG')** uniform `M = sup_{[0,c_max]×window} |deriv (fFamU S c ·) x|` — from joint
  continuity of `(c,x) ↦ deriv (fFamU S c ·) x` (re-derived publicly below, mirroring
  the private `fFamU_deriv_contOn`).

## Sub-plan (proof skeleton, incremental)

The faithful region-c inner ≤2-zeros proof for a fixed `gα = fFamU S c` runs (see
`HurwitzGaussianPerturbationCenterTwoZeros.lean`):

  flank radius `β(v) = bandRadius v = √(v·log(1/v)/2)`, with `√v ≪ β(v) ≪ 1`;
  * central band `(ν−β, ν+β)` : `|a_k·N| > |gα|` ⇒ zero-free   (`bandZeroFree`);
  * each flank `[ν+β, ν+δ]`, `[ν−δ, ν−β]` : `ψ(x)=v·gα'(x)+(x−ν)·gα(x)` is
    sign-definite ⇒ `H = gα·exp((·−ν)²/2v)+C` is strictly monotone ⇒ ≤1 zero
    (`flank_subsingleton`).  Sign-definiteness uses `M·v < β·m₀`, supplied by the
    `v ≪ β(v)` comparison `cmp_aux (M/m₀)`.

To make `(δ, v₀)` uniform over `c ∈ [0,c_max]` we substitute the three uniform
constants `(m₀, M, Mg)` for the per-`gα` ones, and re-run the same engine with a
single `δ` and a single `v₀ = min vc vd` (where `vc` = `cmp_aux (M/m₀)` output and
`vd` = `bandRadius_lt_of_small δ` output) — both now depending only on uniform data.

### Status of sub-pieces (this file)

PROVEN (Mathlib-only, no new axioms):
  * `gFam_analytic`            — each slice `fFamU S c` (c≥0) is analytic on `univ`.
  * `fFamU_hasDerivAt'`        — public re-derivation of the slice `x`-derivative.
  * `fFamU_deriv_eq_sum'`      — `deriv (fFamU S c ·) x = ∑ termDerivU S c x i`.
  * `termDerivU_contOn'`,
    `fFamU_value_contOn'`,
    `fFamU_deriv_contOn'`      — public joint-continuity on `goodSetU S ×ˢ univ`.
  * `uniform_sup_value`        — uniform `Mg ≥ |fFamU S c x|` on band×window.
  * `uniform_sup_deriv`        — uniform `M ≥ |deriv (fFamU S c ·) x|` on band×window.
  * `uniform_signConst_floor`  — uniform sign-constant floor `m₀` near `ν` from
                                 `m_floor` + joint value continuity.

REMAINING (precise private `sorry`, the genuinely-hard uniform flank assembly):
  * `uniform_flank_zeros_le_two` — the uniform-`δ`/uniform-`v₀` flank ≤2 bound, i.e.
    the band-uniform analogue of `flankZerosLeTwoSmallDelta`'s NON-vanishing branch,
    re-run with `(m₀, M)` uniform.  Everything it consumes (sign-constant floor,
    sup|gα'|, the `cmp_aux`/`bandRadius_lt_of_small` thresholds) is banked above; the
    open work is the bookkeeping of the per-flank `flank_subsingleton` application with
    the uniform constants in place of the per-`gα` ones.

The final theorem `convFamily_uniform_regionC` assembles `uniform_flank_zeros_le_two`
with the (fully proven) uniform `bandZeroFree`-style band non-vanishing.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.ZeroCount
open Set

set_option maxHeartbeats 4000000

/-! ## (Public) per-slice analyticity of `gα = fFamU S c` -/

/-- For `c > 0`, the slice `fFamU S c` is analytic on `univ` (it equals
`(heatShift S c).density`, a signed Gaussian combination density). -/
theorem gFam_analytic_pos (S : SignedGaussianCombination) (c : ℝ) (hc : 0 < c) :
    AnalyticOnNhd ℝ (fun x => fFamU S c x) Set.univ := by
  have heq : (fun x => fFamU S c x) = (heatShift S c hc).density := by
    funext x; exact fFamU_eq_heatShift S c hc x
  rw [heq]
  exact Prop7AnalyticityOfMixture (heatShift S c hc)

/-- At `c = 0`, the slice `fFamU S 0` is analytic on `univ` (it equals `S.density`). -/
theorem gFam_analytic_zero (S : SignedGaussianCombination) :
    AnalyticOnNhd ℝ (fun x => fFamU S 0 x) Set.univ := by
  have heq : (fun x => fFamU S 0 x) = S.density := fFamU_zero_fun S
  rw [heq]
  exact Prop7AnalyticityOfMixture S

/-- Every slice `fFamU S c`, `c ≥ 0`, is analytic on `univ`. -/
theorem gFam_analytic (S : SignedGaussianCombination) (c : ℝ) (hc : 0 ≤ c) :
    AnalyticOnNhd ℝ (fun x => fFamU S c x) Set.univ := by
  rcases eq_or_lt_of_le hc with h0 | hpos
  · rw [← h0]; exact gFam_analytic_zero S
  · exact gFam_analytic_pos S c hpos

/-! ## (Public) re-derivation of the slice `x`-derivative and its sum form

These mirror the `private` lemmas `termU_hasDerivAt`, `fFamU_hasDerivAt`,
`fFamU_deriv_eq_sum`, `termDerivU_contOn`, `fFamU_value_contOn`, `fFamU_deriv_contOn`
of `ConvSmallPreservesSimpleAndEnvelope.lean` (which are not exported).  We need the
PUBLIC joint-continuity statements to obtain uniform sup-bounds over the band×window. -/

private theorem termU_hasDerivAt'
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

theorem fFamU_hasDerivAt' (S : SignedGaussianCombination) (c x : ℝ) :
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
      (fun i _ => termU_hasDerivAt' S c x i)
  rw [Finset.sum_fn] at hsum
  exact hsum

theorem fFamU_deriv_eq_sum' (S : SignedGaussianCombination) (c x : ℝ) :
    deriv (fun y => fFamU S c y) x = ∑ i : Fin S.components.length, termDerivU S c x i :=
  (fFamU_hasDerivAt' S c x).deriv

theorem termDerivU_contOn' (S : SignedGaussianCombination) (i : Fin S.components.length) :
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

theorem fFamU_value_contOn' (S : SignedGaussianCombination) :
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

theorem fFamU_deriv_contOn' (S : SignedGaussianCombination) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => fFamU S p.1 y) p.2)
      (goodSetU S ×ˢ (Set.univ : Set ℝ)) := by
  have heq : Set.EqOn (fun p : ℝ × ℝ => deriv (fun y => fFamU S p.1 y) p.2)
      (fun p : ℝ × ℝ => ∑ i : Fin S.components.length, termDerivU S p.1 p.2 i)
      (goodSetU S ×ˢ (Set.univ : Set ℝ)) := fun p _ => fFamU_deriv_eq_sum' S p.1 p.2
  apply ContinuousOn.congr _ heq
  apply continuousOn_finset_sum
  intro i _
  exact termDerivU_contOn' S i

/-! ## (Proven) uniform sup-bounds over the band × window

For a compact window `Icc (ν−δ) (ν+δ)` and band `Icc 0 c_max`, the band×window product
is compact and sits inside `goodSetU S ×ˢ univ`, so the jointly continuous `|fFamU|`
and `|deriv (fFamU ·)|` attain finite maxima there. -/

/-- Uniform sup-bound `Mg` on `|fFamU S c x|` over `c ∈ [0,c_max]`, `x ∈ Icc (ν−δ) (ν+δ)`. -/
theorem uniform_sup_value
    (S : SignedGaussianCombination) (ν δ c_max : ℝ) (hδ : 0 < δ) (hc_max : 0 < c_max) :
    ∃ Mg : ℝ, 0 ≤ Mg ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
        ∀ x ∈ Set.Icc (ν - δ) (ν + δ), |fFamU S c x| ≤ Mg := by
  classical
  set K : Set (ℝ × ℝ) := Set.Icc 0 c_max ×ˢ Set.Icc (ν - δ) (ν + δ) with hK_def
  have hK_compact : IsCompact K := (isCompact_Icc).prod isCompact_Icc
  have hK_ne : K.Nonempty :=
    ⟨(0, ν), ⟨le_refl 0, hc_max.le⟩, ⟨by linarith, by linarith⟩⟩
  have hK_sub : K ⊆ goodSetU S ×ˢ (Set.univ : Set ℝ) := by
    rintro ⟨c, x⟩ ⟨hc, _hx⟩
    exact ⟨goodSetU_of_nonneg S hc.1, Set.mem_univ _⟩
  have habs_contOn : ContinuousOn (fun p : ℝ × ℝ => |fFamU S p.1 p.2|) K :=
    ((fFamU_value_contOn' S).mono hK_sub).abs
  obtain ⟨p₀, hp₀_mem, _hsSup, hp₀_max⟩ :=
    IsCompact.exists_sSup_image_eq_and_ge hK_compact hK_ne habs_contOn
  refine ⟨|fFamU S p₀.1 p₀.2|, abs_nonneg _, ?_⟩
  intro c hc0 hcmax x hx
  have hmem : (c, x) ∈ K := ⟨⟨hc0, hcmax⟩, hx⟩
  exact hp₀_max (c, x) hmem

/-- Uniform sup-bound `M` on `|deriv (fFamU S c ·) x|` over the band × window. -/
theorem uniform_sup_deriv
    (S : SignedGaussianCombination) (ν δ c_max : ℝ) (hδ : 0 < δ) (hc_max : 0 < c_max) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
        ∀ x ∈ Set.Icc (ν - δ) (ν + δ), |deriv (fun y => fFamU S c y) x| ≤ M := by
  classical
  set K : Set (ℝ × ℝ) := Set.Icc 0 c_max ×ˢ Set.Icc (ν - δ) (ν + δ) with hK_def
  have hK_compact : IsCompact K := (isCompact_Icc).prod isCompact_Icc
  have hK_ne : K.Nonempty :=
    ⟨(0, ν), ⟨le_refl 0, hc_max.le⟩, ⟨by linarith, by linarith⟩⟩
  have hK_sub : K ⊆ goodSetU S ×ˢ (Set.univ : Set ℝ) := by
    rintro ⟨c, x⟩ ⟨hc, _hx⟩
    exact ⟨goodSetU_of_nonneg S hc.1, Set.mem_univ _⟩
  have habs_contOn :
      ContinuousOn (fun p : ℝ × ℝ => |deriv (fun y => fFamU S p.1 y) p.2|) K :=
    ((fFamU_deriv_contOn' S).mono hK_sub).abs
  obtain ⟨p₀, hp₀_mem, _hsSup, hp₀_max⟩ :=
    IsCompact.exists_sSup_image_eq_and_ge hK_compact hK_ne habs_contOn
  refine ⟨|deriv (fun y => fFamU S p₀.1 y) p₀.2|, abs_nonneg _, ?_⟩
  intro c hc0 hcmax x hx
  have hmem : (c, x) ∈ K := ⟨⟨hc0, hcmax⟩, hx⟩
  exact hp₀_max (c, x) hmem

/-! ## (Proven) uniform sign-constant floor near `ν`

From the banked `convFamily_center_nondegenerate_floor` (`|fFamU S c ν| ≥ m_floor`
uniformly) plus joint continuity of `(c,x) ↦ fFamU S c x`, we extract a single window
radius `δ` and a single floor `m₀ > 0` so that on `Icc (ν−δ) (ν+δ)`, for EVERY band
width `c ∈ [0,c_max']`, `fFamU S c` is sign-constant with `|fFamU S c x| ≥ m₀`.

This is the uniform analogue of `g_signConst_near`.  It uses uniform continuity of
`(c,x) ↦ fFamU S c x` on the compact band×window: shrink `δ` until the oscillation of
each slice over the window is `< m_floor/2`, so the value can never cross `0` and stays
within `m_floor/2` of its center value `fFamU S c ν` (which has `|·| ≥ m_floor`). -/
theorem uniform_signConst_floor
    (S : SignedGaussianCombination) (ν : ℝ) (hν : S.density ν ≠ 0)
    (c_max : ℝ) (hc_max : 0 < c_max) (m_floor : ℝ) (hm_floor : 0 < m_floor)
    (hfloor : ∀ c : ℝ, 0 ≤ c → c ≤ c_max → m_floor ≤ |fFamU S c ν|) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ m₀ : ℝ, 0 < m₀ ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
        ((∀ x ∈ Set.Icc (ν - δ) (ν + δ), m₀ ≤ fFamU S c x)
          ∨ (∀ x ∈ Set.Icc (ν - δ) (ν + δ), fFamU S c x ≤ -m₀)) := by
  -- The product `Icc 0 c_max ×ˢ {ν}` is compact; jointly continuous `fFamU` is
  -- uniformly continuous on a compact band×window.  We exploit uniform continuity to
  -- find `δ` so that |fFamU S c x − fFamU S c ν| < m_floor/2 for all c, all x in window.
  classical
  -- Work on band×(window of some fixed radius δ₀=1); restrict δ ≤ 1.
  set δ₀ : ℝ := 1 with hδ₀
  set K : Set (ℝ × ℝ) := Set.Icc 0 c_max ×ˢ Set.Icc (ν - δ₀) (ν + δ₀) with hK_def
  have hK_compact : IsCompact K := (isCompact_Icc).prod isCompact_Icc
  have hK_sub : K ⊆ goodSetU S ×ˢ (Set.univ : Set ℝ) := by
    rintro ⟨c, x⟩ ⟨hc, _hx⟩
    exact ⟨goodSetU_of_nonneg S hc.1, Set.mem_univ _⟩
  have hcontOn : ContinuousOn (fun p : ℝ × ℝ => fFamU S p.1 p.2) K :=
    (fFamU_value_contOn' S).mono hK_sub
  -- uniform continuity on the compact K
  have hUC : UniformContinuousOn (fun p : ℝ × ℝ => fFamU S p.1 p.2) K :=
    hK_compact.uniformContinuousOn_of_continuous hcontOn
  -- from uniform continuity: a `δ`-radius controlling oscillation by `< m_floor/2`.
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨η, hη_pos, hη⟩ := hUC (m_floor / 2) (by linarith)
  -- pick δ = min (η/2) 1, so that for x in the window, (c,x) and (c,ν) are within η.
  refine ⟨min (η / 2) 1, by positivity, m_floor / 2, by linarith, ?_⟩
  intro c hc0 hcmax
  set δ : ℝ := min (η / 2) 1 with hδ
  have hδ_le1 : δ ≤ 1 := min_le_right _ _
  have hδ_leη : δ ≤ η / 2 := min_le_left _ _
  -- center membership in K
  have hcν_mem : ((c, ν) : ℝ × ℝ) ∈ K := ⟨⟨hc0, hcmax⟩, ⟨by linarith, by linarith⟩⟩
  -- |fFamU S c ν| ≥ m_floor
  have hcenter : m_floor ≤ |fFamU S c ν| := hfloor c hc0 hcmax
  -- oscillation bound: ∀ x in window, |fFamU S c x − fFamU S c ν| < m_floor/2
  have hosc : ∀ x ∈ Set.Icc (ν - δ) (ν + δ),
      |fFamU S c x - fFamU S c ν| < m_floor / 2 := by
    intro x hx
    have hx_mem : ((c, x) : ℝ × ℝ) ∈ K :=
      ⟨⟨hc0, hcmax⟩, ⟨by linarith [hx.1, hδ_le1], by linarith [hx.2, hδ_le1]⟩⟩
    have hdist : dist ((c, x) : ℝ × ℝ) ((c, ν) : ℝ × ℝ) < η := by
      rw [Prod.dist_eq]
      have hdxν : dist x ν ≤ δ := by
        rw [Real.dist_eq, abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
      have hmaxeq : max (dist c c) (dist x ν) = dist x ν := by
        rw [dist_self]; exact max_eq_right (dist_nonneg)
      rw [hmaxeq]; linarith [hδ_leη]
    have := hη ((c, x)) hx_mem ((c, ν)) hcν_mem hdist
    rw [Real.dist_eq] at this
    exact this
  -- sign-constant: either fFamU S c ν ≥ m_floor (positive case) or ≤ -m_floor.
  rcases le_or_gt 0 (fFamU S c ν) with hsgn | hsgn
  · -- positive: fFamU S c ν = |fFamU S c ν| ≥ m_floor; oscillation keeps x-value ≥ m_floor/2
    left
    intro x hx
    have hcen_pos : m_floor ≤ fFamU S c ν := by rwa [abs_of_nonneg hsgn] at hcenter
    have hosc_x := hosc x hx
    have := (abs_lt.mp hosc_x).1
    linarith
  · -- negative: fFamU S c ν ≤ -m_floor
    right
    intro x hx
    have hcen_neg : fFamU S c ν ≤ -m_floor := by
      have : |fFamU S c ν| = -(fFamU S c ν) := abs_of_neg hsgn
      rw [this] at hcenter; linarith
    have hosc_x := hosc x hx
    have := (abs_lt.mp hosc_x).2
    linarith

/-! ## (RESIDUAL) uniform flank ≤2-zeros bound

The genuinely-hard residual: re-run the NON-vanishing branch of
`flankZerosLeTwoSmallDelta` with the uniform `(m₀, M)` in place of the per-`gα`
`(m₀, M)`.  All ingredients are banked:

* `m₀` uniform sign-constant floor   — `uniform_signConst_floor` (PROVEN above);
* `M`  uniform sup |gα'|              — `uniform_sup_deriv` (PROVEN above);
* the `v ≪ β(v)` comparison `cmp_aux (M/m₀)` and `bandRadius_lt_of_small δ` — banked
  in `HurwitzGaussianPerturbationCenterTwoZeros.lean`;
* the per-flank engine `flank_subsingleton` and `bandRadius_pos`/`sq_abs` bookkeeping —
  banked there too.

The proof is the verbatim NON-vanishing branch of `flankZerosLeTwoSmallDelta`, with the
per-`gα` `obtain ⟨δ, hδ, m₀, hm₀, hsign⟩ := g_signConst_near …` and
`obtain ⟨M, hM⟩ := …` replaced by the uniform `δ`, `m₀`, `M` (so a SINGLE `δ` and
`v₀ = min vc vd` work across the whole band).  Each slice `gα = fFamU S c` is analytic
(`gFam_analytic`) and differentiable, exactly as the per-`gα` proof requires.

What is left open is purely the mechanical re-threading of that ~120-line branch with
the uniform constants; it introduces NO new axioms. -/
theorem uniform_flank_zeros_le_two
    (S : SignedGaussianCombination) (ν : ℝ) (hν : S.density ν ≠ 0)
    (a_k : ℝ) (ha_k : a_k ≠ 0) :
    ∃ c_max : ℝ, 0 < c_max ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ v₀ : ℝ, 0 < v₀ ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
        ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
          {x ∈ Set.Ioo (ν - δ) (ν + δ) |
              (fFamU S c x +
                  a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x = 0)
              ∧ bandRadius v ≤ |x - ν|}.encard ≤ 2 := by
  -- Uniform non-degeneracy floor at the center ν (paper's `μ_k not a zero of g₀`).
  obtain ⟨c_max₀, hc_max₀, m_floor, hm_floor, hfloor₀⟩ :=
    convFamily_center_nondegenerate_floor S ν hν
  -- Uniform sign-constant floor `m₀` on a window `Icc (ν-δ) (ν+δ)`, all `c ∈ [0,c_max₀]`.
  obtain ⟨δ, hδ, m₀, hm₀, hsign⟩ :=
    uniform_signConst_floor S ν hν c_max₀ hc_max₀ m_floor hm_floor hfloor₀
  -- Uniform sup |gα'| =: M over band×window.
  obtain ⟨M, hMnn, hM⟩ := uniform_sup_deriv S ν δ c_max₀ hδ hc_max₀
  -- `v ≪ β(v)` comparison with `K = M / m₀` (the region-c flank threshold).
  have hKnn : 0 ≤ M / m₀ := by positivity
  obtain ⟨vc, hvc_pos, _hvc_lt1, hvc⟩ := cmp_aux (M / m₀) hKnn
  -- `bandRadius v < δ` for small `v`.
  obtain ⟨vd, hvd_pos, hvd⟩ := bandRadius_lt_of_small (δ := δ) hδ
  refine ⟨c_max₀, hc_max₀, δ, hδ, min vc vd, lt_min hvc_pos hvd_pos, ?_⟩
  intro c hc0 hcmax v hv hvle
  have hvleC : v ≤ vc := le_trans hvle (min_le_left _ _)
  have hvleD : v ≤ vd := le_trans hvle (min_le_right _ _)
  -- This slice `gα = fFamU S c` is analytic & differentiable.
  have hg : AnalyticOnNhd ℝ (fun x => fFamU S c x) Set.univ := gFam_analytic S c hc0
  have hgd : Differentiable ℝ (fun x => fFamU S c x) :=
    fun x => (hg x (Set.mem_univ x)).differentiableAt
  set β : ℝ := bandRadius v with hβ
  have hβlt : β < δ := hvd v hv hvleD
  have hv1 : v < 1 := lt_of_le_of_lt hvleC _hvc_lt1
  have hβpos : 0 < β := bandRadius_pos hv hv1
  -- Key inequality `M·v < β·m₀`.
  have hMvβ : M * v < β * m₀ := by
    have hcmp := hvc v hv hvleC          -- (M/m₀)·v < β
    rw [div_mul_eq_mul_div, div_lt_iff₀ hm₀] at hcmp
    linarith [hcmp]
  -- The uniform sign-constant data for THIS slice on the window.
  have hsignc := hsign c hc0 hcmax
  -- `v·gα' x` is bounded by `±M·v` on the window.
  have hvderiv : ∀ x ∈ Set.Icc (ν - δ) (ν + δ),
      -(M * v) ≤ v * deriv (fun y => fFamU S c y) x
        ∧ v * deriv (fun y => fFamU S c y) x ≤ M * v := by
    intro x hx
    have habs : |deriv (fun y => fFamU S c y) x| ≤ M := hM c hc0 hcmax x hx
    have h1 : deriv (fun y => fFamU S c y) x ≤ M := le_of_abs_le habs
    have h2 : -M ≤ deriv (fun y => fFamU S c y) x := neg_le_of_abs_le habs
    constructor
    · have : -M * v ≤ deriv (fun y => fFamU S c y) x * v :=
        mul_le_mul_of_nonneg_right h2 (le_of_lt hv)
      nlinarith [this]
    · have : deriv (fun y => fFamU S c y) x * v ≤ M * v :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hv)
      nlinarith [this]
  -- ψ sign-definite on the RIGHT flank `Icc (ν+β) (ν+δ)`.
  have hψ_right :
      (∀ x ∈ Set.Icc (ν + β) (ν + δ),
          0 < v * deriv (fun y => fFamU S c y) x + (x - ν) * fFamU S c x)
        ∨ (∀ x ∈ Set.Icc (ν + β) (ν + δ),
          v * deriv (fun y => fFamU S c y) x + (x - ν) * fFamU S c x < 0) := by
    rcases hsignc with hpos | hneg
    · left
      intro x hx
      have hxw : x ∈ Set.Icc (ν - δ) (ν + δ) := ⟨by linarith [hx.1, hβpos], hx.2⟩
      have hgx : m₀ ≤ fFamU S c x := hpos x hxw
      have hxμ : β ≤ x - ν := by linarith [hx.1]
      have hprod : β * m₀ ≤ (x - ν) * fFamU S c x :=
        mul_le_mul hxμ hgx (le_of_lt hm₀) (by linarith [hβpos, hxμ])
      have hvd' := (hvderiv x hxw).1
      linarith [hprod, hvd', hMvβ]
    · right
      intro x hx
      have hxw : x ∈ Set.Icc (ν - δ) (ν + δ) := ⟨by linarith [hx.1, hβpos], hx.2⟩
      have hgx : fFamU S c x ≤ -m₀ := hneg x hxw
      have hxμ : β ≤ x - ν := by linarith [hx.1]
      have hxμpos : 0 < x - ν := by linarith [hβpos]
      have hprod : (x - ν) * fFamU S c x ≤ (x - ν) * (-m₀) :=
        mul_le_mul_of_nonneg_left hgx (le_of_lt hxμpos)
      have hbound : (x - ν) * (-m₀) ≤ β * (-m₀) := by nlinarith [hxμ, hm₀]
      have hvd' := (hvderiv x hxw).2
      nlinarith [hprod, hbound, hvd', hMvβ]
  -- ψ sign-definite on the LEFT flank `Icc (ν-δ) (ν-β)`.
  have hψ_left :
      (∀ x ∈ Set.Icc (ν - δ) (ν - β),
          0 < v * deriv (fun y => fFamU S c y) x + (x - ν) * fFamU S c x)
        ∨ (∀ x ∈ Set.Icc (ν - δ) (ν - β),
          v * deriv (fun y => fFamU S c y) x + (x - ν) * fFamU S c x < 0) := by
    rcases hsignc with hpos | hneg
    · right
      intro x hx
      have hxw : x ∈ Set.Icc (ν - δ) (ν + δ) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
      have hgx : m₀ ≤ fFamU S c x := hpos x hxw
      have hxμ : x - ν ≤ -β := by linarith [hx.2]
      have hxμneg : x - ν < 0 := by linarith [hβpos]
      have hprod : (x - ν) * fFamU S c x ≤ (x - ν) * m₀ :=
        mul_le_mul_of_nonpos_left hgx (le_of_lt hxμneg)
      have hbound : (x - ν) * m₀ ≤ -β * m₀ := by nlinarith [hxμ, hm₀]
      have hvd' := (hvderiv x hxw).2
      nlinarith [hprod, hbound, hvd', hMvβ]
    · left
      intro x hx
      have hxw : x ∈ Set.Icc (ν - δ) (ν + δ) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
      have hgx : fFamU S c x ≤ -m₀ := hneg x hxw
      have hxμ : x - ν ≤ -β := by linarith [hx.2]
      have hxμneg : x - ν < 0 := by linarith [hβpos]
      have hprod : (x - ν) * (-m₀) ≤ (x - ν) * fFamU S c x :=
        mul_le_mul_of_nonpos_left hgx (le_of_lt hxμneg)
      have hbound : β * m₀ ≤ (x - ν) * (-m₀) := by nlinarith [hxμ, hm₀]
      have hvd' := (hvderiv x hxw).1
      nlinarith [hprod, hbound, hvd', hMvβ]
  -- Each flank zero set is a subsingleton (the φ = h/N monotonicity engine).
  have hsubR := flank_subsingleton (fun x => fFamU S c x) hgd a_k ν v hv (ν + β) (ν + δ) hψ_right
  have hsubL := flank_subsingleton (fun x => fFamU S c x) hgd a_k ν v hv (ν - δ) (ν - β) hψ_left
  -- Cover the flank zero set by the two flanks and bound by 1 + 1.
  set ZR : Set ℝ := {x ∈ Set.Icc (ν + β) (ν + δ) |
      fFamU S c x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x = 0}
    with hZR
  set ZL : Set ℝ := {x ∈ Set.Icc (ν - δ) (ν - β) |
      fFamU S c x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x = 0}
    with hZL
  have hcover :
      {x ∈ Set.Ioo (ν - δ) (ν + δ) |
          (fFamU S c x +
              a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x = 0)
          ∧ bandRadius v ≤ |x - ν|} ⊆ ZR ∪ ZL := by
    intro x hx
    obtain ⟨hxIoo, hxz, hxβ⟩ := hx
    rw [← hβ] at hxβ
    rcases le_or_gt ν x with hle | hlt
    · left
      have : β ≤ x - ν := by rwa [abs_of_nonneg (by linarith)] at hxβ
      exact ⟨⟨by linarith, le_of_lt hxIoo.2⟩, hxz⟩
    · right
      rw [abs_of_neg (by linarith)] at hxβ
      have : β ≤ ν - x := by linarith [hxβ]
      exact ⟨⟨le_of_lt hxIoo.1, by linarith⟩, hxz⟩
  calc {x ∈ Set.Ioo (ν - δ) (ν + δ) |
          (fFamU S c x +
              a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x = 0)
          ∧ bandRadius v ≤ |x - ν|}.encard
      ≤ (ZR ∪ ZL).encard := Set.encard_le_encard hcover
    _ ≤ ZR.encard + ZL.encard := Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add (Set.encard_le_one_iff_subsingleton.mpr hsubR)
                            (Set.encard_le_one_iff_subsingleton.mpr hsubL)
    _ = 2 := by norm_num

/-! ## (Proven) uniform band non-vanishing

The uniform analogue of `bandZeroFree`: the band `(ν−β(v), ν+β(v))` is zero-free for
EVERY `c ∈ [0,c_max]` simultaneously, once `v ≤ v₀`.  Uses the uniform `Mg` sup-bound
(`uniform_sup_value`) in place of the per-`gα` `Mg`, fed to `bandEdgeValue_gt`. -/
theorem uniform_bandZeroFree
    (S : SignedGaussianCombination) (a_k : ℝ) (ha_k : a_k ≠ 0) (ν : ℝ)
    (c_max : ℝ) (hc_max : 0 < c_max) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v₀ : ℝ, 0 < v₀ ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
        ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
          bandRadius v < δ ∧
          (∀ x ∈ Set.Ioo (ν - bandRadius v) (ν + bandRadius v),
            fFamU S c x +
              a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x ≠ 0) := by
  -- uniform sup |fFamU S c x| =: Mg over band×window.
  obtain ⟨Mg, hMg_nn, hMg⟩ := uniform_sup_value S ν δ c_max hδ hc_max
  have hMpos : 0 ≤ Mg / |a_k| := by positivity
  obtain ⟨vB, hvB_pos, hvB_lt1, hvB⟩ := bandEdgeValue_gt hMpos
  obtain ⟨vδ, hvδ_pos, hvδ⟩ := bandRadius_lt_of_small (δ := δ) hδ
  refine ⟨min vB vδ, lt_min hvB_pos hvδ_pos, ?_⟩
  intro c hc0 hcmax v hv hvle
  have hvleB : v ≤ vB := le_trans hvle (min_le_left _ _)
  have hvleδ : v ≤ vδ := le_trans hvle (min_le_right _ _)
  have hv1 : v < 1 := lt_of_le_of_lt hvleB hvB_lt1
  have hβlt : bandRadius v < δ := hvδ v hv hvleδ
  refine ⟨hβlt, ?_⟩
  intro x hx
  show fFamU S c x +
      a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x ≠ 0
  have hxmem : x ∈ Set.Icc (ν - δ) (ν + δ) := by
    constructor <;> [linarith [hx.1, hβlt]; linarith [hx.2, hβlt]]
  have hgx : |fFamU S c x| ≤ Mg := hMg c hc0 hcmax x hxmem
  have hak_pos : 0 < |a_k| := abs_pos.mpr ha_k
  have hdens_ge := density_ge_on_band hv hv1 (μ_k := ν) (x := x) hx
  have hedge := hvB hv hvleB
  have hdens_gt : Mg / |a_k| <
      Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x :=
    lt_of_lt_of_le hedge hdens_ge
  have hdens_pos : 0 < Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x :=
    lt_of_le_of_lt hMpos hdens_gt
  have habsN : |a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x|
      = |a_k| * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x := by
    rw [abs_mul, abs_of_pos hdens_pos]
  have hgt : |fFamU S c x|
      < |a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x| := by
    rw [habsN]
    have hMgN : Mg < Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x * |a_k| :=
      (div_lt_iff₀ hak_pos).mp hdens_gt
    have : Mg < |a_k| * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x := by
      rw [mul_comm]; exact hMgN
    linarith [hgx]
  intro hzero
  have heq : a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x
      = - fFamU S c x := by linarith [hzero]
  rw [heq, abs_neg] at hgt
  exact (lt_irrefl (|fFamU S c x|)) hgt

/-! ## Band-uniform region (c): inner ≤2-zeros, the main result

Combine the uniform flank bound (`uniform_flank_zeros_le_two`) with uniform band
non-vanishing (`uniform_bandZeroFree`): every zero of `h = fFamU S c + a_k·N(ν,v)` in
the inner window lies in the flank region `{β(v) ≤ |x − ν|}`, of cardinality ≤ 2, for
all `c ∈ [0,c_max]` and all `v ≤ v0c`, with a SINGLE `(δ, v0c)`. -/
theorem convFamily_uniform_regionC
    (S : SignedGaussianCombination) (ν : ℝ) (hν : S.density ν ≠ 0)
    (a_k : ℝ) (ha_k : a_k ≠ 0) :
    ∃ c_max : ℝ, 0 < c_max ∧ ∃ v0c : ℝ, 0 < v0c ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ c : ℝ, 0 ≤ c → c ≤ c_max →
        ∀ (v : ℝ) (hv : 0 < v), v ≤ v0c →
          (Workspace.Types.ZeroCount.zeroSet
              (fun x => fFamU S c x +
                a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x)
            ∩ Set.Ioo (ν - δ) (ν + δ)).encard ≤ (2 : ℕ∞) := by
  obtain ⟨c_max, hc_max, δ, hδ, v₀f, hv₀f, hflank⟩ :=
    uniform_flank_zeros_le_two S ν hν a_k ha_k
  obtain ⟨v₀b, hv₀b, hband⟩ :=
    uniform_bandZeroFree S a_k ha_k ν c_max hc_max hδ
  refine ⟨c_max, hc_max, min v₀f v₀b, lt_min hv₀f hv₀b, δ, hδ, ?_⟩
  intro c hc0 hcmax v hv hvle
  have hvf : v ≤ v₀f := le_trans hvle (min_le_left _ _)
  have hvb : v ≤ v₀b := le_trans hvle (min_le_right _ _)
  set h : ℝ → ℝ := fun x =>
    fFamU S c x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x with hh
  obtain ⟨_hβlt, hmid⟩ := hband c hc0 hcmax v hv hvb
  -- Rewrite (zeroSet ∩ Ioo) into the set-builder form.
  have hset_eq :
      (Workspace.Types.ZeroCount.zeroSet h ∩ Set.Ioo (ν - δ) (ν + δ))
        = {x ∈ Set.Ioo (ν - δ) (ν + δ) | h x = 0} := by
    ext x
    simp only [Workspace.Types.ZeroCount.zeroSet_def, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_Ioo]
    tauto
  rw [hset_eq]
  -- Every window zero lies OUTSIDE the band (β ≤ |x − ν|).
  have hsub :
      {x ∈ Set.Ioo (ν - δ) (ν + δ) | h x = 0}
        ⊆ {x ∈ Set.Ioo (ν - δ) (ν + δ) |
            (fFamU S c x +
                a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x = 0)
            ∧ bandRadius v ≤ |x - ν|} := by
    intro x hx
    obtain ⟨hxIoo, hxz⟩ := hx
    refine ⟨hxIoo, hxz, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hxband : x ∈ Set.Ioo (ν - bandRadius v) (ν + bandRadius v) := by
      rw [Set.mem_Ioo]
      have := abs_lt.mp hlt
      constructor <;> [linarith [this.1]; linarith [this.2]]
    exact (hmid x hxband) hxz
  exact le_trans (Set.encard_le_encard hsub) (hflank c hc0 hcmax v hv hvf)

end Workspace.ProofLemmas
