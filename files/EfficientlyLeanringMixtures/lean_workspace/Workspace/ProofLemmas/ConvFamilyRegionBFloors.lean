import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope
import Workspace.ProofLemmas.ConvFamilyUniformRegionB

/-!
# Region-(b) FLOOR-BUNDLE producers for the convolution-width family

`convFamily_uniform_regionB` (and, downstream, `convFamily_uniform_diagonal_threshold`)
takes as hypotheses the region-(b) **floor bundle**: a uniform derivative floor
`ε₁_unif`, a uniform value floor `g_lb_unif`, a per-slice cover radius `ε₂fam`, and the
three per-slice facts (`hderiv_lb_fam`, `hε₁_unif_le`, `hg_lb_unif_spec`).  These were so
far threaded as *un-produced* hypotheses.

This file PRODUCES that bundle for the actual convolution base, starting from the §6.1
zero-enumeration substrate of `S = g̃₀'`:

* `S.density` has all-simple zeros, and `x₁ < ⋯ < x_r` enumerate ALL its zeros
  (`zeroCount S.density = r`);
* every band slice `gα(c) = fFamU S c` has `≤ r` zeros (Hummel–Gidas on the band).

The producers ASSEMBLE the already-proven uniform floors:

* `Workspace.ProofLemmas.branchDeriv_uniform_lower_bound` (per base zero) — a finite
  `min` over the `r` base zeros gives the uniform derivative floor `ε₁_unif`;
* `Workspace.ProofLemmas.convFamily_C0_floor_on_band` (uniform C⁰ floor on a supplied
  compact zero-free set) — fed the compact `Kbig` minus the `ε₂fam`-windows of the
  continuously-moving zeros — gives the uniform value floor `g_lb_unif`.

The bridge between "base zeros" and "slice zeros" is the **count-pinch**: for `c` small
the slice's zeros are exactly the IFT-branch images `{φ_j c}` of the base zeros (the
finite-set antisymmetry `Set.Finite.eq_of_subset_of_encard_le`, exactly as in
`convSmall_all_zeros_simple`).

The output `convFamily_regionB_floor_bundle` packages everything in EXACTLY the
hypothesis shape `convFamily_uniform_regionB` consumes, so that the latter applies
directly to the produced floors.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.ZeroCount

set_option maxHeartbeats 4000000

/-! ## Joint continuity of the `x`-derivative (verbatim mirror of the private originals)

`fFamU_value_contOn` / `fFamU_deriv_contOn` are `private` in
`ConvSmallPreservesSimpleAndEnvelope`; we re-derive them here with a `'` suffix
(short, copying the originals exactly) because the cover/floor construction needs the
JOINT continuity `(c,x) ↦ deriv (fFamU S c) x` rather than the per-`x₀` slice version. -/

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

private theorem fFamU_hasDerivAt' (S : SignedGaussianCombination) (c x : ℝ) :
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

private theorem fFamU_deriv_eq_sum' (S : SignedGaussianCombination) (c x : ℝ) :
    deriv (fun y => fFamU S c y) x = ∑ i : Fin S.components.length, termDerivU S c x i :=
  (fFamU_hasDerivAt' S c x).deriv

private theorem termDerivU_contOn' (S : SignedGaussianCombination) (i : Fin S.components.length) :
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

private theorem fFamU_deriv_contOn' (S : SignedGaussianCombination) :
    ContinuousOn (fun p : ℝ × ℝ => deriv (fun y => fFamU S p.1 y) p.2)
      (goodSetU S ×ˢ (Set.univ : Set ℝ)) := by
  have heq : Set.EqOn (fun p : ℝ × ℝ => deriv (fun y => fFamU S p.1 y) p.2)
      (fun p : ℝ × ℝ => ∑ i : Fin S.components.length, termDerivU S p.1 p.2 i)
      (goodSetU S ×ˢ (Set.univ : Set ℝ)) := fun p _ => fFamU_deriv_eq_sum' S p.1 p.2
  apply ContinuousOn.congr _ heq
  apply continuousOn_finset_sum
  intro i _
  exact termDerivU_contOn' S i

/-! ## The count-pinch substrate: slice zeros = branch images, on a small band

We run the per-base-zero IFT branch construction once (via
`branchDeriv_uniform_lower_bound`, which also bundles the uniform derivative floor) and
choose a band `[0, c_maxB]` small enough that:

* every branch is defined (`c < δf j`) and the branch images stay within `ε₀` of their
  base zero (`ε₀` = half the minimal base-zero separation), so the `r` images are
  distinct;
* the uniform derivative floor clause holds (`c < αd j`).

On that band, given `zeroCount (fFamU S c) ≤ r` (Hummel–Gidas), the finite-set
antisymmetry forces `zeroSet (fFamU S c) = range (fun j => φ j c)`, exposing the slice's
zeros as the branch images — the bridge every floor needs. -/

/-- **Region-(b) floor-bundle producer for the convolution-width family.**

From the §6.1 zero-enumeration substrate of `S = g̃₀'` — all-simple zeros, the complete
enumeration `x : Fin r → ℝ` of `S.density`'s zeros, and the band Hummel–Gidas `≤ r`-zero
bound — this lemma produces, for any window radius `δ > 0` and band edges `b < b'`, the
EXACT region-(b) floor bundle that `convFamily_uniform_regionB` consumes:

* a band `[0, c_maxB]` (with `c_maxB > 0`);
* the uniform derivative floor `ε₁_unif > 0` and value floor `g_lb_unif > 0`;
* the per-slice cover radius `ε₂fam : ℝ → ℝ` (constant on the band, `≤ δ/8`, `≤ 1`);
* the three per-slice facts `hderiv_lb_fam`, `hε₁_unif_le`, `hg_lb_unif_spec`.

`ε₁_unif` is `(min_j |deriv (fFamU S 0) (x_j)|) / 2`, assembled over the `r` base zeros
from `branchDeriv_uniform_lower_bound`; `g_lb_unif` comes from
`convFamily_C0_floor_on_band` on `Kbig` minus the `ε₂fam`-windows of the (moving) zeros. -/
theorem convFamily_regionB_floor_bundle
    (S : SignedGaussianCombination)
    (hsimple0 : ∀ x, S.density x = 0 → deriv S.density x ≠ 0)
    (r : ℕ) (x : Fin r → ℝ) (hx_mono : StrictMono x)
    (hx_zero : ∀ j, S.density (x j) = 0)
    (hx_all : zeroCount S.density = (r : ℕ∞))
    (μ_k : ℝ) (b b' : ℝ) (δ : ℝ) (hδ : 0 < δ)
    -- band Hummel–Gidas on a fixed reference band `c_max_HG`: each slice has `≤ r` zeros.
    (c_max_HG : ℝ) (hc_max_HG : 0 < c_max_HG)
    (hgα_zeros : ∀ c : ℝ, 0 ≤ c → c ≤ c_max_HG →
      zeroCount (fun y => fFamU S c y) ≤ (r : ℕ∞)) :
    ∃ c_maxB : ℝ, 0 < c_maxB ∧ c_maxB ≤ c_max_HG ∧
    ∃ ε₁_unif : ℝ, 0 < ε₁_unif ∧
    ∃ g_lb_unif : ℝ, 0 < g_lb_unif ∧
    ∃ ε₂fam : ℝ → ℝ,
      (∀ c : ℝ, 0 ≤ c → c ≤ c_maxB → 0 < ε₂fam c) ∧
      (∀ c : ℝ, 0 ≤ c → c ≤ c_maxB → ε₂fam c ≤ δ/8) ∧
      (∀ c : ℝ, 0 ≤ c → c ≤ c_maxB → ε₂fam c ≤ 1) ∧
      (∀ c : ℝ, 0 ≤ c → c ≤ c_maxB →
        ∀ x_j : ℝ, fFamU S c x_j = 0 →
          ∀ y ∈ Set.Icc (x_j - ε₂fam c) (x_j + ε₂fam c),
            |deriv (fun z => fFamU S c z) x_j| / 2 ≤ |deriv (fun z => fFamU S c z) y|) ∧
      (∀ c : ℝ, 0 ≤ c → c ≤ c_maxB →
        ∀ x_j : ℝ, fFamU S c x_j = 0 → ε₁_unif ≤ |deriv (fun z => fFamU S c z) x_j|) ∧
      (∀ c : ℝ, 0 ≤ c → c ≤ c_maxB →
        ∀ y ∈ (Set.Icc b b' \ Set.Ioo (μ_k - δ) (μ_k + δ)) \
            (⋃ x_j ∈ {z : ℝ | fFamU S c z = 0}, Set.Ioo (x_j - ε₂fam c) (x_j + ε₂fam c)),
          g_lb_unif ≤ |fFamU S c y|) := by
  classical
  -- ===== Per-base-zero IFT branches with the uniform derivative floor. =====
  have hf0_zero : ∀ j : Fin r, fFamU S 0 (x j) = 0 := by
    intro j; rw [fFamU_zero]; exact hx_zero j
  have hD0_ne : ∀ j : Fin r, deriv (fun y => fFamU S 0 y) (x j) ≠ 0 := by
    intro j; rw [fFamU_zero_fun]; exact hsimple0 (x j) (hx_zero j)
  have hbranch : ∀ j : Fin r, ∃ δb : ℝ, 0 < δb ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δb) δb) ∧ φ 0 = x j ∧
      (∀ c : ℝ, |c| < δb → fFamU S c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δb → deriv (fun y => fFamU S c y) (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δb → ∀ y : ℝ,
        fFamU S c y = 0 → |y - x j| < ε → y = φ c) ∧
      (∃ αd : ℝ, 0 < αd ∧ αd ≤ δb ∧
        ∀ c : ℝ, 0 ≤ c → c < αd →
          |deriv (fun y => fFamU S 0 y) (x j)| / 2
            ≤ |deriv (fun y => fFamU S c y) (φ c)|) :=
    fun j => branchDeriv_uniform_lower_bound S (x j) (hf0_zero j) (hD0_ne j)
  choose δf hδf_pos φ hφ_contOn hφ0 hφ_zero hφ_deriv hφ_uniqEx hφ_floorEx using hbranch
  -- Separation radius `ε₀` between distinct base zeros.
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
      have hxne : x p.1 ≠ x p.2 := fun h => hp.2 (hx_mono.injective h)
      have hpos : 0 < |x p.1 - x p.2| := abs_pos.mpr (sub_ne_zero.mpr hxne)
      linarith
    · norm_num
  have hε₀_sep : ∀ i j : Fin r, i ≠ j → ε₀ ≤ |x i - x j| / 2 := by
    intro i j hij
    have hmem : (i, j) ∈ pairs := by
      rw [hpairs_def, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hij⟩
    rw [hε₀_def, dif_pos ⟨(i, j), hmem⟩]; exact Finset.inf'_le _ hmem
  -- Uniform derivative floor: `ε₁_unif := (min_j |deriv (fFamU S 0) (x_j)|) / 2`.
  set Lmin : ℝ :=
    if hne : (Finset.univ : Finset (Fin r)).Nonempty then
      (Finset.univ : Finset (Fin r)).inf' hne (fun j => |deriv (fun y => fFamU S 0 y) (x j)|)
    else 1 with hLmin_def
  have hLmin_pos : 0 < Lmin := by
    rw [hLmin_def]
    split
    · rename_i hne; rw [Finset.lt_inf'_iff]; intro j _; exact abs_pos.mpr (hD0_ne j)
    · norm_num
  have hLmin_le : ∀ j : Fin r, Lmin ≤ |deriv (fun y => fFamU S 0 y) (x j)| := by
    intro j
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j, Finset.mem_univ _⟩
    rw [hLmin_def, dif_pos hne]; exact Finset.inf'_le _ (Finset.mem_univ j)
  set ε₁_unif : ℝ := Lmin / 2 with hε₁_def
  have hε₁_pos : 0 < ε₁_unif := by rw [hε₁_def]; linarith
  -- ===== Uniform-continuity cover radius for the derivative. =====
  -- On the compact `W := Icc 0 c_max_HG ×ˢ Wx`, where `Wx := ⋃_k Icc(x_k - 2, x_k + 2)`,
  -- the jointly-continuous derivative `(c,y) ↦ deriv (fFamU S c) y` is uniformly
  -- continuous.  Pick `ρ_cov > 0` so the deriv oscillation over any `ρ_cov`-window is
  -- `< ε₁_unif/2`.  Folding `ρ_cov` into `ε₂` makes `hderiv_lb_fam` hold on the fixed
  -- window: `|deriv y| ≥ |deriv x_j| − ε₁_unif/2 ≥ |deriv x_j| − |deriv x_j|/2`.
  set Wx : Set ℝ := ⋃ k : Fin r, Set.Icc (x k - 2) (x k + 2) with hWx_def
  have hWx_compact : IsCompact Wx := by
    rw [hWx_def]; exact isCompact_iUnion (fun k => isCompact_Icc)
  set Wprod : Set (ℝ × ℝ) := Set.Icc 0 c_max_HG ×ˢ Wx with hWprod_def
  have hWprod_compact : IsCompact Wprod := (isCompact_Icc).prod hWx_compact
  have hWprod_sub : Wprod ⊆ goodSetU S ×ˢ (Set.univ : Set ℝ) := by
    rintro ⟨c, y⟩ ⟨hc, _hy⟩
    exact ⟨goodSetU_of_nonneg S hc.1, Set.mem_univ _⟩
  have hderiv_contOnW : ContinuousOn (fun p : ℝ × ℝ => deriv (fun z => fFamU S p.1 z) p.2) Wprod :=
    (fFamU_deriv_contOn' S).mono hWprod_sub
  have hUC : UniformContinuousOn (fun p : ℝ × ℝ => deriv (fun z => fFamU S p.1 z) p.2) Wprod :=
    hWprod_compact.uniformContinuousOn_of_continuous hderiv_contOnW
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨ρ_cov0, hρ_cov0_pos, hρ_cov0⟩ := hUC (ε₁_unif / 2) (by linarith)
  set ρ_cov : ℝ := min ρ_cov0 1 with hρ_cov_def
  have hρ_cov_pos : 0 < ρ_cov := lt_min hρ_cov0_pos one_pos
  have hρ_cov_le0 : ρ_cov ≤ ρ_cov0 := min_le_left _ _
  -- The constant cover radius and the base-window radius.
  -- Slice windows have radius `ε₂ := min (δ/8) (min 1 (min (ε₀/2) (ρ_cov/2)))`;
  -- base windows `ε₂/2`.  `ε₂ ≤ ρ_cov/2 ≤ 1/2` ensures the deriv-oscillation control.
  set ε₂ : ℝ := min (δ/8) (min 1 (min (ε₀/2) (ρ_cov/2))) with hε₂_def
  have hε₂_pos : 0 < ε₂ := by
    rw [hε₂_def]
    exact lt_min (by linarith) (lt_min one_pos (lt_min (by linarith) (by linarith)))
  have hε₂_le_δ8 : ε₂ ≤ δ/8 := by rw [hε₂_def]; exact min_le_left _ _
  have hε₂_le_1 : ε₂ ≤ 1 := le_trans (by rw [hε₂_def]; exact min_le_right _ _) (min_le_left _ _)
  have hε₂_le_ε₀2 : ε₂ ≤ ε₀/2 :=
    le_trans (by rw [hε₂_def]; exact min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₂_le_ρcov2 : ε₂ ≤ ρ_cov/2 :=
    le_trans (by rw [hε₂_def]; exact min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  -- Destructure the per-branch uniqueness radius and the deriv-floor radius.
  choose εu hεu_pos hεu_uniq using hφ_uniqEx
  choose αd hαd_pos hαd_le hαd_floor using hφ_floorEx
  -- Closeness radii: `0 ≤ c < ρ j ⟹ |φ j c - x j| < min (ε₂/2) (εu j)` (so the moving
  -- zero stays inside the base window AND within the branch's own uniqueness radius).
  have hclose : ∀ j : Fin r, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ δf j ∧
      ∀ c : ℝ, 0 ≤ c → c < ρ → |φ j c - x j| < min (ε₂/2) (εu j) := by
    intro j
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-(δf j)) (δf j) := ⟨by linarith [hδf_pos j], hδf_pos j⟩
    have hcontAt : ContinuousWithinAt (φ j) (Set.Ioo (-(δf j)) (δf j)) 0 := (hφ_contOn j) 0 h0mem
    have htend : Filter.Tendsto (φ j) (nhdsWithin 0 (Set.Ioo (-(δf j)) (δf j))) (nhds (x j)) := by
      have := hcontAt; rw [ContinuousWithinAt, hφ0 j] at this; exact this
    set εtgt : ℝ := min (ε₂/2) (εu j) with hεtgt_def
    have hεtgt_pos : 0 < εtgt := lt_min (by linarith) (hεu_pos j)
    have hball : {y : ℝ | |y - x j| < εtgt} ∈ nhds (x j) := by
      have : Metric.ball (x j) εtgt ∈ nhds (x j) := Metric.ball_mem_nhds _ hεtgt_pos
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
    have := hU_sub ⟨hc_U, hc_Ioo⟩; simpa using this
  choose ρ hρ_pos hρ_le hρ_close using hclose
  -- The produced band edge: STRICTLY below every `ρ j`, every `αd j`, and ≤ the HG band.
  -- Halving the inner inf' guarantees strict inequalities on the CLOSED band `[0, c_maxB]`.
  set innerInf : ℝ :=
    if hne : (Finset.univ : Finset (Fin r)).Nonempty then
      (Finset.univ : Finset (Fin r)).inf' hne (fun j => min (ρ j) (αd j))
    else 1 with hinner_def
  have hinner_pos : 0 < innerInf := by
    rw [hinner_def]; split
    · rename_i hne; rw [Finset.lt_inf'_iff]; intro j _; exact lt_min (hρ_pos j) (hαd_pos j)
    · norm_num
  have hinner_le : ∀ j : Fin r, innerInf ≤ min (ρ j) (αd j) := by
    intro j
    have hne : (Finset.univ : Finset (Fin r)).Nonempty := ⟨j, Finset.mem_univ _⟩
    rw [hinner_def, dif_pos hne]; exact Finset.inf'_le _ (Finset.mem_univ j)
  set c_maxB : ℝ := min c_max_HG (innerInf / 2) with hcmaxB_def
  have hcmaxB_pos : 0 < c_maxB := lt_min hc_max_HG (by linarith)
  have hcmaxB_le_HG : c_maxB ≤ c_max_HG := min_le_left _ _
  have hcmaxB_lt_ρ : ∀ j : Fin r, c_maxB < ρ j := by
    intro j
    have h1 : c_maxB ≤ innerInf / 2 := min_le_right _ _
    have h2 : innerInf ≤ ρ j := le_trans (hinner_le j) (min_le_left _ _)
    linarith
  have hcmaxB_lt_αd : ∀ j : Fin r, c_maxB < αd j := by
    intro j
    have h1 : c_maxB ≤ innerInf / 2 := min_le_right _ _
    have h2 : innerInf ≤ αd j := le_trans (hinner_le j) (min_le_right _ _)
    linarith
  -- Convenience: for `c` in the produced band and any `j`, `|c| < δf j`, and the strict
  -- closeness `|φ j c - x j| < min (ε₂/2) (εu j)` holds.
  have hc_lt_ρ : ∀ (c : ℝ), c ≤ c_maxB → ∀ j : Fin r, c < ρ j :=
    fun c hcle j => lt_of_le_of_lt hcle (hcmaxB_lt_ρ j)
  have hc_lt_αd : ∀ (c : ℝ), c ≤ c_maxB → ∀ j : Fin r, c < αd j :=
    fun c hcle j => lt_of_le_of_lt hcle (hcmaxB_lt_αd j)
  have hc_lt_δf : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB → ∀ j : Fin r, |c| < δf j := by
    intro c hc0 hcle j
    rw [abs_of_nonneg hc0]
    exact lt_of_lt_of_le (hc_lt_ρ c hcle j) (hρ_le j)
  have hclose_band : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB → ∀ j : Fin r,
      |φ j c - x j| < min (ε₂/2) (εu j) :=
    fun c hc0 hcle j => hρ_close j c hc0 (hc_lt_ρ c hcle j)
  -- Closeness in each handy form.
  have hclose_ε2 : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB → ∀ j : Fin r, |φ j c - x j| < ε₂/2 :=
    fun c hc0 hcle j => lt_of_lt_of_le (hclose_band c hc0 hcle j) (min_le_left _ _)
  have hclose_εu : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB → ∀ j : Fin r, |φ j c - x j| < εu j :=
    fun c hc0 hcle j => lt_of_lt_of_le (hclose_band c hc0 hcle j) (min_le_right _ _)
  -- ===== Per-`c` pinch: slice zeros = branch images. =====
  -- The branch images are slice zeros.
  have hz_zero : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB → ∀ j : Fin r, fFamU S c (φ j c) = 0 :=
    fun c hc0 hcle j => hφ_zero j c (hc_lt_δf c hc0 hcle j)
  -- The branch-image map is injective (disjoint base-zero windows).
  have hz_inj : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB →
      Function.Injective (fun j : Fin r => φ j c) := by
    intro c hc0 hcle i j hij
    by_contra hne
    have heq : φ i c = φ j c := hij
    have hsep : ε₀ ≤ |x i - x j| / 2 := hε₀_sep i j hne
    have hci : |φ i c - x i| < ε₂/2 := hclose_ε2 c hc0 hcle i
    have hcj : |φ j c - x j| < ε₂/2 := hclose_ε2 c hc0 hcle j
    have h1 : |x i - x j| ≤ |x i - φ i c| + |φ i c - x j| := abs_sub_le _ _ _
    have h2 : |φ i c - x j| ≤ |φ i c - φ j c| + |φ j c - x j| := abs_sub_le _ _ _
    have h3 : |φ i c - φ j c| = 0 := by rw [heq]; simp
    have h4 : |x i - φ i c| = |φ i c - x i| := abs_sub_comm _ _
    rw [h4] at h1
    have hbound : |x i - x j| < ε₂ := by
      calc |x i - x j| ≤ |φ i c - x i| + |φ i c - x j| := h1
        _ ≤ |φ i c - x i| + (|φ i c - φ j c| + |φ j c - x j|) := by linarith [h2]
        _ = |φ i c - x i| + |φ j c - x j| := by rw [h3]; ring
        _ < ε₂/2 + ε₂/2 := by linarith [hci, hcj]
        _ = ε₂ := by ring
    -- but `ε₂ ≤ ε₀/2 ≤ |x i - x j|`, contradiction.
    have : ε₂ ≤ |x i - x j| := le_trans hε₂_le_ε₀2 (by linarith [hsep])
    linarith
  -- The image set has encard `r`.
  have hrange_card : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB →
      (Set.range (fun j : Fin r => φ j c)).encard = (r : ℕ∞) := by
    intro c hc0 hcle
    rw [← Set.image_univ, Set.InjOn.encard_image ((hz_inj c hc0 hcle).injOn),
      Set.encard_univ]; simp
  -- range ⊆ zeroSet.
  have hrange_sub : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB →
      Set.range (fun j : Fin r => φ j c) ⊆ zeroSet (fun y => fFamU S c y) := by
    intro c hc0 hcle y hy
    obtain ⟨j, hj⟩ := hy
    rw [zeroSet_def, Set.mem_setOf_eq, ← hj]; exact hz_zero c hc0 hcle j
  -- Antisymmetry: range = zeroSet.
  have hpinch : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB →
      zeroSet (fun y => fFamU S c y) = Set.range (fun j : Fin r => φ j c) := by
    intro c hc0 hcle
    have hle : (zeroSet (fun y => fFamU S c y)).encard
        ≤ (Set.range (fun j : Fin r => φ j c)).encard := by
      rw [hrange_card c hc0 hcle, ← zeroCount_def]
      exact hgα_zeros c hc0 (le_trans hcle hcmaxB_le_HG)
    exact (Set.Finite.eq_of_subset_of_encard_le (Set.finite_range _)
      (hrange_sub c hc0 hcle) hle).symm
  -- Membership form: every slice zero equals some branch image.
  have hzero_branch : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB → ∀ y : ℝ,
      fFamU S c y = 0 → ∃ j : Fin r, y = φ j c := by
    intro c hc0 hcle y hy
    have hy_mem : y ∈ zeroSet (fun y => fFamU S c y) := by
      rw [zeroSet_def, Set.mem_setOf_eq]; exact hy
    rw [hpinch c hc0 hcle] at hy_mem
    obtain ⟨j, hj⟩ := hy_mem; exact ⟨j, hj.symm⟩
  -- ===== Uniform derivative floor at the zeros (`hε₁_unif_le`). =====
  have hε₁_unif_le : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB →
      ∀ x_j : ℝ, fFamU S c x_j = 0 → ε₁_unif ≤ |deriv (fun z => fFamU S c z) x_j| := by
    intro c hc0 hcle x_j hx_j
    obtain ⟨k, hk⟩ := hzero_branch c hc0 hcle x_j hx_j
    -- deriv floor at the branch image, using `c < αd k`.
    have hfloor := hαd_floor k c hc0 (hc_lt_αd c hcle k)
    -- `ε₁_unif = Lmin/2 ≤ |deriv (fFamU S 0)(x_k)|/2 ≤ |deriv(fFamU S c)(φ k c)|`.
    have hL : Lmin ≤ |deriv (fun y => fFamU S 0 y) (x k)| := hLmin_le k
    calc ε₁_unif = Lmin / 2 := hε₁_def
      _ ≤ |deriv (fun y => fFamU S 0 y) (x k)| / 2 := by linarith
      _ ≤ |deriv (fun y => fFamU S c y) (φ k c)| := hfloor
      _ = |deriv (fun z => fFamU S c z) x_j| := by rw [hk]
  -- ===== Per-slice derivative-decay on the cover window (`hderiv_lb_fam`). =====
  -- `ε₂ ≤ ρ_cov/2` ⟹ the deriv oscillation over `Icc(x_j ± ε₂)` is `< ε₁_unif/2`, and
  -- `ε₁_unif ≤ |deriv x_j|` ⟹ `|deriv y| ≥ |deriv x_j| − |deriv x_j|/2 = |deriv x_j|/2`.
  have hderiv_lb_fam : ∀ (c : ℝ), 0 ≤ c → c ≤ c_maxB →
      ∀ x_j : ℝ, fFamU S c x_j = 0 →
        ∀ y ∈ Set.Icc (x_j - ε₂) (x_j + ε₂),
          |deriv (fun z => fFamU S c z) x_j| / 2 ≤ |deriv (fun z => fFamU S c z) y| := by
    intro c hc0 hcle x_j hx_j y hy
    -- `x_j = φ k c` is near a base zero `x k`.
    obtain ⟨k, hk⟩ := hzero_branch c hc0 hcle x_j hx_j
    have hxjk : |x_j - x k| < ε₂/2 := by rw [hk]; exact hclose_ε2 c hc0 hcle k
    -- membership of `(c, x_j)` and `(c, y)` in `Wprod`.
    have hc_HG : c ≤ c_max_HG := le_trans hcle hcmaxB_le_HG
    have hxj_Wx : x_j ∈ Wx := by
      rw [hWx_def, Set.mem_iUnion]; refine ⟨k, ?_⟩
      rw [Set.mem_Icc]; rw [abs_lt] at hxjk
      constructor <;> [linarith [hxjk.1, hε₂_le_1]; linarith [hxjk.2, hε₂_le_1]]
    have hyxj : |y - x_j| ≤ ε₂ := by
      rw [Set.mem_Icc] at hy; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
    have hy_Wx : y ∈ Wx := by
      rw [hWx_def, Set.mem_iUnion]; refine ⟨k, ?_⟩
      -- `|y - x k| ≤ |y - x_j| + |x_j - x k| < ε₂ + ε₂/2 ≤ 3/2 < 2`.
      have htri : |y - x k| ≤ |y - x_j| + |x_j - x k| := abs_sub_le _ _ _
      have hbnd : |y - x k| < 2 := by
        have : |y - x k| < ε₂ + ε₂/2 := by linarith [htri, hyxj, hxjk]
        have : |y - x k| < 3/2 := by linarith [this, hε₂_le_1]
        linarith
      rw [Set.mem_Icc]; rw [abs_lt] at hbnd; constructor <;> linarith [hbnd.1, hbnd.2]
    have hxj_mem : ((c, x_j) : ℝ × ℝ) ∈ Wprod := ⟨⟨hc0, hc_HG⟩, hxj_Wx⟩
    have hy_mem : ((c, y) : ℝ × ℝ) ∈ Wprod := ⟨⟨hc0, hc_HG⟩, hy_Wx⟩
    -- distance bound: `dist (c,y) (c,x_j) = |y - x_j| ≤ ε₂ ≤ ρ_cov/2 < ρ_cov0`.
    have hdist : dist ((c, y) : ℝ × ℝ) ((c, x_j) : ℝ × ℝ) < ρ_cov0 := by
      rw [Prod.dist_eq]
      have hdyxj : dist y x_j ≤ ε₂ := by rw [Real.dist_eq]; exact hyxj
      have hmaxeq : max (dist c c) (dist y x_j) = dist y x_j := by
        rw [dist_self]; exact max_eq_right dist_nonneg
      rw [hmaxeq]
      have : dist y x_j ≤ ρ_cov / 2 := le_trans hdyxj hε₂_le_ρcov2
      have : dist y x_j ≤ ρ_cov0 / 2 := le_trans this (by linarith [hρ_cov_le0])
      linarith [hρ_cov0_pos]
    -- oscillation `< ε₁_unif/2`.
    have hosc := hρ_cov0 ((c, y)) hy_mem ((c, x_j)) hxj_mem hdist
    rw [Real.dist_eq] at hosc
    -- `ε₁_unif ≤ |deriv x_j|`.
    have hflr : ε₁_unif ≤ |deriv (fun z => fFamU S c z) x_j| := hε₁_unif_le c hc0 hcle x_j hx_j
    -- assemble.
    have hrev : |deriv (fun z => fFamU S c z) x_j| - |deriv (fun z => fFamU S c z) y|
        ≤ |deriv (fun z => fFamU S c z) y - deriv (fun z => fFamU S c z) x_j| := by
      rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
    linarith [hrev, hosc, hflr]
  -- ===== Uniform value floor on the fixed zero-free compact `A`. =====
  -- `Kbig` is the c-independent outer region of region (b).
  set Kbig : Set ℝ := Set.Icc (b - δ) (b' + δ) \ Set.Ioo (μ_k - δ/2) (μ_k + δ/2) with hKbig_def
  -- The fixed zero-free compact: `Kbig` minus the (c-independent) base-zero windows.
  set baseWin : Set ℝ := ⋃ j : Fin r, Set.Ioo (x j - ε₂/2) (x j + ε₂/2) with hbaseWin_def
  have hbaseWin_open : IsOpen baseWin := by
    rw [hbaseWin_def]; exact isOpen_iUnion (fun j => isOpen_Ioo)
  set A : Set ℝ := Kbig \ baseWin with hA_def
  have hKbig_compact : IsCompact Kbig := (isCompact_Icc).diff isOpen_Ioo
  have hA_compact : IsCompact A := hKbig_compact.diff hbaseWin_open
  -- `A` is uniformly zero-free across the band.
  have hA_zero_free : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB → ∀ y ∈ A, fFamU S c y ≠ 0 := by
    intro c hc0 hcle y hy hzero
    obtain ⟨k, hk⟩ := hzero_branch c hc0 hcle y hzero
    -- `|y - x k| = |φ k c - x k| < ε₂/2`, so `y ∈ baseWin`, contradicting `y ∈ A`.
    have hclose_k : |y - x k| < ε₂/2 := by rw [hk]; exact hclose_ε2 c hc0 hcle k
    have hyWin : y ∈ baseWin := by
      rw [hbaseWin_def, Set.mem_iUnion]
      refine ⟨k, ?_⟩
      rw [Set.mem_Ioo]; rw [abs_lt] at hclose_k; constructor <;> linarith [hclose_k.1, hclose_k.2]
    exact hy.2 hyWin
  -- `A` is nonempty: the right edge `b' + δ` lies in `A` if no base zero is within `ε₂/2`
  -- of it; we use the band-edge point and remove via... but nonemptiness can fail if a
  -- base zero is exactly there.  We instead provide nonemptiness through the convFamily
  -- floor lemma's robustness: if `A = ∅` the floor is vacuous, so we case-split.
  by_cases hA_ne : A.Nonempty
  · -- Nonempty `A`: get a genuine uniform value floor.
    obtain ⟨g_lb_unif, hg_lb_pos, hg_lb_spec⟩ :=
      convFamily_C0_floor_on_band S c_maxB hcmaxB_pos A hA_compact hA_ne hA_zero_free
    refine ⟨c_maxB, hcmaxB_pos, hcmaxB_le_HG, ε₁_unif, hε₁_pos, g_lb_unif, hg_lb_pos,
      (fun _ => ε₂), ?_, ?_, ?_, ?_, hε₁_unif_le, ?_⟩
    · intro c _ _; exact hε₂_pos
    · intro c _ _; exact hε₂_le_δ8
    · intro c _ _; exact hε₂_le_1
    · -- hderiv_lb_fam
      intro c hc0 hcle x_j hx_j y hy
      exact hderiv_lb_fam c hc0 hcle x_j hx_j y hy
    · -- hg_lb_unif_spec: reduce the per-c set to membership in `A`.
      intro c hc0 hcle y hy
      apply hg_lb_spec c hc0 hcle y
      -- `y ∈ A`, i.e. `y ∈ Kbig` and `y ∉ baseWin`.
      obtain ⟨⟨hy_in, hy_out⟩, hy_notslice⟩ := hy
      rw [hA_def, Set.mem_diff]
      constructor
      · -- `y ∈ Kbig`: `Icc b b' \ Ioo(μ±δ) ⊆ Kbig = Icc(b-δ)(b'+δ) \ Ioo(μ±δ/2)`.
        rw [hKbig_def, Set.mem_diff]
        rw [Set.mem_Icc] at hy_in
        constructor
        · rw [Set.mem_Icc]; constructor <;> linarith [hy_in.1, hy_in.2]
        · -- not in `Ioo(μ±δ/2)`: it is not even in `Ioo(μ±δ)`.
          intro hc'
          rw [Set.mem_Ioo] at hc'
          exact hy_out (by rw [Set.mem_Ioo]; constructor <;> linarith [hc'.1, hc'.2])
      · -- `y ∉ baseWin`: if `y ∈ Ioo(x_k ± ε₂/2)` then `y` is within `ε₂` of the slice
        -- zero `φ k c`, so `y ∈ Ioo(φ k c ± ε₂)` ⊆ the removed slice union — contradiction.
        intro hyWin
        rw [hbaseWin_def, Set.mem_iUnion] at hyWin
        obtain ⟨k, hyk⟩ := hyWin
        rw [Set.mem_Ioo] at hyk
        -- `|y - x k| < ε₂/2` and `|φ k c - x k| < ε₂/2`, so `|y - φ k c| < ε₂`.
        have hyxk : |y - x k| < ε₂/2 := by rw [abs_lt]; constructor <;> linarith [hyk.1, hyk.2]
        have hφxk : |φ k c - x k| < ε₂/2 := hclose_ε2 c hc0 hcle k
        have hyφ : |y - φ k c| < ε₂ := by
          have : |y - φ k c| ≤ |y - x k| + |x k - φ k c| := abs_sub_le _ _ _
          rw [abs_sub_comm (x k) (φ k c)] at this
          linarith [hyxk, hφxk]
        -- `φ k c` is a slice zero, so its window is one of the removed sets.
        apply hy_notslice
        rw [Set.mem_iUnion₂]
        refine ⟨φ k c, ?_, ?_⟩
        · rw [Set.mem_setOf_eq]; exact hz_zero c hc0 hcle k
        · rw [Set.mem_Ioo]; rw [abs_lt] at hyφ; constructor <;> linarith [hyφ.1, hyφ.2]
  · -- Empty `A`: the value-floor predicate is vacuous; pick `g_lb_unif = 1`.
    rw [Set.not_nonempty_iff_eq_empty] at hA_ne
    refine ⟨c_maxB, hcmaxB_pos, hcmaxB_le_HG, ε₁_unif, hε₁_pos, 1, one_pos,
      (fun _ => ε₂), ?_, ?_, ?_, ?_, hε₁_unif_le, ?_⟩
    · intro c _ _; exact hε₂_pos
    · intro c _ _; exact hε₂_le_δ8
    · intro c _ _; exact hε₂_le_1
    · intro c hc0 hcle x_j hx_j y hy
      exact hderiv_lb_fam c hc0 hcle x_j hx_j y hy
    · -- value floor: the per-c set is contained in `A = ∅`, so it is empty ⟹ vacuous.
      intro c hc0 hcle y hy
      exfalso
      -- mirror the `y ∈ A` derivation; then `A = ∅` gives a contradiction.
      obtain ⟨⟨hy_in, hy_out⟩, hy_notslice⟩ := hy
      have hyA : y ∈ A := by
        rw [hA_def, Set.mem_diff]
        refine ⟨?_, ?_⟩
        · rw [hKbig_def, Set.mem_diff]
          rw [Set.mem_Icc] at hy_in
          refine ⟨?_, ?_⟩
          · rw [Set.mem_Icc]; constructor <;> linarith [hy_in.1, hy_in.2]
          · intro hc'
            rw [Set.mem_Ioo] at hc'
            exact hy_out (by rw [Set.mem_Ioo]; constructor <;> linarith [hc'.1, hc'.2])
        · intro hyWin
          rw [hbaseWin_def, Set.mem_iUnion] at hyWin
          obtain ⟨k, hyk⟩ := hyWin
          rw [Set.mem_Ioo] at hyk
          have hyxk : |y - x k| < ε₂/2 := by rw [abs_lt]; constructor <;> linarith [hyk.1, hyk.2]
          have hφxk : |φ k c - x k| < ε₂/2 := hclose_ε2 c hc0 hcle k
          have hyφ : |y - φ k c| < ε₂ := by
            have : |y - φ k c| ≤ |y - x k| + |x k - φ k c| := abs_sub_le _ _ _
            rw [abs_sub_comm (x k) (φ k c)] at this
            linarith [hyxk, hφxk]
          apply hy_notslice
          rw [Set.mem_iUnion₂]
          refine ⟨φ k c, ?_, ?_⟩
          · rw [Set.mem_setOf_eq]; exact hz_zero c hc0 hcle k
          · rw [Set.mem_Ioo]; rw [abs_lt] at hyφ; constructor <;> linarith [hyφ.1, hyφ.2]
      rw [hA_ne] at hyA; exact hyA

end Workspace.ProofLemmas
