import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope
import Workspace.ProofLemmas.ConvFamilyUniformRegionB
import Workspace.ProofLemmas.ConvFamilyUniformRegionC
import Workspace.ProofLemmas.ConvFamilyRegionBFloors
import Workspace.ProofLemmas.ConvFamilyUniformEnvelope
import Workspace.ProofLemmas.HurwitzGaussianPerturbationTailDominance
import Workspace.ProofLemmas.SublemmaAddGaussianTailRegionNoZeros
import Workspace.ProofLemmas.FinitenessOfSignedGaussianZeros
import Workspace.PriorWork.HummelGidasZeroCount
import Workspace.ProofLemmas.SignedGaussianCombinationDensityBounded

/-!
# `ConvFamilyDiagonalThresholdConcrete` — STEP-1-concrete

Unconditional diagonal near-delta threshold for the normalized convolution family of a
SIMPLE-zero base.  This DISCHARGES the region-(a) (uniform tail envelope) and region-(b)
(floor bundle) hypotheses of the assembly skeleton `convFamily_uniform_diagonal_threshold`
with the now-proven producers `convFamilyUniformEnvelope`,
`HurwitzGaussianPerturbationTailDominance`, and `convFamily_regionB_floor_bundle`, mirroring
the skeleton's body inline (the skeleton's `hcover : ∀ δ, …` cannot be supplied from the
δ-dependent floor-bundle producer, so the assembly is re-derived here at the single δ that
region (c) fixes).

Conclusion: for a simple base `S` with `S.density ν ≠ 0`, `≤ N` zeros, and a nonzero
top coefficient, and any `a_k ≠ 0`, there is `v_diag > 0` such that for every
`v ∈ (0, v_diag]`, `hasAtMostNZeros (fFamU S v + a_k·N(ν, v)) (N + 2)`.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open Workspace.Types.ZeroCount

set_option maxHeartbeats 4000000

/-- **STEP-1-concrete — unconditional band-uniform diagonal near-delta threshold for the
normalized convolution family of a SIMPLE-zero base.**

`S` is a signed Gaussian combination whose density has only simple zeros, has `≤ N` zeros,
is somewhere nonzero, and is nonzero at `ν`.  For any `a_k ≠ 0`, there is a single
`v_diag > 0` such that for every `v ∈ (0, v_diag]` the diagonal perturbed slice
`fFamU S v + a_k·N(ν, v)` has at most `N + 2` zeros. -/
theorem convFamily_diagonal_threshold_concrete
    (S : SignedGaussianCombination)
    (hsimple0 : ∀ x, S.density x = 0 → deriv S.density x ≠ 0)
    (hne : ∃ x : ℝ, S.density x ≠ 0)
    (ν : ℝ) (hν : S.density ν ≠ 0)
    (N : ℕ) (hN : Workspace.Types.ZeroCount.hasAtMostNZeros S.density N)
    (a_k : ℝ) (ha_k : a_k ≠ 0) :
    ∃ v_diag : ℝ, 0 < v_diag ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v_diag →
        Workspace.Types.ZeroCount.hasAtMostNZeros
          (fun x => fFamU S v x +
            a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x)
          (N + 2) := by
  classical
  -- ===== Region (c): self-contained inner ≤2 bound; supplies `c_maxC`, `v0c`, `δ`. =====
  obtain ⟨c_maxC, hc_maxC, v0c, hv0c, δ, hδ, hregionC⟩ :=
    convFamily_uniform_regionC S ν hν a_k ha_k
  -- ===== Enumerate the zeros of `S.density` as a StrictMono `x : Fin r → ℝ`. =====
  obtain ⟨hFin, _hLt⟩ := FinitenessOfSignedGaussianZeros S hne
  set F : Set ℝ := zeroSet S.density with hF_def
  set Fs : Finset ℝ := hFin.toFinset with hFs_def
  set r : ℕ := Fs.card with hr_def
  set xz : Fin r → ℝ := fun j => Fs.orderEmbOfFin (rfl) j with hxz_def
  have hxz_mono : StrictMono xz := (Fs.orderEmbOfFin (rfl)).strictMono
  have hxz_mem : ∀ j : Fin r, xz j ∈ F := by
    intro j
    have : xz j ∈ Fs := Fs.orderEmbOfFin_mem (rfl) j
    rwa [hFs_def, Set.Finite.mem_toFinset] at this
  have hxz_zero : ∀ j : Fin r, S.density (xz j) = 0 := by
    intro j; have := hxz_mem j; rw [hF_def, zeroSet_def] at this; exact this
  have hcount_eq : zeroCount S.density = (r : ℕ∞) := by
    rw [zeroCount_def, ← hF_def, hFin.encard_eq_coe_toFinset_card, ← hFs_def, ← hr_def]
  -- The zero count `r ≤ N`.
  have hr_le_N : (r : ℕ∞) ≤ (N : ℕ∞) := by rw [← hcount_eq]; exact hN
  -- ===== Reference Hummel–Gidas band: every slice keeps `≤ r` zeros for `c ≥ 0`. =====
  -- `fFamU S c = conv(S.density, c)` (for `c > 0`); `S.density` is analytic with `≤ r` zeros;
  -- Hummel–Gidas keeps `≤ r` zeros under convolution.
  have hSdens_analytic : AnalyticOnNhd ℝ S.density Set.univ := by
    have := gFam_analytic_zero S; rwa [fFamU_zero_fun S] at this
  have hSdens_r : Workspace.Types.ZeroCount.hasAtMostNZeros S.density r := by
    rw [Workspace.Types.ZeroCount.hasAtMostNZeros]; rw [hcount_eq]
  set c_max_HG : ℝ := 1 with hc_max_HG_def
  have hc_max_HG : (0 : ℝ) < c_max_HG := by rw [hc_max_HG_def]; norm_num
  have hgα_zeros_HG : ∀ c : ℝ, 0 ≤ c → c ≤ c_max_HG →
      zeroCount (fun y => fFamU S c y) ≤ (r : ℕ∞) := by
    intro c hc0 _hcle
    rcases eq_or_lt_of_le hc0 with h0 | hpos
    · -- c = 0: fFamU S 0 = S.density
      have : (fun y => fFamU S c y) = S.density := by rw [← h0]; exact fFamU_zero_fun S
      rw [this]; rw [hcount_eq]
    · -- c > 0: fFamU S c = conv(S.density, c); apply Hummel–Gidas.
      have hconv : (fun y => fFamU S c y) =
          Workspace.Types.GaussianConvolution.convolveWithGaussian S.density c hpos := by
        funext y; exact fFamU_eq_convolve S c hpos y
      rw [hconv]
      have := Workspace.PriorWork.HummelGidasZeroCount S.density hSdens_analytic
                (Workspace.ProofLemmas.SignedGaussianCombinationDensityBounded S) r hSdens_r c hpos
      rw [Workspace.Types.ZeroCount.hasAtMostNZeros] at this; exact this
  -- band substrate `hgα_analytic`/`hgα_simple` on `[0, c_max_HG]`.
  have hgα_analytic_HG : ∀ c : ℝ, 0 ≤ c → c ≤ c_max_HG →
      AnalyticOnNhd ℝ (fun x => fFamU S c x) Set.univ :=
    fun c hc0 _ => gFam_analytic S c hc0
  -- ===== Region (b) floor bundle at the region-(c) δ, on band `[0, c_max_HG]`. =====
  -- Choose a wide tail window `[bw, bw']` containing `ν` strictly (supplied to region (b)
  -- AND to the fuse); region (a)'s envelope window is widened to it below.
  -- First the envelope (region (a)) to learn its window, then widen to include `ν`.
  obtain ⟨be, be', ae, ae', se, se', hbe_lt, hae, hae', hse, hse', henv⟩ :=
    convFamilyUniformEnvelope S hne c_max_HG hc_max_HG
  -- Widened band containing `ν` strictly: `b = min be (ν-1)`, `b' = max be' (ν+1)`.
  set b : ℝ := min be (ν - 1) with hb_def
  set b' : ℝ := max be' (ν + 1) with hb'_def
  have hb_le_be : b ≤ be := min_le_left _ _
  have hbe'_le_b' : be' ≤ b' := le_max_left _ _
  have hb_lt_ν : b < ν := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hν_lt_b' : ν < b' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hbb' : b < b' := lt_trans hb_lt_ν hν_lt_b'
  -- Region (b) floor bundle.
  obtain ⟨c_maxB, hc_maxB_pos, hc_maxB_le, ε₁_unif, hε₁_unif_pos,
          g_lb_unif, hg_lb_unif_pos, ε₂fam,
          hε₂fam_pos, hε₂fam_le_δ8, hε₂fam_le_1, hderiv_lb_fam,
          hε₁_unif_le, hg_lb_unif_spec⟩ :=
    convFamily_regionB_floor_bundle S hsimple0 r xz hxz_mono hxz_zero hcount_eq
      ν b b' δ hδ c_max_HG hc_max_HG hgα_zeros_HG
  -- The band substrate restricted to `[0, c_maxB]`.
  have hcB_le_HG : c_maxB ≤ c_max_HG := hc_maxB_le
  have hgα_analytic_B : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB →
      AnalyticOnNhd ℝ (fun x => fFamU S c x) Set.univ :=
    fun c hc0 hcle => hgα_analytic_HG c hc0 (le_trans hcle hcB_le_HG)
  have hgα_zeros_B : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB →
      Workspace.Types.ZeroCount.hasAtMostNZeros (fun x => fFamU S c x) N := by
    intro c hc0 hcle
    have h := hgα_zeros_HG c hc0 (le_trans hcle hcB_le_HG)
    rw [Workspace.Types.ZeroCount.hasAtMostNZeros]; exact le_trans h hr_le_N
  -- simplicity on `[0, c_maxB]` via `convSmall_all_zeros_simple`.
  obtain ⟨α_pers, hα_pers_pos, hα_pers_spec⟩ :=
    convSmall_all_zeros_simple S hsimple0 r xz hxz_mono hxz_zero hcount_eq
  -- We need a simplicity-bearing sub-band of `[0, c_maxB]`: shrink to `c_maxB' = min c_maxB (α_pers/2)`.
  set c_maxB' : ℝ := min c_maxB (α_pers / 2) with hc_maxB'_def
  have hc_maxB'_pos : 0 < c_maxB' := lt_min hc_maxB_pos (by linarith)
  have hc_maxB'_le_B : c_maxB' ≤ c_maxB := min_le_left _ _
  have hc_maxB'_lt_pers : c_maxB' < α_pers :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hgα_simple_B : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' →
      ∀ x : ℝ, fFamU S c x = 0 → deriv (fun y => fFamU S c y) x ≠ 0 := by
    intro c hc0 hcle x hx
    rcases eq_or_lt_of_le hc0 with h0 | hpos
    · -- c = 0: simplicity is `hsimple0`.
      have hfun0 : (fun y => fFamU S c y) = S.density := by rw [← h0]; exact fFamU_zero_fun S
      have hx0 : S.density x = 0 := by rw [← hfun0]; exact hx
      rw [hfun0]; exact hsimple0 x hx0
    · -- c > 0, c < α_pers: convSmall simplicity.
      have hconv : (fun y => fFamU S c y) =
          Workspace.Types.GaussianConvolution.convolveWithGaussian S.density c hpos := by
        funext y; exact fFamU_eq_convolve S c hpos y
      have hxc : Workspace.Types.GaussianConvolution.convolveWithGaussian S.density c hpos x = 0 := by
        rw [← hconv]; exact hx
      have hcount_c : zeroCount
          (Workspace.Types.GaussianConvolution.convolveWithGaussian S.density c hpos) ≤ (r : ℕ∞) := by
        have := hgα_zeros_HG c hc0 (le_trans (le_trans hcle hc_maxB'_le_B) hcB_le_HG)
        rwa [hconv] at this
      have hc_lt : c < α_pers := lt_of_le_of_lt hcle hc_maxB'_lt_pers
      have := hα_pers_spec c hpos hc_lt hcount_c x hxc
      rw [hconv]; exact this
  -- Region (b) bundle clauses restricted from `[0, c_maxB]` to the sub-band `[0, c_maxB']`.
  have hgα_analytic_B' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' →
      AnalyticOnNhd ℝ (fun x => fFamU S c x) Set.univ :=
    fun c hc0 hcle => hgα_analytic_B c hc0 (le_trans hcle hc_maxB'_le_B)
  have hgα_zeros_B' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' →
      Workspace.Types.ZeroCount.hasAtMostNZeros (fun x => fFamU S c x) N :=
    fun c hc0 hcle => hgα_zeros_B c hc0 (le_trans hcle hc_maxB'_le_B)
  have hε₂fam_pos' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' → 0 < ε₂fam c :=
    fun c hc0 hcle => hε₂fam_pos c hc0 (le_trans hcle hc_maxB'_le_B)
  have hε₂fam_le_δ8' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' → ε₂fam c ≤ δ/8 :=
    fun c hc0 hcle => hε₂fam_le_δ8 c hc0 (le_trans hcle hc_maxB'_le_B)
  have hε₂fam_le_1' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' → ε₂fam c ≤ 1 :=
    fun c hc0 hcle => hε₂fam_le_1 c hc0 (le_trans hcle hc_maxB'_le_B)
  have hderiv_lb_fam' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' →
      ∀ x_j : ℝ, fFamU S c x_j = 0 →
        ∀ x ∈ Set.Icc (x_j - ε₂fam c) (x_j + ε₂fam c),
          |deriv (fun y => fFamU S c y) x_j| / 2 ≤ |deriv (fun y => fFamU S c y) x| :=
    fun c hc0 hcle => hderiv_lb_fam c hc0 (le_trans hcle hc_maxB'_le_B)
  have hε₁_unif_le' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' →
      ∀ x_j : ℝ, fFamU S c x_j = 0 → ε₁_unif ≤ |deriv (fun y => fFamU S c y) x_j| :=
    fun c hc0 hcle => hε₁_unif_le c hc0 (le_trans hcle hc_maxB'_le_B)
  have hg_lb_unif_spec' : ∀ c : ℝ, 0 ≤ c → c ≤ c_maxB' →
      ∀ x ∈ (Set.Icc b b' \ Set.Ioo (ν - δ) (ν + δ)) \
          (⋃ x_j ∈ {y : ℝ | fFamU S c y = 0}, Set.Ioo (x_j - ε₂fam c) (x_j + ε₂fam c)),
        g_lb_unif ≤ |fFamU S c x| :=
    fun c hc0 hcle => hg_lb_unif_spec c hc0 (le_trans hcle hc_maxB'_le_B)
  -- ===== Region (b): outer ≤N bound on `Icc b b' \ Ioo(ν-δ)(ν+δ)`, band `[0, c_maxB']`. =====
  obtain ⟨v0b, hv0b, hregionB⟩ :=
    convFamily_uniform_regionB S c_maxB' hc_maxB'_pos N a_k ha_k ν b b' hbb' δ hδ
      hgα_analytic_B' hgα_zeros_B' hgα_simple_B
      ε₁_unif hε₁_unif_pos g_lb_unif hg_lb_unif_pos
      ε₂fam hε₂fam_pos' hε₂fam_le_δ8' hε₂fam_le_1' hderiv_lb_fam' hε₁_unif_le' hg_lb_unif_spec'
  -- ===== Region (a): uniform tail containment from envelope + tail dominance. =====
  -- Uniform tail-dominance threshold `v0a` for the WIDENED window `(b, b')` with `b < ν < b'`.
  obtain ⟨v0a, hv0a, htail0⟩ :=
    HurwitzGaussianPerturbationTailDominance_uniform b b' ae ae' se se'
      hbb' hae hae' hse hse' ν hb_lt_ν hν_lt_b' a_k ha_k
  -- ===== Common band & diagonal threshold. =====
  set c_max : ℝ := min c_max_HG (min c_maxB' c_maxC) with hc_max_def
  have hc_max_pos : 0 < c_max := lt_min hc_max_HG (lt_min hc_maxB'_pos hc_maxC)
  have hc_max_leHG : c_max ≤ c_max_HG := min_le_left _ _
  have hc_max_leB' : c_max ≤ c_maxB' := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc_max_leC : c_max ≤ c_maxC := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨min (min v0a (min v0b v0c)) c_max,
    lt_min (lt_min hv0a (lt_min hv0b hv0c)) hc_max_pos, ?_⟩
  intro v hv hv_le
  have hv_le_inner : v ≤ min v0a (min v0b v0c) := le_trans hv_le (min_le_left _ _)
  have hv_le_v0a : v ≤ v0a := le_trans hv_le_inner (min_le_left _ _)
  have hv_le_v0b : v ≤ v0b := le_trans hv_le_inner (le_trans (min_le_right _ _) (min_le_left _ _))
  have hv_le_v0c : v ≤ v0c := le_trans hv_le_inner (le_trans (min_le_right _ _) (min_le_right _ _))
  have hv_le_cmax : v ≤ c_max := le_trans hv_le (min_le_right _ _)
  have hv_le_HG : v ≤ c_max_HG := le_trans hv_le_cmax hc_max_leHG
  have hv_le_cB' : v ≤ c_maxB' := le_trans hv_le_cmax hc_max_leB'
  have hv_le_cC : v ≤ c_maxC := le_trans hv_le_cmax hc_max_leC
  have hv_nn : (0 : ℝ) ≤ v := le_of_lt hv
  set h : ℝ → ℝ := fun x =>
    fFamU S v x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨ν, v, hv⟩ x with hh_def
  -- ----- Region (a): `zeroSet h ⊆ Icc b b'`. -----
  -- Diagonal slice envelope clauses (widened from `henv v` at `(be, be')` to `(b, b')`).
  have henv_v := henv v hv hv_le_HG
  have hL_v : ∀ x : ℝ, x < b →
      (fFamU S v x).sign = ae.sign ∧
      |ae| * (1 / Real.sqrt (2 * Real.pi * se)) * Real.exp (-x ^ 2 / (2 * se)) <
        |fFamU S v x| := by
    intro x hx; exact henv_v.1 x (lt_of_lt_of_le hx hb_le_be)
  have hR_v : ∀ x : ℝ, x > b' →
      (fFamU S v x).sign = ae'.sign ∧
      |ae'| * (1 / Real.sqrt (2 * Real.pi * se')) * Real.exp (-x ^ 2 / (2 * se')) <
        |fFamU S v x| := by
    intro x hx; exact henv_v.2 x (lt_of_le_of_lt hbe'_le_b' hx)
  have h_tail : zeroSet h ⊆ Set.Icc b b' :=
    htail0 (fun x => fFamU S v x) hL_v hR_v v hv hv_le_v0a
  -- ----- Region (b): outer encard ≤ N. -----
  have h_outer :
      (zeroSet h ∩ (Set.Icc b b' \ Set.Ioo (ν - δ) (ν + δ))).encard ≤ (N : ℕ∞) :=
    hregionB v hv_nn hv_le_cB' v hv hv_le_v0b
  -- ----- Region (c): inner encard ≤ 2. -----
  have h_inner :
      (zeroSet h ∩ Set.Ioo (ν - δ) (ν + δ)).encard ≤ (2 : ℕ∞) :=
    hregionC v hv_nn hv_le_cC v hv hv_le_v0c
  -- ----- Fuse. -----
  exact SublemmaAddGaussianTailRegionNoZeros h b b' ν δ N h_tail h_outer h_inner

end Workspace.ProofLemmas
