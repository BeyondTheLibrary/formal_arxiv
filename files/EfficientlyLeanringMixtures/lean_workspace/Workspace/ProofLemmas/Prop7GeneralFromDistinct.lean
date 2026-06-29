import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FinitenessOfSignedGaussianZeros
import Workspace.ProofLemmas.FirstReductionSimpleZeros
import Workspace.ProofLemmas.FirstReductionCountNonDecrease
import Workspace.ProofLemmas.DistinctVariancePerturbationExists
import Workspace.ProofLemmas.SimpleZeroPersistsUnderVariancePerturbation
import Workspace.ProofLemmas.VariancePerturbFamily
import Workspace.ProofLemmas.Proposition7ZeroCount

/-!
# `Prop7GeneralFromDistinct` — general (coincident-variance-allowed) Proposition 7

Assembles the five sub-lemmas of the Moitra–Valiant §6.1 first-reduction argument
(plus the distinct-variance Proposition 7 black box `Proposition7ZeroCount`) into
the general statement: any signed combination of `k` Gaussian densities, with a
nonzero coefficient and not identically zero, has at most `2·(k−1)` distinct real
zeros — with NO assumption that the variances are pairwise distinct.

This theorem statement is byte-identical to the axiom it replaces,
`Workspace.PriorWork.HurwitzAnalyticZeroCountUSC`.

Proof skeleton (see proof_detailed.md):
1. `FirstReductionSimpleZeros` perturbs a single coefficient to get `S_ε` with all
   simple zeros, same length `k`, nonzero coeff, density ≢ 0, and
   `zeroCount S.density ≤ zeroCount S_ε.density`.
2. `FinitenessOfSignedGaussianZeros` makes `S_ε`'s zero set finite; enumerate it
   strictly monotonically as `x : Fin r → ℝ`, with `zeroCount S_ε.density = r`.
3. `DistinctVariancePerturbationExists S_ε` gives `δ₀`.
4. `SimpleZeroPersistsUnderVariancePerturbation` injects the `r` simple zeros into
   distinct zeros of `variancePerturb S_ε δ` for small `δ`, so
   `r ≤ zeroCount (variancePerturb S_ε δ).density`.
5. `Proposition7ZeroCount` on `variancePerturb S_ε δ` (Nodup variances, length `k`,
   nonzero coeff) gives `zeroCount ≤ 2·(k−1)`.
6. Chain in `ℕ∞`.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.ZeroCount

theorem Prop7GeneralFromDistinct
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (h_nonzero_coeffs : ∃ p ∈ S.components, p.fst ≠ 0)
    (h_density_nonzero : ∃ x, S.density x ≠ 0)
    (hm : 1 ≤ S.components.length) :
    Workspace.Types.ZeroCount.hasAtMostNZeros S.density (2 * (S.components.length - 1)) := by
  -- Step 1: first reduction to all-simple-zeros.
  obtain ⟨i₀, η, hη_pos, hη_lt, hSε_len, hSε_coeff, hSε_ne, hSε_simple, hSε_count⟩ :=
    FirstReductionSimpleZeros S hm h_nonzero_coeffs h_density_nonzero 1 (by norm_num)
  set Sε := coeffPerturbSub S i₀ η with hSε_def
  -- It suffices to bound zeroCount Sε.density ≤ 2*(k-1).
  rw [hasAtMostNZeros_def]
  -- Length of Sε equals k.
  have hk_eq : Sε.components.length = S.components.length := hSε_len
  -- Step 2: finiteness of Sε's zero set; enumerate it.
  obtain ⟨hFin, hLt⟩ := FinitenessOfSignedGaussianZeros Sε hSε_ne
  set F : Set ℝ := zeroSet Sε.density with hF_def
  -- The finite set as a Finset.
  set Fs : Finset ℝ := hFin.toFinset with hFs_def
  set r : ℕ := Fs.card with hr_def
  -- Strictly monotone enumeration x : Fin r → ℝ.
  set x : Fin r → ℝ := fun j => Fs.orderEmbOfFin (rfl) j with hx_def
  have hx_mono : StrictMono x := (Fs.orderEmbOfFin (rfl)).strictMono
  have hx_mem : ∀ j : Fin r, x j ∈ F := by
    intro j
    have : x j ∈ Fs := Fs.orderEmbOfFin_mem (rfl) j
    rwa [hFs_def, Set.Finite.mem_toFinset] at this
  have hx_zero : ∀ j : Fin r, Sε.density (x j) = 0 := by
    intro j
    have := hx_mem j
    rw [hF_def, zeroSet_def] at this
    exact this
  -- zeroCount Sε.density = r.
  have hcount_eq : zeroCount Sε.density = (r : ℕ∞) := by
    rw [zeroCount_def, ← hF_def, hFin.encard_eq_coe_toFinset_card, ← hFs_def, ← hr_def]
  -- Step 3: distinct-variance perturbation threshold for Sε.
  obtain ⟨δ₀, hδ₀_pos, hδ₀_prop⟩ := DistinctVariancePerturbationExists Sε (hk_eq ▸ hm)
  -- Step 4: simple-zero persistence.
  obtain ⟨δp, hδp_pos, hδp_prop⟩ :=
    SimpleZeroPersistsUnderVariancePerturbation Sε hSε_simple r x hx_mono hx_zero
  -- Pick δ* in (0, min δ₀ δp).
  set δstar : ℝ := min δ₀ δp / 2 with hδstar_def
  have hmin_pos : 0 < min δ₀ δp := lt_min hδ₀_pos hδp_pos
  have hδstar_pos : 0 < δstar := by rw [hδstar_def]; linarith
  have hδstar_lt₀ : δstar < δ₀ := by
    rw [hδstar_def]
    have : min δ₀ δp ≤ δ₀ := min_le_left _ _
    linarith
  have hδstar_ltp : δstar < δp := by
    rw [hδstar_def]
    have : min δ₀ δp ≤ δp := min_le_right _ _
    linarith
  -- The variance-perturbed combination at δ*.
  set P : SignedGaussianCombination := variancePerturb Sε δstar (le_of_lt hδstar_pos) with hP_def
  -- Distinct variances and positivity for P.
  obtain ⟨hP_nodup, hP_pos⟩ := hδ₀_prop δstar hδstar_pos hδstar_lt₀
  -- Persistence injection at δ*.
  obtain ⟨ε, hε_pos, hε_sep, z, hz_inj, hz_zero, hz_close⟩ := hδp_prop δstar hδstar_pos hδstar_ltp
  -- P has the same length as Sε (= k).
  have hP_len : P.components.length = S.components.length := by
    rw [hP_def, variancePerturb_length, hk_eq]
  -- P has a nonzero coefficient: the coefficient lists of P and Sε agree.
  have hP_coeffs : P.components.map (fun p => p.1) = Sε.components.map (fun p => p.1) := by
    rw [hP_def]
    unfold variancePerturb
    simp only [List.map_map]
    show (List.finRange Sε.components.length).map (fun i => (Sε.components.get i).1)
        = Sε.components.map (fun p => p.1)
    have h : (fun i => ((Sε.components.get i).1)) = (fun p => p.1) ∘ Sε.components.get := rfl
    rw [h, ← List.map_map, List.map_get_finRange]
  have hP_coeff : ∃ p ∈ P.components, p.1 ≠ 0 := by
    obtain ⟨q, hq_mem, hq_ne⟩ := hSε_coeff
    -- q.1 is in the coefficient list of Sε, hence of P.
    have hq_in : q.1 ∈ Sε.components.map (fun p => p.1) := List.mem_map_of_mem hq_mem
    rw [← hP_coeffs] at hq_in
    obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_map.mp hq_in
    exact ⟨p, hp_mem, by rw [hp_eq]; exact hq_ne⟩
  -- Step 5: distinct-variance Proposition 7 bounds zeroCount P.density.
  have hP_bound : zeroCount P.density ≤ ((2 * (S.components.length - 1)) : ℕ∞) := by
    have h7 := Proposition7ZeroCount P (by rw [hP_len]; exact hm)
      (by
        -- Nodup of variances; p.snd.varSq is defeq to p.2.varSq.
        exact hP_nodup)
      hP_coeff
    rw [hasAtMostNZeros_def] at h7
    rw [hP_len] at h7
    exact h7
  -- Step 4: the r persistence zeros inject into the zero set of P, so r ≤ zeroCount P.density.
  have hinj : (r : ℕ∞) ≤ zeroCount P.density := by
    rw [zeroCount_def]
    -- range z ⊆ zeroSet P.density
    have hsub : Set.range z ⊆ zeroSet P.density := by
      rintro y ⟨j, rfl⟩
      rw [zeroSet_def]
      exact hz_zero j
    have hrange_card : (Set.range z).encard = (r : ℕ∞) := by
      rw [← Set.image_univ, Function.Injective.encard_image hz_inj]
      rw [Set.encard_univ]
      simp
    calc (r : ℕ∞) = (Set.range z).encard := hrange_card.symm
      _ ≤ (zeroSet P.density).encard := Set.encard_le_encard hsub
  -- Step 6: chain the inequalities.
  calc zeroCount S.density
      ≤ zeroCount Sε.density := hSε_count
    _ = (r : ℕ∞) := hcount_eq
    _ ≤ zeroCount P.density := hinj
    _ ≤ ((2 * (S.components.length - 1)) : ℕ∞) := hP_bound

end Workspace.ProofLemmas
