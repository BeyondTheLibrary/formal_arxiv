import Mathlib
import Workspace.Types.PlanarCounting

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.PlanarCounting
open Filter

theorem Thm23FinalBound (γ B : ℝ) (hγ : 0 < γ) (hB : 0 < B)
    (fseq : ℕ → ℕ) (nseq : ℕ → ℕ) (Pseq : ℕ → Finset (EuclideanSpace ℝ (Fin 2)))
    (hf : Filter.Tendsto fseq Filter.atTop Filter.atTop)
    (hcard : ∀ j, (Pseq j).card = nseq j)
    (hnu : ∀ j, (nu (Pseq j) : ℝ) ≥ (1 / 2) * Real.exp (γ * (fseq j : ℝ) / 2) * (nseq j : ℝ))
    (hsize : ∀ j, (nseq j : ℝ) ≤ Real.exp (B * (fseq j : ℝ)))
    (hlb : ∀ j, Real.exp (γ * (fseq j : ℝ) / 2) ≤ (nseq j : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (nuMax n : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) + δ) := by
  set δ : ℝ := γ / (4 * B) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨δ, hδ, ?_⟩
  -- `n_j ≥ 1`.
  have hn1R : ∀ j, (1 : ℝ) ≤ (nseq j : ℝ) := by
    intro j
    refine le_trans ?_ (hlb j)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (div_nonneg (mul_nonneg hγ.le (Nat.cast_nonneg _)) (by norm_num))
  have hn1 : ∀ j, 1 ≤ nseq j := fun j => by exact_mod_cast hn1R j
  have hnpos : ∀ j, (0 : ℝ) < (nseq j : ℝ) := fun j => lt_of_lt_of_le one_pos (hn1R j)
  -- Per-`j` bound: `nu (Pseq j) ≥ ½ n_j^{1+2δ}`.
  have hper : ∀ j, (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ) ≤ (nu (Pseq j) : ℝ) := by
    intro j
    have hexp_ge : (nseq j : ℝ) ^ (2 * δ) ≤ Real.exp (γ * (fseq j : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos (hnpos j)]
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (nseq j) ≤ B * (fseq j : ℝ) :=
        (Real.log_le_iff_le_exp (hnpos j)).mpr (hsize j)
      have h2δ : (2 : ℝ) * δ = γ / (2 * B) := by rw [hδdef]; field_simp; ring
      rw [h2δ]
      calc Real.log (nseq j) * (γ / (2 * B))
            ≤ (B * (fseq j : ℝ)) * (γ / (2 * B)) :=
              mul_le_mul_of_nonneg_right hlog (div_nonneg hγ.le (by positivity))
        _ = γ * (fseq j : ℝ) / 2 := by field_simp
    calc (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ)
        = (1 / 2) * ((nseq j : ℝ) ^ (2 * δ) * (nseq j : ℝ)) := by
          rw [show (1 : ℝ) + 2 * δ = 2 * δ + 1 from by ring, Real.rpow_add (hnpos j),
            Real.rpow_one]
      _ ≤ (1 / 2) * (Real.exp (γ * (fseq j : ℝ) / 2) * (nseq j : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hexp_ge (hnpos j).le
      _ = (1 / 2) * Real.exp (γ * (fseq j : ℝ) / 2) * (nseq j : ℝ) := by ring
      _ ≤ (nu (Pseq j) : ℝ) := hnu j
  -- `n_j → ∞`.
  have htexp : Tendsto (fun j => Real.exp (γ * (fseq j : ℝ) / 2)) atTop atTop := by
    have hfR : Tendsto (fun j => (fseq j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hf
    have hg : Tendsto (fun j => (fseq j : ℝ) * (γ / 2)) atTop atTop :=
      hfR.atTop_mul_const (half_pos hγ)
    have hg' : Tendsto (fun j => γ * (fseq j : ℝ) / 2) atTop atTop := hg.congr (fun j => by ring)
    exact Real.tendsto_exp_atTop.comp hg'
  have htn : Tendsto (fun j => (nseq j : ℝ)) atTop atTop :=
    tendsto_atTop_mono hlb htexp
  -- `BddAbove` of the `nuMax` value set.
  have hbdd : ∀ n : ℕ,
      BddAbove {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ nu P = k} := by
    intro n
    refine ⟨(n + 1).choose 2, ?_⟩
    rintro k ⟨P, hPc, rfl⟩
    calc nu P ≤ P.sym2.card := by
          have heq : nu P = (P.sym2.filter (fun s => ¬ s.IsDiag ∧ distSym2 s = 1)).card := by
            unfold nu; congr!
          rw [heq]
          exact Finset.card_filter_le _ _
      _ = (P.card + 1).choose 2 := Finset.card_sym2 P
      _ = (n + 1).choose 2 := by rw [hPc]
  -- Conclusion.
  intro N
  obtain ⟨j, hj⟩ := (htn.eventually_ge_atTop (max (N : ℝ) ((2 : ℝ) ^ (1 / δ)))).exists
  refine ⟨nseq j, ?_, hn1 j, ?_⟩
  · have : (N : ℝ) ≤ (nseq j : ℝ) := le_trans (le_max_left _ _) hj
    exact_mod_cast this
  · -- `nuMax (nseq j) ≥ (nseq j)^{1+δ}`.
    have hmem : nu (Pseq j) ∈ {k : ℕ | ∃ P, P.card = nseq j ∧ nu P = k} :=
      ⟨Pseq j, hcard j, rfl⟩
    have hnumaxR : (nu (Pseq j) : ℝ) ≤ (nuMax (nseq j) : ℝ) := by
      exact_mod_cast le_csSup (hbdd (nseq j)) hmem
    have hn2δ : (2 : ℝ) ≤ (nseq j : ℝ) ^ δ := by
      have h2δpow : ((2 : ℝ) ^ (1 / δ)) ^ δ = 2 := by
        rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      rw [← h2δpow]
      exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hj) hδ.le
    have hnδpos : (0 : ℝ) ≤ (nseq j : ℝ) ^ (1 + δ) := Real.rpow_nonneg (hnpos j).le _
    have hfinal : (nseq j : ℝ) ^ (1 + δ) ≤ (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ) := by
      have hsplit : (nseq j : ℝ) ^ (1 + 2 * δ) = (nseq j : ℝ) ^ (1 + δ) * (nseq j : ℝ) ^ δ := by
        rw [← Real.rpow_add (hnpos j)]; congr 1; ring
      rw [hsplit]
      nlinarith [hn2δ, hnδpos, mul_nonneg hnδpos (sub_nonneg.mpr hn2δ)]
    calc (nseq j : ℝ) ^ ((1 : ℝ) + δ) = (nseq j : ℝ) ^ (1 + δ) := by norm_num
      _ ≤ (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ) := hfinal
      _ ≤ (nu (Pseq j) : ℝ) := hper j
      _ ≤ (nuMax (nseq j) : ℝ) := hnumaxR
