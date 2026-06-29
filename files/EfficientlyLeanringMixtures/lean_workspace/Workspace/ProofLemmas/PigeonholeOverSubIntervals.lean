import Mathlib

namespace Workspace.ProofLemmas

theorem PigeonholeOverSubIntervals
    (a b : ℝ) (hab : a ≤ b)
    (g : ℝ → ℝ) (hg_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ g x)
    (hg_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (N : ℕ)
    (xs : Fin (N + 2) → ℝ)
    (h_x0 : xs 0 = a)
    (h_xN1 : xs (Fin.last (N + 1)) = b)
    (h_mono : Monotone xs)
    (A : ℝ)
    (h_total : A ≤ ∫ x in a..b, g x) :
    ∃ k : Fin (N + 1),
      A / (N + 1 : ℝ) ≤ ∫ x in (xs k.castSucc)..(xs k.succ), g x := by
  -- ℕ-indexed extension: p k = xs ⟨min k (N+1), _⟩
  let p : ℕ → ℝ := fun k => xs ⟨min k (N + 1), by
    have : min k (N + 1) ≤ N + 1 := min_le_right _ _
    omega⟩
  -- xs bounds
  have hxs_ge_a : ∀ i : Fin (N + 2), a ≤ xs i := by
    intro i
    have : xs 0 ≤ xs i := h_mono (Fin.zero_le i)
    rw [h_x0] at this; exact this
  have hxs_le_b : ∀ i : Fin (N + 2), xs i ≤ b := by
    intro i
    have : xs i ≤ xs (Fin.last (N + 1)) := h_mono (Fin.le_last i)
    rw [h_xN1] at this; exact this
  -- p k for k ≤ N+1 unfolds to xs ⟨k, _⟩
  have hp_eq : ∀ k : ℕ, ∀ hk : k ≤ N + 1, p k = xs ⟨k, by omega⟩ := by
    intro k hk
    simp only [p]
    congr 1
    apply Fin.mk_eq_mk.mpr
    exact min_eq_left hk
  have hp_0 : p 0 = a := by
    rw [hp_eq 0 (by omega)]
    convert h_x0 using 2
  have hp_N1 : p (N + 1) = b := by
    rw [hp_eq (N + 1) (le_refl _)]
    convert h_xN1 using 2
  have hp_in_ab : ∀ k : ℕ, k ≤ N + 1 → a ≤ p k ∧ p k ≤ b := by
    intro k hk
    rw [hp_eq k hk]; exact ⟨hxs_ge_a _, hxs_le_b _⟩
  have hp_mono : ∀ k : ℕ, p k ≤ p (k + 1) := by
    intro k
    simp only [p]
    apply h_mono
    simp only [Fin.mk_le_mk]
    exact min_le_min_right _ (Nat.le_succ k)
  -- Integrability on each subinterval
  have hii : ∀ k : ℕ, k < N + 1 → IntervalIntegrable g MeasureTheory.volume (p k) (p (k + 1)) := by
    intro k hk
    have hk1 : k + 1 ≤ N + 1 := hk
    have hkk : k ≤ N + 1 := by omega
    have hpk_in := hp_in_ab k hkk
    have hpk1_in := hp_in_ab (k + 1) hk1
    have hle : p k ≤ p (k + 1) := hp_mono k
    exact hg_integrable.mono_set (by
      rw [Set.uIcc_of_le hle, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc hpk_in.1 hpk1_in.2)
  -- Sum of adjacent integrals = ∫_a^b
  have hsum_eq : ∑ k ∈ Finset.range (N + 1), ∫ x in (p k)..(p (k + 1)), g x
                  = ∫ x in (p 0)..(p (N + 1)), g x := by
    exact intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hii k hk)
  rw [hp_0, hp_N1] at hsum_eq
  -- Convert each p-indexed integral to xs.castSucc / xs.succ form
  -- First, the indexes:
  have h_castSucc : ∀ k : Fin (N + 1), p (k : ℕ) = xs k.castSucc := by
    intro k
    have hkk : (k : ℕ) ≤ N + 1 := by have := k.isLt; omega
    rw [hp_eq k hkk]
    congr 1
  have h_succ : ∀ k : Fin (N + 1), p ((k : ℕ) + 1) = xs k.succ := by
    intro k
    have hk1 : (k : ℕ) + 1 ≤ N + 1 := k.isLt
    rw [hp_eq ((k : ℕ) + 1) hk1]
    congr 1
  -- Now sum equality bridging range and univ
  have hsum_range : ∑ k ∈ Finset.range (N + 1), ∫ x in (p k)..(p (k + 1)), g x
      = ∑ k : Fin (N + 1), ∫ x in (xs k.castSucc)..(xs k.succ), g x := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ∫ x in (p k)..(p (k + 1)), g x) (N + 1)]
    apply Finset.sum_congr rfl
    intro k _
    rw [h_castSucc k, h_succ k]
  rw [hsum_range] at hsum_eq
  -- Now: sum of subinterval integrals = ∫_a^b g
  -- ≥ A.
  have hsum_ge_A : A ≤ ∑ k : Fin (N + 1), ∫ x in (xs k.castSucc)..(xs k.succ), g x := by
    rw [hsum_eq]; exact h_total
  -- Pigeonhole
  by_contra hcon
  push_neg at hcon
  have hN1_pos : (0 : ℝ) < (N + 1 : ℝ) := by
    have : (0 : ℕ) < N + 1 := Nat.succ_pos N
    exact_mod_cast this
  have hcard : (Finset.univ : Finset (Fin (N + 1))).card = N + 1 := by
    simp
  have hsum_const : (∑ _ : Fin (N + 1), (A / (N + 1 : ℝ))) = A := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    have hne : (N + 1 : ℝ) ≠ 0 := ne_of_gt hN1_pos
    field_simp
    push_cast
    ring
  have hsum_lt : (∑ k : Fin (N + 1), ∫ x in (xs k.castSucc)..(xs k.succ), g x) < A := by
    calc (∑ k : Fin (N + 1), ∫ x in (xs k.castSucc)..(xs k.succ), g x)
        < ∑ _ : Fin (N + 1), (A / (N + 1 : ℝ)) := by
          apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
          intro k _; exact hcon k
      _ = A := hsum_const
  linarith

end Workspace.ProofLemmas
