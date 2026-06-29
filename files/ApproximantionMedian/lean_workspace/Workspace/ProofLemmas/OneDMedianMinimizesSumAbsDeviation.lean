import Mathlib

open Finset

theorem OneDMedianMinimizesSumAbsDeviation
    {n : ℕ} (y : Fin n → ℝ) (mu : ℝ)
    (hlt : (Finset.univ.filter (fun i : Fin n => y i < mu)).card ≤ n / 2)
    (hgt : (Finset.univ.filter (fun i : Fin n => y i > mu)).card ≤ n / 2)
    (t : ℝ) :
    (∑ i, |y i - mu|) ≤ ∑ i, |y i - t| := by
  -- It suffices to show ∑ (|y i - t| - |y i - mu|) ≥ 0
  rw [← sub_nonneg]
  have hsum_eq : (∑ i, |y i - t|) - (∑ i, |y i - mu|) =
      ∑ i, (|y i - t| - |y i - mu|) := by
    rw [← Finset.sum_sub_distrib]
  rw [hsum_eq]
  -- Split into cases based on the sign of (t - mu)
  rcases le_total mu t with htmu | htmu
  · -- Case t ≥ mu
    -- For each i: pointwise lower bound
    -- If y i ≤ mu: |y i - t| - |y i - mu| = (t - y i) - (mu - y i) = t - mu ≥ 0
    -- If y i > mu: |y i - t| - |y i - mu| ≥ -(t - mu)
    --   because |y i - t| ≥ y i - t = (y i - mu) - (t - mu) = |y i - mu| - (t - mu)
    -- So pointwise: |y i - t| - |y i - mu| ≥ if y i ≤ mu then t - mu else mu - t
    set A : Finset (Fin n) := Finset.univ.filter (fun i => y i ≤ mu) with hA
    set B : Finset (Fin n) := Finset.univ.filter (fun i => mu < y i) with hB
    -- A and B are disjoint, A ∪ B = univ
    have hAB_disj : Disjoint A B := by
      rw [hA, hB]
      rw [Finset.disjoint_filter]
      intros i _ hi1 hi2
      linarith
    have hAB_union : A ∪ B = Finset.univ := by
      rw [hA, hB]
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact (lt_or_ge mu (y i)).symm.imp id id
    -- Define lower bound function
    have key : ∀ i : Fin n, (if y i ≤ mu then (t - mu) else (mu - t)) ≤ |y i - t| - |y i - mu| := by
      intro i
      by_cases h : y i ≤ mu
      · simp only [if_pos h]
        -- y i ≤ mu ≤ t, so |y i - t| = t - y i, |y i - mu| = mu - y i
        have h1 : |y i - t| = t - y i := by
          rw [abs_of_nonpos]; · ring
          linarith
        have h2 : |y i - mu| = mu - y i := by
          rw [abs_of_nonpos]; · ring
          linarith
        rw [h1, h2]; ring_nf; linarith
      · simp only [if_neg h]
        -- y i > mu, want: mu - t ≤ |y i - t| - |y i - mu|
        -- equivalently |y i - mu| + (mu - t) ≤ |y i - t|
        -- |y i - mu| = y i - mu (since y i > mu), so y i - mu + mu - t = y i - t ≤ |y i - t|. True.
        have hgt' : mu < y i := lt_of_not_ge h
        have h2 : |y i - mu| = y i - mu := by
          rw [abs_of_nonneg]; linarith
        rw [h2]
        have h3 : y i - t ≤ |y i - t| := le_abs_self _
        linarith
    -- Now sum the lower bound
    have hsum_lower : (∑ i, (if y i ≤ mu then (t - mu) else (mu - t))) ≤
        ∑ i, (|y i - t| - |y i - mu|) := Finset.sum_le_sum (fun i _ => key i)
    refine le_trans ?_ hsum_lower
    -- Compute ∑ (if y i ≤ mu then t-mu else mu-t)
    -- = (t - mu) * #A + (mu - t) * #B  where A = {y i ≤ mu}, B = {y i > mu}
    have hsum_split : (∑ i, (if y i ≤ mu then (t - mu) else (mu - t))) =
        A.card • (t - mu) + B.card • (mu - t) := by
      rw [← hAB_union, Finset.sum_union hAB_disj]
      have hA_eval : (∑ i ∈ A, (if y i ≤ mu then (t - mu) else (mu - t))) =
          A.card • (t - mu) := by
        rw [Finset.sum_congr rfl]
        · rw [Finset.sum_const]
        · intro i hi
          have : y i ≤ mu := by rw [hA, Finset.mem_filter] at hi; exact hi.2
          simp [this]
      have hB_eval : (∑ i ∈ B, (if y i ≤ mu then (t - mu) else (mu - t))) =
          B.card • (mu - t) := by
        rw [Finset.sum_congr rfl]
        · rw [Finset.sum_const]
        · intro i hi
          have : mu < y i := by rw [hB, Finset.mem_filter] at hi; exact hi.2
          have : ¬ y i ≤ mu := not_le.mpr this
          simp [this]
      rw [hA_eval, hB_eval]
    rw [hsum_split]
    -- A.card • (t - mu) + B.card • (mu - t) = (A.card - B.card) * (t - mu)
    -- We have B.card ≤ n/2 (from hgt) and A.card + B.card = n
    -- So A.card - B.card = n - 2 * B.card ≥ n - 2*(n/2) ≥ 0
    -- And t - mu ≥ 0
    simp only [nsmul_eq_mul]
    have hcard : A.card + B.card = n := by
      have : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB_disj
      rw [hAB_union] at this
      simp at this
      linarith
    have hB_le : B.card ≤ n / 2 := by
      rw [hB]; exact hgt
    have hA_ge : (n : ℝ) - 2 * (B.card : ℝ) ≥ 0 := by
      have h2 : 2 * (n / 2) ≤ n := by omega
      have h3 : 2 * B.card ≤ n := le_trans (by linarith) h2
      have hcast : 2 * (B.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast h3
      linarith
    -- Goal: 0 ≤ A.card * (t - mu) + B.card * (mu - t)
    have : (A.card : ℝ) * (t - mu) + (B.card : ℝ) * (mu - t) =
        ((A.card : ℝ) - (B.card : ℝ)) * (t - mu) := by ring
    rw [this]
    have hAB_diff : (A.card : ℝ) - (B.card : ℝ) ≥ 0 := by
      have : ((A.card + B.card : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hcard
      push_cast at this
      have hAcard_eq : (A.card : ℝ) = (n : ℝ) - (B.card : ℝ) := by linarith
      rw [hAcard_eq]; linarith
    have ht_pos : t - mu ≥ 0 := by linarith
    exact mul_nonneg hAB_diff ht_pos
  · -- Case t < mu (symmetric)
    set A : Finset (Fin n) := Finset.univ.filter (fun i => y i < mu) with hA
    set B : Finset (Fin n) := Finset.univ.filter (fun i => mu ≤ y i) with hB
    have hAB_disj : Disjoint A B := by
      rw [hA, hB]
      rw [Finset.disjoint_filter]
      intros i _ hi1 hi2
      linarith
    have hAB_union : A ∪ B = Finset.univ := by
      rw [hA, hB]
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact lt_or_ge (y i) mu
    -- For t < mu:
    -- If y i ≥ mu: y i ≥ mu > t, so |y i - t| = y i - t, |y i - mu| = y i - mu
    --   diff = (y i - t) - (y i - mu) = mu - t > 0
    -- If y i < mu: want mu - t ≤ |y i - t| - |y i - mu|? No, want: t - mu ≤ ...
    --   Actually we want (mu - t) - bound. We use: |y i - t| ≥ -(y i - t) = t - y i
    --     |y i - mu| = mu - y i
    --     diff = |y i - t| - (mu - y i) ≥ (t - y i) - (mu - y i) = t - mu
    -- So pointwise: |y i - t| - |y i - mu| ≥ if y i < mu then t - mu else mu - t
    have key : ∀ i : Fin n, (if y i < mu then (t - mu) else (mu - t)) ≤ |y i - t| - |y i - mu| := by
      intro i
      by_cases h : y i < mu
      · simp only [if_pos h]
        -- y i < mu, |y i - mu| = mu - y i
        have h2 : |y i - mu| = mu - y i := by
          rw [abs_of_nonpos]; · ring
          linarith
        rw [h2]
        -- want t - mu ≤ |y i - t| - (mu - y i)
        -- i.e., |y i - t| ≥ t - mu + mu - y i = t - y i
        have h3 : -(y i - t) ≤ |y i - t| := neg_le_abs _
        linarith
      · simp only [if_neg h]
        -- y i ≥ mu, and t < mu, so y i ≥ mu > t
        have hge : mu ≤ y i := not_lt.mp h
        have h1 : |y i - t| = y i - t := by
          rw [abs_of_nonneg]; linarith
        have h2 : |y i - mu| = y i - mu := by
          rw [abs_of_nonneg]; linarith
        rw [h1, h2]; ring_nf; linarith
    have hsum_lower : (∑ i, (if y i < mu then (t - mu) else (mu - t))) ≤
        ∑ i, (|y i - t| - |y i - mu|) := Finset.sum_le_sum (fun i _ => key i)
    refine le_trans ?_ hsum_lower
    have hsum_split : (∑ i, (if y i < mu then (t - mu) else (mu - t))) =
        A.card • (t - mu) + B.card • (mu - t) := by
      rw [← hAB_union, Finset.sum_union hAB_disj]
      have hA_eval : (∑ i ∈ A, (if y i < mu then (t - mu) else (mu - t))) =
          A.card • (t - mu) := by
        rw [Finset.sum_congr rfl]
        · rw [Finset.sum_const]
        · intro i hi
          have : y i < mu := by rw [hA, Finset.mem_filter] at hi; exact hi.2
          simp [this]
      have hB_eval : (∑ i ∈ B, (if y i < mu then (t - mu) else (mu - t))) =
          B.card • (mu - t) := by
        rw [Finset.sum_congr rfl]
        · rw [Finset.sum_const]
        · intro i hi
          have : mu ≤ y i := by rw [hB, Finset.mem_filter] at hi; exact hi.2
          have : ¬ y i < mu := not_lt.mpr this
          simp [this]
      rw [hA_eval, hB_eval]
    rw [hsum_split]
    simp only [nsmul_eq_mul]
    have hcard : A.card + B.card = n := by
      have : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hAB_disj
      rw [hAB_union] at this
      simp at this
      linarith
    have hA_le : A.card ≤ n / 2 := by
      rw [hA]; exact hlt
    have : (A.card : ℝ) * (t - mu) + (B.card : ℝ) * (mu - t) =
        ((B.card : ℝ) - (A.card : ℝ)) * (mu - t) := by ring
    rw [this]
    have hBA_diff : (B.card : ℝ) - (A.card : ℝ) ≥ 0 := by
      have hBcard_eq : (B.card : ℝ) = (n : ℝ) - (A.card : ℝ) := by
        have : ((A.card + B.card : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hcard
        push_cast at this; linarith
      have h2 : 2 * (n / 2) ≤ n := by omega
      have hAtimes : 2 * A.card ≤ n := le_trans (by linarith) h2
      have hcast : 2 * (A.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hAtimes
      rw [hBcard_eq]; linarith
    have hmu_t_pos : mu - t ≥ 0 := by linarith
    exact mul_nonneg hBA_diff hmu_t_pos
