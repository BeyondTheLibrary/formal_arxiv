import Mathlib

open Classical

theorem MedianConstraintToSumX
    {n d : ℕ} (hn_even : Even n) (q : ℝ)
    (f : Fin d → ℝ) (hf_nn : ∀ j, 0 ≤ f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma : Fin n → Fin d → ℝ)
    (hsigma_pm : ∀ i j, sigma i j = 1 ∨ sigma i j = -1)
    (hsigma_zero : ∀ j, ∑ i, sigma i j = 0) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => sigma i j = 1), (f j) ^ q) = (n : ℝ) / 2 := by
  classical
  -- Key combinatorial lemma: for each j, the number of i with sigma i j = 1 is n/2.
  have card_eq : ∀ j : Fin d,
      ((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card * 2 = n := by
    intro j
    -- Split the universe by sigma i j
    set Spos := (Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1) with hSpos
    set Sneg := (Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = -1) with hSneg
    -- Spos ∪ Sneg = univ and disjoint
    have hdisj : Disjoint Spos Sneg := by
      rw [Finset.disjoint_filter]
      intro i _ h1 h2
      rw [h1] at h2
      norm_num at h2
    have hunion : Spos ∪ Sneg = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      rcases hsigma_pm i j with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    -- Cardinalities sum to n
    have hcard_sum : Spos.card + Sneg.card = n := by
      have h1 : (Spos ∪ Sneg).card = Spos.card + Sneg.card :=
        Finset.card_union_of_disjoint hdisj
      rw [hunion] at h1
      simp at h1
      linarith
    -- Sum of sigma over univ
    have hsum := hsigma_zero j
    -- Split sum over Spos ∪ Sneg
    have hsum_split : ∑ i, sigma i j = ∑ i ∈ Spos, sigma i j + ∑ i ∈ Sneg, sigma i j := by
      rw [← Finset.sum_union hdisj, hunion]
    -- On Spos, sigma i j = 1; on Sneg, sigma i j = -1.
    have hsum_pos : ∑ i ∈ Spos, sigma i j = (Spos.card : ℝ) := by
      rw [Finset.sum_congr rfl (fun i hi => by
        have := (Finset.mem_filter.mp hi).2
        exact this)]
      simp
    have hsum_neg : ∑ i ∈ Sneg, sigma i j = -(Sneg.card : ℝ) := by
      rw [Finset.sum_congr rfl (fun i hi => by
        have := (Finset.mem_filter.mp hi).2
        exact this)]
      simp
    rw [hsum_split, hsum_pos, hsum_neg] at hsum
    -- Now: Spos.card - Sneg.card = 0 and Spos.card + Sneg.card = n.
    have hcard_eq : (Spos.card : ℝ) = (Sneg.card : ℝ) := by linarith
    have hcard_eq_nat : Spos.card = Sneg.card := by exact_mod_cast hcard_eq
    rw [hcard_eq_nat] at hcard_sum
    omega
  -- Now use this to compute the sum.
  have step1 :
      (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin d)).filter (fun j => sigma i j = 1), (f j) ^ q) =
      ∑ i, ∑ j, (if sigma i j = 1 then (f j) ^ q else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_filter]
  rw [step1]
  rw [Finset.sum_comm]
  -- Now: ∑ j, ∑ i, (if sigma i j = 1 then (f j) ^ q else 0) = (n : ℝ) / 2
  have step2 : ∀ j : Fin d,
      (∑ i, (if sigma i j = 1 then (f j) ^ q else 0)) =
      (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ) * (f j) ^ q := by
    intro j
    rw [← Finset.sum_filter]
    rw [Finset.sum_const]
    ring
  simp_rw [step2]
  -- Now: ∑ j, (filter card : ℝ) * (f j)^q = n / 2
  have step3 : ∀ j : Fin d,
      (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ) =
      (n : ℝ) / 2 := by
    intro j
    have := card_eq j
    have hnpos : (2 : ℝ) ≠ 0 := by norm_num
    field_simp
    have : (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card * 2 : ℕ) = n := this
    have hcast : (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ) * 2 = (n : ℝ) := by
      exact_mod_cast this
    linarith
  simp_rw [step3]
  -- Now: ∑ j, (n/2) * (f j)^q = n/2
  rw [← Finset.mul_sum]
  rw [hf_sum]
  ring
