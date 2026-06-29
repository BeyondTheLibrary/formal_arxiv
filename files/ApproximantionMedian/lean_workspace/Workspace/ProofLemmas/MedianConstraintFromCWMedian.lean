import Mathlib
import Workspace.Types.CoordinateMedian

open Workspace.Types.CoordinateMedian
open Finset

theorem MedianConstraintFromCWMedian
    {n d : ℕ} (hn_even : Even n) (P : Fin n → Fin d → ℝ)
    (hP : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ)) P) :
    ∃ sigma : Fin n → Fin d → ℝ,
      (∀ i j, sigma i j = 1 ∨ sigma i j = -1) ∧
      (∀ i j, P i j > 0 → sigma i j = 1) ∧
      (∀ i j, P i j < 0 → sigma i j = -1) ∧
      (∀ j, ∑ i, sigma i j = 0) := by
  classical
  -- Per-coordinate sets
  let posSet : Fin d → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => P i j > 0)
  let negSet : Fin d → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => P i j < 0)
  let zeroSet : Fin d → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => P i j = 0)
  have hpos_mem : ∀ {i j}, i ∈ posSet j ↔ P i j > 0 := by
    intro i j
    simp [posSet]
  have hneg_mem : ∀ {i j}, i ∈ negSet j ↔ P i j < 0 := by
    intro i j
    simp [negSet]
  have hzero_mem : ∀ {i j}, i ∈ zeroSet j ↔ P i j = 0 := by
    intro i j
    simp [zeroSet]
  -- Cardinality bounds from hP
  have hpos_le : ∀ j, (posSet j).card ≤ n / 2 := fun j => (hP j).2
  have hneg_le : ∀ j, (negSet j).card ≤ n / 2 := fun j => (hP j).1
  -- Disjointness
  have hpos_neg_disj : ∀ j, Disjoint (posSet j) (negSet j) := by
    intro j; rw [Finset.disjoint_filter]
    intros i _ hpi hni; linarith
  have hpos_zero_disj : ∀ j, Disjoint (posSet j) (zeroSet j) := by
    intro j; rw [Finset.disjoint_filter]
    intros i _ hpi hzi; linarith
  have hneg_zero_disj : ∀ j, Disjoint (negSet j) (zeroSet j) := by
    intro j; rw [Finset.disjoint_filter]
    intros i _ hni hzi; linarith
  -- The three sets partition univ.
  have hunion : ∀ j,
      (posSet j) ∪ (negSet j) ∪ (zeroSet j) = (Finset.univ : Finset (Fin n)) := by
    intro j
    apply Finset.eq_univ_of_forall
    intro i
    rcases lt_trichotomy (P i j) 0 with h | h | h
    · -- i ∈ negSet j
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      right
      exact hneg_mem.mpr h
    · -- i ∈ zeroSet j
      apply Finset.mem_union.mpr
      right
      exact hzero_mem.mpr h
    · -- i ∈ posSet j
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      exact hpos_mem.mpr h
  -- Cardinality sum: |posSet| + |negSet| + |zeroSet| = n
  have hcard_sum : ∀ j, (posSet j).card + (negSet j).card + (zeroSet j).card = n := by
    intro j
    have hd1 : Disjoint (posSet j ∪ negSet j) (zeroSet j) := by
      rw [Finset.disjoint_union_left]
      exact ⟨hpos_zero_disj j, hneg_zero_disj j⟩
    have h1 : ((posSet j ∪ negSet j) ∪ zeroSet j).card =
        (posSet j ∪ negSet j).card + (zeroSet j).card :=
      Finset.card_union_of_disjoint hd1
    have h2 : (posSet j ∪ negSet j).card = (posSet j).card + (negSet j).card :=
      Finset.card_union_of_disjoint (hpos_neg_disj j)
    have h3 : ((posSet j ∪ negSet j) ∪ zeroSet j).card = n := by
      rw [hunion j]; simp
    omega
  -- We need to choose a subset T j ⊆ zeroSet j with |T j| = n/2 - |posSet j|.
  have hu_le : ∀ j, n / 2 - (posSet j).card ≤ (zeroSet j).card := by
    intro j
    have hsum := hcard_sum j
    have hneg := hneg_le j
    omega
  have hexT : ∀ j, ∃ T : Finset (Fin n), T ⊆ zeroSet j ∧
      T.card = n / 2 - (posSet j).card := by
    intro j
    exact Finset.exists_subset_card_eq (hu_le j)
  let T : Fin d → Finset (Fin n) := fun j => (hexT j).choose
  have hT_sub : ∀ j, T j ⊆ zeroSet j := fun j => (hexT j).choose_spec.1
  have hT_card : ∀ j, (T j).card = n / 2 - (posSet j).card :=
    fun j => (hexT j).choose_spec.2
  -- Define the signature.
  refine ⟨fun i j => if P i j > 0 then (1 : ℝ)
                     else if P i j < 0 then (-1 : ℝ)
                     else if i ∈ T j then (1 : ℝ) else (-1 : ℝ), ?_, ?_, ?_, ?_⟩
  · -- sigma values are ±1
    intro i j
    by_cases h1 : P i j > 0
    · left; simp [h1]
    · by_cases h2 : P i j < 0
      · right; simp [h1, h2]
      · by_cases h3 : i ∈ T j
        · left; simp [h1, h2, h3]
        · right; simp [h1, h2, h3]
  · intro i j hij; simp [hij]
  · intro i j hij
    have h1 : ¬ P i j > 0 := by linarith
    simp [h1, hij]
  · -- Sum equals zero per coordinate
    intro j
    have hsigma_pos : ∀ i ∈ posSet j,
        (if P i j > 0 then (1 : ℝ) else if P i j < 0 then -1 else if i ∈ T j then 1 else -1) = 1 := by
      intros i hi
      have h := hpos_mem.mp hi
      simp [h]
    have hsigma_neg : ∀ i ∈ negSet j,
        (if P i j > 0 then (1 : ℝ) else if P i j < 0 then -1 else if i ∈ T j then 1 else -1) = -1 := by
      intros i hi
      have h := hneg_mem.mp hi
      have h1 : ¬ P i j > 0 := by linarith
      simp [h1, h]
    have hsigma_zero_in : ∀ i ∈ T j,
        (if P i j > 0 then (1 : ℝ) else if P i j < 0 then -1 else if i ∈ T j then 1 else -1) = 1 := by
      intros i hT
      have hi : i ∈ zeroSet j := hT_sub j hT
      have h := hzero_mem.mp hi
      have h1 : ¬ P i j > 0 := by linarith
      have h2 : ¬ P i j < 0 := by linarith
      simp [h1, h2, hT]
    have hsigma_zero_out : ∀ i ∈ zeroSet j \ T j,
        (if P i j > 0 then (1 : ℝ) else if P i j < 0 then -1 else if i ∈ T j then 1 else -1) = -1 := by
      intros i hi
      have hi1 : i ∈ zeroSet j := (Finset.mem_sdiff.mp hi).1
      have hi2 : i ∉ T j := (Finset.mem_sdiff.mp hi).2
      have h := hzero_mem.mp hi1
      have h1 : ¬ P i j > 0 := by linarith
      have h2 : ¬ P i j < 0 := by linarith
      simp [h1, h2, hi2]
    -- Express sum over univ as sum over the partition.
    have hpart : (Finset.univ : Finset (Fin n)) = (posSet j ∪ negSet j) ∪ zeroSet j :=
      (hunion j).symm
    have hd1 : Disjoint (posSet j ∪ negSet j) (zeroSet j) := by
      rw [Finset.disjoint_union_left]
      exact ⟨hpos_zero_disj j, hneg_zero_disj j⟩
    rw [hpart, Finset.sum_union hd1, Finset.sum_union (hpos_neg_disj j)]
    rw [Finset.sum_congr rfl hsigma_pos]
    rw [Finset.sum_congr rfl hsigma_neg]
    have hd2 : Disjoint (T j) (zeroSet j \ T j) := Finset.disjoint_sdiff
    have hzs_eq : zeroSet j = T j ∪ (zeroSet j \ T j) := by
      rw [Finset.union_sdiff_of_subset (hT_sub j)]
    rw [hzs_eq, Finset.sum_union hd2]
    rw [Finset.sum_congr rfl hsigma_zero_in]
    rw [Finset.sum_congr rfl hsigma_zero_out]
    rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.sum_const]
    -- Goal: |posSet| • 1 + |negSet| • (-1) + (|T j| • 1 + |zeroSet \ T j| • (-1)) = 0
    simp only [smul_eq_mul, mul_one, mul_neg_one, nsmul_eq_mul]
    -- Now arithmetic identity in ℝ
    have hT_le_zs : (T j).card ≤ (zeroSet j).card := Finset.card_le_card (hT_sub j)
    have hsdiff_card : (zeroSet j \ T j).card = (zeroSet j).card - (T j).card :=
      Finset.card_sdiff_of_subset (hT_sub j)
    obtain ⟨k, hk⟩ := hn_even
    have hn2 : n / 2 = k := by omega
    have hcard_sum_j := hcard_sum j
    have hT_card_j := hT_card j
    have hpos_le_j := hpos_le j
    -- Cast everything carefully
    have hT_real : ((T j).card : ℝ) = ((n / 2 : ℕ) : ℝ) - ((posSet j).card : ℝ) := by
      rw [hT_card_j]
      push_cast [Nat.cast_sub hpos_le_j]
      ring
    have hzs_real : ((zeroSet j).card : ℝ) =
        (n : ℝ) - ((posSet j).card : ℝ) - ((negSet j).card : ℝ) := by
      have : ((posSet j).card : ℝ) + ((negSet j).card : ℝ) + ((zeroSet j).card : ℝ) = (n : ℝ) := by
        exact_mod_cast hcard_sum_j
      linarith
    have hsdiff_real : ((zeroSet j \ T j).card : ℝ) =
        ((zeroSet j).card : ℝ) - ((T j).card : ℝ) := by
      have h1 : ((zeroSet j \ T j).card : ℝ) = (((zeroSet j).card - (T j).card : ℕ) : ℝ) := by
        rw [hsdiff_card]
      rw [h1, Nat.cast_sub hT_le_zs]
    have h2n : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
      have hh : (n : ℕ) = 2 * (n / 2) := by omega
      exact_mod_cast hh
    rw [hsdiff_real, hT_real, hzs_real]
    linarith
