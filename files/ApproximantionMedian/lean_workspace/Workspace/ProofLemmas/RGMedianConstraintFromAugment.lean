import Mathlib
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs

open Workspace.Types.CoordinateMedian
open Workspace.ConsistencyTheorem
open Finset

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.RGMedianConstraintFromAugment

theorem RGMedianConstraintFromAugment
    {n d : ℕ} (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hne : Even (n + ⌊c * (n : ℝ)⌋₊))
    (f : Fin d → ℝ) (hf_sum : (∑ j, (f j) ^ (2 : ℝ)) = 1)
    (pred : Fin d → ℝ) (hpred_gp : ∀ j, pred j ≠ 0)
    (s : Fin d → ℝ) (hs_pm : ∀ j, s j = 1 ∨ s j = -1)
    (hs_pos : ∀ j, pred j > 0 → s j = 1) (hs_neg : ∀ j, pred j < 0 → s j = -1)
    (P : Fin n → Fin d → ℝ)
    (hP : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
            (augment P pred (⌊c * (n : ℝ)⌋₊))) :
    ∃ sigma : Fin n → Fin d → ℝ,
      (∀ i j, sigma i j = 1 ∨ sigma i j = -1) ∧
      (∀ i j, P i j > 0 → sigma i j = 1) ∧
      (∀ i j, P i j < 0 → sigma i j = -1) ∧
      (∀ j, ∑ i, sigma i j = -(⌊c * (n : ℝ)⌋₊ : ℝ) * s j) ∧
      (∀ j, (((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card : ℝ) * 2
              = (n : ℝ) - (⌊c * (n : ℝ)⌋₊ : ℝ) * s j) := by
  classical
  set k : ℕ := ⌊c * (n : ℝ)⌋₊ with hk_def
  -- k ≤ n, since c < 1.
  have hk_le_n : k ≤ n := by
    rw [hk_def]
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · subst hn0; simp
    · have hcn_lt : c * (n : ℝ) < (n : ℝ) := by
        have : c * (n : ℝ) < 1 * (n : ℝ) := by
          apply mul_lt_mul_of_pos_right hc1
          exact_mod_cast hn0
        simpa using this
      have hcn_nonneg : 0 ≤ c * (n : ℝ) := mul_nonneg hc0 (by positivity)
      have : (⌊c * (n : ℝ)⌋₊ : ℝ) ≤ c * (n : ℝ) := Nat.floor_le hcn_nonneg
      have hlt : (⌊c * (n : ℝ)⌋₊ : ℝ) < (n : ℝ) := lt_of_le_of_lt this hcn_lt
      have : (⌊c * (n : ℝ)⌋₊ : ℕ) < n := by exact_mod_cast hlt
      omega
  -- Per-coordinate original sets.
  set posSet : Fin d → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => P i j > 0) with hposSet
  set negSet : Fin d → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => P i j < 0) with hnegSet
  set zeroSet : Fin d → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i => P i j = 0) with hzeroSet
  have hpos_mem : ∀ {i j}, i ∈ posSet j ↔ P i j > 0 := by
    intro i j; simp [hposSet]
  have hneg_mem : ∀ {i j}, i ∈ negSet j ↔ P i j < 0 := by
    intro i j; simp [hnegSet]
  have hzero_mem : ∀ {i j}, i ∈ zeroSet j ↔ P i j = 0 := by
    intro i j; simp [hzeroSet]
  -- Augmented "< 0" count.
  have haug_neg_pos_pred : ∀ j, pred j > 0 →
      ((Finset.univ : Finset (Fin (n + k))).filter
        (fun i => augment P pred k i j < 0)).card = (negSet j).card := by
    intro j hpredj
    symm
    apply Finset.card_bij (fun (i : Fin n) _ => (Fin.castAdd k i : Fin (n + k)))
    · intro i hi
      rw [hneg_mem] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [augment, Fin.addCases_left] using hi
    · intro a _ b _ hab
      exact Fin.castAdd_injective _ _ hab
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine Fin.addCases (motive := fun i => (augment P pred k i j < 0) →
        ∃ a, ∃ (_ : a ∈ negSet j), Fin.castAdd k a = i) ?_ ?_ i hi
      · intro a ha
        refine ⟨a, ?_, rfl⟩
        rw [hneg_mem]
        simpa [augment, Fin.addCases_left] using ha
      · intro a ha
        exfalso
        have : pred j < 0 := by simpa [augment, Fin.addCases_right] using ha
        linarith
  have haug_pos_pos_pred : ∀ j, pred j > 0 →
      ((Finset.univ : Finset (Fin (n + k))).filter
        (fun i => augment P pred k i j > 0)).card = (posSet j).card + k := by
    intro j hpredj
    rw [Finset.card_filter]
    rw [Fin.sum_univ_add]
    have hleft : (∑ i : Fin n, if augment P pred k (Fin.castAdd k i) j > 0 then 1 else 0)
        = (posSet j).card := by
      rw [hposSet]
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp [augment, Fin.addCases_left]
    have hright : (∑ i : Fin k, if augment P pred k (Fin.natAdd n i) j > 0 then 1 else 0)
        = k := by
      have : ∀ i : Fin k, (if augment P pred k (Fin.natAdd n i) j > 0 then (1 : ℕ) else 0) = 1 := by
        intro i
        have heq : augment P pred k (Fin.natAdd n i) j = pred j := by
          simp [augment, Fin.addCases_right]
        rw [heq]
        simp [hpredj]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      simp
    rw [hleft, hright]
  -- For pred j < 0.
  have haug_pos_neg_pred : ∀ j, pred j < 0 →
      ((Finset.univ : Finset (Fin (n + k))).filter
        (fun i => augment P pred k i j > 0)).card = (posSet j).card := by
    intro j hpredj
    symm
    apply Finset.card_bij (fun (i : Fin n) _ => (Fin.castAdd k i : Fin (n + k)))
    · intro i hi
      rw [hpos_mem] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [augment, Fin.addCases_left] using hi
    · intro a _ b _ hab
      exact Fin.castAdd_injective _ _ hab
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      refine Fin.addCases (motive := fun i => (augment P pred k i j > 0) →
        ∃ a, ∃ (_ : a ∈ posSet j), Fin.castAdd k a = i) ?_ ?_ i hi
      · intro a ha
        refine ⟨a, ?_, rfl⟩
        rw [hpos_mem]
        simpa [augment, Fin.addCases_left] using ha
      · intro a ha
        exfalso
        have : pred j > 0 := by simpa [augment, Fin.addCases_right] using ha
        linarith
  have haug_neg_neg_pred : ∀ j, pred j < 0 →
      ((Finset.univ : Finset (Fin (n + k))).filter
        (fun i => augment P pred k i j < 0)).card = (negSet j).card + k := by
    intro j hpredj
    rw [Finset.card_filter]
    rw [Fin.sum_univ_add]
    have hleft : (∑ i : Fin n, if augment P pred k (Fin.castAdd k i) j < 0 then 1 else 0)
        = (negSet j).card := by
      rw [hnegSet]
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp [augment, Fin.addCases_left]
    have hright : (∑ i : Fin k, if augment P pred k (Fin.natAdd n i) j < 0 then 1 else 0)
        = k := by
      have : ∀ i : Fin k, (if augment P pred k (Fin.natAdd n i) j < 0 then (1 : ℕ) else 0) = 1 := by
        intro i
        have heq : augment P pred k (Fin.natAdd n i) j = pred j := by
          simp [augment, Fin.addCases_right]
        rw [heq]
        simp [hpredj]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      simp
    rw [hleft, hright]
  -- Disjointness and partition (sign-independent).
  have hpos_neg_disj : ∀ j, Disjoint (posSet j) (negSet j) := by
    intro j; rw [hposSet, hnegSet, Finset.disjoint_filter]
    intros i _ hpi hni; linarith
  have hpos_zero_disj : ∀ j, Disjoint (posSet j) (zeroSet j) := by
    intro j; rw [hposSet, hzeroSet, Finset.disjoint_filter]
    intros i _ hpi hzi; linarith
  have hneg_zero_disj : ∀ j, Disjoint (negSet j) (zeroSet j) := by
    intro j; rw [hnegSet, hzeroSet, Finset.disjoint_filter]
    intros i _ hni hzi; linarith
  have hunion : ∀ j,
      (posSet j) ∪ (negSet j) ∪ (zeroSet j) = (Finset.univ : Finset (Fin n)) := by
    intro j
    apply Finset.eq_univ_of_forall
    intro i
    rcases lt_trichotomy (P i j) 0 with h | h | h
    · apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; right
      exact hneg_mem.mpr h
    · apply Finset.mem_union.mpr; right
      exact hzero_mem.mpr h
    · apply Finset.mem_union.mpr; left
      apply Finset.mem_union.mpr; left
      exact hpos_mem.mpr h
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
  -- Parity: n + k even.
  obtain ⟨w, hw⟩ := hne
  have hnk2 : 2 * ((n + k) / 2) = n + k := by rw [hk_def] at hw ⊢; omega
  -- Per coordinate: define a target count `tcount j` = number of +1 zeros to pick.
  -- tcount = (target+ count) - |posSet|, where target+ = (n - k·s j)/2 as a nat:
  --   s j = 1 -> (n-k)/2 ; s j = -1 -> (n+k)/2.
  -- Build everything per coordinate with a case split on the sign of pred j.
  -- We produce the full sigma via choosing T j ⊆ zeroSet j of the right card.
  -- First, the required nat cardinality bound for T (feasibility) in each case.
  have hexT : ∀ j, ∃ T : Finset (Fin n), T ⊆ zeroSet j ∧
      ((pred j > 0 → T.card = (n - k) / 2 - (posSet j).card) ∧
       (pred j < 0 → T.card = (n + k) / 2 - (posSet j).card)) := by
    intro j
    rcases lt_trichotomy (pred j) 0 with hlt | heq | hgt
    · -- pred j < 0 : target = (n+k)/2 - |posSet|
      have hpos_bd : (posSet j).card ≤ (n + k) / 2 := by
        have h := (hP j).2
        rw [haug_pos_neg_pred j hlt] at h
        exact h
      have hu_le : (n + k) / 2 - (posSet j).card ≤ (zeroSet j).card := by
        have hneg_bd : (negSet j).card + k ≤ (n + k) / 2 := by
          have h := (hP j).1
          rw [haug_neg_neg_pred j hlt] at h
          exact h
        have hsum := hcard_sum j
        omega
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hu_le
      refine ⟨T, hTsub, ?_, ?_⟩
      · intro hh; linarith
      · intro _; exact hTcard
    · exact absurd heq (hpred_gp j)
    · -- pred j > 0 : target = (n-k)/2 - |posSet|
      have hpos_bd : (posSet j).card + k ≤ (n + k) / 2 := by
        have h := (hP j).2
        rw [haug_pos_pos_pred j hgt] at h
        exact h
      have hu_le : (n - k) / 2 - (posSet j).card ≤ (zeroSet j).card := by
        have hneg_bd : (negSet j).card ≤ (n + k) / 2 := by
          have h := (hP j).1
          rw [haug_neg_pos_pred j hgt] at h
          exact h
        have hsum := hcard_sum j
        omega
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hu_le
      refine ⟨T, hTsub, ?_, ?_⟩
      · intro _; exact hTcard
      · intro hh; linarith
  let T : Fin d → Finset (Fin n) := fun j => (hexT j).choose
  have hT_sub : ∀ j, T j ⊆ zeroSet j := fun j => (hexT j).choose_spec.1
  have hT_card_pos : ∀ j, pred j > 0 → (T j).card = (n - k) / 2 - (posSet j).card :=
    fun j => (hexT j).choose_spec.2.1
  have hT_card_neg : ∀ j, pred j < 0 → (T j).card = (n + k) / 2 - (posSet j).card :=
    fun j => (hexT j).choose_spec.2.2
  -- Define the signature.
  refine ⟨fun i j => if P i j > 0 then (1 : ℝ)
                     else if P i j < 0 then (-1 : ℝ)
                     else if i ∈ T j then (1 : ℝ) else (-1 : ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
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
  · -- Sum equals -k·s j per coordinate.
    intro j
    -- general signature-sum value via T-count, in ℝ.
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
    have hpart : (Finset.univ : Finset (Fin n)) = (posSet j ∪ negSet j) ∪ zeroSet j :=
      (hunion j).symm
    have hd1 : Disjoint (posSet j ∪ negSet j) (zeroSet j) := by
      rw [Finset.disjoint_union_left]
      exact ⟨hpos_zero_disj j, hneg_zero_disj j⟩
    have hT_le_zs : (T j).card ≤ (zeroSet j).card := Finset.card_le_card (hT_sub j)
    have hsdiff_real : ((zeroSet j \ T j).card : ℝ) =
        ((zeroSet j).card : ℝ) - ((T j).card : ℝ) := by
      rw [Finset.card_sdiff_of_subset (hT_sub j), Nat.cast_sub hT_le_zs]
    have hd2 : Disjoint (T j) (zeroSet j \ T j) := Finset.disjoint_sdiff
    have hzs_eq : zeroSet j = T j ∪ (zeroSet j \ T j) := by
      rw [Finset.union_sdiff_of_subset (hT_sub j)]
    have hzero_sum :
        ∑ i ∈ zeroSet j, (if P i j > 0 then (1 : ℝ) else if P i j < 0 then -1
              else if i ∈ T j then 1 else -1)
        = ((T j).card : ℝ) - ((zeroSet j \ T j).card : ℝ) := by
      conv_lhs => rw [hzs_eq]
      rw [Finset.sum_union hd2]
      rw [Finset.sum_congr rfl hsigma_zero_in]
      rw [Finset.sum_congr rfl hsigma_zero_out]
      rw [Finset.sum_const, Finset.sum_const]
      simp only [smul_eq_mul, mul_one, mul_neg_one, nsmul_eq_mul]
      ring
    have hsum_val :
        ∑ i, (if P i j > 0 then (1 : ℝ) else if P i j < 0 then -1
              else if i ∈ T j then 1 else -1)
        = ((posSet j).card : ℝ) - ((negSet j).card : ℝ)
          + (((T j).card : ℝ) - ((zeroSet j \ T j).card : ℝ)) := by
      rw [hpart, Finset.sum_union hd1, Finset.sum_union (hpos_neg_disj j)]
      rw [Finset.sum_congr rfl hsigma_pos]
      rw [Finset.sum_congr rfl hsigma_neg]
      rw [hzero_sum]
      rw [Finset.sum_const, Finset.sum_const]
      simp only [smul_eq_mul, mul_one, mul_neg_one, nsmul_eq_mul]
      ring
    rw [hsum_val, hsdiff_real]
    -- Now branch on sign of pred j.
    rcases lt_trichotomy (pred j) 0 with hlt | heq | hgt
    · -- s j = -1 ; sum should be -k·(-1) = k
      have hsj : s j = -1 := hs_neg j hlt
      rw [hsj]
      have hTc := hT_card_neg j hlt
      have hpos_le : (posSet j).card ≤ (n + k) / 2 := by
        have h := (hP j).2
        rw [haug_pos_neg_pred j hlt] at h; exact h
      -- |T| = (n+k)/2 - |posSet| ; |zeroSet| = n - |posSet| - |negSet|
      have hTreal : ((T j).card : ℝ) = (((n + k) / 2 : ℕ) : ℝ) - ((posSet j).card : ℝ) := by
        rw [hTc]; push_cast [Nat.cast_sub hpos_le]; ring
      have hzs_real : ((zeroSet j).card : ℝ) =
          (n : ℝ) - ((posSet j).card : ℝ) - ((negSet j).card : ℝ) := by
        have : ((posSet j).card : ℝ) + ((negSet j).card : ℝ) + ((zeroSet j).card : ℝ) = (n : ℝ) := by
          exact_mod_cast hcard_sum j
        linarith
      have hnk_real : (((n + k) / 2 : ℕ) : ℝ) * 2 = (n : ℝ) + (k : ℝ) := by
        have h2 : (2 : ℝ) * (((n + k) / 2 : ℕ) : ℝ) = ((n + k : ℕ) : ℝ) := by
          exact_mod_cast hnk2
        rw [Nat.cast_add] at h2; linarith
      -- Need: |negSet| relation. From median, |negSet|+k ≤ (n+k)/2 isn't enough; we need exact.
      -- Actually sum = |pos| - |neg| + (2|T| - |zero|). With |T|=(n+k)/2-|pos|, |zero|=n-|pos|-|neg|:
      --   = |pos| - |neg| + (n+k) - 2|pos| - (n - |pos| - |neg|) = |pos| - |neg| + k + |neg| = |pos| ...
      -- recompute: 2|T| - |zero| = (n+k) - 2|pos| - n + |pos| + |neg| = k - |pos| + |neg|
      -- sum = |pos| - |neg| + k - |pos| + |neg| = k. Good, = k = -k·(-1).
      rw [hTreal, hzs_real]
      have hk_real : ((k : ℕ) : ℝ) = (k : ℝ) := rfl
      nlinarith [hnk_real]
    · exact absurd heq (hpred_gp j)
    · -- s j = 1 ; sum should be -k
      have hsj : s j = 1 := hs_pos j hgt
      rw [hsj]
      have hTc := hT_card_pos j hgt
      have hpos_le : (posSet j).card ≤ (n - k) / 2 := by
        have h := (hP j).2
        rw [haug_pos_pos_pred j hgt] at h; omega
      have hTreal : ((T j).card : ℝ) = (((n - k) / 2 : ℕ) : ℝ) - ((posSet j).card : ℝ) := by
        rw [hTc]; push_cast [Nat.cast_sub hpos_le]; ring
      have hzs_real : ((zeroSet j).card : ℝ) =
          (n : ℝ) - ((posSet j).card : ℝ) - ((negSet j).card : ℝ) := by
        have : ((posSet j).card : ℝ) + ((negSet j).card : ℝ) + ((zeroSet j).card : ℝ) = (n : ℝ) := by
          exact_mod_cast hcard_sum j
        linarith
      have hnmk2 : 2 * ((n - k) / 2) = n - k := by omega
      have hnmk_real : (((n - k) / 2 : ℕ) : ℝ) * 2 = (n : ℝ) - (k : ℝ) := by
        have hkn : k ≤ n := hk_le_n
        have h2 : (2 : ℝ) * (((n - k) / 2 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) := by
          exact_mod_cast hnmk2
        have : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hkn]
        linarith
      rw [hTreal, hzs_real]
      nlinarith [hnmk_real]
  · -- Count of +1 signs.
    intro j
    have hset_eq : ((Finset.univ : Finset (Fin n)).filter
        (fun i => (if P i j > 0 then (1 : ℝ) else if P i j < 0 then -1
                   else if i ∈ T j then 1 else -1) = 1))
        = posSet j ∪ T j := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hi
        by_cases h1 : P i j > 0
        · left; exact hpos_mem.mpr h1
        · by_cases h2 : P i j < 0
          · exfalso
            rw [if_neg h1, if_pos h2] at hi
            norm_num at hi
          · by_cases h3 : i ∈ T j
            · right; exact h3
            · exfalso
              rw [if_neg h1, if_neg h2, if_neg h3] at hi
              norm_num at hi
      · intro hi
        rcases hi with hi | hi
        · have h1 : P i j > 0 := hpos_mem.mp hi
          simp [h1]
        · have hz : i ∈ zeroSet j := hT_sub j hi
          have h := hzero_mem.mp hz
          have h1 : ¬ P i j > 0 := by linarith
          have h2 : ¬ P i j < 0 := by linarith
          simp [h1, h2, hi]
    rw [hset_eq]
    have hdisj : Disjoint (posSet j) (T j) := by
      apply Finset.disjoint_left.mpr
      intro i hip hiT
      have hz : i ∈ zeroSet j := hT_sub j hiT
      have hpij : P i j > 0 := hpos_mem.mp hip
      have hzij : P i j = 0 := hzero_mem.mp hz
      linarith
    rw [Finset.card_union_of_disjoint hdisj]
    -- Branch on sign.
    rcases lt_trichotomy (pred j) 0 with hlt | heq | hgt
    · have hsj : s j = -1 := hs_neg j hlt
      rw [hsj]
      have hTc := hT_card_neg j hlt
      have hpos_le : (posSet j).card ≤ (n + k) / 2 := by
        have h := (hP j).2
        rw [haug_pos_neg_pred j hlt] at h; exact h
      rw [hTc]
      have hnk_real : (((n + k) / 2 : ℕ) : ℝ) * 2 = (n : ℝ) + (k : ℝ) := by
        have h2 : (2 : ℝ) * (((n + k) / 2 : ℕ) : ℝ) = ((n + k : ℕ) : ℝ) := by
          exact_mod_cast hnk2
        rw [Nat.cast_add] at h2; linarith
      have hcast : (((posSet j).card + ((n + k) / 2 - (posSet j).card) : ℕ) : ℝ)
          = (((n + k) / 2 : ℕ) : ℝ) := by
        congr 1; omega
      rw [hcast]; push_cast; linarith [hnk_real]
    · exact absurd heq (hpred_gp j)
    · have hsj : s j = 1 := hs_pos j hgt
      rw [hsj]
      have hTc := hT_card_pos j hgt
      have hpos_le : (posSet j).card ≤ (n - k) / 2 := by
        have h := (hP j).2
        rw [haug_pos_pos_pred j hgt] at h; omega
      rw [hTc]
      have hnmk2 : 2 * ((n - k) / 2) = n - k := by omega
      have hnmk_real : (((n - k) / 2 : ℕ) : ℝ) * 2 = (n : ℝ) - (k : ℝ) := by
        have hkn : k ≤ n := hk_le_n
        have h2 : (2 : ℝ) * (((n - k) / 2 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) := by
          exact_mod_cast hnmk2
        have : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by rw [Nat.cast_sub hkn]
        linarith
      have hcast : (((posSet j).card + ((n - k) / 2 - (posSet j).card) : ℕ) : ℝ)
          = (((n - k) / 2 : ℕ) : ℝ) := by
        congr 1; omega
      rw [hcast]; push_cast; linarith [hnmk_real]

end Workspace.ProofLemmas.RGMedianConstraintFromAugment
