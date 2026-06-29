import Mathlib
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs

open Workspace.Types.CoordinateMedian
open Workspace.ConsistencyTheorem
open Finset

namespace Workspace.ProofLemmas.CGMedianConstraintFromAugment

/-- **CGMedianConstraintFromAugment** (prediction.tex line 30, `eq:consistency
main`; consistency analog of `MedianConstraintFromCWMedian`).  Gap (i).

Normalized setting: `m = 0`, `f j > 0` for all `j`, `‖f‖₂ = 1` (i.e.
`∑ⱼ (fⱼ)² = 1`), and `n + ⌊cn⌋` even.  If `0` is a coordinate-wise median of
`augment P f ⌊cn⌋` (the instance `P` with `⌊cn⌋` extra agents all at `f`), then
there is a signature assignment `σ : Fin n → Fin d → {−1,+1}` consistent with the
signs of `P` such that for every coordinate `j`,
`∑_{i∈[n]} σ(pᵢ) j = −⌊cn⌋`.
Equivalently, for every `j`, `#{i : σⱼ(pᵢ) = +1} = (n − ⌊cn⌋)/2`. -/
theorem CGMedianConstraintFromAugment
    {n d : ℕ} (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hne : Even (n + ⌊c * (n : ℝ)⌋₊))
    (f : Fin d → ℝ) (hf_pos : ∀ j, 0 < f j) (hf_sum : (∑ j, (f j) ^ (2 : ℝ)) = 1)
    (P : Fin n → Fin d → ℝ)
    (hP : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
            (augment P f (⌊c * (n : ℝ)⌋₊))) :
    ∃ sigma : Fin n → Fin d → ℝ,
      (∀ i j, sigma i j = 1 ∨ sigma i j = -1) ∧
      (∀ i j, P i j > 0 → sigma i j = 1) ∧
      (∀ i j, P i j < 0 → sigma i j = -1) ∧
      (∀ j, ∑ i, sigma i j = -(⌊c * (n : ℝ)⌋₊ : ℝ)) ∧
      (∀ j, ((Finset.univ : Finset (Fin n)).filter (fun i => sigma i j = 1)).card * 2
              = n - ⌊c * (n : ℝ)⌋₊) := by
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
  -- Relate augmented filter cardinalities to original ones.
  -- Augmented "< 0" count = |negSet j|.
  have haug_neg : ∀ j,
      ((Finset.univ : Finset (Fin (n + k))).filter
        (fun i => augment P f k i j < 0)).card = (negSet j).card := by
    intro j
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
      -- i : Fin (n+k); show it is a castAdd of some j' with P j' j < 0
      refine Fin.addCases (motive := fun i => (augment P f k i j < 0) →
        ∃ a, ∃ (_ : a ∈ negSet j), Fin.castAdd k a = i) ?_ ?_ i hi
      · intro a ha
        refine ⟨a, ?_, rfl⟩
        rw [hneg_mem]
        simpa [augment, Fin.addCases_left] using ha
      · intro a ha
        exfalso
        have : f j < 0 := by simpa [augment, Fin.addCases_right] using ha
        linarith [hf_pos j]
  -- Augmented "> 0" count = |posSet j| + k.
  have haug_pos : ∀ j,
      ((Finset.univ : Finset (Fin (n + k))).filter
        (fun i => augment P f k i j > 0)).card = (posSet j).card + k := by
    intro j
    -- card = ∑_{i:Fin(n+k)} indicator, split via Fin.sum_univ_add.
    rw [Finset.card_filter]
    rw [Fin.sum_univ_add]
    have hleft : (∑ i : Fin n, if augment P f k (Fin.castAdd k i) j > 0 then 1 else 0)
        = (posSet j).card := by
      rw [hposSet]
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp [augment, Fin.addCases_left]
    have hright : (∑ i : Fin k, if augment P f k (Fin.natAdd n i) j > 0 then 1 else 0)
        = k := by
      have : ∀ i : Fin k, (if augment P f k (Fin.natAdd n i) j > 0 then (1 : ℕ) else 0) = 1 := by
        intro i
        have : augment P f k (Fin.natAdd n i) j = f j := by
          simp [augment, Fin.addCases_right]
        rw [this]
        simp [hf_pos j]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      simp
    rw [hleft, hright]
  -- Median inequalities, transported to the original sets.
  have hneg_le : ∀ j, (negSet j).card ≤ (n + k) / 2 := by
    intro j
    have h := (hP j).1
    rw [haug_neg j] at h
    exact h
  have hpos_k_le : ∀ j, (posSet j).card + k ≤ (n + k) / 2 := by
    intro j
    have h := (hP j).2
    rw [haug_pos j] at h
    exact h
  -- Disjointness of the three original sets.
  have hpos_neg_disj : ∀ j, Disjoint (posSet j) (negSet j) := by
    intro j; rw [hposSet, hnegSet, Finset.disjoint_filter]
    intros i _ hpi hni; linarith
  have hpos_zero_disj : ∀ j, Disjoint (posSet j) (zeroSet j) := by
    intro j; rw [hposSet, hzeroSet, Finset.disjoint_filter]
    intros i _ hpi hzi; linarith
  have hneg_zero_disj : ∀ j, Disjoint (negSet j) (zeroSet j) := by
    intro j; rw [hnegSet, hzeroSet, Finset.disjoint_filter]
    intros i _ hni hzi; linarith
  -- The three sets partition univ.
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
  -- Parity facts from `Even (n + k)`.
  obtain ⟨w, hw⟩ := hne
  have hnk2 : 2 * ((n + k) / 2) = n + k := by omega
  have hnmk2 : 2 * ((n - k) / 2) = n - k := by omega
  -- The target balance: choose (n-k)/2 - |posSet| zeros to be +1.
  have hu_le : ∀ j, (n - k) / 2 - (posSet j).card ≤ (zeroSet j).card := by
    intro j
    have hsum := hcard_sum j
    have hneg := hneg_le j
    omega
  have hexT : ∀ j, ∃ T : Finset (Fin n), T ⊆ zeroSet j ∧
      T.card = (n - k) / 2 - (posSet j).card := by
    intro j
    exact Finset.exists_subset_card_eq (hu_le j)
  let T : Fin d → Finset (Fin n) := fun j => (hexT j).choose
  have hT_sub : ∀ j, T j ⊆ zeroSet j := fun j => (hexT j).choose_spec.1
  have hT_card : ∀ j, (T j).card = (n - k) / 2 - (posSet j).card :=
    fun j => (hexT j).choose_spec.2
  -- Define the signature.
  refine ⟨fun i j => if P i j > 0 then (1 : ℝ)
                     else if P i j < 0 then (-1 : ℝ)
                     else if i ∈ T j then (1 : ℝ) else (-1 : ℝ), ?_, ?_, ?_, ?_, ?_⟩
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
  · -- Sum equals -k per coordinate.
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
    simp only [smul_eq_mul, mul_one, mul_neg_one, nsmul_eq_mul]
    have hT_le_zs : (T j).card ≤ (zeroSet j).card := Finset.card_le_card (hT_sub j)
    have hsdiff_card : (zeroSet j \ T j).card = (zeroSet j).card - (T j).card :=
      Finset.card_sdiff_of_subset (hT_sub j)
    have hcard_sum_j := hcard_sum j
    have hT_card_j := hT_card j
    have hpos_le_j : (posSet j).card ≤ (n - k) / 2 := by
      have hpk := hpos_k_le j
      omega
    have hT_real : ((T j).card : ℝ) = (((n - k) / 2 : ℕ) : ℝ) - ((posSet j).card : ℝ) := by
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
    have hnmk_real : (((n - k) / 2 : ℕ) : ℝ) * 2 = (n : ℝ) - (k : ℝ) := by
      have hkn : k ≤ n := hk_le_n
      have : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
        rw [Nat.cast_sub hkn]
      have h2 : (2 : ℝ) * (((n - k) / 2 : ℕ) : ℝ) = ((n - k : ℕ) : ℝ) := by
        have := hnmk2
        exact_mod_cast this
      linarith
    rw [hsdiff_real, hT_real, hzs_real]
    have hkn_real : ((k : ℕ) : ℝ) = (k : ℝ) := rfl
    linarith
  · -- Count of +1 signs equals (n-k)/2.
    intro j
    -- The +1 set is exactly posSet j ∪ T j.
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
    rw [hT_card j]
    have hpos_le_j : (posSet j).card ≤ (n - k) / 2 := by
      have hpk := hpos_k_le j
      omega
    omega

end Workspace.ProofLemmas.CGMedianConstraintFromAugment
