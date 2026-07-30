import Mathlib
import Workspace.Types.DiscriminantsClassNumber

/-!
# Counting integral ideals of bounded norm

This file carries out everything in `IdealCountByNormBound` except the combinatorial
ideal-to-divisor-tuple comparison, which is provided separately by
`Workspace.ProofLemmas.IdealCountInjection`.

* `D n m` — the `n`-tuples of positive naturals with product at most `m`;
* `card_D_le` — **`#(D n m) ≤ 2ⁿ m²`**, proved by induction on `n` by splitting off the first
  coordinate and using `∑_{c ≤ m} 1/c² ≤ 2`.  (The usual `X(log X)^{n-1}/(n-1)!` bound is not
  needed: the crude `2ⁿ X²` already beats `max{2, rd}^{Cn}` because the Minkowski bound itself is
  at most `max{2, rd}^{3n/2}`.)
* `MB_le` — **`MB K ≤ max{2, rd K} ^ (3n/2)`**, from `(4/π)^{r₂} ≤ 2ⁿ`, `n!/nⁿ ≤ 1` and
  `√|D_K| = rd(K)^{n/2}`;
* `idealCount_bound_of_inj` — combining the two: given the ideal-to-tuple injection, the number of
  nonzero ideals of norm at most `MB K` is at most `max{2, rd K} ^ (4n)`.
-/

open Finset
open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.IdealNormCount

namespace DivisorCount

/-- Tuples of positive naturals of length `n` with product at most `m`. -/
def D (n m : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 m)).filter (fun a => ∏ i, a i ≤ m)

theorem mem_D {n m : ℕ} {a : Fin n → ℕ} :
    a ∈ D n m ↔ (∀ i, 1 ≤ a i ∧ a i ≤ m) ∧ ∏ i, a i ≤ m := by
  simp [D, Fintype.mem_piFinset, Finset.mem_Icc]

/-- The membership condition simplifies: for positive entries with product `≤ m`, each entry is
automatically `≤ m`. -/
theorem mem_D_iff {n m : ℕ} (hm : 1 ≤ m) {a : Fin n → ℕ} :
    a ∈ D n m ↔ (∀ i, 1 ≤ a i) ∧ ∏ i, a i ≤ m := by
  rw [mem_D]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => (h1 i).1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨h1 i, ?_⟩, h2⟩
    calc a i ≤ ∏ j, a j := Finset.single_le_prod' (fun j _ => h1 j) (Finset.mem_univ i)
      _ ≤ m := h2

/-- `∑_{c=1}^{m} 1/c² ≤ 2 - 1/m` for `m ≥ 1`. -/
theorem sum_inv_sq_le' : ∀ m : ℕ, 1 ≤ m →
    ∑ c ∈ Finset.Icc 1 m, (1 : ℝ) / (c : ℝ) ^ 2 ≤ 2 - 1 / (m : ℝ) := by
  intro m
  induction m with
  | zero => omega
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num
      · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) - 1 / (((k + 1 : ℕ)) : ℝ) := by
          push_cast
          rw [div_sub_div _ _ (ne_of_gt hk0) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          ring_nf
          nlinarith
        linarith [ih hk]

/-- `∑_{c=1}^{m} 1/c² ≤ 2`. -/
theorem sum_inv_sq_le (m : ℕ) : ∑ c ∈ Finset.Icc 1 m, (1 : ℝ) / (c : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h := sum_inv_sq_le' m hm
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    linarith

/-- Splitting off the first coordinate. -/
theorem card_D_succ (n m : ℕ) (hm : 1 ≤ m) :
    (D (n + 1) m).card = ∑ c ∈ Finset.Icc 1 m, (D n (m / c)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => a 0) (t := Finset.Icc 1 m) ?first]
  case first =>
    intro a ha
    simp only [Finset.mem_coe] at ha
    rw [mem_D_iff hm] at ha
    simp only [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨ha.1 0, le_trans (Finset.single_le_prod' (fun j _ => ha.1 j) (Finset.mem_univ 0)) ha.2⟩
  refine Finset.sum_congr rfl ?_
  intro c hc
  simp only [Finset.mem_Icc] at hc
  have hc0 : 0 < c := hc.1
  refine Finset.card_bij' (fun a _ => Fin.tail a) (fun b _ => Fin.cons c b) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨haD, ha0⟩ := ha
    rw [mem_D_iff hm] at haD
    rw [mem_D_iff (Nat.one_le_div_iff hc0 |>.mpr hc.2)]
    refine ⟨fun i => haD.1 i.succ, ?_⟩
    have hprod : ∏ i : Fin (n + 1), a i = a 0 * ∏ i : Fin n, a i.succ := Fin.prod_univ_succ a
    rw [Nat.le_div_iff_mul_le hc0]
    have := haD.2
    rw [hprod, ha0] at this
    calc (∏ i : Fin n, Fin.tail a i) * c = c * ∏ i : Fin n, a i.succ := by
          simp [Fin.tail, mul_comm]
      _ ≤ m := this
  · intro b hb
    rw [mem_D_iff (Nat.one_le_div_iff hc0 |>.mpr hc.2)] at hb
    simp only [Finset.mem_filter]
    refine ⟨?_, by simp⟩
    rw [mem_D_iff hm]
    constructor
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hc0
      · intro j; simpa using hb.1 j
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      calc c * ∏ i : Fin n, b i ≤ c * (m / c) := by
            exact Nat.mul_le_mul_left c hb.2
        _ ≤ m := Nat.mul_div_le m c
  · intro a ha
    simp only [Finset.mem_filter] at ha
    show Fin.cons c (Fin.tail a) = a
    rw [show c = a 0 from ha.2.symm]
    exact Fin.cons_self_tail a
  · intro b _
    funext i
    simp [Fin.tail]

/-- **Divisor-tuple count.** The number of `n`-tuples of positive naturals with product at most `m`
is at most `2ⁿ m²`. -/
theorem card_D_le (n : ℕ) : ∀ m : ℕ, 1 ≤ m → ((D n m).card : ℝ) ≤ 2 ^ n * (m : ℝ) ^ 2 := by
  induction n with
  | zero =>
      intro m hm
      have : D 0 m = Finset.univ := by
        ext a
        simp only [mem_D_iff hm, Finset.mem_univ, iff_true]
        exact ⟨fun i => i.elim0, by simpa using hm⟩
      rw [this]
      have hcard : (Finset.univ : Finset (Fin 0 → ℕ)).card = 1 := by simp
      rw [hcard]
      have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      norm_num
      nlinarith
  | succ n ih =>
      intro m hm
      rw [card_D_succ n m hm]
      push_cast
      have hstep : ∀ c ∈ Finset.Icc 1 m,
          (((D n (m / c)).card : ℝ)) ≤ 2 ^ n * ((m : ℝ) / (c : ℝ)) ^ 2 := by
        intro c hc
        simp only [Finset.mem_Icc] at hc
        have hc0 : 0 < c := hc.1
        have h1 : ((D n (m / c)).card : ℝ) ≤ 2 ^ n * ((m / c : ℕ) : ℝ) ^ 2 :=
          ih (m / c) (Nat.one_le_div_iff hc0 |>.mpr hc.2)
        have h2 : ((m / c : ℕ) : ℝ) ≤ (m : ℝ) / (c : ℝ) := Nat.cast_div_le
        have h3 : (0 : ℝ) ≤ ((m / c : ℕ) : ℝ) := Nat.cast_nonneg _
        calc ((D n (m / c)).card : ℝ) ≤ 2 ^ n * ((m / c : ℕ) : ℝ) ^ 2 := h1
          _ ≤ 2 ^ n * ((m : ℝ) / (c : ℝ)) ^ 2 := by
              have hsq : ((m / c : ℕ) : ℝ) ^ 2 ≤ ((m : ℝ) / (c : ℝ)) ^ 2 := by
                gcongr
              nlinarith [pow_nonneg (le_of_lt (show (0:ℝ) < 2 from by norm_num)) n]
      calc (∑ c ∈ Finset.Icc 1 m, ((D n (m / c)).card : ℝ))
          ≤ ∑ c ∈ Finset.Icc 1 m, 2 ^ n * ((m : ℝ) / (c : ℝ)) ^ 2 := Finset.sum_le_sum hstep
        _ = 2 ^ n * (m : ℝ) ^ 2 * ∑ c ∈ Finset.Icc 1 m, (1 : ℝ) / (c : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [div_pow]
            ring
        _ ≤ 2 ^ n * (m : ℝ) ^ 2 * 2 := by
            have hpos : (0 : ℝ) ≤ 2 ^ n * (m : ℝ) ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left (sum_inv_sq_le m) hpos
        _ = 2 ^ (n + 1) * (m : ℝ) ^ 2 := by ring

end DivisorCount

section Arithmetic

open scoped NumberField
open DivisorCount

/-- The Minkowski bound appearing in the statement. -/
noncomputable def MB (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
    ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
      Real.sqrt |(NumberField.discr K : ℝ)|)

/-- `MB K ≤ max 2 (rootDiscriminant K) ^ ((3 / 2) * n)`. -/
theorem MB_le (K : Type) [Field K] [NumberField K] :
    MB K ≤ (max 2 (rootDiscriminant K)) ^ ((3 / 2 : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  set n := Module.finrank ℚ K with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  set R := max 2 (rootDiscriminant K) with hR
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR2
  have hD0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  -- `√|D| = rd ^ (n/2)`
  have hsqrt : Real.sqrt |(NumberField.discr K : ℝ)| = (rootDiscriminant K) ^ ((n : ℝ) / 2) := by
    rw [rootDiscriminant, ← Real.rpow_mul (le_of_lt hD0), Real.sqrt_eq_rpow]
    congr 1
    field_simp
    exact (div_self (ne_of_gt hnR)).symm
  have hrd0 : (0 : ℝ) ≤ rootDiscriminant K := Real.rpow_nonneg (le_of_lt hD0) _
  have hpi : (4 : ℝ) / Real.pi ≤ 2 := by
    have h3 := Real.pi_gt_three
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  have hr2 : NumberField.InfinitePlace.nrComplexPlaces K ≤ n := by
    have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hstep1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤ R ^ (n : ℝ) := by
    have h1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K
        ≤ R ^ NumberField.InfinitePlace.nrComplexPlaces K := by
      gcongr <;> first | positivity | linarith
    have h2 : R ^ NumberField.InfinitePlace.nrComplexPlaces K ≤ R ^ n := by
      gcongr <;> first | positivity | linarith
    calc (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤ R ^ n := le_trans h1 h2
      _ = R ^ (n : ℝ) := (Real.rpow_natCast R n).symm
  have hfact : ((Nat.factorial n : ℝ) / (n : ℝ) ^ n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le_pow n
  have hsq : Real.sqrt |(NumberField.discr K : ℝ)| ≤ R ^ ((n : ℝ) / 2) := by
    rw [hsqrt]
    exact Real.rpow_le_rpow hrd0 (le_max_right _ _) (by positivity)
  have hfact0 : (0 : ℝ) ≤ (Nat.factorial n : ℝ) / (n : ℝ) ^ n := by positivity
  calc MB K = (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Nat.factorial n : ℝ) / (n : ℝ) ^ n) * Real.sqrt |(NumberField.discr K : ℝ)|) := rfl
    _ ≤ R ^ (n : ℝ) * (1 * R ^ ((n : ℝ) / 2)) := by
        gcongr <;>
          first | positivity | exact Real.sqrt_nonneg _ | linarith
    _ = R ^ ((3 / 2 : ℝ) * (n : ℝ)) := by
        rw [one_mul, ← Real.rpow_add hR0]
        ring_nf

/-- **Main arithmetic assembly.**  Given the ideal-to-divisor-tuple injection, the number of
nonzero ideals of norm at most the Minkowski bound is at most `max{2, rd(K)} ^ (4·[K:ℚ])`. -/
theorem idealCount_bound_of_inj
    (hinj : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ),
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
        ≤ (D (Module.finrank ℚ K) m).card)
    (K : Type) [Field K] [NumberField K] :
    (Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB K} : ℝ)
      ≤ (max 2 (rootDiscriminant K)) ^ (4 * (Module.finrank ℚ K : ℝ)) := by
  set n := Module.finrank ℚ K with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  set R := max 2 (rootDiscriminant K) with hR
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR2
  have hD0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hMB0 : (0 : ℝ) ≤ MB K := by
    rw [MB]
    have : (0 : ℝ) ≤ 4 / Real.pi := by positivity
    positivity
  set m : ℕ := ⌊MB K⌋₊ with hm
  -- rewrite the index set
  have hset : Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB K}
      = Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun I => ?_)
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, le_trans (by exact_mod_cast h2) (Nat.floor_le hMB0)⟩
  rw [hset]
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- no ideals at all
    have hempty : IsEmpty {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} := by
      constructor
      rintro ⟨I, hI, hIn⟩
      rw [hm0, Nat.le_zero, Ideal.absNorm_eq_zero_iff] at hIn
      exact hI hIn
    rw [Nat.card_eq_zero.mpr (Or.inl hempty)]
    simp only [Nat.cast_zero]
    positivity
  · have hcard : (Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} : ℝ)
        ≤ ((D n m).card : ℝ) := by exact_mod_cast hinj K m
    have hDbd : ((D n m).card : ℝ) ≤ 2 ^ n * (m : ℝ) ^ 2 := card_D_le n m hm1
    have hmMB : (m : ℝ) ≤ MB K := Nat.floor_le hMB0
    have h2R : (2 : ℝ) ^ n ≤ R ^ (n : ℝ) := by
      rw [Real.rpow_natCast R n]
      gcongr <;> first | positivity | linarith
    have hMBsq : (m : ℝ) ^ 2 ≤ R ^ (3 * (n : ℝ)) := by
      have h1 : (m : ℝ) ^ 2 ≤ (MB K) ^ 2 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        nlinarith
      have h2 : (MB K) ^ 2 ≤ (R ^ ((3 / 2 : ℝ) * (n : ℝ))) ^ 2 := by
        have := MB_le K
        nlinarith [Real.rpow_nonneg (le_of_lt hR0) ((3 / 2 : ℝ) * (n : ℝ))]
      have h3 : (R ^ ((3 / 2 : ℝ) * (n : ℝ))) ^ 2 = R ^ (3 * (n : ℝ)) := by
        rw [← Real.rpow_natCast (R ^ ((3 / 2 : ℝ) * (n : ℝ))) 2, ← Real.rpow_mul (le_of_lt hR0)]
        norm_num
        ring_nf
      linarith [h1, h2, h3.le, h3.ge]
    calc (Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} : ℝ)
        ≤ 2 ^ n * (m : ℝ) ^ 2 := le_trans hcard hDbd
      _ ≤ R ^ (n : ℝ) * R ^ (3 * (n : ℝ)) := by
          have hpos : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
          have hRn : (0 : ℝ) ≤ R ^ (n : ℝ) := le_of_lt (Real.rpow_pos_of_pos hR0 _)
          nlinarith
      _ = R ^ (4 * (n : ℝ)) := by rw [← Real.rpow_add hR0]; ring_nf

end Arithmetic

end Workspace.ProofLemmas.IdealNormCount
