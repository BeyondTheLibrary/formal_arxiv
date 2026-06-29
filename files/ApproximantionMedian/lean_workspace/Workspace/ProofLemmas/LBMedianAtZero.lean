import Mathlib
import Workspace.Types.CoordinateMedian
import Workspace.ProofLemmas.LBConstruction
import Workspace.ProofLemmas.LBIntegrality
import Workspace.ProofLemmas.LBLambdaStarLtOne
import Workspace.ProofLemmas.AStarLessThanOneHalf

open Workspace.Types.CoordinateMedian Workspace.ProofLemmas.LBConstruction
open Finset

/-- The all-zero vector `0 ∈ ℝ^d` is a coordinate-wise median of the
lower-bound placement `P_LB q d t`. Concretely, for every coordinate `j`,
`#{i : P_{i,j} < 0} = 0` and `#{i : P_{i,j} > 0} = (d−k)t = n/2`, so both
sides are `≤ n/2` and the `IsCoordinateMedian` predicate holds. -/
theorem LBMedianAtZero (q : ℝ) (hq : 1 < q) (d : ℕ) (hd : 1 ≤ d) (t : ℕ) (ht : 1 ≤ t) :
    IsCoordinateMedian (fun _ : Fin d => (0 : ℝ)) (P_LB q d t) := by
  -- Positivity of the Type-I active entry value 1/(1 - c*).
  have ha := AStarLessThanOneHalf q hq
  have hmu := Workspace.ProofLemmas.LBLambdaStarLtOne.LBLambdaStarLtOne q hq
  have ha_pos : 0 < Workspace.ProofLemmas.FqHasUniqueInteriorZero.a_star q := ha.1
  have hmu_pos : 0 < mu q := hmu.2.1.1
  have hmu_lt : mu q < 1 := hmu.2.1.2
  have hc_lt_one : c_star q < 1 := by
    have hbase_pos :
        0 < (1 - Workspace.ProofLemmas.FqHasUniqueInteriorZero.a_star q) /
              (Workspace.ProofLemmas.FqHasUniqueInteriorZero.a_star q) *
              (mu q / (1 - mu q)) :=
      mul_pos (div_pos (by linarith [ha.2]) ha_pos) (div_pos hmu_pos (by linarith))
    have hK_pos : 0 < Kconst q := by
      unfold Kconst; exact Real.rpow_pos_of_pos hbase_pos _
    unfold c_star; rw [div_lt_one (by linarith)]; linarith
  have hval_pos : (0 : ℝ) < 1 / (1 - c_star q) := div_pos one_pos (by linarith)
  -- Every entry of P_LB is nonnegative.
  have hnonneg : ∀ (i : Fin (nCount q d t)) (j : Fin d), 0 ≤ P_LB q d t i j := by
    intro i j
    unfold P_LB
    split_ifs <;> first | exact le_of_lt hval_pos | norm_num
  -- Integrality facts.
  obtain ⟨hk, _, _hnI, hnII, _hnn, _, hcount, _, hhalf⟩ := LBIntegrality q hq d hd t ht
  intro j
  refine ⟨?_, ?_⟩
  · -- Negative side: no entry is < 0, so the filter is empty.
    have hempty :
        (Finset.univ.filter (fun i : Fin (nCount q d t) =>
          P_LB q d t i j < (fun _ : Fin d => (0 : ℝ)) j)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      simp only [not_lt]
      exact hnonneg i j
    rw [hempty]; simp
  · -- Positive side: exactly `(d - k) t` entries are positive, which equals `n / 2`.
    rw [hhalf, Finset.card_filter]
    -- Split the sum over `Fin (nCount) = Fin (numTypeI + numTypeII)` into the
    -- Type-I prefix and the Type-II suffix.
    have hsplit :=
      Fin.sum_univ_add (a := numTypeI q d t) (b := numTypeII q d t)
        (f := fun i => if P_LB q d t i j > (fun _ : Fin d => (0 : ℝ)) j then (1 : ℕ) else 0)
    -- Type-I part: counts exactly the coordinates activated at `j`, namely `k t`.
    have hI :
        (∑ i : Fin (numTypeI q d t),
            if P_LB q d t (Fin.castAdd (numTypeII q d t) i) j > (fun _ : Fin d => (0 : ℝ)) j
            then (1 : ℕ) else 0) = kCount q d * t := by
      have hterm : ∀ i : Fin (numTypeI q d t),
          (if P_LB q d t (Fin.castAdd (numTypeII q d t) i) j > (fun _ : Fin d => (0 : ℝ)) j
            then (1 : ℕ) else 0)
            = (if typeIActive q d ((i : ℕ) % d) (j : ℕ) then (1 : ℕ) else 0) := by
        intro i
        have hlt : ((Fin.castAdd (numTypeII q d t) i : Fin (nCount q d t)) : ℕ)
            < numTypeI q d t := by simp [Fin.castAdd, Fin.castLE]
        have hcast : ((Fin.castAdd (numTypeII q d t) i : Fin (nCount q d t)) : ℕ) = (i : ℕ) := by
          simp [Fin.castAdd, Fin.castLE]
        have hbeq : typeIActiveB q d ((Fin.castAdd (numTypeII q d t) i : Fin (nCount q d t)).val % d) (j : ℕ)
            = decide (typeIActive q d ((i : ℕ) % d) (j : ℕ)) := by
          unfold typeIActiveB; rw [hcast]; rfl
        have hval : P_LB q d t (Fin.castAdd (numTypeII q d t) i) j
            = (if typeIActive q d ((i : ℕ) % d) (j : ℕ) then 1 / (1 - c_star q) else 0) := by
          unfold P_LB
          rw [if_pos hlt, hbeq]
          by_cases hact : typeIActive q d ((i : ℕ) % d) (j : ℕ) <;> simp [hact]
        rw [hval]
        by_cases hact : typeIActive q d ((i : ℕ) % d) (j : ℕ)
        · rw [if_pos hact, if_pos hact, if_pos hval_pos]
        · rw [if_neg hact, if_neg hact, if_neg (lt_irrefl _)]
      rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.card_filter]
      exact hcount j
    -- Type-II part: every entry equals `1 > 0`, so all `numTypeII` of them count.
    have hII :
        (∑ i : Fin (numTypeII q d t),
            if P_LB q d t (Fin.natAdd (numTypeI q d t) i) j > (fun _ : Fin d => (0 : ℝ)) j
            then (1 : ℕ) else 0) = numTypeII q d t := by
      have hterm : ∀ i : Fin (numTypeII q d t),
          (if P_LB q d t (Fin.natAdd (numTypeI q d t) i) j > (fun _ : Fin d => (0 : ℝ)) j
            then (1 : ℕ) else 0) = 1 := by
        intro i
        have hge : ¬ ((Fin.natAdd (numTypeI q d t) i : Fin (nCount q d t)) : ℕ)
            < numTypeI q d t := by simp [Fin.natAdd]
        have hval : P_LB q d t (Fin.natAdd (numTypeI q d t) i) j = 1 := by
          unfold P_LB; rw [if_neg hge]
        rw [hval]; simp
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]; simp
    -- Combine: `k t + (d - 2k) t = (d - k) t`.
    refine le_of_eq (hsplit.trans ?_)
    rw [hI, hII, hnII]
    have h2k : 1 ≤ d - 2 * kCount q d := hk.2.1
    have hklt : kCount q d < d := hk.2.2
    rw [← Nat.add_mul]
    congr 1
    omega
