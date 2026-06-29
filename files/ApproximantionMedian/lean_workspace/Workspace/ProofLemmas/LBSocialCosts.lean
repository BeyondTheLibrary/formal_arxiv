import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.LBConstruction
import Workspace.ProofLemmas.LBIntegrality
import Workspace.ProofLemmas.LBLambdaStarLtOne
import Workspace.ProofLemmas.AStarLessThanOneHalf

open Workspace.Types.LqNorm Workspace.Types.SocialCost Workspace.ProofLemmas.LBConstruction
open Workspace.ProofLemmas.LBLambdaStarLtOne
open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Finset

/-- Per-point count: for a fixed cyclic shift `s`, exactly `kCount q d` coordinates
are active for a Type-I point (the length-`k` cyclic block, when `k < d`). This is
the per-POINT analogue of `LBIntegrality`'s per-coordinate balancedness count, proved
by the same cyclic-rotation bijection. -/
theorem perPointCount (q : ℝ) (d : ℕ) (hd0 : 0 < d) (hk : kCount q d ≤ d) (s : ℕ) :
    (Finset.univ.filter (fun j : Fin d => typeIActive q d s j.val)).card = kCount q d := by
  set K := kCount q d with hK
  set r := s % d with hr
  have hrlt : r < d := Nat.mod_lt _ hd0
  -- forward/backward round trips of the rotation `j ↦ (j + d - r) % d`
  have fwd : ∀ j : ℕ, j < d → ((j + d - r) % d + r) % d = j := by
    intro j hj
    have heq : ((j + d - r) % d + r) % d = ((j + d - r) + r) % d := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [heq]
    have h : (j + d - r) + r = j + d := by omega
    rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have bwd : ∀ v : ℕ, v < d → ((v + r) % d + d - r) % d = v := by
    intro v hv
    have hsplit : (v + r) % d + d - r = (v + r) % d + (d - r) := by omega
    rw [hsplit, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have h2 : (v + r) + (d - r) = v + d := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hv]
  -- rewrite predicate
  have hpred : (Finset.univ.filter (fun j : Fin d => typeIActive q d s j.val))
      = (Finset.univ.filter (fun j : Fin d => (j.val + d - r) % d < K)) := by
    apply Finset.filter_congr
    intro j _
    simp only [typeIActive, hr, hK]
  rw [hpred]
  have hbij : (Finset.univ.filter (fun j : Fin d => (j.val + d - r) % d < K)).card
      = (Finset.univ.filter (fun v : Fin d => v.val < K)).card := by
    apply Finset.card_nbij' (fun j => (⟨(j.val + d - r) % d, Nat.mod_lt _ hd0⟩ : Fin d))
      (fun v => (⟨(v.val + r) % d, Nat.mod_lt _ hd0⟩ : Fin d))
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      rw [bwd v.val v.isLt]; exact hv
    · intro j hj
      apply Fin.ext
      exact fwd j.val j.isLt
    · intro v hv
      apply Fin.ext
      exact bwd v.val v.isLt
  rw [hbij, Fin.card_filter_val_lt]
  omega

theorem LBSocialCosts (q : ℝ) (hq : 1 < q) (d : ℕ) (hd : 1 ≤ d) (t : ℕ) (ht : 1 ≤ t) :
    -- (iii) cost at median 0
    socialCost q (P_LB q d t) (fun _ : Fin d => (0 : ℝ))
      = (1 / (1 - c_star q)) * (kCount q d : ℝ) ^ ((1:ℝ)/q) * (numTypeI q d t : ℝ)
        + (d : ℝ) ^ ((1:ℝ)/q) * (numTypeII q d t : ℝ)
    ∧
    -- (iii) cost at optimum f
    socialCost q (P_LB q d t) (f_opt d)
      = ( (c_star q / (1 - c_star q)) ^ q * (kCount q d : ℝ) + ((d : ℝ) - (kCount q d : ℝ)) ) ^ ((1:ℝ)/q)
        * (numTypeI q d t : ℝ)
    ∧
    -- (iv) cancelled ratio
    socialCost q (P_LB q d t) (fun _ : Fin d => (0 : ℝ)) / socialCost q (P_LB q d t) (f_opt d)
      = ( (1 / (1 - c_star q)) * ((kCount q d : ℝ) / (d : ℝ)) ^ ((1:ℝ)/q)
            + (1 - 2 * ((kCount q d : ℝ) / (d : ℝ))) )
        / ( (c_star q / (1 - c_star q)) ^ q * ((kCount q d : ℝ) / (d : ℝ)) + (1 - ((kCount q d : ℝ) / (d : ℝ))) ) ^ ((1:ℝ)/q) := by
  -- ===== Foundational facts =====
  have hq_pos : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hInt := LBIntegrality q hq d hd t ht
  have hLam := LBLambdaStarLtOne q hq
  have ha := AStarLessThanOneHalf q hq
  have hk_lt_d : kCount q d < d := hInt.1.2.2
  have hk_le_d : kCount q d ≤ d := le_of_lt hk_lt_d
  have hd0 : 0 < d := hd
  have hdR : (0:ℝ) < d := by exact_mod_cast hd0
  -- c_star positivity and < 1
  set K := Kconst q with hKdef
  have hKpos : 0 < K := by
    rw [hKdef, Kconst]
    apply Real.rpow_pos_of_pos
    have h1 : 0 < (1 - a_star q) / a_star q := by
      apply div_pos <;> [linarith [ha.2]; exact ha.1]
    have h2 : 0 < mu q / (1 - mu q) := div_pos hLam.2.1.1 hLam.2.2.1
    exact mul_pos h1 h2
  have hc_eq : c_star q = K / (1 + K) := by rw [c_star, hKdef]
  have hcpos : 0 < c_star q := by rw [hc_eq]; positivity
  have h1pK : 0 < 1 + K := by linarith
  have hc_lt1 : c_star q < 1 := by
    rw [hc_eq, div_lt_one h1pK]; linarith
  have h1mc : 0 < 1 - c_star q := by linarith
  have h1mc_ne : (1 - c_star q) ≠ 0 := ne_of_gt h1mc
  set v := 1 / (1 - c_star q) with hvdef
  have hv_pos : 0 < v := by rw [hvdef]; positivity
  have hv_nonneg : 0 ≤ v := le_of_lt hv_pos
  -- key identities: 1/(1-c*) = 1+K, c*/(1-c*) = K
  have h1mc_val : 1 - c_star q = 1 / (1 + K) := by
    rw [hc_eq]; field_simp; ring
  have hv_eq : v = 1 + K := by
    rw [hvdef, h1mc_val, one_div_one_div]
  have hvm1 : v - 1 = K := by rw [hv_eq]; ring_nf
  have hvm1_nonneg : 0 ≤ v - 1 := by rw [hvm1]; exact le_of_lt hKpos
  -- c*/(1-c*) = K
  have hcc : c_star q / (1 - c_star q) = K := by
    rw [div_eq_iff h1mc_ne, hc_eq]
    field_simp; ring
  -- ===== Per-point active count, as Bool =====
  have hcount : ∀ s : ℕ,
      (Finset.univ.filter (fun j : Fin d => typeIActiveB q d s j.val = true)).card = kCount q d := by
    intro s
    rw [← perPointCount q d hd0 hk_le_d s]
    congr 1
    apply Finset.filter_congr
    intro j _
    simp only [typeIActiveB, decide_eq_true_eq, typeIActive]
  -- abbreviations
  set K' := (c_star q / (1 - c_star q)) ^ q with hK'def
  -- ===== Per-point norm at median (f = 0) =====
  -- Type-I index i (i.val < numTypeI): norm = v * k^{1/q}
  have hnormI0 : ∀ i : Fin (nCount q d t), i.val < numTypeI q d t →
      lqNorm q (fun j => P_LB q d t i j - (0:ℝ)) = v * (kCount q d : ℝ) ^ ((1:ℝ)/q) := by
    intro i hi
    unfold lqNorm
    have hP : ∀ j : Fin d, P_LB q d t i j - (0:ℝ)
        = (if typeIActiveB q d (i.val % d) j.val then v else 0) := by
      intro j; rw [sub_zero]; unfold P_LB; rw [if_pos hi]
    simp_rw [hP]
    have hterm : ∀ j : Fin d, |(if typeIActiveB q d (i.val % d) j.val then v else (0:ℝ))| ^ q
        = (if typeIActiveB q d (i.val % d) j.val then v^q else 0) := by
      intro j; by_cases h : typeIActiveB q d (i.val % d) j.val <;>
        simp [h, abs_of_nonneg hv_nonneg, Real.zero_rpow hq_ne]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    simp only [smul_zero, add_zero, nsmul_eq_mul]
    rw [hcount (i.val % d)]
    rw [mul_comm (kCount q d : ℝ) (v^q)]
    rw [Real.mul_rpow (Real.rpow_nonneg hv_nonneg q) (by positivity)]
    rw [← Real.rpow_mul hv_nonneg, mul_one_div, div_self hq_ne, Real.rpow_one]
  -- Type-II index i (numTypeI ≤ i.val): norm = d^{1/q}
  have hnormII0 : ∀ i : Fin (nCount q d t), ¬ (i.val < numTypeI q d t) →
      lqNorm q (fun j => P_LB q d t i j - (0:ℝ)) = (d : ℝ) ^ ((1:ℝ)/q) := by
    intro i hi
    have hP : ∀ j : Fin d, P_LB q d t i j - (0:ℝ) = (1:ℝ) := by
      intro j; rw [sub_zero]; unfold P_LB; rw [if_neg hi]
    unfold lqNorm
    simp_rw [hP]
    simp only [abs_one, Real.one_rpow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- ===== Per-point norm at optimum (f = f_opt = 1) =====
  -- Type-I: norm = (K'*k + (d-k))^{1/q}
  have hnormIf : ∀ i : Fin (nCount q d t), i.val < numTypeI q d t →
      lqNorm q (fun j => P_LB q d t i j - f_opt d j)
        = (K' * (kCount q d : ℝ) + ((d:ℝ) - (kCount q d : ℝ))) ^ ((1:ℝ)/q) := by
    intro i hi
    unfold lqNorm
    have hP : ∀ j : Fin d, P_LB q d t i j - f_opt d j
        = (if typeIActiveB q d (i.val % d) j.val then v - 1 else (-1)) := by
      intro j; unfold P_LB f_opt; rw [if_pos hi]
      by_cases h : typeIActiveB q d (i.val % d) j.val
      · rw [if_pos h, if_pos h, hvdef]
      · rw [if_neg h, if_neg h]; ring
    simp_rw [hP]
    have hterm : ∀ j : Fin d, |(if typeIActiveB q d (i.val % d) j.val then v - 1 else (-1:ℝ))| ^ q
        = (if typeIActiveB q d (i.val % d) j.val then (v-1)^q else 1) := by
      intro j; by_cases h : typeIActiveB q d (i.val % d) j.val <;>
        simp [h, abs_of_nonneg hvm1_nonneg, Real.one_rpow]
    simp_rw [hterm]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
    rw [hcount (i.val % d)]
    -- count of inactive = d - k
    have hcompl : (Finset.filter (fun j : Fin d => ¬ (typeIActiveB q d (i.val % d) j.val = true)) Finset.univ).card
        = d - kCount q d := by
      have hsum := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin d))) (p := fun j : Fin d => typeIActiveB q d (i.val % d) j.val = true)
      rw [hcount (i.val % d), Finset.card_univ, Fintype.card_fin] at hsum
      omega
    rw [hcompl]
    simp only [nsmul_eq_mul, mul_one]
    -- now: (k * (v-1)^q + (d-k) * 1)^{1/q} = (K'*k + (d-k))^{1/q}
    push_cast [Nat.cast_sub hk_le_d]
    rw [hvm1, hK'def, hcc]
    ring_nf
  -- Type-II: norm = 0
  have hnormIIf : ∀ i : Fin (nCount q d t), ¬ (i.val < numTypeI q d t) →
      lqNorm q (fun j => P_LB q d t i j - f_opt d j) = 0 := by
    intro i hi
    have hP : ∀ j : Fin d, P_LB q d t i j - f_opt d j = (0:ℝ) := by
      intro j; unfold P_LB f_opt; rw [if_neg hi]; ring
    unfold lqNorm
    simp_rw [hP]
    simp only [abs_zero, Real.zero_rpow hq_ne, Finset.sum_const, smul_zero]
    rw [Real.zero_rpow (by rw [one_div]; exact inv_ne_zero hq_ne)]
  -- ===== Index counts =====
  have hcountI : (Finset.filter (fun i : Fin (nCount q d t) => i.val < numTypeI q d t) Finset.univ).card
      = numTypeI q d t := by
    rw [Fin.card_filter_val_lt]
    have : numTypeI q d t ≤ nCount q d t := by rw [nCount]; omega
    omega
  have hcountII : (Finset.filter (fun i : Fin (nCount q d t) => ¬ (i.val < numTypeI q d t)) Finset.univ).card
      = numTypeII q d t := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (nCount q d t)))) (p := fun i : Fin (nCount q d t) => i.val < numTypeI q d t)
    rw [hcountI, Finset.card_univ, Fintype.card_fin] at hsum
    have hnle : numTypeI q d t ≤ nCount q d t := by rw [nCount]; omega
    have : numTypeII q d t = nCount q d t - numTypeI q d t := by rw [nCount]; omega
    rw [this]; omega
  -- ===== Social cost at median =====
  have hSC0 : socialCost q (P_LB q d t) (fun _ : Fin d => (0:ℝ))
      = v * (kCount q d : ℝ) ^ ((1:ℝ)/q) * (numTypeI q d t : ℝ)
        + (d : ℝ) ^ ((1:ℝ)/q) * (numTypeII q d t : ℝ) := by
    unfold socialCost
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin (nCount q d t) => i.val < numTypeI q d t)]
    rw [Finset.sum_congr rfl (fun i hi => hnormI0 i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_congr rfl (fun i hi => hnormII0 i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, Finset.sum_const, hcountI, hcountII]
    simp only [nsmul_eq_mul]
    ring
  -- ===== Social cost at optimum =====
  have hSCf : socialCost q (P_LB q d t) (f_opt d)
      = (K' * (kCount q d : ℝ) + ((d:ℝ) - (kCount q d : ℝ))) ^ ((1:ℝ)/q) * (numTypeI q d t : ℝ) := by
    unfold socialCost
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i : Fin (nCount q d t) => i.val < numTypeI q d t)]
    rw [Finset.sum_congr rfl (fun i hi => hnormIf i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_congr rfl (fun i hi => hnormIIf i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_const, Finset.sum_const, hcountI, hcountII]
    simp only [nsmul_eq_mul, mul_zero, add_zero]
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- conjunct 1
    rw [hSC0]
  · -- conjunct 2
    rw [hSCf, hK'def]
  · -- conjunct 3: ratio
    rw [hSC0, hSCf, hK'def]
    -- numType casts
    have h2k : 2 * kCount q d ≤ d := by omega
    have hnumI : (numTypeI q d t : ℝ) = (d:ℝ) * (t:ℝ) := by
      rw [hInt.2.2.1]; push_cast; ring
    have hnumII : (numTypeII q d t : ℝ) = ((d:ℝ) - 2*(kCount q d:ℝ)) * (t:ℝ) := by
      rw [hInt.2.2.2.1]; push_cast [Nat.cast_sub h2k]; ring
    rw [hnumI, hnumII]
    -- positivity facts
    have htR : (0:ℝ) < t := by exact_mod_cast ht
    have hdt_pos : (0:ℝ) < (d:ℝ) * (t:ℝ) := mul_pos hdR htR
    set kr := (kCount q d : ℝ) with hkr
    set dr := (d : ℝ) with hdr
    set KK := (c_star q / (1 - c_star q)) ^ q with hKK
    have hKK_nonneg : 0 ≤ KK := by rw [hKK]; positivity
    have hkr_nonneg : 0 ≤ kr := by rw [hkr]; positivity
    have hdr_pos : 0 < dr := by rw [hdr]; exact hdR
    -- denominator base (un-normalized) positive
    have hkr_lt_dr : kr < dr := by rw [hkr, hdr]; exact_mod_cast hk_lt_d
    have hbase_pos : 0 < KK * kr + (dr - kr) := by
      have hpos : 0 < dr - kr := by linarith
      nlinarith [mul_nonneg hKK_nonneg hkr_nonneg]
    -- d^{1/q} > 0
    have hd_rpow_pos : 0 < dr ^ ((1:ℝ)/q) := Real.rpow_pos_of_pos hdr_pos _
    -- split (k/d)^{1/q} = k^{1/q}/d^{1/q}
    have hsplit1 : (kr / dr) ^ ((1:ℝ)/q) = kr ^ ((1:ℝ)/q) / dr ^ ((1:ℝ)/q) :=
      Real.div_rpow hkr_nonneg (le_of_lt hdr_pos) _
    -- split denominator base: KK*(k/d)+(1-k/d) = (KK*k+(d-k))/d
    have hdenbase : KK * (kr / dr) + (1 - kr / dr) = (KK * kr + (dr - kr)) / dr := by
      field_simp
    rw [hsplit1, hdenbase, Real.div_rpow (le_of_lt hbase_pos) (le_of_lt hdr_pos)]
    -- now everything in terms of d^{1/q}; clear denominators
    have hbase_rpow_pos : 0 < (KK * kr + (dr - kr)) ^ ((1:ℝ)/q) := Real.rpow_pos_of_pos hbase_pos _
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
