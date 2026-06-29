import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.LqNormPartialDerivative_PosBranch
import Workspace.ProofLemmas.LqNormBoundaryUpwardExpansion

open scoped BigOperators
open Workspace.Types.LqNorm

theorem LqNormBoundaryRightDeriv
    {q : ℝ} (hq : 1 < q) {d : ℕ} (hd : 1 ≤ d)
    (x : Fin d → ℝ) (j : Fin d)
    (hx_nn : 0 ≤ x j) (hlq_pos : 0 < lqNorm q x) :
    HasDerivWithinAt (fun t : ℝ => lqNorm q (Function.update x j t))
      ((x j) ^ (q - 1) / (lqNorm q x) ^ (q - 1)) (Set.Ici (x j)) (x j) := by
  -- Useful basic facts about q.
  have hq_pos : 0 < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq_one_le : (1 : ℝ) ≤ q := le_of_lt hq
  have hq1_pos : 0 < q - 1 := sub_pos.mpr hq
  have hq1_nonneg : (0 : ℝ) ≤ q - 1 := le_of_lt hq1_pos
  have hq1_ne : q - 1 ≠ 0 := ne_of_gt hq1_pos
  have hlq_nn : 0 ≤ lqNorm q x := le_of_lt hlq_pos
  have hlq_ne : lqNorm q x ≠ 0 := ne_of_gt hlq_pos
  -- Split on x j > 0 vs x j = 0.
  rcases lt_or_eq_of_le hx_nn with hxj_pos | hxj_zero_eq
  · -- Case x j > 0: use LqNormPartialDerivative_PosBranch.
    have h := LqNormPartialDerivative_PosBranch hq hd x j hxj_pos hlq_pos
    exact h.hasDerivWithinAt
  · -- Case 0 = x j (so x j = 0).
    have hxj0 : x j = 0 := hxj_zero_eq.symm
    -- The target derivative is 0:
    have htarget : (x j) ^ (q - 1) / (lqNorm q x) ^ (q - 1) = 0 := by
      rw [hxj0, Real.zero_rpow hq1_ne, zero_div]
    rw [htarget, hxj0]
    -- We want HasDerivWithinAt (fun t => lqNorm q (update x j t)) 0 (Set.Ici 0) 0.
    -- Define g(t) := ((lqNorm q x)^q + t^q)^(1/q). By LqNormBoundaryUpwardExpansion,
    -- on Ici 0 we have lqNorm q (update x j t) = g(t).
    set L : ℝ := lqNorm q x with hL_def
    -- L^q > 0, so the inner sum L^q + t^q > 0 for t ≥ 0.
    have hLq_pos : 0 < L ^ q := Real.rpow_pos_of_pos hlq_pos q
    have hLq_ne : L ^ q ≠ 0 := ne_of_gt hLq_pos
    -- Step A: HasDerivAt (fun t => L^q + t^q) (q * 0^(q-1)) 0.
    have h_pow_q : HasDerivAt (fun t : ℝ => t ^ q) (q * (0 : ℝ) ^ (q - 1)) 0 :=
      Real.hasDerivAt_rpow_const (Or.inr hq_one_le)
    have h_inner : HasDerivAt (fun t : ℝ => L ^ q + t ^ q) (q * (0 : ℝ) ^ (q - 1)) 0 := by
      have := h_pow_q.const_add (L ^ q)
      simpa using this
    -- Step B: simplify (q * 0^(q-1)) = 0
    have h_inner_deriv_zero : q * (0 : ℝ) ^ (q - 1) = 0 := by
      rw [Real.zero_rpow hq1_ne, mul_zero]
    rw [h_inner_deriv_zero] at h_inner
    -- Step C: Apply rpow_const at p = 1/q with f(0) = L^q ≠ 0.
    have h_outer : HasDerivAt (fun t : ℝ => (L ^ q + t ^ q) ^ ((1 : ℝ) / q))
        (0 * (1 / q) * (L ^ q + (0 : ℝ) ^ q) ^ ((1 : ℝ) / q - 1)) 0 := by
      have hbase : (fun t : ℝ => L ^ q + t ^ q) 0 ≠ 0 := by
        show L ^ q + (0 : ℝ) ^ q ≠ 0
        rw [Real.zero_rpow hq_ne, add_zero]
        exact hLq_ne
      exact h_inner.rpow_const (Or.inl hbase)
    -- Step D: simplify the derivative value to 0.
    have h_outer_deriv_zero :
        (0 : ℝ) * (1 / q) * (L ^ q + (0 : ℝ) ^ q) ^ ((1 : ℝ) / q - 1) = 0 := by
      ring
    rw [h_outer_deriv_zero] at h_outer
    -- Step E: Lift to HasDerivWithinAt on Ici 0.
    have h_outer_within : HasDerivWithinAt
        (fun t : ℝ => (L ^ q + t ^ q) ^ ((1 : ℝ) / q))
        0 (Set.Ici (0 : ℝ)) 0 := h_outer.hasDerivWithinAt
    -- Step F: Show eventually-equal in nhdsWithin 0 (Ici 0):
    -- For t ≥ 0, lqNorm q (update x j t) = (L^q + t^q)^(1/q).
    have h_eq_on : ∀ t ∈ Set.Ici (0 : ℝ),
        lqNorm q (Function.update x j t) = (L ^ q + t ^ q) ^ ((1 : ℝ) / q) := by
      intro t ht
      have ht_nn : 0 ≤ t := ht
      exact LqNormBoundaryUpwardExpansion hq hd x j t ht_nn hxj0
    -- Use HasDerivWithinAt.congr to switch from g to lqNorm.
    -- HasDerivWithinAt.congr : HasDerivWithinAt f f' s x → (∀ x ∈ s, f₁ x = f x) → f₁ x = f x → HasDerivWithinAt f₁ s x
    refine h_outer_within.congr ?_ ?_
    · intros t ht
      exact h_eq_on t ht
    · -- f₁ 0 = f 0 where f₁ = lqNorm composition, f = (L^q + t^q)^(1/q)
      exact h_eq_on 0 Set.self_mem_Ici
