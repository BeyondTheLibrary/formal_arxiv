import Mathlib
import Workspace.ProofLemmas.AStarLessThanOneHalf
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.LBConstruction

open Workspace.ProofLemmas.FqHasUniqueInteriorZero Workspace.ProofLemmas.LBConstruction
open Finset

theorem LBIntegrality (q : ℝ) (hq : 1 < q) (d : ℕ) (hd : 1 ≤ d) (t : ℕ) (ht : 1 ≤ t) :
    -- (a)
    (0 ≤ kCount q d ∧ 1 ≤ d - 2 * kCount q d ∧ kCount q d < d) ∧
    -- (b) balancedness: each coordinate covered by exactly k of the d shifts
    (∀ j : Fin d,
      ((Finset.range d).filter (fun s => typeIActive q d s j.val)).card = kCount q d) ∧
    -- (c) exact counts + per-coordinate Type-I positive count + evenness of n
    ( numTypeI q d t = d * t ∧
      numTypeII q d t = (d - 2 * kCount q d) * t ∧
      nCount q d t = (2 * d - 2 * kCount q d) * t ∧
      1 ≤ numTypeII q d t ∧
      (∀ j : Fin d,
        (Finset.univ.filter
          (fun i : Fin (numTypeI q d t) => typeIActive q d (i.val % d) j.val)).card
          = kCount q d * t) ∧
      Even (nCount q d t) ∧
      nCount q d t / 2 = (d - kCount q d) * t ) := by
  -- Basic positivity / floor facts.
  have ha := AStarLessThanOneHalf q hq
  have ha_pos : 0 < a_star q := ha.1
  have hd0 : 0 < d := hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hk_le : (kCount q d : ℝ) ≤ a_star q * d := by
    rw [kCount]; exact Nat.floor_le (by positivity)
  -- Key inequality: 2k < d (since a* < 1/2 gives k = ⌊a*d⌋ < d/2).
  have h2k : 2 * kCount q d < d := by
    have h1 : (kCount q d : ℝ) < (1 / 2) * d :=
      lt_of_le_of_lt hk_le (mul_lt_mul_of_pos_right ha.2 hdR)
    have h2 : ((2 * kCount q d : ℕ) : ℝ) < (d : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  -- Modular involution: s ↦ (j + d - s) % d is its own inverse on range d.
  have hinv : ∀ (D J v : ℕ), 0 < D → v < D → (J + D - (J + D - v) % D) % D = v := by
    intro D J v hD0 hvd
    set r := (J + D - v) % D with hr
    have hrlt : r < D := Nat.mod_lt _ hD0
    have hcong : (J + D - r) ≡ v [MOD D] := by
      have e1 : r ≡ (J + D - v) [MOD D] := Nat.mod_modEq _ _
      have e2 : (J + D - r) + r = v + (J + D - v) := by omega
      have e3 : (J + D - r) + r ≡ (J + D - r) + (J + D - v) [MOD D] := Nat.ModEq.add_left _ e1
      rw [e2] at e3
      exact (Nat.ModEq.add_right_cancel' (J + D - v) e3).symm
    calc (J + D - r) % D = v % D := hcong
      _ = v := Nat.mod_eq_of_lt hvd
  -- Counting on range D: #{s ∈ range D | (J + D - s) % D < K} = K, for K ≤ D, J < D.
  have hcount : ∀ (D K J : ℕ), 0 < D → K ≤ D → J < D →
      ((range D).filter (fun s => (J + D - s) % D < K)).card = K := by
    intro D K J hD0 hKD hJD
    have hbij : ((range D).filter (fun s => (J + D - s) % D < K)).card = (range K).card := by
      apply Finset.card_nbij' (fun s => (J + D - s) % D) (fun v => (J + D - v) % D)
      · intro s hs
        simp only [Finset.coe_filter, mem_range, Set.mem_setOf_eq] at hs
        simp only [Finset.coe_range, Set.mem_Iio]; exact hs.2
      · intro v hv
        simp only [Finset.coe_range, Set.mem_Iio] at hv
        have hvD : v < D := lt_of_lt_of_le hv hKD
        simp only [Finset.coe_filter, mem_range, Set.mem_setOf_eq]
        refine ⟨Nat.mod_lt _ hD0, ?_⟩
        rw [hinv D J v hD0 hvD]; exact hv
      · intro s hs
        simp only [Finset.coe_filter, mem_range, Set.mem_setOf_eq] at hs
        exact hinv D J s hD0 hs.1
      · intro v hv
        simp only [Finset.coe_range, Set.mem_Iio] at hv
        exact hinv D J v hD0 (lt_of_lt_of_le hv hKD)
    rw [hbij, Finset.card_range]
  -- Balancedness (b): each coordinate covered by exactly k shifts.
  have hbal : ∀ (j : Fin d),
      ((range d).filter (fun s => typeIActive q d s j.val)).card = kCount q d := by
    intro j
    have key : ((range d).filter (fun s => typeIActive q d s j.val))
        = ((range d).filter (fun s => (j.val + d - s) % d < kCount q d)) := by
      apply Finset.filter_congr
      intro s hs
      simp only [mem_range] at hs
      rw [typeIActive, Nat.mod_eq_of_lt hs]
    rw [key]
    exact hcount d (kCount q d) j.val hd0 (by omega) j.isLt
  -- Per-residue counting on Fin (D * T): predicate depends only on i % D.
  have hbound : ∀ (D T r m : ℕ), r < D → m < T → r + D * m < D * T := by
    intro D T r m hr hm
    calc r + D * m < D + D * m := by omega
      _ = D * (m + 1) := by ring
      _ ≤ D * T := Nat.mul_le_mul_left D (by omega)
  have hpc : ∀ (D T : ℕ) (Q : ℕ → Prop) [DecidablePred Q], 0 < D →
      (Finset.univ.filter (fun i : Fin (D * T) => Q (i.val % D))).card
        = ((range D).filter Q).card * T := by
    intro D T Q _ hD0
    have step : (Finset.univ.filter (fun i : Fin (D * T) => Q (i.val % D))).card
        = (((range D).filter Q) ×ˢ (range T)).card := by
      refine Finset.card_bij'
        (fun (a : Fin (D * T)) _ => (a.val % D, a.val / D))
        (fun (p : ℕ × ℕ) hp => (⟨p.1 + D * p.2, by
          simp only [Finset.mem_product, Finset.mem_filter, mem_range] at hp
          exact hbound D T p.1 p.2 hp.1.1 hp.2⟩ : Fin (D * T)))
        ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_product, Finset.mem_filter, mem_range]
        exact ⟨⟨Nat.mod_lt _ hD0, ha⟩, Nat.div_lt_of_lt_mul a.isLt⟩
      · intro p hp
        simp only [Finset.mem_product, Finset.mem_filter, mem_range] at hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show Q ((p.1 + D * p.2) % D)
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.1]
        exact hp.1.2
      · intro a ha
        apply Fin.ext
        show (a.val % D) + D * (a.val / D) = a.val
        exact Nat.mod_add_div a.val D
      · intro p hp
        simp only [Finset.mem_product, Finset.mem_filter, mem_range] at hp
        have h1 : (p.1 + D * p.2) % D = p.1 := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.1.1]
        have h2 : (p.1 + D * p.2) / D = p.2 := by
          rw [Nat.add_mul_div_left _ _ hD0, Nat.div_eq_of_lt hp.1.1]; ring
        rw [Prod.ext_iff]; exact ⟨h1, h2⟩
    rw [step, Finset.card_product, Finset.card_range]
  -- Assemble.
  refine ⟨⟨Nat.zero_le _, by omega, by omega⟩, hbal, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- nCount = (2d - 2k) * t
    simp only [nCount, numTypeI, numTypeII]
    rw [← Nat.add_mul]
    congr 1
    omega
  · -- 1 ≤ numTypeII
    simp only [numTypeII]
    have h1 : 1 ≤ d - 2 * kCount q d := by omega
    calc 1 = 1 * 1 := by ring
      _ ≤ (d - 2 * kCount q d) * t := Nat.mul_le_mul h1 ht
  · -- per-coordinate Type-I positive count = k * t
    intro j
    have hcast : numTypeI q d t = d * t := rfl
    rw [hcast]
    have := hpc d t (fun s => typeIActive q d s j.val) hd0
    rw [this, hbal j]
  · -- Even (nCount)
    simp only [nCount, numTypeI, numTypeII]
    refine ⟨(d - kCount q d) * t, ?_⟩
    rw [← Nat.add_mul, ← Nat.add_mul]
    congr 1
    omega
  · -- nCount / 2 = (d - k) * t
    simp only [nCount, numTypeI, numTypeII]
    rw [← Nat.add_mul]
    rw [show d + (d - 2 * kCount q d) = 2 * (d - kCount q d) by omega]
    rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
