import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank

/-!
# The Golod–Shafarevich generating-function argument

`gs_core`: if a sequence `c : ℕ → ℕ` satisfies `c 0 = 1`, `c 1 = d`, the *filtration inequality*
`d · c (n+1) ≤ c (n+2) + r · c n`, and vanishes eventually, then `1 ≤ d` forces `d² < 4r`.

Proof.  If `r = 0` the recursion gives `c (n+2) ≥ d · c (n+1) ≥ c (n+1)`, so `c` never vanishes —
contradiction.  So `r ≥ 1`; if `d² ≥ 4r`, the polynomial `r t² − d t + 1` has the positive root
`t₀ = (d − √(d²−4r))/(2r)`.  Summing the filtration inequality against `t₀ⁿ⁺²` and telescoping,
`0 ≤ A·(1 − d t₀ + r t₀²) − 1 = −1` where `A = ∑ₙ cₙ t₀ⁿ` — contradiction.

`one_le_dRank`: a nontrivial Hausdorff topological group has generator rank at least `1`
(the empty set topologically generates only the trivial group).
-/

open Finset
open Workspace.Types.ProPGroup

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.GolodShafarevichCore

/-- **The Golod–Shafarevich generating-function argument.**
If a sequence `c` of naturals satisfies `c 0 = 1`, `c 1 = d`, the filtration inequality
`d · c (n+1) ≤ c (n+2) + r · c n`, and vanishes eventually, then `d ≥ 1` forces `d² < 4r`. -/
theorem gs_core (d r : ℕ) (hd1 : 1 ≤ d) (c : ℕ → ℕ)
    (hc0 : c 0 = 1) (hc1 : c 1 = d)
    (hrec : ∀ n, d * c (n + 1) ≤ c (n + 2) + r * c n)
    (N : ℕ) (hN : ∀ n, N ≤ n → c n = 0) :
    d ^ 2 < 4 * r := by
  by_contra hcon
  push_neg at hcon
  -- `r = 0` is impossible: the recursion would force `c` to grow
  have hr1 : 1 ≤ r := by
    by_contra hr0
    push_neg at hr0
    interval_cases r
    · -- `c (n+2) ≥ d * c (n+1) ≥ c (n+1)`, so `c n ≥ 1` for all `n ≥ 1`
      have hgrow : ∀ n, 1 ≤ c (n + 1) := by
        intro n
        induction n with
        | zero => rw [hc1]; exact hd1
        | succ k ih =>
            have := hrec k
            simp only [Nat.zero_mul, Nat.add_zero] at this
            calc 1 ≤ c (k + 1) := ih
              _ ≤ d * c (k + 1) := Nat.le_mul_of_pos_left _ hd1
              _ ≤ c (k + 2) := this
      have := hgrow N
      rw [hN (N + 1) (by omega)] at this
      omega
  -- the smaller root `t₀ > 0` of `r t² - d t + 1`
  set D : ℝ := Real.sqrt ((d : ℝ) ^ 2 - 4 * r) with hD
  have hdisc : (0 : ℝ) ≤ (d : ℝ) ^ 2 - 4 * r := by
    have : (4 : ℝ) * r ≤ (d : ℝ) ^ 2 := by exact_mod_cast hcon
    linarith
  have hDsq : D ^ 2 = (d : ℝ) ^ 2 - 4 * r := Real.sq_sqrt hdisc
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hDlt : D < (d : ℝ) := by
    nlinarith [hDsq, hD0, hrR]
  set t : ℝ := ((d : ℝ) - D) / (2 * r) with ht
  have ht0 : 0 < t := by
    rw [ht]
    apply div_pos (by linarith) (by linarith)
  have hroot : 1 - (d : ℝ) * t + (r : ℝ) * t ^ 2 = 0 := by
    rw [ht]
    field_simp
    nlinarith [hDsq]
  -- the partial sums of the generating function
  have hSstab : ∀ M, N ≤ M → ∑ n ∈ Finset.range M, (c n : ℝ) * t ^ n
      = ∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n := by
    intro M hM
    refine (Finset.sum_subset (Finset.range_mono hM) ?_).symm
    intro n _ hnN
    rw [Finset.mem_range] at hnN
    push_neg at hnN
    rw [hN n hnN]
    simp
  -- shift identities
  have hshift1 : ∀ M : ℕ, ∑ n ∈ Finset.range M, (c (n + 1) : ℝ) * t ^ (n + 1)
      = (∑ n ∈ Finset.range (M + 1), (c n : ℝ) * t ^ n) - (c 0 : ℝ) := by
    intro M
    have h := Finset.sum_range_succ' (fun n => (c n : ℝ) * t ^ n) M
    simp only [pow_zero, mul_one] at h
    rw [h]
    ring
  have hshift2 : ∀ M : ℕ, ∑ n ∈ Finset.range M, (c (n + 2) : ℝ) * t ^ (n + 2)
      = (∑ n ∈ Finset.range (M + 2), (c n : ℝ) * t ^ n) - (c 0 : ℝ) - (c 1 : ℝ) * t := by
    intro M
    have h1 := hshift1 (M + 1)
    have h2 : ∑ n ∈ Finset.range (M + 1), (c (n + 1) : ℝ) * t ^ (n + 1)
        = (c 1 : ℝ) * t + ∑ n ∈ Finset.range M, (c (n + 2) : ℝ) * t ^ (n + 2) := by
      have h := Finset.sum_range_succ' (fun n => (c (n + 1) : ℝ) * t ^ (n + 1)) M
      simp only [pow_one] at h
      rw [h]
      ring
    rw [h2] at h1
    linarith
  -- sum the filtration inequality
  have hnonneg : (0 : ℝ) ≤
      ∑ n ∈ Finset.range N,
        (((c (n + 2) : ℝ) + (r : ℝ) * (c n : ℝ)) - (d : ℝ) * (c (n + 1) : ℝ)) * t ^ (n + 2) := by
    refine Finset.sum_nonneg ?_
    intro n _
    have h := hrec n
    have h' : (d : ℝ) * (c (n + 1) : ℝ) ≤ (c (n + 2) : ℝ) + (r : ℝ) * (c n : ℝ) := by
      exact_mod_cast h
    have hpow : (0 : ℝ) ≤ t ^ (n + 2) := le_of_lt (pow_pos ht0 _)
    nlinarith
  -- expand the sum
  have hexpand :
      ∑ n ∈ Finset.range N,
        (((c (n + 2) : ℝ) + (r : ℝ) * (c n : ℝ)) - (d : ℝ) * (c (n + 1) : ℝ)) * t ^ (n + 2)
      = (∑ n ∈ Finset.range N, (c (n + 2) : ℝ) * t ^ (n + 2))
        + (r : ℝ) * t ^ 2 * (∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n)
        - (d : ℝ) * t * (∑ n ∈ Finset.range N, (c (n + 1) : ℝ) * t ^ (n + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hexpand, hshift1 N, hshift2 N, hSstab (N + 2) (by omega), hSstab (N + 1) (by omega),
    hc0, hc1] at hnonneg
  set A : ℝ := ∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n with hA
  push_cast at hnonneg
  have key : A - 1 - (d : ℝ) * t + (r : ℝ) * t ^ 2 * A - (d : ℝ) * t * (A - 1)
      = A * (1 - (d : ℝ) * t + (r : ℝ) * t ^ 2) - 1 := by ring
  rw [key, hroot, mul_zero] at hnonneg
  linarith




/-- A nontrivial (Hausdorff) topological group has generator rank at least `1`. -/
theorem one_le_dRank (G : Type*) [Group G] [TopologicalSpace G] [T2Space G]
    (hnt : Nontrivial G) : 1 ≤ dRank G := by
  by_contra h
  push_neg at h
  have h0 : dRank G = 0 := by
    rcases eq_or_ne (dRank G) 0 with h' | h'
    · exact h'
    · exact absurd h (not_lt.mpr (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr h')))
  -- `0` is then a member of the defining set
  have hmem : (0 : ℕ∞) ∈ {n : ℕ∞ | ∃ S : Finset G, TopologicallyGenerates (S : Set G) ∧
      (S.card : ℕ∞) = n} := by
    by_contra hcon
    have : (1 : ℕ∞) ≤ dRank G := by
      rw [dRank]
      refine le_sInf ?_
      intro b hb
      rcases eq_or_ne b 0 with rfl | hb0
      · exact absurd hb hcon
      · exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hb0)
    rw [h0] at this
    simp at this
  obtain ⟨S, hgen, hcard⟩ := hmem
  have hS : S = ∅ := by
    have : S.card = 0 := by exact_mod_cast hcard
    exact Finset.card_eq_zero.mp this
  subst hS
  rw [TopologicallyGenerates] at hgen
  simp only [Finset.coe_empty, Subgroup.closure_empty] at hgen
  have h1 : ((⊥ : Subgroup G) : Set G) = {(1 : G)} := by simp
  rw [h1, closure_singleton] at hgen
  obtain ⟨x, y, hxy⟩ := hnt
  have hx : x ∈ ({(1 : G)} : Set G) := by rw [hgen]; trivial
  have hy : y ∈ ({(1 : G)} : Set G) := by rw [hgen]; trivial
  simp only [Set.mem_singleton_iff] at hx hy
  exact hxy (hx.trans hy.symm)



end Workspace.ProofLemmas.GolodShafarevichCore
