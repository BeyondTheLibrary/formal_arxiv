import Mathlib

/-!
# An elementary Mertens theorem for primes `≡ 1 (mod 3)`

Development toward the polynomial bound `PrimesOneModThreePolyBound` (the `i`-th prime `≡ 1 (mod 3)`
is polynomially bounded).  Everything here is elementary arithmetic over `ℕ`; no algebraic number
theory is used, although the underlying object is the ideal-counting function of `ℚ(√-3)`:

* `chi` — the nontrivial character mod `3`;
* `r = 1 * chi` — `r n` is the number of ideals of `𝓞_{ℚ(√-3)}` of norm `n`;
* `A N = ∑_{n ≤ N} r n`, with `N/2 ≤ A N ≤ N` (`A_ge`, `A_le`) proved by summation by parts,
  using only that the partial sums of `chi` lie in `{0, 1}`.  This is where the positivity of
  `L(1, χ)` enters, in completely elementary form;
* `swap`, `hyp_symm` — the Dirichlet divisor-sum swap and the symmetry of the hyperbola region;
* `T_eq` — `∑_{n ≤ N} r(n) log n = ∑_{k ≤ N} Λ(k)(1 + χ(k)) A(⌊N/k⌋)`, the summatory form of
  `ζ_K'/ζ_K`, obtained by triple-sum rearrangement (no multiplicativity needed);
* `T_le`, `T_ge` — `(N/2) log N − N ≤ ∑_{n≤N} r(n) log n ≤ N log N`;
* `mertens_lower` — hence `∑_{k ≤ N} Λ(k)(1+χ(k))/k ≥ (1/2) log N − 1`.
-/

open Finset

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.MertensThreeMod

/-- The nontrivial character mod `3`, as an integer-valued function. -/
def chi (n : ℕ) : ℤ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

@[simp] theorem chi_one : chi 1 = 1 := by decide

/-- `chi` is completely multiplicative. -/
theorem chi_mul (m n : ℕ) : chi (m * n) = chi m * chi n := by
  have h : (m * n) % 3 = (m % 3) * (n % 3) % 3 := Nat.mul_mod m n 3
  have hm : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hm' : (m % 3) <;> interval_cases hn' : (n % 3) <;>
    simp [chi, h, hm', hn']

/-- The ideal-counting function of `ℚ(√-3)`: `r n = ∑_{d ∣ n} χ(d)`. -/
def r (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi d

/-- The summatory function `A N = ∑_{n ≤ N} r n`. -/
def A (N : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 N, r n

/-- For `1 ≤ n ≤ N`, the divisors of `n` are exactly the `d ∈ [1, N]` dividing `n`. -/
theorem divisors_eq_filter {n N : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N) :
    n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, hn0⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at hd; omega),
      le_trans (Nat.le_of_dvd (by omega) hd) h2⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, by omega⟩

/-- The number of multiples of `d` in `[1, N]` is `⌊N/d⌋`. -/
theorem card_multiples_Icc (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  classical
  rw [← Nat.card_multiples' N d]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd⟩; exact ⟨by omega, by omega, hd⟩
  · rintro ⟨h1, h2, hd⟩; exact ⟨⟨by omega, by omega⟩, hd⟩

/-- `A N = ∑_{d ≤ N} χ(d) ⌊N/d⌋`. -/
theorem A_eq (N : ℕ) : A N = ∑ d ∈ Finset.Icc 1 N, chi d * (N / d : ℕ) := by
  classical
  unfold A r
  have hinner : ∀ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, chi d
      = ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then chi d else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [divisors_eq_filter hn.1 hn.2, Finset.sum_filter]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_multiples_Icc, nsmul_eq_mul, mul_comm]

/-! ### Partial sums of `chi` and summation by parts -/

/-- Partial sums of `chi`. -/
def X (k : ℕ) : ℤ := ∑ d ∈ Finset.Icc 1 k, chi d

@[simp] theorem X_zero : X 0 = 0 := by simp [X]

theorem X_succ (k : ℕ) : X (k + 1) = X k + chi (k + 1) := by
  rw [X, X, Finset.sum_Icc_succ_top (by omega)]

/-- `X k = 1` if `k ≡ 1 (mod 3)` and `0` otherwise. -/
theorem X_eq (k : ℕ) : X k = if k % 3 = 1 then 1 else 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [X_succ, ih, chi]
      have h : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have h2 : (n + 1) % 3 = (n % 3 + 1) % 3 := by omega
      interval_cases hn : (n % 3) <;> simp [h2, hn]

theorem X_nonneg (k : ℕ) : 0 ≤ X k := by rw [X_eq]; split <;> norm_num

theorem X_le_one (k : ℕ) : X k ≤ 1 := by rw [X_eq]; split <;> norm_num

@[simp] theorem X_one : X 1 = 1 := by rw [X_eq]; norm_num

/-- **Summation by parts.** -/
theorem abel (g : ℕ → ℤ) : ∀ N : ℕ,
    ∑ d ∈ Finset.Icc 1 (N + 1), chi d * g d
      = X (N + 1) * g (N + 1) + ∑ d ∈ Finset.Icc 1 N, X d * (g d - g (d + 1)) := by
  intro N
  induction N with
  | zero => simp [X_eq]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1), ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), X_succ (n + 1)]
      ring

/-- Telescoping. -/
theorem telescope (g : ℕ → ℤ) : ∀ M : ℕ,
    ∑ d ∈ Finset.Icc 1 M, (g d - g (d + 1)) = g 1 - g (M + 1) := by
  intro M
  induction M with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      ring

/-! ### `A N ≍ N` -/

theorem A_le (N : ℕ) : A N ≤ N := by
  rcases N with _ | M
  · simp [A]
  set g : ℕ → ℤ := fun d => ((M + 1) / d : ℕ) with hg
  have hganti : ∀ d, 1 ≤ d → g (d + 1) ≤ g d := by
    intro d hd
    simp only [hg]
    exact_mod_cast Nat.div_le_div_left (by omega) (by omega)
  have hg0 : ∀ d, 0 ≤ g d := fun d => by positivity
  have hkey : A (M + 1) = ∑ d ∈ Finset.Icc 1 (M + 1), chi d * g d := A_eq (M + 1)
  rw [hkey, abel g M]
  have h1 : X (M + 1) * g (M + 1) ≤ g (M + 1) := by
    nlinarith [X_le_one (M + 1), X_nonneg (M + 1), hg0 (M + 1)]
  have h2 : ∑ d ∈ Finset.Icc 1 M, X d * (g d - g (d + 1))
      ≤ ∑ d ∈ Finset.Icc 1 M, (g d - g (d + 1)) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have := hganti d hd.1
    nlinarith [X_le_one d, X_nonneg d]
  rw [telescope g M] at h2
  have hg1 : g 1 = ((M + 1 : ℕ) : ℤ) := by simp [hg]
  linarith [h1, h2, hg1.le, hg1.ge]

theorem A_ge (N : ℕ) : (N : ℤ) ≤ 2 * A N := by
  rcases N with _ | M
  · simp [A]
  set g : ℕ → ℤ := fun d => ((M + 1) / d : ℕ) with hg
  have hganti : ∀ d, 1 ≤ d → g (d + 1) ≤ g d := by
    intro d hd
    simp only [hg]
    exact_mod_cast Nat.div_le_div_left (by omega) (by omega)
  have hg0 : ∀ d, 0 ≤ g d := fun d => by positivity
  have hkey : A (M + 1) = ∑ d ∈ Finset.Icc 1 (M + 1), chi d * g d := A_eq (M + 1)
  rw [hkey, abel g M]
  -- every term is nonnegative, and the `d = 1` term is `g 1 - g 2`
  have hterms : ∀ d ∈ Finset.Icc 1 M, 0 ≤ X d * (g d - g (d + 1)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have := hganti d hd.1
    nlinarith [X_nonneg d]
  have hfirst : X (M + 1) * g (M + 1) ≥ 0 := by nlinarith [X_nonneg (M + 1), hg0 (M + 1)]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · -- `N = 1`
    simp [hg, X_eq]
  · have h1mem : (1 : ℕ) ∈ Finset.Icc 1 M := by simp only [Finset.mem_Icc]; omega
    have hsum : X 1 * (g 1 - g 2) ≤ ∑ d ∈ Finset.Icc 1 M, X d * (g d - g (d + 1)) :=
      Finset.single_le_sum hterms h1mem
    have hg1 : g 1 = ((M + 1 : ℕ) : ℤ) := by simp [hg]
    have hg2 : g 2 = (((M + 1) / 2 : ℕ) : ℤ) := by simp [hg]
    have hdiv2 : (M + 1) ≤ 2 * ((M + 1) - (M + 1) / 2) := by omega
    rw [X_one, one_mul] at hsum
    have : ((M + 1 : ℕ) : ℤ) - (((M + 1) / 2 : ℕ) : ℤ) ≤ ∑ d ∈ Finset.Icc 1 M,
        X d * (g d - g (d + 1)) := by rw [← hg1, ← hg2]; exact hsum
    have hcast : ((M + 1 : ℕ) : ℤ) ≤ 2 * (((M + 1 : ℕ) : ℤ) - (((M + 1) / 2 : ℕ) : ℤ)) := by
      push_cast
      omega
    linarith

/-! ### The Dirichlet swap -/

/-- Sums over `n ≤ N` and divisors `d ∣ n` are sums over pairs `(d, e)` with `d·e ≤ N`. -/
theorem swap {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d (n / d)
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), F d e := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun y => ⟨y.1 * y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨h1, h2⟩, hd, _⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    refine ⟨⟨hd0, le_trans (Nat.le_of_dvd (by omega) hd) h2⟩, ?_, ?_⟩
    · exact Nat.one_le_div_iff hd0 |>.mpr (Nat.le_of_dvd (by omega) hd)
    · exact Nat.div_le_div_right h2 |>.trans (le_refl _)
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hy ⊢
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hy
    refine ⟨⟨Nat.mul_pos hd1 he1, ?_⟩, ⟨e, rfl⟩, by positivity⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le (by omega)).mp heN
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    obtain ⟨⟨h1, h2⟩, hd, _⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    simp [Nat.mul_div_cancel' hd]
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hy
    have hd0 : 0 < d := hy.1.1
    simp [Nat.mul_div_cancel_left e hd0]
  · rintro ⟨n, d⟩ _
    rfl

/-- The hyperbola region is symmetric. -/
theorem hyp_symm {M : Type*} [AddCommMonoid M] (N : ℕ) (G : ℕ → ℕ → M) :
    ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), G d e
      = ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / e), G d e := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun y => ⟨y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hx
    have hde : d * e ≤ N := by
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp heN
    have hle : e ≤ N := le_trans (Nat.le_mul_of_pos_left e (by omega)) hde
    exact ⟨⟨he1, hle⟩, hd1, (Nat.le_div_iff_mul_le (by omega)).mpr hde⟩
  · rintro ⟨e, d⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hy ⊢
    obtain ⟨⟨he1, heN⟩, hd1, hdN⟩ := hy
    have hde : d * e ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hdN
    have hle : d ≤ N := le_trans (Nat.le_mul_of_pos_right d (by omega)) hde
    refine ⟨⟨hd1, hle⟩, he1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
    rw [mul_comm]; exact hde
  · rintro ⟨d, e⟩ _; rfl
  · rintro ⟨e, d⟩ _; rfl
  · rintro ⟨d, e⟩ _; rfl

/-! ### The main identity -/

open ArithmeticFunction in
/-- `∑_{e ≤ M} log e = ∑_{k ≤ M} Λ(k)⌊M/k⌋`. -/
theorem sumLog_eq (M : ℕ) :
    ∑ e ∈ Finset.Icc 1 M, Real.log e = ∑ k ∈ Finset.Icc 1 M, Λ k * ((M / k : ℕ) : ℝ) := by
  have h1 : ∑ e ∈ Finset.Icc 1 M, Real.log e
      = ∑ e ∈ Finset.Icc 1 M, ∑ k ∈ e.divisors, Λ k :=
    Finset.sum_congr rfl fun e _ => vonMangoldt_sum.symm
  rw [h1, swap M (fun a _ => Λ a)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp [mul_comm]

open ArithmeticFunction in
/-- The Dirichlet-series identity in summatory form:
`∑_{n ≤ N} r(n) log n = ∑_{k ≤ N} Λ(k)(1 + χ(k)) A(⌊N/k⌋)`. -/
theorem T_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (r n : ℝ) * Real.log n
      = ∑ k ∈ Finset.Icc 1 N, (Λ k * (1 + (chi k : ℝ))) * ((A (N / k) : ℤ) : ℝ) := by
  classical
  -- unfold `r` and reindex as a sum over pairs
  have step1 : ∑ n ∈ Finset.Icc 1 N, (r n : ℝ) * Real.log n
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d),
          ((chi d : ℝ) * Real.log d + (chi d : ℝ) * Real.log e) := by
    rw [← swap N (fun d e => (chi d : ℝ) * Real.log d + (chi d : ℝ) * Real.log e)]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    rw [r, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mem_divisors] at hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hd.1) hd0
    have hd0' : ((d : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd0).ne'
    have hnd' : (((n / d : ℕ) : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnd).ne'
    have hlog : Real.log (n : ℝ) = Real.log (d : ℝ) + Real.log ((n / d : ℕ) : ℝ) := by
      rw [← Real.log_mul hd0' hnd']
      congr 1
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hd.1]
    rw [hlog]
    ring
  have hsplit : ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d),
        ((chi d : ℝ) * Real.log d + (chi d : ℝ) * Real.log e)
      = (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d)
        + (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log e) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_add_distrib
  -- the two halves
  have hT1 : ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d
      = ∑ k ∈ Finset.Icc 1 N, (Λ k * (chi k : ℝ)) * ((A (N / k) : ℤ) : ℝ) := by
    have hcol : ∀ d ∈ Finset.Icc 1 N,
        (∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d)
          = ∑ k ∈ d.divisors,
              ((chi (k * (d / k)) : ℝ) * Λ k * (((N / (k * (d / k))) : ℕ) : ℝ)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hinner : ∀ k ∈ d.divisors,
          ((chi (k * (d / k)) : ℝ) * Λ k * (((N / (k * (d / k))) : ℕ) : ℝ))
            = (chi d : ℝ) * ((N / d : ℕ) : ℝ) * Λ k := by
        intro k hk
        rw [Nat.mem_divisors] at hk
        rw [Nat.mul_div_cancel' hk.1]
        ring
      have hL : (∑ _e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d)
          = ((N / d : ℕ) : ℝ) * ((chi d : ℝ) * Real.log d) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring
      have hR : (∑ k ∈ d.divisors, (chi d : ℝ) * ((N / d : ℕ) : ℝ) * Λ k)
          = (chi d : ℝ) * ((N / d : ℕ) : ℝ) * Real.log d := by
        rw [← Finset.mul_sum, vonMangoldt_sum]
      rw [Finset.sum_congr rfl hinner, hR, hL]
      ring
    rw [Finset.sum_congr rfl hcol,
      swap N (fun k m => (chi (k * m) : ℝ) * Λ k * (((N / (k * m)) : ℕ) : ℝ))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [A_eq, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [chi_mul, ← Nat.div_div_eq_div_mul]
    simp only [Int.cast_mul, Int.cast_natCast]
    ring
  have hT2 : ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log e
      = ∑ k ∈ Finset.Icc 1 N, Λ k * ((A (N / k) : ℤ) : ℝ) := by
    have hcol : ∀ d ∈ Finset.Icc 1 N,
        (∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log e)
          = ∑ k ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Λ k * (((N / (d * k)) : ℕ) : ℝ) := by
      intro d hd
      rw [← Finset.mul_sum, sumLog_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.div_div_eq_div_mul]
      ring
    rw [Finset.sum_congr rfl hcol,
      hyp_symm N (fun d k => (chi d : ℝ) * Λ k * (((N / (d * k)) : ℕ) : ℝ))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [A_eq, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [mul_comm d k, ← Nat.div_div_eq_div_mul]
    simp only [Int.cast_mul, Int.cast_natCast]
    ring
  rw [step1, hsplit, hT1, hT2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Bounds on `T` -/

/-- General summation by parts. -/
theorem abel_gen (a g : ℕ → ℝ) : ∀ N : ℕ,
    ∑ d ∈ Finset.Icc 1 (N + 1), a d * g d
      = (∑ d ∈ Finset.Icc 1 (N + 1), a d) * g (N + 1)
        + ∑ d ∈ Finset.Icc 1 N, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) := by
  intro N
  induction N with
  | zero => simp
  | succ n ih =>
      have e1 : ∑ x ∈ Finset.Icc 1 (n + 1), a x = (∑ x ∈ Finset.Icc 1 n, a x) + a (n + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e2 : ∑ x ∈ Finset.Icc 1 (n + 1 + 1), a x
          = (∑ x ∈ Finset.Icc 1 (n + 1), a x) + a (n + 1 + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e3 : ∑ d ∈ Finset.Icc 1 (n + 1), (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1))
          = (∑ d ∈ Finset.Icc 1 n, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)))
            + (∑ e ∈ Finset.Icc 1 (n + 1), a e) * (g (n + 1) - g (n + 1 + 1)) :=
        Finset.sum_Icc_succ_top (by omega) _
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1), ih, e3, e2, e1]
      ring

theorem log_succ_sub_le (d : ℕ) (hd : 1 ≤ d) :
    Real.log ((d : ℝ) + 1) - Real.log d ≤ 1 / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : Real.log ((d : ℝ) + 1) - Real.log d = Real.log (((d : ℝ) + 1) / d) := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [h1]
  have h2 : Real.log (((d : ℝ) + 1) / d) ≤ ((d : ℝ) + 1) / d - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : ((d : ℝ) + 1) / d - 1 = 1 / d := by
    field_simp
    ring
  linarith

/-- `T N ≥ (N/2) log N - N`. -/
theorem T_ge (N : ℕ) :
    ((N : ℝ) / 2) * Real.log N - N ≤ ∑ n ∈ Finset.Icc 1 N, (r n : ℝ) * Real.log n := by
  rcases N with _ | M
  · simp
  rw [abel_gen (fun n => (r n : ℝ)) (fun n => Real.log n) M]
  have hAN : (∑ d ∈ Finset.Icc 1 (M + 1), (r d : ℝ)) = ((A (M + 1) : ℤ) : ℝ) := by
    rw [A, Int.cast_sum]
  rw [hAN]
  have hlog0 : (0 : ℝ) ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hAge : ((M + 1 : ℕ) : ℝ) ≤ 2 * ((A (M + 1) : ℤ) : ℝ) := by exact_mod_cast A_ge (M + 1)
  have hterm : ∀ d ∈ Finset.Icc 1 M,
      (-1 : ℝ) ≤ (∑ e ∈ Finset.Icc 1 d, (r e : ℝ)) * (Real.log d - Real.log ((d : ℕ) + 1 : ℕ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hcast : (∑ e ∈ Finset.Icc 1 d, (r e : ℝ)) = ((A d : ℤ) : ℝ) := by rw [A, Int.cast_sum]
    rw [hcast]
    have hAd : ((A d : ℤ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast A_le d
    have hAd0 : (0 : ℝ) ≤ ((A d : ℤ) : ℝ) := by
      have h1 : (0 : ℤ) ≤ (d : ℤ) := by positivity
      have h2 : (0 : ℤ) ≤ 2 * A d := le_trans h1 (A_ge d)
      exact_mod_cast (by omega : (0 : ℤ) ≤ A d)
    have hlogd : Real.log (((d : ℕ) + 1 : ℕ) : ℝ) - Real.log d ≤ 1 / d := by
      have := log_succ_sub_le d hd.1
      push_cast
      exact this
    have hmono : Real.log d ≤ Real.log (((d : ℕ) + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log hd0
      push_cast
      linarith
    have hkey : (d : ℝ) * (Real.log (((d : ℕ) + 1 : ℕ) : ℝ) - Real.log d) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hlogd (le_of_lt hd0)
      rwa [mul_one_div, div_self (ne_of_gt hd0)] at h
    nlinarith [hkey]
  have hsum : (-(M : ℝ)) ≤ ∑ d ∈ Finset.Icc 1 M,
      (∑ e ∈ Finset.Icc 1 d, (r e : ℝ)) * (Real.log d - Real.log ((d : ℕ) + 1 : ℕ)) := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Nat.card_Icc] at this
    simpa using this
  have hAge' : ((M + 1 : ℕ) : ℝ) / 2 ≤ ((A (M + 1) : ℤ) : ℝ) := by linarith
  have hmul : (((M + 1 : ℕ) : ℝ) / 2) * Real.log ((M + 1 : ℕ) : ℝ)
      ≤ ((A (M + 1) : ℤ) : ℝ) * Real.log ((M + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hAge' hlog0
  have hM : (0 : ℝ) ≤ (M : ℝ) := by positivity
  push_cast at hmul hsum ⊢
  linarith

/-! ### Mertens-type lower bound -/

open ArithmeticFunction in
/-- The twisted von Mangoldt function of `ℚ(√-3)`. -/
noncomputable def LK (k : ℕ) : ℝ := Λ k * (1 + (chi k : ℝ))

theorem LK_nonneg (k : ℕ) : 0 ≤ LK k := by
  have h1 : 0 ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (0 : ℝ) ≤ 1 + (chi k : ℝ) := by
    rw [chi]
    split
    · norm_num
    · split <;> norm_num
  exact mul_nonneg h1 h2

theorem LK_le_two_vonMangoldt (k : ℕ) : LK k ≤ 2 * ArithmeticFunction.vonMangoldt k := by
  have h1 : 0 ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (1 : ℝ) + (chi k : ℝ) ≤ 2 := by
    rw [chi]
    split
    · norm_num
    · split <;> norm_num
  rw [LK]
  nlinarith

/-- `∑_{k ≤ N} Λ_K(k)/k ≥ (1/2) log N - 1`. -/
theorem mertens_lower (N : ℕ) :
    (1 / 2 : ℝ) * Real.log N - 1 ≤ ∑ k ∈ Finset.Icc 1 N, LK k / k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT := T_ge N
  rw [T_eq N] at hT
  have hb : ∀ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt k * (1 + (chi k : ℝ)))
        * ((A (N / k) : ℤ) : ℝ) ≤ (N : ℝ) * (LK k / k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hA : ((A (N / k) : ℤ) : ℝ) ≤ (N : ℝ) / k := by
      have h1 : ((A (N / k) : ℤ) : ℝ) ≤ ((N / k : ℕ) : ℝ) := by
        have h := (Int.cast_le (R := ℝ)).mpr (A_le (N / k))
        rwa [Int.cast_natCast] at h
      have h2 : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
      linarith
    have hLK := LK_nonneg k
    have : (N : ℝ) * (LK k / k) = LK k * ((N : ℝ) / k) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hA hLK
  have hstep : ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt k * (1 + (chi k : ℝ)))
      * ((A (N / k) : ℤ) : ℝ) ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, LK k / k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hb
  have hfin := le_trans hT hstep
  have hS : (N : ℝ) * ((1 / 2 : ℝ) * Real.log N - 1)
      ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, LK k / k := by nlinarith [hfin]
  exact le_of_mul_le_mul_left hS hN0

/-! ### Mertens upper bound (all primes), from Chebyshev -/

open ArithmeticFunction Chebyshev in
theorem psi_eq_sum (N : ℕ) : ψ (N : ℝ) = ∑ k ∈ Finset.Icc 1 N, Λ k := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

open ArithmeticFunction in
/-- `∑_{k ≤ N} Λ(k)/k ≤ log N + (log 4 + 4)`. -/
theorem mertens_upper (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Λ k / k ≤ Real.log N + (Real.log 4 + 4) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- lower bound for the divisor sum
  have hlow : (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, Λ k / k) - (∑ k ∈ Finset.Icc 1 N, Λ k)
      ≤ ∑ k ∈ Finset.Icc 1 N, Λ k * ((N / k : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hfl : (N : ℝ) / k - 1 ≤ ((N / k : ℕ) : ℝ) := by
      have hk' : 0 < k := by omega
      have hnat : N < k * (N / k) + k := by
        have hdm := Nat.div_add_mod N k
        have hmod := Nat.mod_lt N hk'
        omega
      have h2 : (N : ℝ) < (k : ℝ) * ((N / k : ℕ) : ℝ) + (k : ℝ) := by exact_mod_cast hnat
      rw [sub_le_iff_le_add, div_le_iff₀ hk0]
      linarith
    have hLam : 0 ≤ Λ k := vonMangoldt_nonneg
    have : (N : ℝ) * (Λ k / k) - Λ k = Λ k * ((N : ℝ) / k - 1) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hfl hLam
  -- upper bound for the log sum
  have hup : ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ (N : ℝ) * Real.log N := by
    have : ∀ n ∈ Finset.Icc 1 N, Real.log n ≤ Real.log N := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    calc ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log N :=
          Finset.sum_le_sum this
      _ = (N : ℝ) * Real.log N := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          push_cast
          ring
  have hpsi : (∑ k ∈ Finset.Icc 1 N, Λ k) ≤ (Real.log 4 + 4) * N := by
    rw [← psi_eq_sum N]
    exact Chebyshev.psi_le_const_mul_self (by positivity)
  rw [sumLog_eq N] at hup
  have hkey : (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, Λ k / k)
      ≤ (N : ℝ) * Real.log N + (Real.log 4 + 4) * N := by linarith
  have := le_of_mul_le_mul_left (by nlinarith [hkey] :
    (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, Λ k / k) ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4))) hN0
  exact this

/-! ### `∑_{p ≤ N} log p / p² = O(1)` -/

open Chebyshev in
theorem theta_eq_sum (N : ℕ) :
    θ (N : ℝ) = ∑ k ∈ Finset.Icc 1 N, (if k.Prime then Real.log k else 0) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [Chebyshev.theta, Nat.floor_natCast, hIoc, Finset.sum_filter]

/-- Telescoping. -/
theorem telescope_inv (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, ((1 : ℝ) / d - 1 / (d + 1)) ≤ 1 := by
  have h : ∀ M : ℕ, ∑ d ∈ Finset.Icc 1 M, ((1 : ℝ) / d - 1 / (d + 1))
      = 1 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
        push_cast
        ring
  rw [h M]
  have h1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  linarith

/-- `∑_{p ≤ N} log p / p² ≤ 4 (log 4 + 4)`. -/
theorem sum_log_div_sq_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (if k.Prime then Real.log k else 0) / (k : ℝ) ^ 2
      ≤ 4 * (Real.log 4 + 4) := by
  set c : ℝ := Real.log 4 + 4 with hc
  have hc0 : (0 : ℝ) < c := by
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [hc]; linarith
  rcases N with _ | M
  · simp
    positivity
  set a : ℕ → ℝ := fun k => (if k.Prime then Real.log k else 0) with ha
  set g : ℕ → ℝ := fun k => 1 / (k : ℝ) ^ 2 with hg
  have hkey : ∑ k ∈ Finset.Icc 1 (M + 1), a k * g k
      = (∑ k ∈ Finset.Icc 1 (M + 1), a k) * g (M + 1)
        + ∑ d ∈ Finset.Icc 1 M, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) :=
    abel_gen a g M
  have hpartial : ∀ d : ℕ, (∑ e ∈ Finset.Icc 1 d, a e) ≤ c * d := by
    intro d
    have h1 : Chebyshev.theta (d : ℝ) ≤ Real.log 4 * d :=
      Chebyshev.theta_le_log4_mul_x (by positivity)
    rw [ha, ← theta_eq_sum d]
    have hd0 : (0 : ℝ) ≤ d := by positivity
    simp only [hc]
    nlinarith [h1, hd0]
  have hfirst : (∑ k ∈ Finset.Icc 1 (M + 1), a k) * g (M + 1) ≤ c := by
    have h1 := hpartial (M + 1)
    have hMpos : (0 : ℝ) < ((M : ℝ) + 1) := by positivity
    have hg0 : g (M + 1) = 1 / ((M : ℝ) + 1) ^ 2 := by rw [hg]; push_cast; ring
    rw [hg0]
    push_cast at h1
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have hsq : ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [h1, hMpos, hc0, hsq]
  have hterm : ∀ d ∈ Finset.Icc 1 M,
      (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) ≤ 3 * c * ((1 : ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hgd : g d - g (d + 1) = (2 * (d : ℝ) + 1) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2) := by
      rw [hg]
      push_cast
      field_simp
      ring
    have hgd0 : 0 ≤ g d - g (d + 1) := by rw [hgd]; positivity
    have hbnd : (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) ≤ (c * d) * (g d - g (d + 1)) :=
      mul_le_mul_of_nonneg_right (hpartial d) hgd0
    refine le_trans hbnd ?_
    rw [hgd]
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
    have hd1ne : (d : ℝ) + 1 ≠ 0 := by positivity
    have hrhs : (1 : ℝ) / d - 1 / ((d : ℝ) + 1) = 1 / ((d : ℝ) * ((d : ℝ) + 1)) := by
      field_simp
      ring
    have hL : (c * (d : ℝ)) * ((2 * (d : ℝ) + 1) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2))
        = (c * (d : ℝ) * (2 * (d : ℝ) + 1)) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2) := by ring
    have hR : 3 * c * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)))
        = (3 * c) / ((d : ℝ) * ((d : ℝ) + 1)) := by ring
    rw [hrhs, hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
    have key : 3 * c * ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2)
        - c * (d : ℝ) * (2 * (d : ℝ) + 1) * ((d : ℝ) * ((d : ℝ) + 1))
        = c * (d : ℝ) ^ 2 * ((d : ℝ) + 1) * ((d : ℝ) + 2) := by ring
    have hpos : 0 ≤ c * (d : ℝ) ^ 2 * ((d : ℝ) + 1) * ((d : ℝ) + 2) := by positivity
    linarith [key, hpos]
  have hsum : ∑ d ∈ Finset.Icc 1 M, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) ≤ 3 * c := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have h := telescope_inv M
    nlinarith [hc0]
  have hrewrite : ∑ k ∈ Finset.Icc 1 (M + 1),
      (if k.Prime then Real.log k else 0) / (k : ℝ) ^ 2
      = ∑ k ∈ Finset.Icc 1 (M + 1), a k * g k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha, hg]
    ring
  rw [hrewrite, hkey]
  linarith [hfirst, hsum]

/-! ### The prime-power (non-prime) tail of `∑ Λ(k)/k` -/

/-- For `j ≥ 2`, `∑_{p ≤ M} log p / p^j ≤ (1/2)^{j-2} · 4(log 4 + 4)`. -/
theorem sum_log_div_pow_le (M j : ℕ) (hj : 2 ≤ j) :
    ∑ p ∈ (Finset.Icc 1 M).filter (fun p => Nat.Prime p), Real.log p / (p : ℝ) ^ j
      ≤ ((1 : ℝ) / 2) ^ (j - 2) * (4 * (Real.log 4 + 4)) := by
  have hpow2 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (j - 2) := by positivity
  have key : ∀ p ∈ (Finset.Icc 1 M).filter (fun p => Nat.Prime p),
      Real.log p / (p : ℝ) ^ j
        ≤ ((1 : ℝ) / 2) ^ (j - 2) * ((if p.Prime then Real.log p else 0) / (p : ℝ) ^ 2) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp := hp.2
    rw [if_pos hpp]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hpow : (p : ℝ) ^ j = (p : ℝ) ^ 2 * (p : ℝ) ^ (j - 2) := by
      rw [← pow_add]; congr 1; omega
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hR : ((1 : ℝ) / 2) ^ (j - 2) * (Real.log p / (p : ℝ) ^ 2)
        = Real.log p / ((p : ℝ) ^ 2 * 2 ^ (j - 2)) := by
      rw [div_pow, one_pow]
      field_simp
    rw [hpow, hR]
    have h2p : (2 : ℝ) ^ (j - 2) ≤ (p : ℝ) ^ (j - 2) :=
      pow_le_pow_left₀ (by norm_num) hp2 _
    have hd : (0 : ℝ) < (p : ℝ) ^ 2 * 2 ^ (j - 2) := by
      have : (0 : ℝ) < (p : ℝ) := by linarith
      positivity
    exact div_le_div_of_nonneg_left hlog hd (by nlinarith [sq_nonneg ((p:ℝ))])
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hpow2
  refine le_trans ?_ (sum_log_div_sq_le M)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  positivity

/-- Geometric bookkeeping for the outer sum over exponents. -/
theorem sum_geom_shift (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (if 2 ≤ j then ((1 : ℝ) / 2) ^ (j - 2) else 0) ≤ 4 := by
  rw [show Finset.Icc 1 J = Finset.Ico 1 (J + 1) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine le_trans (Finset.sum_le_sum (g := fun i => 2 * ((1 : ℝ) / 2) ^ i) (fun i _ => ?_)) ?_
  · show (if 2 ≤ 1 + i then ((1 : ℝ) / 2) ^ (1 + i - 2) else 0) ≤ 2 * ((1 : ℝ) / 2) ^ i
    rcases i with _ | i
    · norm_num
    · rw [if_pos (by omega), show 1 + (i + 1) - 2 = i by omega]
      rw [div_pow, one_pow, div_pow, one_pow]
      rw [pow_succ]
      rw [mul_comm (2:ℝ)]
      rw [div_le_iff₀ (by positivity)]
      field_simp
      norm_num
  · rw [← Finset.mul_sum]
    have := sum_geometric_two_le J
    linarith

open ArithmeticFunction in
/-- The whole non-prime part of `∑_{k ≤ N} Λ(k)/k` is bounded by an absolute constant. -/
theorem tail_le (N : ℕ) :
    ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k.Prime), Λ k / (k : ℝ)
      ≤ 16 * (Real.log 4 + 4) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set f : ℕ → ℝ := fun n => if n.Prime then 0 else Λ n / n with hf
  have h1 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k.Prime), Λ k / (k : ℝ)
      = ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => IsPrimePow n), f n := by
    rw [Finset.sum_filter, Finset.sum_filter]
    have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIoc]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [hf, hp, hp.isPrimePow]
    · by_cases hpp : IsPrimePow n
      · simp [hf, hp, hpp]
      · simp [hf, hp, hpp, ArithmeticFunction.vonMangoldt_apply]
  have h2 := Chebyshev.sum_PrimePow_eq_sum_sum f (x := (N : ℝ)) (by positivity)
  rw [Nat.floor_natCast] at h2
  rw [h1, h2]
  set J : ℕ := ⌊Real.log (N : ℝ) / Real.log 2⌋₊ with hJ
  have hinner : ∀ j ∈ Finset.Icc 1 J,
      ∑ p ∈ (Finset.Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / j)⌋₊).filter (fun p => Nat.Prime p), f (p ^ j)
        ≤ (if 2 ≤ j then ((1 : ℝ) / 2) ^ (j - 2) else 0) * (4 * (Real.log 4 + 4)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    set M : ℕ := ⌊(N : ℝ) ^ ((1 : ℝ) / j)⌋₊ with hM
    have hIoc : Finset.Ioc 0 M = Finset.Icc 1 M := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rcases eq_or_lt_of_le hj.1 with h1j | h2j
    · -- j = 1 : every term vanishes because `p ^ 1 = p` is prime
      rw [if_neg (by omega)]
      rw [zero_mul]
      refine le_of_eq ?_
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_filter] at hp
      simp [hf, ← h1j, hp.2]
    · -- j ≥ 2
      have hj2 : 2 ≤ j := h2j
      rw [if_pos hj2, hIoc]
      refine le_trans (le_of_eq ?_) (sum_log_div_pow_le M j hj2)
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      have hpp := hp.2
      have hnp : ¬ (p ^ j).Prime := by
        intro hc
        rcases hc.eq_one_or_self_of_dvd p (dvd_pow_self p (by omega : j ≠ 0)) with h | h
        · exact hpp.ne_one h
        · have hlt : p ^ 1 < p ^ j := Nat.pow_lt_pow_right hpp.one_lt (by omega)
          rw [pow_one] at hlt
          omega
      have hΛ : Λ (p ^ j) = Real.log p := by
        rw [ArithmeticFunction.vonMangoldt_apply, if_pos (hpp.isPrimePow.pow (by omega)),
          Nat.Prime.pow_minFac hpp (by omega)]
      simp only [hf, if_neg hnp, hΛ, Nat.cast_pow]
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.sum_mul]
  have hg := sum_geom_shift J
  nlinarith [hg, hlog4]

/-! ### Extracting the primes `≡ 1 (mod 3)` -/

/-- `∑_{p ≤ N, p prime, p ≡ 1 (3)} log p / p`. -/
noncomputable def S1 (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % 3 = 1), Real.log p / (p : ℝ)

open ArithmeticFunction in
theorem S1_lower (N : ℕ) :
    (1 / 4 : ℝ) * Real.log N - (1 / 2 + Real.log 3 / 6 + 16 * (Real.log 4 + 4)) ≤ S1 N := by
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hml := mertens_lower N
  -- split into primes / non-primes
  have hsplit :
      ∑ k ∈ Finset.Icc 1 N, LK k / (k : ℝ)
        = ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k), LK k / (k : ℝ)
          + ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ Nat.Prime k), LK k / (k : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- non-prime part
  have hnp : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ Nat.Prime k), LK k / (k : ℝ)
      ≤ 32 * (Real.log 4 + 4) := by
    have hstep : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ Nat.Prime k),
        LK k / (k : ℝ) ≤ 2 * (Λ k / (k : ℝ)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1.1
      have := LK_le_two_vonMangoldt k
      rw [div_le_iff₀ hk0]
      have h2 : 2 * (Λ k / (k : ℝ)) * k = 2 * Λ k := by field_simp
      rw [h2]
      exact this
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have := tail_le N
    linarith
  -- prime part
  have hp : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k), LK k / (k : ℝ)
      ≤ 2 * S1 N + Real.log 3 / 3 := by
    have hstep : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k),
        LK k / (k : ℝ)
          ≤ 2 * (if k % 3 = 1 then Real.log k / (k : ℝ) else 0)
            + (if k = 3 then Real.log 3 / 3 else 0) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hkp := hk.2
      have hΛ : Λ k = Real.log k := ArithmeticFunction.vonMangoldt_apply_prime hkp
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkp.pos
      have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hkp.one_le)
      have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h3 with h | h | h
      · -- 3 ∣ k, k prime ⇒ k = 3
        have hk3 : k = 3 := by
          have hdvd : (3 : ℕ) ∣ k := Nat.dvd_of_mod_eq_zero h
          rcases (Nat.Prime.eq_one_or_self_of_dvd hkp 3 hdvd) with h' | h'
          · omega
          · omega
        subst hk3
        simp only [LK, chi, hΛ]
        norm_num
      · rw [if_pos h, if_neg (by omega)]
        simp only [LK, chi, hΛ, if_pos h]
        push_cast
        rw [add_zero]
        have : Real.log k * (1 + 1) / (k : ℝ) = 2 * (Real.log k / k) := by ring
        rw [this]
      · rw [if_neg (by omega), if_neg (by omega)]
        simp only [LK, chi, hΛ, if_neg (by omega : ¬ k % 3 = 1), if_pos h]
        push_cast
        norm_num
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k),
        (if k % 3 = 1 then Real.log k / (k : ℝ) else 0) = S1 N := by
      rw [S1, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h1 : Nat.Prime k <;> by_cases h2 : k % 3 = 1 <;> simp [h1, h2]
    have h2 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k),
        (if k = 3 then Real.log 3 / 3 else 0) ≤ Real.log 3 / 3 := by
      rw [Finset.sum_ite_eq' ((Finset.Icc 1 N).filter (fun k => Nat.Prime k)) 3
        (fun _ => Real.log 3 / 3)]
      split
      · exact le_rfl
      · positivity
    rw [h1]
    linarith
  linarith [hml, hsplit ▸ hml]

open ArithmeticFunction in
theorem S1_upper (M : ℕ) : S1 M ≤ Real.log M + (Real.log 4 + 4) := by
  refine le_trans ?_ (mertens_upper M)
  have h : S1 M
      = ∑ p ∈ (Finset.Icc 1 M).filter (fun p => Nat.Prime p ∧ p % 3 = 1), Λ p / (p : ℝ) := by
    rw [S1]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2.1]
  rw [h]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  have h1 : (0 : ℝ) ≤ Λ i := ArithmeticFunction.vonMangoldt_nonneg
  positivity

/-- The absolute constant governing where the Chebyshev-type lower bound kicks in. -/
noncomputable def C4 : ℝ :=
  (1 / 2 + Real.log 3 / 6 + 16 * (Real.log 4 + 4)) + (Real.log 4 + 4)

theorem C4_pos : 0 < C4 := by
  have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [C4]; linarith

/-- The threshold `m₀`. -/
noncomputable def m0 : ℕ := ⌈Real.exp (2 * C4)⌉₊

theorem log_ge_of_m0_le {m : ℕ} (hm : m0 ≤ m) : 2 * C4 ≤ Real.log m := by
  have h1 : Real.exp (2 * C4) ≤ (m0 : ℝ) := Nat.le_ceil _
  have h2 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h3 : Real.exp (2 * C4) ≤ (m : ℝ) := le_trans h1 h2
  have := Real.log_le_log (Real.exp_pos _) h3
  rwa [Real.log_exp] at this

theorem two_le_m0 : 2 ≤ m0 := by
  have hC := C4_pos
  have h1 : (1 : ℝ) < Real.exp (2 * C4) := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have : (1 : ℝ) < (m0 : ℝ) := lt_of_lt_of_le h1 (Nat.le_ceil _)
  have : 1 < m0 := by exact_mod_cast this
  omega

/-- Chebyshev-type lower bound for primes `≡ 1 (mod 3)` along `N = m^8`. -/
theorem count_lower (m : ℕ) (hm : m0 ≤ m) :
    (m : ℝ) / 16
      ≤ (((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card : ℝ) := by
  have hm2 : 2 ≤ m := le_trans two_le_m0 hm
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hlogm : 2 * C4 ≤ Real.log m := log_ge_of_m0_le hm
  have hC := C4_pos
  have hlogm0 : 0 < Real.log m := by linarith
  set F : Finset ℕ := (Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1) with hF
  set G : Finset ℕ := (Finset.Icc 1 m).filter (fun p => Nat.Prime p ∧ p % 3 = 1) with hG
  have hGF : G ⊆ F := by
    refine Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right ?_)
    calc m = m ^ 1 := (pow_one m).symm
    _ ≤ m ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  -- the difference of the two partial sums
  have hdiff : S1 (m ^ 8) - S1 m = ∑ p ∈ F \ G, Real.log p / (p : ℝ) := by
    rw [Finset.sum_sdiff_eq_sub hGF, S1, S1]
  -- lower bound for the difference
  have hlow : Real.log m - C4 ≤ S1 (m ^ 8) - S1 m := by
    have h1 := S1_lower (m ^ 8)
    have h2 := S1_upper m
    have hcast : ((m ^ 8 : ℕ) : ℝ) = (m : ℝ) ^ 8 := by push_cast; ring
    rw [hcast, Real.log_pow] at h1
    rw [C4]
    push_cast at h1
    linarith
  -- upper bound for the difference
  have hup : ∑ p ∈ F \ G, Real.log p / (p : ℝ)
      ≤ (F.card : ℝ) * (8 * Real.log m / (m : ℝ)) := by
    have hstep : ∀ p ∈ F \ G, Real.log p / (p : ℝ) ≤ 8 * Real.log m / (m : ℝ) := by
      intro p hp
      rw [Finset.mem_sdiff, hF, hG, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hp1, hp2⟩, hpP⟩, hpG⟩ := hp
      have hpm : m < p := by
        by_contra hc
        exact hpG ⟨Finset.mem_Icc.mpr ⟨hp1, by omega⟩, hpP⟩
      have hpR : (m : ℝ) < (p : ℝ) := by exact_mod_cast hpm
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hlogp : Real.log p ≤ 8 * Real.log m := by
        have h1 : ((p : ℝ)) ≤ (m : ℝ) ^ 8 := by
          have : (p : ℝ) ≤ ((m ^ 8 : ℕ) : ℝ) := by exact_mod_cast hp2
          rwa [show ((m ^ 8 : ℕ) : ℝ) = (m : ℝ) ^ 8 by push_cast; ring] at this
        have := Real.log_le_log hp0 h1
        rwa [Real.log_pow] at this
        <;> norm_num
      have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
      calc Real.log p / (p : ℝ) ≤ (8 * Real.log m) / (p : ℝ) := by gcongr
        _ ≤ (8 * Real.log m) / (m : ℝ) := by
            refine div_le_div_of_nonneg_left (by linarith) (by linarith) (le_of_lt hpR)
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((F \ G).card : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
    have hpos : (0 : ℝ) ≤ 8 * Real.log m / (m : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right hcard hpos
  -- combine
  have hkey : Real.log m - C4 ≤ (F.card : ℝ) * (8 * Real.log m / (m : ℝ)) := by
    rw [hdiff] at hlow
    linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hhalf : Real.log m / 2 ≤ (F.card : ℝ) * (8 * Real.log m / (m : ℝ)) := by linarith
  have h8 : (F.card : ℝ) * (8 * Real.log m / (m : ℝ))
      = 16 * (F.card : ℝ) * Real.log m / (m : ℝ) / 2 := by
    field_simp
    ring
  rw [h8, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2),
    le_div_iff₀ hm0] at hhalf
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16)]
  nlinarith [hhalf, hlogm0, hm0]

/-! ### The polynomial bound on the `i`-th prime `≡ 1 (mod 3)` -/

theorem card_eq_count (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card
      = Nat.count (fun n => Nat.Prime n ∧ n % 3 = 1) (N + 1) := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, hP⟩
    exact ⟨by omega, hP⟩
  · rintro ⟨h1, hP⟩
    refine ⟨⟨?_, by omega⟩, hP⟩
    exact hP.1.one_lt.le.trans' (by norm_num)

/-- **The i-th prime `≡ 1 (mod 3)` is polynomially bounded.** -/
theorem primes_one_mod_three_poly_bound :
    ∃ A : ℕ, 0 < A ∧ ∀ i : ℕ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i ≤ (i + 2) ^ A := by
  refine ⟨max 40 (m0 ^ 8), lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun i => ?_⟩
  set A : ℕ := max 40 (m0 ^ 8) with hA
  set m : ℕ := max (16 * (i + 2)) m0 with hm
  have hmm0 : m0 ≤ m := le_max_right _ _
  have hmi : 16 * (i + 2) ≤ m := le_max_left _ _
  -- there are at least `i + 2` primes `≡ 1 (mod 3)` below `m ^ 8`
  have hcl := count_lower m hmm0
  have hcard : i + 2 ≤ ((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card := by
    have h1 : ((i : ℝ) + 2) ≤ (m : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
      have : ((16 * (i + 2) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmi
      push_cast at this
      linarith
    have h2 : ((i : ℝ) + 2)
        ≤ (((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card : ℝ) :=
      le_trans h1 hcl
    have h3 : (((i + 2 : ℕ)) : ℝ)
        ≤ (((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  -- turn it into a bound on `Nat.nth`
  have hlt : i < Nat.count (fun n => Nat.Prime n ∧ n % 3 = 1) (m ^ 8 + 1) := by
    rw [← card_eq_count]
    omega
  have hnth := Nat.nth_lt_of_lt_count hlt
  have hle : Nat.nth (fun n => Nat.Prime n ∧ n % 3 = 1) i ≤ m ^ 8 := by omega
  refine hle.trans ?_
  -- `m ^ 8 ≤ (i + 2) ^ A`
  have hi2 : 2 ≤ i + 2 := by omega
  rcases le_total (m0 : ℕ) (16 * (i + 2)) with h | h
  · have hmv : m = 16 * (i + 2) := max_eq_left h
    rw [hmv]
    have h1 : (16 * (i + 2)) ^ 8 = 2 ^ 32 * (i + 2) ^ 8 := by ring
    have h2 : (2 : ℕ) ^ 32 ≤ (i + 2) ^ 32 := Nat.pow_le_pow_left hi2 32
    calc (16 * (i + 2)) ^ 8 = 2 ^ 32 * (i + 2) ^ 8 := h1
      _ ≤ (i + 2) ^ 32 * (i + 2) ^ 8 := Nat.mul_le_mul_right _ h2
      _ = (i + 2) ^ 40 := by rw [← pow_add]
      _ ≤ (i + 2) ^ A := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  · have hmv : m = m0 := max_eq_right h
    rw [hmv]
    calc m0 ^ 8 ≤ 2 ^ (m0 ^ 8) := Nat.le_of_lt (Nat.lt_two_pow_self)
      _ ≤ (i + 2) ^ (m0 ^ 8) := Nat.pow_le_pow_left hi2 _
      _ ≤ (i + 2) ^ A := Nat.pow_le_pow_right (by omega) (le_max_right _ _)

end Workspace.ProofLemmas.MertensThreeMod
