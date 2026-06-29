-- Cited from: Folland, G. B. (1999). Real Analysis: Modern Techniques and Their Applications (2nd ed.). Wiley. §8.3 (Fourier transform identities). Also Feller, W. (1971). An Introduction to Probability Theory and Its Applications, Vol. II. Wiley. Chapter XV §4 (characteristic functions of standard discrete distributions).
-- Paper label: Standard Fourier-of-binomial
-- NL statement: For every n ∈ ℕ with n ≥ 1 and every ξ ∈ ℝ with |ξ| ≤ π, the discrete Fourier transform of the centered binomial pmf p(r) := bin(n, 1/2, r) := C(n, r) · 2^(-n) (extended by zero outside {0, …, n}), evaluated at ξ, equals exp(-i·ξ·n/2) · cos(ξ/2)^n.
import Mathlib

set_option maxHeartbeats 1000000

/--
**Standard Fourier-of-binomial closed form.** For `n ≥ 1` and `|ξ| ≤ π`, the
discrete Fourier transform of the symmetric binomial pmf
`p(r) = C(n, r) · 2^(-n)` (extended by zero outside `{0, …, n}`),
evaluated at `ξ`, equals `exp(-i·ξ·n/2) · cos(ξ/2)^n`.

The discrete Fourier sum is `∑' r : ℤ, p(r) · exp(-i ξ r)`. The summand
vanishes outside `0 ≤ r ≤ n`, so the sum reduces to a finite Bernstein-style
binomial expansion.
-/
theorem BinomialFourierClosedForm :
    ∀ (n : ℕ), 1 ≤ n →
      ∀ ξ : ℝ, |ξ| ≤ Real.pi →
        (∑' r : ℤ,
            (if 0 ≤ r ∧ r ≤ (n : ℤ) then
              ((Nat.choose n r.toNat : ℂ) * ((2 : ℂ) ^ n)⁻¹)
             else 0) *
              Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
          = Complex.exp (-(Complex.I * (ξ : ℂ) * ((n : ℂ) / 2))) *
              (Real.cos (ξ / 2) : ℂ) ^ n := by
  intro n hn ξ hξ
  rw [tsum_eq_sum (s := Finset.Icc (0:ℤ) (n:ℤ))]
  rotate_left
  · intro b hb
    rw [if_neg (by simp only [Finset.mem_Icc, not_and, not_le] at hb; omega), zero_mul]
  -- Reindex the finite ℤ-sum over Icc 0 n to a ℕ-sum over range (n+1).
  rw [show Finset.Icc (0:ℤ) (n:ℤ) = Finset.map ⟨fun k : ℕ => (k : ℤ), fun a b h => by simpa using h⟩ (Finset.range (n+1)) by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨x.toNat, by omega, by omega⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp hk⟩]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hsimp : ∀ x ∈ Finset.range (n+1),
      (if 0 ≤ (x:ℤ) ∧ (x:ℤ) ≤ (n:ℤ) then ((n.choose ((x:ℤ)).toNat : ℂ) * ((2:ℂ) ^ n)⁻¹) else 0)
          * Complex.exp (-(Complex.I * ↑ξ * (((x:ℤ)):ℂ)))
        = (n.choose x : ℂ) * ((2:ℂ)^n)⁻¹ * Complex.exp (-(Complex.I * ↑ξ * (x:ℂ))) := by
    intro x hx
    simp only [Finset.mem_range] at hx
    rw [if_pos (by exact ⟨by positivity, by exact_mod_cast Nat.lt_succ_iff.mp hx⟩)]
    simp
  rw [Finset.sum_congr rfl hsimp]
  -- exp(-(I ξ x)) = (exp(-(I ξ)))^x
  have hexp : ∀ x : ℕ, Complex.exp (-(Complex.I * ↑ξ * (x:ℂ))) = (Complex.exp (-(Complex.I * ↑ξ)))^x := by
    intro x; rw [← Complex.exp_nat_mul]; ring_nf
  -- binomial theorem
  have hbin : ∑ x ∈ Finset.range (n + 1), (n.choose x : ℂ) * (Complex.exp (-(Complex.I * ↑ξ)))^x
      = (Complex.exp (-(Complex.I * ↑ξ)) + 1)^n := by
    rw [add_pow]; apply Finset.sum_congr rfl; intro x hx; rw [one_pow, mul_one]; ring
  have hlhs : ∑ x ∈ Finset.range (n + 1), (n.choose x : ℂ) * (2 ^ n)⁻¹ * Complex.exp (-(Complex.I * ↑ξ * ↑x))
      = (2^n)⁻¹ * (Complex.exp (-(Complex.I * ↑ξ)) + 1)^n := by
    rw [← hbin, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; rw [hexp]; ring
  rw [hlhs]
  -- (1 + exp(-iξ))/2 = exp(-iξ/2) · cos(ξ/2)
  have hbase : (Complex.exp (-(Complex.I * ↑ξ)) + 1)
      = 2 * (Complex.exp (-(Complex.I * ((ξ:ℂ)/2))) * (Real.cos (ξ/2):ℂ)) := by
    rw [Complex.ofReal_cos, mul_comm (Complex.exp _), ← mul_assoc, Complex.two_cos,
        add_mul, ← Complex.exp_add, ← Complex.exp_add]
    rw [show (↑(ξ / 2) * Complex.I + -(Complex.I * (↑ξ / 2))) = 0 by push_cast; ring,
        show (-↑(ξ / 2) * Complex.I + -(Complex.I * (↑ξ / 2))) = -(Complex.I * ↑ξ) by push_cast; ring,
        Complex.exp_zero]
    ring
  rw [hbase, mul_pow, mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n two_ne_zero),
      one_mul, ← Complex.exp_nat_mul]
  rw [show (↑n * -(Complex.I * (↑ξ / 2))) = -(Complex.I * ↑ξ * (↑n / 2)) by ring]
