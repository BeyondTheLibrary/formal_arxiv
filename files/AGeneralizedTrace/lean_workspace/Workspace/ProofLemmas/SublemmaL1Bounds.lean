import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.L1Distance

/--
`SublemmaL1Bounds` (parametric form).

Fix `c' := 1/(4·e²·√(2π))`, `c_1 := c'/2 = 1/(8·e²·√(2π))`, and
`C_1 := 2·c' = 1/(2·e²·√(2π))`.

For every `n ≥ 1` with `n ≡ 1 (mod 8)` and every pair of probability
vectors `Se, So : ProbVec n` whose coordinates have the parametric form
used by `SublemmaWitnessConstruction` — i.e.

* `Se.p i = α · bin(n, 1/2, i)` if `i` is even, `0` if `i` is odd;
* `So.p i = α · bin(n, 1/2, i)` if `i` is odd,  `0` if `i` is even,

where `α = c' · √n` and `bin(n, 1/2, i) = C(n, i) · 2^(-n)` —
the L¹ distance between `Se` and `So` satisfies the two-sided bound

  `c_1 · √n ≤ L1Distance Se So ≤ C_1 · √n`.

Mathematically: the per-index identity `|Se.p i - So.p i| = α · bin(n, 1/2, i)`
(case-split on `i % 2`) sums to `α · (1 - bin(n, 1/2, 0)) = c' · √n · (1 - 2^(-n))`,
and `1/2 ≤ 1 - 2^(-n) ≤ 1` for `n ≥ 1` brackets the result.
-/
theorem SublemmaL1Bounds :
    ∀ n : ℕ, 1 ≤ n → n % 8 = 1 →
      ∀ Se So : Workspace.Types.ProbVec.ProbVec n,
        (∀ i : Fin n, Se.p i =
          (if (i.val) % 2 = 0
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        (∀ i : Fin n, So.p i =
          (if (i.val) % 2 = 1
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        (1 / (8 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
          ≤ Workspace.Types.L1Distance.L1Distance Se So ∧
        Workspace.Types.L1Distance.L1Distance Se So
          ≤ (1 / (2 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n := by
  intro n hn _hmod Se So hSe hSo
  -- Set abbreviations
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  -- Positivity facts
  have hexp_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsqrt_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hpi_pos
  have hc'_pos : 0 < c' := by
    rw [hc'_def]; positivity
  have hsqrtn_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  -- Per-index identity: |Se.p i - So.p i| = c' · √n · C(n, i.val) · 2^(-n)
  have key_id : ∀ i : Fin n,
      |Se.p i - So.p i| = c' * Real.sqrt n * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) := by
    intro i
    have hpos : 0 ≤ c' * Real.sqrt n * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹) := by
      have h2n : (0 : ℝ) ≤ (2 ^ n : ℝ)⁻¹ := by positivity
      have hch : (0 : ℝ) ≤ (Nat.choose n i.val : ℝ) := by positivity
      have : 0 ≤ c' * Real.sqrt n := mul_nonneg hc'_pos.le hsqrtn_nn
      positivity
    rw [hSe i, hSo i]
    by_cases hev : i.val % 2 = 0
    · -- even: Se = c'·√n·C·2^(-n), So = 0
      have hodd : ¬ (i.val % 2 = 1) := by omega
      rw [if_pos hev, if_neg hodd]
      rw [sub_zero, abs_of_nonneg hpos]
    · -- odd: Se = 0, So = c'·√n·C·2^(-n)
      have hodd : i.val % 2 = 1 := by omega
      rw [if_neg hev, if_pos hodd]
      rw [zero_sub, abs_neg, abs_of_nonneg hpos]
  -- Compute L1Distance
  have l1_eq : Workspace.Types.L1Distance.L1Distance Se So
      = c' * Real.sqrt n * (2 ^ n : ℝ)⁻¹ * ((2 : ℝ) ^ n - 1) := by
    unfold Workspace.Types.L1Distance.L1Distance
    rw [Finset.sum_congr rfl (fun i _ => key_id i)]
    -- ∑ i : Fin n, c' * √n * (C(n, i.val) * 2^(-n))
    have factor : ∀ i : Fin n,
        c' * Real.sqrt n * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
        = c' * Real.sqrt n * (2 ^ n : ℝ)⁻¹ * (Nat.choose n i.val : ℝ) := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => factor i)]
    rw [← Finset.mul_sum]
    -- Now: ∑ i : Fin n, (Nat.choose n i.val : ℝ) = 2^n - 1
    have sum_choose_fin : ∑ i : Fin n, (Nat.choose n i.val : ℝ) = (2 : ℝ) ^ n - 1 := by
      have h1 : ∑ i : Fin n, (Nat.choose n i.val : ℝ)
          = ∑ i ∈ Finset.range n, (Nat.choose n i : ℝ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun k => (Nat.choose n k : ℝ)) n]
      rw [h1]
      have hsum : ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) = (2 : ℝ) ^ n := by
        have := Nat.sum_range_choose n
        have := congrArg (fun k : ℕ => (k : ℝ)) this
        push_cast at this
        exact this
      rw [Finset.sum_range_succ] at hsum
      rw [Nat.choose_self] at hsum
      push_cast at hsum
      linarith
    rw [sum_choose_fin]
  -- Now prove the bracket
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have h2pow_inv_pos : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have h2pow_inv_le_half : ((2 : ℝ) ^ n)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_iff_one_le_mul₀ h2pos]
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ n := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    rw [pow_one] at this
    linarith
  have h2pow_ge_2 : (2 : ℝ) ≤ (2 : ℝ) ^ n := by
    have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ n := by
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
    rwa [pow_one] at this
  -- Rewrite L1 = c' * √n * (1 - 2^(-n))
  have l1_eq2 : Workspace.Types.L1Distance.L1Distance Se So
      = c' * Real.sqrt n * (1 - ((2 : ℝ) ^ n)⁻¹) := by
    rw [l1_eq]
    field_simp
  refine ⟨?_, ?_⟩
  · -- Lower bound: c'/2 · √n ≤ c' · √n · (1 - 2^(-n))
    show (1 / (8 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
        ≤ Workspace.Types.L1Distance.L1Distance Se So
    rw [l1_eq2]
    -- LHS = c'/2 · √n
    have lhs_eq : (1 / (8 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
        = (c' / 2) * Real.sqrt n := by
      rw [hc'_def]; field_simp; ring
    rw [lhs_eq]
    -- Need: c'/2 · √n ≤ c' · √n · (1 - 2^(-n))
    have h1m : (1 : ℝ) / 2 ≤ 1 - ((2 : ℝ) ^ n)⁻¹ := by linarith
    have h1m_nn : (0 : ℝ) ≤ 1 - ((2 : ℝ) ^ n)⁻¹ := by linarith
    have hcsn : 0 ≤ c' * Real.sqrt n := mul_nonneg hc'_pos.le hsqrtn_nn
    have : c' * Real.sqrt n * (1 / 2) ≤ c' * Real.sqrt n * (1 - ((2 : ℝ) ^ n)⁻¹) :=
      mul_le_mul_of_nonneg_left h1m hcsn
    have eq1 : (c' / 2) * Real.sqrt n = c' * Real.sqrt n * (1 / 2) := by ring
    linarith [this, eq1]
  · -- Upper bound: c' · √n · (1 - 2^(-n)) ≤ 2c' · √n
    show Workspace.Types.L1Distance.L1Distance Se So
        ≤ (1 / (2 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
    rw [l1_eq2]
    have rhs_eq : (1 / (2 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
        = (2 * c') * Real.sqrt n := by
      rw [hc'_def]; field_simp; ring
    rw [rhs_eq]
    -- Need: c' · √n · (1 - 2^(-n)) ≤ 2c' · √n
    have h1m_le : 1 - ((2 : ℝ) ^ n)⁻¹ ≤ 2 := by
      have : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := h2pow_inv_pos.le
      linarith
    have hcsn : 0 ≤ c' * Real.sqrt n := mul_nonneg hc'_pos.le hsqrtn_nn
    have step1 : c' * Real.sqrt n * (1 - ((2 : ℝ) ^ n)⁻¹) ≤ c' * Real.sqrt n * 2 :=
      mul_le_mul_of_nonneg_left h1m_le hcsn
    have eq2 : c' * Real.sqrt n * 2 = 2 * c' * Real.sqrt n := by ring
    linarith [step1, eq2]
