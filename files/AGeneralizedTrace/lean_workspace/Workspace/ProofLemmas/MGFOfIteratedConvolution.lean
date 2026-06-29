import Mathlib
import Workspace.PriorWork.MGFOfConvolution

set_option maxHeartbeats 4000000

/--
**MGF of iterated convolution.**

For `H : ℝ → ℝ` non-negative integrable with support contained in `[-R, R]` for some
`R > 0`, and `Hconv : ℕ → ℝ → ℝ` the iterated linear self-convolution of `H`
(`Hconv 1 = H`, `Hconv (b+1) η = ∫ y, Hconv b y * H (η - y)`), the MGF of the
`(b+1)`-fold self-convolution factors as the `(b+1)`-th power of the MGF of `H`:

  `∫ exp(t·η) · Hconv (b+1) η = (∫ exp(t·η) · H η) ^ (b+1)`

for every `b : ℕ` and `t : ℝ`.

The support hypothesis is provided per-`b` via `hHconv_supp`, since each
convolution of compactly supported functions has support contained in the
Minkowski sum of the underlying supports (so `Hconv b` is supported in
`[-b·R, b·R]`).
-/
theorem MGFOfIteratedConvolution
    (H : ℝ → ℝ) (hH_nn : ∀ x, 0 ≤ H x) (hH_int : MeasureTheory.Integrable H)
    (R : ℝ) (hR_pos : 0 < R) (hH_supp : ∀ x, |x| > R → H x = 0)
    (Hconv : ℕ → ℝ → ℝ)
    (hHconv1 : Hconv 1 = H)
    (hHconv_rec : ∀ b : ℕ, 1 ≤ b → ∀ η : ℝ,
        Hconv (b + 1) η = ∫ y, Hconv b y * H (η - y))
    (hHconv_nn : ∀ b : ℕ, 1 ≤ b → ∀ η, 0 ≤ Hconv b η)
    (hHconv_int : ∀ b : ℕ, 1 ≤ b → MeasureTheory.Integrable (Hconv b))
    (hHconv_supp : ∀ b : ℕ, 1 ≤ b → ∀ x, |x| > (b : ℝ) * R → Hconv b x = 0)
    (t : ℝ) :
    ∀ b : ℕ,
      (∫ η, Real.exp (t * η) * Hconv (b + 1) η) =
        (∫ ξ, Real.exp (t * ξ) * H ξ) ^ (b + 1) := by
  intro b
  induction b with
  | zero =>
    -- ∫ exp(t·η) * Hconv 1 η = ∫ exp(t·η) * H η = (∫ exp(t·ξ) * H ξ)^1
    simp only [zero_add, pow_one, hHconv1]
  | succ b ih =>
    -- Hconv (b + 2) η = ∫ y, Hconv (b+1) y * H(η - y).
    -- By MGFOfConvolution applied to f = Hconv (b+1), g = H with R' = (b+2)·R:
    --   ∫ exp(t·η) * (∫ y, Hconv(b+1) y * H(η-y)) = (∫ exp(t·η) * Hconv(b+1)) * (∫ exp(t·η) * H)
    -- Use ih to rewrite the first factor, then collapse to (b+2)-th power.
    have hb1 : (1 : ℕ) ≤ b + 1 := Nat.succ_le_succ (Nat.zero_le _)
    -- Rewrite LHS using the recurrence at index (b+1) → (b+2).
    have h_rec_b1 : ∀ η : ℝ, Hconv (b + 1 + 1) η = ∫ y, Hconv (b + 1) y * H (η - y) :=
      hHconv_rec (b + 1) hb1
    -- ∫ exp(t·η) * Hconv (b+2) η = ∫ exp(t·η) * (∫ y, Hconv (b+1) y * H (η - y))
    have h_eq1 :
        (∫ η, Real.exp (t * η) * Hconv (b + 1 + 1) η)
          = ∫ η, Real.exp (t * η) * (∫ y, Hconv (b + 1) y * H (η - y)) := by
      apply MeasureTheory.integral_congr_ae
      refine Filter.Eventually.of_forall (fun η => ?_)
      simp only
      rw [h_rec_b1 η]
    -- Apply MGFOfConvolution with R' := (b + 1 + 1) * R.
    -- Both Hconv(b+1) (supported in [-(b+1)·R,(b+1)·R]) and H (supported in [-R, R])
    -- vanish outside [-(b+2)·R, (b+2)·R].
    set R' : ℝ := ((b : ℝ) + 1 + 1) * R with hR'_def
    have hR'_pos : 0 < R' := by
      apply mul_pos _ hR_pos
      have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
      linarith
    have hf_supp : ∀ x, |x| > R' → Hconv (b + 1) x = 0 := by
      intro x hx
      apply hHconv_supp (b + 1) hb1 x
      -- Need: |x| > (b+1) * R. We have |x| > (b+1+1) * R ≥ (b+1) * R (since R > 0).
      have h_le : ((b : ℝ) + 1) * R ≤ ((b : ℝ) + 1 + 1) * R := by
        have hR_nn : 0 ≤ R := le_of_lt hR_pos
        nlinarith
      have h_cast : ((b + 1 : ℕ) : ℝ) * R = ((b : ℝ) + 1) * R := by push_cast; ring
      rw [h_cast]
      linarith
    have hg_supp : ∀ x, |x| > R' → H x = 0 := by
      intro x hx
      apply hH_supp x
      have h_R_le : R ≤ ((b : ℝ) + 1 + 1) * R := by
        have h_one_le : (1 : ℝ) ≤ ((b : ℝ) + 1 + 1) := by
          have : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg _
          linarith
        nlinarith [hR_pos]
      linarith
    have h_factor :=
      MGFOfConvolution (Hconv (b + 1)) H
        (hHconv_nn (b + 1) hb1) hH_nn
        (hHconv_int (b + 1) hb1) hH_int
        ⟨R', hR'_pos, hf_supp, hg_supp⟩ t
    -- h_factor : ∫ η, exp(t·η) * (∫ y, Hconv(b+1) y * H(η-y))
    --             = (∫ η, exp(t·η) * Hconv(b+1) η) * (∫ η, exp(t·η) * H η)
    rw [h_eq1, h_factor, ih]
    -- Now: (∫ ξ, exp(t·ξ) * H ξ) ^ (b+1) * (∫ η, exp(t·η) * H η) = (∫ ξ, exp(t·ξ) * H ξ) ^ (b+2)
    ring
