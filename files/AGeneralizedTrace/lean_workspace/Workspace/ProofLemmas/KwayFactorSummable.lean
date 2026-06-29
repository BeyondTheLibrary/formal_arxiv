import Mathlib

open scoped Real Complex

set_option maxHeartbeats 4000000

namespace KwayFactorSummable

/-- Generic building block: a real-valued function on `ℤ` that vanishes outside a
finite interval `Finset.Icc lo hi` is summable in absolute value (and summable). -/
theorem summable_of_off_Icc_zero (lo hi : ℤ) (fac : ℤ → ℝ)
    (h : ∀ r : ℤ, r ∉ Finset.Icc lo hi → fac r = 0) :
    Summable (fun r : ℤ => ‖fac r‖) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc lo hi)
  intro b hb
  rw [h b hb, norm_zero]

/-- The same building block, concluding plain summability. -/
theorem summable_of_off_Icc_zero' (lo hi : ℤ) (fac : ℤ → ℝ)
    (h : ∀ r : ℤ, r ∉ Finset.Icc lo hi → fac r = 0) :
    Summable fac := by
  apply summable_of_ne_finset_zero (s := Finset.Icc lo hi)
  intro b hb
  exact h b hb

/-- The concrete per-factor function (j-th factor of the k-way product), as a
function of `r : ℤ`, for fixed `n`, shift index value `ℓj : ℕ`. This is exactly
the body of the product in `SublemmaFourierKway`, specialized to one index. -/
noncomputable def factor (n : ℕ) (ℓj : ℕ) (r : ℤ) : ℝ :=
  let m : ℤ := r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)
  if 0 ≤ m ∧ m ≤ (n : ℤ) then
    let i : ℕ := m.toNat
    let α : ℝ :=
      (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
    let p : ℝ := α * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
    p / (1 - p)
  else 0

/-- The j-th factor vanishes off the finite interval determined by its support
condition `0 ≤ r + c ∧ r + c ≤ n`, where `c := (n-1)/4 + ℓj`. -/
theorem factor_off_Icc_zero (n : ℕ) (ℓj : ℕ) :
    ∀ r : ℤ,
      r ∉ Finset.Icc (-(((n : ℤ) - 1) / 4 + (ℓj : ℤ)))
                     ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓj : ℤ))) →
      factor n ℓj r = 0 := by
  intro r hr
  rw [Finset.mem_Icc, not_and_or] at hr
  unfold factor
  simp only
  rw [if_neg]
  rintro ⟨h1, h2⟩
  -- m = r + (n-1)/4 + ℓj, with 0 ≤ m ≤ n.  So r ∈ [-(c), n - c].
  rcases hr with hlo | hhi
  · omega
  · omega

/-- The j-th factor is summable in absolute value (ℝ version). -/
theorem factor_summable (n : ℕ) (ℓj : ℕ) :
    Summable (fun r : ℤ => ‖factor n ℓj r‖) :=
  summable_of_off_Icc_zero _ _ _ (factor_off_Icc_zero n ℓj)

/-- The ℂ-cast version: the caller uses `f j : ℤ → ℂ := fun r => ((factor j r : ℝ) : ℂ)`. -/
theorem factor_summable_complex (n : ℕ) (ℓj : ℕ) :
    Summable (fun r : ℤ => ‖((factor n ℓj r : ℝ) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖((factor n ℓj r : ℝ) : ℂ)‖) = (fun r : ℤ => ‖factor n ℓj r‖) := by
    funext r
    rw [Complex.norm_real]
  rw [h]
  exact factor_summable n ℓj

/-! ### Generic product-of-factors summability -/

/-- Generic building block for any normed (commutative) field: a function `g : ℤ → 𝕜`
that vanishes off `Finset.Icc lo hi` is summable in absolute value. -/
theorem summable_norm_of_off_Icc_zero {𝕜 : Type*} [NormedField 𝕜]
    (lo hi : ℤ) (g : ℤ → 𝕜)
    (h : ∀ r : ℤ, r ∉ Finset.Icc lo hi → g r = 0) :
    Summable (fun r : ℤ => ‖g r‖) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc lo hi)
  intro b hb
  rw [h b hb, norm_zero]

/-- A product `∏ j ∈ s, fac j r` over a NONEMPTY finset `s`, where ONE distinguished
factor `fac j₀` (`j₀ ∈ s`) vanishes off a finite interval `Finset.Icc lo hi`,
itself vanishes off that same interval (because the whole product is zero whenever
one factor is). Hence it is summable in absolute value. Works over any normed
commutative field (in particular `ℝ` and `ℂ`). -/
theorem prod_summable_of_one_factor_off_Icc_zero
    {𝕜 : Type*} [NormedField 𝕜]
    {ι : Type*} (s : Finset ι) (fac : ι → ℤ → 𝕜) (j₀ : ι) (hj₀ : j₀ ∈ s)
    (lo hi : ℤ)
    (h : ∀ r : ℤ, r ∉ Finset.Icc lo hi → fac j₀ r = 0) :
    Summable (fun r : ℤ => ‖∏ j ∈ s, fac j r‖) := by
  apply summable_norm_of_off_Icc_zero lo hi
  intro r hr
  apply Finset.prod_eq_zero hj₀
  exact h r hr

/-! ### Concrete partial-product summability (regime `m ≥ 1`) -/

/-- The complex-valued j-th factor used by the caller: `fcx n ℓ j r = ((factor n (ℓ j) r : ℝ) : ℂ)`
for `j` in range, and `0` for `j` out of range. This makes every factor and every
partial product over `Finset.range m` (for `m ≥ 1`) have finite support. -/
noncomputable def fcx (n k : ℕ) (ℓ : Fin k → ℕ) (j : ℕ) (r : ℤ) : ℂ :=
  if h : j < k then ((factor n (ℓ ⟨j, h⟩) r : ℝ) : ℂ) else 0

/-- Each complex factor `fcx n k ℓ j` is summable in absolute value (all `j : ℕ`). -/
theorem fcx_summable (n k : ℕ) (ℓ : Fin k → ℕ) (j : ℕ) :
    Summable (fun r : ℤ => ‖fcx n k ℓ j r‖) := by
  by_cases hj : j < k
  · have h : (fun r : ℤ => ‖fcx n k ℓ j r‖)
        = (fun r : ℤ => ‖((factor n (ℓ ⟨j, hj⟩) r : ℝ) : ℂ)‖) := by
      funext r
      simp only [fcx, dif_pos hj]
    rw [h]
    exact factor_summable_complex n (ℓ ⟨j, hj⟩)
  · have h : (fun r : ℤ => ‖fcx n k ℓ j r‖) = (fun _ : ℤ => (0 : ℝ)) := by
      funext r
      simp only [fcx, dif_neg hj, norm_zero]
    rw [h]
    exact summable_zero

/-- The partial product of the complex factors over `Finset.range m`, evaluated at `r`. -/
noncomputable def partialProdCx (n k : ℕ) (ℓ : Fin k → ℕ) (m : ℕ) (r : ℤ) : ℂ :=
  ∏ j ∈ Finset.range m, fcx n k ℓ j r

/-- For `m ≥ 1` the partial product over `range m` vanishes off the support interval
of its first factor (`j = 0`), hence is summable in absolute value. (For `m = 0`
the product is the constant `1`, which is NOT summable — excluded by `1 ≤ m`.) -/
theorem partialProdCx_summable (n k : ℕ) (ℓ : Fin k → ℕ) (m : ℕ) (hm : 1 ≤ m) :
    Summable (fun r : ℤ => ‖partialProdCx n k ℓ m r‖) := by
  unfold partialProdCx
  -- The factor `fcx … 0` vanishes off a finite interval.
  -- Case on whether index 0 is in range of `Fin k`.
  by_cases hk : 0 < k
  · -- `fcx n k ℓ 0 r = ((factor n (ℓ 0) r : ℝ) : ℂ)`, which vanishes off an Icc.
    refine prod_summable_of_one_factor_off_Icc_zero (Finset.range m) (fcx n k ℓ) 0
      (Finset.mem_range.mpr hm)
      (-(((n : ℤ) - 1) / 4 + (ℓ ⟨0, hk⟩ : ℤ)))
      ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓ ⟨0, hk⟩ : ℤ))) ?_
    intro r hr
    simp only [fcx, dif_pos hk]
    rw [factor_off_Icc_zero n (ℓ ⟨0, hk⟩) r hr]
    simp
  · -- `k = 0`, so `fcx n k ℓ 0 r = 0` for all `r`; the whole product is `0`.
    have hfac0 : ∀ r : ℤ, fcx n k ℓ 0 r = 0 := by
      intro r
      simp only [fcx, dif_neg (by omega : ¬ (0 < k))]
    -- Product over range m (m ≥ 1) contains the j=0 factor, which is 0.
    refine prod_summable_of_one_factor_off_Icc_zero (Finset.range m) (fcx n k ℓ) 0
      (Finset.mem_range.mpr hm) 0 0 ?_
    intro r _
    exact hfac0 r

/-! ### The full k-way product `T4` (over `Fin k`, `k ≥ 1`) -/

/-- For `k ≥ 1`, the full k-way product `r ↦ ∏ j : Fin k, factor n (ℓ j) r` (the ℝ-valued
`T4`) vanishes off the support interval of its `j = 0` factor, hence is summable in
absolute value. -/
theorem T4_summable (n k : ℕ) (ℓ : Fin k → ℕ) (hk : 0 < k) :
    Summable (fun r : ℤ => ‖∏ j : Fin k, factor n (ℓ j) r‖) := by
  refine prod_summable_of_one_factor_off_Icc_zero Finset.univ (fun j => factor n (ℓ j))
    ⟨0, hk⟩ (Finset.mem_univ _)
    (-(((n : ℤ) - 1) / 4 + (ℓ ⟨0, hk⟩ : ℤ)))
    ((n : ℤ) - (((n : ℤ) - 1) / 4 + (ℓ ⟨0, hk⟩ : ℤ))) ?_
  intro r hr
  exact factor_off_Icc_zero n (ℓ ⟨0, hk⟩) r hr

/-- ℂ-cast version of `T4_summable`: `r ↦ ‖((∏ j : Fin k, factor n (ℓ j) r : ℝ) : ℂ)‖`
is summable for `k ≥ 1`. -/
theorem T4_summable_complex (n k : ℕ) (ℓ : Fin k → ℕ) (hk : 0 < k) :
    Summable (fun r : ℤ => ‖(((∏ j : Fin k, factor n (ℓ j) r : ℝ)) : ℂ)‖) := by
  have h : (fun r : ℤ => ‖(((∏ j : Fin k, factor n (ℓ j) r : ℝ)) : ℂ)‖)
      = (fun r : ℤ => ‖∏ j : Fin k, factor n (ℓ j) r‖) := by
    funext r
    rw [Complex.norm_real]
  rw [h]
  exact T4_summable n k ℓ hk

end KwayFactorSummable
