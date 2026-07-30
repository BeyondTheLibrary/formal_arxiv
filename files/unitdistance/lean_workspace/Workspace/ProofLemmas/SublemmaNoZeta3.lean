import Mathlib

open NumberField

theorem SublemmaNoZeta3 (F : IntermediateField ℚ ℂ) [NumberField ↥F]
    (hF : NumberField.IsTotallyReal ↥F) :
    ¬ ∃ x : ↥F, IsPrimitiveRoot x 3 := by
  rintro ⟨x, hx⟩
  -- The natural embedding of F into ℂ.
  set φ : ↥F →+* ℂ := algebraMap ↥F ℂ with hφ
  have hinj : Function.Injective φ := φ.injective
  -- φ x is a primitive cube root of unity in ℂ.
  have hxc : IsPrimitiveRoot (φ x) 3 := hx.map_of_injective hinj
  -- φ is a real embedding, so φ x is real.
  have hreal : NumberField.ComplexEmbedding.IsReal φ := hF.complexEmbedding_isReal φ
  have hconj : (starRingEnd ℂ) (φ x) = φ x := by
    have := NumberField.ComplexEmbedding.isReal_iff.mp hreal
    exact RingHom.congr_fun this x
  have him : (φ x).im = 0 := by
    have := Complex.conj_eq_iff_im.mp hconj
    exact this
  -- Let r be the real part; φ x = r.
  set r : ℝ := (φ x).re with hr
  have hxr : φ x = (r : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simp [him]
  -- (φ x) ^ 3 = 1
  have hpow : (φ x) ^ 3 = 1 := hxc.pow_eq_one
  rw [hxr] at hpow
  have hr3 : r ^ 3 = 1 := by
    have : ((r ^ 3 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination hpow
    exact_mod_cast this
  -- φ x ≠ 1
  have hne : φ x ≠ 1 := hxc.ne_one (by norm_num)
  rw [hxr] at hne
  have hrne : r ≠ 1 := by
    intro h; apply hne; rw [h]; norm_num
  -- Derive contradiction.
  have hfac : (r - 1) * (r ^ 2 + r + 1) = 0 := by linear_combination hr3
  have hquad : r ^ 2 + r + 1 = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith : r = 1) hrne
    · exact h
  nlinarith [sq_nonneg (2 * r + 1), hquad]
