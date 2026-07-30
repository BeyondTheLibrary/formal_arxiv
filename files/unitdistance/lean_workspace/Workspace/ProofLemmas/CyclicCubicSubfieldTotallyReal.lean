-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Chapter 3, especially Theorem 3.11; J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VI.
-- Paper label: Proposition A.11(i)
-- NL statement: For a rational prime r congruent to 1 mod 3, the unique cyclic cubic subfield of Q(zeta_r) is totally real.
--   Proof idea: reduce `IsTotallyReal` of the lifted subfield to membership of the fixed field
--   `E = fixedField H` inside `maximalRealSubfield (ℚ(ζ_r))`. Since ℚ(ζ_r)/ℚ is Galois, every
--   complex embedding φ factors as `ι ∘ σ` (`Normal.algHomEquivAut`). Complex conjugation gives an
--   automorphism `c` with `c ∘ c = 1`; hence `galToUnits c` is its own cube (`g² = 1 ⇒ g³ = g`), so
--   `c ∈ H` (the cubes subgroup). The Galois group is abelian (`galToUnits` is a `MulEquiv` onto the
--   commutative group `(ZMod r)ˣ`), so `σ x ∈ E` whenever `x ∈ E`, and `c` fixes it — giving
--   `star (φ x) = φ x` for every embedding `φ`.
import Mathlib
import Workspace.Types.CyclotomicCharacterFields

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 800000

theorem CyclicCubicSubfieldTotallyReal (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    [NumberField ↥(cyclicCubicSubfield r hr hr3)] :
    NumberField.IsTotallyReal ↥(cyclicCubicSubfield r hr hr3) := by
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    ((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom with hH
  have hlift : cyclicCubicSubfield r hr hr3
      = IntermediateField.lift (IntermediateField.fixedField H) := rfl
  rw [hlift]
  rw [← NumberField.isTotallyReal_iff_ofRingEquiv
        (IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)).toRingEquiv]
  refine (NumberField.isTotallyReal_iff_le_maximalRealSubfield
            (E := (IntermediateField.fixedField H).toSubfield)).mpr ?_
  set ι : cyclotomicField' r →+* ℂ := algebraMap (cyclotomicField' r) ℂ with hι
  have hιinj : Function.Injective ι := (algebraMap (cyclotomicField' r) ℂ).injective
  set eqv := Normal.algHomEquivAut ℚ ℂ (E := cyclotomicField' r) with heqv
  -- Every complex embedding factors through the Galois group: `g y = ι (eqv g y)`.
  have key : ∀ (g : cyclotomicField' r →ₐ[ℚ] ℂ) (y : cyclotomicField' r),
      g y = ι ((eqv g) y) := by
    intro g y
    have h1 : g = eqv.symm (eqv g) := (Equiv.symm_apply_apply _ g).symm
    conv_lhs => rw [h1]
    rw [heqv, Normal.algHomEquivAut_symm_apply]
    rfl
  -- The Galois group is abelian (it is `MulEquiv` to `(ZMod r)ˣ`).
  have hcomm : ∀ a b : cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r, a * b = b * a := by
    intro a b
    apply (galToUnits r).injective
    rw [map_mul, map_mul, mul_comm]
  intro x hx φ
  set φA : cyclotomicField' r →ₐ[ℚ] ℂ := φ.toRatAlgHom with hφA
  set ψR : cyclotomicField' r →+* ℂ := (starRingEnd ℂ).comp ι with hψR
  set ψA : cyclotomicField' r →ₐ[ℚ] ℂ := ψR.toRatAlgHom with hψA
  set σ := eqv φA with hσ
  set c := eqv ψA with hc
  -- Complex conjugation of the ambient field, transported to the automorphism `c`.
  have hcrel : ∀ y, ι (c y) = starRingEnd ℂ (ι y) := by
    intro y
    have hk := (key ψA y).symm
    rw [hc, hk, hψA, RingHom.toRatAlgHom_apply, hψR]
    rfl
  -- `c` is an involution.
  have hcinv : c * c = 1 := by
    apply AlgEquiv.ext
    intro y
    apply hιinj
    show ι ((c * c) y) = ι y
    rw [AlgEquiv.mul_apply, hcrel, hcrel, Complex.conj_conj]
  -- Since `galToUnits c` squares to `1`, it equals its own cube, so `c ∈ H`.
  have hcH : c ∈ H := by
    rw [hH]
    show (galToUnits r).toMonoidHom c
        ∈ (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range
    have hsq : (galToUnits r c) ^ 2 = 1 := by
      have h2 : galToUnits r (c * c) = (galToUnits r c) ^ 2 := by rw [map_mul, sq]
      rw [hcinv, map_one] at h2
      exact h2.symm
    refine ⟨galToUnits r c, ?_⟩
    show (galToUnits r c) ^ 3 = galToUnits r c
    rw [pow_succ, hsq, one_mul]
  -- `σ x` lies in the fixed field (abelian group ⇒ the fixed field is `σ`-stable).
  have hσx : σ x ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    intro h hhH
    have hhx : h x = x := (IntermediateField.mem_fixedField_iff H x).mp hx h hhH
    calc h (σ x) = (h * σ) x := (AlgEquiv.mul_apply h σ x).symm
      _ = (σ * h) x := by rw [hcomm]
      _ = σ (h x) := AlgEquiv.mul_apply σ h x
      _ = σ x := by rw [hhx]
  -- Therefore `c` fixes `σ x`.
  have hcfix : c (σ x) = σ x :=
    (IntermediateField.mem_fixedField_iff H (σ x)).mp hσx c hcH
  show star (φ x) = φ x
  have hφx : φ x = ι (σ x) := by
    have hxeq : φ x = φA x := (RingHom.toRatAlgHom_apply φ x).symm
    rw [hxeq, hσ]; exact key φA x
  rw [hφx, Complex.star_def, ← hcrel (σ x), hcfix]
