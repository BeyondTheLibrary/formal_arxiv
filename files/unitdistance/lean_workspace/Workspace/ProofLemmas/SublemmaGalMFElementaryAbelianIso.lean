import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.Prop32CyclotomicBase

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

/-- Classification: a finite group `G` that is commutative and has exponent dividing `3`,
with `Nat.card G = 3 ^ n`, is isomorphic to `(Fin n → Multiplicative (ZMod 3))`.
This is fully proved (no `sorry`). -/
private theorem classify {G : Type*} [Group G] [Finite G] (n : ℕ)
    (hcomm : ∀ a b : G, a * b = b * a) (hexp : ∀ a : G, a ^ 3 = 1)
    (hcard : Nat.card G = 3 ^ n) :
    Nonempty (G ≃* (Fin n → Multiplicative (ZMod 3))) := by
  letI : CommGroup G := { mul_comm := hcomm }
  have h3 : ∀ x : Additive G, (3 : ℕ) • x = 0 := by
    intro x
    have hx : (Additive.toMul x) ^ 3 = 1 := hexp _
    have := congrArg Additive.ofMul hx
    simpa [ofMul_pow] using this
  letI : Module (ZMod 3) (Additive G) := AddCommGroup.zmodModule h3
  haveI : Finite (Additive G) := inferInstanceAs (Finite G)
  haveI : Module.Finite (ZMod 3) (Additive G) := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod 3) (Additive G) := inferInstance
  haveI : Fintype (Additive G) := Fintype.ofFinite _
  have hpow : Fintype.card (Additive G)
      = (Fintype.card (ZMod 3)) ^ Module.finrank (ZMod 3) (Additive G) :=
    Module.card_eq_pow_finrank
  have hcardA : Fintype.card (Additive G) = 3 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hfr : Module.finrank (ZMod 3) (Additive G) = n := by
    have h33 : Fintype.card (ZMod 3) = 3 := by simp [ZMod.card]
    rw [h33, hcardA] at hpow
    exact Nat.pow_right_injective (by norm_num) hpow.symm
  let b := Module.finBasis (ZMod 3) (Additive G)
  let e : Additive G ≃ₗ[ZMod 3] (Fin (Module.finrank (ZMod 3) (Additive G)) → ZMod 3) :=
    b.equivFun
  let e2 : Additive G ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
    e.trans (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (finCongr hfr).symm)
  have eadd : Additive G ≃+ (Fin n → ZMod 3) := e2.toAddEquiv
  have emul : Multiplicative (Additive G) ≃* Multiplicative (Fin n → ZMod 3) :=
    AddEquiv.toMultiplicative eadd
  refine ⟨?_⟩
  refine (MulEquiv.multiplicativeAdditive G).symm.trans (emul.trans ?_)
  exact MulEquiv.funMultiplicative _ _

/-- **Prop 3.8, Step 1 — `Gal(M/F) ≅ (ℤ/3)^{ℓ-1}`.** -/
theorem SublemmaGalMFElementaryAbelianIso (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) [NumberField ↥M]
    (F : IntermediateField ℚ ℂ) (hFM : F ≤ M) [NumberField ↥F]
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hFcut : F = cutOutField D chi)
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3))) := by
  -- Relative degree [M:F] = 3^{ℓ-1}.
  have hdeg := Prop32CyclotomicBase_relative_degree ℓ (by omega) r hp hm hdist M hM F hFM D hD
    chi hchi_ord hFcut
  -- Gal(M/ℚ) elementary abelian: commutative and every element cubes to 1.
  have hea := Prop32CyclotomicBase_galois_elementary_abelian ℓ (by omega) r hp hm hdist M hM
  haveI hfin : FiniteDimensional ↥F ↥M := FiniteDimensional.right ℚ ↥F ↥M
  -- `Gal(M/F)` embeds into `Gal(M/ℚ)` via restriction of scalars; the embedding is
  -- multiplicative, so it transports commutativity and exponent 3 from `Gal(M/ℚ)`.
  have hcomm : ∀ σ τ : (↥M ≃ₐ[↥F] ↥M), σ * τ = τ * σ := by
    intro σ τ
    apply AlgEquiv.restrictScalars_injective ℚ
    have hmul : ∀ a b : (↥M ≃ₐ[↥F] ↥M),
        AlgEquiv.restrictScalars ℚ (a * b)
          = AlgEquiv.restrictScalars ℚ a * AlgEquiv.restrictScalars ℚ b := by
      intro a b; rfl
    rw [hmul, hmul]
    exact hea.1 _ _
  have hexp : ∀ σ : (↥M ≃ₐ[↥F] ↥M), σ ^ 3 = 1 := by
    intro σ
    apply AlgEquiv.restrictScalars_injective ℚ
    have hpw : AlgEquiv.restrictScalars ℚ (σ ^ 3)
        = (AlgEquiv.restrictScalars ℚ σ) ^ 3 := by rfl
    have hone : AlgEquiv.restrictScalars ℚ (1 : ↥M ≃ₐ[↥F] ↥M) = 1 := rfl
    rw [hpw, hone]
    exact hea.2 _
  -- The cardinality of the automorphism group equals the degree, PROVIDED M/F is Galois.
  -- `M/F` is Galois because `M/ℚ` is Galois (a compositum of the Galois cyclic cubic
  -- subfields `cyclicCubicSubfield (r i)`) and `F` is intermediate, so `IsGalois ℚ M`
  -- transfers to `IsGalois F M` via `tower_top`.
  haveI hGal : IsGalois ↥F ↥M := by
    -- Each `cyclicCubicSubfield (r i)` is Galois over `ℚ`: it is the fixed field of a
    -- normal subgroup (the comap of a subgroup of the *abelian* group `(ℤ/rℤ)ˣ`) of the
    -- Galois group of the cyclotomic field `ℚ(ζ_{r i})`.
    have hnormal : ∀ i, Normal ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := by
      intro i
      set H := (((powMonoidHom 3 : (ZMod (r i : ℕ))ˣ →* (ZMod (r i : ℕ))ˣ).range).comap
        (galToUnits (r i)).toMonoidHom) with hH
      haveI hg : IsGalois ℚ ↥(IntermediateField.fixedField H) :=
        IsGalois.of_fixedField_normal_subgroup _
      have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ]
          ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
        IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)
      exact (IsGalois.of_algEquiv e).to_normal
    haveI hnormal' : ∀ i, Normal ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := hnormal
    have hnorm : Normal ℚ ↥M := by
      rw [hM]
      exact IntermediateField.normal_iSup ℚ ℂ
        (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) (h := hnormal')
    haveI : Normal ℚ ↥M := hnorm
    haveI hGalQM : IsGalois ℚ ↥M := isGalois_iff.mpr ⟨inferInstance, hnorm⟩
    exact IsGalois.tower_top_of_isGalois ℚ ↥F ↥M
  have hcard : Nat.card (↥M ≃ₐ[↥F] ↥M) = 3 ^ (ℓ - 1) := by
    rw [IsGalois.card_aut_eq_finrank ↥F ↥M, hdeg]
  exact classify (ℓ - 1) hcomm hexp hcard
