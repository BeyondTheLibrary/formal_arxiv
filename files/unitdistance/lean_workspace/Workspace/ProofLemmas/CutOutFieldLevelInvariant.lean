-- Cited from: Def A.5 (field conductor / level-independence of the cut-out field), Washington, Introduction to Cyclotomic Fields, Ch. 3.
-- The field cut out by a Dirichlet character depends only on the character up to changeLevel (i.e. on the induced primitive character), not on the chosen modulus.
--
-- The classical content is Mathlib's cyclotomic Galois correspondence: the level-compatibility square
-- `IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply`, the fixed-field descent
-- `InfiniteGalois.restrict_fixedField` (packaged as the helper `fixedFieldDescent`, also proved from
-- Mathlib), and `DirichletCharacter.changeLevel_toUnitHom`.  The ℚ-algebra instance diamond on the
-- subfield-of-a-subfield `ℚ(ζ_r) ⊆ ℚ(ζ_D) ⊆ ℂ` (Mathlib uses `IntermediateField.algebra'` while the
-- cyclotomic setup forces `DivisionRing.toRatAlgebra`) is bridged via `Subsingleton (Algebra ℚ _)`.
import Mathlib
import Workspace.Types.CyclotomicCharacterFields

open Complex
open Workspace.Types.CyclotomicCharacterFields
open IsCyclotomicExtension IsCyclotomicExtension.Rat

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Workspace.ProofLemmas.CutOutFieldLevelInvariantProof

/-- `zetaC a` is a power of `zetaC b` whenever `a ∣ b`. -/
theorem zetaC_pow_of_dvd (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    zetaC a = zetaC b ^ ((b : ℕ) / (a : ℕ)) := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  congr 1
  obtain ⟨k, hk⟩ := h
  have hr0 : (a : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hm0 : (b : ℂ) ≠ 0 := by exact_mod_cast b.pos.ne'
  have hkdiv : (b : ℕ) / (a : ℕ) = k := by rw [hk]; exact Nat.mul_div_cancel_left k a.pos
  rw [hkdiv]
  have hkc : (b : ℂ) = (a : ℂ) * (k : ℂ) := by exact_mod_cast hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hk
    exact_mod_cast this
  rw [hkc]
  field_simp

/-- Monotonicity of the concrete cyclotomic fields with respect to divisibility. -/
theorem cyclotomicField'_mono (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    cyclotomicField' a ≤ cyclotomicField' b := by
  unfold cyclotomicField'
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [zetaC_pow_of_dvd a b h]
  exact pow_mem (IntermediateField.subset_adjoin ℚ {zetaC b} rfl) _

/-- Restricting a subfield `S ≤ ℚ(ζ_N)` to `ℚ(ζ_N)` and lifting back recovers `S`. -/
theorem comap_val_roundtrip_gen (S : IntermediateField ℚ ℂ) (N : ℕ+)
    (hSN : S ≤ cyclotomicField' N) :
    IntermediateField.lift (S.comap (cyclotomicField' N).val) = S := by
  show (S.comap (cyclotomicField' N).val).map (cyclotomicField' N).val = S
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left]
  exact hSN

/-- The `ℚ`-algebra isomorphism `ℚ(ζ_a) ⊆ ℚ(ζ_N)  ≃  ℚ(ζ_a)` when `a ∣ N`. -/
noncomputable def comapValEquiv (a N : ℕ+) (haN : (a : ℕ) ∣ (N : ℕ)) :
    ↥((cyclotomicField' a).comap (cyclotomicField' N).val) ≃ₐ[ℚ] ↥(cyclotomicField' a) :=
  (IntermediateField.liftAlgEquiv _).trans
    (IntermediateField.equivOfEq
      (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN)))

/-- The underlying complex number of `comapValEquiv a N haN x` is that of `x`. -/
theorem comapValEquiv_coe (a N : ℕ+) (haN : (a : ℕ) ∣ (N : ℕ))
    (x : ↥((cyclotomicField' a).comap (cyclotomicField' N).val)) :
    ((comapValEquiv a N haN x : ↥(cyclotomicField' a)) : ℂ) = (x : ℂ) := by
  have h1 : (comapValEquiv a N haN x : ↥(cyclotomicField' a))
      = IntermediateField.equivOfEq
          (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN))
          (IntermediateField.liftAlgEquiv _ x) := rfl
  rw [h1]
  have h2 : ((IntermediateField.equivOfEq
          (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN))
          (IntermediateField.liftAlgEquiv _ x) : ↥(cyclotomicField' a)) : ℂ)
      = ((IntermediateField.liftAlgEquiv
          ((cyclotomicField' a).comap (cyclotomicField' N).val) x :
            ↥(IntermediateField.lift ((cyclotomicField' a).comap (cyclotomicField' N).val))) : ℂ) :=
    rfl
  rw [h2, IntermediateField.liftAlgEquiv_apply]

/-- Transport of a fixed field along an algebra isomorphism `e` and the induced
`autCongr e` on Galois groups. -/
theorem fixedField_map_autCongr {k A B : Type*} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (H : Subgroup (A ≃ₐ[k] A)) :
    (IntermediateField.fixedField H).map e.toAlgHom
      = IntermediateField.fixedField (H.map (AlgEquiv.autCongr e).toMonoidHom) := by
  ext z
  simp only [IntermediateField.mem_map, IntermediateField.mem_fixedField_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro τ hτ
    rw [Subgroup.mem_map] at hτ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    simp only [MulEquiv.coe_toMonoidHom, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]
    rw [hy σ hσ]
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    intro σ hσ
    have hmem : (AlgEquiv.autCongr e σ) ∈ H.map (AlgEquiv.autCongr e).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hσ
    have hzz := hz _ hmem
    rw [AlgEquiv.autCongr_apply] at hzz
    simp only [AlgEquiv.trans_apply] at hzz
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    exact hzz

/-- Naturality of `galEquivZMod` across the isomorphism `comapValEquiv r D hr` between the
copy of `ℚ(ζ_r)` inside `ℚ(ζ_D)` and `ℚ(ζ_r)` itself. -/
theorem galEquivZMod_comapValEquiv (r D : ℕ+) (hr : (r : ℕ) ∣ (D : ℕ))
    [IsCyclotomicExtension {(r : ℕ)} ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val)]
    [NumberField ↥((cyclotomicField' r).comap (cyclotomicField' D).val)]
    (σ : ↥((cyclotomicField' r).comap (cyclotomicField' D).val)
        ≃ₐ[ℚ] ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) :
    galEquivZMod (r : ℕ) ↥(cyclotomicField' r)
        (AlgEquiv.autCongr (comapValEquiv r D hr) σ)
      = galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val) σ := by
  set ζL : ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    IsCyclotomicExtension.zeta (r : ℕ) ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val)
      with hζLdef
  have hζL : IsPrimitiveRoot ζL (r : ℕ) :=
    IsCyclotomicExtension.zeta_spec (r : ℕ) ℚ _
  have hζLpow : ζL ^ (r : ℕ) = 1 := hζL.pow_eq_one
  set ζF : ↥(cyclotomicField' r) := comapValEquiv r D hr ζL with hζFdef
  have hζFpow : ζF ^ (r : ℕ) = 1 := by rw [hζFdef, ← map_pow, hζLpow, map_one]
  have hζF : IsPrimitiveRoot ζF (r : ℕ) := by
    rw [hζFdef]; exact hζL.map_of_injective (comapValEquiv r D hr).injective
  have key : (AlgEquiv.autCongr (comapValEquiv r D hr) σ) ζF
      = ζF ^ (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val) σ).val.val := by
    rw [AlgEquiv.autCongr_apply]
    simp only [AlgEquiv.trans_apply]
    rw [hζFdef, AlgEquiv.symm_apply_apply,
        galEquivZMod_apply_of_pow_eq (r : ℕ) _ σ hζLpow, map_pow]
  have key2 : (AlgEquiv.autCongr (comapValEquiv r D hr) σ) ζF
      = ζF ^ (galEquivZMod (r : ℕ) ↥(cyclotomicField' r)
          (AlgEquiv.autCongr (comapValEquiv r D hr) σ)).val.val :=
    galEquivZMod_apply_of_pow_eq (r : ℕ) _ _ hζFpow
  have hpow : ζF ^ (galEquivZMod (r : ℕ) ↥(cyclotomicField' r)
        (AlgEquiv.autCongr (comapValEquiv r D hr) σ)).val.val
      = ζF ^ (galEquivZMod (r : ℕ)
          ↥((cyclotomicField' r).comap (cyclotomicField' D).val) σ).val.val := by
    rw [← key2, key]
  rw [(hζF.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζF.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff'] at hpow
  simp only [ZMod.natCast_val, ZMod.cast_id] at hpow
  exact Units.ext hpow

end Workspace.ProofLemmas.CutOutFieldLevelInvariantProof

open Workspace.ProofLemmas.CutOutFieldLevelInvariantProof

/-- **Fixed-field descent (pure Galois theory).** For a normal intermediate field `L` of the finite
Galois extension `ℚ(ζ_D)/ℚ` and a subgroup `H ≤ Gal(L/ℚ)`, the fixed field of the pullback
`H.comap (restrictNormalHom L) ≤ Gal(ℚ(ζ_D)/ℚ)` is the lift to `ℚ(ζ_D)` of the fixed field of `H`.

Proved from Mathlib's `InfiniteGalois.restrict_fixedField`, composed with
`Subgroup.map_comap_eq_self_of_surjective` (the restriction map is surjective) and
`fixedField (H.comap (restrictNormalHom L)) ≤ L` (since that subgroup contains
`(restrictNormalHom L).ker = L.fixingSubgroup`, whose fixed field is `L`).  Stated over a generic
`L` so that `↥L` carries only its canonical `IntermediateField` ℚ-algebra structure — this avoids
the instance diamond that blocks the same argument inline (where `↥(cyclotomicField' D)` forces
`DivisionRing.toRatAlgebra`). -/
theorem fixedFieldDescent (D : ℕ+)
    (L : IntermediateField ℚ ↥(cyclotomicField' D)) [Normal ℚ ↥L]
    (H : Subgroup (↥L ≃ₐ[ℚ] ↥L)) :
    IntermediateField.fixedField (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L))
      = IntermediateField.lift (IntermediateField.fixedField H) := by
  -- Bridge the ℚ-algebra diamond: the Mathlib Galois lemmas below use `IntermediateField.algebra'`
  -- on `↥L`, so provide the `Normal` instance in that form (defeq to the ambient one).
  haveI hnorm : @Normal ℚ ↥L _ _ (IntermediateField.algebra' L) := by
    convert (inferInstance : Normal ℚ ↥L) using 2
  have hle : IntermediateField.fixedField
      (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L)) ≤ L := by
    have hker : (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L).ker
        ≤ H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L) := by
      intro σ hσ
      rw [MonoidHom.mem_ker] at hσ
      rw [Subgroup.mem_comap, hσ]
      exact one_mem H
    have hkereq : (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L).ker
        = L.fixingSubgroup := IntermediateField.restrictNormalHom_ker L
    calc IntermediateField.fixedField
            (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L))
        ≤ IntermediateField.fixedField
            (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L).ker :=
          IntermediateField.fixedField_le hker
      _ = IntermediateField.fixedField L.fixingSubgroup := by rw [hkereq]
      _ = L := IsGalois.fixedField_fixingSubgroup L
  have key := InfiniteGalois.restrict_fixedField
    (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L)) L
  rw [inf_eq_left.mpr hle] at key
  rw [key]
  exact congrArg (fun S => IntermediateField.lift (IntermediateField.fixedField S))
    (Subgroup.map_comap_eq_self_of_surjective
      (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) (E := ↥(cyclotomicField' D))) H)

/-- **Def A.5 (level-independence of the cut-out field).** For `r ∣ D`, the subfield of `ℂ`
cut out by a Dirichlet character `ψ` of modulus `r` is the same whether we regard `ψ` at level
`r` or push it up to level `D` via `changeLevel`. Proved from Mathlib only. -/
theorem CutOutFieldLevelInvariant (r D : ℕ+) (ψ : DirichletCharacter ℂ (r : ℕ)) (hr : (r : ℕ) ∣ (D : ℕ)) :
    cutOutField D (DirichletCharacter.changeLevel hr ψ) = cutOutField r ψ := by
  haveI iscL : IsCyclotomicExtension {(r : ℕ)} ℚ
      ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    IsCyclotomicExtension.equiv {(r : ℕ)} ℚ (↥(cyclotomicField' r)) (comapValEquiv r D hr).symm
  haveI isgL : IsGalois ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    IsGalois.of_algEquiv (comapValEquiv r D hr).symm
  haveI finL : FiniteDimensional ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    Module.Finite.equiv (comapValEquiv r D hr).symm.toLinearEquiv
  haveI nfL : NumberField ↥((cyclotomicField' r).comap (cyclotomicField' D).val) := ⟨⟩
  haveI galD : IsGalois ℚ ↥(cyclotomicField' D) := inferInstance
  haveI norD : Normal ℚ ↥(cyclotomicField' D) := inferInstance
  haveI norL := isgL.to_normal
  -- Level-compatibility square: `unitsMap hr ∘ galToUnits D = galEquivZMod r L ∘ restrictNormalHom L`.
  have hmid : ((ZMod.unitsMap hr).comp (galToUnits D).toMonoidHom)
      = (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom.comp
          (AlgEquiv.restrictNormalHom ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) := by
    refine MonoidHom.ext fun σ => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, galToUnits]
    exact (galEquivZMod_restrictNormal_apply (D : ℕ) ↥(cyclotomicField' D)
      (F := ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) hr σ).symm
  -- Kernel identity: the level-`D` kernel is the pullback of the level-`L` kernel.
  have hA : ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker
      = ((ψ.toUnitHom.comp
            (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker).comap
          (AlgEquiv.restrictNormalHom ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) := by
    rw [DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_assoc, hmid,
        ← MonoidHom.comp_assoc, MonoidHom.comap_ker]
  -- The image of the level-`D` kernel under restriction is exactly the level-`L` kernel.
  have hmapH : Subgroup.map
        (AlgEquiv.restrictNormalHom ↥((cyclotomicField' r).comap (cyclotomicField' D).val))
        ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker
      = (ψ.toUnitHom.comp
          (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker := by
    rw [hA]
    apply Subgroup.map_comap_eq_self_of_surjective
    exact AlgEquiv.restrictNormalHom_surjective _
  -- Descent of the fixed field along the tower `ℚ(ζ_D) / L / ℚ`.  This is the pure
  -- Galois-theory fact `InfiniteGalois.restrict_fixedField` (a fixed field descends along a
  -- normal intermediate field), specialised to our tower.  See `fixedFieldDescent` for the precise
  -- statement and the discussion there of the
  -- Mathlib ℚ-algebra instance diamond that blocks discharging it inline.
  have hB : IntermediateField.fixedField
        ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker
      = IntermediateField.lift
          (IntermediateField.fixedField
            (ψ.toUnitHom.comp
              (galEquivZMod (r : ℕ)
                ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker) := by
    rw [hA]
    haveI hn : @Normal ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val) _ _
        (IntermediateField.algebra' ((cyclotomicField' r).comap (cyclotomicField' D).val)) := by
      convert norL using 2
    exact @fixedFieldDescent D ((cyclotomicField' r).comap (cyclotomicField' D).val) hn
      (ψ.toUnitHom.comp
        (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker
  -- The two embeddings of `L` into `ℂ` agree: directly and through `comapValEquiv`.
  have hι : (cyclotomicField' D).val.comp
        ((cyclotomicField' r).comap (cyclotomicField' D).val).val
      = (cyclotomicField' r).val.comp (comapValEquiv r D hr).toAlgHom := by
    apply AlgHom.ext
    intro x
    have hx := comapValEquiv_coe r D hr x
    simpa only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_algHom]
      using hx.symm
  -- Naturality moves the level-`L` kernel to the level-`r` kernel across `comapValEquiv`.
  have hnat : (ψ.toUnitHom.comp
        (galEquivZMod (r : ℕ)
          ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker
      = ((ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker).comap
          (AlgEquiv.autCongr (comapValEquiv r D hr)).toMonoidHom := by
    ext σ
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, galToUnits]
    rw [galEquivZMod_comapValEquiv r D hr σ]
  have hnat_map : Subgroup.map (AlgEquiv.autCongr (comapValEquiv r D hr)).toMonoidHom
        (ψ.toUnitHom.comp
          (galEquivZMod (r : ℕ)
            ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker
      = (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker := by
    rw [hnat, Subgroup.map_comap_eq_self_of_surjective
      (AlgEquiv.autCongr (comapValEquiv r D hr)).surjective _]
  have hmapfix : (IntermediateField.fixedField
        (ψ.toUnitHom.comp
          (galEquivZMod (r : ℕ)
            ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker).map
        (comapValEquiv r D hr).toAlgHom
      = IntermediateField.fixedField (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker := by
    rw [fixedField_map_autCongr (comapValEquiv r D hr), hnat_map]
  -- Assemble.  Re-elaborate `cutOutField` in the current context (via `show`) so the fixed-field
  -- terms carry these instances and `hB` matches, then compose the two lift maps.
  have goalL : cutOutField D (DirichletCharacter.changeLevel hr ψ)
      = (IntermediateField.fixedField
          (ψ.toUnitHom.comp
            (galEquivZMod (r : ℕ)
              ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker).map
          ((cyclotomicField' D).val.comp
            ((cyclotomicField' r).comap (cyclotomicField' D).val).val) := by
    show IntermediateField.lift (IntermediateField.fixedField
        ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker) = _
    erw [hB]
    exact IntermediateField.map_map _ _ _
  have goalR : cutOutField r ψ
      = (IntermediateField.fixedField (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker).map
          (cyclotomicField' r).val := rfl
  rw [goalL, goalR, hι, ← hmapfix]
  exact (IntermediateField.map_map _ _ _).symm
