import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.SplittingRamification
import Workspace.Types.DiscriminantsClassNumber

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.SplittingRamification
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 1000000

namespace SublemmaLayerIsoAux

variable {R S S₁ : Type*} [CommRing R] [CommRing S] [CommRing S₁] [Algebra R S] [Algebra R S₁]

/-- `Ideal.map φ` composed with `Ideal.map φ.symm` is the identity. -/
lemma map_symm_map (φ : S ≃ₐ[R] S₁) (Q : Ideal S₁) :
    Ideal.map φ (Ideal.map φ.symm Q) = Q := by
  show Ideal.map (φ : S →+* S₁) (Ideal.map (φ.symm : S₁ →+* S) Q) = Q
  rw [Ideal.map_map]
  have h : ((φ : S →+* S₁).comp (φ.symm : S₁ →+* S)) = RingHom.id S₁ := by ext x; simp
  rw [h, Ideal.map_id]

/-- `Ideal.map φ` is injective for an algebra equivalence `φ`. -/
lemma map_injective (φ : S ≃ₐ[R] S₁) : Function.Injective (Ideal.map φ) := by
  have hleft : Function.LeftInverse (Ideal.comap φ) (Ideal.map φ) :=
    fun I => Ideal.comap_map_of_bijective φ φ.bijective
  exact hleft.injective

/-- The set of primes over `p` in `S₁` is the image under `Ideal.map φ` of those in `S`. -/
lemma primesOver_image (φ : S ≃ₐ[R] S₁) (p : Ideal R) :
    p.primesOver S₁ = Ideal.map φ '' p.primesOver S := by
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hQp, hQl⟩
    refine ⟨Ideal.map φ.symm Q, ⟨?_, ?_⟩, map_symm_map φ Q⟩
    · haveI := hQp; exact Ideal.map_isPrime_of_equiv φ.symm
    · haveI := hQl; exact Ideal.map_equiv_liesOver Q p φ.symm
  · rintro ⟨P, ⟨hPp, hPl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · haveI := hPp; exact Ideal.map_isPrime_of_equiv φ
    · haveI := hPl; exact Ideal.map_equiv_liesOver P p φ

/-- The number of primes over `p` is preserved by an algebra equivalence. -/
lemma primesOver_ncard (φ : S ≃ₐ[R] S₁) (p : Ideal R) :
    (p.primesOver S₁).ncard = (p.primesOver S).ncard := by
  rw [primesOver_image φ p, Set.ncard_image_of_injective _ (map_injective φ)]

/-- Ramification index over `p` being `1` transfers along an algebra equivalence. -/
lemma ram_transfer (φ : S ≃ₐ[R] S₁) (p : Ideal R)
    (h : ∀ P ∈ p.primesOver S, p.ramificationIdx P = 1) :
    ∀ Q ∈ p.primesOver S₁, p.ramificationIdx Q = 1 := by
  intro Q hQ
  rw [primesOver_image φ p] at hQ
  obtain ⟨P, hPmem, rfl⟩ := hQ
  rw [Ideal.ramificationIdx_map_eq p P φ]
  exact h P hPmem

/-- Ramification index and inertia degree both being `1` transfers along an algebra equivalence. -/
lemma raminertia_transfer (φ : S ≃ₐ[R] S₁) (p : Ideal R)
    (h : ∀ P ∈ p.primesOver S, p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1) :
    ∀ Q ∈ p.primesOver S₁, p.ramificationIdx Q = 1 ∧ p.inertiaDeg Q = 1 := by
  intro Q hQ
  rw [primesOver_image φ p] at hQ
  obtain ⟨P, hPmem, rfl⟩ := hQ
  rw [Ideal.ramificationIdx_map_eq p P φ, Ideal.inertiaDeg_map_eq p P φ]
  exact h P hPmem

/-- Unramifiedness at infinite places transfers along an algebra equivalence over `F`. -/
lemma inf_transfer {F E Fj : Type*} [Field F] [Field E] [Field Fj]
    [Algebra F E] [Algebra F Fj] (e : E ≃ₐ[F] Fj)
    (hE : IsUnramifiedAtInfinitePlaces F E) : IsUnramifiedAtInfinitePlaces F Fj := by
  refine ⟨fun u => ?_⟩
  have hv := hE.isUnramified (u.comap (e : E →+* Fj))
  have h2 := hv.comap_algHom (e.symm : Fj →ₐ[F] E)
  have hcomp : (u.comap (e : E →+* Fj)).comap ((e.symm : Fj →ₐ[F] E) : Fj →+* E) = u := by
    rw [← NumberField.InfinitePlace.comap_comp]
    convert NumberField.InfinitePlace.comap_id u using 2
    ext x; simp
  rwa [hcomp] at h2

end SublemmaLayerIsoAux

theorem SublemmaLayerIso (F : Type*) [Field F] [NumberField F]
    (H : Subgroup (galUr 3 F))
    [FiniteDimensional F (fixedFieldOf 3 F H : Type _)] :
    haveI : NumberField (fixedFieldOf 3 F H : Type _) :=
      NumberField.of_module_finite F (fixedFieldOf 3 F H : Type _)
    ∃ _e : (fixedFieldOf 3 F H : Type _) ≃ₐ[F]
        (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
          (fixedFieldOf 3 F H) : Type _),
      ∃ _hfd : FiniteDimensional F
          (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
            (fixedFieldOf 3 F H) : Type _),
        haveI := _hfd
        haveI : NumberField
            (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
              (fixedFieldOf 3 F H) : Type _) :=
          NumberField.of_module_finite F
            (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
              (fixedFieldOf 3 F H) : Type _)
        (FiniteDimensional F (fixedFieldOf 3 F H : Type _) ↔
            FiniteDimensional F
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (NumberField (fixedFieldOf 3 F H : Type _) ↔
            NumberField
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (IsGalois F (fixedFieldOf 3 F H : Type _) ↔
            IsGalois F
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (EverywhereUnramified F (fixedFieldOf 3 F H : Type _) ↔
            EverywhereUnramified F
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (IsPGroup 3 ((fixedFieldOf 3 F H : Type _) ≃ₐ[F] (fixedFieldOf 3 F H : Type _)) →
            IsPGroup 3
              ((IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                  (fixedFieldOf 3 F H) : Type _) ≃ₐ[F]
                (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                  (fixedFieldOf 3 F H) : Type _))) ∧
        (NumberField.IsTotallyReal (fixedFieldOf 3 F H : Type _) ↔
            NumberField.IsTotallyReal
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (rootDiscriminant
            (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
              (fixedFieldOf 3 F H) : Type _) =
          rootDiscriminant (fixedFieldOf 3 F H : Type _)) ∧
        (∀ q : ℕ, SplitsCompletelyRat q (fixedFieldOf 3 F H : Type _) ↔
            SplitsCompletelyRat q
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) := by
  -- The algebra iso E ≃ₐ[F] Fj
  set val := IntermediateField.val (maxUnramifiedProPExt 3 F) with hval
  set E := (fixedFieldOf 3 F H : Type _) with hE
  set Fj := (IntermediateField.map val (fixedFieldOf 3 F H) : Type _) with hFj
  set e : E ≃ₐ[F] Fj := IntermediateField.equivMap (fixedFieldOf 3 F H) val with he
  have hfd : FiniteDimensional F Fj := LinearEquiv.finiteDimensional e.toLinearEquiv
  refine ⟨e, hfd, ?_⟩
  haveI nfE : NumberField E := NumberField.of_module_finite F E
  haveI nfFj : NumberField Fj := NumberField.of_module_finite F Fj
  have hrank : Module.finrank ℚ E = Module.finrank ℚ Fj :=
    LinearEquiv.finrank_eq (e.restrictScalars ℚ).toLinearEquiv
  -- Ring-of-integers algebra equivalences transporting the arithmetic
  set φ : 𝓞 E ≃ₐ[𝓞 F] 𝓞 Fj := NumberField.RingOfIntegers.mapAlgEquiv e with hφ
  set φℤ : 𝓞 E ≃ₐ[ℤ] 𝓞 Fj := φ.restrictScalars ℤ with hφℤ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- FiniteDimensional iff
    exact ⟨fun _ => hfd, fun _ => ‹FiniteDimensional F E›⟩
  · -- NumberField iff
    exact ⟨fun _ => nfFj, fun _ => nfE⟩
  · -- IsGalois iff
    exact AlgEquiv.transfer_galois e
  · -- EverywhereUnramified iff
    constructor
    · rintro ⟨hfin, hinf⟩
      refine ⟨?_, ?_⟩
      · intro p hp hpp Q hQ
        exact SublemmaLayerIsoAux.ram_transfer φ p (hfin p hp hpp) Q hQ
      · exact SublemmaLayerIsoAux.inf_transfer e hinf
    · rintro ⟨hfin, hinf⟩
      refine ⟨?_, ?_⟩
      · intro p hp hpp P hP
        exact SublemmaLayerIsoAux.ram_transfer φ.symm p (hfin p hp hpp) P hP
      · exact SublemmaLayerIsoAux.inf_transfer e.symm hinf
  · -- IsPGroup forward
    exact fun h => IsPGroup.of_equiv h (AlgEquiv.autCongr e)
  · -- IsTotallyReal iff
    exact NumberField.isTotallyReal_iff_ofRingEquiv e.toRingEquiv
  · -- rootDiscriminant equal
    have hdiscr : NumberField.discr E = NumberField.discr Fj :=
      NumberField.discr_eq_discr_of_ringEquiv E e.toRingEquiv
    unfold rootDiscriminant
    rw [hdiscr, hrank]
  · -- SplitsCompletelyRat iff
    intro q
    constructor
    · rintro ⟨hq, hncard, hrest⟩
      refine ⟨hq, ?_, ?_⟩
      · rw [SublemmaLayerIsoAux.primesOver_ncard φℤ (Ideal.span {(q : ℤ)}), hncard, hrank]
      · exact SublemmaLayerIsoAux.raminertia_transfer φℤ (Ideal.span {(q : ℤ)}) hrest
    · rintro ⟨hq, hncard, hrest⟩
      refine ⟨hq, ?_, ?_⟩
      · rw [SublemmaLayerIsoAux.primesOver_ncard φℤ.symm (Ideal.span {(q : ℤ)}), hncard, ← hrank]
      · exact SublemmaLayerIsoAux.raminertia_transfer φℤ.symm (Ideal.span {(q : ℤ)}) hrest
