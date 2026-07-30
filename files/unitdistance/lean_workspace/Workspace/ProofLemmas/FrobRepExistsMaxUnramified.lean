-- Cited from J. Neukirch, Algebraic Number Theory, Springer, 1999, Ch. VII (infinite
-- Galois theory / Chebotarev setup).
-- The existence of a Frobenius representative at a prime v in the profinite Galois group
-- Gal(F^{ur,3}/F) is obtained by a compactness / finite-intersection-property argument.
--
-- Proof outline:
--   * `galoisOmega`   : F^{ur,3} = sSup of finite Galois everywhere-unramified 3-group layers is
--                       Galois over F (Normal via `normal_iSup`, separable via `isSeparable_iSup`),
--                       hence `galUr 3 F` is a `CompactSpace` (Mathlib profinite Galois instance).
--   * `frobSet`       : for each finite Galois layer E of F^{ur,3}/F, the set of σ ∈ galUr whose
--                       restriction to E is a Frobenius at v; it is CLOSED (continuous restriction
--                       into a discrete finite Galois group).
--   * `frobSet_nonempty` (finite-layer Frobenius EXISTENCE): from Mathlib's
--                       `IsArithFrobAt.exists_of_isInvariant` at the layer E, lifted to galUr via
--                       surjectivity of `restrictNormalHom`. The group Frobenius bridges to the
--                       workspace's `IsFrobeniusAtPrime` via `galRestrict`.
--   * `frobSet_antitone` (finite-layer Frobenius RESTRICTION-COMPATIBILITY): a Frobenius on a
--                       larger layer restricts to a Frobenius on a smaller one, via `galRestrict'`
--                       naturality and the pure `isArithFrobAt_comap_of_comm` compatibility lemma.
--   * The family `{frobSet E}` is directed (compositum) with the finite-intersection property, so
--     by Cantor's intersection theorem for a compact space the total intersection is nonempty; any
--     element is a Frobenius representative on every finite layer, i.e. `IsFrobeniusRepAt`.
--
-- Paper label: prerequisite of §3.1 Chebotarev application (Proposition 3.6).
-- NL statement: For every number field F and every nonzero prime v of 𝓞 F, there exists an
-- element σ of galUr 3 F = Gal(F^{ur,3}/F) that is a Frobenius representative at v, i.e. whose
-- restriction to every finite-dimensional Galois layer F ≤ E ≤ F^{ur,3} is a Frobenius element at v.
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.FrobeniusSplitting

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.FrobeniusSplitting

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace FrobRepProof

variable (F : Type*) [Field F] [NumberField F]

/-- `F^{ur,3}` is Galois over `F` (compositum of finite Galois layers). -/
instance galoisOmega : IsGalois F (maxUnramifiedProPExt 3 F) := by
  set S : Set (IntermediateField F (AlgebraicClosure F)) :=
    {E | IsFiniteUnramifiedProPExt 3 F E} with hS
  have hnorm : ∀ i : ↥S, Normal F (i : IntermediateField F (AlgebraicClosure F)) := by
    rintro ⟨E, hE⟩; obtain ⟨hfd, hgal, -, -⟩ := hE; haveI := hfd; exact hgal.to_normal
  have hsep : ∀ i : ↥S, Algebra.IsSeparable F (i : IntermediateField F (AlgebraicClosure F)) := by
    rintro ⟨E, hE⟩; obtain ⟨hfd, hgal, -, -⟩ := hE; haveI := hfd; exact hgal.to_isSeparable
  have hmax : maxUnramifiedProPExt 3 F = ⨆ i : ↥S, (i : IntermediateField F (AlgebraicClosure F)) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
  rw [hmax]
  haveI : Normal F (↥(⨆ i : ↥S, (i : IntermediateField F (AlgebraicClosure F)))) :=
    IntermediateField.normal_iSup F (AlgebraicClosure F) (h := hnorm)
  haveI : Algebra.IsSeparable F (↥(⨆ i : ↥S, (i : IntermediateField F (AlgebraicClosure F)))) :=
    IntermediateField.isSeparable_iSup (h := hsep)
  exact ⟨⟩

/-- The set of `σ ∈ galUr 3 F` whose restriction to the finite Galois layer `E` is a Frobenius
at `v`. -/
noncomputable def frobSet (v : Ideal (𝓞 F))
    (E : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd : FiniteDimensional F E) (hgal : IsGalois F E) : Set (galUr 3 F) :=
  letI := hfd
  letI := hgal
  letI : NumberField E := NumberField.of_module_finite (K := F) (L := (E : Type _))
  (AlgEquiv.restrictNormalHom (E : Type _)) ⁻¹' {τ | IsFrobeniusAt τ v}

/-- Pure ring-theoretic compatibility of an arithmetic Frobenius under an algebra map. -/
theorem isArithFrobAt_comap_of_comm
    {R Sa Sb : Type*} [CommRing R] [CommRing Sa] [CommRing Sb]
    [Algebra R Sa] [Algebra R Sb] (j : Sa →ₐ[R] Sb)
    {φ : Sa →ₐ[R] Sa} {φ' : Sb →ₐ[R] Sb} {Q' : Ideal Sb}
    (hcomm : ∀ x, j (φ x) = φ' (j x)) (H' : φ'.IsArithFrobAt Q') :
    φ.IsArithFrobAt (Q'.comap (j : Sa →+* Sb)) := by
  have hunder : (Q'.comap (j : Sa →+* Sb)).under R = Q'.under R := by
    simp only [Ideal.under_def]
    rw [Ideal.comap_comap]
    congr 1
    exact j.comp_algebraMap
  intro x
  rw [hunder, Ideal.mem_comap, map_sub, map_pow]
  simp only [RingHom.coe_coe]
  rw [hcomm]
  exact H' (j x)

/-- Finite-layer Frobenius EXISTENCE: some `σ ∈ galUr 3 F` restricts to a Frobenius at `v` on `E`. -/
theorem frobSet_nonempty (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime)
    (E : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd : FiniteDimensional F E) (hgal : IsGalois F E) :
    (frobSet F v E hfd hgal).Nonempty := by
  letI := hfd
  letI := hgal
  haveI : Normal F (E : Type _) := hgal.to_normal
  letI : NumberField (E : Type _) := NumberField.of_module_finite (K := F) (L := (E : Type _))
  haveI : v.IsPrime := hvp
  obtain ⟨Q, hQp, hQlo⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver v (𝓞 (E : Type _)))).some
  haveI : Q.IsPrime := hQp
  haveI : Q.LiesOver v := hQlo
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hv
    have hunder : v = Q.under (𝓞 F) := hQlo.over
    rw [h] at hunder
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 (E : Type _)))] at hunder
    exact hunder
  haveI : Q.IsMaximal := hQp.isMaximal hQbot
  haveI : Finite (𝓞 (E : Type _) ⧸ Q) := inferInstance
  obtain ⟨τ, hτ⟩ :=
    IsArithFrobAt.exists_of_isInvariant (𝓞 F) ((E : Type _) ≃ₐ[F] (E : Type _)) Q
  have hbridge : (galRestrict (𝓞 F) F (E : Type _) (𝓞 (E : Type _)) τ).toAlgHom
      = MulSemiringAction.toAlgHom (𝓞 F) (𝓞 (E : Type _)) τ := by
    apply AlgHom.ext
    intro x
    apply IsFractionRing.injective (𝓞 (E : Type _)) (E : Type _)
    show algebraMap (𝓞 (E : Type _)) (E : Type _)
          (galRestrict (𝓞 F) F (E : Type _) (𝓞 (E : Type _)) τ x)
        = algebraMap (𝓞 (E : Type _)) (E : Type _) (τ • x)
    rw [algebraMap_galRestrict_apply]
    rfl
  have hfrob : IsFrobeniusAtPrime τ Q := by
    show (galRestrict (𝓞 F) F (E : Type _) (𝓞 (E : Type _)) τ).toAlgHom.IsArithFrobAt Q
    rw [hbridge]; exact hτ
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := (E : Type _)) (maxUnramifiedProPExt 3 F : Type _) τ
  refine ⟨s, ?_⟩
  show IsFrobeniusAt (AlgEquiv.restrictNormalHom (E : Type _) s) v
  rw [hs]
  exact ⟨Q, hQp, hQlo, hfrob⟩

/-- Finite-layer Frobenius RESTRICTION-COMPATIBILITY: a Frobenius on a larger layer `E₂` restricts
to a Frobenius on a smaller layer `E₁ ≤ E₂`. -/
theorem frobSet_antitone (v : Ideal (𝓞 F))
    (E₁ E₂ : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd₁ : FiniteDimensional F E₁) (hgal₁ : IsGalois F E₁)
    (hfd₂ : FiniteDimensional F E₂) (hgal₂ : IsGalois F E₂)
    (hle : E₁ ≤ E₂) :
    frobSet F v E₂ hfd₂ hgal₂ ⊆ frobSet F v E₁ hfd₁ hgal₁ := by
  letI := hfd₁; letI := hfd₂; letI := hgal₁; letI := hgal₂
  haveI : Normal F (E₁ : Type _) := hgal₁.to_normal
  haveI : Normal F (E₂ : Type _) := hgal₂.to_normal
  letI : NumberField (E₁ : Type _) := NumberField.of_module_finite (K := F) (L := (E₁ : Type _))
  letI : NumberField (E₂ : Type _) := NumberField.of_module_finite (K := F) (L := (E₂ : Type _))
  intro σ hσ
  simp only [frobSet, Set.mem_preimage, Set.mem_setOf_eq] at hσ ⊢
  obtain ⟨Q₂, hQ₂p, hQ₂lo, hQ₂frob⟩ := hσ
  haveI : Q₂.IsPrime := hQ₂p
  set τ₁ := AlgEquiv.restrictNormalHom (F := F)
    (K₁ := (maxUnramifiedProPExt 3 F : Type _)) (E₁ : Type _) σ with hτ₁
  set τ₂ := AlgEquiv.restrictNormalHom (F := F)
    (K₁ := (maxUnramifiedProPExt 3 F : Type _)) (E₂ : Type _) σ with hτ₂
  let incl : (E₁ : Type _) →ₐ[F] (E₂ : Type _) := IntermediateField.inclusion hle
  let j : 𝓞 (E₁ : Type _) →ₐ[𝓞 F] 𝓞 (E₂ : Type _) :=
    galRestrict' (𝓞 F) (𝓞 (E₁ : Type _)) (𝓞 (E₂ : Type _)) incl
  have hincl : ∀ z : (E₁ : Type _),
      algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _) (incl z)
      = algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) z := by
    intro z
    show algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _)
        (IntermediateField.inclusion hle z)
      = algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) z
    simp only [IntermediateField.algebraMap_apply, IntermediateField.coe_inclusion]
  have hfield : ∀ y : (E₁ : Type _), incl (τ₁ y) = τ₂ (incl y) := by
    intro y
    apply FaithfulSMul.algebraMap_injective (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _)
    have e1 : algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _) (incl (τ₁ y))
        = σ (algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) y) := by
      rw [hincl (τ₁ y)]
      exact AlgEquiv.restrictNormal_commutes σ (E₁ : Type _) y
    have e2 : algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _) (τ₂ (incl y))
        = σ (algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) y) := by
      have h := AlgEquiv.restrictNormal_commutes σ (E₂ : Type _) (incl y)
      rw [hincl y] at h
      exact h
    rw [e1, e2]
  have hcomm : ∀ x, j ((galRestrict (𝓞 F) F (E₁ : Type _) (𝓞 (E₁ : Type _)) τ₁).toAlgHom x)
      = (galRestrict (𝓞 F) F (E₂ : Type _) (𝓞 (E₂ : Type _)) τ₂).toAlgHom (j x) := by
    intro x
    apply IsFractionRing.injective (𝓞 (E₂ : Type _)) (E₂ : Type _)
    show algebraMap (𝓞 (E₂ : Type _)) (E₂ : Type _)
          (j (galRestrict (𝓞 F) F (E₁ : Type _) (𝓞 (E₁ : Type _)) τ₁ x))
        = algebraMap (𝓞 (E₂ : Type _)) (E₂ : Type _)
          (galRestrict (𝓞 F) F (E₂ : Type _) (𝓞 (E₂ : Type _)) τ₂ (j x))
    rw [algebraMap_galRestrict'_apply, algebraMap_galRestrict_apply,
      algebraMap_galRestrict_apply, algebraMap_galRestrict'_apply, hfield]
  refine ⟨Q₂.comap (j : 𝓞 (E₁ : Type _) →+* 𝓞 (E₂ : Type _)), inferInstance, ?_, ?_⟩
  · refine ⟨?_⟩
    have : v = Q₂.under (𝓞 F) := hQ₂lo.over
    rw [this, Ideal.under_def, Ideal.under_def, Ideal.comap_comap]
    congr 1
    exact (j.comp_algebraMap).symm
  · show (galRestrict (𝓞 F) F (E₁ : Type _) (𝓞 (E₁ : Type _)) τ₁).toAlgHom.IsArithFrobAt _
    exact isArithFrobAt_comap_of_comm j hcomm hQ₂frob

/-- Closedness of the finite-layer Frobenius set. -/
theorem frobSet_isClosed (v : Ideal (𝓞 F))
    (E : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd : FiniteDimensional F E) (hgal : IsGalois F E) :
    IsClosed (frobSet F v E hfd hgal) := by
  letI := hfd
  letI := hgal
  letI : NumberField (E : Type _) := NumberField.of_module_finite (K := F) (L := (E : Type _))
  haveI : DiscreteTopology ((E : Type _) ≃ₐ[F] (E : Type _)) :=
    krullTopology_discreteTopology_of_finiteDimensional F (E : Type _)
  exact (isClosed_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous E)

end FrobRepProof

open FrobRepProof

/-- **Existence of a Frobenius representative in `Gal(F^{ur,3}/F)` at an unramified prime.**
Proved from Mathlib (infinite Galois theory, compactness): the decomposition system at a prime `v`
assembles, by the finite-intersection property in the compact profinite group `galUr 3 F`, into a
single element restricting to a Frobenius on every finite Galois layer. -/
theorem FrobRepExistsMaxUnramified
    (F : Type*) [Field F] [NumberField F]
    (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime) :
    ∃ σ : galUr 3 F, IsFrobeniusRepAt 3 F σ v := by
  haveI : CompactSpace (galUr 3 F) := inferInstance
  set Idx := {E : IntermediateField F (maxUnramifiedProPExt 3 F) //
    FiniteDimensional F E ∧ IsGalois F E} with hIdx
  set t : Idx → Set (galUr 3 F) := fun EE => frobSet F v EE.1 EE.2.1 EE.2.2 with ht
  haveI : Nonempty Idx := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  have hclosed : ∀ EE : Idx, IsClosed (t EE) := fun EE => frobSet_isClosed F v EE.1 EE.2.1 EE.2.2
  have hcompact : ∀ EE : Idx, IsCompact (t EE) := fun EE => (hclosed EE).isCompact
  have hne : ∀ EE : Idx, (t EE).Nonempty := fun EE => frobSet_nonempty F v hv hvp EE.1 EE.2.1 EE.2.2
  have hdir : Directed (· ⊇ ·) t := by
    rintro ⟨E₁, hfd₁, hgal₁⟩ ⟨E₂, hfd₂, hgal₂⟩
    haveI := hfd₁; haveI := hfd₂; haveI := hgal₁; haveI := hgal₂
    haveI : FiniteDimensional F (↥(E₁ ⊔ E₂)) := IntermediateField.finiteDimensional_sup E₁ E₂
    haveI : IsGalois F (↥(E₁ ⊔ E₂)) := inferInstance
    refine ⟨⟨E₁ ⊔ E₂, ⟨‹_›, ‹_›⟩⟩, ?_, ?_⟩
    · exact frobSet_antitone F v E₁ (E₁ ⊔ E₂) hfd₁ hgal₁ ‹_› ‹_› le_sup_left
    · exact frobSet_antitone F v E₂ (E₁ ⊔ E₂) hfd₂ hgal₂ ‹_› ‹_› le_sup_right
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hdir hne hcompact hclosed
  refine ⟨σ, ?_⟩
  intro E hfdE hgalE
  have := Set.mem_iInter.mp hσ ⟨E, hfdE, hgalE⟩
  exact this
