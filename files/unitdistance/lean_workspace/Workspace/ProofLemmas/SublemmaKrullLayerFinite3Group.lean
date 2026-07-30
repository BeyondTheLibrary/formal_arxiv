import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.GalUrIsProP
import Workspace.ProofLemmas.SublemmaFixedFieldKernel
import Workspace.ProofLemmas.GalUrOpenNormalThreePowerIndex

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

theorem SublemmaKrullLayerFinite3Group
    (F : Type) [Field F] [NumberField F]
    (hpro : IsProP 3 (galUr 3 F))
    (H : Subgroup (galUr 3 F))
    (hHopen : IsOpen (H : Set (galUr 3 F)))
    (hHnormal : H.Normal) :
    ∃ (_ : FiniteDimensional F ↥(fixedFieldOf 3 F H))
      (_ : IsGalois F ↥(fixedFieldOf 3 F H))
      (hn : Normal F ↥(fixedFieldOf 3 F H)),
      (letI := hn
       Function.Surjective
         (AlgEquiv.restrictNormalHom (F := F)
           (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))) ∧
      (letI := hn
       MonoidHom.ker
         (AlgEquiv.restrictNormalHom (F := F)
           (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)) = H) ∧
      IsPGroup 3 (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H)) := by
  -- Galois structure on the ambient field K = F^{ur,3}.
  have hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    apply IntermediateField.normal_iSup (h := ?_)
    rintro ⟨E, hE⟩
    obtain ⟨hfd, hg, _, _⟩ := hE
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    haveI := hg
    infer_instance
  haveI : Normal F (maxUnramifiedProPExt 3 F) := hnorm
  haveI hgalK : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  -- H is closed, being an open subgroup of a topological group.
  have hclosed : IsClosed (H : Set (galUr 3 F)) := H.isClosed_of_isOpen hHopen
  let Hc : ClosedSubgroup (galUr 3 F) := ⟨H, hclosed⟩
  -- Krull correspondence: the fixing subgroup of the fixed field of (closed) H is H.
  have hff : (fixedFieldOf 3 F H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField
      (k := F) (K := ↥(maxUnramifiedProPExt 3 F)) Hc
  -- FiniteDimensional and IsGalois of the finite layer E = fixedField H.
  have hfin_gal :
      FiniteDimensional F ↥(fixedFieldOf 3 F H) ∧ IsGalois F ↥(fixedFieldOf 3 F H) := by
    rw [← InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (fixedFieldOf 3 F H), hff]
    exact ⟨hHopen, hHnormal⟩
  obtain ⟨hfd, hgal⟩ := hfin_gal
  haveI := hfd
  haveI := hgal
  haveI hn : Normal F ↥(fixedFieldOf 3 F H) := inferInstance
  -- Surjectivity of the restriction homomorphism to the normal layer.
  have hsurj :
      Function.Surjective
        (AlgEquiv.restrictNormalHom (F := F)
          (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)) :=
    AlgEquiv.restrictNormalHom_surjective
      (F := F) (K₁ := ↥(fixedFieldOf 3 F H)) (↥(maxUnramifiedProPExt 3 F))
  -- Kernel of the restriction homomorphism is exactly H (cited sublemma).
  have hker :
      MonoidHom.ker
        (AlgEquiv.restrictNormalHom (F := F)
          (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)) = H :=
    SublemmaFixedFieldKernel F H hHopen hHnormal
  refine ⟨hfd, hgal, hn, hsurj, hker, ?_⟩
  -- |Gal(E/F)| = |range restrictNormalHom| = |G/ker| = H.index = 3^k, hence a 3-group.
  obtain ⟨k, hk⟩ := GalUrOpenNormalThreePowerIndex F H hHnormal hHopen
  refine IsPGroup.of_card (n := k) ?_
  -- Forward chain, rewriting ONLY the `H` inside `H.index` (never inside `fixedFieldOf`).
  have step1 :
      Nat.card (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H))
        = Nat.card ↥(⊤ : Subgroup (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H))) :=
    (Nat.card_congr
      (Subgroup.topEquiv
        (G := ↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H))).toEquiv).symm
  have step2 :
      Nat.card ↥(⊤ : Subgroup (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H)))
        = Nat.card ↥(MonoidHom.range
            (AlgEquiv.restrictNormalHom (F := F)
              (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))) := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
  have step3 :
      Nat.card ↥(MonoidHom.range
          (AlgEquiv.restrictNormalHom (F := F)
            (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)))
        = (MonoidHom.ker
            (AlgEquiv.restrictNormalHom (F := F)
              (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))).index :=
    (Subgroup.index_ker _).symm
  have step4 :
      (MonoidHom.ker
          (AlgEquiv.restrictNormalHom (F := F)
            (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))).index = H.index := by
    rw [hker]
  rw [step1, step2, step3, step4, hk]
