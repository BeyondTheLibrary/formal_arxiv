import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.GalUrOpenNormalThreePowerIndex

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

theorem GalUrIsProP :
    ∀ (F : Type) [Field F] [NumberField F], IsProP 3 (galUr 3 F) := by
  intro F _ _
  have hsep : Algebra.IsSeparable F (maxUnramifiedProPExt 3 F) := inferInstance
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
  have hgal : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  have halg : Algebra.IsAlgebraic F (maxUnramifiedProPExt 3 F) := inferInstance
  have hint : Algebra.IsIntegral F (maxUnramifiedProPExt 3 F) := halg.isIntegral
  unfold IsProP
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · exact InfiniteGalois.instCompactSpaceAlgEquivOfIsGalois F _
  · exact krullTopology_t2
  · exact inferInstance
  · exact GalUrOpenNormalThreePowerIndex F
