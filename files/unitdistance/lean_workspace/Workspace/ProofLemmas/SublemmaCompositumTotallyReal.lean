import Mathlib
import Workspace.ProofLemmas.CompositumSubfieldsGenerateTop
import Workspace.ProofLemmas.SubfieldComapOfIntermediateTotallyReal

open scoped NumberField

theorem SublemmaCompositumTotallyReal {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [∀ i, NumberField ↥(L i)] [∀ i, NumberField.IsTotallyReal ↥(L i)]
    [NumberField ↥(⨆ i, L i)] :
    NumberField.IsTotallyReal ↥(⨆ i, L i) := by
  haveI : ∀ i, NumberField.IsTotallyReal
      ↥(Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) := fun i =>
    SubfieldComapOfIntermediateTotallyReal L i
  have htop : (⨆ i, Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) =
      (⊤ : Subfield ↥(⨆ i, L i)) := CompositumSubfieldsGenerateTop L
  have h1 : NumberField.IsTotallyReal
      ↥(⨆ i, Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) :=
    NumberField.isTotallyReal_iSup
  rw [htop] at h1
  haveI := h1
  exact NumberField.IsTotallyReal.ofRingEquiv Subfield.topEquiv
