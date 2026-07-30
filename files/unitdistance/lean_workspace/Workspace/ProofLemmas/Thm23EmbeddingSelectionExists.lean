import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Workspace.Types.AdmissibleDatum

theorem Thm23EmbeddingSelectionExists (d : AdmissibleDatum) :
    Nonempty (EmbeddingSelection d.L d.K (deg d)) := by
  -- There are exactly `deg d = [L : ℚ]` embeddings `L → ℂ`.
  have hcard : Fintype.card (d.L →+* ℂ) = deg d := by
    unfold deg; rw [NumberField.Embeddings.card d.L ℂ]
  let e : Fin (deg d) ≃ (d.L →+* ℂ) := (Fintype.equivFinOfCardEq hcard).symm
  -- Every `L → ℂ` embedding extends to a `K → ℂ` embedding.
  have hext : ∀ ψ : d.L →+* ℂ, ∃ σ : d.K →+* ℂ, σ.comp (algebraMap d.L d.K) = ψ := by
    intro ψ
    letI : Algebra d.L ℂ := ψ.toAlgebra
    haveI : Algebra.IsAlgebraic d.L d.K := Algebra.IsAlgebraic.of_finite d.L d.K
    let σA : d.K →ₐ[d.L] ℂ := IsAlgClosed.lift
    refine ⟨σA.toRingHom, ?_⟩
    ext x
    show σA (algebraMap d.L d.K x) = ψ x
    rw [AlgHom.commutes]; rfl
  refine ⟨⟨fun r => (hext (e r)).choose, ?_, ?_⟩⟩
  · -- restriction map is bijective
    have hspec : (fun r => ((hext (e r)).choose).comp (algebraMap d.L d.K)) = ⇑e :=
      funext fun r => (hext (e r)).choose_spec
    rw [hspec]; exact e.bijective
  · -- each restriction is real
    intro r
    rw [(hext (e r)).choose_spec]
    exact NumberField.IsTotallyReal.complexEmbedding_isReal (e r)
