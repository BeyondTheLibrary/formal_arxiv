import Mathlib
import Workspace.Types.SplittingRamification

open scoped NumberField
open NumberField NumberField.InfinitePlace

theorem SublemmaTotallyRealDescends
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [NumberField.IsTotallyReal F]
    (hodd : Odd (Module.finrank F E)) :
    NumberField.IsTotallyReal E := by
  have hunr : IsUnramifiedAtInfinitePlaces F E :=
    IsUnramifiedAtInfinitePlaces_of_odd_finrank hodd
  rw [NumberField.isTotallyReal_iff]
  intro w
  have hw : w.IsUnramified F := hunr.isUnramified w
  rcases (NumberField.InfinitePlace.isUnramified_iff.1 hw) with h | h
  · exact h
  · exfalso
    have hre : (w.comap (algebraMap F E)).IsReal := NumberField.IsTotallyReal.isReal _
    exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 h) hre
