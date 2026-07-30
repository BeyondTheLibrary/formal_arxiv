import Mathlib

open scoped NumberField
open NumberField NumberField.InfinitePlace

/-- If `F` and `M` are number fields with `M` an extension of `F`, and both are totally real,
then `M/F` is unramified at all infinite places. -/
theorem SublemmaInfinitePlacesUnramifiedTotallyReal
    (F M : Type*) [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] [FiniteDimensional F M]
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal M] :
    IsUnramifiedAtInfinitePlaces F M := by
  refine ⟨fun w => ?_⟩
  refine NumberField.InfinitePlace.isUnramified_iff.2 (Or.inl ?_)
  exact NumberField.IsTotallyReal.isReal w
