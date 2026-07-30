import Mathlib

open scoped NumberField

theorem SubfieldComapOfIntermediateTotallyReal {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [NumberField ↥(⨆ i, L i)] (i : Fin ℓ) [NumberField ↥(L i)]
    [NumberField.IsTotallyReal ↥(L i)] :
    NumberField.IsTotallyReal
      ↥(Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) := by
  set N : IntermediateField ℚ ℂ := ⨆ i, L i with hN
  set ι : ↥N →+* ℂ := algebraMap ↥N ℂ with hι
  set S : Subfield ↥N := Subfield.comap ι (L i).toSubfield with hS
  have hLiN : L i ≤ N := le_iSup L i
  have hιinj : Function.Injective ι := (algebraMap ↥N ℂ).injective
  -- the ring map ↥S → ↥(L i) induced by the inclusion ι : ↥N → ℂ
  have hmem : ∀ x : ↥S, (ι.comp (Subfield.subtype S)) x ∈ (L i).toSubfield := fun x => x.2
  let g : ↥S →+* ↥(L i) := RingHom.codRestrict (ι.comp (Subfield.subtype S))
    (L i).toSubfield.toSubsemiring hmem
  have hginj : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply hιinj
    have : (g a : ℂ) = (g b : ℂ) := congrArg _ h
    simpa [g, RingHom.codRestrict] using this
  have hgsurj : Function.Surjective g := by
    intro y
    refine ⟨⟨⟨(y : ℂ), hLiN y.2⟩, ?_⟩, ?_⟩
    · show ι ⟨(y : ℂ), hLiN y.2⟩ ∈ (L i).toSubfield
      exact y.2
    · apply Subtype.ext
      rfl
  let e : ↥S ≃+* ↥(L i) := RingEquiv.ofBijective g ⟨hginj, hgsurj⟩
  exact NumberField.IsTotallyReal.ofRingEquiv e.symm
