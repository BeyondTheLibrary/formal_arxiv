import Mathlib

open scoped NumberField

theorem CompositumSubfieldsGenerateTop {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [NumberField ↥(⨆ i, L i)] :
    (⨆ i, Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) =
      (⊤ : Subfield ↥(⨆ i, L i)) := by
  set N : IntermediateField ℚ ℂ := ⨆ i, L i with hN
  set ι : ↥N →+* ℂ := algebraMap ↥N ℂ with hι
  have hιinj : Function.Injective ι := (algebraMap ↥N ℂ).injective
  have hrange : ι.fieldRange = N.toSubfield := by
    ext c
    simp only [RingHom.mem_fieldRange, IntermediateField.mem_toSubfield]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hc; exact ⟨⟨c, hc⟩, rfl⟩
  -- comap ι ∘ map ι = id  (ι injective)
  have hcm : ∀ X : Subfield ↥N, Subfield.comap ι (Subfield.map ι X) = X := by
    intro X
    ext x
    simp only [Subfield.mem_comap, Subfield.mem_map]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [hιinj hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩
  cases isEmpty_or_nonempty (Fin ℓ) with
  | inl hempty =>
    have hN0 : N = ⊥ := by rw [hN, iSup_of_empty]
    rw [iSup_of_empty, eq_top_iff]
    intro x _
    have hxb : (x : ℂ) ∈ (⊥ : IntermediateField ℚ ℂ) := by rw [← hN0]; exact x.2
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hxb
    have hxe : x = (q : ↥N) := by
      apply Subtype.ext
      rw [← hq]; simp
    rw [hxe]
    exact SubfieldClass.ratCast_mem _ q
  | inr hne =>
    have hmt : Subfield.map ι ⊤ = N.toSubfield := by
      rw [← hrange]; ext c; simp [Subfield.mem_map, RingHom.mem_fieldRange]
    have key : Subfield.map ι (⨆ i, Subfield.comap ι (L i).toSubfield) = Subfield.map ι ⊤ := by
      rw [hmt, (Subfield.gc_map_comap ι).l_iSup]
      have hstep : ∀ i, Subfield.map ι (Subfield.comap ι (L i).toSubfield) = (L i).toSubfield := by
        intro i
        rw [Subfield.map_comap_eq, hrange, inf_eq_left]
        intro c hc
        simp only [IntermediateField.mem_toSubfield] at hc ⊢
        exact (le_iSup L i) hc
      simp_rw [hstep]
      rw [← IntermediateField.iSup_toSubfield]
    rw [← hcm (⨆ i, Subfield.comap ι (L i).toSubfield), key, hcm]
