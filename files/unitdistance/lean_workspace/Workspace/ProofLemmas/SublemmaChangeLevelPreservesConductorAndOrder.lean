import Mathlib

open DirichletCharacter

theorem SublemmaChangeLevelPreservesConductorAndOrder
    {D : ℕ} :
    ∀ {r : ℕ} [NeZero D] (ψ : DirichletCharacter ℂ r) (hr : r ∣ D),
      DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ)
        = DirichletCharacter.conductor ψ
      ∧ orderOf ((DirichletCharacter.changeLevel hr) ψ) = orderOf ψ := by
  intro r _ ψ hr
  haveI hrne : NeZero r :=
    ⟨fun h => (NeZero.ne D) (Nat.eq_zero_of_zero_dvd (h ▸ hr))⟩
  -- Direction 1: conductor of the lifted character divides conductor of ψ.
  have h1 : DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ)
      ∣ DirichletCharacter.conductor ψ := by
    obtain ⟨hc, ψ₀, hψ₀⟩ := DirichletCharacter.factorsThrough_conductor ψ
    refine DirichletCharacter.conductor_dvd_of_mem_conductorSet _ ?_
    refine ⟨dvd_trans hc hr, ψ₀, ?_⟩
    conv_lhs => rw [hψ₀]
    exact (DirichletCharacter.changeLevel_trans ψ₀ hc hr).symm
  -- Direction 2: conductor of ψ divides conductor of the lifted character.
  have h2 : DirichletCharacter.conductor ψ
      ∣ DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ) := by
    obtain ⟨heD, χ₀, hχ₀⟩ :=
      DirichletCharacter.factorsThrough_conductor ((DirichletCharacter.changeLevel hr) ψ)
    have er : DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ) ∣ r :=
      h1.trans (DirichletCharacter.conductor_dvd_level ψ)
    refine DirichletCharacter.conductor_dvd_of_mem_conductorSet _ ?_
    refine ⟨er, χ₀, ?_⟩
    apply DirichletCharacter.changeLevel_injective hr
    conv_lhs => rw [hχ₀]
    exact DirichletCharacter.changeLevel_trans χ₀ er hr
  refine ⟨Nat.dvd_antisymm h1 h2, ?_⟩
  exact orderOf_injective (DirichletCharacter.changeLevel hr)
    (DirichletCharacter.changeLevel_injective hr) ψ
