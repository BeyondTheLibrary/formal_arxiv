import Mathlib

theorem SublemmaCubicCharacterOfConductorR :
    ∀ (r : ℕ+), (r : ℕ).Prime → (r : ℕ) % 3 = 1 →
      ∃ ψ : DirichletCharacter ℂ (r : ℕ),
        orderOf ψ = 3 ∧ DirichletCharacter.conductor ψ = (r : ℕ) := by
  intro r hp hm
  haveI : Fact (Nat.Prime (r : ℕ)) := ⟨hp⟩
  have hcard : Fintype.card (ZMod (r : ℕ)) = (r : ℕ) := ZMod.card (r : ℕ)
  have h3dvd : (3 : ℕ) ∣ Fintype.card (ZMod (r : ℕ)) - 1 := by
    rw [hcard]; omega
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  obtain ⟨ψ, hψ⟩ := MulChar.exists_mulChar_orderOf (ZMod (r : ℕ)) h3dvd hζ
  refine ⟨ψ, hψ, ?_⟩
  have hdvd : DirichletCharacter.conductor ψ ∣ (r : ℕ) :=
    DirichletCharacter.conductor_dvd_level ψ
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hr
  · exfalso
    have hft : DirichletCharacter.FactorsThrough ψ 1 :=
      h1 ▸ DirichletCharacter.factorsThrough_conductor ψ
    have hψ1 : ψ = 1 := (DirichletCharacter.factorsThrough_one_iff ψ).mp hft
    rw [hψ1] at hψ
    simp [orderOf_one] at hψ
  · exact hr
