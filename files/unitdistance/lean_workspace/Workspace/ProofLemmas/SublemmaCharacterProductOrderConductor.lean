import Mathlib
import Workspace.ProofLemmas.ConductorMultiplicativeFamily

open scoped NumberField

/-- For a family of cubic characters `χ_i` (order 3) of common modulus `D` with pairwise
coprime conductors `r_i`, whose product of conductors is `D` with `1 < D`, the product
`χ = ∏ χ_i` has conductor `D` and order `3`. -/
theorem SublemmaCharacterProductOrderConductor
    (ℓ : ℕ) (D : ℕ) (r : Fin ℓ → ℕ+)
    (χ : Fin ℓ → DirichletCharacter ℂ D)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (r i : ℕ) (r j : ℕ))
    (hcond : ∀ i, DirichletCharacter.conductor (χ i) = (r i : ℕ))
    (hord : ∀ i, orderOf (χ i) = 3)
    (hD : D = ∏ i, (r i : ℕ))
    (hD1 : 1 < D) :
    DirichletCharacter.conductor (∏ i, χ i) = D ∧ orderOf (∏ i, χ i) = 3 := by
  haveI : NeZero D := ⟨by omega⟩
  -- conductor of the product equals D
  have hcondprod : DirichletCharacter.conductor (∏ i, χ i) = D := by
    have hcopcond : ∀ i j, i ≠ j →
        Nat.Coprime (DirichletCharacter.conductor (χ i))
          (DirichletCharacter.conductor (χ j)) := by
      intro i j hij
      rw [hcond i, hcond j]
      exact hcop i j hij
    rw [ConductorMultiplicativeFamily D ℓ χ hcopcond]
    have hprod : ∏ i, DirichletCharacter.conductor (χ i) = ∏ i, (r i : ℕ) :=
      Finset.prod_congr rfl (fun i _ => hcond i)
    rw [hprod]
    exact hD.symm
  refine ⟨hcondprod, ?_⟩
  -- the product is a cube, hence order divides 3
  have hcube : (∏ i, χ i) ^ 3 = 1 := by
    rw [← Finset.prod_pow]
    have : ∀ i ∈ Finset.univ, (χ i) ^ 3 = 1 := by
      intro i _
      have := pow_orderOf_eq_one (χ i)
      rwa [hord i] at this
    rw [Finset.prod_congr rfl this]
    exact Finset.prod_const_one
  have hdvd : orderOf (∏ i, χ i) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  -- the product is nontrivial since its conductor is D > 1
  have hne : (∏ i, χ i) ≠ 1 := by
    intro h
    rw [h, DirichletCharacter.conductor_one] at hcondprod
    omega
  have hordne : orderOf (∏ i, χ i) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    exact hne
  rcases (Nat.prime_three).eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact absurd h1 hordne
  · exact h3
