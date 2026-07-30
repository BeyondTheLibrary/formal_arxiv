-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Ch. 3 (Thm 3.11);
-- J. Neukirch, Algebraic Number Theory, Springer, 1999, Ch. VI.
-- Paper label: Proposition A.11(ii)
-- NL statement: For a finite family of Dirichlet characters of the same (positive) modulus with pairwise
-- coprime conductors, the conductor of the product equals the product of the conductors.
--
-- Proved purely from Mathlib. The reverse divisibility direction is elementary: since (χ·ψ)·ψ⁻¹ = χ,
-- `conductor_mul_dvd_lcm_conductor` applied to (χ·ψ, ψ⁻¹) with `conductor_inv` and coprimality yields
-- `conductor χ ∣ conductor(χ·ψ)` (symmetrically for ψ).
--
-- The `[NeZero n]` hypothesis is necessary: at n = 0, k = 0 the statement fails, since
-- LHS = conductor(1 : DirichletCharacter ℂ 0) = 0 but RHS = (empty product) = 1. A "modulus" in the
-- paper is a positive integer, so `[NeZero n]` is the faithful reading.
import Mathlib

open scoped NumberField
open DirichletCharacter

set_option maxHeartbeats 800000

/-- Number theory helper: `a ∣ lcm b d` together with `Coprime a d` gives `a ∣ b`. -/
private theorem cmf_lcmHelper (a b d : ℕ) (hlcm : a ∣ Nat.lcm b d) (hcop : Nat.Coprime a d) :
    a ∣ b := by
  have h1 : Nat.lcm b d ∣ b * d := Dvd.intro_left (Nat.gcd b d) (Nat.gcd_mul_lcm b d)
  exact hcop.dvd_of_dvd_mul_right (hlcm.trans h1)

/-- Binary coprime-conductor multiplicativity. -/
private theorem cmf_binary (n : ℕ) [NeZero n] (χ ψ : DirichletCharacter ℂ n)
    (hcop : Nat.Coprime (conductor χ) (conductor ψ)) :
    conductor (χ * ψ) = conductor χ * conductor ψ := by
  apply Nat.dvd_antisymm
  · have h := conductor_mul_dvd_lcm_conductor χ ψ
    rwa [hcop.lcm_eq_mul] at h
  · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
    · have h1 := conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
      rw [conductor_inv] at h1
      have he : (χ * ψ) * ψ⁻¹ = χ := mul_inv_cancel_right χ ψ
      rw [he] at h1
      exact cmf_lcmHelper _ _ _ h1 hcop
    · have h1 := conductor_mul_dvd_lcm_conductor (χ * ψ) χ⁻¹
      rw [conductor_inv] at h1
      have he : (χ * ψ) * χ⁻¹ = ψ := by rw [mul_comm χ ψ]; exact mul_inv_cancel_right ψ χ
      rw [he] at h1
      exact cmf_lcmHelper _ _ _ h1 hcop.symm

/-- Family version over an arbitrary `Finset`, by induction. -/
private theorem cmf_family (n : ℕ) [NeZero n] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ n)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Nat.Coprime (conductor (χ i)) (conductor (χ j))) :
    conductor (∏ i ∈ s, χ i) = ∏ i ∈ s, conductor (χ i) := by
  induction s using Finset.induction with
  | empty => simp [conductor_one]
  | @insert a s ha ih =>
    have hsub : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Nat.Coprime (conductor (χ i)) (conductor (χ j)) :=
      fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have ihs := ih hsub
    have hcopprod : Nat.Coprime (conductor (χ a)) (∏ i ∈ s, conductor (χ i)) := by
      apply Nat.Coprime.prod_right
      intro i hi
      exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hcon => ha (hcon ▸ hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop' : Nat.Coprime (conductor (χ a)) (conductor (∏ i ∈ s, χ i)) := by
      rw [ihs]; exact hcopprod
    rw [cmf_binary n (χ a) (∏ i ∈ s, χ i) hcop', ihs]

theorem ConductorMultiplicativeFamily (n : ℕ) [NeZero n] (k : ℕ)
    (χ : Fin k → DirichletCharacter ℂ n)
    (h : ∀ i j, i ≠ j →
      Nat.Coprime (DirichletCharacter.conductor (χ i)) (DirichletCharacter.conductor (χ j))) :
    DirichletCharacter.conductor (∏ i, χ i)
      = ∏ i, DirichletCharacter.conductor (χ i) := by
  exact cmf_family n Finset.univ χ (fun i _ j _ hij => h i j hij)
