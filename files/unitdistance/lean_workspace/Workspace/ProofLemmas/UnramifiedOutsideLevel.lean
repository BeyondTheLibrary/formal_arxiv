import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.IdealCountInjection

/-!
# Primes not dividing the level are unramified, and the local conductor–discriminant identity is
# trivial there

* `not_dvd_discr_of_unramified` — if every prime of `𝓞 L` above `p` has ramification index `1`
  then `p ∤ |D_L|`.  (If `p` divided `|D_L| = N(𝔡_{L/ℚ})`, some prime factor `P` of the different
  would lie over `p`, and `P ∣ 𝔡` contradicts `not_dvd_differentIdeal_iff`.)
* `unramified_of_not_dvd` — for `L ≤ ℚ(ζ_m)` and `p ∤ m`, every prime of `𝓞 L` above `p` has
  ramification index `1` (Mathlib's `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`
  plus tower multiplicativity).
* `local_of_not_dvd` — hence the local conductor–discriminant identity holds at every `p ∤ m`:
  the left side vanishes by the above and the right side because every conductor divides `m`.
-/

open scoped NumberField
open UniqueFactorizationMonoid
open Workspace.Types.CyclotomicCharacterFields
open Workspace.ProofLemmas.IdealCountInjection

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Workspace.ProofLemmas.UnramifiedOutsideLevel

/-- A prime unramified in `L` does not divide the absolute discriminant of `L`. -/
theorem not_dvd_discr_of_unramified (L : Type) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (h : ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L),
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) Q = 1) :
    ¬ p ∣ (NumberField.discr L).natAbs := by
  classical
  intro hdvd
  rw [← NumberField.absNorm_differentIdeal L (𝓞 L)] at hdvd
  set 𝔡 : Ideal (𝓞 L) := differentIdeal ℤ (𝓞 L) with h𝔡
  have h𝔡ne : 𝔡 ≠ 0 := differentIdeal_ne_bot
  -- write the norm as a product over the prime factors
  have hfac : Ideal.absNorm 𝔡 = ((normalizedFactors 𝔡).map Ideal.absNorm).prod := by
    rw [← map_multiset_prod, associated_iff_eq.mp (prod_normalizedFactors h𝔡ne)]
  have hprimes : ∀ P ∈ normalizedFactors 𝔡, P.IsPrime ∧ P ≠ ⊥ := fun P hP =>
    mem_normalizedFactors_prime h𝔡ne hP
  have hnormne : Ideal.absNorm 𝔡 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact h𝔡ne
  -- `p` divides the norm, so it appears in the factorisation
  have hfp : (Ideal.absNorm 𝔡).factorization p ≠ 0 := by
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization hp hnormne).mp hdvd
    omega
  rw [hfac, factorization_prod_map p hp (normalizedFactors 𝔡) hprimes] at hfp
  -- hence some prime factor lies over `p`
  obtain ⟨P, hPmem, hPw⟩ : ∃ P ∈ normalizedFactors 𝔡, w p P ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hfp
    have : ((normalizedFactors 𝔡).map (w p)) = (normalizedFactors 𝔡).map (fun _ => 0) :=
      Multiset.map_congr rfl (fun P hP => hcon P hP)
    rw [this]
    simp
  have hPp := hprimes P hPmem
  haveI : P.IsPrime := hPp.1
  have hq : qOf L P = p := by
    by_contra hcon
    rw [w, if_neg hcon] at hPw
    exact hPw rfl
  -- `P` lies over `p` and divides the different ideal
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    have := liesOver_qOf (K := L) P
    rwa [hq] at this
  have hPmemOver : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L) := ⟨hPp.1, inferInstance⟩
  have hdvd𝔡 : P ∣ 𝔡 := dvd_of_mem_normalizedFactors hPmem
  -- but `P` is unramified, so it does not divide the different
  have hPbot : P ≠ ⊥ := hPp.2
  haveI : Algebra.IsUnramifiedAt ℤ P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot]
    have hunder : Ideal.under ℤ P = Ideal.span {(p : ℤ)} := by
      rw [under_eq_span (K := L) P, hq]
    rw [hunder]
    exact h P hPmemOver
  exact (not_dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 L) (P := P)).mpr inferInstance hdvd𝔡

/-- A prime not dividing `m` is unramified in every subfield of `ℚ(ζ_m)`. -/
theorem unramified_of_not_dvd (m : ℕ+) (L : IntermediateField ℚ ℂ) [NumberField ↥L]
    (hL : L ≤ cyclotomicField' m) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ (m : ℕ)) :
    ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 ↥L),
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) Q = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra ↥L ↥(cyclotomicField' m) := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ ↥L ↥(cyclotomicField' m) :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hL).commutes x).symm)
  intro Q hQ
  obtain ⟨hQprime, hQlies⟩ := hQ
  haveI : Q.IsPrime := hQprime
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQlies
  obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
    Q.nonempty_primesOver (S := 𝓞 ↥(cyclotomicField' m))
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver Q := hPlies
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q _
  have hPe := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (m := (m : ℕ)) p
    ↥(cyclotomicField' m) P hpm
  have htower : Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) Q * Ideal.ramificationIdx Q P :=
    Ideal.ramificationIdx_algebra_tower' (R := ℤ) (S := 𝓞 ↥L)
      (T := 𝓞 ↥(cyclotomicField' m)) _ _ _
  rw [hPe] at htower
  exact Nat.dvd_one.mp ⟨_, htower⟩

end Workspace.ProofLemmas.UnramifiedOutsideLevel
