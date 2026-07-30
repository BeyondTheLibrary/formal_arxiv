-- Cited from: Neukirch, Algebraic Number Theory (Neu99), Ch. VII §13 (paper Definition A.7):
-- at a prime unramified in a finite Galois extension, the Frobenius class is trivial iff the prime
-- splits completely. This file proves the direction (trivial Frobenius ⟹ complete splitting): the
-- trivial Frobenius forces `y = y^q` on the residue field `κ(P)`, a finite-field root-count gives
-- inertia degree `1`, unramifiedness gives ramification index `1`, and the fundamental identity
-- `∑ e·f = [M:F]` gives the prime count.
-- Paper label: Definition A.7 [Neu99, Ch. VII §13]
-- NL statement: Let F, M be number fields with [Algebra F M], IsGalois F M and FiniteDimensional F M,
-- and let v : Ideal(𝒪_F) be a nonzero prime unramified in M (every P ∈ Ideal.primesOver v (𝒪_M) has
-- ramificationIdx v P = 1; supplied by UnramifiedAtFinitePrimes F M). Suppose some Frobenius element of
-- v is trivial: there is σ : M ≃ₐ[F] M with IsFrobeniusAt σ v and σ = 1. Then v splits completely in
-- M/F: SplitsCompletely (F := F) (M := M) v.
import Mathlib
import Workspace.Types.FrobeniusSplitting
import Workspace.Types.SplittingRamification

open scoped NumberField

open Workspace.Types.FrobeniusSplitting Workspace.Types.SplittingRamification

attribute [local instance] Ideal.Quotient.field

set_option maxHeartbeats 1600000

/-- In a finite integral domain `L` (a finite field), if every element satisfies `y ^ q = y` and
`2 ≤ q`, then `Nat.card L ≤ q` (the polynomial `X^q - X` has at most `q` roots). -/
theorem card_le_of_forall_pow_eq_self (L : Type*) [CommRing L] [IsDomain L] [Finite L]
    (q : ℕ) (hq : 2 ≤ q) (h : ∀ y : L, y ^ q = y) : Nat.card L ≤ q := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card]
  set p : Polynomial L := Polynomial.X ^ q - Polynomial.X with hp
  have hcoeff : p.coeff q = 1 := by
    have h1 : (Polynomial.X ^ q : Polynomial L).coeff q = 1 := by
      rw [Polynomial.coeff_X_pow]; simp
    have h2 : (Polynomial.X : Polynomial L).coeff q = 0 := by
      rw [Polynomial.coeff_X]; simp [Nat.ne_of_lt (by omega : 1 < q)]
    rw [hp, Polynomial.coeff_sub, h1, h2, sub_zero]
  have hpne : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  have hdeg : p.natDegree ≤ q := by
    calc p.natDegree ≤ max (Polynomial.X ^ q : Polynomial L).natDegree
              (Polynomial.X : Polynomial L).natDegree := Polynomial.natDegree_sub_le _ _
      _ = max q 1 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      _ = q := by omega
  have hsub : (Finset.univ : Finset L) ⊆ p.roots.toFinset := by
    intro y _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne]
    show p.eval y = 0
    rw [hp]; simp [h y]
  calc Fintype.card L = (Finset.univ : Finset L).card := (Finset.card_univ).symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ q := hdeg

/-- **Definition A.7 [Neu99, Ch. VII §13] — trivial Frobenius ⟹ complete splitting.**

For a finite Galois extension `M/F` of number fields and a nonzero prime `v` of `𝓞 F` that is
unramified in `M`, if some Frobenius element of `v` is the identity automorphism, then `v` splits
completely in `M/F`. This is the converse direction of Def A.7 (at an unramified prime, the
Frobenius class is trivial iff the prime splits completely). -/
theorem SublemmaTrivialFrobSplits :
    ∀ (F M : Type*) [Field F] [NumberField F] [Field M] [NumberField M]
      [Algebra F M] [IsGalois F M] [FiniteDimensional F M]
      (v : Ideal (𝓞 F)), v ≠ ⊥ → v.IsPrime →
      UnramifiedAtFinitePrimes F M →
      (∃ σ : M ≃ₐ[F] M, IsFrobeniusAt σ v ∧ σ = 1) →
      SplitsCompletely (F := F) (M := M) v := by
  intro F M _ _ _ _ _ _ _ v hv hvp hunram hfrob
  classical
  haveI : v.IsMaximal := hvp.isMaximal hv
  obtain ⟨σ, hFrob, hσ1⟩ := hfrob
  subst hσ1
  obtain ⟨P, hP_prime, hP_lies, hFrobP⟩ := hFrob
  haveI : P.IsPrime := hP_prime
  haveI : P.LiesOver v := hP_lies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv P
  haveI : P.IsMaximal := hP_prime.isMaximal hPne
  have hPunder : P.under (𝓞 F) = v := (Ideal.over_def P v).symm
  -- q = size of residue field of v
  set q : ℕ := Nat.card (𝓞 F ⧸ v) with hq_def
  -- φ = 1 acts as identity on 𝓞 M
  have hφx : ∀ x : 𝓞 M,
      (galRestrict (𝓞 F) F M (𝓞 M) (1 : M ≃ₐ[F] M)).toAlgHom x = x := by
    intro x
    rw [map_one]
    rfl
  -- trivial Frobenius ⇒ every residue class satisfies y^q = y
  have hmk : ∀ x : 𝓞 M, (Ideal.Quotient.mk P x) ^ q = Ideal.Quotient.mk P x := by
    intro x
    have key := hFrobP.mk_apply x
    rw [hφx x, hPunder] at key
    exact key.symm
  -- residue fields are finite fields
  have h2q : 2 ≤ q := by
    have : 1 < Nat.card (𝓞 F ⧸ v) := Finite.one_lt_card
    omega
  -- every element of κ(P) satisfies y^q = y
  have hpow : ∀ y : 𝓞 M ⧸ P, y ^ q = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hmk x
  have hcardP : Nat.card (𝓞 M ⧸ P) ≤ q :=
    card_le_of_forall_pow_eq_self (𝓞 M ⧸ P) q h2q hpow
  -- inertia degree of P is 1
  have hf1 : Ideal.inertiaDeg v P = 1 := by
    haveI : Module.Finite (𝓞 F ⧸ v) (𝓞 M ⧸ P) := Module.Finite.of_finite
    have hcardpow : Nat.card (𝓞 M ⧸ P)
        = Nat.card (𝓞 F ⧸ v) ^ Module.finrank (𝓞 F ⧸ v) (𝓞 M ⧸ P) :=
      Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v) (V := 𝓞 M ⧸ P)
    rw [← hq_def, ← Ideal.inertiaDeg_algebraMap v P] at hcardpow
    set f := Ideal.inertiaDeg v P with hf_def
    -- hcardpow : Nat.card (𝓞 M ⧸ P) = q ^ f
    have hgt : 1 < Nat.card (𝓞 M ⧸ P) := Finite.one_lt_card
    have hfpos : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h
      · rw [h0, pow_zero] at hcardpow; omega
      · omega
    have hle : q ^ f ≤ q ^ 1 := by rw [pow_one, ← hcardpow]; exact hcardP
    have hfle := (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp hle
    omega
  -- extend e = 1, f = 1 to all primes over v
  have hall : ∀ P' ∈ Ideal.primesOver v (𝓞 M),
      Ideal.ramificationIdx v P' = 1 ∧ Ideal.inertiaDeg v P' = 1 := by
    intro P' hP'
    obtain ⟨hP'_prime, hP'_lies⟩ := hP'
    haveI : P'.IsPrime := hP'_prime
    haveI : P'.LiesOver v := hP'_lies
    refine ⟨hunram v hv hvp P' ⟨hP'_prime, hP'_lies⟩, ?_⟩
    rw [Ideal.inertiaDeg_eq_of_isGaloisGroup v P' P (M ≃ₐ[F] M), hf1]
  -- count: ncard = finrank F M via the fundamental identity
  have hcount : (Ideal.primesOver v (𝓞 M)).ncard = Module.finrank F M := by
    rw [← IsDedekindDomain.coe_primesOverFinset hv (𝓞 M), Set.ncard_coe_finset,
      ← Ideal.sum_ramification_inertia (𝓞 M) F M hv, Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro P' hP'
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hv (𝓞 M)] at hP'
    obtain ⟨he, hfe⟩ := hall P' hP'
    rw [he, hfe, mul_one]
  exact ⟨hcount, hall⟩
