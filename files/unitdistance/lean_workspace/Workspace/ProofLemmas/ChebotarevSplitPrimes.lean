import Mathlib
import Workspace.Types.SplittingRamification

/-!
# Infinitely many rational primes split completely in a finite Galois extension of `ℚ`

Proof that infinitely many rational primes split completely in a finite Galois extension `N/ℚ`
(the input the paper draws from Chebotarev density), by an elementary Schur/Kummer–Dedekind argument.

The full Chebotarev density theorem is not in Mathlib.  But the statement
actually used by the paper is much weaker — *there exist `t` distinct primes outside a finite set `T`
splitting completely in `N`* — and that has a classical elementary proof, formalised here:

* `exists_prime_gt_dvd_eval` (**Schur**): a nonconstant `f ∈ ℤ[X]` has values divisible by
  arbitrarily large primes.  Proof: with `c = f(0) ≠ 0` and `M = c·n₀!`, every value `f(M y)` equals
  `c·(1 + n₀!·k)`; a prime factor of the second factor is coprime to `n₀!`, hence `> n₀`.
* `exists_int_mul_mem_adjoin` / `exponent_ne_zero`: for a primitive integral generator `θ` of `N`,
  the Kummer–Dedekind exponent of `θ` is nonzero (clear denominators using
  `Algebra.discr_mul_isIntegral_mem_adjoin`).
* `ramificationIdx_one_of_not_dvd_discr`: a prime not dividing `|D_N|` is unramified (via
  `NumberField.absNorm_differentIdeal` and `not_dvd_differentIdeal_iff`).
* `splitsCompletelyRat_of_root`: if `minpoly ℤ θ` has a root mod `p` and `p` divides neither the
  exponent nor the discriminant, then `p` splits completely.  Kummer–Dedekind
  (`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) turns the root into a prime of residue
  degree `1`; since `N/ℚ` is Galois *all* residue degrees are then `1`
  (`Ideal.inertiaDeg_eq_of_isGaloisGroup`), and the fundamental identity gives exactly `[N:ℚ]`
  primes above `p`.
* `infinite_splitsCompletelyRat` and `chebotarevManySplitPrimes` assemble these.
-/

open scoped NumberField
open Polynomial Workspace.Types.SplittingRamification

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Workspace.ProofLemmas.ChebotarevSplitPrimes

/-- The set of integers at which `f` takes one of finitely many prescribed nonzero-polynomial
values is finite: here, the `x` with `f.eval x ∈ ({0, c, -c} : Set ℤ)`. -/
private theorem finite_bad (f : ℤ[X]) (hf : 0 < f.natDegree) (c : ℤ) :
    {x : ℤ | f.eval x = 0 ∨ f.eval x = c ∨ f.eval x = -c}.Finite := by
  have hne : ∀ d : ℤ, (f - C d) ≠ 0 := by
    intro d hd
    have : f = C d := by linear_combination (norm := ring_nf) hd
    rw [this] at hf
    simp at hf
  have h : ∀ d : ℤ, {x : ℤ | f.eval x = d}.Finite := by
    intro d
    have : {x : ℤ | f.eval x = d} ⊆ {x : ℤ | (f - C d).IsRoot x} := by
      intro x hx
      simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, eval_C] at *
      omega
    exact Set.Finite.subset (Polynomial.finite_setOf_isRoot (hne d)) this
  have : {x : ℤ | f.eval x = 0 ∨ f.eval x = c ∨ f.eval x = -c}
      = {x : ℤ | f.eval x = 0} ∪ ({x : ℤ | f.eval x = c} ∪ {x : ℤ | f.eval x = -c}) := by
    ext x; simp [Set.mem_union]
  rw [this]
  exact (h 0).union ((h c).union (h (-c)))

/-- **Schur's theorem.**  For a nonconstant integer polynomial `f` and any bound `n₀`, there is a
prime `p > n₀` dividing some value of `f`. -/
theorem exists_prime_gt_dvd_eval (f : ℤ[X]) (hf : 0 < f.natDegree) (n₀ : ℕ) :
    ∃ p : ℕ, p.Prime ∧ n₀ < p ∧ ∃ m : ℤ, (p : ℤ) ∣ f.eval m := by
  classical
  set c : ℤ := f.eval 0 with hc
  by_cases hc0 : c = 0
  · obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (n₀ + 1)
    exact ⟨p, hp, by omega, 0, by rw [← hc, hc0]; exact dvd_zero _⟩
  -- `M = c * n₀!`; every value `f (M * y)` is `c * (1 + n₀! * k)`
  set N : ℤ := (Nat.factorial n₀ : ℤ) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact_mod_cast Nat.factorial_ne_zero n₀
  set M : ℤ := c * N with hM
  have hM0 : M ≠ 0 := mul_ne_zero hc0 hN0
  -- choose `y` avoiding the finitely many bad values
  have hbad := finite_bad f hf c
  have hinj : Function.Injective (fun y : ℤ => M * y) := fun a b h => by
    simpa [hM0] using mul_left_cancel₀ hM0 h
  have hfiny : {y : ℤ | f.eval (M * y) = 0 ∨ f.eval (M * y) = c ∨ f.eval (M * y) = -c}.Finite := by
    have : {y : ℤ | f.eval (M * y) = 0 ∨ f.eval (M * y) = c ∨ f.eval (M * y) = -c}
        ⊆ (fun y : ℤ => M * y) ⁻¹' {x : ℤ | f.eval x = 0 ∨ f.eval x = c ∨ f.eval x = -c} := by
      intro y hy; exact hy
    exact Set.Finite.subset (Set.Finite.preimage hinj.injOn hbad) this
  obtain ⟨y, hy⟩ : ∃ y : ℤ, ¬ (f.eval (M * y) = 0 ∨ f.eval (M * y) = c ∨ f.eval (M * y) = -c) := by
    by_contra hcon
    push_neg at hcon
    exact Set.infinite_univ (α := ℤ) (Set.Finite.subset hfiny (fun y _ => hcon y))
  push_neg at hy
  obtain ⟨hy0, hyc, hync⟩ := hy
  -- `M ∣ f (M*y) - c`
  set D : ℤ := f.eval (M * y) with hD
  have hdvd : M ∣ D - c := by
    have := sub_dvd_eval_sub (M * y) 0 f
    simp only [sub_zero] at this
    exact dvd_trans (Dvd.intro y rfl) this
  obtain ⟨k, hk⟩ := hdvd
  set B : ℤ := 1 + N * k with hB
  have hDB : D = c * B := by
    rw [hB, hD]
    have : D - c = c * N * k := by rw [hk, hM]
    linarith [this]
  -- `|B| ≥ 2`
  have hB2 : B.natAbs ≠ 1 ∧ B.natAbs ≠ 0 := by
    constructor
    · intro h
      rcases Int.natAbs_eq_iff.mp h with h1 | h1
      · exact hyc (by rw [hDB, h1]; ring)
      · exact hync (by rw [hDB, h1]; ring)
    · intro h
      have : B = 0 := by omega
      exact hy0 (by rw [hDB, this, mul_zero])
  set p : ℕ := B.natAbs.minFac with hp
  have hpprime : p.Prime := Nat.minFac_prime hB2.1
  have hpB : (p : ℤ) ∣ B :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd _)) (Int.natAbs_dvd.mpr dvd_rfl)
  refine ⟨p, hpprime, ?_, M * y, ?_⟩
  · -- `p ∤ n₀!`, hence `p > n₀`
    by_contra hple
    push_neg at hple
    have hdvdfac : (p : ℤ) ∣ N := by
      rw [hN]
      exact_mod_cast Nat.dvd_factorial hpprime.pos hple
    have : (p : ℤ) ∣ 1 := by
      have h1 : (1 : ℤ) = B - N * k := by rw [hB]; ring
      rw [h1]
      exact dvd_sub hpB (Dvd.dvd.mul_right hdvdfac k)
    have := Int.le_of_dvd one_pos this
    have := hpprime.two_le
    omega
  · rw [← hD, hDB]
    exact Dvd.dvd.mul_left hpB c

/-- For a primitive integral generator `θ` of a number field, some nonzero integer multiplies all of
`𝓞 N` into `ℤ[θ]` (clear denominators via the discriminant of the power basis). -/
theorem exists_int_mul_mem_adjoin (N : Type*) [Field N] [NumberField N] (θ : 𝓞 N)
    (hθ : Algebra.adjoin ℚ ({(θ : N)} : Set N) = ⊤) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ z : 𝓞 N, (d : 𝓞 N) * z ∈ Algebra.adjoin ℤ ({θ} : Set (𝓞 N)) := by
  have hint : IsIntegral ℚ (θ : N) := IsIntegral.of_finite ℚ _
  -- the power basis generated by `θ`
  let pb0 : PowerBasis ℚ ↥(Algebra.adjoin ℚ ({(θ : N)} : Set N)) := Algebra.adjoin.powerBasis hint
  let e : ↥(Algebra.adjoin ℚ ({(θ : N)} : Set N)) ≃ₐ[ℚ] N :=
    (Subalgebra.equivOfEq _ ⊤ hθ).trans Subalgebra.topEquiv
  let pb : PowerBasis ℚ N := pb0.map e
  have hgen : pb.gen = (θ : N) := by
    show e pb0.gen = (θ : N)
    rw [Algebra.adjoin.powerBasis_gen]
    rfl
  have hbint : ∀ i, IsIntegral ℤ (pb.basis i) := by
    intro i
    rw [pb.basis_eq_pow, hgen]
    exact (θ.isIntegral_coe).pow _
  have hdQint : IsIntegral ℤ (Algebra.discr ℚ pb.basis) := Algebra.discr_isIntegral ℚ hbint
  obtain ⟨d, hdeq⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdQint
  have hdQne : Algebra.discr ℚ pb.basis ≠ 0 := Algebra.discr_not_zero_of_basis ℚ pb.basis
  have hd0 : d ≠ 0 := by
    intro h
    apply hdQne
    rw [← hdeq, h]
    simp
  refine ⟨d, hd0, ?_⟩
  intro z
  have hz : IsIntegral ℤ (z : N) := z.isIntegral_coe
  have hmem : Algebra.discr ℚ pb.basis • (z : N) ∈ Algebra.adjoin ℤ ({pb.gen} : Set N) :=
    Algebra.discr_mul_isIntegral_mem_adjoin ℚ (hgen ▸ (θ.isIntegral_coe)) hz
  rw [hgen] at hmem
  -- rewrite the ℚ-scalar action as multiplication by the integer `d`
  have hsmul : Algebra.discr ℚ pb.basis • (z : N) = ((d : 𝓞 N) * z : 𝓞 N) := by
    rw [← hdeq, Algebra.smul_def]
    push_cast
    simp [algebraMap_int_eq]
  rw [hsmul] at hmem
  -- descend the membership from `N` to `𝓞 N`
  have hmapadj : Algebra.adjoin ℤ ({(θ : N)} : Set N)
      = (Algebra.adjoin ℤ ({θ} : Set (𝓞 N))).map (IsScalarTower.toAlgHom ℤ (𝓞 N) N) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp
  rw [hmapadj] at hmem
  obtain ⟨w, hw, hwz⟩ := hmem
  have : w = (d : 𝓞 N) * z := by
    apply NumberField.RingOfIntegers.coe_injective
    exact hwz
  rwa [this] at hw


/-- The Kummer–Dedekind exponent of a primitive integral generator is nonzero. -/
theorem exponent_ne_zero (N : Type*) [Field N] [NumberField N] (θ : 𝓞 N)
    (hθ : Algebra.adjoin ℚ ({(θ : N)} : Set N) = ⊤) :
    RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨d, hd0, hd⟩ := exists_int_mul_mem_adjoin N θ hθ
  have hmem : (d : 𝓞 N) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    exact hd
  have hmem' : d ∈ Ideal.under ℤ (conductor ℤ θ) := by
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hmem
  intro hzero
  rw [RingOfIntegers.exponent, Ideal.absNorm_eq_zero_iff] at hzero
  rw [hzero, Ideal.mem_bot] at hmem'
  exact hd0 hmem'

/-- A number field has an integral primitive element. -/
theorem exists_integral_primitive_element (N : Type*) [Field N] [NumberField N] :
    ∃ θ : 𝓞 N, Algebra.adjoin ℚ ({(θ : N)} : Set N) = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ N
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.IsAlgebraic ℤ N := Algebra.IsAlgebraic.trans (R := ℤ) (S := ℚ) (A := N)
  obtain ⟨y, hy0, hyint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) α).exists_integral_multiple
  refine ⟨⟨y • α, hyint⟩, ?_⟩
  show Algebra.adjoin ℚ ({y • α} : Set N) = ⊤
  rw [← Int.cast_smul_eq_zsmul ℚ y α]
  have hy0' : (y : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hy0
  have hsmul : IntermediateField.adjoin ℚ ({(y : ℚ) • α} : Set N)
      = IntermediateField.adjoin ℚ ({α} : Set N) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have h1 : α ∈ IntermediateField.adjoin ℚ ({α} : Set N) :=
        IntermediateField.mem_adjoin_simple_self ℚ α
      show (y : ℚ) • α ∈ IntermediateField.adjoin ℚ ({α} : Set N)
      rw [Algebra.smul_def]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) h1
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have h1 : (y : ℚ) • α ∈ IntermediateField.adjoin ℚ ({(y : ℚ) • α} : Set N) :=
        IntermediateField.mem_adjoin_simple_self ℚ _
      have h2 : (algebraMap ℚ N ((y : ℚ)⁻¹)) * ((y : ℚ) • α)
          ∈ IntermediateField.adjoin ℚ ({(y : ℚ) • α} : Set N) :=
        mul_mem (IntermediateField.algebraMap_mem _ _) h1
      have h3 : (algebraMap ℚ N ((y : ℚ)⁻¹)) * ((y : ℚ) • α) = α := by
        rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hy0', one_smul]
      rwa [h3] at h2
  have hint2 : IsIntegral ℚ ((y : ℚ) • α) := IsIntegral.of_finite ℚ _
  have hEq := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hint2.isAlgebraic (R := ℚ))
  rw [← hEq, hsmul, hα]
  rfl

/-- A rational prime not dividing the absolute discriminant is unramified. -/
theorem ramificationIdx_one_of_not_dvd_discr (N : Type*) [Field N] [NumberField N]
    (p : ℕ) (hp : p.Prime) (hdiscr : ¬ p ∣ (NumberField.discr N).natAbs)
    (P : Ideal (𝓞 N)) (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 N)) :
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1 := by
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPlies
  have hspan : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan P
  -- if `P` divided the different ideal, `p` would divide the discriminant
  have hnotdvd : ¬ P ∣ differentIdeal ℤ (𝓞 N) := by
    intro hdvd
    have h1 : Ideal.absNorm P ∣ Ideal.absNorm (differentIdeal ℤ (𝓞 N)) := map_dvd _ hdvd
    rw [NumberField.absNorm_differentIdeal N] at h1
    refine hdiscr (dvd_trans ?_ h1)
    -- `p ∣ absNorm P` because `absNorm P ∈ P` and `P ∩ ℤ = pℤ`
    have h2 : ((Ideal.absNorm P : ℤ) : 𝓞 N) ∈ P := by
      have := Ideal.absNorm_mem P
      exact_mod_cast this
    have h3 : (Ideal.absNorm P : ℤ) ∈ Ideal.under ℤ P := by
      rw [Ideal.under, Ideal.mem_comap]
      simpa using h2
    rw [← hPlies.over, Ideal.mem_span_singleton] at h3
    exact_mod_cast h3
  haveI : Algebra.IsUnramifiedAt ℤ P := (not_dvd_differentIdeal_iff).mp hnotdvd
  rw [hPlies.over]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (S := 𝓞 N) (p := P) hPne

open NumberField RingOfIntegers NumberField.Ideal in
/-- If the minimal polynomial of a primitive integral generator has a root mod `p`, and `p` divides
neither the Kummer–Dedekind exponent nor the discriminant, then `p` splits completely. -/
theorem splitsCompletelyRat_of_root (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (θ : 𝓞 N) (p : ℕ) (hpprime : p.Prime)
    (hexp : ¬ p ∣ RingOfIntegers.exponent θ)
    (hdiscr : ¬ p ∣ (NumberField.discr N).natAbs)
    (m : ℤ) (hm : (p : ℤ) ∣ (minpoly ℤ θ).eval m) :
    SplitsCompletelyRat p N := by
  haveI : Fact p.Prime := ⟨hpprime⟩
  classical
  letI act : MulSemiringAction (N ≃ₐ[ℚ] N) (𝓞 N) :=
    IsIntegralClosure.MulSemiringAction ℤ ℚ N (𝓞 N)
  haveI : IsGaloisGroup (N ≃ₐ[ℚ] N) ℤ (𝓞 N) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ N
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hspan : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simp [hpprime.ne_zero]
  set f : ℤ[X] := minpoly ℤ θ with hf
  have hfmonic : f.Monic := minpoly.monic θ.isIntegral
  have hfbar : f.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    (hfmonic.map (Int.castRingHom (ZMod p))).ne_zero
  set a : ZMod p := (m : ZMod p) with ha
  set Q : (ZMod p)[X] := X - C a with hQdef
  have hroot : (f.map (Int.castRingHom (ZMod p))).eval a = 0 := by
    rw [ha, eval_map]
    have hcast : ((Int.castRingHom (ZMod p)) m) = (m : ZMod p) := rfl
    rw [← hcast, eval₂_hom]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hm
  have hQ : Q ∈ monicFactorsMod θ p := by
    rw [monicFactorsMod, Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hfbar]
    exact ⟨irreducible_X_sub_C a, monic_X_sub_C a, (dvd_iff_isRoot).mpr hroot⟩
  set P₀ := (primesOverSpanEquivMonicFactorsMod hexp).symm ⟨Q, hQ⟩ with hP₀
  have hP₀mem : (P₀ : Ideal (𝓞 N)) ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 N) := P₀.2
  have hinertia₀ : Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) (P₀ : Ideal (𝓞 N)) = 1 := by
    rw [hP₀, inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp hQ, hQdef]
    simp
  have hall : ∀ P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 N),
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = 1 := by
    intro P hP
    refine ⟨ramificationIdx_one_of_not_dvd_discr N p hpprime hdiscr P hP, ?_⟩
    obtain ⟨hPprime, hPlies⟩ := hP
    haveI : P.IsPrime := hPprime
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPlies
    obtain ⟨hP₀prime, hP₀lies⟩ := hP₀mem
    haveI : (P₀ : Ideal (𝓞 N)).IsPrime := hP₀prime
    haveI : (P₀ : Ideal (𝓞 N)).LiesOver (Ideal.span {(p : ℤ)}) := hP₀lies
    rw [← hinertia₀]
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P
      (P₀ : Ideal (𝓞 N)) (N ≃ₐ[ℚ] N)
  haveI : (P₀ : Ideal (𝓞 N)).IsPrime := hP₀mem.1
  haveI : (P₀ : Ideal (𝓞 N)).LiesOver (Ideal.span {(p : ℤ)}) := hP₀mem.2
  have hridx : Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 N) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)})
      (P₀ : Ideal (𝓞 N)) (N ≃ₐ[ℚ] N)]
    exact (hall _ hP₀mem).1
  have hidxin : Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 N) = 1 := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)})
      (P₀ : Ideal (𝓞 N)) (N ≃ₐ[ℚ] N)]
    exact hinertia₀
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hspan (𝓞 N)
    (N ≃ₐ[ℚ] N)
  rw [hridx, hidxin, one_mul, mul_one] at hfund
  refine ⟨hpprime, ?_, fun P hP => hall P hP⟩
  rw [hfund]
  exact IsGalois.card_aut_eq_finrank ℚ N

section Assembly

variable (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]

/-- There are infinitely many rational primes splitting completely in a finite Galois `N/ℚ`. -/
theorem infinite_splitsCompletelyRat :
    {p : ℕ | p.Prime ∧ SplitsCompletelyRat p N}.Infinite := by
  classical
  obtain ⟨θ, hθ⟩ := exists_integral_primitive_element N
  have hexp0 : RingOfIntegers.exponent θ ≠ 0 := exponent_ne_zero N θ hθ
  have hdiscr0 : (NumberField.discr N).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero N)
  have hdeg : 0 < (minpoly ℤ θ).natDegree := minpoly.natDegree_pos θ.isIntegral
  rw [← Nat.frequently_atTop_iff_infinite]
  refine Filter.frequently_atTop.2 fun n => ?_
  obtain ⟨p, hpprime, hgt, m, hm⟩ :=
    exists_prime_gt_dvd_eval (minpoly ℤ θ) hdeg
      (max n (max (RingOfIntegers.exponent θ) (NumberField.discr N).natAbs))
  have h1 : n ≤ p := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hgt)
  have h2 : ¬ p ∣ RingOfIntegers.exponent θ := by
    intro hdvd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hexp0) hdvd
    have : RingOfIntegers.exponent θ < p :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hgt
    omega
  have h3 : ¬ p ∣ (NumberField.discr N).natAbs := by
    intro hdvd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hdiscr0) hdvd
    have : (NumberField.discr N).natAbs < p :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hgt
    omega
  exact ⟨p, h1, hpprime, splitsCompletelyRat_of_root N θ p hpprime h2 h3 m hm⟩

/-- **Chebotarev, weak form used by the paper.**  For a finite Galois `N/ℚ`, a finite excluded set
`T` of rational primes and any `t`, there are `t` distinct rational primes outside `T` splitting
completely in `N`. -/
theorem chebotarevManySplitPrimes (T : Finset ℕ) (t : ℕ) :
    ∃ q : Fin t → ℕ, Function.Injective q ∧
      ∀ b, (q b).Prime ∧ q b ∉ T ∧ SplitsCompletelyRat (q b) N := by
  classical
  have hinf : ({p : ℕ | p.Prime ∧ SplitsCompletelyRat p N} \ (T : Set ℕ)).Infinite :=
    (infinite_splitsCompletelyRat N).diff T.finite_toSet
  obtain ⟨u, husub, hucard⟩ := hinf.exists_subset_card_eq t
  refine ⟨fun i => ((u.orderIsoOfFin hucard i : ℕ)), ?_, ?_⟩
  · intro i j hij
    exact (u.orderIsoOfFin hucard).injective (Subtype.ext hij)
  · intro b
    have hmem : ((u.orderIsoOfFin hucard b : ℕ)) ∈ ({p : ℕ | p.Prime ∧ SplitsCompletelyRat p N}
        \ (T : Set ℕ)) := husub (u.orderIsoOfFin hucard b).2
    exact ⟨hmem.1.1, fun hcon => hmem.2 hcon, hmem.1.2⟩

end Assembly

end Workspace.ProofLemmas.ChebotarevSplitPrimes
