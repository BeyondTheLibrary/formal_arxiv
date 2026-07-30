import Mathlib

/-!
# Unramifiedness at finite primes and the absolute discriminant

Mathlib-only bridge lemmas for the finiteness of the Frattini quotient of `Gal(F^{ur,3}/F)` and
for unramifiedness of a compositum of everywhere-unramified extensions.

* `differentIdeal_eq_top_of_unramified` — every ramification index `1` ⟹ trivial relative different;
* `ramIdx_one_of_differentIdeal_eq_top` — the converse;
* `natAbs_discr_of_unramified` — hence `|D_L| = |D_K| ^ [L : K]` for an everywhere-unramified `L/K`;
* `unramified_iff_natAbs_discr` — the two are equivalent, which makes unramifiedness transportable
  along ring isomorphisms (since `NumberField.discr` is);
* `residue_isSeparable` — residue-field extensions of number fields are separable.
-/

open scoped NumberField

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.UnramifiedDiscriminant

/-- If every nonzero prime of `𝓞 L` is unramified over `𝓞 K`, the relative different ideal is
trivial. -/
theorem differentIdeal_eq_top_of_unramified (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (h : ∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
        ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  haveI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  by_contra hne
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  haveI : P.IsMaximal := hPmax
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPmax
    (fun hf => (NumberField.RingOfIntegers.not_isField L) hf)
  have hdvd : P ∣ differentIdeal (𝓞 K) (𝓞 L) := Ideal.dvd_iff_le.mpr hPle
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot]
    have hlo : P.LiesOver (P.under (𝓞 K)) := ⟨rfl⟩
    haveI := hlo
    haveI : (P.under (𝓞 K)).IsPrime := Ideal.IsPrime.under _ P
    have hpbot : P.under (𝓞 K) ≠ ⊥ := by
      intro hcon
      exact hPbot (by
        simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 K) (S := 𝓞 L) (I := P) hcon)
    exact h (P.under (𝓞 K)) hpbot inferInstance P ⟨inferInstance, hlo⟩
  exact (not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L) (P := P)).mpr hunram hdvd

/-- Trivial relative different implies every ramification index is `1`. -/
theorem ramIdx_one_of_differentIdeal_eq_top (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (hdiff : differentIdeal (𝓞 K) (𝓞 L) = ⊤) :
    ∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
      ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1 := by
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  intro p hp hpp P hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver p := hPlies
  have hnotdvd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    rw [hdiff, Ideal.dvd_iff_le]
    intro hle
    exact hPprime.ne_top (top_le_iff.mp hle)
  haveI : Algebra.IsUnramifiedAt (𝓞 K) P := (not_dvd_differentIdeal_iff).mp hnotdvd
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  rw [hPlies.over]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (S := 𝓞 L) (p := P) hPne

/-- **Discriminant of an everywhere-unramified extension.**  If `L/K` is unramified at every
finite prime then `|D_L| = |D_K| ^ [L : K]`. -/
theorem natAbs_discr_of_unramified (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (h : ∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
        ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1) :
    (NumberField.discr L).natAbs = (NumberField.discr K).natAbs ^ Module.finrank K L := by
  haveI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L),
    differentIdeal_eq_top_of_unramified K L h, Ideal.absNorm_top, one_mul]

/-- **Unramifiedness at finite primes is exactly the discriminant identity.** -/
theorem unramified_iff_natAbs_discr (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    (∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
        ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1) ↔
      (NumberField.discr L).natAbs = (NumberField.discr K).natAbs ^ Module.finrank K L := by
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  refine ⟨natAbs_discr_of_unramified K L, fun h => ?_⟩
  have htower :=
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  rw [h] at htower
  have hDK : (NumberField.discr K).natAbs ^ Module.finrank K L ≠ 0 :=
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hone : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) = 1 := by
    have hx : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) *
          (NumberField.discr K).natAbs ^ Module.finrank K L
        = 1 * (NumberField.discr K).natAbs ^ Module.finrank K L := by
      rw [one_mul]; exact htower.symm
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hDK) hx
  exact ramIdx_one_of_differentIdeal_eq_top K L (Ideal.absNorm_eq_one_iff.mp hone)

/-- Residue-field extensions of number fields are separable (extensions of finite, hence perfect,
fields). -/
theorem residue_isSeparable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (hp : p ≠ ⊥) (P : Ideal (𝓞 L)) [hPp : P.IsPrime]
    [P.LiesOver p] (hP : P ≠ ⊥) :
    Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P) := by
  haveI hpp : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  haveI : p.IsMaximal := hpp.isMaximal hp
  haveI : P.IsMaximal := hPp.isMaximal hP
  haveI : Finite (𝓞 K ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot _ hp
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP
  haveI : Finite p.ResidueField := IsLocalization.finite _ (nonZeroDivisors (𝓞 K ⧸ p))
  haveI : Finite P.ResidueField := IsLocalization.finite _ (nonZeroDivisors (𝓞 L ⧸ P))
  haveI : PerfectField p.ResidueField := PerfectField.ofFinite
  haveI : Module.Finite p.ResidueField P.ResidueField := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic p.ResidueField P.ResidueField := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable p.ResidueField P.ResidueField := inferInstance
  infer_instance

end Workspace.ProofLemmas.UnramifiedDiscriminant
