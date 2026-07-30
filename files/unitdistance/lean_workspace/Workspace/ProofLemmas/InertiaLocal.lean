import Mathlib
import Workspace.ProofLemmas.UnramifiedDiscriminant

/-!
# Inertia at a single prime

A prime-by-prime version of the Hilbert inertia argument used in
`Workspace.ProofLemmas.CompositumUnramified`.  The two statements are

* `card_inertia_eq_ramificationIdx` — `|I(P)| = e(P/p)`;
* `inertia_le_fixingSubgroup` — if the intermediate field `E` is unramified **at `p`** then the
  inertia group of `P` fixes `E` pointwise.

Together they give both directions we need: composita of extensions unramified at `p` are
unramified at `p`, and (conversely) a subfield fixed by the whole inertia group is unramified.
-/

open scoped NumberField

namespace Workspace.ProofLemmas.InertiaLocal

set_option maxHeartbeats 1000000

open Workspace.ProofLemmas.UnramifiedDiscriminant

variable {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M]
  [Algebra F M] [IsGalois F M]

/-! ### Ramification versus the discriminant -/

section Discr

/-- If a rational prime `r` is ramified in `E` then `r` divides `|disc E|`. -/
theorem dvd_discr_of_ramified (E : Type*) [Field E] [NumberField E]
    (r : ℕ) (hr : r.Prime) (Q : Ideal (𝓞 E)) [hQp : Q.IsPrime]
    [hQl : Q.LiesOver (Ideal.span {(r : ℤ)})] (hQne : Q ≠ ⊥)
    (he : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ≠ 1) :
    r ∣ (NumberField.discr E).natAbs := by
  have hrprime : Prime ((r : ℤ)) := Nat.prime_iff_prime_int.mp hr
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact hrprime
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  haveI : Q.IsMaximal := hQp.isMaximal hQne
  have hdvd : Q ∣ differentIdeal ℤ (𝓞 E) := by
    by_contra hcon
    haveI : Algebra.IsUnramifiedAt ℤ Q := (not_dvd_differentIdeal_iff).mp hcon
    exact he (by
      rw [hQl.over]
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (S := 𝓞 E) hQne)
  have h2 := map_dvd Ideal.absNorm hdvd
  rw [NumberField.absNorm_differentIdeal E (𝓞 E),
    Ideal.absNorm_eq_pow_inertiaDeg Q hrprime, Int.natAbs_natCast] at h2
  refine dvd_trans ?_ h2
  exact dvd_pow_self _ (Ideal.inertiaDeg_pos (Ideal.span {(r : ℤ)}) Q).ne'

/-- Contrapositive: if `r ∤ |disc E|` then `r` is unramified in `E`. -/
theorem ramificationIdx_eq_one_of_not_dvd_discr (E : Type*) [Field E] [NumberField E]
    (r : ℕ) (hr : r.Prime) (Q : Ideal (𝓞 E)) [hQp : Q.IsPrime]
    [hQl : Q.LiesOver (Ideal.span {(r : ℤ)})] (hQne : Q ≠ ⊥)
    (h : ¬ r ∣ (NumberField.discr E).natAbs) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q = 1 := by
  by_contra hcon
  exact h (dvd_discr_of_ramified E r hr Q hQne hcon)

end Discr

/-! ### The absolute case: base `ℤ ⊆ ℚ` -/

section Rat

/-- Residue extensions over `ℤ` are separable. -/
theorem residue_isSeparable_int {L : Type*} [Field L] [NumberField L]
    (p : Ideal ℤ) (hp : p ≠ ⊥) (P : Ideal (𝓞 L)) [hPp : P.IsPrime]
    [P.LiesOver p] (hP : P ≠ ⊥) :
    Algebra.IsSeparable (ℤ ⧸ p) (𝓞 L ⧸ P) := by
  haveI hpp : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  haveI : p.IsMaximal := hpp.isMaximal hp
  haveI : P.IsMaximal := hPp.isMaximal hP
  haveI : Finite (ℤ ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot _ hp
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP
  haveI : Finite p.ResidueField := IsLocalization.finite _ (nonZeroDivisors (ℤ ⧸ p))
  haveI : Finite P.ResidueField := IsLocalization.finite _ (nonZeroDivisors (𝓞 L ⧸ P))
  haveI : PerfectField p.ResidueField := PerfectField.ofFinite
  haveI : Module.Finite p.ResidueField P.ResidueField := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic p.ResidueField P.ResidueField := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable p.ResidueField P.ResidueField := inferInstance
  infer_instance

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]

/-- `|I(P)| = e(P/p)` over the base `ℤ`. -/
theorem card_inertia_eq_ramificationIdx_int
    (p : Ideal ℤ) (hp : p ≠ ⊥) [hpp : p.IsPrime]
    (P : Ideal (𝓞 M)) [hPprime : P.IsPrime] [hPlies : P.LiesOver p] (hPne : P ≠ ⊥) :
    Nat.card (P.inertia (M ≃ₐ[ℚ] M)) = Ideal.ramificationIdx p P := by
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  haveI : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ M
  haveI := residue_isSeparable_int p hp P hPne
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) p hp P,
    Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[ℚ] M)]

/-- **Inertia fixes every intermediate field unramified at `p`** (absolute version). -/
theorem inertia_le_fixingSubgroup_int (E : IntermediateField ℚ M)
    (p : Ideal ℤ) (hp : p ≠ ⊥) [hpp : p.IsPrime]
    (P : Ideal (𝓞 M)) [hPprime : P.IsPrime] [hPlies : P.LiesOver p] (hPne : P ≠ ⊥)
    (hE : haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
      Ideal.ramificationIdx p (P.under (𝓞 ↥E)) = 1) :
    P.inertia (M ≃ₐ[ℚ] M) ≤ E.fixingSubgroup := by
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  haveI : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ M
  haveI := residue_isSeparable_int p hp P hPne
  have hcardF : Nat.card (P.inertia (M ≃ₐ[ℚ] M)) = Ideal.ramificationIdx p P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) p hp P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[ℚ] M)]
  intro σ hσ
  haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
  haveI : IsGalois ↥E M := IsGalois.tower_top_of_isGalois ℚ ↥E M
  haveI tower : IsScalarTower ℤ (𝓞 ↥E) (𝓞 M) := inferInstance
  haveI : IsGaloisGroup (M ≃ₐ[↥E] M) (𝓞 ↥E) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing _ _ _ (↥E) M
  set pE : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E) with hpE
  haveI : P.LiesOver pE := ⟨rfl⟩
  haveI : pE.IsPrime := Ideal.IsPrime.under _ P
  have hpEover : pE.under ℤ = p := by
    rw [hpE, Ideal.under_under]
    exact (Ideal.over_def P p).symm
  haveI : pE.LiesOver p := ⟨hpEover.symm⟩
  have hpEne : pE ≠ ⊥ := by
    intro hcon
    exact hp (by rw [← hpEover, hcon, Ideal.under_bot])
  haveI := residue_isSeparable pE hpEne P hPne
  have hcardE : Nat.card (P.inertia (M ≃ₐ[↥E] M)) = Ideal.ramificationIdx pE P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[↥E] M) pE hpEne P,
      Ideal.ramificationIdxIn_eq_ramificationIdx pE P (M ≃ₐ[↥E] M)]
  have htower : Ideal.ramificationIdx p P
      = Ideal.ramificationIdx p pE * Ideal.ramificationIdx pE P :=
    Ideal.ramificationIdx_algebra_tower' (R := ℤ) (S := 𝓞 ↥E) (T := 𝓞 M) p pE P
  rw [hE, one_mul] at htower
  have hsmul : ∀ (τ : M ≃ₐ[↥E] M) (x : 𝓞 M), (τ.restrictScalars ℚ) • x = τ • x := by
    intro τ x
    exact Subtype.ext rfl
  have hmaps : ∀ τ : M ≃ₐ[↥E] M, τ ∈ P.inertia (M ≃ₐ[↥E] M) →
      τ.restrictScalars ℚ ∈ P.inertia (M ≃ₐ[ℚ] M) := by
    intro τ hτ x
    rw [hsmul]
    exact hτ x
  set g : (P.inertia (M ≃ₐ[↥E] M)) → (P.inertia (M ≃ₐ[ℚ] M)) :=
    fun τ => ⟨(τ : M ≃ₐ[↥E] M).restrictScalars ℚ, hmaps _ τ.2⟩ with hg
  have hginj : Function.Injective g := by
    rintro ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩ h
    have h' : (τ₁.restrictScalars ℚ) = (τ₂.restrictScalars ℚ) := congrArg Subtype.val h
    ext x
    exact DFunLike.congr_fun h' x
  haveI : Finite (M ≃ₐ[ℚ] M) := inferInstance
  haveI : Finite (M ≃ₐ[↥E] M) := inferInstance
  haveI : Fintype (P.inertia (M ≃ₐ[↥E] M)) := Fintype.ofFinite _
  haveI : Fintype (P.inertia (M ≃ₐ[ℚ] M)) := Fintype.ofFinite _
  have hcards : Fintype.card (P.inertia (M ≃ₐ[↥E] M))
      = Fintype.card (P.inertia (M ≃ₐ[ℚ] M)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardE, hcardF, htower]
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcards⟩
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨σ, hσ⟩
  have hστ : σ = (τ : M ≃ₐ[↥E] M).restrictScalars ℚ := (congrArg Subtype.val hτ).symm
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [hστ]
  exact (τ : M ≃ₐ[↥E] M).commutes (⟨x, hx⟩ : ↥E)

/-- **Discriminant form.**  If the rational prime `r` does not divide `|disc E|` then the inertia
group of any prime over `r` fixes `E`. -/
theorem inertia_le_fixingSubgroup_of_not_dvd_discr (E : IntermediateField ℚ M)
    (r : ℕ) (hr : r.Prime)
    (P : Ideal (𝓞 M)) [hPprime : P.IsPrime] [hPlies : P.LiesOver (Ideal.span {(r : ℤ)})]
    (hPne : P ≠ ⊥)
    (hE : haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
      ¬ r ∣ (NumberField.discr ↥E).natAbs) :
    P.inertia (M ≃ₐ[ℚ] M) ≤ E.fixingSubgroup := by
  haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  refine inertia_le_fixingSubgroup_int M E _ hrbot P hPne ?_
  haveI : (P.under (𝓞 ↥E)).IsPrime := Ideal.IsPrime.under _ P
  haveI : (P.under (𝓞 ↥E)).LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    rw [Ideal.under_under]
    exact hPlies.over
  have hPEne : (P.under (𝓞 ↥E)) ≠ ⊥ := by
    intro hcon
    exact hPne (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 ↥E) (S := 𝓞 M) (I := P) hcon)
  exact ramificationIdx_eq_one_of_not_dvd_discr ↥E r hr _ hPEne hE

end Rat

end Workspace.ProofLemmas.InertiaLocal
