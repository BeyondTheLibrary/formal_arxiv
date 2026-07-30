import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.Types.UnramifiedProPExtension
import Workspace.ProofLemmas.UnramifiedDiscriminant

/-!
# Compositum of everywhere-unramified extensions is everywhere unramified (finite primes)

A compositum of finitely many everywhere-unramified (at the finite primes) extensions is again
everywhere unramified at the finite primes.

The argument is Hilbert's inertia-group argument.  For a prime `P` of `𝓞 M` over `p` of `𝓞 F`, with
`M/F` finite Galois, Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` says the inertia group
`I(P) ≤ Gal(M/F)` has order `e(P/p)`.  If `E` is an intermediate field with `E/F` unramified, then
`e(P/p) = e(P/P∩E)` by tower multiplicativity, and `I_{M/E}(P) = I_{M/F}(P) ∩ Gal(M/E)` is defined by
the *same* condition on `𝓞 M`; equality of the (finite) cardinalities forces `I_{M/F}(P) ≤ Gal(M/E)`.
Applying this to `A` and `B` with `A ⊔ B = ⊤` gives `I(P) ≤ Gal(M/A) ⊓ Gal(M/B) = Gal(M/⊤) = 1`,
i.e. `e(P/p) = 1`.  A `Finset` induction then covers the whole family.

Transport of unramifiedness along field isomorphisms is free here because
`Workspace.ProofLemmas.UnramifiedDiscriminant.unramified_iff_natAbs_discr` re-expresses it as an
identity between absolute discriminants.
-/

open scoped NumberField
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension
open Workspace.ProofLemmas.UnramifiedDiscriminant

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Workspace.ProofLemmas.CompositumUnramified

/-- Compositum of finitely many finite Galois subextensions is Galois (local copy of the helper in
`SublemmaSubextUnramified`, duplicated here to keep the import graph acyclic). -/
theorem isGalois_biSup {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
    {ι : Type*} (t : ι → IntermediateField F K) (s : Finset ι)
    (hg : ∀ i, IsGalois F ↥(t i)) :
    IsGalois F ↥(⨆ i ∈ s, t i) := by
  haveI : ∀ i, Normal F ↥(t i) := fun i => (hg i).to_normal
  haveI : ∀ i, Algebra.IsSeparable F ↥(t i) := fun i => (hg i).to_isSeparable
  haveI : Normal F ↥(⨆ i ∈ s, t i) :=
    iSup_subtype'' (s : Set ι) t ▸
      IntermediateField.normal_iSup (t := fun i : ↥(s : Set ι) => t i.1)
  haveI : Algebra.IsSeparable F ↥(⨆ i ∈ s, t i) :=
    iSup_subtype'' (s : Set ι) t ▸
      IntermediateField.isSeparable_iSup (t := fun i : ↥(s : Set ι) => t i.1)
  exact { }

/-- **Compositum of two everywhere-unramified Galois subextensions.**  If `M/F` is a finite Galois
extension of number fields and `A ⊔ B = ⊤` for two intermediate fields that are unramified over `F`
at all finite primes, then `M/F` is unramified at all finite primes.

The proof is Hilbert's: the inertia group of a prime `P` of `𝓞 M` has order `e(P/p)`; because
`e(P/p) = e(P/P∩A)` (as `A/F` is unramified) and the inertia group for `M/A` is the intersection of
the inertia group for `M/F` with `Gal(M/A)`, that intersection has the same (finite) cardinality as
the whole inertia group, so the inertia group is contained in `Gal(M/A)`; likewise for `B`.  Hence
the inertia group lies in `Gal(M/A) ⊓ Gal(M/B) = Gal(M/(A ⊔ B)) = Gal(M/M) = 1`, i.e. `e(P/p) = 1`. -/
theorem unramified_of_sup_eq_top {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] [IsGalois F M] (A B : IntermediateField F M) (hAB : A ⊔ B = ⊤)
    (hA : ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 ↥A),
        haveI : NumberField ↥A := NumberField.of_module_finite (K := F) (L := ↥A)
        Ideal.ramificationIdx q Q = 1)
    (hB : ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 ↥B),
        haveI : NumberField ↥B := NumberField.of_module_finite (K := F) (L := ↥B)
        Ideal.ramificationIdx q Q = 1) :
    ∀ (p : Ideal (𝓞 F)), p ≠ ⊥ → p.IsPrime →
      ∀ P ∈ Ideal.primesOver p (𝓞 M), Ideal.ramificationIdx p P = 1 := by
  haveI : IsScalarTower ℚ F M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional F M := Module.Finite.right ℚ F M
  intro p hp hpp P hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver p := hPlies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  -- the action of `Gal(M/F)` on `𝓞 M`
  letI actF : MulSemiringAction (M ≃ₐ[F] M) (𝓞 M) :=
    IsIntegralClosure.MulSemiringAction (𝓞 F) F M (𝓞 M)
  haveI : IsGaloisGroup (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ F M
  haveI := residue_isSeparable p hp P hPne
  have hcardF : Nat.card (P.inertia (M ≃ₐ[F] M)) = Ideal.ramificationIdx p P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[F] M) p hp P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[F] M)]
  -- KEY: the inertia group lies inside the fixing subgroup of any unramified intermediate field
  have key : ∀ (E : IntermediateField F M),
      (∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
        ∀ Q ∈ Ideal.primesOver q (𝓞 ↥E),
          haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
          Ideal.ramificationIdx q Q = 1) →
      P.inertia (M ≃ₐ[F] M) ≤ E.fixingSubgroup := by
    intro E hE σ hσ
    haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
    haveI : IsGalois ↥E M := IsGalois.tower_top_of_isGalois F ↥E M
    haveI tower : IsScalarTower (𝓞 F) (𝓞 ↥E) (𝓞 M) :=
      NumberField.RingOfIntegers.inst_isScalarTower F ↥E M
    letI actE : MulSemiringAction (M ≃ₐ[↥E] M) (𝓞 M) :=
      IsIntegralClosure.MulSemiringAction (𝓞 ↥E) (↥E) M (𝓞 M)
    haveI : IsGaloisGroup (M ≃ₐ[↥E] M) (𝓞 ↥E) (𝓞 M) :=
      IsGaloisGroup.of_isFractionRing _ _ _ (↥E) M
    set pE : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E) with hpE
    haveI : P.LiesOver pE := ⟨rfl⟩
    haveI : pE.IsPrime := Ideal.IsPrime.under _ P
    have hpEover : pE.under (𝓞 F) = p := by
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
    -- ramification tower: e(P/p) = e(pE/p) * e(P/pE) = e(P/pE)
    have htower : Ideal.ramificationIdx p P
        = Ideal.ramificationIdx p pE * Ideal.ramificationIdx pE P :=
      Ideal.ramificationIdx_algebra_tower' (R := 𝓞 F) (S := 𝓞 ↥E) (T := 𝓞 M) p pE P
    have hone : Ideal.ramificationIdx p pE = 1 :=
      hE p hp hpp pE ⟨inferInstance, inferInstance⟩
    rw [hone, one_mul] at htower
    -- the restriction map on inertia groups
    have hsmul : ∀ (τ : M ≃ₐ[↥E] M) (x : 𝓞 M), (τ.restrictScalars F) • x = τ • x := by
      intro τ x
      show galRestrict (𝓞 F) F M (𝓞 M) (τ.restrictScalars F) x
        = galRestrict (𝓞 ↥E) (↥E) M (𝓞 M) τ x
      apply FaithfulSMul.algebraMap_injective (𝓞 M) M
      rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
      rfl
    have hmaps : ∀ τ : M ≃ₐ[↥E] M, τ ∈ P.inertia (M ≃ₐ[↥E] M) →
        τ.restrictScalars F ∈ P.inertia (M ≃ₐ[F] M) := by
      intro τ hτ x
      rw [hsmul]
      exact hτ x
    set g : (P.inertia (M ≃ₐ[↥E] M)) → (P.inertia (M ≃ₐ[F] M)) :=
      fun τ => ⟨(τ : M ≃ₐ[↥E] M).restrictScalars F, hmaps _ τ.2⟩ with hg
    have hginj : Function.Injective g := by
      rintro ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩ h
      have h' : (τ₁.restrictScalars F) = (τ₂.restrictScalars F) := congrArg Subtype.val h
      ext x
      exact DFunLike.congr_fun h' x
    haveI : Finite (M ≃ₐ[F] M) := inferInstance
    haveI : Finite (M ≃ₐ[↥E] M) := inferInstance
    haveI : Fintype (P.inertia (M ≃ₐ[↥E] M)) := Fintype.ofFinite _
    haveI : Fintype (P.inertia (M ≃ₐ[F] M)) := Fintype.ofFinite _
    have hcards : Fintype.card (P.inertia (M ≃ₐ[↥E] M))
        = Fintype.card (P.inertia (M ≃ₐ[F] M)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardE, hcardF, htower]
    have hbij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcards⟩
    obtain ⟨τ, hτ⟩ := hbij.2 ⟨σ, hσ⟩
    have hστ : σ = (τ : M ≃ₐ[↥E] M).restrictScalars F := (congrArg Subtype.val hτ).symm
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hστ]
    exact (τ : M ≃ₐ[↥E] M).commutes (⟨x, hx⟩ : ↥E)
  -- combine: the inertia group is trivial
  have hbot : P.inertia (M ≃ₐ[F] M) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro σ hσ
    have h1 := key A hA hσ
    have h2 := key B hB hσ
    have h3 : σ ∈ (A ⊔ B).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨h1, h2⟩
    rwa [hAB, IntermediateField.fixingSubgroup_top] at h3
  rw [← hcardF, hbot]
  simp




/-- Unramifiedness at all finite primes, as a predicate on intermediate fields (instance-free, so
that it can be rewritten along equalities of intermediate fields). -/
def Unram (F : Type*) [Field F] [NumberField F] {K : Type*} [Field K] [Algebra F K]
    (E : IntermediateField F K) : Prop :=
  ∀ hfd : FiniteDimensional F ↥E,
    haveI := hfd
    haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
    ∀ (p : Ideal (𝓞 F)), p ≠ ⊥ → p.IsPrime →
      ∀ P ∈ Ideal.primesOver p (𝓞 ↥E), Ideal.ramificationIdx p P = 1

/-- Unramifiedness at finite primes transports along an `F`-algebra equivalence. -/
theorem unramified_transport {F : Type*} [Field F] [NumberField F]
    {A B : Type*} [Field A] [NumberField A] [Field B] [NumberField B]
    [Algebra F A] [Algebra F B] (e : A ≃ₐ[F] B)
    (h : ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 A), Ideal.ramificationIdx q Q = 1) :
    ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 B), Ideal.ramificationIdx q Q = 1 := by
  rw [unramified_iff_natAbs_discr] at h ⊢
  rw [← NumberField.discr_eq_discr_of_ringEquiv _ e.toRingEquiv, ← e.toLinearEquiv.finrank_eq]
  exact h

/-- `⊥` is unramified. -/
theorem unram_bot (F : Type*) [Field F] [NumberField F] {K : Type*} [Field K] [Algebra F K] :
    Unram F (⊥ : IntermediateField F K) := by
  intro hfd
  haveI := hfd
  haveI : NumberField ↥(⊥ : IntermediateField F K) :=
    NumberField.of_module_finite (K := F) (L := ↥(⊥ : IntermediateField F K))
  refine unramified_transport (IntermediateField.botEquiv F K).symm ?_
  rw [unramified_iff_natAbs_discr]
  simp

/-- **Compositum of two unramified finite Galois subextensions is unramified.** -/
theorem unram_sup {F K : Type*} [Field F] [NumberField F] [Field K] [Algebra F K]
    (A B : IntermediateField F K) [FiniteDimensional F ↥A] [FiniteDimensional F ↥B]
    [IsGalois F ↥A] [IsGalois F ↥B] (hA : Unram F A) (hB : Unram F B) :
    Unram F (A ⊔ B) := by
  intro hfd
  haveI := hfd
  haveI : NumberField ↥(A ⊔ B) := NumberField.of_module_finite (K := F) (L := ↥(A ⊔ B))
  haveI : IsGalois F ↥(A ⊔ B) := by
    haveI : Normal F ↥(A ⊔ B) := inferInstance
    haveI : Algebra.IsSeparable F ↥(A ⊔ B) := inferInstance
    exact { }
  set M : IntermediateField F K := A ⊔ B with hM
  let A' : IntermediateField F ↥M := IntermediateField.restrict (le_sup_left : A ≤ M)
  let B' : IntermediateField F ↥M := IntermediateField.restrict (le_sup_right : B ≤ M)
  let eA : ↥A ≃ₐ[F] ↥A' := IntermediateField.restrict_algEquiv (le_sup_left : A ≤ M)
  let eB : ↥B ≃ₐ[F] ↥B' := IntermediateField.restrict_algEquiv (le_sup_right : B ≤ M)
  haveI : FiniteDimensional F ↥A' := eA.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional F ↥B' := eB.toLinearEquiv.finiteDimensional
  haveI : NumberField ↥A := NumberField.of_module_finite (K := F) (L := ↥A)
  haveI : NumberField ↥B := NumberField.of_module_finite (K := F) (L := ↥B)
  haveI : NumberField ↥A' := NumberField.of_module_finite (K := F) (L := ↥A')
  haveI : NumberField ↥B' := NumberField.of_module_finite (K := F) (L := ↥B')
  have hsup : A' ⊔ B' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict (le_sup_left : A ≤ M),
      IntermediateField.lift_restrict (le_sup_right : B ≤ M)]
  exact unramified_of_sup_eq_top (F := F) (M := ↥M) A' B' hsup
    (unramified_transport eA (hA inferInstance)) (unramified_transport eB (hB inferInstance))

/-- **The compositum of a finite family of unramified finite Galois subextensions is
unramified at all finite primes.** -/
theorem unram_biSup {F K : Type*} [Field F] [NumberField F] [Field K] [Algebra F K]
    {ι : Type*} (t : ι → IntermediateField F K)
    (hfd : ∀ i, FiniteDimensional F ↥(t i)) (hgal : ∀ i, IsGalois F ↥(t i))
    (hunr : ∀ i, Unram F (t i)) (s : Finset ι) :
    Unram F (⨆ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unram_bot F (K := K)
  | insert a s ha ih =>
      have hins : (⨆ i ∈ insert a s, t i) = t a ⊔ (⨆ i ∈ s, t i) := by
        simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
      rw [hins]
      haveI := hfd a
      haveI := hgal a
      haveI : FiniteDimensional F ↥(⨆ i ∈ s, t i) :=
        IntermediateField.finiteDimensional_iSup_of_finset' (fun i _ => hfd i)
      haveI : IsGalois F ↥(⨆ i ∈ s, t i) := isGalois_biSup t s hgal
      exact unram_sup (t a) (⨆ i ∈ s, t i) (hunr a) ih


/-- For a finite set `s` of members of the defining family of
finite Galois everywhere-unramified pro-3 subextensions of `AlgebraicClosure F`, their compositum
`⨆ i ∈ s, i` is unramified at every finite prime of `F`. -/
theorem compositumFamilyUnramifiedAtFinitePrimes :
    ∀ (F : Type) [Field F] [NumberField F]
      (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E})
      [FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))],
      haveI : NumberField ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
        NumberField.of_module_finite (K := F)
          (L := ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))))
      UnramifiedAtFinitePrimes F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) := by
  intro F _ _ s hfdM
  exact unram_biSup (F := F) (K := AlgebraicClosure F)
    (t := fun i : ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E} => (i : IntermediateField F (AlgebraicClosure F)))
    (fun i => i.2.choose)
    (fun i => i.2.choose_spec.1)
    (fun i _ => (i.2.choose_spec.2.1).1)
    s hfdM

end Workspace.ProofLemmas.CompositumUnramified
