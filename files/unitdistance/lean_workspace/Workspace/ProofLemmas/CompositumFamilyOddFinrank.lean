-- Cited from: J. Neukirch, Algebraic Number Theory, Springer, 1999 (Neu99).
-- Each member `Eᵢ` of the defining family is a finite Galois pro-3 extension, so `[Eᵢ : F]` equals
-- `|Gal(Eᵢ/F)|`, a power of `3` (hence odd).  For a compositum of two finite Galois extensions
-- `A, B ≤ AlgebraicClosure F`, the restriction map `Gal(A ⊔ B / F) ↪ Gal(A/F) × Gal(B/F)` is
-- injective (an automorphism fixing both `A` and `B` fixes their compositum `A ⊔ B = ⊤`), so by
-- Lagrange `[A ⊔ B : F] = |Gal(A ⊔ B / F)|` divides `|Gal(A/F)| · |Gal(B/F)| = [A:F]·[B:F]`.  A
-- divisor of an odd number is odd, so by induction over the finite family the compositum
-- `⨆ i ∈ s, Eᵢ` has odd degree over `F`.
-- Paper label: Definitions A.2/A.3 (odd-degree half).
--
-- NL statement: For a finite set `s` of members of the defining family (finite Galois everywhere-
-- unramified pro-3 subextensions of `AlgebraicClosure F`), the degree `[⨆ i ∈ s, Eᵢ : F]` is odd.
--
-- This feeds the infinite-places half of everywhere-unramifiedness: given this odd degree and the
-- Mathlib-derived `IsGalois F (⨆ i ∈ s, Eᵢ)`, `IsUnramifiedAtInfinitePlaces F (⨆ i ∈ s, Eᵢ)` is
-- proved from Mathlib via `IsUnramifiedAtInfinitePlaces_of_odd_finrank` in the consuming file.
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.SplittingRamification

open scoped NumberField
open Module IntermediateField
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- For finite Galois intermediate fields `A, B` of `E / F`, the degree of the compositum
`[A ⊔ B : F]` divides `[A : F] · [B : F]`, via the injective restriction embedding
`Gal(A ⊔ B / F) ↪ Gal(A/F) × Gal(B/F)`. -/
private theorem finrank_sup_dvd {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A B : IntermediateField F E) [FiniteDimensional F A] [FiniteDimensional F B]
    [IsGalois F A] [IsGalois F B] :
    finrank F ↥(A ⊔ B) ∣ finrank F A * finrank F B := by
  set C : IntermediateField F E := A ⊔ B with hC
  let A' : IntermediateField F C := IntermediateField.restrict (le_sup_left : A ≤ C)
  let B' : IntermediateField F C := IntermediateField.restrict (le_sup_right : B ≤ C)
  let eA : ↥A ≃ₐ[F] ↥A' := IntermediateField.restrict_algEquiv (le_sup_left : A ≤ C)
  let eB : ↥B ≃ₐ[F] ↥B' := IntermediateField.restrict_algEquiv (le_sup_right : B ≤ C)
  haveI : FiniteDimensional F ↥A' := eA.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional F ↥B' := eB.toLinearEquiv.finiteDimensional
  haveI : IsGalois F ↥A' := IsGalois.of_algEquiv eA
  haveI : IsGalois F ↥B' := IsGalois.of_algEquiv eB
  have hsup : A' ⊔ B' = ⊤ := by
    rw [← lift_inj, lift_top, lift_sup, lift_restrict (le_sup_left : A ≤ C),
      lift_restrict (le_sup_right : B ≤ C)]
  let Φ := (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥C) (↥A')).prod
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥C) (↥B'))
  have hker : Φ.ker = ⊥ := by
    rw [MonoidHom.ker_prod, IntermediateField.restrictNormalHom_ker,
      IntermediateField.restrictNormalHom_ker, ← IntermediateField.fixingSubgroup_sup, hsup,
      IntermediateField.fixingSubgroup_top]
  have hinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hker
  have hdvd : Nat.card (↥C ≃ₐ[F] ↥C) ∣ Nat.card (↥A' ≃ₐ[F] ↥A') * Nat.card (↥B' ≃ₐ[F] ↥B') := by
    have := Subgroup.card_dvd_of_injective Φ hinj
    rwa [Nat.card_prod] at this
  rw [IsGalois.card_aut_eq_finrank F ↥C, IsGalois.card_aut_eq_finrank F ↥A',
    IsGalois.card_aut_eq_finrank F ↥B'] at hdvd
  have hA : finrank F ↥A' = finrank F A := (eA.toLinearEquiv.finrank_eq).symm
  have hB : finrank F ↥B' = finrank F B := (eB.toLinearEquiv.finrank_eq).symm
  rw [hA, hB] at hdvd
  exact hdvd

/-- A member `E` of the defining family is finite Galois over `F` with odd degree (its degree is a
power of `3`, coming from `Gal(E/F)` being a finite `3`-group). -/
private theorem member_odd {F : Type} [Field F] [NumberField F]
    (E : IntermediateField F (AlgebraicClosure F))
    (h : IsFiniteUnramifiedProPExt 3 F E) :
    FiniteDimensional F E ∧ IsGalois F E ∧ Odd (finrank F E) := by
  obtain ⟨hfd, hgal, _, hpg⟩ := h
  haveI := hfd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨hfd, hgal, ?_⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := E ≃ₐ[F] E)).mp hpg
  rw [IsGalois.card_aut_eq_finrank F E] at hn
  rw [hn]
  exact (by norm_num : Odd 3).pow

/-- The compositum `⨆ i ∈ s, Eᵢ` of a finite family of members is finite-dimensional and Galois over
`F` with odd degree, proved by induction on `s` using `finrank_sup_dvd`. -/
private theorem family_props {F : Type} [Field F] [NumberField F]
    (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E}) :
    FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) ∧
      IsGalois F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) ∧
      Odd (finrank F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E}), (i : IntermediateField F (AlgebraicClosure F)))
        = ⊥ :=
      iSup_eq_bot.mpr (fun i => iSup_eq_bot.mpr (fun hi => absurd hi (Finset.notMem_empty i)))
    rw [hbot]
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IntermediateField.finrank_bot]
    exact odd_one
  | @insert a t ha ih =>
    obtain ⟨ihfd, ihgal, ihodd⟩ := ih
    obtain ⟨afd, agal, aodd⟩ := member_odd (F := F) (↑a) a.2
    haveI := ihfd; haveI := ihgal; haveI := afd; haveI := agal
    rw [Finset.iSup_insert]
    refine ⟨inferInstance, inferInstance, ?_⟩
    have hd := finrank_sup_dvd (F := F) (E := AlgebraicClosure F) (↑a)
      (⨆ i ∈ t, (i : IntermediateField F (AlgebraicClosure F)))
    exact (aodd.mul ihodd).of_dvd_nat hd

/-- **Compositum of family members has odd degree over `F`.**
For a finite set `s` of members of the defining family of finite Galois everywhere-unramified
pro-3 subextensions of `AlgebraicClosure F`, the degree `[⨆ i ∈ s, i : F]` is odd (it is a power
of `3`). Feeds the infinite-places half of everywhere-unramifiedness,
which is otherwise derived from Mathlib's `IsUnramifiedAtInfinitePlaces_of_odd_finrank`. -/
theorem CompositumFamilyOddFinrank :
    ∀ (F : Type) [Field F] [NumberField F]
      (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E})
      [FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))],
      Odd (Module.finrank F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))) := by
  intro F _ _ s _
  exact (family_props s).2.2
