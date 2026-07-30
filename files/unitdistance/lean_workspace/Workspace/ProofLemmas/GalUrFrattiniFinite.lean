import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.ProPMaxOpenFree
import Workspace.ProofLemmas.UnramifiedDiscriminant
import Workspace.ProofLemmas.GalUrIsProP
import Workspace.ProofLemmas.SublemmaSubextUnramified
import Workspace.ProofLemmas.UnramifiedProPTowerCorrespondence

/-!
# Finiteness of the Frattini quotient of `Gal(F^{ur,3}/F)`

Finiteness of the Frattini quotient of `G = Gal(F^{ur,3}/F)`, via the Hermite/discriminant bound.

The cited route went through unramified class field theory (the Artin map identifies the maximal
elementary-abelian-`3` quotient of `G = Gal(F^{ur,3}/F)` with `Cl_F ⊗ ℤ/3ℤ`, which is finite because
the class group is).  Artin reciprocity is not in Mathlib, so we take the **Hermite** route instead,
which is entirely Mathlib-supported and gives the same conclusion:

* every maximal proper open subgroup `H ≤ G` is normal of index `3`
  (`ProPMaxOpenFree.maxOpen_normal_index_p`, from pro-`3`-ness);
* by the infinite Galois correspondence (`UnramifiedProPTowerCorrespondence_partA`) the assignment
  `H ↦ fixedFieldOf 3 F H` is injective, and each fixed field is a degree-`3` extension of `F`;
* each such layer is everywhere unramified over `F` (`SublemmaSubextUnramified`), so its relative
  different ideal is trivial and the tower formula gives `|D_E| = |D_F|³`;
* **Hermite's theorem** (`NumberField.finite_of_discr_bdd`) then bounds the number of such fields,
  so there are only finitely many maximal open subgroups;
* hence `Φ(G)` — their intersection — is open, and `G` is compact, so `G/Φ(G)` is finite.
-/

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.GalUrFrattiniFinite

open Workspace.ProofLemmas.UnramifiedDiscriminant

/-- **Hermite, relative form.** For a number field `F` there are only finitely many
finite-dimensional intermediate fields of `AlgebraicClosure F / F` whose absolute discriminant is
bounded by `N`. -/
theorem finite_subfields_discr_le (F : Type) [Field F] [NumberField F] (N : ℕ) :
    {E : IntermediateField F (AlgebraicClosure F) | ∃ _ : FiniteDimensional F ↥E,
        haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
        (NumberField.discr ↥E).natAbs ≤ N}.Finite := by
  haveI : CharZero (AlgebraicClosure F) := charZero_of_injective_algebraMap
    (algebraMap ℚ (AlgebraicClosure F)).injective
  haveI : IsScalarTower ℚ F (AlgebraicClosure F) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hHermite := NumberField.finite_of_discr_bdd (AlgebraicClosure F) N
  set g : IntermediateField F (AlgebraicClosure F) → IntermediateField ℚ (AlgebraicClosure F) :=
    fun E => E.restrictScalars ℚ with hg
  have hginj : Function.Injective g := IntermediateField.restrictScalars_injective ℚ
  refine Set.Finite.of_finite_image ?_ (hginj.injOn)
  refine Set.Finite.subset (hHermite.image Subtype.val) ?_
  rintro _ ⟨E, ⟨hfd, hdisc⟩, rfl⟩
  haveI := hfd
  haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
  haveI hfd' : FiniteDimensional ℚ ↥(g E) := by
    show FiniteDimensional ℚ ↥E
    exact Module.Finite.trans (R := ℚ) F ↥E
  refine ⟨⟨g E, hfd'⟩, ?_, rfl⟩
  haveI : NumberField ↥(g E) := inferInstanceAs (NumberField ↥E)
  show |NumberField.discr ↥(g E)| ≤ (N : ℤ)
  have h2 : NumberField.discr ↥(g E) = NumberField.discr ↥E := rfl
  rw [h2, Int.abs_eq_natAbs]
  exact_mod_cast hdisc

/-- The set of maximal proper open subgroups of `Gal(F^{ur,3}/F)` is finite. -/
theorem finite_maximalOpen_galUr (F : Type) [Field F] [NumberField F] :
    {H : Subgroup (galUr 3 F) | IsMaximalOpenSubgroup H}.Finite := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  obtain ⟨hpartA, hinj, _⟩ := UnramifiedProPTowerCorrespondence_partA F
  set ι := IntermediateField.val (maxUnramifiedProPExt 3 F) with hι
  set ff : Subgroup (galUr 3 F) → IntermediateField F (AlgebraicClosure F) :=
    fun H => IntermediateField.map ι (fixedFieldOf 3 F H) with hff
  -- the target finite set
  set N : ℕ := (NumberField.discr F).natAbs ^ 3 with hN
  refine Set.Finite.of_finite_image (f := ff) ?_ ?_
  · refine Set.Finite.subset (finite_subfields_discr_le F N) ?_
    rintro _ ⟨H, hH, rfl⟩
    obtain ⟨hHnorm, hHidx⟩ :=
      Workspace.ProofLemmas.ProPMaxOpenFree.maxOpen_normal_index_p 3 (galUr 3 F) hpro H hH
    haveI := hHnorm
    obtain ⟨hgalL, hfdL, hrankL, _⟩ := hpartA H hHnorm hH.1
    haveI := hfdL
    letI : NumberField ↥(fixedFieldOf 3 F H) :=
      NumberField.of_module_finite (K := F) (L := ↥(fixedFieldOf 3 F H))
    -- the F-algebra equivalence onto the image inside `AlgebraicClosure F`
    have e : (fixedFieldOf 3 F H) ≃ₐ[F] ↥(ff H) :=
      IntermediateField.equivMap (fixedFieldOf 3 F H) ι
    haveI hfd'' : FiniteDimensional F ↥(ff H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    letI : NumberField ↥(ff H) := NumberField.of_module_finite (K := F) (L := ↥(ff H))
    refine ⟨hfd'', ?_⟩
    -- discriminants agree
    have hdd : NumberField.discr ↥(ff H) = NumberField.discr ↥(fixedFieldOf 3 F H) :=
      (NumberField.discr_eq_discr_of_ringEquiv _ (e.toRingEquiv)).symm
    -- the layer is everywhere unramified
    have hunr : EverywhereUnramified F ↥(fixedFieldOf 3 F H) :=
      SublemmaSubextUnramified F (fixedFieldOf 3 F H)
    have hdiscr :
        (NumberField.discr ↥(fixedFieldOf 3 F H)).natAbs
          = (NumberField.discr F).natAbs ^ Module.finrank F ↥(fixedFieldOf 3 F H) :=
      natAbs_discr_of_unramified F ↥(fixedFieldOf 3 F H)
        (fun p hp hpp P hP => hunr.1 p hp hpp P hP)
    rw [hdd, hdiscr, hrankL, hHidx, hN]
  · -- injectivity
    intro H₁ h₁ H₂ h₂ heq
    obtain ⟨hn₁, _⟩ :=
      Workspace.ProofLemmas.ProPMaxOpenFree.maxOpen_normal_index_p 3 (galUr 3 F) hpro H₁ h₁
    obtain ⟨hn₂, _⟩ :=
      Workspace.ProofLemmas.ProPMaxOpenFree.maxOpen_normal_index_p 3 (galUr 3 F) hpro H₂ h₂
    exact hinj H₁ H₂ hn₁ h₁.1 hn₂ h₂.1
      (IntermediateField.map_injective ι heq)

/-- **The Frattini quotient of `Gal(F^{ur,3}/F)` is finite.** -/
theorem galUrFrattiniQuotientFinite (F : Type) [Field F] [NumberField F] :
    Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)) := by
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  obtain ⟨_, hcompact, _, _, _⟩ := hpro
  haveI := hcompact
  have hfin := finite_maximalOpen_galUr F
  have hopen : IsOpen ((frattiniOpen (galUr 3 F) : Subgroup (galUr 3 F)) : Set (galUr 3 F)) := by
    rw [frattiniOpen, Subgroup.coe_sInf]
    exact hfin.isOpen_biInter (fun H hH => hH.1)
  exact Subgroup.quotient_finite_of_isOpen _ hopen

end Workspace.ProofLemmas.GalUrFrattiniFinite
