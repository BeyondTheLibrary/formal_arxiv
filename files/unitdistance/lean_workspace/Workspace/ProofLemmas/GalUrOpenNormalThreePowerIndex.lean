-- Cited from: J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed., Springer, 2008, Chapter X; standard infinite Galois theory of the maximal everywhere-unramified pro-p extension (Definition A.3 of the source paper).
-- Paper label: Definition A.3 (pro-3 property of Gal(F^{ur,3}/F))
-- Every open normal subgroup H of G = galUr 3 F has
-- index a power of 3. Proof: by the infinite Galois correspondence
-- `UnramifiedProPTowerCorrespondence_partA`, the fixed field E = fixedFieldOf 3 F H is a finite Galois
-- layer with finrank F E = H.index, so H.index = Nat.card (Gal(E/F)); it remains to show Gal(E/F) is a
-- 3-group. Lifting E into AlgebraicClosure F, E is a finite-dimensional (hence compact-element)
-- subextension of maxUnramifiedProPExt 3 F = sSup of the defining family of finite Galois everywhere-
-- unramified 3-group extensions, so E lies in a finite subcompositum W of family members. A finite
-- compositum of 3-group Galois extensions has 3-group Galois group (product-injection
-- Gal(A⊔B) ↪ Gal A × Gal B + Finset induction), and Gal(W/F) surjects onto Gal(E/F), so Gal(E/F) is a
-- 3-group.
-- NL statement: For every number field F, every open normal subgroup H of G = galUr 3 F (the Galois group of the maximal everywhere-unramified pro-3 extension F^{ur,3}/F) has index a power of 3: there exists k with H.index = 3 ^ k. This is the arithmetic core of the pro-3 property of Gal(F^{ur,3}/F), which the paper's Definition A.3 states as background (the Galois group of the maximal unramified pro-p extension is a pro-p group).
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.UnramifiedProPTowerCorrespondence

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 800000

/-- The Galois group of the compositum of two finite Galois 3-group extensions inside a common
field is again a 3-group. -/
lemma pgroup_sup {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
    (A B : IntermediateField F K)
    [FiniteDimensional F A] [IsGalois F A] [FiniteDimensional F B] [IsGalois F B]
    (hA : IsPGroup 3 (A ≃ₐ[F] A)) (hB : IsPGroup 3 (B ≃ₐ[F] B)) :
    IsPGroup 3 (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) := by
  haveI hnA : Normal F A := IsGalois.to_normal
  haveI hnB : Normal F B := IsGalois.to_normal
  letI algA : Algebra ↥A ↥(A ⊔ B) :=
    (IntermediateField.inclusion (le_sup_left)).toRingHom.toAlgebra
  letI algB : Algebra ↥B ↥(A ⊔ B) :=
    (IntermediateField.inclusion (le_sup_right)).toRingHom.toAlgebra
  haveI towerA : IsScalarTower F ↥A ↥(A ⊔ B) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion (le_sup_left)).commutes x).symm)
  haveI towerB : IsScalarTower F ↥B ↥(A ⊔ B) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion (le_sup_right)).commutes x).symm)
  haveI halg : Algebra.IsAlgebraic F ↥(A ⊔ B) := Algebra.IsAlgebraic.of_finite F _
  -- the product-of-restrictions monoid hom
  let f := AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(A ⊔ B)) ↥A
  let g := AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(A ⊔ B)) ↥B
  let ρ := f.prod g
  -- injectivity
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hσA : σ.restrictNormal ↥A = 1 := congrArg Prod.fst hσ
    have hσB : σ.restrictNormal ↥B = 1 := congrArg Prod.snd hσ
    -- the two subfields, viewed as intermediate fields of A ⊔ B
    set A' : IntermediateField F ↥(A ⊔ B) := IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B)
      with hA'def
    set B' : IntermediateField F ↥(A ⊔ B) := IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B)
      with hB'def
    have hmapA : A'.map ((A ⊔ B).val) = A := IntermediateField.lift_restrict _
    have hmapB : B'.map ((A ⊔ B).val) = B := IntermediateField.lift_restrict _
    have hgen : A' ⊔ B' = (⊤ : IntermediateField F ↥(A ⊔ B)) := by
      apply IntermediateField.map_injective ((A ⊔ B).val)
      rw [IntermediateField.map_sup, hmapA, hmapB, ← AlgHom.fieldRange_eq_map,
        IntermediateField.fieldRange_val]
    -- σ fixes A' and B' pointwise
    have hfixA : ∀ x ∈ A', σ x = x := by
      intro x hx
      rw [hA'def, IntermediateField.mem_restrict] at hx
      have hxy : (algebraMap ↥A ↥(A ⊔ B)) ⟨x.1, hx⟩ = x := by
        apply Subtype.ext; rfl
      have hc := AlgEquiv.restrictNormal_commutes σ ↥A ⟨x.1, hx⟩
      rw [hσA, AlgEquiv.one_apply, hxy] at hc
      exact hc.symm
    have hfixB : ∀ x ∈ B', σ x = x := by
      intro x hx
      rw [hB'def, IntermediateField.mem_restrict] at hx
      have hxy : (algebraMap ↥B ↥(A ⊔ B)) ⟨x.1, hx⟩ = x := by
        apply Subtype.ext; rfl
      have hc := AlgEquiv.restrictNormal_commutes σ ↥B ⟨x.1, hx⟩
      rw [hσB, AlgEquiv.one_apply, hxy] at hc
      exact hc.symm
    -- hence σ is the identity
    have hadj : Algebra.adjoin F ((A' : Set ↥(A ⊔ B)) ∪ (B' : Set ↥(A ⊔ B))) = ⊤ := by
      rw [← IntermediateField.adjoin_eq_top_iff]
      apply le_antisymm le_top
      rw [← hgen]
      apply sup_le
      · exact fun x hx => IntermediateField.subset_adjoin F _ (Set.subset_union_left hx)
      · exact fun x hx => IntermediateField.subset_adjoin F _ (Set.subset_union_right hx)
    have hEqOn : Set.EqOn (σ.toAlgHom) (AlgHom.id F ↥(A ⊔ B))
        ((A' : Set ↥(A ⊔ B)) ∪ (B' : Set ↥(A ⊔ B))) := by
      intro x hx
      rcases hx with hx | hx
      · show σ x = x; exact hfixA x hx
      · show σ x = x; exact hfixB x hx
    have hEq : σ.toAlgHom = AlgHom.id F ↥(A ⊔ B) := AlgHom.ext_of_adjoin_eq_top hadj hEqOn
    ext x
    simpa using AlgHom.ext_iff.mp hEq x
  -- the product of two 3-groups is a 3-group
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpgProd : IsPGroup 3 ((A ≃ₐ[F] A) × (B ≃ₐ[F] B)) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hA
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hB
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_prod, ha, hb, pow_add]
  exact hpgProd.of_injective ρ hinj

/-- A finite union (compositum) of members of the defining pro-`3` family is a finite Galois
3-group extension of `F`. -/
lemma pgroup_finset_sup {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
    {ι : Type*} (fam : ι → IntermediateField F K)
    (hfd : ∀ i, FiniteDimensional F (fam i)) (hgal : ∀ i, IsGalois F (fam i))
    (hpg : ∀ i, IsPGroup 3 ((fam i) ≃ₐ[F] (fam i))) (t : Finset ι) :
    FiniteDimensional F ↥(⨆ i ∈ t, fam i) ∧ IsGalois F ↥(⨆ i ∈ t, fam i) ∧
      IsPGroup 3 (↥(⨆ i ∈ t, fam i) ≃ₐ[F] ↥(⨆ i ∈ t, fam i)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  induction t using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), fam i) = ⊥ by simp]
    refine ⟨inferInstance, inferInstance, ?_⟩
    apply IsPGroup.of_card (n := 0)
    rw [pow_zero, IsGalois.card_aut_eq_finrank F (⊥ : IntermediateField F K),
      IntermediateField.finrank_bot]
  | @insert a s ha ih =>
    obtain ⟨ihfd, ihgal, ihpg⟩ := ih
    rw [Finset.iSup_insert]
    haveI := hfd a; haveI := ihfd; haveI := hgal a; haveI := ihgal
    refine ⟨inferInstance, inferInstance, ?_⟩
    exact pgroup_sup (fam a) (⨆ i ∈ s, fam i) (hpg a) ihpg

/-- **Every open normal subgroup of `galUr 3 F` has 3-power index.** -/
theorem GalUrOpenNormalThreePowerIndex :
    ∀ (F : Type) [Field F] [NumberField F] (H : Subgroup (galUr 3 F)),
      H.Normal → IsOpen (H : Set (galUr 3 F)) → ∃ k : ℕ, H.index = 3 ^ k := by
  intro F _ _ H hHnorm hHopen
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Part (a) of the Krull correspondence: the fixed field is a finite Galois layer.
  obtain ⟨hgalE, hfdE, hrank, _⟩ :=
    (UnramifiedProPTowerCorrespondence_partA F).1 H hHnorm hHopen
  haveI := hfdE
  haveI := hgalE
  -- STEP A: it suffices to show Gal(E/F) is a 3-group.
  suffices hpgE : IsPGroup 3 (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H)) by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpgE
    refine ⟨k, ?_⟩
    rw [← hrank, ← IsGalois.card_aut_eq_finrank F ↥(fixedFieldOf 3 F H), hk]
  -- STEP B: lift E into the algebraic closure and use the compositum structure of F^{ur,3}.
  set Ehat := IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
    (fixedFieldOf 3 F H) with hEhatdef
  have eEE : ↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥Ehat :=
    IntermediateField.equivMap (fixedFieldOf 3 F H)
      (IntermediateField.val (maxUnramifiedProPExt 3 F))
  haveI hfdEhat : FiniteDimensional F ↥Ehat := LinearEquiv.finiteDimensional eEE.toLinearEquiv
  haveI hgalEhat : IsGalois F ↥Ehat := (AlgEquiv.transfer_galois eEE).mp hgalE
  haveI hnormEhat : Normal F ↥Ehat := hgalEhat.to_normal
  -- The defining family and its per-member properties.
  set fam : ↥{E : IntermediateField F (AlgebraicClosure F) | IsFiniteUnramifiedProPExt 3 F E} →
      IntermediateField F (AlgebraicClosure F) := fun i => (i : IntermediateField F _) with hfamdef
  have hfamfd : ∀ i, FiniteDimensional F (fam i) := by
    intro i; obtain ⟨hfd, _⟩ := i.2; exact hfd
  have hfamgal : ∀ i, IsGalois F (fam i) := by
    intro i; obtain ⟨_, hgal, _, _⟩ := i.2; exact hgal
  have hfampg : ∀ i, IsPGroup 3 ((fam i) ≃ₐ[F] (fam i)) := by
    intro i; obtain ⟨_, _, _, hpg⟩ := i.2; exact hpg
  -- Kbig = ⨆ i, fam i
  have hKbigSup : maxUnramifiedProPExt 3 F = ⨆ i, fam i := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
  -- Ê ≤ Kbig ≤ ⨆ fam
  have hEhatKbig : Ehat ≤ maxUnramifiedProPExt 3 F := by
    rw [hEhatdef]
    calc IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
            (fixedFieldOf 3 F H)
        ≤ IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) ⊤ :=
          IntermediateField.map_mono _ le_top
      _ = maxUnramifiedProPExt 3 F := by
          rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  have hEhatSup : Ehat ≤ ⨆ i, fam i := le_of_le_of_eq hEhatKbig hKbigSup
  -- Ê is compact (adjoin of a primitive element), so lies in a finite subcompositum.
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F ↥Ehat
  set a := (IntermediateField.val Ehat) α with hadef
  have hEhatAdj : Ehat = IntermediateField.adjoin F {a} := by
    have h1 : IntermediateField.map (IntermediateField.val Ehat)
        (IntermediateField.adjoin F {α}) = IntermediateField.adjoin F {a} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    have h2 : IntermediateField.map (IntermediateField.val Ehat)
        (⊤ : IntermediateField F ↥Ehat) = Ehat := by
      rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
    calc Ehat = IntermediateField.map (IntermediateField.val Ehat) ⊤ := h2.symm
      _ = IntermediateField.map (IntermediateField.val Ehat) (IntermediateField.adjoin F {α}) := by
          rw [hα]
      _ = IntermediateField.adjoin F {a} := h1
  have hcompact : IsCompactElement Ehat := by
    rw [hEhatAdj]; exact IntermediateField.adjoin_simple_isCompactElement a
  obtain ⟨t, ht⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (hk := hcompact) (f := fam)
      (h := hEhatSup)
  -- The finite subcompositum W is a finite Galois 3-group extension.
  obtain ⟨hWfd, hWgal, hWpg⟩ := pgroup_finset_sup fam hfamfd hfamgal hfampg t
  haveI := hWfd
  haveI := hWgal
  haveI hWnorm : Normal F ↥(⨆ i ∈ t, fam i) := hWgal.to_normal
  -- Ê is a subfield of W, so Gal(W/F) surjects onto Gal(Ê/F).
  letI algEW : Algebra ↥Ehat ↥(⨆ i ∈ t, fam i) :=
    (IntermediateField.inclusion ht).toRingHom.toAlgebra
  haveI towerEW : IsScalarTower F ↥Ehat ↥(⨆ i ∈ t, fam i) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion ht).commutes x).symm)
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(⨆ i ∈ t, fam i)) ↥Ehat) :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥Ehat) (↥(⨆ i ∈ t, fam i))
  have hpgEhat : IsPGroup 3 (↥Ehat ≃ₐ[F] ↥Ehat) := hWpg.of_surjective _ hsurj
  -- Transport back to Gal(E/F).
  exact hpgEhat.of_equiv (AlgEquiv.autCongr eEE).symm
