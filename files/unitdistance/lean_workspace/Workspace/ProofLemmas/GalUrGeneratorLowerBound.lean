import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.ProPBurnsideBasis

open scoped NumberField Classical

open Workspace.Types.UnramifiedProPExtension Workspace.Types.ProPGroup

/-- A finite set generating the elementary abelian group `(ℤ/3)^n` (written multiplicatively)
has at least `n` elements: its `𝔽₃`-dimension is a lower bound for the number of generators. -/
private theorem elem_abelian_rank (n : ℕ) (T : Finset (Multiplicative (Fin n → ZMod 3)))
    (hT : Subgroup.closure (↑T : Set (Multiplicative (Fin n → ZMod 3))) = ⊤) :
    n ≤ T.card := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set T' : Finset (Fin n → ZMod 3) := T.image Multiplicative.toAdd with hT'
  have hcard : T'.card = T.card := by
    rw [hT']
    exact Finset.card_image_of_injective _ Multiplicative.toAdd.injective
  have hclos : AddSubgroup.closure (↑T' : Set (Fin n → ZMod 3)) = ⊤ := by
    have h2 := Subgroup.toAddSubgroup'_closure (↑T : Set (Multiplicative (Fin n → ZMod 3)))
    rw [hT] at h2
    have hset : (Multiplicative.ofAdd ⁻¹' (↑T : Set (Multiplicative (Fin n → ZMod 3))) :
        Set (Fin n → ZMod 3)) = (↑T' : Set (Fin n → ZMod 3)) := by
      rw [hT']; ext x; simp
    rw [hset] at h2
    simpa using h2.symm
  have hspan : Submodule.span (ZMod 3) (↑T' : Set (Fin n → ZMod 3)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ AddSubgroup.closure (↑T' : Set (Fin n → ZMod 3)) := by
      rw [hclos]; exact AddSubgroup.mem_top x
    exact (AddSubgroup.closure_le
      (Submodule.span (ZMod 3) (↑T' : Set (Fin n → ZMod 3))).toAddSubgroup).mpr
      Submodule.subset_span hx
  have hfin : Module.finrank (ZMod 3) (Fin n → ZMod 3) = n := by simp
  calc n = Module.finrank (ZMod 3) (Fin n → ZMod 3) := hfin.symm
    _ = Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) (↑T' : Set (Fin n → ZMod 3))) := by
          rw [hspan, finrank_top]
    _ ≤ (↑T' : Set (Fin n → ZMod 3)).toFinset.card := finrank_span_le_card _
    _ = T'.card := by simp
    _ = T.card := hcard

/-- **Proposition 3.8, eqn (5).** Let `F` be a totally real cyclic cubic number field and
`ℓ ≥ 2` an integer. Suppose there is a finite everywhere-unramified Galois extension `M/F`
that is a member of the defining family (`IsFiniteUnramifiedProPExt 3 F M'` for `M'` the image
of `M` as an `IntermediateField F (AlgebraicClosure F)`) whose Galois group is elementary abelian
of rank `ℓ-1` (a group isomorphism `(M' ≃ₐ[F] M') ≃* Multiplicative (Fin (ℓ-1) → ZMod 3)`).
Then the generator rank of `G := galUr 3 F` satisfies `(ℓ - 1 : ℕ∞) ≤ dRank G`. -/
theorem GalUrGeneratorLowerBound
    (F : Type*) [Field F] [NumberField F]
    (hTR : NumberField.IsTotallyReal F) (hGal : IsGalois ℚ F)
    (hdeg : Module.finrank ℚ F = 3)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (M' : IntermediateField F (AlgebraicClosure F))
    (hM : IsFiniteUnramifiedProPExt 3 F M')
    (φ : (M' ≃ₐ[F] M') ≃* Multiplicative (Fin (ℓ - 1) → ZMod 3)) :
    ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (galUr 3 F) := by
  set L := maxUnramifiedProPExt 3 F with hLdef
  have hle : M' ≤ L := le_sSup hM
  have hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    apply IntermediateField.normal_iSup (h := ?_)
    rintro ⟨E, hE⟩
    obtain ⟨hfd, hg, _, _⟩ := hE
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    haveI := hg
    infer_instance
  -- realise `M'` as an intermediate field `M''` of `L = F^{ur,3}`
  set valL := IntermediateField.val (maxUnramifiedProPExt 3 F) with hvalL
  set M'' := IntermediateField.comap valL M' with hM''
  have hmapeq : IntermediateField.map valL M'' = M' := by
    apply IntermediateField.map_comap_eq_self
    rw [hvalL, IntermediateField.fieldRange_val]; exact hle
  -- instances on `M'`
  obtain ⟨hfd, hgalM, _, _⟩ := hM
  haveI := hfd
  letI : NumberField (M' : Type _) :=
    NumberField.of_module_finite (K := F) (L := (M' : Type _))
  haveI : IsGalois F (↥M') := hgalM
  haveI : Normal F (↥M') := inferInstance
  -- field isomorphism `M'' ≃ₐ[F] M'`
  let g : ↥M'' ≃ₐ[F] ↥M' := (M''.equivMap valL).trans (IntermediateField.equivOfEq hmapeq)
  haveI : Normal F (↥M'') := Normal.of_algEquiv g.symm
  haveI : FiniteDimensional F (↥M'') := LinearEquiv.finiteDimensional g.symm.toLinearEquiv
  haveI : Normal F (↥L) := hnorm
  haveI : DiscreteTopology (↥M'' ≃ₐ[F] ↥M'') :=
    krullTopology_discreteTopology_of_finiteDimensional F ↥M''
  -- restriction homomorphism `Gal(L/F) ↠ Gal(M''/F)`, continuous and surjective
  let ρ₁ : (↥L ≃ₐ[F] ↥L) →* (↥M'' ≃ₐ[F] ↥M'') := AlgEquiv.restrictNormalHom ↥M''
  have hρ₁surj : Function.Surjective ρ₁ :=
    AlgEquiv.restrictNormalHom_surjective (K₁ := ↥M'') ↥L
  have hρ₁cont : Continuous ⇑ρ₁ := InfiniteGalois.restrictNormalHom_continuous M''
  -- group isomorphism `Gal(M''/F) ≃* (ℤ/3)^{ℓ-1}`
  let e : (↥M'' ≃ₐ[F] ↥M'') ≃* Multiplicative (Fin (ℓ - 1) → ZMod 3) :=
    (AlgEquiv.autCongr g).trans φ
  -- reduce `dRank` to a lower bound on the cardinality of any topological generating set
  show ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (↥L ≃ₐ[F] ↥L)
  rw [dRank]
  apply le_sInf
  rintro m ⟨S, hgen, rfl⟩
  rw [Nat.cast_le]
  have hgen' : _root_.closure (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) :
      Set (↥L ≃ₐ[F] ↥L)) = Set.univ := hgen
  -- the image of `S` topologically (hence, by discreteness, algebraically) generates `Gal(M''/F)`
  have hgenT1 : Subgroup.closure (↑(S.image ρ₁) : Set (↥M'' ≃ₐ[F] ↥M'')) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := hρ₁surj y
    have hxA : x ∈ _root_.closure
        (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) : Set (↥L ≃ₐ[F] ↥L)) := by
      rw [hgen']; exact Set.mem_univ x
    have h1 : ρ₁ x ∈ _root_.closure
        (ρ₁ '' (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) : Set (↥L ≃ₐ[F] ↥L))) :=
      image_closure_subset_closure_image hρ₁cont (Set.mem_image_of_mem ρ₁ hxA)
    have h2 : (ρ₁ '' (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) : Set (↥L ≃ₐ[F] ↥L)))
        = (↑(Subgroup.closure (↑(S.image ρ₁) : Set (↥M'' ≃ₐ[F] ↥M''))) :
          Set (↥M'' ≃ₐ[F] ↥M'')) := by
      rw [← Subgroup.coe_map, MonoidHom.map_closure]
      congr 1
      rw [Finset.coe_image]
    rw [h2, (isClosed_discrete _).closure_eq] at h1
    exact h1
  -- transport the generating set through the group isomorphism `e`
  have hgenT0 : Subgroup.closure
      (↑((S.image ρ₁).image e) : Set (Multiplicative (Fin (ℓ - 1) → ZMod 3))) = ⊤ := by
    have hmap : Subgroup.map e.toMonoidHom
        (Subgroup.closure (↑(S.image ρ₁) : Set (↥M'' ≃ₐ[F] ↥M''))) =
        Subgroup.closure (↑((S.image ρ₁).image e) :
          Set (Multiplicative (Fin (ℓ - 1) → ZMod 3))) := by
      rw [MonoidHom.map_closure]; congr 1; simp [Finset.coe_image]
    rw [hgenT1, Subgroup.map_top_of_surjective _ e.surjective] at hmap
    exact hmap.symm
  -- the elementary abelian rank bound closes the goal
  have hEA : (ℓ - 1) ≤ ((S.image ρ₁).image e).card := elem_abelian_rank (ℓ - 1) _ hgenT0
  have hc1 : ((S.image ρ₁).image e).card ≤ (S.image ρ₁).card := Finset.card_image_le
  have hc2 : (S.image ρ₁).card ≤ S.card := Finset.card_image_le
  omega
