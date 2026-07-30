-- Cited from: Ribes, L., Zalesskii, P. (2010). Profinite Groups, 2nd ed., Ergebnisse der Math. 40, Springer (infinite Galois correspondence for profinite groups; Frattini series and descending open-normal chains in infinite finitely generated pro-p groups). Combined with the maximal-unramified-pro-p setup of Definition A.3 (its finite quotients correspond to finite everywhere-unramified Galois p-group extensions of F).
-- Paper label: Definition A.3; [RZ10] Profinite Groups
-- This theorem has two parts. Part (a) [the infinite Galois correspondence for the open normal
-- subgroups of galUr 3 F: finite-Galois layers, finrank = index, Gal(layer) ≃ G⧸H, injectivity,
-- inclusion-reversing] is proved from Mathlib (see `UnramifiedProPTowerCorrespondence_partA`), using
-- Mathlib's infinite Galois (Krull) correspondence `FieldTheory/Galois/Infinite.lean` together with
-- the enabler `IsGalois F (maxUnramifiedProPExt 3 F)` (a compositum of Galois extensions is Galois).
-- Part (b) [the descending open-normal chain of index → ∞ in an infinite finitely generated
-- pro-3 quotient] is cited from prior published work, isolated as the
-- axiom `UnramifiedProPDescendingChain` (Ribes–Zalesskii, Profinite Groups), which this theorem
-- applies.
-- NL statement: For every number field F, letting G := galUr 3 F: (a) [infinite Galois correspondence] for every open normal subgroup H of G, the fixed field fixedFieldOf 3 F H is finite Galois over F with Module.finrank F (fixedFieldOf 3 F H) = H.index and a group isomorphism (fixedFieldOf 3 F H ≃ₐ[F] ·) ≃ (G ⧸ H), and the assignment H ↦ fixedFieldOf 3 F H is injective and inclusion-reversing on open normal subgroups; and (b) [descending chain] whenever a quotient Ḡ = G ⧸ N (for a closed normal N ≤ G) is infinite, topologically finitely generated and pro-3, there exists a family H : ℕ → Subgroup G of open normal subgroups with N ≤ H_j for all j, H_0 = ⊤, StrictAnti H, each (H_j).index finite, and Filter.Tendsto (fun j => (H_j).index) Filter.atTop Filter.atTop.
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.UnramifiedProPDescendingChain

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000

/-- **Part (a): the infinite Galois correspondence for `F^{ur,3}/F`, proved from Mathlib.**

For every number field `F`, writing `G := galUr 3 F` for the Galois group of the maximal everywhere-
unramified pro-`3` extension, for every open normal subgroup `H` of `G`:

* the fixed field `fixedFieldOf 3 F H` is finite-dimensional and Galois over `F`,
* `Module.finrank F (fixedFieldOf 3 F H) = H.index`,
* there is a group isomorphism `Gal(fixedFieldOf 3 F H / F) ≃* (G ⧸ H)`;

moreover `H ↦ fixedFieldOf 3 F H` is injective and inclusion-reversing on the open normal subgroups
of `G`. This is Mathlib's infinite fundamental theorem of Galois theory specialized to Definition
A.3; the enabler `IsGalois F (maxUnramifiedProPExt 3 F)` is the fact that a compositum of Galois
extensions is Galois. -/
theorem UnramifiedProPTowerCorrespondence_partA
    (F : Type*) [Field F] [NumberField F] :
    (∀ (H : Subgroup (galUr 3 F)) (hHnorm : H.Normal),
        IsOpen (H : Set (galUr 3 F)) →
          letI := hHnorm
          IsGalois F (fixedFieldOf 3 F H) ∧
            FiniteDimensional F (fixedFieldOf 3 F H) ∧
              Module.finrank F (fixedFieldOf 3 F H) = H.index ∧
                Nonempty
                  ((fixedFieldOf 3 F H ≃ₐ[F] fixedFieldOf 3 F H) ≃* (galUr 3 F ⧸ H))) ∧
      (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
          H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
            fixedFieldOf 3 F H₁ = fixedFieldOf 3 F H₂ → H₁ = H₂) ∧
      (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
          H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
            H₁ ≤ H₂ → fixedFieldOf 3 F H₂ ≤ fixedFieldOf 3 F H₁) := by
  -- Enabler: `F^{ur,3}/F` is Galois (compositum of finite Galois extensions).
  haveI hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    apply IntermediateField.normal_iSup (h := ?_)
    rintro ⟨E, hE⟩
    obtain ⟨hfd, hg, _, _⟩ := hE
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    haveI := hg
    infer_instance
  haveI hgal : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  refine ⟨?_, ?_, ?_⟩
  · -- (A1) fixed field of an open normal subgroup is a finite Galois layer with the right degree/iso
    intro H hHnorm hHopen
    haveI := hHnorm
    have hclosed : IsClosed (H : Set (galUr 3 F)) := H.isClosed_of_isOpen hHopen
    let Hc : ClosedSubgroup (galUr 3 F) := ⟨H, hclosed⟩
    have hff : (fixedFieldOf 3 F H).fixingSubgroup = H :=
      InfiniteGalois.fixingSubgroup_fixedField Hc
    -- finite-dimensionality + Galois of the layer, from the Krull correspondence
    have hfg : FiniteDimensional F (fixedFieldOf 3 F H) ∧ IsGalois F (fixedFieldOf 3 F H) := by
      rw [← InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (fixedFieldOf 3 F H), hff]
      exact ⟨hHopen, hHnorm⟩
    haveI hfdL := hfg.1
    haveI hgalL := hfg.2
    haveI hnormL : Normal F (fixedFieldOf 3 F H) := hgalL.to_normal
    -- restriction homomorphism G → Gal(layer/F)
    let φ : galUr 3 F →* ((fixedFieldOf 3 F H) ≃ₐ[F] (fixedFieldOf 3 F H)) :=
      AlgEquiv.restrictNormalHom (F := F) (K₁ := maxUnramifiedProPExt 3 F) (fixedFieldOf 3 F H)
    have hker : φ.ker = H :=
      (IntermediateField.restrictNormalHom_ker (fixedFieldOf 3 F H)).trans hff
    have hsurj : Function.Surjective φ :=
      AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := (fixedFieldOf 3 F H))
        (maxUnramifiedProPExt 3 F)
    -- iso  G ⧸ H ≃* Gal(layer/F)
    let e : (galUr 3 F ⧸ H) ≃* ((fixedFieldOf 3 F H) ≃ₐ[F] (fixedFieldOf 3 F H)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
    refine ⟨hgalL, hfdL, ?_, ⟨e.symm⟩⟩
    -- finrank = index
    have hcard : Nat.card ((fixedFieldOf 3 F H) ≃ₐ[F] (fixedFieldOf 3 F H))
        = Nat.card (galUr 3 F ⧸ H) := (Nat.card_congr e.toEquiv).symm
    rw [← IsGalois.card_aut_eq_finrank F (fixedFieldOf 3 F H), hcard, ← Subgroup.index_eq_card]
  · -- (A2) injectivity of  H ↦ fixedFieldOf 3 F H  on open normal subgroups
    intro H₁ H₂ _ ho1 _ ho2 heq
    have hc1 : IsClosed (H₁ : Set (galUr 3 F)) := H₁.isClosed_of_isOpen ho1
    have hc2 : IsClosed (H₂ : Set (galUr 3 F)) := H₂.isClosed_of_isOpen ho2
    let Hc1 : ClosedSubgroup (galUr 3 F) := ⟨H₁, hc1⟩
    let Hc2 : ClosedSubgroup (galUr 3 F) := ⟨H₂, hc2⟩
    have hff1 : (fixedFieldOf 3 F H₁).fixingSubgroup = H₁ :=
      InfiniteGalois.fixingSubgroup_fixedField Hc1
    have hff2 : (fixedFieldOf 3 F H₂).fixingSubgroup = H₂ :=
      InfiniteGalois.fixingSubgroup_fixedField Hc2
    calc H₁ = (fixedFieldOf 3 F H₁).fixingSubgroup := hff1.symm
      _ = (fixedFieldOf 3 F H₂).fixingSubgroup := by rw [heq]
      _ = H₂ := hff2
  · -- (A3) inclusion-reversing (unconditional antitonicity of the fixed-field map)
    intro H₁ H₂ _ _ _ _ hle
    exact IntermediateField.fixedField_le hle

/-- **Infinite Galois correspondence for `F^{ur,3}/F` plus descending-chain existence.**

For every number field `F`, writing `G := galUr 3 F` for the Galois group of the maximal
everywhere-unramified pro-`3` extension:

* **(a)** *(infinite fundamental theorem of Galois theory, specialized to Definition A.3).* For every
  open normal subgroup `H` of `G`, the fixed field `fixedFieldOf 3 F H` is a finite Galois extension
  of `F` with `Module.finrank F (fixedFieldOf 3 F H) = H.index` and a group isomorphism
  `Gal(fixedFieldOf 3 F H / F) ≃* (G ⧸ H)`; moreover `H ↦ fixedFieldOf 3 F H` is injective and
  inclusion-reversing on the open normal subgroups of `G`. **This part is proved from Mathlib**
  (`UnramifiedProPTowerCorrespondence_partA`).

* **(b)** *(descending chain in an infinite finitely generated pro-`3` quotient).* Whenever a quotient
  `Ḡ = G ⧸ N` (for a closed normal subgroup `N ≤ G`) is infinite, topologically finitely generated
  and pro-`3`, there is a chain `H : ℕ → Subgroup G` of open normal subgroups above `N` with
  `H 0 = ⊤`, strictly decreasing, each of finite index, whose indices tend to infinity. **This part
  is admitted from prior published work** via `UnramifiedProPDescendingChain` (Ribes–Zalesskii,
  *Profinite Groups*); the corresponding pro-`p` Frattini / lower-central series theory is not
  currently in Mathlib. -/
theorem UnramifiedProPTowerCorrespondence :
    ∀ (F : Type*) [Field F] [NumberField F],
      -- (a) infinite Galois correspondence for the open normal subgroups of `galUr 3 F`
      (∀ (H : Subgroup (galUr 3 F)) (hHnorm : H.Normal),
          IsOpen (H : Set (galUr 3 F)) →
            letI := hHnorm
            IsGalois F (fixedFieldOf 3 F H) ∧
              FiniteDimensional F (fixedFieldOf 3 F H) ∧
                Module.finrank F (fixedFieldOf 3 F H) = H.index ∧
                  Nonempty
                    ((fixedFieldOf 3 F H ≃ₐ[F] fixedFieldOf 3 F H) ≃* (galUr 3 F ⧸ H))) ∧
        -- injectivity of `H ↦ fixedFieldOf 3 F H` on open normal subgroups
        (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
            H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
              fixedFieldOf 3 F H₁ = fixedFieldOf 3 F H₂ → H₁ = H₂) ∧
        -- inclusion-reversing on open normal subgroups
        (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
            H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
              H₁ ≤ H₂ → fixedFieldOf 3 F H₂ ≤ fixedFieldOf 3 F H₁) ∧
        -- (b) descending open-normal chain of index → ∞ in an infinite f.g. pro-3 quotient
        (∀ (N : Subgroup (galUr 3 F)) (hNnorm : N.Normal),
            IsClosed (N : Set (galUr 3 F)) →
              letI := hNnorm
              Infinite (galUr 3 F ⧸ N) →
                TopFinitelyGenerated (galUr 3 F ⧸ N) →
                  IsProP 3 (galUr 3 F ⧸ N) →
                    ∃ H : ℕ → Subgroup (galUr 3 F),
                      (∀ j, (H j).Normal) ∧
                        (∀ j, IsOpen ((H j : Set (galUr 3 F)))) ∧
                          (∀ j, N ≤ H j) ∧
                            H 0 = ⊤ ∧
                              StrictAnti H ∧
                                (∀ j, 0 < (H j).index) ∧
                                  Filter.Tendsto (fun j => (H j).index)
                                    Filter.atTop Filter.atTop) := by
  intro F _ _
  obtain ⟨ha1, ha2, ha3⟩ := UnramifiedProPTowerCorrespondence_partA F
  exact ⟨ha1, ha2, ha3, UnramifiedProPDescendingChain F⟩
