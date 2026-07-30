-- Cited from: J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed., Springer, 2008 (NSW08), and J. Neukirch, Algebraic Number Theory, Springer, 1999 (Neu99): a compositum of finitely many finite Galois everywhere-unramified extensions is everywhere unramified.
-- Paper label: Definitions A.2/A.3
--
-- `CompositumFamilyEverywhereUnramified`'s everywhere-unramifiedness conclusion
-- `EverywhereUnramified F (⨆ i ∈ s, i)` splits as:
--   * finite-primes half `UnramifiedAtFinitePrimes F (⨆ i ∈ s, i)` — cited as the arithmetic input
--     `Workspace.ProofLemmas.CompositumFamilyUnramifiedAtFinitePrimes` (the
--     Neukirch input; the closure of the finite-prime ramification index under compositum is not
--     currently in Mathlib);
--   * infinite-places half `IsUnramifiedAtInfinitePlaces F (⨆ i ∈ s, i)` — derived from Mathlib
--     via `IsUnramifiedAtInfinitePlaces_of_odd_finrank`, using the Mathlib-proved
--     `IsGalois F (⨆ i ∈ s, i)` (compositum of finite Galois extensions is Galois, `isGalois_biSup_of_finset`
--     below) together with the residual degree fact
--     `Workspace.ProofLemmas.CompositumFamilyOddFinrank` (the degree is a 3-power, hence odd).
-- The descent of everywhere-unramifiedness to an arbitrary finite subextension `E'` of the maximal
-- pro-3 extension is proved below from Mathlib (tower multiplicativity of ramification indices at
-- finite primes, and `IsUnramifiedAtInfinitePlaces.bot` at infinite places), together with a
-- finite-capture (compactness) argument realizing `E'` inside a finite sub-compositum.
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.SublemmaUnramifiedTransport
import Workspace.ProofLemmas.CompositumFamilyUnramifiedAtFinitePrimes
import Workspace.ProofLemmas.CompositumFamilyOddFinrank

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

/-- **Compositum of finite Galois extensions from the family is Galois over `F`.**
Generic helper with abstract index/field data so the elaborator never needs to whnf the heavy
`setOf`/coercion of the defining family; the compositum of finitely many finite Galois
subextensions is again Galois (normality via `IntermediateField.normal_iSup`, separability via
`IntermediateField.isSeparable_iSup`, collapsing the finite biSup with `iSup_subtype''`). -/
theorem isGalois_biSup_of_finset {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
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

/-- **The compositum of finitely many family members is everywhere unramified over `F`.**
Its everywhere-unramifiedness is split into (1) the finite-primes arithmetic input
`CompositumFamilyUnramifiedAtFinitePrimes` and (2) the infinite-places half derived from Mathlib's
`IsUnramifiedAtInfinitePlaces_of_odd_finrank`, using the Mathlib-proved `IsGalois F (⨆ i ∈ s, i)`
and the residual degree fact `CompositumFamilyOddFinrank`. -/
theorem CompositumFamilyEverywhereUnramified :
    ∀ (F : Type) [Field F] [NumberField F]
      (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E})
      [FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))],
      haveI : NumberField ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
        NumberField.of_module_finite (K := F)
          (L := ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))))
      EverywhereUnramified F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) := by
  intro F _ _ s _
  haveI : NumberField ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
    NumberField.of_module_finite (K := F)
      (L := ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))))
  haveI hgalM : IsGalois F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
    isGalois_biSup_of_finset
      (t := fun i : ↥{E : IntermediateField F (AlgebraicClosure F) | IsFiniteUnramifiedProPExt 3 F E} =>
        (i : IntermediateField F (AlgebraicClosure F))) s
      (by intro i; have h := i.2; rw [Set.mem_setOf_eq] at h; exact h.choose_spec.1)
  refine ⟨CompositumFamilyUnramifiedAtFinitePrimes F s, ?_⟩
  exact IsUnramifiedAtInfinitePlaces_of_odd_finrank (CompositumFamilyOddFinrank F s)

namespace SublemmaSubextUnramifiedAux

open Workspace.Types.SplittingRamification

/-- Descent of unramifiedness at finite primes to a subfield `E'' ≤ M`. -/
lemma descent_finite (F : Type) [Field F] [NumberField F]
    (E'' M : IntermediateField F (AlgebraicClosure F)) (hle : E'' ≤ M)
    [NumberField ↥E''] [NumberField ↥M]
    (hM : UnramifiedAtFinitePrimes F ↥M) :
    UnramifiedAtFinitePrimes F ↥E'' := by
  letI : Algebra ↥E'' ↥M := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥E'' ↥M :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  intro p hp hpp P hP
  obtain ⟨hP_prime, hP_lo⟩ := hP
  haveI : P.IsPrime := hP_prime
  haveI : P.LiesOver p := hP_lo
  -- a prime `Q` of `𝓞 M` lying over `P`
  obtain ⟨⟨Q, hQprime, hQlo⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver P (𝓞 ↥M)))
  haveI : Q.IsPrime := hQprime
  haveI : Q.LiesOver P := hQlo
  haveI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have hQmem : Q ∈ Ideal.primesOver p (𝓞 ↥M) := ⟨hQprime, inferInstance⟩
  have hram1 : Ideal.ramificationIdx p Q = 1 := hM p hp hpp Q hQmem
  have htower :
      Ideal.ramificationIdx p Q =
        Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q :=
    Ideal.ramificationIdx_algebra_tower' (R := 𝓞 F) (S := 𝓞 ↥E'') (T := 𝓞 ↥M) p P Q
  rw [hram1] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- Descent of unramifiedness at infinite places to a subfield `E'' ≤ M`. -/
lemma descent_inf (F : Type) [Field F] [NumberField F]
    (E'' M : IntermediateField F (AlgebraicClosure F)) (hle : E'' ≤ M)
    [NumberField ↥E''] [NumberField ↥M] [FiniteDimensional F ↥M]
    (hM : IsUnramifiedAtInfinitePlaces F ↥M) :
    IsUnramifiedAtInfinitePlaces F ↥E'' := by
  letI : Algebra ↥E'' ↥M := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥E'' ↥M :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  haveI : Module.Finite ↥E'' ↥M := Module.Finite.right F ↥E'' ↥M
  haveI : Algebra.IsAlgebraic ↥E'' ↥M := inferInstance
  exact IsUnramifiedAtInfinitePlaces.bot (k := F) (K := ↥E'') (F := ↥M)

end SublemmaSubextUnramifiedAux

/-- **Every finite subextension of the maximal everywhere-unramified pro-3 extension is
everywhere unramified over `F`.**  Proved from the residual compositum axiom by descent. -/
theorem SublemmaSubextUnramified :
    ∀ (F : Type) [Field F] [NumberField F]
      (E' : IntermediateField F (maxUnramifiedProPExt 3 F))
      [FiniteDimensional F E'],
      haveI : NumberField (E' : Type _) :=
        NumberField.of_module_finite (K := F) (L := (E' : Type _))
      Workspace.Types.SplittingRamification.EverywhereUnramified F (E' : Type _) := by
  intro F _ _ E' _
  haveI : NumberField (E' : Type _) :=
    NumberField.of_module_finite (K := F) (L := (E' : Type _))
  show EverywhereUnramified F (E' : Type _)
  -- realize `E'` as an intermediate field `E''` of `AlgebraicClosure F` via `ι = val`
  set E'' : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) E' with hE''
  have e : E' ≃ₐ[F] ↥E'' :=
    IntermediateField.equivMap E' (IntermediateField.val (maxUnramifiedProPExt 3 F))
  haveI : FiniteDimensional F ↥E'' := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : NumberField (↥E'' : Type _) :=
    NumberField.of_module_finite (K := F) (L := (↥E'' : Type _))
  -- `E'' ≤ maxUnramifiedProPExt 3 F`
  have hE''_le : E'' ≤ maxUnramifiedProPExt 3 F := by
    rw [hE'']
    calc IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) E'
          ≤ IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) ⊤ :=
          IntermediateField.map_mono _ le_top
      _ = (IntermediateField.val (maxUnramifiedProPExt 3 F)).fieldRange :=
          (AlgHom.fieldRange_eq_map _).symm
      _ = maxUnramifiedProPExt 3 F := IntermediateField.fieldRange_val _
  -- FINITE CAPTURE: `E''` sits inside a finite sub-compositum of the defining family.
  have hFG : E''.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨t, ht_fin, ht_eq⟩ := IntermediateField.fg_def.mp hFG
  have hcompact : IsCompactElement E'' :=
    ht_eq ▸ IntermediateField.adjoin_finite_isCompactElement (F := F) ht_fin
  -- `maxUnramifiedProPExt 3 F = ⨆ i : S, i`
  have hle_isup :
      E'' ≤ ⨆ i : ↥{E : IntermediateField F (AlgebraicClosure F) |
          IsFiniteUnramifiedProPExt 3 F E}, (i : IntermediateField F (AlgebraicClosure F)) := by
    have hKe : maxUnramifiedProPExt 3 F =
        ⨆ i : ↥{E : IntermediateField F (AlgebraicClosure F) |
          IsFiniteUnramifiedProPExt 3 F E}, (i : IntermediateField F (AlgebraicClosure F)) := by
      rw [maxUnramifiedProPExt, sSup_eq_iSup']
    rw [← hKe]; exact hE''_le
  obtain ⟨s, hs_le⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hcompact
      (fun i : ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E} => (i : IntermediateField F (AlgebraicClosure F)))
      hle_isup
  -- the finite compositum `M`
  set M : IntermediateField F (AlgebraicClosure F) :=
    ⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)) with hM_def
  have hE''_le_M : E'' ≤ M := hs_le
  haveI : FiniteDimensional F ↥M := by
    rw [hM_def]
    apply IntermediateField.finiteDimensional_iSup_of_finset'
    intro i _
    exact i.2.choose
  haveI : NumberField (↥M : Type _) :=
    NumberField.of_module_finite (K := F) (L := (↥M : Type _))
  -- `M` is everywhere unramified (residual axiom)
  have hEU_M : EverywhereUnramified F (↥M : Type _) :=
    CompositumFamilyEverywhereUnramified F s
  -- descend to `E''`
  have hEU_E'' : EverywhereUnramified F (↥E'' : Type _) :=
    ⟨SublemmaSubextUnramifiedAux.descent_finite F E'' M hE''_le_M hEU_M.1,
     SublemmaSubextUnramifiedAux.descent_inf F E'' M hE''_le_M hEU_M.2⟩
  -- transport back to `E'`
  exact (SublemmaUnramifiedTransport e).mpr hEU_E''
