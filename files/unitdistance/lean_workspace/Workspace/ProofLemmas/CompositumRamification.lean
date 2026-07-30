import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.InertiaLocal
import Workspace.ProofLemmas.CyclotomicTameDiscriminant
import Workspace.ProofLemmas.CyclicCubicSubfieldDegree
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.SublemmaCyclicCubicSubfieldNormal
import Workspace.ProofLemmas.SublemmaCompositumGalois
import Workspace.ProofLemmas.UnramifiedOutsideLevel

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields
open Workspace.ProofLemmas.InertiaLocal
open Workspace.ProofLemmas.CyclotomicTameDiscriminant

set_option maxHeartbeats 1000000

/-!
# Ramification in a compositum of cyclic cubic fields

The inertia group at `r i` in `M = ⨆_j L_j` is disjoint from `Gal(M/L_i)` (because it fixes every
`L_j`, `j ≠ i`, all of which are unramified at `r i`), so it has at most `[L_i : ℚ] = 3` elements;
it is also a subgroup of the elementary abelian `Gal(M/ℚ)` of order `3^ℓ` and nontrivial because
`r i` divides `disc M`.  Hence `e(P / r i) = 3` — and therefore `M/F` is unramified at every finite
prime for any cubic subfield `F ⊆ M` of discriminant `D²`.
-/

namespace Workspace.ProofLemmas.CompositumRamification

section Ram

variable {ℓ : ℕ}

/-- Abstract version: an automorphism fixing every member of a family generating `N` is trivial. -/
theorem eq_one_of_fixes_family' {N : Type*} [Field N] [Algebra ℚ N]
    {ι : Type*} (E : ι → IntermediateField ℚ N) (hE : (⨆ i, E i) = ⊤)
    (σ : N ≃ₐ[ℚ] N) (hσ : ∀ i, σ ∈ (E i).fixingSubgroup) :
    σ = 1 := by
  have hle : (⨆ i, E i) ≤ IntermediateField.fixedField (Subgroup.closure ({σ} : Set (N ≃ₐ[ℚ] N))) := by
    refine iSup_le fun i => ?_
    intro x hx
    refine (IntermediateField.mem_fixedField_iff _ x).mpr ?_
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
        simp only [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp (hσ i) x hx
    | one => rfl
    | mul a b _ _ ha hb => rw [AlgEquiv.mul_apply, hb, ha]
    | inv a _ ha =>
        have hinv : a⁻¹ (a x) = x := by simp
        rwa [ha] at hinv
  rw [hE] at hle
  ext x
  have hx : x ∈ IntermediateField.fixedField (Subgroup.closure ({σ} : Set (N ≃ₐ[ℚ] N))) :=
    hle (by trivial)
  simpa using
    (IntermediateField.mem_fixedField_iff _ x).mp hx σ (Subgroup.subset_closure rfl)

/-- **Ramification in a compositum of cubic fields** (abstract ambient field). -/
theorem ramificationIdx_eq_three (N : Type) [Field N] [NumberField N] [hgalN : IsGalois ℚ N]
    (E : Fin ℓ → IntermediateField ℚ N) (hE : (⨆ j, E j) = ⊤)
    (hdeg : ∀ j, Module.finrank ℚ ↥(E j) = 3)
    (hNdeg : Module.finrank ℚ N = 3 ^ ℓ)
    (i : Fin ℓ) (r : ℕ) (hr : r.Prime)
    (hother : ∀ j, j ≠ i →
      haveI : NumberField ↥(E j) := NumberField.of_module_finite ℚ ↥(E j)
      ¬ r ∣ (NumberField.discr ↥(E j)).natAbs)
    (hrN : r ∣ (NumberField.discr N).natAbs)
    (P : Ideal (𝓞 N)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {(r : ℤ)})]
    (hPne : P ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P = 3 := by
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  -- the inertia group is disjoint from the fixing subgroup of `E i`
  have hdisjoint : Disjoint (P.inertia (N ≃ₐ[ℚ] N)) ((E i).fixingSubgroup) := by
    rw [Subgroup.disjoint_def]
    intro σ hσI hσE
    refine eq_one_of_fixes_family' E hE σ ?_
    intro j
    by_cases hj : j = i
    · subst hj; exact hσE
    · exact inertia_le_fixingSubgroup_of_not_dvd_discr N (E j) r hr P hPne (hother j hj) hσI
  -- the index of that fixing subgroup is `3`
  have hindex : ((E i).fixingSubgroup).index = 3 := by
    have h1 := Subgroup.index_mul_card ((E i).fixingSubgroup)
    rw [IsGalois.card_fixingSubgroup_eq_finrank, IsGalois.card_aut_eq_finrank ℚ N] at h1
    have h2 : Module.finrank ℚ ↥(E i) * Module.finrank ↥(E i) N = Module.finrank ℚ N :=
      Module.finrank_mul_finrank ℚ _ N
    rw [hdeg i] at h2
    have h3 : 0 < Module.finrank ↥(E i) N := Module.finrank_pos
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right h3 h1
  -- hence `|I| ≤ 3`
  have hIle : Nat.card ↥(P.inertia (N ≃ₐ[ℚ] N)) ≤ 3 := by
    rw [← hindex]
    have hinj : Function.Injective
        (fun σ : ↥(P.inertia (N ≃ₐ[ℚ] N)) =>
          (QuotientGroup.mk (σ : N ≃ₐ[ℚ] N) : (N ≃ₐ[ℚ] N) ⧸ ((E i).fixingSubgroup))) := by
      rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      have h1 : σ⁻¹ * τ ∈ (E i).fixingSubgroup := by
        simpa [QuotientGroup.eq] using h
      have h2 : σ⁻¹ * τ ∈ P.inertia (N ≃ₐ[ℚ] N) := mul_mem (inv_mem hσ) hτ
      have h3 : σ⁻¹ * τ = 1 := Subgroup.disjoint_def.mp hdisjoint h2 h1
      have h4 : σ = τ := by
        have h5 := congrArg (fun g => σ * g) h3
        simpa [← mul_assoc] using h5.symm
      exact Subtype.ext h4
    exact Nat.card_le_card_of_injective _ hinj
  have hcardI := card_inertia_eq_ramificationIdx_int N (Ideal.span {(r : ℤ)}) hrbot P hPne
  have hdvd : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P ∣ 3 ^ ℓ := by
    rw [← hcardI, ← hNdeg, ← IsGalois.card_aut_eq_finrank ℚ N]
    exact Subgroup.card_subgroup_dvd_card _
  have hne1 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P ≠ 1 := by
    intro hcon
    refine (Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified N r hr
      ?_) hrN
    intro Q hQ
    obtain ⟨hQp, hQl⟩ := hQ
    haveI := hQp
    haveI := hQl
    have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hrbot Q
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) Q (N ≃ₐ[ℚ] N),
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) P (N ≃ₐ[ℚ] N)]
    exact hcon
  have hle3 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P ≤ 3 := by
    rw [← hcardI]; exact hIle
  rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd with ⟨k, hk, hkeq⟩
  match k, hk, hkeq with
  | 0, _, hkeq => exact absurd (by simpa using hkeq) hne1
  | 1, _, hkeq => simpa using hkeq
  | (n + 2), _, hkeq =>
      exfalso
      rw [hkeq] at hle3
      have : (9 : ℕ) ≤ 3 ^ (n + 2) := by
        calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end Ram

section Concrete

/-- The copies inside `M` of a family whose compositum is `M` generate `M`. -/
theorem iSup_comap_eq_top {ι : Type*} (E : ι → IntermediateField ℚ ℂ)
    (M : IntermediateField ℚ ℂ) (hM : M = ⨆ i, E i) :
    (⨆ i, (E i).comap M.val) = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro x _
  have hle : ∀ i, E i ≤ M := fun i => by rw [hM]; exact le_iSup E i
  have hsub0 : (⨆ i, E i) ≤ IntermediateField.lift (⨆ i, (E i).comap M.val) := by
    refine iSup_le fun i => ?_
    intro y hy
    refine ⟨⟨y, hle i hy⟩, ?_, rfl⟩
    exact le_iSup (fun i => (E i).comap M.val) i (show (⟨y, hle i hy⟩ : ↥M) ∈ (E i).comap M.val
      from hy)
  have hsub : M ≤ IntermediateField.lift (⨆ i, (E i).comap M.val) := hM.le.trans hsub0
  obtain ⟨z, hz, hzx⟩ := hsub x.2
  have hzex : z = x := Subtype.ext hzx
  rwa [← hzex]

/-- **`e = 3` at each `r i` in the compositum of the cyclic cubic fields.** -/
theorem ramificationIdx_compositum_eq_three (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ j, cyclicCubicSubfield (r j) (hp j) (hm j)) [NumberField ↥M]
    (hMdeg : Module.finrank ℚ ↥M = 3 ^ ℓ)
    (i : Fin ℓ)
    (P : Ideal (𝓞 ↥M)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {((r i : ℕ) : ℤ)})]
    (hPne : P ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {((r i : ℕ) : ℤ)}) P = 3 := by
  haveI hfdL : ∀ j, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r j) (hp j) (hm j)) :=
    fun j => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r j) (hp j) (hm j)]; norm_num)
  haveI hnfL : ∀ j, NumberField ↥(cyclicCubicSubfield (r j) (hp j) (hm j)) := fun j => ⟨⟩
  haveI hgalL : ∀ j, IsGalois ℚ ↥(cyclicCubicSubfield (r j) (hp j) (hm j)) :=
    fun j => SublemmaCyclicCubicSubfieldNormal (r j) (hp j) (hm j)
  haveI hgalM : IsGalois ℚ ↥M := by
    rw [hM]; exact (SublemmaCompositumGalois _).1
  have hle : ∀ j, cyclicCubicSubfield (r j) (hp j) (hm j) ≤ M := fun j => by
    rw [hM]; exact le_iSup (fun j => cyclicCubicSubfield (r j) (hp j) (hm j)) j
  haveI hnfE : ∀ j, NumberField ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val) :=
    fun j => NumberField.of_module_finite ℚ _
  have hdiscE : ∀ j, (NumberField.discr
      ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val)).natAbs = (r j : ℕ) ^ 2 := by
    intro j
    rw [discr_comap M (cyclicCubicSubfield (r j) (hp j) (hm j)) (hle j)]
    exact discr_cyclicCubicSubfield (r j) (hp j) (hm j)
  have hdegE : ∀ j, Module.finrank ℚ
      ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val) = 3 := by
    intro j
    rw [LinearEquiv.finrank_eq
      (comapEquiv M (cyclicCubicSubfield (r j) (hp j) (hm j)) (hle j)).toLinearEquiv]
    exact CyclicCubicSubfieldDegree (r j) (hp j) (hm j)
  refine ramificationIdx_eq_three ↥M (fun j => (cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val)
    (iSup_comap_eq_top _ M hM) hdegE ?_ i (r i : ℕ) (hp i) ?_ ?_ P hPne
  · exact hMdeg
  · intro j hj
    show ¬ (r i : ℕ) ∣
      (NumberField.discr ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val)).natAbs
    rw [hdiscE j]
    intro hdvd
    have hprime := (Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp ((hp i).dvd_of_dvd_pow hdvd)
    exact hj (hdist (by exact_mod_cast hprime.symm))
  · have h1 : (NumberField.discr ↥((cyclicCubicSubfield (r i) (hp i) (hm i)).comap M.val))
        ∣ NumberField.discr ↥M := NumberField.discr_dvd_discr _ _
    have h2 : (NumberField.discr
        ↥((cyclicCubicSubfield (r i) (hp i) (hm i)).comap M.val)).natAbs
        ∣ (NumberField.discr ↥M).natAbs := Int.natAbs_dvd_natAbs.mpr h1
    rw [hdiscE i] at h2
    exact dvd_trans (dvd_pow_self _ (by norm_num)) h2

end Concrete

/-- In a cubic Galois field, every prime dividing the discriminant is totally ramified. -/
theorem ramificationIdx_eq_three_of_dvd_discr (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (hdeg : Module.finrank ℚ F = 3) (r : ℕ) (hr : r.Prime)
    (hrA : r ∣ (NumberField.discr F).natAbs)
    (Q : Ideal (𝓞 F)) [hQp : Q.IsPrime] [hQl : Q.LiesOver (Ideal.span {(r : ℤ)})] (hQne : Q ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q = 3 := by
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  have hcardI := card_inertia_eq_ramificationIdx_int F (Ideal.span {(r : ℤ)}) hrbot Q hQne
  have hdvd : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ∣ 3 := by
    rw [← hcardI, ← hdeg, ← IsGalois.card_aut_eq_finrank ℚ F]
    exact Subgroup.card_subgroup_dvd_card _
  have hne1 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ≠ 1 := by
    intro hcon
    refine (Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified F r hr
      ?_) hrA
    intro R hR
    obtain ⟨hRp, hRl⟩ := hR
    haveI := hRp
    haveI := hRl
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) R (F ≃ₐ[ℚ] F),
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) Q (F ≃ₐ[ℚ] F)]
    exact hcon
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

/-- Every nonzero prime of `ℤ` is `(r)` for a rational prime `r`. -/
theorem exists_prime_span (I : Ideal ℤ) (hIp : I.IsPrime) (hIne : I ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ I = Ideal.span {(r : ℤ)} := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I)
  rw [ha] at hIp hIne ⊢
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hIne
    simp at hIne
  have hprime : Prime a := (Ideal.span_singleton_prime ha0).mp hIp
  refine ⟨a.natAbs, ?_, ?_⟩
  · rw [Int.prime_iff_natAbs_prime] at hprime
    exact hprime
  · rcases Int.natAbs_eq a with h | h
    · rw [← h]
    · rw [← neg_neg (a.natAbs : ℤ), ← h]
      exact (Ideal.span_singleton_neg a).symm

open Workspace.Types.SplittingRamification in
/-- **`M/F` is unramified at every finite prime**, for `F` a cubic Galois field of discriminant
`D²` inside the compositum `M`. -/
theorem unramified_compositum (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ) (hM : M = ⨆ j, cyclicCubicSubfield (r j) (hp j) (hm j))
    [NumberField ↥M] (hMdeg : Module.finrank ℚ ↥M = 3 ^ ℓ)
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] [Algebra F ↥M] [IsScalarTower ℚ F ↥M]
    (hFdeg : Module.finrank ℚ F = 3)
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (hFdisc : (NumberField.discr F).natAbs = (D : ℕ) ^ 2)
    (hMD : M ≤ cyclotomicField' D) :
    UnramifiedAtFinitePrimes F ↥M := by
  intro p hpne hpprime P hP
  obtain ⟨hPp, hPl⟩ := hP
  haveI := hPp
  haveI := hPl
  haveI : FiniteDimensional F ↥M := Module.Finite.right ℚ F ↥M
  haveI : Module.Finite (𝓞 F) (𝓞 ↥M) := IsIntegralClosure.finite (𝓞 F) F ↥M (𝓞 ↥M)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpne P
  haveI hup : (p.under ℤ).IsPrime := Ideal.IsPrime.under _ p
  have hupne : p.under ℤ ≠ ⊥ := by
    intro hcon
    exact hpne (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (S := 𝓞 F) (I := p) hcon)
  obtain ⟨q, hq, hqspan⟩ := exists_prime_span (p.under ℤ) hup hupne
  haveI hpq : p.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hqspan.symm⟩
  haveI hPq : P.LiesOver (Ideal.span {(q : ℤ)}) := by
    constructor
    rw [← hqspan, ← Ideal.under_under (A := ℤ) (B := 𝓞 F) (C := 𝓞 ↥M)]
    exact congrArg (Ideal.under ℤ) hPl.over
  have hqbot : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  have hinjF : Function.Injective (algebraMap (𝓞 F) (𝓞 ↥M)) :=
    FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 ↥M)
  have hinjZ : Function.Injective (algebraMap ℤ (𝓞 ↥M)) :=
    FaithfulSMul.algebraMap_injective ℤ (𝓞 ↥M)
  have htower : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) p * Ideal.ramificationIdx p P := by
    refine Ideal.ramificationIdx_algebra_tower (R := ℤ) (S := 𝓞 F) (T := 𝓞 ↥M) ?_ ?_ ?_
    · exact (Ideal.map_eq_bot_iff_of_injective hinjF).not.mpr hpne
    · exact (Ideal.map_eq_bot_iff_of_injective hinjZ).not.mpr hqbot
    · exact Ideal.map_le_of_le_comap (le_of_eq hPl.over)
  by_cases hqD : q ∣ (D : ℕ)
  · -- `q` is one of the `r i`
    have hex : ∃ i, (r i : ℕ) = q := by
      rw [hD] at hqD
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hqD
      exact ⟨i, ((Nat.prime_dvd_prime_iff_eq hq (hp i)).mp hi).symm⟩
    obtain ⟨i, hi⟩ := hex
    have hMram : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 3 := by
      subst hi
      exact ramificationIdx_compositum_eq_three ℓ hℓ r hp hm hdist M hM hMdeg i P hPne
    have hFram : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) p = 3 := by
      refine ramificationIdx_eq_three_of_dvd_discr F hFdeg q hq ?_ p hpne
      rw [hFdisc]
      exact dvd_trans hqD (dvd_pow_self _ (by norm_num))
    rw [hMram, hFram] at htower
    omega
  · -- `q` is unramified in `M`
    have hun := Workspace.ProofLemmas.UnramifiedOutsideLevel.unramified_of_not_dvd D M hMD q hq hqD
    have h1 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 :=
      hun P ⟨hPp, hPq⟩
    rw [h1] at htower
    have h2 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) p * Ideal.ramificationIdx p P = 1 :=
      htower.symm
    exact (Nat.eq_one_of_mul_eq_one_left h2)

end Workspace.ProofLemmas.CompositumRamification
