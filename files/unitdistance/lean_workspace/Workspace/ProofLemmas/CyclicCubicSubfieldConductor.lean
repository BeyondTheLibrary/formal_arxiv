-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Chapter 3, especially Theorem 3.11; J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VI.
-- Paper label: Proposition A.11(i)
-- NL statement: For a rational prime r congruent to 1 mod 3, the cyclic cubic subfield of Q(zeta_r) has field conductor exactly r: it embeds into Q(zeta_m) precisely when r divides m.
--
-- The classical content
-- is Mathlib's cyclotomic Galois correspondence in
-- `Mathlib.NumberTheory.NumberField.Cyclotomic.Galois`
-- (`intermediateFieldEquivSubgroupChar` and
-- `mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd`).
import Mathlib
import Workspace.Types.CyclotomicCharacterFields

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields
open Complex IsCyclotomicExtension IsCyclotomicExtension.Rat

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

namespace Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof

/-- `zetaC a` is a power of `zetaC b` whenever `a ∣ b`. -/
theorem zetaC_pow_of_dvd (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    zetaC a = zetaC b ^ ((b : ℕ) / (a : ℕ)) := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  congr 1
  obtain ⟨k, hk⟩ := h
  have hr0 : (a : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hm0 : (b : ℂ) ≠ 0 := by exact_mod_cast b.pos.ne'
  have hkdiv : (b : ℕ) / (a : ℕ) = k := by rw [hk]; exact Nat.mul_div_cancel_left k a.pos
  rw [hkdiv]
  have hkc : (b : ℂ) = (a : ℂ) * (k : ℂ) := by exact_mod_cast hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hk
    exact_mod_cast this
  rw [hkc]
  field_simp

/-- Monotonicity of the concrete cyclotomic fields with respect to divisibility. -/
theorem cyclotomicField'_mono (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    cyclotomicField' a ≤ cyclotomicField' b := by
  unfold cyclotomicField'
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [zetaC_pow_of_dvd a b h]
  exact pow_mem (IntermediateField.subset_adjoin ℚ {zetaC b} rfl) _

/-- The subgroup of cubes in `(ℤ/rℤ)ˣ` is proper when `r ≡ 1 (mod 3)` is prime. -/
theorem cubes_range_ne_top (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1) :
    (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range ≠ ⊤ := by
  haveI : Fact (r : ℕ).Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : (3 : ℕ) ∣ Fintype.card (ZMod (r : ℕ))ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hr]; omega
  intro htop
  have hsurj : Function.Surjective (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ) :=
    MonoidHom.range_eq_top.mp htop
  have hinj : Function.Injective (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ) :=
    (Finite.injective_iff_surjective).mpr hsurj
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x = 1 := hinj (by simpa [powMonoidHom] using hx3)
  rw [hx1] at hx; simp at hx

/-- Restricting a subfield `S ≤ ℚ(ζ_N)` to `ℚ(ζ_N)` and lifting back recovers `S`. -/
theorem comap_val_roundtrip_gen (S : IntermediateField ℚ ℂ) (N : ℕ+)
    (hSN : S ≤ cyclotomicField' N) :
    IntermediateField.lift (S.comap (cyclotomicField' N).val) = S := by
  show (S.comap (cyclotomicField' N).val).map (cyclotomicField' N).val = S
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left]
  exact hSN

/-- The `ℚ`-algebra isomorphism `ℚ(ζ_a) ⊆ ℚ(ζ_N)  ≃  ℚ(ζ_a)` when `a ∣ N`. -/
noncomputable def comapValEquiv (a N : ℕ+) (haN : (a : ℕ) ∣ (N : ℕ)) :
    ↥((cyclotomicField' a).comap (cyclotomicField' N).val) ≃ₐ[ℚ] ↥(cyclotomicField' a) :=
  (IntermediateField.liftAlgEquiv _).trans
    (IntermediateField.equivOfEq
      (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN)))

/-- The cyclic cubic subfield of `ℚ(ζ_r)` is nontrivial (not equal to `ℚ`). -/
theorem cyclicCubicSubfield_ne_bot (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1) :
    cyclicCubicSubfield r hr hr3 ≠ ⊥ := by
  intro hbot
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    ((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom with hHdef
  have hbot' : IntermediateField.lift (IntermediateField.fixedField H) = ⊥ := hbot
  have hlbot : IntermediateField.lift (⊥ : IntermediateField ℚ ↥(cyclotomicField' r)) = ⊥ :=
    IntermediateField.map_bot _
  have hfixedbot : IntermediateField.fixedField H = ⊥ :=
    (IntermediateField.lift_inj _ _).mp (hbot'.trans hlbot.symm)
  have hHtop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hfixedbot,
      IntermediateField.fixingSubgroup_bot]
  have hf : Function.Surjective ⇑((galToUnits r).toMonoidHom) := (galToUnits r).surjective
  have hrange : (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range = ⊤ := by
    have hself := Subgroup.map_comap_eq_self_of_surjective hf
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range
    rw [← hHdef, hHtop, Subgroup.map_top_of_surjective _ hf] at hself
    exact hself.symm
  exact cubes_range_ne_top r hr hr3 hrange

/-- Key direction: if the cyclic cubic subfield embeds in `ℚ(ζ_m)`, then `r ∣ m`. -/
theorem hardDir (r m : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    (hle : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' m) : (r : ℕ) ∣ (m : ℕ) := by
  set N : ℕ+ := r * m with hN
  have hNcoe : (N : ℕ) = (r : ℕ) * (m : ℕ) := by rw [hN]; exact PNat.mul_coe r m
  have hrN : (r : ℕ) ∣ (N : ℕ) := by rw [hNcoe]; exact dvd_mul_right _ _
  have hmN : (m : ℕ) ∣ (N : ℕ) := by rw [hNcoe]; exact dvd_mul_left _ _
  haveI hER : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod (N : ℕ))ˣ) := inferInstance
  haveI iscr : IsCyclotomicExtension {(r : ℕ)} ℚ
      ↥((cyclotomicField' r).comap (cyclotomicField' N).val) :=
    IsCyclotomicExtension.equiv {(r : ℕ)} ℚ (↥(cyclotomicField' r)) (comapValEquiv r N hrN).symm
  haveI isgr : IsGalois ℚ ↥((cyclotomicField' r).comap (cyclotomicField' N).val) :=
    IsGalois.of_algEquiv (comapValEquiv r N hrN).symm
  haveI iscm : IsCyclotomicExtension {(m : ℕ)} ℚ
      ↥((cyclotomicField' m).comap (cyclotomicField' N).val) :=
    IsCyclotomicExtension.equiv {(m : ℕ)} ℚ (↥(cyclotomicField' m)) (comapValEquiv m N hmN).symm
  haveI isgm : IsGalois ℚ ↥((cyclotomicField' m).comap (cyclotomicField' N).val) :=
    IsGalois.of_algEquiv (comapValEquiv m N hmN).symm
  have hLr0 : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' r := IntermediateField.lift_le _
  have hLK : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' N :=
    le_trans hLr0 (cyclotomicField'_mono r N hrN)
  have hround_L : IntermediateField.lift
      ((cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val)
      = cyclicCubicSubfield r hr hr3 := comap_val_roundtrip_gen _ N hLK
  have hFL_ne : (cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val ≠ ⊥ := by
    intro hbot
    apply cyclicCubicSubfield_ne_bot r hr hr3
    rw [← hround_L, hbot, IntermediateField.lift_bot]
  set Φ := intermediateFieldEquivSubgroupChar (N : ℕ) (↥(cyclotomicField' N)) ℂ with hΦ
  have hΦL_ne : Φ ((cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val) ≠ ⊥ := by
    rw [← OrderIso.map_bot Φ]
    intro h
    exact hFL_ne (Φ.injective h)
  obtain ⟨χ, hχmem, hχ1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hΦL_ne
  have hLr : (cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val
      ≤ (cyclotomicField' r).comap (cyclotomicField' N).val :=
    (IntermediateField.gc_map_comap (cyclotomicField' N).val).monotone_u hLr0
  have hLm : (cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val
      ≤ (cyclotomicField' m).comap (cyclotomicField' N).val :=
    (IntermediateField.gc_map_comap (cyclotomicField' N).val).monotone_u hle
  have hχr : χ ∈ Φ ((cyclotomicField' r).comap (cyclotomicField' N).val) := Φ.monotone hLr hχmem
  have hχm : χ ∈ Φ ((cyclotomicField' m).comap (cyclotomicField' N).val) := Φ.monotone hLm hχmem
  have hiffr := @mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd (N : ℕ) _
    (↥(cyclotomicField' N)) _ _ _ ℂ _ _ _
    ((cyclotomicField' r).comap (cyclotomicField' N).val) (r : ℕ) _ isgr iscr hrN
  have hiffm := @mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd (N : ℕ) _
    (↥(cyclotomicField' N)) _ _ _ ℂ _ _ _
    ((cyclotomicField' m).comap (cyclotomicField' N).val) (m : ℕ) _ isgm iscm hmN
  rw [← hΦ] at hiffr hiffm
  have hcondr : χ.conductor ∣ (r : ℕ) := (hiffr χ).mp hχr
  have hcondm : χ.conductor ∣ (m : ℕ) := (hiffm χ).mp hχm
  have hcond1 : χ.conductor ≠ 1 := by
    intro h1
    apply hχ1
    have hft : χ.FactorsThrough 1 := by
      have hfc := DirichletCharacter.factorsThrough_conductor χ
      rwa [h1] at hfc
    exact (DirichletCharacter.factorsThrough_one_iff χ).mp hft
  have hcondeq : χ.conductor = (r : ℕ) := (hr.eq_one_or_self_of_dvd _ hcondr).resolve_left hcond1
  rw [← hcondeq]
  exact hcondm

end Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof

/-- **Proposition A.11(i).** For a rational prime `r ≡ 1 (mod 3)`, the cyclic cubic
subfield of `ℚ(ζ_r)` embeds into `ℚ(ζ_m)` iff `r ∣ m`; equivalently its field
conductor is exactly `r`. Proved from Mathlib's cyclotomic Galois correspondence. -/
theorem CyclicCubicSubfieldConductor (r : ℕ+) (hr : (r : ℕ).Prime)
    (hr3 : (r : ℕ) % 3 = 1) :
    ∀ m : ℕ+, cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' m ↔ (r : ℕ) ∣ (m : ℕ) := by
  intro m
  refine ⟨fun hle => ?_, fun hdvd => ?_⟩
  · exact Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof.hardDir r m hr hr3 hle
  · exact le_trans (IntermediateField.lift_le _)
      (Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof.cyclotomicField'_mono r m hdvd)
