import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.InertiaLocal
import Workspace.ProofLemmas.UnramifiedOutsideLevel
import Workspace.ProofLemmas.SublemmaCutOutFieldGalois
import Workspace.ProofLemmas.TameDifferent
import Workspace.ProofLemmas.CyclicCubicSubfieldDegree

/-!
# The tame conductor–discriminant computation for subfields of `ℚ(ζ_D)`, `D` squarefree

This file replaces the Artin-conductor input of the classical conductor–discriminant formula by an
inertia argument that works whenever the level is squarefree (so all ramification is tame).

Main results:

* `conductor_dvd_of_cutOutField_le` — if `cutOutField D χ ⊆ ℚ(ζ_m)` then `f(χ) ∣ m`
  (the Galois correspondence plus `DirichletCharacter.factorsThrough_iff_ker_unitsMap`);
* `le_cyclotomicField_of_not_dvd_discr` — a subfield of `ℚ(ζ_D)` unramified at `r ‖ D` already
  lies in `ℚ(ζ_{D/r})` (the inertia group at `r` *is* `Gal(ℚ(ζ_D)/ℚ(ζ_{D/r}))`);
* `not_pow_totient_dvd_discr` — `r^{φ(D)} ∤ |disc ℚ(ζ_D)|`, from Mathlib's discriminant formula;
* `natAbs_discr_cutOutField` — **`|disc(cutOutField D χ)| = D²`** for `D` squarefree, `f(χ) = D`
  and `[cutOutField D χ : ℚ] = 3`.
-/

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CyclotomicTameDiscriminant

open Workspace.ProofLemmas.InertiaLocal

/-- `ζ_a = ζ_b ^ (b / a)` for `a ∣ b`. -/
theorem zetaC_pow_of_dvd (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    zetaC a = zetaC b ^ ((b : ℕ) / (a : ℕ)) := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact b.pos.ne' hc
  have ha : ((a : ℕ) : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hcC : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [zetaC, zetaC, ← Complex.exp_nat_mul, hc, Nat.mul_div_cancel_left _ a.pos]
  congr 1
  push_cast
  field_simp

/-- `ℚ(ζ_a) ⊆ ℚ(ζ_b)` for `a ∣ b`. -/
theorem cyclotomicField'_mono (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    cyclotomicField' a ≤ cyclotomicField' b := by
  unfold cyclotomicField'
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [zetaC_pow_of_dvd a b h]
  exact pow_mem (IntermediateField.subset_adjoin ℚ {zetaC b} rfl) _

/-- If the field cut out by `chi` sits inside `ℚ(ζ_m)` then `chi` factors through level `m`;
in particular its conductor divides `m`. -/
theorem conductor_dvd_of_cutOutField_le (D m : ℕ+) (hmD : (m : ℕ) ∣ (D : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ))
    (h : cutOutField D chi ≤ cyclotomicField' m) :
    DirichletCharacter.conductor chi ∣ (m : ℕ) := by
  classical
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  set K := cyclotomicField' D with hK
  set H : Subgroup (↥K ≃ₐ[ℚ] ↥K) := (chi.toUnitHom.comp (galToUnits D).toMonoidHom).ker with hHdef
  -- `fixedField H` sits inside the copy of `ℚ(ζ_m)` inside `K`
  have hfix : IntermediateField.fixedField H ≤ (cyclotomicField' m).comap K.val := by
    intro x hx
    have hmem : (x : ℂ) ∈ cutOutField D chi := ⟨x, hx, rfl⟩
    exact h hmem
  -- every unit congruent to `1` mod `m` acts trivially on `ℚ(ζ_m)`
  have hker : (ZMod.unitsMap hmD).ker ≤ chi.toUnitHom.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    set σ : ↥K ≃ₐ[ℚ] ↥K := (galToUnits D).symm a with hσ
    have hgal : galToUnits D σ = a := by rw [hσ]; exact (galToUnits D).apply_symm_apply a
    have hzmem : zetaC m ∈ K :=
      cyclotomicField'_mono m D hmD (IntermediateField.mem_adjoin_simple_self ℚ _)
    set y : ↥K := ⟨zetaC m, hzmem⟩ with hy
    have hym : y ^ (m : ℕ) = 1 := by
      apply Subtype.ext
      show (zetaC m) ^ (m : ℕ) = 1
      exact (isPrimitiveRoot_zetaC m).pow_eq_one
    have hyD : y ^ (D : ℕ) = 1 := by
      obtain ⟨c, hc⟩ := hmD
      apply Subtype.ext
      show (zetaC m) ^ (D : ℕ) = 1
      rw [hc, pow_mul, (isPrimitiveRoot_zetaC m).pow_eq_one, one_pow]
    have hact : σ y = y ^ ((galToUnits D σ : ZMod (D : ℕ))).val :=
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (D : ℕ) ↥K σ hyD
    -- the exponent is `≡ 1 (mod m)`
    have hmod : ((a : ZMod (D : ℕ))).val % (m : ℕ) = 1 % (m : ℕ) := by
      have h1 : (ZMod.castHom hmD (ZMod (m : ℕ))) ((a : ZMod (D : ℕ))) = 1 := by
        have h0 := congrArg (fun u : (ZMod (m : ℕ))ˣ => (u : ZMod (m : ℕ))) ha
        simpa [ZMod.unitsMap, Units.coe_map] using h0
      have h2 : ((((a : ZMod (D : ℕ))).val : ℕ) : ZMod (m : ℕ)) = ((1 : ℕ) : ZMod (m : ℕ)) := by
        calc ((((a : ZMod (D : ℕ))).val : ℕ) : ZMod (m : ℕ))
            = ZMod.castHom hmD (ZMod (m : ℕ)) ((((a : ZMod (D : ℕ))).val : ℕ) : ZMod (D : ℕ)) :=
              (map_natCast _ _).symm
          _ = ZMod.castHom hmD (ZMod (m : ℕ)) ((a : ZMod (D : ℕ))) := by
              rw [ZMod.natCast_val, ZMod.cast_id]
          _ = 1 := h1
          _ = ((1 : ℕ) : ZMod (m : ℕ)) := by simp
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h2
    have hpow : ∀ k : ℕ, y ^ k = y ^ (k % (m : ℕ)) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k (m : ℕ)]
      rw [pow_add, pow_mul, hym, one_pow, one_mul]
    have hfixy : σ y = y := by
      rw [hact, hgal, hpow, hmod, ← hpow 1, pow_one]
    -- hence `σ` fixes the copy of `ℚ(ζ_m)` pointwise
    set S : IntermediateField ℚ ↥K :=
      IntermediateField.fixedField (Subgroup.closure ({σ} : Set (↥K ≃ₐ[ℚ] ↥K))) with hS
    have hyS : y ∈ S := by
      rw [hS]
      refine (IntermediateField.mem_fixedField_iff _ y).mpr ?_
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
          simp only [Set.mem_singleton_iff] at hx
          subst hx
          exact hfixy
      | one => rfl
      | mul a b _ _ ha' hb' => rw [AlgEquiv.mul_apply, hb', ha']
      | inv a _ ha' =>
          have hinv : a⁻¹ (a y) = y := by simp
          rwa [ha'] at hinv
    have hlift : cyclotomicField' m ≤ IntermediateField.lift S := by
      show IntermediateField.adjoin ℚ {zetaC m} ≤ _
      rw [IntermediateField.adjoin_le_iff]
      rintro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨y, hyS, rfl⟩
    have hEle : ((cyclotomicField' m).comap K.val) ≤ S := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hlift hx
      have hzex : z = x := Subtype.ext hzx
      rwa [← hzex]
    have hσfix : σ ∈ ((cyclotomicField' m).comap K.val).fixingSubgroup := by
      refine (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr ?_
      intro x hx
      have hxS := hEle hx
      rw [hS] at hxS
      exact (IntermediateField.mem_fixedField_iff _ x).mp hxS σ (Subgroup.subset_closure rfl)
    -- transfer along the Galois correspondence
    have hanti : ((cyclotomicField' m).comap K.val).fixingSubgroup
        ≤ (IntermediateField.fixedField H).fixingSubgroup := by
      intro τ hτ
      refine (IntermediateField.mem_fixingSubgroup_iff _ τ).mpr ?_
      intro x hx
      exact (IntermediateField.mem_fixingSubgroup_iff _ τ).mp hτ x (hfix hx)
    have hσH : σ ∈ H := by
      have := hanti hσfix
      rwa [IntermediateField.fixingSubgroup_fixedField] at this
    rw [hHdef, MonoidHom.mem_ker, MonoidHom.comp_apply] at hσH
    rw [← hgal]
    exact hσH
  have hfac : DirichletCharacter.FactorsThrough chi (m : ℕ) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hmD]
    exact hker
  exact DirichletCharacter.conductor_dvd_of_mem_conductorSet (χ := chi) hfac

section Inertia

open Workspace.ProofLemmas.InertiaLocal

/-- The `ℚ`-isomorphism `↥(S.comap K.val) ≃ₐ[ℚ] ↥S` for `S ≤ K`. -/
noncomputable def comapEquiv (K S : IntermediateField ℚ ℂ) (hS : S ≤ K) :
    ↥(S.comap K.val) ≃ₐ[ℚ] ↥S :=
  (IntermediateField.liftAlgEquiv _).trans
    (IntermediateField.equivOfEq (by
      show (S.comap K.val).map K.val = S
      rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left]
      exact hS))

theorem discr_comap (K S : IntermediateField ℚ ℂ) (hS : S ≤ K) [NumberField ↥S]
    [NumberField ↥(S.comap K.val)] :
    NumberField.discr ↥(S.comap K.val) = NumberField.discr ↥S :=
  NumberField.discr_eq_discr_of_algEquiv _ (comapEquiv K S hS)

/-- Abstract form of the inertia argument: if `S` and `E` are both unramified at `r` and the
fixing subgroup of `E` has exactly `e(P/r)` elements, then `S ≤ E`. -/
theorem le_of_inertia (K : Type) [Field K] [NumberField K] [hgal : IsGalois ℚ K]
    (r : ℕ) (hr : r.Prime)
    (P : Ideal (𝓞 K)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {(r : ℤ)})] (hPne : P ≠ ⊥)
    (E S : IntermediateField ℚ K)
    (hdS : haveI : NumberField ↥S := NumberField.of_module_finite ℚ ↥S
      ¬ r ∣ (NumberField.discr ↥S).natAbs)
    (hdE : haveI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
      ¬ r ∣ (NumberField.discr ↥E).natAbs)
    (hfin : Module.finrank ↥E K = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P) :
    S ≤ E := by
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  have hIS := inertia_le_fixingSubgroup_of_not_dvd_discr K S r hr P hPne hdS
  have hIE := inertia_le_fixingSubgroup_of_not_dvd_discr K E r hr P hPne hdE
  have hcardI := card_inertia_eq_ramificationIdx_int K (Ideal.span {(r : ℤ)}) hrbot P hPne
  have hcardE : Nat.card ↥(E.fixingSubgroup) = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank E, hfin]
  have hIeq := Subgroup.eq_of_le_of_card_ge hIE (by rw [hcardI, hcardE])
  have h1 : E.fixingSubgroup ≤ S.fixingSubgroup := by rw [← hIeq]; exact hIS
  have h2 := (IntermediateField.le_iff_le (E.fixingSubgroup) S).mpr h1
  rwa [IsGalois.fixedField_fixingSubgroup] at h2

/-- **Only the ramified primes can cut a subfield down.**  If the rational prime `r` (with
`D = r·m`, `r ∤ m`) does not divide `|disc S|` for a subfield `S ≤ ℚ(ζ_D)`, then already
`S ≤ ℚ(ζ_m)`. -/
theorem le_cyclotomicField_of_not_dvd_discr (D : ℕ+) (r : ℕ) (hr : r.Prime) (m : ℕ+)
    (hD : (D : ℕ) = r * (m : ℕ)) (hrm : ¬ r ∣ (m : ℕ))
    (S : IntermediateField ℚ ℂ) [NumberField ↥S] (hS : S ≤ cyclotomicField' D)
    (hdisc : ¬ r ∣ (NumberField.discr ↥S).natAbs) :
    S ≤ cyclotomicField' m := by
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  haveI hrf : Fact r.Prime := ⟨hr⟩
  have hmD : (m : ℕ) ∣ (D : ℕ) := ⟨r, by rw [hD]; ring⟩
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  obtain ⟨P, hPmax, hPlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ) (S := 𝓞 ↥(cyclotomicField' D))
      (Ideal.span {(r : ℤ)})
  haveI := hPmax
  haveI := hPlies
  haveI : P.IsPrime := hPmax.isPrime
  have hPne : P ≠ ⊥ := by
    intro hcon
    subst hcon
    exact hrbot (by simpa using hPlies.over)
  have hmDle : cyclotomicField' m ≤ cyclotomicField' D := cyclotomicField'_mono m D hmD
  haveI : NumberField ↥(S.comap (cyclotomicField' D).val) := NumberField.of_module_finite ℚ _
  haveI : NumberField ↥((cyclotomicField' m).comap (cyclotomicField' D).val) :=
    NumberField.of_module_finite ℚ _
  have hdS : ¬ r ∣ (NumberField.discr ↥(S.comap (cyclotomicField' D).val)).natAbs := by
    rw [discr_comap (cyclotomicField' D) S hS]; exact hdisc
  have hdE : ¬ r ∣
      (NumberField.discr ↥((cyclotomicField' m).comap (cyclotomicField' D).val)).natAbs := by
    rw [discr_comap (cyclotomicField' D) (cyclotomicField' m) hmDle]
    refine Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified
      ↥(cyclotomicField' m) r hr ?_
    exact Workspace.ProofLemmas.UnramifiedOutsideLevel.unramified_of_not_dvd m
      (cyclotomicField' m) le_rfl r hr hrm
  -- the degree computation
  have hcoprime : Nat.Coprime r (m : ℕ) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrm
  have htotD : (D : ℕ).totient = (r - 1) * (m : ℕ).totient := by
    rw [hD, Nat.totient_mul hcoprime, Nat.totient_prime hr]
  have hmpos : 0 < (m : ℕ).totient := Nat.totient_pos.mpr m.pos
  have hram : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P = r - 1 := by
    have h := IsCyclotomicExtension.Rat.ramificationIdx_eq (n := (D : ℕ)) (p := r) (k := 0)
      (m := (m : ℕ)) ↥(cyclotomicField' D) P (by rw [hD]; ring) hrm
    rw [h, pow_zero, one_mul]
  have hfin : Module.finrank ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
      ↥(cyclotomicField' D) = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P := by
    rw [hram]
    have h1 : Module.finrank ℚ ↥(cyclotomicField' D) = (D : ℕ).totient :=
      IsCyclotomicExtension.Rat.finrank (K := ↥(cyclotomicField' D)) (k := (D : ℕ))
    have h2 : Module.finrank ℚ ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
        = (m : ℕ).totient := by
      rw [LinearEquiv.finrank_eq
        (comapEquiv (cyclotomicField' D) (cyclotomicField' m) hmDle).toLinearEquiv]
      exact IsCyclotomicExtension.Rat.finrank (K := ↥(cyclotomicField' m)) (k := (m : ℕ))
    have h3 : Module.finrank ℚ ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
        * Module.finrank ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
            ↥(cyclotomicField' D) = Module.finrank ℚ ↥(cyclotomicField' D) :=
      Module.finrank_mul_finrank ℚ _ ↥(cyclotomicField' D)
    rw [h1, h2, htotD] at h3
    exact Nat.eq_of_mul_eq_mul_left hmpos (by linarith [h3])
  -- apply the abstract lemma
  have hle := @le_of_inertia ↥(cyclotomicField' D) _ _ (instIsGalois D) r hr P _ _ hPne
    ((cyclotomicField' m).comap (cyclotomicField' D).val) (S.comap (cyclotomicField' D).val)
    hdS hdE hfin
  intro x hx
  have hxK : x ∈ cyclotomicField' D := hS hx
  exact hle (show (⟨x, hxK⟩ : ↥(cyclotomicField' D)) ∈ S.comap (cyclotomicField' D).val from hx)

end Inertia

section DiscrBound

/-- `r ^ φ(D)` does not divide the discriminant of `ℚ(ζ_D)` when `r ‖ D`. -/
theorem not_pow_totient_dvd_discr (D : ℕ+) (r : ℕ) (hr : r.Prime) (m : ℕ+)
    (hD : (D : ℕ) = r * (m : ℕ)) (hrm : ¬ r ∣ (m : ℕ)) :
    ¬ r ^ ((D : ℕ).totient) ∣ (NumberField.discr ↥(cyclotomicField' D)).natAbs := by
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  set N := (D : ℕ).totient with hN
  set Q := ∏ p ∈ (D : ℕ).primeFactors, p ^ (N / (p - 1)) with hQ
  have hQdvd : Q ∣ (D : ℕ) ^ N := Nat.prod_primeFactors_pow_totient_ediv_dvd D.pos
  have hdisc : (NumberField.discr ↥(cyclotomicField' D)).natAbs = (D : ℕ) ^ N / Q :=
    IsCyclotomicExtension.Rat.natAbs_discr (D : ℕ) ↥(cyclotomicField' D)
  have hmul : (NumberField.discr ↥(cyclotomicField' D)).natAbs * Q = (D : ℕ) ^ N := by
    rw [hdisc]
    exact Nat.div_mul_cancel hQdvd
  -- `r` divides `Q`
  have hrmem : r ∈ (D : ℕ).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hr, ⟨(m : ℕ), hD⟩, D.pos.ne'⟩
  have hr1N : (r - 1) ∣ N := by
    rw [hN, ← Nat.totient_prime hr]
    exact Nat.totient_dvd_of_dvd ⟨(m : ℕ), hD⟩
  have hNpos : 0 < N := Nat.totient_pos.mpr D.pos
  have hr2 : 2 ≤ r := hr.two_le
  have hexp : 1 ≤ N / (r - 1) := by
    refine Nat.one_le_div_iff (by omega) |>.mpr ?_
    exact Nat.le_of_dvd hNpos hr1N
  have hrQ : r ∣ Q := by
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun p => p ^ (N / (p - 1))) hrmem)
    exact dvd_pow_self r (Nat.one_le_iff_ne_zero.mp hexp)
  -- conclude
  intro hcon
  obtain ⟨c, hc⟩ := hcon
  obtain ⟨d, hd⟩ := hrQ
  have hkey : r ^ (N + 1) ∣ (D : ℕ) ^ N := by
    refine ⟨c * d, ?_⟩
    rw [← hmul, hc, hd]
    ring
  rw [hD, mul_pow] at hkey
  have hcancel : r ∣ (m : ℕ) ^ N := by
    have h1 : r ^ N * r ∣ r ^ N * (m : ℕ) ^ N := by
      rw [← pow_succ]
      exact hkey
    exact (mul_dvd_mul_iff_left (pow_ne_zero N hr.ne_zero)).mp h1
  exact hrm (hr.dvd_of_dvd_pow hcancel)

end DiscrBound

/-- In a cubic Galois field, a ramified prime divides the discriminant to order at least `2`. -/
theorem sq_dvd_discr_of_dvd_discr (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (hdeg : Module.finrank ℚ F = 3) (r : ℕ) (hr : r.Prime)
    (hrA : r ∣ (NumberField.discr F).natAbs) :
    r ^ 2 ∣ (NumberField.discr F).natAbs := by
  have hrprime : Prime ((r : ℤ)) := Nat.prime_iff_prime_int.mp hr
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact hrprime
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  have hex : ∃ Q ∈ Ideal.primesOver (Ideal.span {(r : ℤ)}) (𝓞 F),
      Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact (Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified F r hr
      hcon) hrA
  obtain ⟨Q, hQmem, hQe⟩ := hex
  obtain ⟨hQp, hQl⟩ := hQmem
  haveI := hQp
  haveI := hQl
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hrbot Q
  have hcard := card_inertia_eq_ramificationIdx_int F (Ideal.span {(r : ℤ)}) hrbot Q hQne
  have hdvd3 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ∣ 3 := by
    rw [← hcard, ← hdeg, ← IsGalois.card_aut_eq_finrank ℚ F]
    exact Subgroup.card_subgroup_dvd_card _
  have he3 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q = 3 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd3 with h | h
    · exact absurd h hQe
    · exact h
  have h2 : Q ^ 2 ∣ differentIdeal ℤ (𝓞 F) := by
    have h := pow_sub_one_dvd_differentIdeal ℤ Q
      (Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q) hrbot
      (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
    rwa [he3] at h
  have h3 := map_dvd Ideal.absNorm h2
  rw [map_pow, NumberField.absNorm_differentIdeal F (𝓞 F),
    Ideal.absNorm_eq_pow_inertiaDeg Q hrprime, Int.natAbs_natCast, ← pow_mul] at h3
  refine dvd_trans ?_ h3
  refine pow_dvd_pow r ?_
  have := Ideal.inertiaDeg_pos (Ideal.span {(r : ℤ)}) Q
  omega

/-- A prime dividing the (squarefree) conductor really is ramified. -/
theorem dvd_discr_cutOutField (D : ℕ+) (chi : DirichletCharacter ℂ (D : ℕ))
    [NumberField ↥(cutOutField D chi)]
    (r : ℕ) (hr : r.Prime) (m : ℕ+) (hD : (D : ℕ) = r * (m : ℕ)) (hrm : ¬ r ∣ (m : ℕ))
    (hcond : DirichletCharacter.conductor chi = (D : ℕ)) :
    r ∣ (NumberField.discr ↥(cutOutField D chi)).natAbs := by
  by_contra hcon
  have hle := le_cyclotomicField_of_not_dvd_discr D r hr m hD hrm (cutOutField D chi)
    (IntermediateField.lift_le _) hcon
  have hdvd := conductor_dvd_of_cutOutField_le D m ⟨r, by rw [hD]; ring⟩ chi hle
  rw [hcond] at hdvd
  have hDm : (D : ℕ) ≤ (m : ℕ) := Nat.le_of_dvd m.pos hdvd
  have h2 : 2 * (m : ℕ) ≤ r * (m : ℕ) := Nat.mul_le_mul_right _ hr.two_le
  have hmpos := m.pos
  omega

/-- **Discriminant of the cubic field cut out by a character of squarefree conductor `D`.** -/
theorem natAbs_discr_cutOutField (D : ℕ+) (chi : DirichletCharacter ℂ (D : ℕ))
    [NumberField ↥(cutOutField D chi)]
    (hsq : Squarefree (D : ℕ))
    (hcond : DirichletCharacter.conductor chi = (D : ℕ))
    (hdeg : Module.finrank ℚ ↥(cutOutField D chi) = 3) :
    (NumberField.discr ↥(cutOutField D chi)).natAbs = (D : ℕ) ^ 2 := by
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  haveI hgal : IsGalois ℚ ↥(cutOutField D chi) := SublemmaCutOutFieldGalois D chi
  have hFle : cutOutField D chi ≤ cyclotomicField' D := IntermediateField.lift_le _
  have hApos : (NumberField.discr ↥(cutOutField D chi)).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact NumberField.discr_ne_zero _
  haveI : NumberField ↥((cutOutField D chi).comap (cyclotomicField' D).val) :=
    NumberField.of_module_finite ℚ _
  have hdiscF' : (NumberField.discr ↥((cutOutField D chi).comap (cyclotomicField' D).val)).natAbs
      = (NumberField.discr ↥(cutOutField D chi)).natAbs := by
    rw [discr_comap (cyclotomicField' D) (cutOutField D chi) hFle]
  -- degrees
  have h3q : 3 * Module.finrank ↥((cutOutField D chi).comap (cyclotomicField' D).val)
      ↥(cyclotomicField' D) = (D : ℕ).totient := by
    have h1 : Module.finrank ℚ ↥(cyclotomicField' D) = (D : ℕ).totient :=
      IsCyclotomicExtension.Rat.finrank (K := ↥(cyclotomicField' D)) (k := (D : ℕ))
    have h2 : Module.finrank ℚ ↥((cutOutField D chi).comap (cyclotomicField' D).val) = 3 := by
      rw [LinearEquiv.finrank_eq
        (comapEquiv (cyclotomicField' D) (cutOutField D chi) hFle).toLinearEquiv]
      exact hdeg
    have h3 := Module.finrank_mul_finrank ℚ
      ↥((cutOutField D chi).comap (cyclotomicField' D).val) ↥(cyclotomicField' D)
    rw [h1, h2] at h3
    exact h3
  -- the tower divisibility
  have hAq : (NumberField.discr ↥(cutOutField D chi)).natAbs
      ^ (Module.finrank ↥((cutOutField D chi).comap (cyclotomicField' D).val)
          ↥(cyclotomicField' D))
      ∣ (NumberField.discr ↥(cyclotomicField' D)).natAbs := by
    have htow := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      ↥((cutOutField D chi).comap (cyclotomicField' D).val)
      (𝓞 ↥((cutOutField D chi).comap (cyclotomicField' D).val))
      ↥(cyclotomicField' D) (𝓞 ↥(cyclotomicField' D))
    rw [hdiscF'] at htow
    exact ⟨_, by rw [htow]; ring⟩
  -- compare factorisations
  refine Nat.eq_of_factorization_eq hApos (by positivity) (fun p => ?_)
  by_cases hp : p.Prime
  · by_cases hpD : p ∣ (D : ℕ)
    · -- `p` is one of the (simple) prime factors of `D`
      obtain ⟨m, hm⟩ := hpD
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hm; exact absurd hm D.pos.ne'
        · exact h
      set m' : ℕ+ := ⟨m, hmpos⟩ with hm'
      have hD : (D : ℕ) = p * (m' : ℕ) := hm
      have hm'm : (m' : ℕ) = m := rfl
      have hpm : ¬ p ∣ (m' : ℕ) := by
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        have hpp : p * p ∣ (D : ℕ) := by
          refine ⟨c, ?_⟩
          rw [hD, hm'm] at *
          rw [hc]
          ring
        exact hp.not_isUnit (hsq p hpp)
      -- lower bound
      have hlow : p ^ 2 ∣ (NumberField.discr ↥(cutOutField D chi)).natAbs :=
        sq_dvd_discr_of_dvd_discr ↥(cutOutField D chi) hdeg p hp
          (dvd_discr_cutOutField D chi p hp m' hD hpm hcond)
      -- upper bound
      have hup : ¬ p ^ 3 ∣ (NumberField.discr ↥(cutOutField D chi)).natAbs := by
        intro hc3
        refine not_pow_totient_dvd_discr D p hp m' hD hpm ?_
        refine dvd_trans ?_ hAq
        rw [← h3q, pow_mul]
        exact pow_dvd_pow_of_dvd hc3 _
      have hfp : (NumberField.discr ↥(cutOutField D chi)).natAbs.factorization p = 2 := by
        have h1 := (Nat.Prime.pow_dvd_iff_le_factorization hp hApos).mp hlow
        have h2 : ¬ (3 ≤ (NumberField.discr ↥(cutOutField D chi)).natAbs.factorization p) := by
          intro hc
          exact hup ((Nat.Prime.pow_dvd_iff_le_factorization hp hApos).mpr hc)
        omega
      have hD1 : (D : ℕ).factorization p = 1 := by
        have h1 : 1 ≤ (D : ℕ).factorization p :=
          (Nat.Prime.dvd_iff_one_le_factorization hp D.pos.ne').mp ⟨m, hm⟩
        have h2 := hsq.natFactorization_le_one p
        omega
      rw [hfp, Nat.factorization_pow]
      simp only [Finsupp.smul_apply, smul_eq_mul, hD1]
    · -- `p ∤ D`: unramified, so it divides neither side
      have h1 : (NumberField.discr ↥(cutOutField D chi)).natAbs.factorization p = 0 := by
        refine Nat.factorization_eq_zero_of_not_dvd ?_
        refine Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified
          ↥(cutOutField D chi) p hp ?_
        exact Workspace.ProofLemmas.UnramifiedOutsideLevel.unramified_of_not_dvd D
          (cutOutField D chi) hFle p hp hpD
      have h2 : ((D : ℕ) ^ 2).factorization p = 0 := by
        rw [Nat.factorization_pow]
        simp only [Finsupp.smul_apply, smul_eq_mul]
        rw [Nat.factorization_eq_zero_of_not_dvd hpD]
      rw [h1, h2]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
      Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **The discriminant of the cyclic cubic subfield of `ℚ(ζ_r)` is `r²`.** -/
theorem discr_cyclicCubicSubfield (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    [NumberField ↥(cyclicCubicSubfield r hr hr3)] :
    (NumberField.discr ↥(cyclicCubicSubfield r hr hr3)).natAbs = (r : ℕ) ^ 2 := by
  haveI : Fact ((r : ℕ).Prime) := ⟨hr⟩
  have hle : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' r := IntermediateField.lift_le _
  letI : Algebra ↥(cyclicCubicSubfield r hr hr3) ↥(cyclotomicField' r) :=
    (IntermediateField.inclusion hle).toAlgebra
  have hdeg : Module.finrank ℚ ↥(cyclicCubicSubfield r hr hr3) = 3 :=
    CyclicCubicSubfieldDegree r hr hr3
  have h := Workspace.ProofLemmas.TameDifferent.natAbs_discr_subfield (r : ℕ)
    ↥(cyclotomicField' r) ↥(cyclicCubicSubfield r hr hr3)
  rw [hdeg] at h
  simpa using h

end Workspace.ProofLemmas.CyclotomicTameDiscriminant
