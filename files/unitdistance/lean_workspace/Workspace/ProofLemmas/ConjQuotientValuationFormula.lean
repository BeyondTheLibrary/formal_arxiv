import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.AdicValuationEqNegCount
import Workspace.ProofLemmas.ConjAutSpanSingletonCountSwap

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

-- reconciliation: multiplicity = FractionalIdeal.count of coeIdeal (proved)
private theorem recon (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (multiplicity v.asIdeal I : ℤ) = FractionalIdeal.count K v (↑I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.count_coe K v hI]
  norm_cast
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors v.irreducible hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]
  congr 1
  exact normalize_eq _

-- STEP A: count of A_δ at the prime P w0 (using distinctness prop 2).
private theorem countAδ_P {m : ℕ} (K : Type*) [Field K] [NumberField K]
    (P Pc : Fin m → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)))
    (δ : Fin m → Bool) (w0 : Fin m) :
    FractionalIdeal.count K (P w0)
        (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = (if δ w0 then 1 else 0 : ℤ) := by
  classical
  have hprodne : ∀ t : Fin m, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal)
      : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro t
    rw [FractionalIdeal.coeIdeal_ne_zero]
    by_cases h : δ t
    · simp only [h, if_true]; exact (P t).ne_bot
    · simp only [h, if_false]; exact (Pc t).ne_bot
  have hPne : ∀ t, t ≠ w0 → (P t) ≠ (P w0) := by
    intro t ht hc
    apply ht
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl w0) := by
      simp only [Sum.elim_inl]; exact congrArg _ hc
    exact Sum.inl_injective (hinj hh)
  have hPcne : ∀ t, (Pc t) ≠ (P w0) := by
    intro t hc
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl w0) := by
      simp only [Sum.elim_inr, Sum.elim_inl]; exact congrArg _ hc
    exact Sum.inr_ne_inl (hinj hh)
  have hcoe : (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ t, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (𝓞 K)⁰ K, map_prod]
    simp only [FractionalIdeal.coeIdealHom_apply]
  rw [hcoe, FractionalIdeal.count_prod K (P w0) Finset.univ _ (fun t _ => hprodne t),
    Finset.sum_eq_single w0]
  · by_cases h : δ w0
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_pos rfl]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_neg (hPcne w0)]
  · intro t _ hts
    by_cases h : δ t
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_neg (hPne t hts)]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_neg (hPcne t)]
  · intro hc; exact absurd (Finset.mem_univ w0) hc

-- helper: spanSingleton of a mk' as a quotient of coeIdeals of principal ideals
private theorem span_mk' (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) (s0 : (𝓞 K)⁰) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K a s0)
      = (↑(Ideal.span {a}) : FractionalIdeal (𝓞 K)⁰ K) *
        (↑(Ideal.span {(s0 : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
    IsFractionRing.mk'_eq_div, div_eq_mul_inv]

-- STEP A: count of A_δ at the prime Pc w0.
private theorem countAδ_Pc {m : ℕ} (K : Type*) [Field K] [NumberField K]
    (P Pc : Fin m → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)))
    (δ : Fin m → Bool) (w0 : Fin m) :
    FractionalIdeal.count K (Pc w0)
        (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = (if δ w0 then 0 else 1 : ℤ) := by
  classical
  have hprodne : ∀ t : Fin m, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal)
      : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro t
    rw [FractionalIdeal.coeIdeal_ne_zero]
    by_cases h : δ t
    · simp only [if_pos h]; exact (P t).ne_bot
    · simp only [if_neg h]; exact (Pc t).ne_bot
  have hPcne : ∀ t, t ≠ w0 → (Pc t) ≠ (Pc w0) := by
    intro t ht hc
    apply ht
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr w0) := by
      simp only [Sum.elim_inr]; exact congrArg _ hc
    exact Sum.inr_injective (hinj hh)
  have hPne : ∀ t, (P t) ≠ (Pc w0) := by
    intro t hc
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr w0) := by
      simp only [Sum.elim_inr, Sum.elim_inl]; exact congrArg _ hc
    exact Sum.inl_ne_inr (hinj hh)
  have hcoe : (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ t, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (𝓞 K)⁰ K, map_prod]
    simp only [FractionalIdeal.coeIdealHom_apply]
  rw [hcoe, FractionalIdeal.count_prod K (Pc w0) Finset.univ _ (fun t _ => hprodne t),
    Finset.sum_eq_single w0]
  · by_cases h : δ w0
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_neg (hPne w0)]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_pos rfl]
  · intro t _ hts
    by_cases h : δ t
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_neg (hPne t)]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_neg (hPcne t hts)]
  · intro hc; exact absurd (Finset.mem_univ w0) hc

-- general multiplicity transport under a ring equiv
private theorem multMap {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (p I : Ideal R) :
    multiplicity (Ideal.map e p) (Ideal.map e I) = multiplicity p I := by
  have hmapdvd : ∀ (f : R ≃+* R) {J K : Ideal R},
      J ∣ K → Ideal.map f J ∣ Ideal.map f K := by
    rintro f J K ⟨L, rfl⟩
    exact ⟨Ideal.map f L, Ideal.map_mul f J L⟩
  have hcancel : ∀ J : Ideal R, Ideal.map e.symm (Ideal.map e J) = J := by
    intro J
    rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ e.bijective]
  have hdvd : ∀ n : ℕ, (Ideal.map e p) ^ n ∣ (Ideal.map e I) ↔ p ^ n ∣ I := by
    intro n
    rw [← Ideal.map_pow]
    constructor
    · intro h
      have h2 := hmapdvd e.symm h
      rwa [hcancel, hcancel] at h2
    · exact fun h => hmapdvd e h
  have hemul : emultiplicity (Ideal.map e p) (Ideal.map e I) = emultiplicity p I := by
    rw [emultiplicity_eq_emultiplicity_iff]
    exact hdvd
  unfold multiplicity
  rw [hemul]

-- STEP A: count of A_δ at an off-family prime = 0.
private theorem countAδ_off {m : ℕ} (K : Type*) [Field K] [NumberField K]
    (P Pc : Fin m → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (δ : Fin m → Bool) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hw : ∀ t, w ≠ P t ∧ w ≠ Pc t) :
    FractionalIdeal.count K w
        (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  have hprodne : ∀ t : Fin m, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal)
      : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro t
    rw [FractionalIdeal.coeIdeal_ne_zero]
    by_cases h : δ t
    · simp only [if_pos h]; exact (P t).ne_bot
    · simp only [if_neg h]; exact (Pc t).ne_bot
  have hcoe : (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ t, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (𝓞 K)⁰ K, map_prod]
    simp only [FractionalIdeal.coeIdealHom_apply]
  rw [hcoe, FractionalIdeal.count_prod K w Finset.univ _ (fun t _ => hprodne t)]
  apply Finset.sum_eq_zero
  intro t _
  by_cases h : δ t
  · simp only [if_pos h]
    rw [FractionalIdeal.count_maximal, if_neg (fun hc => (hw t).1 hc.symm)]
  · simp only [if_neg h]
    rw [FractionalIdeal.count_maximal, if_neg (fun hc => (hw t).2 hc.symm)]

theorem ConjQuotientValuationFormula (d : AdmissibleDatum)
    (P Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
    (bidx : Fin (d.t * deg d) → Fin d.t)
    (hfam :
      (∀ s, Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) (P s).asIdeal
              = (Pc s).asIdeal ∧ (Pc s).asIdeal ≠ (P s).asIdeal) ∧
      Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)) ∧
      (∀ s, (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (∀ b, multiplicity (P s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0) ∧
            (∀ b, multiplicity (Pc s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0)) ∧
      (∀ (I : Ideal (𝓞 d.K)) (s : Fin (d.t * deg d)),
          multiplicity (P s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (Pc s).asIdeal I ∧
          multiplicity (Pc s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (P s).asIdeal I))
    (η ε : Fin (d.t * deg d) → Bool)
    (α : d.K) (hα : α ≠ 0)
    (hgen : FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α =
      (↑(∏ s, if ε s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K) *
      (↑(∏ s, if η s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) :
    (∀ s, (P s).valuation d.K (α / conjAut d.h_adjoin α)
            = WithZero.exp (-(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) ∧
          (Pc s).valuation d.K (α / conjAut d.h_adjoin α)
            = WithZero.exp (2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
          (∀ s, w ≠ P s ∧ w ≠ Pc s) → w.valuation d.K (α / conjAut d.h_adjoin α) = 1) := by
  classical
  obtain ⟨hswap, hinj, hram, htransfam⟩ := hfam
  set c' := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hc'
  have hcα0 : conjAut d.h_adjoin α ≠ 0 :=
    (map_ne_zero_iff _ (conjAut d.h_adjoin).injective).mpr hα
  have hquot0 : α / conjAut d.h_adjoin α ≠ 0 := div_ne_zero hα hcα0
  have hprodne : ∀ (δ : Fin (d.t * deg d) → Bool),
      (∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) ≠ 0 := by
    intro δ
    rw [Finset.prod_ne_zero_iff]
    intro t _
    by_cases h : δ t
    · simp only [if_pos h]; exact (P t).ne_bot
    · simp only [if_neg h]; exact (Pc t).ne_bot
  -- count of span(α/cα) at w = count(span α) - count(span(conjAut α))
  have hcountq : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
      FractionalIdeal.count d.K w
          (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (α / conjAut d.h_adjoin α))
        = FractionalIdeal.count d.K w (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α)
          - FractionalIdeal.count d.K w
              (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (conjAut d.h_adjoin α)) := by
    intro w
    rw [show FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (α / conjAut d.h_adjoin α)
          = FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α *
            (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (conjAut d.h_adjoin α))⁻¹ from by
        rw [FractionalIdeal.spanSingleton_inv,
          FractionalIdeal.spanSingleton_mul_spanSingleton, ← div_eq_mul_inv],
      FractionalIdeal.count_mul d.K w
        (by rwa [FractionalIdeal.spanSingleton_ne_zero_iff])
        (inv_ne_zero (by rwa [FractionalIdeal.spanSingleton_ne_zero_iff])),
      FractionalIdeal.count_inv]
    ring
  -- count of span α at w = count(↑A_ε) - count(↑A_η)
  have hcountα : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
      FractionalIdeal.count d.K w (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α)
        = FractionalIdeal.count d.K w
            (↑(∏ t, if ε t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 d.K)⁰ d.K)
          - FractionalIdeal.count d.K w
            (↑(∏ t, if η t then (P t).asIdeal else (Pc t).asIdeal)) := by
    intro w
    rw [hgen, FractionalIdeal.count_mul d.K w
        ((FractionalIdeal.coeIdeal_ne_zero).mpr (hprodne ε))
        (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).mpr (hprodne η))),
      FractionalIdeal.count_inv]
    ring
  refine ⟨fun s => ⟨?_, ?_⟩, ?_⟩
  · -- (P s) valuation
    rw [AdicValuationEqNegCount d.K (P s) (α / conjAut d.h_adjoin α) hquot0, hcountq (P s),
      hcountα (P s), countAδ_P d.K P Pc hinj ε s, countAδ_P d.K P Pc hinj η s,
      ConjAutSpanSingletonCountSwap d (Pc s) (P s) α hα (fun I => (htransfam I s).1),
      hcountα (Pc s), countAδ_Pc d.K P Pc hinj ε s, countAδ_Pc d.K P Pc hinj η s]
    congr 1
    cases ε s <;> cases η s <;> simp <;> ring
  · -- (Pc s) valuation
    rw [AdicValuationEqNegCount d.K (Pc s) (α / conjAut d.h_adjoin α) hquot0, hcountq (Pc s),
      hcountα (Pc s), countAδ_Pc d.K P Pc hinj ε s, countAδ_Pc d.K P Pc hinj η s,
      ConjAutSpanSingletonCountSwap d (P s) (Pc s) α hα (fun I => (htransfam I s).2),
      hcountα (P s), countAδ_P d.K P Pc hinj ε s, countAδ_P d.K P Pc hinj η s]
    congr 1
    cases ε s <;> cases η s <;> simp <;> ring
  · -- off-family
    intro w hw
    have hwne : w.asIdeal ≠ ⊥ := w.ne_bot
    haveI hwp : w.asIdeal.IsPrime := w.isPrime
    -- `conjAut` is an involution on the field `d.K`.
    have hinvfield : ∀ y : d.K, conjAut d.h_adjoin (conjAut d.h_adjoin y) = y := by
      set iota := d.h_adjoin.choose with hiota
      have hsqι : iota ^ 2 = -1 := d.h_adjoin.choose_spec.1
      have hadjι : IntermediateField.adjoin d.L {iota} = ⊤ := d.h_adjoin.choose_spec.2
      have hint : IsIntegral d.L iota := by
        refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
        · monicity!
        · simp [hsqι]
      have halg : IsAlgebraic d.L iota := hint.isAlgebraic
      have hcι2 : (conjAut d.h_adjoin iota) ^ 2 = -1 := by
        rw [← map_pow, hsqι, map_neg, map_one]
      have hcases : conjAut d.h_adjoin iota = iota ∨ conjAut d.h_adjoin iota = -iota := by
        have hfac : (conjAut d.h_adjoin iota - iota) * (conjAut d.h_adjoin iota + iota) = 0 := by
          have hz : (conjAut d.h_adjoin iota) ^ 2 - iota ^ 2 = 0 := by rw [hcι2, hsqι]; ring
          linear_combination hz
        rcases mul_eq_zero.mp hfac with hh | hh
        · left; exact sub_eq_zero.mp hh
        · right; linear_combination hh
      have hinvι : conjAut d.h_adjoin (conjAut d.h_adjoin iota) = iota := by
        rcases hcases with hh | hh
        · rw [hh, hh]
        · rw [hh, map_neg, hh, neg_neg]
      have hadjalg : Algebra.adjoin d.L {iota} = ⊤ :=
        Algebra.adjoin_eq_top_of_primitive_element halg hadjι
      have hEq : ((conjAut d.h_adjoin).toAlgHom.comp (conjAut d.h_adjoin).toAlgHom)
          = AlgHom.id d.L d.K := by
        apply AlgHom.ext_of_adjoin_eq_top hadjalg
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        subst hz
        simpa using hinvι
      intro y
      have := AlgHom.congr_fun hEq y
      simpa using this
    -- Transport the involution to `𝓞 d.K` and then to ideals.
    have hnat : ∀ x : 𝓞 d.K,
        (algebraMap (𝓞 d.K) d.K) (c' x) = conjAut d.h_adjoin ((algebraMap (𝓞 d.K) d.K) x) :=
      fun _ => rfl
    have hinvring : ∀ x : 𝓞 d.K, c' (c' x) = x := by
      intro x
      apply IsFractionRing.injective (𝓞 d.K) d.K
      rw [hnat, hnat, hinvfield]
    have hbridge : ∀ I : Ideal (𝓞 d.K),
        Ideal.map c' I = Ideal.map (c' : 𝓞 d.K →+* 𝓞 d.K) I := fun _ => rfl
    have hbridge2 : ∀ I : Ideal (𝓞 d.K),
        Ideal.map c'.toRingEquiv I = Ideal.map c' I := fun _ => rfl
    have hcomp : (c' : 𝓞 d.K →+* 𝓞 d.K).comp (c' : 𝓞 d.K →+* 𝓞 d.K) = RingHom.id _ := by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      exact_mod_cast hinvring x
    have hinvideal : ∀ I : Ideal (𝓞 d.K), Ideal.map c' (Ideal.map c' I) = I := by
      intro I
      rw [hbridge, hbridge, Ideal.map_map, hcomp, Ideal.map_id]
    -- `P' = c'(w)` is an off-family prime whose `c'`-image is `w`.
    have hnebot : Ideal.map c' w.asIdeal ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective c'.injective]
      exact hwne
    haveI hprime : (Ideal.map c' w.asIdeal).IsPrime := Ideal.map_isPrime_of_equiv c'
    set P' : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K) :=
      ⟨Ideal.map c' w.asIdeal, hprime, hnebot⟩ with hP'
    have hmapP' : Ideal.map c' P'.asIdeal = w.asIdeal := by
      rw [hP']; exact hinvideal w.asIdeal
    have htransw : ∀ I : Ideal (𝓞 d.K),
        multiplicity w.asIdeal (Ideal.map c' I) = multiplicity P'.asIdeal I := by
      intro I
      have he := multMap c'.toRingEquiv P'.asIdeal I
      rw [hbridge2, hbridge2, hmapP'] at he
      exact he
    have hP'off : ∀ t, P' ≠ P t ∧ P' ≠ Pc t := by
      intro t
      constructor
      · intro hc
        apply (hw t).2
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rw [← hmapP', hc]
        exact (hswap t).1
      · intro hc
        apply (hw t).1
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rw [← hmapP', hc, ← (hswap t).1, hinvideal]
    rw [AdicValuationEqNegCount d.K w (α / conjAut d.h_adjoin α) hquot0, hcountq w,
      hcountα w, countAδ_off d.K P Pc ε w hw, countAδ_off d.K P Pc η w hw,
      ConjAutSpanSingletonCountSwap d P' w α hα htransw,
      hcountα P', countAδ_off d.K P Pc ε P' hP'off, countAδ_off d.K P Pc η P' hP'off]
    simp
