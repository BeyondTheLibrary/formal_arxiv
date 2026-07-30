import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.Types.SplittingRamification

open scoped NumberField
open Polynomial UniqueFactorizationMonoid Classical

attribute [local instance] Ideal.Quotient.field

theorem LocalSplitKummerCount
    (d : Workspace.Types.AdmissibleDatum.AdmissibleDatum)
    (b : Fin d.t)
    (ω : 𝓞 d.K)
    (hω_sq : ω ^ 2 = -1)
    (hω_int : IsIntegral (𝓞 d.L) ω)
    (hω_min : minpoly (𝓞 d.L) ω = X ^ 2 + 1)
    (hω_gen : IntermediateField.adjoin d.L {algebraMap (𝓞 d.K) d.K ω} = ⊤)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (hcop : (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) ⊔ 𝔮 = ⊤)
    (hres : ∃ r : (𝓞 d.L) ⧸ 𝔮, r ^ 2 = -1 ∧ r ≠ -r) :
    (Ideal.primesOver 𝔮 (𝓞 d.K)).ncard = 2 ∧
      ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K), Ideal.ramificationIdx 𝔮 𝔓 = 1 := by
  classical
  obtain ⟨h𝔮_prime, h𝔮_lies⟩ := h𝔮
  haveI : 𝔮.IsPrime := h𝔮_prime
  haveI : 𝔮.LiesOver (Ideal.span {(d.q b : ℤ)}) := h𝔮_lies
  -- `(q_b) ≠ ⊥`
  have hqbne : (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (d.hq_prime b).ne_zero
  -- `𝔮 ≠ ⊥`
  have hI' : 𝔮 ≠ ⊥ := by
    intro h
    apply hqbne
    have hover := Ideal.LiesOver.over (p := Ideal.span {(d.q b : ℤ)}) (P := 𝔮)
    rw [h] at hover
    rw [hover]
    exact Ideal.under_bot ℤ (𝓞 d.L)
  -- `𝔮` is maximal
  haveI hImax : 𝔮.IsMaximal := h𝔮_prime.isMaximal hI'
  -- residue field `𝓞 d.L ⧸ 𝔮` is a field via the local instance `Ideal.Quotient.field`
  -- normalized factors of `𝔮 · 𝓞_K` and of `(X²+1) mod 𝔮`
  set MI := normalizedFactors (Ideal.map (algebraMap (𝓞 d.L) (𝓞 d.K)) 𝔮) with hMI_def
  set MP := normalizedFactors (Polynomial.map (Ideal.Quotient.mk 𝔮) (minpoly (𝓞 d.L) ω)) with hMP_def
  obtain ⟨r, hr2, hrne⟩ := hres
  -- `(X²+1) mod 𝔮 = (X - C r)(X - C (-r))`
  have hpoly : Polynomial.map (Ideal.Quotient.mk 𝔮) (minpoly (𝓞 d.L) ω)
      = (X - C r) * (X - C (-r)) := by
    have hpow : (C r : ((𝓞 d.L) ⧸ 𝔮)[X]) ^ 2 = -1 := by
      rw [← map_pow, hr2]; simp
    rw [hω_min]
    have hmap : Polynomial.map (Ideal.Quotient.mk 𝔮) ((X : (𝓞 d.L)[X]) ^ 2 + 1)
        = (X : ((𝓞 d.L) ⧸ 𝔮)[X]) ^ 2 + 1 := by simp
    rw [hmap, map_neg]
    linear_combination hpow
  have hne1 : (X - C r : ((𝓞 d.L) ⧸ 𝔮)[X]) ≠ 0 := (monic_X_sub_C r).ne_zero
  have hne2 : (X - C (-r) : ((𝓞 d.L) ⧸ 𝔮)[X]) ≠ 0 := (monic_X_sub_C (-r)).ne_zero
  have hMP_eq : MP = {X - C r} + {X - C (-r)} := by
    rw [hMP_def, hpoly, normalizedFactors_mul hne1 hne2,
        normalizedFactors_irreducible (irreducible_X_sub_C r),
        normalizedFactors_irreducible (irreducible_X_sub_C (-r)),
        (monic_X_sub_C r).normalize_eq_self, (monic_X_sub_C (-r)).normalize_eq_self]
  have hdist : (X - C r : ((𝓞 d.L) ⧸ 𝔮)[X]) ≠ X - C (-r) := by
    intro hh
    rw [sub_right_inj] at hh
    exact hrne (C_inj.mp hh)
  have hMP_nodup : MP.Nodup := by
    rw [hMP_eq]
    simp only [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton,
      Multiset.nodup_singleton, and_true]
    exact hdist
  have hMP_card : Multiset.card MP = 2 := by
    rw [hMP_eq]; simp
  -- Kummer–Dedekind bijection: factors of `𝔮·𝓞_K` ↔ factors of `(X²+1) mod 𝔮`
  set e := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hImax hI' hcop hω_int
    with he_def
  have hMI_eq : MI = Multiset.map (fun f => (↑(e.symm f) : Ideal (𝓞 d.K))) MP.attach :=
    KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map
      hImax hI' hcop hω_int
  have hg_inj : Function.Injective (fun f => (↑(e.symm f) : Ideal (𝓞 d.K))) := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  have hMI_nodup : MI.Nodup := by
    rw [hMI_eq]
    exact (Multiset.nodup_attach.mpr hMP_nodup).map hg_inj
  have hMI_card : Multiset.card MI = 2 := by
    rw [hMI_eq, Multiset.card_map]
    exact Multiset.card_attach.trans hMP_card
  have hmapne : Ideal.map (algebraMap (𝓞 d.L) (𝓞 d.K)) 𝔮 ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI'
  refine ⟨?_, ?_⟩
  · -- exactly two primes over `𝔮`
    have hset : Ideal.primesOver 𝔮 (𝓞 d.K) = ↑(MI.toFinset) := by
      ext P
      rw [Finset.mem_coe, Multiset.mem_toFinset, hMI_def]
      exact Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 d.K) hI'
    rw [hset, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup hMI_nodup]
    exact hMI_card
  · -- each is unramified
    intro P hP
    obtain ⟨hP_prime, hP_lies⟩ := hP
    haveI : P.IsPrime := hP_prime
    haveI : P.LiesOver 𝔮 := hP_lies
    have hPne : P ≠ ⊥ := by
      intro h
      apply hI'
      have hover := Ideal.LiesOver.over (p := 𝔮) (P := P)
      rw [h] at hover
      rw [hover]
      exact Ideal.under_bot (𝓞 d.L) (𝓞 d.K)
    have hPmem : P ∈ MI := by
      rw [hMI_def]
      exact (Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 d.K) hI').mp ⟨hP_prime, hP_lies⟩
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmapne hP_prime hPne,
        ← hMI_def]
    exact Multiset.count_eq_one_of_mem hMI_nodup hPmem
