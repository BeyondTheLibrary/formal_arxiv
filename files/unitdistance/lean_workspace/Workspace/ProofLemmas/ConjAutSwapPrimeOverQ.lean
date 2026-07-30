import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaLocalSplitAtQ
import Workspace.ProofLemmas.LocalSplitGenerator
import Workspace.ProofLemmas.ResidueMapSurjectiveOfInertiaDegOne

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI
open Polynomial

set_option maxHeartbeats 800000

theorem ConjAutSwapPrimeOverQ (d : AdmissibleDatum) (b : Fin d.t) (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (𝔓 : Ideal (𝓞 d.K)) (h𝔓 : 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K)) :
    Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) 𝔓
        ∈ Ideal.primesOver 𝔮 (𝓞 d.K) ∧
      Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) 𝔓 ≠ 𝔓 := by
  obtain ⟨h𝔓p, h𝔓o⟩ := h𝔓
  haveI := h𝔓p
  haveI := h𝔓o
  set c' := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hc'def
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Ideal.map_isPrime_of_equiv c'
  · exact Ideal.map_equiv_liesOver 𝔓 𝔮 c'
  · intro hcontra
    -- 𝔮 is maximal (nonzero prime of Dedekind 𝓞_L)
    obtain ⟨h𝔮p, h𝔮o⟩ := h𝔮
    haveI := h𝔮p
    haveI := h𝔮o
    have hqZne : ((d.q b : ℤ)) ≠ 0 := by
      exact_mod_cast (d.hq_prime b).ne_zero
    have hspan_ne : Ideal.span {(d.q b : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZne
    haveI h𝔮max : 𝔮.IsMaximal := h𝔮p.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hspan_ne 𝔮)
    -- conjAut negates every square root of -1
    set iota := d.h_adjoin.choose with hiota
    have hsqι : iota ^ 2 = -1 := d.h_adjoin.choose_spec.1
    have hadjι : IntermediateField.adjoin d.L {iota} = ⊤ := d.h_adjoin.choose_spec.2
    have hint : IsIntegral d.L iota := ⟨X ^ 2 + 1, by monicity!, by simp [hsqι]⟩
    have hci : conjAut d.h_adjoin iota = -iota := by
      have hgen : ((IntermediateField.equivOfEq hadjι).trans
          IntermediateField.topEquiv).symm iota
          = IntermediateField.AdjoinSimple.gen d.L iota := by
        apply Subtype.ext; simp [IntermediateField.AdjoinSimple.gen]
      unfold conjAut
      simp only [AlgEquiv.ofBijective_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe]
      erw [hgen, IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
    have hL5 : ∀ j : d.K, j ^ 2 = -1 → conjAut d.h_adjoin j = -j := by
      intro j hj
      have hfactor : (j - iota) * (j + iota) = 0 := by linear_combination hj - hsqι
      rcases mul_eq_zero.mp hfactor with hh | hh
      · have : j = iota := by linear_combination hh
        rw [this, hci]
      · have : j = -iota := by linear_combination hh
        rw [this, map_neg, hci, neg_neg]
    -- generator ω of 𝓞_K with ω² = -1 and c'(ω) = -ω
    obtain ⟨ω, hω_algsq, hω_int, hω_min, hω_gen⟩ := LocalSplitGenerator d
    have hcoinj : Function.Injective (algebraMap (𝓞 d.K) d.K) :=
      IsFractionRing.injective (𝓞 d.K) d.K
    have hω_sq : ω ^ 2 = -1 := by
      apply hcoinj; rw [map_pow, map_neg, map_one]; exact hω_algsq
    have hc'ω : c' ω = -ω := by
      apply hcoinj
      rw [map_neg, hc'def]
      have hcomm : algebraMap (𝓞 d.K) d.K (NumberField.RingOfIntegers.mapAlgEquiv
          (conjAut d.h_adjoin) ω) = conjAut d.h_adjoin (algebraMap (𝓞 d.K) d.K ω) := rfl
      rw [hcomm]
      exact hL5 (algebraMap (𝓞 d.K) d.K ω) hω_algsq
    -- residue field 𝓞_K/𝔓 = 𝓞_L/𝔮 (inertiaDeg = 1) ⇒ ω ≡ (an 𝓞_L element) mod 𝔓
    obtain ⟨_hram, hinertia⟩ := (SublemmaLocalSplitAtQ d b 𝔮 ⟨h𝔮p, h𝔮o⟩).2 𝔓 ⟨h𝔓p, h𝔓o⟩
    have h𝔮ne : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan_ne 𝔮
    haveI h𝔓max : 𝔓.IsMaximal :=
      h𝔓p.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔮ne 𝔓)
    -- residue map 𝓞_L → 𝓞_K/𝔓 is surjective (inertiaDeg = 1): the residue extension is degree 1
    have hsurj : Function.Surjective
        ((Ideal.Quotient.mk 𝔓).comp (algebraMap (𝓞 d.L) (𝓞 d.K))) :=
      ResidueMapSurjectiveOfInertiaDegOne 𝔮 𝔓 hinertia
    obtain ⟨l, hw⟩ := hsurj (Ideal.Quotient.mk 𝔓 ω)
    have hmem1 : ω - algebraMap (𝓞 d.L) (𝓞 d.K) l ∈ 𝔓 := by
      rw [RingHom.comp_apply] at hw
      have hd := Ideal.Quotient.eq.mp hw
      have hn := neg_mem hd
      rwa [neg_sub] at hn
    -- c' preserves 𝔓 (from hcontra) and fixes 𝓞_L
    have hc'mem : ∀ x ∈ 𝔓, c' x ∈ 𝔓 := by
      intro x hx
      have := Ideal.mem_map_of_mem c' hx
      rwa [hcontra] at this
    have hc'l : c' (algebraMap (𝓞 d.L) (𝓞 d.K) l) = algebraMap (𝓞 d.L) (𝓞 d.K) l :=
      c'.commutes l
    have hmem2 : (-ω) - algebraMap (𝓞 d.L) (𝓞 d.K) l ∈ 𝔓 := by
      have := hc'mem _ hmem1
      rwa [map_sub, hc'ω, hc'l] at this
    -- 2ω ∈ 𝔓
    have h2ω : (2 : 𝓞 d.K) * ω ∈ 𝔓 := by
      have hd := Ideal.sub_mem 𝔓 hmem1 hmem2
      have : ω - algebraMap (𝓞 d.L) (𝓞 d.K) l - (-ω - algebraMap (𝓞 d.L) (𝓞 d.K) l)
          = 2 * ω := by ring
      rwa [this] at hd
    -- contradiction: 2ω ∉ 𝔓
    rcases h𝔓p.mem_or_mem h2ω with h2 | hω
    · -- 2 ∈ 𝔓, but 𝔓 lies over q_b (odd) : contradiction
      haveI htower : IsScalarTower ℤ (𝓞 d.L) (𝓞 d.K) :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
      haveI : 𝔓.LiesOver (Ideal.span {(d.q b : ℤ)}) := Ideal.LiesOver.trans 𝔓 𝔮 _
      have h2Z : (2 : ℤ) ∈ Ideal.span {(d.q b : ℤ)} := by
        have hcomap : (2 : ℤ) ∈ 𝔓.under ℤ := by
          rw [Ideal.mem_comap]
          have : (algebraMap ℤ (𝓞 d.K)) 2 = (2 : 𝓞 d.K) := by simp
          rw [this]; exact h2
        rwa [← Ideal.LiesOver.over (p := Ideal.span {(d.q b : ℤ)}) (P := 𝔓)] at hcomap
      rw [Ideal.mem_span_singleton] at h2Z
      have : (d.q b : ℤ) ∣ 2 := h2Z
      have hqle : (d.q b : ℕ) ∣ 2 := by exact_mod_cast this
      have := (Nat.prime_dvd_prime_iff_eq (d.hq_prime b) Nat.prime_two).mp hqle
      have hmod := d.hq_mod4 b
      omega
    · -- ω ∈ 𝔓, but ω is a unit (ω² = -1) : contradiction
      have h1 : (-1 : 𝓞 d.K) ∈ 𝔓 := by
        have := Ideal.mul_mem_left 𝔓 ω hω
        rwa [← sq, hω_sq] at this
      have : (1 : 𝓞 d.K) ∈ 𝔓 := by
        have := neg_mem h1; rwa [neg_neg] at this
      exact h𝔓p.ne_top (Ideal.eq_top_of_isUnit_mem 𝔓 this isUnit_one)
