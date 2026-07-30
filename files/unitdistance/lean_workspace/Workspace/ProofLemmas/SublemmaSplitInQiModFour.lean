import Mathlib
import Workspace.Types.SplittingRamification

open scoped NumberField
open Workspace.Types.SplittingRamification
open Polynomial

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

theorem SublemmaSplitInQiModFour
    (Qi : Type*) [Field Qi] [NumberField Qi] [Algebra ℚ Qi]
    (hi : ∃ x : Qi, x ^ 2 = -1) (hdeg : Module.finrank ℚ Qi = 2)
    (q : ℕ) (hq : q.Prime) :
    SplitsCompletelyRat q Qi → q % 4 = 1 := by
  intro hsplit
  obtain ⟨hqP, hncard, hef⟩ := hsplit
  haveI : Fact (Nat.Prime q) := ⟨hqP⟩
  -- integral element ι with ι² = -1, a unit
  obtain ⟨x, hx⟩ := hi
  have hxint : IsIntegral ℤ x := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · have h : (X ^ 2 + 1 : ℤ[X]) = X ^ 2 + C 1 := by simp
      rw [h]; exact monic_X_pow_add_C 1 (by norm_num)
    · simp [hx]
  set ι : 𝓞 Qi := ⟨x, hxint⟩ with hιdef
  have hcoe : (algebraMap (𝓞 Qi) Qi) ι = x := rfl
  have hι2 : ι ^ 2 = -1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 Qi) Qi
    rw [map_pow, map_neg, map_one, hcoe, hx]
  have hιunit : IsUnit ι :=
    isUnit_of_mul_eq_one (-ι) (by
      have h : ι * (-ι) = -(ι ^ 2) := by ring
      rw [h, hι2]; ring)
  -- basic prime facts
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hqP.ne_zero
  -- pick a prime 𝔮 over (q)
  have hne0 : (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Qi)).ncard ≠ 0 := by
    have h2 : (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Qi)).ncard = 2 := by
      rw [hncard]; convert hdeg using 2; exact Subsingleton.elim _ _
    omega
  obtain ⟨𝔮, h𝔮mem⟩ := Set.nonempty_of_ncard_ne_zero hne0
  obtain ⟨hqp, hqlo⟩ := h𝔮mem
  haveI : 𝔮.IsPrime := hqp
  haveI : 𝔮.LiesOver (Ideal.span {(q : ℤ)}) := hqlo
  have hq_ne : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔮
  haveI : 𝔮.IsMaximal := hqp.isMaximal hq_ne
  -- e = f = 1
  have he1 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 = 1 := (hef 𝔮 ⟨hqp, hqlo⟩).1
  have hf1 : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔮 = 1 := (hef 𝔮 ⟨hqp, hqlo⟩).2
  -- residue field cardinality = q
  letI hMod : Module (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 Qi ⧸ 𝔮) := inferInstance
  haveI hFinF : Finite (𝓞 Qi ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 hq_ne
  haveI hFtF : Fintype (𝓞 Qi ⧸ 𝔮) := Fintype.ofFinite _
  haveI hFinZ : Finite (ℤ ⧸ Ideal.span {(q : ℤ)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb_ne
  haveI hFtZ : Fintype (ℤ ⧸ Ideal.span {(q : ℤ)}) := Fintype.ofFinite _
  letI hFieldZ : Field (ℤ ⧸ Ideal.span {(q : ℤ)}) := Ideal.Quotient.field _
  have hfr : Module.finrank (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 Qi ⧸ 𝔮) = 1 := by
    have h := Ideal.inertiaDeg_algebraMap (Ideal.span {(q : ℤ)}) 𝔮
    rw [hf1] at h; exact h.symm
  have hcard : Fintype.card (𝓞 Qi ⧸ 𝔮)
      = Fintype.card (ℤ ⧸ Ideal.span {(q : ℤ)}) ^
          Module.finrank (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 Qi ⧸ 𝔮) := Module.card_eq_pow_finrank
  rw [hfr, pow_one] at hcard
  have hcardZ : Fintype.card (ℤ ⧸ Ideal.span {(q : ℤ)}) = q := by
    haveI : NeZero q := ⟨hqP.ne_zero⟩
    rw [Fintype.card_congr (Int.quotientSpanEquivZMod (q : ℤ)).toEquiv, ZMod.card]
    exact Int.natAbs_natCast q
  rw [hcardZ] at hcard
  -- IsSquare(-1) in the residue field, via the image of ι
  letI hFieldF : Field (𝓞 Qi ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hsq : IsSquare (-1 : 𝓞 Qi ⧸ 𝔮) := by
    refine ⟨Ideal.Quotient.mk 𝔮 ι, ?_⟩
    have hmm : (Ideal.Quotient.mk 𝔮 ι) * (Ideal.Quotient.mk 𝔮 ι)
        = Ideal.Quotient.mk 𝔮 (ι ^ 2) := by rw [← map_mul]; ring_nf
    rw [hmm, hι2, map_neg, map_one]
  -- q % 4 ≠ 3
  have hmod3 : q % 4 ≠ 3 := by
    have h := (FiniteField.isSquare_neg_one_iff (F := 𝓞 Qi ⧸ 𝔮)).mp hsq
    rwa [hcard] at h
  -- q ≠ 2
  have hq2 : q ≠ 2 := by
    intro hq2eq
    have helt : (2 : 𝓞 Qi) = ι * (1 - ι) ^ 2 := by linear_combination (2 - ι) * hι2
    have h1ι_ne : (1 - ι : 𝓞 Qi) ≠ 0 := by
      intro h
      have hι1 : ι = 1 := by linear_combination -h
      rw [hι1] at hι2; simp only [one_pow] at hι2
      have : (2 : 𝓞 Qi) = 0 := by linear_combination hι2
      exact two_ne_zero this
    have hmap : Ideal.map (algebraMap ℤ (𝓞 Qi)) (Ideal.span {(q : ℤ)})
        = (Ideal.span {(1 - ι : 𝓞 Qi)}) ^ 2 := by
      rw [Ideal.map_span]
      have himg : (algebraMap ℤ (𝓞 Qi)) '' {(q : ℤ)} = {(q : 𝓞 Qi)} := by simp
      rw [himg]
      have hqcoe : (q : 𝓞 Qi) = 2 := by rw [hq2eq]; norm_num
      rw [hqcoe, helt, ← Ideal.span_singleton_mul_span_singleton ι ((1 - ι) ^ 2),
        Ideal.span_singleton_eq_top.mpr hιunit, Ideal.top_mul, ← Ideal.span_singleton_pow]
    have hspan_ne : Ideal.span {(1 - ι : 𝓞 Qi)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact h1ι_ne
    have hmap_ne : Ideal.map (algebraMap ℤ (𝓞 Qi)) (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
      rw [hmap]; exact pow_ne_zero 2 hspan_ne
    have hcount := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      hmap_ne hqp hq_ne
    rw [he1, hmap, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
      at hcount
    omega
  -- conclude
  have hodd : q % 2 = 1 := hqP.eq_two_or_odd.resolve_left hq2
  omega
