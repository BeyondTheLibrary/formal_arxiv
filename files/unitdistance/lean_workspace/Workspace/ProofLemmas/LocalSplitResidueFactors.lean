import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.SplittingRamification

open scoped NumberField
open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

theorem LocalSplitResidueFactors
    (d : AdmissibleDatum) (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (hf : Ideal.inertiaDeg (Ideal.span {(d.q b : ℤ)}) 𝔮 = 1) :
    Nat.card (𝓞 d.L ⧸ 𝔮) = d.q b ∧
    ∃ a : (𝓞 d.L ⧸ 𝔮), a ^ 2 = -1 ∧ a ≠ -a ∧
      (Polynomial.X ^ 2 + 1 : Polynomial (𝓞 d.L ⧸ 𝔮)) =
        (Polynomial.X - Polynomial.C a) * (Polynomial.X + Polynomial.C a) := by
  obtain ⟨hqp, hqlo⟩ := h𝔮
  haveI : 𝔮.IsPrime := hqp
  haveI : 𝔮.LiesOver (Ideal.span {(d.q b : ℤ)}) := hqlo
  have hqb_ne : (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (d.hq_prime b).ne_zero
  have hq_ne : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔮
  haveI : 𝔮.IsMaximal := hqp.isMaximal hq_ne
  have hprime_int : Prime (d.q b : ℤ) := Nat.prime_iff_prime_int.mp (d.hq_prime b)
  haveI hpP : (Ideal.span {(d.q b : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (d.hq_prime b).ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(d.q b : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  -- Establish the module structure BEFORE the Field instance to avoid a diamond
  letI hMod : Module (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮) := inferInstance
  haveI hFinF : Finite (𝓞 d.L ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 hq_ne
  haveI hFtF : Fintype (𝓞 d.L ⧸ 𝔮) := Fintype.ofFinite (𝓞 d.L ⧸ 𝔮)
  haveI hFinZ : Finite (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hqb_ne
  haveI hFtZ : Fintype (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) :=
    Fintype.ofFinite (ℤ ⧸ Ideal.span {(d.q b : ℤ)})
  letI hFieldZ : Field (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) := Ideal.Quotient.field _
  -- finrank = inertiaDeg = 1
  have hfr : Module.finrank (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮) = 1 := by
    have h := Ideal.inertiaDeg_algebraMap (Ideal.span {(d.q b : ℤ)}) 𝔮
    rw [hf] at h; exact h.symm
  -- cardinality of the residue field
  have hcard : Fintype.card (𝓞 d.L ⧸ 𝔮)
      = Fintype.card (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) ^
          Module.finrank (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮) :=
    Module.card_eq_pow_finrank
  rw [hfr, pow_one] at hcard
  have hcardZ : Fintype.card (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) = d.q b := by
    haveI : NeZero (d.q b) := ⟨(d.hq_prime b).ne_zero⟩
    rw [Fintype.card_congr (Int.quotientSpanEquivZMod (d.q b : ℤ)).toEquiv, ZMod.card]
    exact Int.natAbs_natCast (d.q b)
  rw [hcardZ] at hcard
  have hcardF : Nat.card (𝓞 d.L ⧸ 𝔮) = d.q b := by
    rw [Nat.card_eq_fintype_card]; exact hcard
  refine ⟨hcardF, ?_⟩
  -- Part (ii): X² + 1 splits into distinct linear factors.
  letI hFieldF : Field (𝓞 d.L ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  -- -1 is a square since card ≡ 1 (mod 4)
  have hsq : IsSquare (-1 : 𝓞 d.L ⧸ 𝔮) := by
    exact (FiniteField.isSquare_neg_one_iff (F := 𝓞 d.L ⧸ 𝔮)).mpr
      (by rw [hcard]; have h4 := d.hq_mod4 b; omega)
  obtain ⟨a, ha⟩ := hsq
  have ha2 : a ^ 2 = -1 := by rw [sq]; exact ha.symm
  -- The residue field has characteristic q_b (odd), hence 2 ≠ 0.
  haveI : Fact (Nat.Prime (d.q b)) := ⟨d.hq_prime b⟩
  have hnonunit : ((d.q b : ℕ) : ℤ) ∈ nonunits ℤ :=
    mem_nonunits_iff.mpr hprime_int.not_unit
  haveI hCharPZ : CharP (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (d.q b) :=
    CharP.quotient ℤ (d.q b) hnonunit
  have hinj : Function.Injective
      (algebraMap (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮)) :=
    RingHom.injective (algebraMap (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮))
  haveI hCharP : CharP (𝓞 d.L ⧸ 𝔮) (d.q b) := charP_of_injective_algebraMap hinj (d.q b)
  have htwo : ((2 : ℕ) : 𝓞 d.L ⧸ 𝔮) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (𝓞 d.L ⧸ 𝔮) (d.q b) 2] at h
    have h2 := (d.hq_prime b).two_le
    have h4 := d.hq_mod4 b
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have htwo' : (2 : 𝓞 d.L ⧸ 𝔮) ≠ 0 := by exact_mod_cast htwo
  -- factorization identity
  have hCa : (Polynomial.C a) ^ 2 = -1 := by
    rw [← Polynomial.C_pow, ha2, map_neg, map_one]
  refine ⟨a, ha2, ?_, ?_⟩
  · -- a ≠ -a
    intro hcon
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha2
    have h2a : (2 : 𝓞 d.L ⧸ 𝔮) * a = 0 := by linear_combination hcon
    rcases mul_eq_zero.mp h2a with h | h
    · exact htwo' h
    · exact ha0 h
  · -- X² + 1 = (X - C a)(X + C a)
    have expand : (Polynomial.X - Polynomial.C a) * (Polynomial.X + Polynomial.C a)
        = Polynomial.X ^ 2 - (Polynomial.C a) ^ 2 := by ring
    rw [expand, hCa, sub_neg_eq_add]
