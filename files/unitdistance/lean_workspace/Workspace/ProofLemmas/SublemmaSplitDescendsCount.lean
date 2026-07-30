import Mathlib
import Workspace.Types.SplittingRamification

open scoped NumberField
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

theorem SublemmaSplitDescendsCount
    (Lp : Type*) [Field Lp] [NumberField Lp] (q : ℕ) (hq : q.Prime)
    (hef : ∀ 𝔭 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp),
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1) :
    (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp)).ncard = Module.finrank ℚ Lp := by
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  haveI hpP : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(q : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  -- fundamental identity ∑ e·f = [Lp : ℚ]
  have hsum := Ideal.sum_ramification_inertia (𝓞 Lp) ℚ Lp hqb_ne
  -- bridge primesOverFinset ↔ primesOver
  set F := IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 Lp) with hF
  have hcoe : (↑F : Set (Ideal (𝓞 Lp))) = (Ideal.span {(q : ℤ)}).primesOver (𝓞 Lp) :=
    IsDedekindDomain.coe_primesOverFinset hqb_ne (𝓞 Lp)
  have hmem : ∀ P, P ∈ F ↔ P ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 Lp) := fun P => by
    rw [← Finset.mem_coe, hcoe]
  -- each e·f = 1, so the sum equals the cardinality
  have hsumcard : ∑ P ∈ F,
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P * Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P
        = F.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro P hP
    obtain ⟨he, hf⟩ := hef P ((hmem P).mp hP)
    rw [he, hf, one_mul]
  -- so F.card = finrank ℚ Lp
  have hFcard : (F.card : ℕ) = Module.finrank ℚ Lp := by rw [← hsumcard, hsum]
  -- ncard = F.card
  have hncardeq : (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp)).ncard = F.card := by
    rw [← hcoe, Set.ncard_coe_finset]
  rw [hncardeq, hFcard]
