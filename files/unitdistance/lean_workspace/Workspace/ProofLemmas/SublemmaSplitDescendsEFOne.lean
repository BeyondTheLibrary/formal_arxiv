import Mathlib
import Workspace.Types.SplittingRamification

open scoped NumberField
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem SublemmaSplitDescendsEFOne
    (N Lp : Type*) [Field N] [NumberField N] [Field Lp] [NumberField Lp]
    [Algebra ℚ Lp] [Algebra Lp N] [Algebra ℚ N] [IsScalarTower ℚ Lp N]
    [FiniteDimensional Lp N] (q : ℕ) (hsplitN : SplitsCompletelyRat q N)
    (𝔭 : Ideal (𝓞 Lp))
    (h𝔭 : 𝔭 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp)) :
    Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 ∧
      Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1 := by
  obtain ⟨hqP, hncardN, hefN⟩ := hsplitN
  obtain ⟨h𝔭p, h𝔭lo⟩ := h𝔭
  haveI : 𝔭.IsPrime := h𝔭p
  haveI : 𝔭.LiesOver (Ideal.span {(q : ℤ)}) := h𝔭lo
  -- (q) ≠ ⊥, 𝔭 ≠ ⊥, 𝔭 maximal
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hqP.ne_zero
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqP
  haveI hpP : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hqP.ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(q : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  have h𝔭_ne : 𝔭 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔭
  haveI h𝔭max : 𝔭.IsMaximal := h𝔭p.isMaximal h𝔭_ne
  -- relative integral-extension instances 𝓞 Lp ⊆ 𝓞 N
  haveI : Module.Finite (𝓞 Lp) (𝓞 N) := IsIntegralClosure.finite (𝓞 Lp) Lp N (𝓞 N)
  haveI : Algebra.IsIntegral (𝓞 Lp) (𝓞 N) := IsIntegralClosure.isIntegral_algebra (𝓞 Lp) N
  -- going up: a maximal prime 𝔓 of 𝓞 N over 𝔭
  obtain ⟨𝔓, h𝔓max, h𝔓lo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) 𝔭
  haveI : 𝔓.IsMaximal := h𝔓max
  haveI : 𝔓.LiesOver 𝔭 := h𝔓lo
  -- 𝔓 lies over (q)
  haveI h𝔓loq : 𝔓.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.trans 𝔓 𝔭 (Ideal.span {(q : ℤ)})
  have h𝔓mem : 𝔓 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 N) := ⟨h𝔓max.isPrime, h𝔓loq⟩
  obtain ⟨heN, hfN⟩ := hefN 𝔓 h𝔓mem
  -- tower multiplicativity for inertia degree
  have hftower : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔓
      = Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 * Ideal.inertiaDeg 𝔭 𝔓 :=
    Ideal.inertiaDeg_algebra_tower (Ideal.span {(q : ℤ)}) 𝔭 𝔓
  rw [hfN] at hftower
  have hf1 : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1 :=
    Nat.eq_one_of_mul_eq_one_right hftower.symm
  -- tower multiplicativity for ramification index
  have hmap𝔭_ne : Ideal.map (algebraMap (𝓞 Lp) (𝓞 N)) 𝔭 ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 Lp) (𝓞 N))]
    exact h𝔭_ne
  have hmapq_ne : Ideal.map (algebraMap ℤ (𝓞 N)) (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 N))]
    exact hqb_ne
  have hle : Ideal.map (algebraMap (𝓞 Lp) (𝓞 N)) 𝔭 ≤ 𝔓 :=
    Ideal.map_le_iff_le_comap.mpr h𝔓lo.over.le
  have hetower : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔓
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 * Ideal.ramificationIdx 𝔭 𝔓 :=
    Ideal.ramificationIdx_algebra_tower hmap𝔭_ne hmapq_ne hle
  rw [heN] at hetower
  have he1 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 :=
    Nat.eq_one_of_mul_eq_one_right hetower.symm
  exact ⟨he1, hf1⟩
