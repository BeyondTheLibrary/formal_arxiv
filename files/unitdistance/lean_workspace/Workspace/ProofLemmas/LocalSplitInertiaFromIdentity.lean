import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.SplittingRamification

open scoped NumberField

open Workspace.Types.AdmissibleDatum

theorem LocalSplitInertiaFromIdentity
    (d : AdmissibleDatum) (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (hcard : (Ideal.primesOver 𝔮 (𝓞 d.K)).ncard = 2)
    (hram : ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K), Ideal.ramificationIdx 𝔮 𝔓 = 1)
    (hdeg : Module.finrank d.L d.K = 2) :
    ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K), Ideal.inertiaDeg 𝔮 𝔓 = 1 := by
  -- Basic finiteness / integral-closure instances for 𝓞 L ⊆ 𝓞 K
  have hFin : FiniteDimensional d.L d.K := inferInstance
  haveI : Module.Finite (𝓞 d.L) (𝓞 d.K) :=
    IsIntegralClosure.finite (𝓞 d.L) d.L d.K (𝓞 d.K)
  -- Unpack that 𝔮 is prime and lies over (q_b)
  obtain ⟨hqp, hqlo⟩ := h𝔮
  haveI : 𝔮.IsPrime := hqp
  haveI : 𝔮.LiesOver (Ideal.span {(d.q b : ℤ)}) := hqlo
  -- (q_b) ≠ ⊥
  have hqb_ne : (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (d.hq_prime b).ne_zero
  -- 𝔮 ≠ ⊥
  have hq_ne : 𝔮 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔮
  haveI : 𝔮.IsMaximal := hqp.isMaximal hq_ne
  -- The fundamental identity ∑ e·f = [K:L] = 2
  have hsum := Ideal.sum_ramification_inertia (𝓞 d.K) d.L d.K hq_ne
  rw [hdeg] at hsum
  -- Name the finite set of primes over 𝔮 and bridge to the `primesOver` set
  set F := IsDedekindDomain.primesOverFinset 𝔮 (𝓞 d.K) with hF
  have hcoe : (↑F : Set (Ideal (𝓞 d.K))) = 𝔮.primesOver (𝓞 d.K) :=
    IsDedekindDomain.coe_primesOverFinset hq_ne (𝓞 d.K)
  have hmem : ∀ P, P ∈ F ↔ P ∈ 𝔮.primesOver (𝓞 d.K) := fun P => by
    rw [← Finset.mem_coe, hcoe]
  -- The cardinality of `F` is 2
  have hFcard : F.card = 2 := by
    have h2 : (↑F : Set (Ideal (𝓞 d.K))).ncard = 2 := by rw [hcoe]; exact hcard
    rwa [Set.ncard_coe_finset] at h2
  -- Each ramification index is 1, so the sum reduces to ∑ f = 2
  have hsum2 : ∑ P ∈ F, 𝔮.inertiaDeg P = 2 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro P hP
    rw [hram P ((hmem P).mp hP), one_mul]
  -- Each residue degree is ≥ 1
  have hpos : ∀ P ∈ F, (1 : ℕ) ≤ 𝔮.inertiaDeg P := by
    intro P hP
    obtain ⟨hPp, hPlo⟩ := (hmem P).mp hP
    haveI : P.IsPrime := hPp
    haveI : P.LiesOver 𝔮 := hPlo
    have := Ideal.inertiaDeg_pos 𝔮 P
    omega
  -- Two terms, each ≥ 1, summing to 2 ⇒ each = 1
  have hall : ∀ P ∈ F, (1 : ℕ) = 𝔮.inertiaDeg P := by
    have hsumeq : ∑ _P ∈ F, (1 : ℕ) = ∑ P ∈ F, 𝔮.inertiaDeg P := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, hFcard, hsum2]
    exact (Finset.sum_eq_sum_iff_of_le hpos).mp hsumeq
  intro 𝔓 h𝔓
  exact (hall 𝔓 ((hmem 𝔓).mpr h𝔓)).symm
