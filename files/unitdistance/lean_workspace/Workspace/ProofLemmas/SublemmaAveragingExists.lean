import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaLatticeFundamentalDomain
import Workspace.ProofLemmas.SublemmaLatticeDiscrete
import Workspace.ProofLemmas.SublemmaNcountEqTsum
import Workspace.ProofLemmas.SublemmaEcountEqSumTsum
import Workspace.ProofLemmas.SublemmaHaarUnfolding
import Workspace.ProofLemmas.SublemmaWindowVolume
import Workspace.ProofLemmas.SublemmaOverlapVolume
import Workspace.ProofLemmas.SublemmaAveragingPigeonhole

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory Pointwise

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaAveragingExists (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 1 / 2 < R)
    (U : Finset (Fin f → ℂ))
    (hU_lat : ∀ u ∈ U, u ∈ lattice sel DD)
    (hU_ne : ∀ u ∈ U, u ≠ 0)
    (hU_coord : ∀ u ∈ U, ∀ r, ‖u r‖ = 1) :
    ∃ a : Fin f → ℂ, (Xset sel DD R a).Nonempty ∧
      (Ecount sel DD R U a : ℝ) ≥
        (U.card : ℝ) * rho R ^ f * (Ncount sel DD R a : ℝ) := by
  classical
  obtain ⟨F, hFfund, hFpos, hFfin⟩ := SublemmaLatticeFundamentalDomain hcm sel DD hDD
  -- Countability of the lattice.
  haveI hcountOK : Countable (𝓞 K) := by
    have b := Module.Free.chooseBasis ℤ (𝓞 K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI hcountLat : Countable (↥(lattice sel DD)) := by
    have hc : ((lattice sel DD : Set (Fin f → ℂ))).Countable := by
      rw [lattice, AddMonoidHom.coe_range]; exact Set.countable_range _
    exact hc.to_subtype
  -- Periodization function.
  set P : Set (Fin f → ℂ) → (Fin f → ℂ) → ℝ :=
    fun S a => ∑' l : ↥(lattice sel DD), S.indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ))
    with hP
  -- Helper: for a bounded measurable `S`, `P S` is measurable, integrable on `F`, and
  -- `∫_F P S = (vol S).toReal`.
  have helper : ∀ (S : Set (Fin f → ℂ)), MeasurableSet S → Bornology.IsBounded S →
      Measurable (P S) ∧ IntegrableOn (P S) F volume ∧ ∫ a in F, P S a = (volume S).toReal := by
    intro S hSmeas hSbdd
    set M : (Fin f → ℂ) → ENNReal :=
      fun a => ∑' l : ↥(lattice sel DD), S.indicator (fun _ => (1 : ENNReal)) (a + (l : Fin f → ℂ))
      with hM
    have hsummeas : ∀ l : ↥(lattice sel DD),
        Measurable (fun a : Fin f → ℂ => S.indicator (fun _ => (1 : ENNReal)) (a + (l : Fin f → ℂ))) :=
      fun l => (measurable_const.indicator hSmeas).comp (measurable_add_const _)
    have hMmeas : Measurable M := Measurable.ennreal_tsum hsummeas
    have hNM : ∀ a, P S a = (M a).toReal := by
      intro a
      rw [hP, hM, ENNReal.tsum_toReal_eq (fun l => ?_)]
      · exact tsum_congr fun l => by
          by_cases h : a + (l : Fin f → ℂ) ∈ S <;> simp [h]
      · by_cases h : a + (l : Fin f → ℂ) ∈ S <;> simp [h]
    have hPmeas : Measurable (P S) := by
      have : P S = fun a => (M a).toReal := funext hNM
      rw [this]; exact hMmeas.ennreal_toReal
    have hPnonneg : ∀ a, 0 ≤ P S a :=
      fun a => tsum_nonneg fun l => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    -- `∫⁻_F M = vol S`.
    have hMlint : ∫⁻ a in F, M a ∂volume = volume S := by
      have hconv : ∫⁻ a in F, M a ∂volume
          = ∫⁻ a in F, (∑' l : ↥(lattice sel DD),
              S.indicator (fun _ => (1 : ENNReal)) (l +ᵥ a)) ∂volume := by
        apply lintegral_congr
        intro a; rw [hM]
        exact tsum_congr fun l => by
          rw [show (l +ᵥ a : Fin f → ℂ) = (l : Fin f → ℂ) + a from rfl, add_comm]
      rw [hconv,
        lintegral_tsum (fun l =>
          (show AEMeasurable (fun a => S.indicator (fun _ => (1 : ENNReal)) (l +ᵥ a))
              (volume.restrict F) from
            ((measurable_const.indicator hSmeas).comp (measurable_const_vadd l)).aemeasurable)),
        ← hFfund.lintegral_eq_tsum'' (S.indicator (fun _ => (1 : ENNReal)))]
      exact lintegral_indicator_one hSmeas
    have hPint : IntegrableOn (P S) F volume := by
      refine ⟨hPmeas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hPnonneg)]
      have hle : ∀ a, ENNReal.ofReal (P S a) ≤ M a := fun a => by
        rw [hNM a]; exact ENNReal.ofReal_toReal_le
      calc ∫⁻ a in F, ENNReal.ofReal (P S a) ∂volume
          ≤ ∫⁻ a in F, M a ∂volume := lintegral_mono hle
        _ = volume S := hMlint
        _ < ⊤ := hSbdd.measure_lt_top
    have hPval : ∫ a in F, P S a = (volume S).toReal :=
      SublemmaHaarUnfolding hcm sel DD hDD F hFfund S hSmeas hSbdd
    exact ⟨hPmeas, hPint, hPval⟩
  -- The window and overlap sets.
  have hWmeas : MeasurableSet (window (f := f) R) := by
    have : window (f := f) R = Set.univ.pi (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
      ext z
      simp only [window, Set.mem_setOf_eq, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
    rw [this]; exact MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  have hWbdd : Bornology.IsBounded (window (f := f) R) := by
    have : window (f := f) R ⊆ Metric.closedBall (0 : Fin f → ℂ) R := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith : (0:ℝ) ≤ R)]
      exact hz
    exact Metric.isBounded_closedBall.subset this
  have hRpos : (0 : ℝ) < R := by linarith
  have hdisc_pos : 0 < discArea R := by
    rw [discArea]; positivity
  -- `N := P (window R)`, `E := ∑_{u∈U} P (overlap_u)`.
  set N : (Fin f → ℂ) → ℝ := P (window R) with hNdef
  set E : (Fin f → ℂ) → ℝ :=
    fun a => ∑ u ∈ U, P (window R ∩ (window R - {u})) a with hEdef
  obtain ⟨hNmeas, hNint, hNval0⟩ := helper (window R) hWmeas hWbdd
  -- per-`u` overlap facts
  have hOmeas : ∀ u : Fin f → ℂ, MeasurableSet (window (f := f) R ∩ (window R - {u})) := by
    intro u
    refine hWmeas.inter ?_
    have : (window (f := f) R - {u}) = (fun x => x + u) ⁻¹' window R := by
      ext y; simp only [Set.mem_sub, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro ⟨p, hp, q, rfl, rfl⟩; simpa using hp
      · intro hy; exact ⟨y + u, hy, u, rfl, by abel⟩
    rw [this]; exact hWmeas.preimage (by fun_prop)
  have hObdd : ∀ u : Fin f → ℂ, Bornology.IsBounded (window (f := f) R ∩ (window R - {u})) :=
    fun u => hWbdd.subset Set.inter_subset_left
  have hOhelper : ∀ u ∈ U,
      Measurable (P (window R ∩ (window R - {u}))) ∧
        IntegrableOn (P (window R ∩ (window R - {u}))) F volume ∧
        ∫ a in F, P (window R ∩ (window R - {u})) a =
          (volume (window (f := f) R ∩ (window R - {u}))).toReal :=
    fun u _ => helper _ (hOmeas u) (hObdd u)
  -- Measurability + integrability of `E`.
  have hEmeas : Measurable E := by
    rw [hEdef]; exact Finset.measurable_sum U (fun u hu => (hOhelper u hu).1)
  have hEint : IntegrableOn E F volume := by
    rw [hEdef]
    exact MeasureTheory.integrable_finset_sum U (fun u hu => (hOhelper u hu).2.1)
  have hNnonneg : ∀ a, 0 ≤ N a := fun a =>
    tsum_nonneg fun l => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hEnonneg : ∀ a, 0 ≤ E a := fun a =>
    Finset.sum_nonneg fun u _ => tsum_nonneg fun l => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  -- `∫_F N = discArea^f`.
  have hNval : ∫ a in F, N a = discArea R ^ f := by
    rw [hNdef, hNval0, SublemmaWindowVolume R hRpos.le, ENNReal.toReal_ofReal (by positivity)]
  -- `∫_F E = U.card * overlapArea^f`.
  have hoverlap_nn : (0 : ℝ) ≤ overlapArea R := ENNReal.toReal_nonneg
  have hEval : ∫ a in F, E a = (U.card : ℝ) * overlapArea R ^ f := by
    rw [hEdef, integral_finset_sum U (fun u hu => (hOhelper u hu).2.1)]
    have hterm : ∀ u ∈ U, ∫ a in F, P (window R ∩ (window R - {u})) a = overlapArea R ^ f := by
      intro u hu
      rw [(hOhelper u hu).2.2, SublemmaOverlapVolume hcm R u (hU_coord u hu),
        ENNReal.toReal_ofReal (by positivity)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  -- Relate the two integrals via `rho`.
  set c : ℝ := (U.card : ℝ) * rho R ^ f with hc
  have hEq : ∫ a in F, E a = c * ∫ a in F, N a := by
    rw [hEval, hNval, hc]
    have hrho : overlapArea R ^ f = rho R ^ f * discArea R ^ f := by
      rw [rho, div_pow, div_mul_cancel₀]
      positivity
    rw [hrho]; ring
  have hNpos : 0 < ∫ a in F, N a := by rw [hNval]; positivity
  have hchc : (0 : ℝ) ≤ c := by
    rw [hc]
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (by rw [rho]; exact div_nonneg hoverlap_nn hdisc_pos.le) f)
  -- `E` vanishes where `N` does.
  have hempty : ∀ a, N a = 0 → E a = 0 := by
    intro a hNa
    have hNc : (Ncount sel DD R a : ℝ) = N a := SublemmaNcountEqTsum hcm sel DD hDD R a
    rw [hNa] at hNc
    have hNc0 : Ncount sel DD R a = 0 := by exact_mod_cast hNc
    have hXfin : (Xset sel DD R a).Finite := (SublemmaLatticeDiscrete hcm sel DD hDD R).1 a
    have hXempty : Xset sel DD R a = ∅ := by
      rw [← Set.ncard_eq_zero hXfin]; exact hNc0
    have hEc0 : Ecount sel DD R U a = 0 := by
      have hidx : {p : (Fin f → ℂ) × (Fin f → ℂ) |
          p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro p hp; rw [hXempty] at hp; exact hp.1
      show {p : (Fin f → ℂ) × (Fin f → ℂ) |
          p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U}.ncard = 0
      rw [hidx, Set.ncard_empty]
    have hEc : (Ecount sel DD R U a : ℝ) = E a := SublemmaEcountEqSumTsum hcm sel DD hDD R U hU_lat a
    rw [← hEc, hEc0]; simp
  -- Pigeonhole.
  obtain ⟨a, hNa_pos, hEa⟩ :=
    SublemmaAveragingPigeonhole F hFpos hFfin N E c hchc hNmeas hEmeas hNnonneg hEnonneg
      hNint hEint hempty hEq hNpos
  refine ⟨a, ?_, ?_⟩
  · -- `Xset` nonempty.
    have hNc : (Ncount sel DD R a : ℝ) = N a := SublemmaNcountEqTsum hcm sel DD hDD R a
    have hNcpos : 0 < Ncount sel DD R a := by
      have : (0 : ℝ) < (Ncount sel DD R a : ℝ) := by rw [hNc]; exact hNa_pos
      exact_mod_cast this
    have hXfin : (Xset sel DD R a).Finite := (SublemmaLatticeDiscrete hcm sel DD hDD R).1 a
    rw [Set.nonempty_iff_ne_empty]
    intro hXe
    rw [Ncount, hXe, Set.ncard_empty] at hNcpos
    exact lt_irrefl 0 hNcpos
  · -- `Ecount ≥ c * Ncount`.
    have hNc : (Ncount sel DD R a : ℝ) = N a := SublemmaNcountEqTsum hcm sel DD hDD R a
    have hEc : (Ecount sel DD R U a : ℝ) = E a := SublemmaEcountEqSumTsum hcm sel DD hDD R U hU_lat a
    rw [ge_iff_le, hEc, hNc]
    exact hEa

end MinkowskiLemmas
