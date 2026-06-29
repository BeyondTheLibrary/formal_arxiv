import Mathlib
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.FqHasUniqueInteriorZero
import Workspace.ProofLemmas.LBConstruction
import Workspace.ProofLemmas.LBSocialCosts
import Workspace.ProofLemmas.AStarLessThanOneHalf

open Workspace.Types.SocialCost
open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.LBConstruction
open Filter Topology

namespace Workspace.ProofLemmas.LBRatioLimit

/-- The lower-bound ratio converges to `R = Φ(a*)` (one-sided ε-bound form):
for every `η > 0` there exists `d ≥ 1` such that the social-cost ratio of the
all-zero facility to the optimal facility on `P_LB q d t` is at least `R − η`.
Here `R` is written out explicitly as `num(a*) / denomBase(a*)^{1/q}`, the same
expression as in `LBRatioEqualsUB`. `D(a*) > 0` is taken as a hypothesis. -/
theorem LBRatioLimit (q : ℝ) (hq : 1 < q) (t : ℕ) (ht : 1 ≤ t)
    (hD : 0 < (c_star q / (1 - c_star q)) ^ q * (a_star q) + (1 - a_star q)) :
    ∀ η : ℝ, 0 < η → ∃ d : ℕ, 1 ≤ d ∧
      ( ( (1 / (1 - c_star q)) * (a_star q) ^ ((1:ℝ)/q) + (1 - 2 * a_star q) )
        / ( (c_star q / (1 - c_star q)) ^ q * (a_star q) + (1 - a_star q) ) ^ ((1:ℝ)/q) )
        - η
      ≤ socialCost q (P_LB q d t) (fun _ : Fin d => (0 : ℝ))
          / socialCost q (P_LB q d t) (f_opt d) := by
  intro η hη
  have hq_pos : (0:ℝ) < q := lt_trans zero_lt_one hq
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  obtain ⟨ha_pos, ha_lt_half⟩ := AStarLessThanOneHalf q hq
  -- The ratio function as a function of θ = k/d.
  set Φ : ℝ → ℝ := fun θ =>
      ( (1 / (1 - c_star q)) * θ ^ ((1:ℝ)/q) + (1 - 2 * θ) )
      / ( (c_star q / (1 - c_star q)) ^ q * θ + (1 - θ) ) ^ ((1:ℝ)/q) with hΦ
  -- Continuity of Φ at θ = a*.
  have hcont : ContinuousAt Φ (a_star q) := by
    rw [hΦ]
    have hnum : ContinuousAt
        (fun θ : ℝ => (1 / (1 - c_star q)) * θ ^ ((1:ℝ)/q) + (1 - 2 * θ)) (a_star q) := by
      apply ContinuousAt.add
      · apply ContinuousAt.mul continuousAt_const
        apply ContinuousAt.rpow_const continuousAt_id
        left; exact ne_of_gt ha_pos
      · exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    have hbase : ContinuousAt
        (fun θ : ℝ => (c_star q / (1 - c_star q)) ^ q * θ + (1 - θ)) (a_star q) :=
      (continuousAt_const.mul continuousAt_id).add (continuousAt_const.sub continuousAt_id)
    have hden : ContinuousAt
        (fun θ : ℝ => ((c_star q / (1 - c_star q)) ^ q * θ + (1 - θ)) ^ ((1:ℝ)/q)) (a_star q) := by
      apply ContinuousAt.rpow_const hbase
      left; exact ne_of_gt hD
    have hden_ne : ((c_star q / (1 - c_star q)) ^ q * (a_star q) + (1 - a_star q)) ^ ((1:ℝ)/q) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hD _)
    exact hnum.div hden hden_ne
  -- θ_d = ⌊a* d⌋ / d → a* as d → ∞.
  have htend : Tendsto (fun d : ℕ => (kCount q d : ℝ) / (d : ℝ)) atTop (nhds (a_star q)) := by
    have hbase := tendsto_nat_floor_mul_div_atTop (R := ℝ) (le_of_lt ha_pos)
    have hcast : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have := hbase.comp hcast
    simpa [kCount, Function.comp] using this
  -- Φ(θ_d) → Φ(a*) = R.
  have hcomp : Tendsto (fun d : ℕ => Φ ((kCount q d : ℝ) / (d : ℝ))) atTop
      (nhds (Φ (a_star q))) := hcont.tendsto.comp htend
  -- Φ(a*) is exactly R (the statement's left expression).
  have hΦa : Φ (a_star q) =
      ( (1 / (1 - c_star q)) * (a_star q) ^ ((1:ℝ)/q) + (1 - 2 * a_star q) )
      / ( (c_star q / (1 - c_star q)) ^ q * (a_star q) + (1 - a_star q) ) ^ ((1:ℝ)/q) := by
    rw [hΦ]
  rw [hΦa] at hcomp
  -- Extract a concrete large d with Φ(θ_d) ≥ R − η.
  rw [Metric.tendsto_atTop] at hcomp
  obtain ⟨N, hN⟩ := hcomp η hη
  refine ⟨max N 1, le_trans (le_max_right N 1) (le_refl _), ?_⟩
  set d := max N 1 with hd_def
  have hd1 : 1 ≤ d := le_max_right N 1
  have hdN : N ≤ d := le_max_left N 1
  have hdist := hN d hdN
  -- relate Φ(θ_d) to the actual social-cost ratio
  have hratio := (LBSocialCosts q hq d hd1 t ht).2.2
  rw [Real.dist_eq] at hdist
  have hge : ( (1 / (1 - c_star q)) * (a_star q) ^ ((1:ℝ)/q) + (1 - 2 * a_star q) )
      / ( (c_star q / (1 - c_star q)) ^ q * (a_star q) + (1 - a_star q) ) ^ ((1:ℝ)/q)
      - η ≤ Φ ((kCount q d : ℝ) / (d : ℝ)) := by
    have := abs_lt.mp hdist
    linarith [this.1]
  -- Φ(θ_d) = ratio(d)
  have hΦeq : Φ ((kCount q d : ℝ) / (d : ℝ))
      = socialCost q (P_LB q d t) (fun _ : Fin d => (0 : ℝ))
          / socialCost q (P_LB q d t) (f_opt d) := by
    rw [hΦ, hratio]
  rw [hΦeq] at hge
  exact hge

end Workspace.ProofLemmas.LBRatioLimit
