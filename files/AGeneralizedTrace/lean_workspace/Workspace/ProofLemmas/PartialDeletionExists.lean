import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.DeletionChannel
import Workspace.Types.PartialDeletionProcess
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.CoinFlipDistUnique
import Workspace.ProofLemmas.MiddleIndicatorSumsToOne
import Workspace.ProofLemmas.DeletionChannelTotalMass
import Workspace.ProofLemmas.LengthsOnlyExists

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess

open scoped Classical

namespace PartialDeletionExistsScratch

/-- Inner factor F(r) = 1 for in-range r (partial version, per-b). -/
lemma Fr_eq_one_partial (n : ℕ) (δ : DelProb) (b : BinVec n) (r : ℤ)
    (h : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)) :
    (∑' (m : BinVec (n/2)) (t₁ : Trace n) (t₂ : Trace n),
        prefixWeight n b δ r t₁ *
          (suffixWeight n b δ r t₂ * middleIndicator n b m r)) = 1 := by
  -- Convert hypotheses to the ℤ-division form used by DeletionChannelTotalMass / MiddleIndicator.
  have h_lo : 0 ≤ r + (n / 4 : ℤ) := by
    rw [← DeletionChannelTotalMassProof.nat_div_four_cast]; exact h.1
  have h_hi : r + (n / 4 : ℤ) ≤ (n / 2 : ℤ) := by
    rw [← DeletionChannelTotalMassProof.nat_div_four_cast,
        ← DeletionChannelTotalMassProof.nat_div_two_cast]; exact h.2
  have hmid : (∑' m : BinVec (n/2), middleIndicator n b m r) = 1 :=
    MiddleIndicatorSumsToOne b r h_lo h_hi
  have hpre : (∑' t : Trace n, prefixWeight n b δ r t) = 1 :=
    (DeletionChannelTotalMass b δ r h_lo h_hi).1
  have hsuf : (∑' t : Trace n, suffixWeight n b δ r t) = 1 :=
    (DeletionChannelTotalMass b δ r h_lo h_hi).2
  -- collapse t₂
  have step1 : ∀ (m : BinVec (n/2)) (t₁ : Trace n),
      (∑' t₂ : Trace n, prefixWeight n b δ r t₁ *
          (suffixWeight n b δ r t₂ * middleIndicator n b m r))
        = prefixWeight n b δ r t₁ * middleIndicator n b m r := by
    intro m t₁
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' t₂ : Trace n, suffixWeight n b δ r t₂ * middleIndicator n b m r)
          = (∑' t₂ : Trace n, suffixWeight n b δ r t₂) * middleIndicator n b m r from by
        rw [ENNReal.tsum_mul_right]]
    rw [hsuf, one_mul]
  simp only [step1]
  -- collapse t₁
  have step2 : ∀ (m : BinVec (n/2)),
      (∑' t₁ : Trace n, prefixWeight n b δ r t₁ * middleIndicator n b m r)
        = middleIndicator n b m r := by
    intro m
    rw [ENNReal.tsum_mul_right, hpre, one_mul]
  simp only [step2]
  exact hmid

/-- The mass function for fixed b (partial version). -/
noncomputable def gmassP (n : ℕ) (δ : DelProb) (b : BinVec n)
    (p : BinVec (n/2) × Trace n × Trace n) : ENNReal :=
  ∑' r : ℤ,
    offsetWeight n r *
      (prefixWeight n b δ r p.2.1 *
        (suffixWeight n b δ r p.2.2 *
          middleIndicator n b p.1 r))

lemma gmassP_tsum (n : ℕ) (δ : DelProb) (b : BinVec n) :
    (∑' p : BinVec (n/2) × Trace n × Trace n, gmassP n δ b p) = 1 := by
  unfold gmassP
  rw [ENNReal.tsum_comm]
  rw [show (∑' (r : ℤ) (p : BinVec (n/2) × Trace n × Trace n),
        offsetWeight n r * (prefixWeight n b δ r p.2.1 *
          (suffixWeight n b δ r p.2.2 * middleIndicator n b p.1 r)))
      = ∑' r : ℤ, offsetWeight n r from by
    apply tsum_congr
    intro r
    by_cases hr : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)
    · rw [ENNReal.tsum_mul_left]
      have hinner : (∑' (p : BinVec (n/2) × Trace n × Trace n),
            prefixWeight n b δ r p.2.1 *
              (suffixWeight n b δ r p.2.2 * middleIndicator n b p.1 r)) = 1 := by
        rw [ENNReal.tsum_prod']
        rw [show (∑' (m : BinVec (n/2)) (q : Trace n × Trace n),
              prefixWeight n b δ r (m, q).2.1 *
                (suffixWeight n b δ r (m, q).2.2 * middleIndicator n b (m, q).1 r))
            = (∑' (m : BinVec (n/2)) (t₁ : Trace n) (t₂ : Trace n),
              prefixWeight n b δ r t₁ *
                (suffixWeight n b δ r t₂ * middleIndicator n b m r)) from by
          refine tsum_congr (fun m => ?_)
          rw [ENNReal.tsum_prod']]
        exact Fr_eq_one_partial n δ b r hr
      rw [hinner, mul_one]
    · have : offsetWeight n r = 0 := by unfold offsetWeight; rw [dif_neg hr]
      rw [this]
      simp]
  exact LengthsOnlyExistsScratch.offsetWeight_tsum n

/-- The inner PMF built from gmassP. -/
noncomputable def innerPMFp (n : ℕ) (δ : DelProb) (b : BinVec n) :
    PMF (BinVec (n/2) × Trace n × Trace n) :=
  ⟨gmassP n δ b, (Summable.hasSum_iff ENNReal.summable).mpr (gmassP_tsum n δ b)⟩

end PartialDeletionExistsScratch

theorem partial_exists :
    ∀ {n : ℕ} (S : Workspace.Types.ProbVec.ProbVec n) (δ : Workspace.Types.DelProb.DelProb),
      Nonempty (Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n S δ) := by
  intro n S δ
  obtain ⟨cfd₀⟩ := CoinFlipDistExists S
  refine ⟨{
    toPMF := cfd₀.toPMF.bind (fun b => PartialDeletionExistsScratch.innerPMFp n δ b)
    composition_law := ?_ }⟩
  intro cfd m t₁ t₂
  simp only [PMF.bind_apply]
  apply tsum_congr; intro b
  rw [CoinFlipDistUnique S cfd₀ cfd]
  conv_rhs => rw [ENNReal.tsum_mul_left]
  congr 1
