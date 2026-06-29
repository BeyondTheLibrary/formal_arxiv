import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.DeletionChannel

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.DeletionChannel

namespace DeletionChannelExistsProof

/-- Per-coordinate Bernoulli factor for the deletion process: keep (true) with
probability `1 - δ`, delete (false) with probability `δ`. -/
private noncomputable def factor (δ : DelProb) (bit : Bool) : ENNReal :=
  ENNReal.ofReal (if bit then (1 - δ.val) else δ.val)

private lemma factor_sum_eq_one (δ : DelProb) :
    ∑ bit : Bool, factor δ bit = 1 := by
  have hp_nn : (0 : ℝ) ≤ δ.val := δ.pos.le
  have hone_minus : (0 : ℝ) ≤ 1 - δ.val := by have := δ.lt_one; linarith
  rw [Fintype.sum_bool]
  unfold factor
  show ENNReal.ofReal (1 - δ.val) + ENNReal.ofReal δ.val = 1
  rw [← ENNReal.ofReal_add hone_minus hp_nn]
  have hadd : (1 - δ.val) + δ.val = 1 := by ring
  rw [hadd]
  exact ENNReal.ofReal_one

/-- The product mass over a mask `m : Fin n → Bool`. -/
private noncomputable def prodMass {n : ℕ} (δ : DelProb) (m : Fin n → Bool) : ENNReal :=
  ∏ i : Fin n, factor δ (m i)

private lemma sum_prodMass_eq_one {n : ℕ} (δ : DelProb) :
    ∑ m : (Fin n → Bool), prodMass δ m = 1 := by
  unfold prodMass
  have hsum_eq : (∑ m : Fin n → Bool, ∏ i : Fin n, factor δ (m i))
      = ∑ x ∈ Fintype.piFinset (fun (_ : Fin n) => (Finset.univ : Finset Bool)),
          ∏ i : Fin n, factor δ (x i) := rfl
  rw [hsum_eq, ← Finset.prod_univ_sum]
  rw [show (∑ b : Bool, factor δ b) = 1 from factor_sum_eq_one δ]
  exact Finset.prod_const_one

/-- The mask PMF on `Fin n → Bool`. -/
private noncomputable def maskPMF {n : ℕ} (δ : DelProb) : PMF (Fin n → Bool) :=
  PMF.ofFintype (prodMass δ) (sum_prodMass_eq_one δ)

private lemma maskPMF_apply {n : ℕ} (δ : DelProb) (m : Fin n → Bool) :
    maskPMF δ m = ∏ i : Fin n, factor δ (m i) := by
  unfold maskPMF
  rw [PMF.ofFintype_apply]
  rfl

/-- The deletion output has length at most `n`. -/
private lemma restrict_length_le {n : ℕ} (b : BinVec n) (m : Fin n → Bool) :
    (restrict b m).length ≤ n := by
  show ((List.finRange n).filterMap (fun i => if m i then some (b.bit i) else none)).length ≤ n
  calc ((List.finRange n).filterMap (fun i => if m i then some (b.bit i) else none)).length
      ≤ (List.finRange n).length := List.length_filterMap_le _ _
    _ = n := List.length_finRange

/-- The trace produced by a mask. -/
private def traceOf {n : ℕ} (b : BinVec n) (m : Fin n → Bool) : Trace n :=
  ⟨restrict b m, restrict_length_le b m⟩

/-- The deletion-channel PMF: push the mask PMF forward through `traceOf`. -/
private noncomputable def dcPMF {n : ℕ} (b : BinVec n) (δ : DelProb) : PMF (Trace n) :=
  (maskPMF δ).map (traceOf b)

private lemma dcPMF_apply {n : ℕ} (b : BinVec n) (δ : DelProb) (τ : Trace n) :
    (dcPMF b δ : Trace n → ENNReal) τ =
      ∑ m : Fin n → Bool,
        (if restrict b m = τ.bits then (1 : ENNReal) else 0) *
          ∏ i : Fin n,
            (if m i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) := by
  unfold dcPMF
  rw [PMF.map_apply]
  rw [tsum_fintype]
  -- ∑ m, if τ = traceOf b m then maskPMF δ m else 0
  apply Finset.sum_congr rfl
  intro m _
  rw [maskPMF_apply]
  -- LHS term: if τ = traceOf b m then ∏ factor δ (m i) else 0
  -- align the product factor first
  have hprod : (∏ i : Fin n, factor δ (m i))
      = ∏ i : Fin n, (if m i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) := by
    apply Finset.prod_congr rfl
    intro i _
    unfold factor
    split <;> rfl
  rw [hprod]
  -- align the condition: τ = traceOf b m ↔ restrict b m = τ.bits
  have hcond : (τ = traceOf b m) ↔ (restrict b m = τ.bits) := by
    unfold traceOf
    rw [Trace.mk.injEq]
    exact eq_comm
  by_cases hc : restrict b m = τ.bits
  · rw [if_pos hc]
    rw [if_pos (hcond.mpr hc)]
    rw [one_mul]
  · rw [if_neg hc]
    rw [if_neg (fun h => hc (hcond.mp h))]
    rw [zero_mul]

end DeletionChannelExistsProof

theorem DeletionChannelExists :
    ∀ {n : ℕ} (b : Workspace.Types.BinVec.BinVec n) (δ : Workspace.Types.DelProb.DelProb),
      Nonempty (Workspace.Types.DeletionChannel.DeletionChannel n b δ) := by
  intro n b δ
  refine ⟨{
    toPMF := DeletionChannelExistsProof.dcPMF b δ
    pmf_eq_keep_set_sum := ?_
  }⟩
  intro τ
  exact DeletionChannelExistsProof.dcPMF_apply b δ τ
