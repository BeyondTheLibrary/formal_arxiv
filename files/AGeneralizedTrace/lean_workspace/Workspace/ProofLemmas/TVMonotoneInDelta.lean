import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.DeletionChannel
import Workspace.Types.TraceDist
import Workspace.Types.TVDistance
import Workspace.PriorWork.DataProcessingTV
import Workspace.ProofLemmas.TraceDeletionKernel
import Workspace.ProofLemmas.TraceDistExists
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.CoinFlipDistUnique
import Workspace.ProofLemmas.DeletionChannelExists
import Workspace.ProofLemmas.DeletionChannelUnique

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.CoinFlipDist
open Workspace.Types.DeletionChannel
open Workspace.Types.TraceDist
open Workspace.Types.TVDistance

namespace TVMonotoneInDelta

open TraceDeletionKernel

/-- The "full trace" of a binary vector: its bits in order, length exactly `n`. -/
def fullTrace {n : ℕ} (b : BinVec n) : Trace n :=
  ⟨List.ofFn b.bit, by rw [List.length_ofFn]⟩

@[simp] lemma fullTrace_bits {n : ℕ} (b : BinVec n) :
    (fullTrace b).bits = List.ofFn b.bit := rfl

lemma fullTrace_length {n : ℕ} (b : BinVec n) :
    (fullTrace b).bits.length = n := by
  rw [fullTrace_bits, List.length_ofFn]

/-- Length-cast equivalence for the full-trace mask domain. -/
def lenEquiv {n : ℕ} (b : BinVec n) :
    (Fin (fullTrace b).bits.length) ≃ Fin n :=
  Fin.castOrderIso (fullTrace_length b) |>.toEquiv

/-- `List.finRange` of a length, reindexed through a length cast. -/
lemma finRange_cast {L n : ℕ} (h : L = n) :
    List.finRange L = (List.finRange n).map (Fin.cast h.symm) := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    rw [List.getElem_finRange, List.getElem_map, List.getElem_finRange]
    rfl

/-- `keep` on the full trace, reindexed through the length cast, equals `restrict`. -/
lemma keep_fullTrace_eq_restrict {n : ℕ} (b : BinVec n)
    (m : Fin n → Bool) :
    keep (fullTrace b) (fun j => m ((lenEquiv b) j)) = restrict b m := by
  unfold keep restrict lenEquiv
  have hlen : (fullTrace b).bits.length = n := fullTrace_length b
  rw [finRange_cast hlen, List.filterMap_map]
  apply List.filterMap_congr
  intro x _
  simp only [Function.comp, fullTrace_bits, List.get_ofFn, Fin.castOrderIso]
  rfl

/-- The deletion channel at rate `δ` on `b` is exactly the trace-deletion kernel
applied to the full trace of `b`. -/
lemma deletionChannel_eq_traceDelete {n : ℕ} (b : BinVec n) (δ : DelProb)
    (dc : DeletionChannel n b δ) :
    dc.toPMF = traceDelete δ.val δ.pos.le δ.lt_one.le (fullTrace b) := by
  apply PMF.ext
  intro τ
  rw [dc.pmf_eq_keep_set_sum τ,
      traceDelete_apply δ.val δ.pos.le δ.lt_one.le (fullTrace b) τ]
  -- Reindex the RHS mask sum from `Fin (fullTrace b).bits.length` to `Fin n`.
  rw [← Equiv.sum_comp (Equiv.arrowCongr (lenEquiv b).symm (Equiv.refl Bool))
        (fun m => (if keep (fullTrace b) m = τ.bits then (1 : ENNReal) else 0) *
          ∏ i : Fin (fullTrace b).bits.length,
            (if m i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val))]
  apply Finset.sum_congr rfl
  intro m _
  -- The reindexed mask equals `m ∘ lenEquiv b`.
  have heq : (Equiv.arrowCongr (lenEquiv b).symm (Equiv.refl Bool)) m
      = (fun j => m ((lenEquiv b) j)) := by
    funext j
    rfl
  rw [heq]
  have hkeep : keep (fullTrace b) (fun j => m ((lenEquiv b) j)) = restrict b m :=
    keep_fullTrace_eq_restrict b m
  rw [hkeep]
  congr 1
  -- Product reindex: ∏ i:Fin n, g (m i) = ∏ j:Fin (len), g (m (lenEquiv j)).
  rw [← Equiv.prod_comp (lenEquiv b)
        (fun i => (if m i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val))]

/-- Canonical form of any trace distribution's PMF: the coin-flip PMF bound to the
deletion-channel family.  Uses the composition law together with uniqueness of the
component distributions. -/
lemma traceDist_canonical {n : ℕ} {S : ProbVec n} {δ : DelProb}
    (td : TraceDist n S δ)
    (cfd : CoinFlipDist n S) (dc : ∀ b : BinVec n, DeletionChannel n b δ) :
    td.toPMF = cfd.toPMF.bind (fun b => (dc b).toPMF) := by
  apply PMF.ext
  intro τ
  rw [td.composition_law cfd dc τ, PMF.bind_apply]

/-- **Per-`b` two-stage deletion identity.**  At rate `δ₁ ≤ δ₂` with post-deletion
rate `q = (δ₂-δ₁)/(1-δ₁)`, the rate-`δ₂` deletion channel equals the rate-`δ₁`
deletion channel followed by the rate-`q` trace-deletion kernel. -/
lemma deletion_two_stage {n : ℕ} (b : BinVec n) (δ₁ δ₂ q : DelProb)
    (h_le : δ₁.val ≤ δ₂.val)
    (h_q : q.val = (δ₂.val - δ₁.val) / (1 - δ₁.val))
    (dc₁ : DeletionChannel n b δ₁) (dc₂ : DeletionChannel n b δ₂) :
    (dc₂ : DeletionChannel n b δ₂).toPMF
      = (dc₁.toPMF).bind (traceDelete q.val q.pos.le q.lt_one.le) := by
  have hcomp : (1 - δ₁.val) * (1 - q.val) = 1 - δ₂.val := by
    rw [h_q]
    have h1 : (0:ℝ) < 1 - δ₁.val := by have := δ₁.lt_one; linarith
    field_simp
    ring
  rw [deletionChannel_eq_traceDelete b δ₁ dc₁,
      deletionChannel_eq_traceDelete b δ₂ dc₂]
  rw [traceDelete_compose q.val (q₁ := δ₁.val) (q := δ₂.val)
        δ₁.pos.le δ₁.lt_one.le q.pos.le q.lt_one.le
        δ₂.pos.le δ₂.lt_one.le (by linarith [hcomp]) (fullTrace b)]

/-- The post-deletion rate `q = (δ₂-δ₁)/(1-δ₁)` as a `DelProb`, valid when
`δ₁ < δ₂`. -/
noncomputable def qDelProb (δ₁ δ₂ : DelProb) (h_lt : δ₁.val < δ₂.val) : DelProb where
  val := (δ₂.val - δ₁.val) / (1 - δ₁.val)
  pos := by
    have h1 : (0:ℝ) < 1 - δ₁.val := by have := δ₁.lt_one; linarith
    apply div_pos <;> linarith
  lt_one := by
    have h1 : (0:ℝ) < 1 - δ₁.val := by have := δ₁.lt_one; linarith
    rw [div_lt_one h1]
    have := δ₂.lt_one
    linarith

end TVMonotoneInDelta

/-- `Trace n` is countable: it injects into `List Bool` via its `bits` field. -/
instance instCountableTrace {n : ℕ} : Countable (Workspace.Types.Trace.Trace n) :=
  Function.Injective.countable
    (f := fun t => t.bits)
    (fun t₁ t₂ h => by cases t₁; cases t₂; simpa using h)

open TVMonotoneInDelta TraceDeletionKernel in
/-- **TV-monotonicity of trace distributions in the deletion rate `δ`** (formerly
admitted as `tv_monotone_in_delta`).  TV between trace distributions can only
decrease as the deletion rate grows, via the data-processing inequality applied to
the post-deletion kernel that factors a rate-`δ₂` deletion through a rate-`δ₁` one. -/
theorem tv_monotone_in_delta :
    ∀ {n : ℕ} {S S' : ProbVec n} {δ₁ δ₂ : DelProb}
      (_hδ : δ₁.val ≤ δ₂.val)
      (td₁S : TraceDist n S δ₁) (td₁S' : TraceDist n S' δ₁)
      (td₂S : TraceDist n S δ₂) (td₂S' : TraceDist n S' δ₂),
    TVDistance td₂S.toPMF td₂S'.toPMF ≤
      TVDistance td₁S.toPMF td₁S'.toPMF := by
  intro n S S' δ₁ δ₂ hδ td₁S td₁S' td₂S td₂S'
  -- Degenerate case δ₁ = δ₂: TraceDist toPMFs coincide via uniqueness of components.
  rcases eq_or_lt_of_le hδ with heq | hlt
  · -- δ₁.val = δ₂.val.  Show the two PMFs agree by canonicalising both sides.
    obtain ⟨cfd⟩ := CoinFlipDistExists S
    obtain ⟨cfd'⟩ := CoinFlipDistExists S'
    -- Build deletion families at both rates; equal-rate ⇒ equal channels by uniqueness.
    have hδeq : δ₁ = δ₂ := by
      cases δ₁; cases δ₂; simp only at heq; subst heq; rfl
    subst hδeq
    have hS : td₂S.toPMF = td₁S.toPMF := by
      have dc : ∀ b : BinVec n, DeletionChannel n b δ₁ := fun b =>
        (DeletionChannelExists b δ₁).some
      rw [traceDist_canonical td₂S cfd dc, traceDist_canonical td₁S cfd dc]
    have hS' : td₂S'.toPMF = td₁S'.toPMF := by
      have dc : ∀ b : BinVec n, DeletionChannel n b δ₁ := fun b =>
        (DeletionChannelExists b δ₁).some
      rw [traceDist_canonical td₂S' cfd' dc, traceDist_canonical td₁S' cfd' dc]
    rw [hS, hS']
  · -- δ₁.val < δ₂.val: genuine data-processing step.
    set q : DelProb := qDelProb δ₁ δ₂ hlt with hq
    have hq_val : q.val = (δ₂.val - δ₁.val) / (1 - δ₁.val) := rfl
    -- Choose component witnesses.
    obtain ⟨cfd⟩ := CoinFlipDistExists S
    obtain ⟨cfd'⟩ := CoinFlipDistExists S'
    have dc₁ : ∀ b : BinVec n, DeletionChannel n b δ₁ := fun b =>
      (DeletionChannelExists b δ₁).some
    have dc₂ : ∀ b : BinVec n, DeletionChannel n b δ₂ := fun b =>
      (DeletionChannelExists b δ₂).some
    set K : Trace n → PMF (Trace n) := traceDelete q.val q.pos.le q.lt_one.le with hK
    -- td₂.toPMF = td₁.toPMF.bind K (for both S and S').
    have key : ∀ {S : ProbVec n} (cfdS : CoinFlipDist n S)
        (td₁ : TraceDist n S δ₁) (td₂ : TraceDist n S δ₂),
        td₂.toPMF = (td₁.toPMF).bind K := by
      intro S cfdS td₁ td₂
      rw [traceDist_canonical td₂ cfdS dc₂, traceDist_canonical td₁ cfdS dc₁,
          PMF.bind_bind]
      have hfun : (fun b => (dc₂ b).toPMF)
          = (fun b => ((dc₁ b).toPMF).bind K) := by
        funext b
        rw [hK]
        exact deletion_two_stage b δ₁ δ₂ q hδ hq_val (dc₁ b) (dc₂ b)
      rw [hfun]
    have hSbind : td₂S.toPMF = (td₁S.toPMF).bind K := key cfd td₁S td₂S
    have hS'bind : td₂S'.toPMF = (td₁S'.toPMF).bind K := key cfd' td₁S' td₂S'
    -- Apply the data-processing inequality.
    have hdpi :=
      DataProcessingTV (α := Trace n) (β := Trace n) K td₁S.toPMF td₁S'.toPMF
    -- Reconcile with TVDistance.
    rw [TVDistance, TVDistance, hSbind, hS'bind]
    exact hdpi
