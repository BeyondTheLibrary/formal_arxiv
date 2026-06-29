import Mathlib
import Workspace.Types.Trace
import Workspace.ProofLemmas.TraceDeletionListCompose

open Workspace.Types.Trace

namespace TraceDeletionKernel

/-- Per-coordinate Bernoulli factor for the post-deletion process: keep (true)
with probability `1 - q`, delete (false) with probability `q`. -/
private noncomputable def factor (q : ℝ) (bit : Bool) : ENNReal :=
  ENNReal.ofReal (if bit then (1 - q) else q)

private lemma factor_sum_eq_one (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ bit : Bool, factor q bit = 1 := by
  have hone_minus : (0 : ℝ) ≤ 1 - q := by linarith
  rw [Fintype.sum_bool]
  unfold factor
  show ENNReal.ofReal (1 - q) + ENNReal.ofReal q = 1
  rw [← ENNReal.ofReal_add hone_minus hq]
  have hadd : (1 - q) + q = 1 := by ring
  rw [hadd]
  exact ENNReal.ofReal_one

/-- The product mass over a mask `m : Fin k → Bool`. -/
private noncomputable def prodMass {k : ℕ} (q : ℝ) (m : Fin k → Bool) : ENNReal :=
  ∏ i : Fin k, factor q (m i)

private lemma sum_prodMass_eq_one {k : ℕ} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ m : (Fin k → Bool), prodMass q m = 1 := by
  unfold prodMass
  have hsum_eq : (∑ m : Fin k → Bool, ∏ i : Fin k, factor q (m i))
      = ∑ x ∈ Fintype.piFinset (fun (_ : Fin k) => (Finset.univ : Finset Bool)),
          ∏ i : Fin k, factor q (x i) := rfl
  rw [hsum_eq, ← Finset.prod_univ_sum]
  rw [show (∑ b : Bool, factor q b) = 1 from factor_sum_eq_one q hq hq1]
  exact Finset.prod_const_one

/-- The mask PMF on `Fin k → Bool`. -/
private noncomputable def maskPMF {k : ℕ} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    PMF (Fin k → Bool) :=
  PMF.ofFintype (prodMass q) (sum_prodMass_eq_one q hq hq1)

private lemma maskPMF_apply {k : ℕ} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (m : Fin k → Bool) :
    maskPMF q hq hq1 m = ∏ i : Fin k, factor q (m i) := by
  unfold maskPMF
  rw [PMF.ofFintype_apply]
  rfl

/-- Restriction of an input trace `t` to the positions where the mask `m` is
true, in original order.  `m` ranges over the input trace's own positions
`Fin t.bits.length`. -/
def keep {n : ℕ} (t : Trace n) (m : Fin t.bits.length → Bool) : List Bool :=
  (List.finRange t.bits.length).filterMap
    (fun i => if m i then some (t.bits.get i) else none)

/-- The kept sublist has length at most `n`. -/
private lemma keep_length_le {n : ℕ} (t : Trace n) (m : Fin t.bits.length → Bool) :
    (keep t m).length ≤ n := by
  unfold keep
  calc ((List.finRange t.bits.length).filterMap
          (fun i => if m i then some (t.bits.get i) else none)).length
      ≤ (List.finRange t.bits.length).length := List.length_filterMap_le _ _
    _ = t.bits.length := List.length_finRange
    _ ≤ n := t.length_le

/-- **Bridge between the kernel's `keep` and the list-level `keepWith`.**  The
`Fin`-mask keep operation on a trace's bit list coincides with the reindexing-free
list-level `keepWith` applied to the decision list `List.ofFn m`. -/
lemma keep_eq_keepWith {n : ℕ} (t : Trace n) (m : Fin t.bits.length → Bool) :
    keep t m = TraceDeletionListCompose.keepWith t.bits (List.ofFn m) := by
  rw [TraceDeletionListCompose.keepWith_ofFn]
  rfl

/-- The trace produced from input `t` by keeping the positions selected by `m`. -/
def traceOf {n : ℕ} (t : Trace n) (m : Fin t.bits.length → Bool) : Trace n :=
  ⟨keep t m, keep_length_le t m⟩

/-- The post-deletion kernel: given an input trace `t`, delete each of its bits
independently (keep with probability `1 - q`, drop with probability `q`) and
output the resulting trace.  Built as the push-forward of the mask PMF through
`traceOf`. -/
noncomputable def traceDelete {n : ℕ} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (t : Trace n) : PMF (Trace n) :=
  (maskPMF q hq hq1).map (traceOf t)

/-- Keep-set sum formula for the post-deletion kernel. -/
lemma traceDelete_apply {n : ℕ} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (t : Trace n) (τ : Trace n) :
    (traceDelete q hq hq1 t : Trace n → ENNReal) τ =
      ∑ m : Fin t.bits.length → Bool,
        (if keep t m = τ.bits then (1 : ENNReal) else 0) *
          ∏ i : Fin t.bits.length,
            (if m i then ENNReal.ofReal (1 - q) else ENNReal.ofReal q) := by
  unfold traceDelete
  rw [PMF.map_apply]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro m _
  rw [maskPMF_apply]
  have hprod : (∏ i : Fin t.bits.length, factor q (m i))
      = ∏ i : Fin t.bits.length,
          (if m i then ENNReal.ofReal (1 - q) else ENNReal.ofReal q) := by
    apply Finset.prod_congr rfl
    intro i _
    unfold factor
    split <;> rfl
  rw [hprod]
  have hcond : (τ = traceOf t m) ↔ (keep t m = τ.bits) := by
    unfold traceOf
    rw [Trace.mk.injEq]
    exact eq_comm
  by_cases hc : keep t m = τ.bits
  · rw [if_pos hc]
    rw [if_pos (hcond.mpr hc)]
    rw [one_mul]
  · rw [if_neg hc]
    rw [if_neg (fun h => hc (hcond.mp h))]
    rw [zero_mul]

/-- **Per-coordinate factor composition.**  When the keep-probabilities compose
multiplicatively, `(1 - q₁)·(1 - q₂) = (1 - q)`, the two-stage Bernoulli
keep-factor at a *surviving* position (kept by both stages) equals the
single-stage rate-`q` keep-factor.  This is the per-coordinate identity that any
future proof of the full kernel-composition law
`(traceDelete q₁ t).bind (traceDelete q₂) = traceDelete q t` must rely on.

(The full composition law itself is NOT proved here: the second-stage mask ranges
over `Fin t'.bits.length` of the *intermediate* trace `t'`, whose length is
random, so combining the two stages into a single mask over `Fin t.bits.length`
requires reindexing the second mask onto the surviving positions of a
variable-length list — a sublist-reindexing argument that is deliberately left as
future infrastructure.) -/
lemma factor_keep_compose (q₁ q₂ q : ℝ)
    (hq₁1 : q₁ ≤ 1)
    (hcomp : (1 - q₁) * (1 - q₂) = 1 - q) :
    factor q₁ true * factor q₂ true = factor q true := by
  unfold factor
  simp only [if_true]
  rw [← ENNReal.ofReal_mul (by linarith), hcomp]

/-- **Reduction of the two-stage bind to a mask-sum (sorry-free).**  The
composition `(traceDelete q₁ t).bind (traceDelete q₂)` evaluated at an output
trace `τ` is the finite double sum: outer over the stage-one mask
`x : Fin t.bits.length → Bool` (weighted by the rate-`q₁` product mass), inner over
the *survivor-length* stage-two mask `m : Fin (keep (traceOf t x)).length → Bool`.
This is the concrete object the kernel-composition law must marginalize. -/
lemma traceDelete_bind_apply {n : ℕ} (q₁ q₂ : ℝ)
    (hq₁ : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1)
    (hq₂ : 0 ≤ q₂) (hq₂1 : q₂ ≤ 1)
    (t : Trace n) (τ : Trace n) :
    ((traceDelete q₁ hq₁ hq₁1 t).bind (traceDelete q₂ hq₂ hq₂1) : Trace n → ENNReal) τ
      = ∑ x : Fin t.bits.length → Bool,
          (∏ i : Fin t.bits.length, factor q₁ (x i)) *
            ∑ m : Fin (keep t x).length → Bool,
              (if keep (traceOf t x) m = τ.bits then (1 : ENNReal) else 0) *
                ∏ i : Fin (keep t x).length,
                  (if m i then ENNReal.ofReal (1 - q₂) else ENNReal.ofReal q₂) := by
  have hbm : (traceDelete q₁ hq₁ hq₁1 t).bind (traceDelete q₂ hq₂ hq₂1)
      = (maskPMF q₁ hq₁ hq₁1).bind (fun m₁ => traceDelete q₂ hq₂ hq₂1 (traceOf t m₁)) := by
    unfold traceDelete
    rw [PMF.bind_map]
    rfl
  rw [hbm, PMF.bind_apply, tsum_fintype]
  simp only [maskPMF_apply, traceDelete_apply]
  rfl

/-- **Kernel composition law for the trace-deletion channel.**
Running an independent rate-`q₁` deletion followed by an independent rate-`q₂`
deletion produces the same trace distribution as a single rate-`q` deletion,
provided the keep-probabilities compose multiplicatively
`(1 - q₁) * (1 - q₂) = 1 - q`. -/
theorem traceDelete_compose {n : ℕ} (q₁ q₂ q : ℝ)
    (hq₁ : 0 ≤ q₁) (hq₁1 : q₁ ≤ 1)
    (hq₂ : 0 ≤ q₂) (hq₂1 : q₂ ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hcomp : (1 - q₁) * (1 - q₂) = 1 - q)
    (t : Trace n) :
    (traceDelete q₁ hq₁ hq₁1 t).bind (traceDelete q₂ hq₂ hq₂1)
      = traceDelete q hq hq1 t := by
  classical
  -- Numeric facts feeding `master`.
  have hT : factor q₁ true * factor q₂ true = factor q true :=
    factor_keep_compose q₁ q₂ q hq₁1 hcomp
  have hF : factor q₁ false + factor q₁ true * factor q₂ false = factor q false := by
    show ENNReal.ofReal (if (false : Bool) then (1 - q₁) else q₁)
        + ENNReal.ofReal (if (true : Bool) then (1 - q₁) else q₁)
          * ENNReal.ofReal (if (false : Bool) then (1 - q₂) else q₂)
        = ENNReal.ofReal (if (false : Bool) then (1 - q) else q)
    simp only [if_true, if_false, Bool.false_eq_true]
    rw [← ENNReal.ofReal_mul (by linarith)]
    rw [← ENNReal.ofReal_add hq₁ (by nlinarith)]
    congr 1
    nlinarith [hcomp]
  -- Folding the `if ... ofReal` form back into `factor`.
  have hfold : ∀ (r : ℝ) (bit : Bool),
      (if bit = true then ENNReal.ofReal (1 - r) else ENNReal.ofReal r) = factor r bit := by
    intro r bit; unfold factor; cases bit <;> simp
  apply PMF.ext; intro τ
  rw [traceDelete_bind_apply q₁ q₂ hq₁ hq₁1 hq₂ hq₂1 t τ,
      traceDelete_apply q hq hq1 t τ]
  set g : List Bool → ENNReal := fun l => if l = τ.bits then (1 : ENNReal) else 0 with hg
  -- Rewrite RHS into master's RHS shape.
  have hRHS :
      (∑ m : Fin t.bits.length → Bool,
          (if keep t m = τ.bits then (1 : ENNReal) else 0) *
            ∏ i : Fin t.bits.length,
              (if m i = true then ENNReal.ofReal (1 - q) else ENNReal.ofReal q))
        = ∑ e : Fin t.bits.length → Bool,
            g (TraceDeletionListCompose.keepWith t.bits (List.ofFn e)) *
              TraceDeletionListCompose.dWeight (factor q) (List.ofFn e) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [TraceDeletionListCompose.dWeight_ofFn]
    simp only [hfold]
    rw [← keep_eq_keepWith t e]
  -- Rewrite LHS into master's LHS shape.
  have hLHS :
      (∑ x : Fin t.bits.length → Bool,
          (∏ i : Fin t.bits.length, factor q₁ (x i)) *
            ∑ m : Fin (keep t x).length → Bool,
              (if keep (traceOf t x) m = τ.bits then (1 : ENNReal) else 0) *
                ∏ i : Fin (keep t x).length,
                  (if m i = true then ENNReal.ofReal (1 - q₂) else ENNReal.ofReal q₂))
        = ∑ x : Fin t.bits.length → Bool,
            TraceDeletionListCompose.dWeight (factor q₁) (List.ofFn x) *
              TraceDeletionListCompose.innerS (factor q₂) g
                (TraceDeletionListCompose.keepWith t.bits (List.ofFn x)) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [← TraceDeletionListCompose.dWeight_ofFn (factor q₁) t.bits.length x]
    congr 1
    -- inner sum = innerS
    have hkx : keep t x = TraceDeletionListCompose.keepWith t.bits (List.ofFn x) :=
      keep_eq_keepWith t x
    rw [← hkx]
    -- now both index types are Fin (keep t x).length
    unfold TraceDeletionListCompose.innerS
    apply Finset.sum_congr rfl
    intro m _
    rw [TraceDeletionListCompose.dWeight_ofFn]
    simp only [hfold]
    -- relate keep (traceOf t x) m to keepWith (keep t x) (ofFn m)
    have hkm : keep (traceOf t x) m
        = TraceDeletionListCompose.keepWith (keep t x) (List.ofFn m) := by
      have := keep_eq_keepWith (traceOf t x) m
      simpa [traceOf] using this
    rw [hkm, mul_comm]
  rw [hLHS, hRHS]
  exact TraceDeletionListCompose.master (factor q₁) (factor q₂) (factor q) hT hF t.bits g

end TraceDeletionKernel
