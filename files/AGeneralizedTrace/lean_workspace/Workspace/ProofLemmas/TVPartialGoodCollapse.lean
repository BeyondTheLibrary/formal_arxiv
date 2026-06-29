import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.DeletionLengthMarginal
import Workspace.ProofLemmas.TraceFromZeroIsLengthBinomial
import Workspace.ProofLemmas.TVPartialBoundedHelpers

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open TVPartialBoundedHelpers

open scoped Classical

namespace TVPartialGoodCollapse

variable {n : ℕ}

/-- The all-zero trace of length `z` (requires `z ≤ n`). -/
def allZeroTrace (n : ℕ) (z : ℕ) (hz : z ≤ n) : Workspace.Types.Trace.Trace n :=
  ⟨List.replicate z false, by rw [List.length_replicate]; exact hz⟩

@[simp] lemma allZeroTrace_bits (n z : ℕ) (hz : z ≤ n) :
    (allZeroTrace n z hz).bits = List.replicate z false := rfl

@[simp] lemma allZeroTrace_length (n z : ℕ) (hz : z ≤ n) :
    (allZeroTrace n z hz).bits.length = z := by
  simp [allZeroTrace]

/-- `true` is not a member of an all-zero trace's bits. -/
lemma allZeroTrace_not_mem_true (n z : ℕ) (hz : z ≤ n) :
    true ∉ (allZeroTrace n z hz).bits := by
  simp only [allZeroTrace_bits]
  intro h
  have := List.eq_of_mem_replicate h
  exact Bool.noConfusion this

/-- `binomialPMF len δ z = 0` whenever `z > len`. -/
lemma binomialPMF_eq_zero_of_gt (len : ℕ) (δ : Workspace.Types.DelProb.DelProb)
    (z : ℕ) (h : len < z) :
    Workspace.Types.LengthsOnlyProcess.binomialPMF len δ z = 0 := by
  unfold Workspace.Types.LengthsOnlyProcess.binomialPMF
  rw [Nat.choose_eq_zero_of_lt h]
  simp

/-- `prefixLengthWeight n δ r z = 0` whenever `z > n` (the prefix length never
exceeds `n/2 ≤ n`). -/
lemma prefixLengthWeight_eq_zero_of_gt (δ : Workspace.Types.DelProb.DelProb)
    (r : ℤ) (z : ℕ) (h : n < z) :
    Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r z = 0 := by
  unfold Workspace.Types.LengthsOnlyProcess.prefixLengthWeight
  simp only []; split_ifs with hk
  · apply binomialPMF_eq_zero_of_gt
    -- k.toNat ≤ n/2 ≤ n < z
    have hk2 : (r + (n / 4 : ℕ) : ℤ) ≤ (n / 2 : ℕ) := hk.2
    have : (r + (n / 4 : ℕ) : ℤ).toNat ≤ (n / 2 : ℕ) := by
      have := Int.toNat_le.mpr hk2
      simpa using this
    have h2 : (n / 2 : ℕ) ≤ n := Nat.div_le_self n 2
    omega
  · rfl

/-- `suffixLengthWeight n δ r z = 0` whenever `z > n`. -/
lemma suffixLengthWeight_eq_zero_of_gt (δ : Workspace.Types.DelProb.DelProb)
    (r : ℤ) (z : ℕ) (h : n < z) :
    Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r z = 0 := by
  unfold Workspace.Types.LengthsOnlyProcess.suffixLengthWeight
  simp only []; split_ifs with hk
  · apply binomialPMF_eq_zero_of_gt
    have h2 : (n - n / 2 - (r + (n / 4 : ℕ) : ℤ).toNat : ℕ) ≤ n := by omega
    omega
  · rfl

/-- A trace with no `true` bit is the all-zero trace of its own length. -/
lemma trace_eq_allZeroTrace_of_no_true (t : Workspace.Types.Trace.Trace n)
    (h : true ∉ t.bits) :
    t = allZeroTrace n t.bits.length t.length_le := by
  have hbits : t.bits = List.replicate t.bits.length false := by
    apply List.eq_replicate_iff.mpr
    refine ⟨rfl, ?_⟩
    intro x hx
    cases x with
    | false => rfl
    | true => exact absurd hx h
  cases t with
  | mk bits hle =>
    simp only [allZeroTrace]
    simp only at hbits
    exact Workspace.Types.Trace.Trace.mk.injEq .. |>.mpr hbits

variable {Se : Workspace.Types.ProbVec.ProbVec n} {δ : Workspace.Types.DelProb.DelProb}

/-- On the good event, the partial mass on all-zero traces equals the good
lengths mass at the corresponding lengths (per-summand collapse). -/
lemma goodMass_allZero (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zM zP : ℕ) (hzM : zM ≤ n) (hzP : zP ≤ n) :
    goodMass (δ := δ) cfd m (allZeroTrace n zM hzM) (allZeroTrace n zP hzP)
      = goodLenMass (δ := δ) cfd m zM zP := by
  unfold goodMass goodLenMass
  apply tsum_congr; intro b
  apply tsum_congr; intro r
  by_cases hbad : badPred n b r
  · simp only [hbad, not_true, if_false]
  · simp only [hbad, not_false_iff, if_true]
    -- good event: rewrite prefixWeight / suffixWeight via TraceFromZeroIsLengthBinomial
    obtain ⟨hlo, hhi⟩ := not_bad_inrange_intdiv hbad
    have hpref0 := not_bad_prefix_false hbad
    have hsuff0 := not_bad_suffix_false hbad
    obtain ⟨pa, _pb, sc, _sd⟩ := TraceFromZeroIsLengthBinomial δ r b hlo hhi
    have hp : prefixWeight n b δ r (allZeroTrace n zM hzM)
        = prefixLengthWeight n δ r zM := pa hpref0 zM hzM
    have hs : suffixWeight n b δ r (allZeroTrace n zP hzP)
        = suffixLengthWeight n δ r zP := sc hsuff0 zP hzP
    rw [hp, hs]

/-- `goodLenMass` vanishes when the first length exceeds `n`. -/
lemma goodLenMass_eq_zero_of_gt_left (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zM zP : ℕ) (h : n < zM) :
    goodLenMass (δ := δ) cfd m zM zP = 0 := by
  unfold goodLenMass
  rw [ENNReal.tsum_eq_zero]; intro b
  rw [ENNReal.tsum_eq_zero]; intro r
  rw [prefixLengthWeight_eq_zero_of_gt δ r zM h]
  split_ifs <;> ring

/-- `goodLenMass` vanishes when the second length exceeds `n`. -/
lemma goodLenMass_eq_zero_of_gt_right (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zM zP : ℕ) (h : n < zP) :
    goodLenMass (δ := δ) cfd m zM zP = 0 := by
  unfold goodLenMass
  rw [ENNReal.tsum_eq_zero]; intro b
  rw [ENNReal.tsum_eq_zero]; intro r
  rw [suffixLengthWeight_eq_zero_of_gt δ r zP h]
  split_ifs <;> ring

/-- On the good event, the partial mass vanishes on any trace pair where one
trace contains a `true` bit. -/
lemma goodMass_eq_zero_of_true (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (t₁ t₂ : Workspace.Types.Trace.Trace n)
    (h : true ∈ t₁.bits ∨ true ∈ t₂.bits) :
    goodMass (δ := δ) cfd m t₁ t₂ = 0 := by
  unfold goodMass
  rw [ENNReal.tsum_eq_zero]; intro b
  rw [ENNReal.tsum_eq_zero]; intro r
  by_cases hbad : badPred n b r
  · simp only [hbad, not_true, if_false]
  · simp only [hbad, not_false_iff, if_true]
    obtain ⟨hlo, hhi⟩ := not_bad_inrange_intdiv hbad
    have hpref0 := not_bad_prefix_false hbad
    have hsuff0 := not_bad_suffix_false hbad
    obtain ⟨_pa, pb, _sc, sd⟩ := TraceFromZeroIsLengthBinomial δ r b hlo hhi
    rcases h with h1 | h2
    · have : prefixWeight n b δ r t₁ = 0 := pb hpref0 t₁ h1
      rw [this]; ring
    · have : suffixWeight n b δ r t₂ = 0 := sd hsuff0 t₂ h2
      rw [this]; ring

/-- **Step 1 (good-part pushforward).** -/
lemma good_pushforward {So : Workspace.Types.ProbVec.ProbVec n}
    (cfdE : CoinFlipDist n Se) (cfdO : CoinFlipDist n So) :
    (∑' p : (BinVec (n / 2) × Workspace.Types.Trace.Trace n × Workspace.Types.Trace.Trace n),
        |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
          - (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal|)
      = ∑' c : (BinVec (n / 2) × ℕ × ℕ),
          |(goodLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
            - (goodLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal| := by
  set f : (BinVec (n / 2) × Workspace.Types.Trace.Trace n × Workspace.Types.Trace.Trace n) → ℝ :=
    fun p => |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
              - (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal| with hf
  set g : (BinVec (n / 2) × ℕ × ℕ) → ℝ :=
    fun c => |(goodLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
              - (goodLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal| with hg
  have hlen : ∀ c : (BinVec (n / 2) × ℕ × ℕ), g c ≠ 0 → c.2.1 ≤ n ∧ c.2.2 ≤ n := by
    intro c hc
    obtain ⟨m, zM, zP⟩ := c
    refine ⟨?_, ?_⟩
    · by_contra hgt
      push_neg at hgt
      apply hc
      simp only [hg, goodLenMass_eq_zero_of_gt_left cfdE m zM zP hgt,
        goodLenMass_eq_zero_of_gt_left cfdO m zM zP hgt, ENNReal.toReal_zero,
        sub_zero, abs_zero]
    · by_contra hgt
      push_neg at hgt
      apply hc
      simp only [hg, goodLenMass_eq_zero_of_gt_right cfdE m zM zP hgt,
        goodLenMass_eq_zero_of_gt_right cfdO m zM zP hgt, ENNReal.toReal_zero,
        sub_zero, abs_zero]
  set i : ↑(Function.support g) →
      (BinVec (n / 2) × Workspace.Types.Trace.Trace n × Workspace.Types.Trace.Trace n) :=
    fun x => (x.1.1,
      allZeroTrace n x.1.2.1 (hlen x.1 x.2).1,
      allZeroTrace n x.1.2.2 (hlen x.1 x.2).2) with hi
  apply tsum_eq_tsum_of_ne_zero_bij i
  · rintro ⟨⟨m₁, zM₁, zP₁⟩, hx⟩ ⟨⟨m₂, zM₂, zP₂⟩, hy⟩ hij
    simp only [hi, Prod.mk.injEq] at hij
    obtain ⟨hm, ht1, ht2⟩ := hij
    have e1 : zM₁ = zM₂ := by
      have := congrArg (fun (t : Workspace.Types.Trace.Trace n) => t.bits.length) ht1
      simpa [allZeroTrace_length] using this
    have e2 : zP₁ = zP₂ := by
      have := congrArg (fun (t : Workspace.Types.Trace.Trace n) => t.bits.length) ht2
      simpa [allZeroTrace_length] using this
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    exact ⟨hm, e1, e2⟩
  · intro p hp
    obtain ⟨m, t₁, t₂⟩ := p
    have hnotrue : true ∉ t₁.bits ∧ true ∉ t₂.bits := by
      by_contra hcon
      apply hp
      rw [not_and_or] at hcon
      push_neg at hcon
      have : true ∈ t₁.bits ∨ true ∈ t₂.bits := by tauto
      simp only [hf, goodMass_eq_zero_of_true cfdE m t₁ t₂ this,
        goodMass_eq_zero_of_true cfdO m t₁ t₂ this, ENNReal.toReal_zero,
        sub_zero, abs_zero]
    obtain ⟨h1, h2⟩ := hnotrue
    refine ⟨⟨(m, t₁.bits.length, t₂.bits.length), ?_⟩, ?_⟩
    · show g (m, t₁.bits.length, t₂.bits.length) ≠ 0
      simp only [hg]
      have ht1 : t₁ = allZeroTrace n t₁.bits.length t₁.length_le :=
        trace_eq_allZeroTrace_of_no_true t₁ h1
      have ht2 : t₂ = allZeroTrace n t₂.bits.length t₂.length_le :=
        trace_eq_allZeroTrace_of_no_true t₂ h2
      rw [← goodMass_allZero cfdE m t₁.bits.length t₂.bits.length t₁.length_le t₂.length_le,
        ← goodMass_allZero cfdO m t₁.bits.length t₂.bits.length t₁.length_le t₂.length_le,
        ← ht1, ← ht2]
      simpa [hf] using hp
    · simp only [hi]
      have ht1 : t₁ = allZeroTrace n t₁.bits.length t₁.length_le :=
        trace_eq_allZeroTrace_of_no_true t₁ h1
      have ht2 : t₂ = allZeroTrace n t₂.bits.length t₂.length_le :=
        trace_eq_allZeroTrace_of_no_true t₂ h2
      conv_rhs => rw [ht1, ht2]
  · rintro ⟨⟨m, zM, zP⟩, hx⟩
    simp only [hi, hf, hg]
    rw [goodMass_allZero cfdE m zM zP (hlen _ hx).1 (hlen _ hx).2,
      goodMass_allZero cfdO m zM zP (hlen _ hx).1 (hlen _ hx).2]

end TVPartialGoodCollapse
