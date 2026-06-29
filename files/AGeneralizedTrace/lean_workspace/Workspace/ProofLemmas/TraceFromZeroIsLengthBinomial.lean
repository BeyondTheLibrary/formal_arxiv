import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.DeletionLengthMarginal

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.DeletionChannel

open scoped Classical

/-- Helper: For "good" b (zero on prefix range) and prefix mask μ, restrict b μ is all false. -/
private lemma restrict_good_prefix_eq_replicate {n : ℕ} (b : BinVec n) (r : ℤ)
    (hb : ∀ i : Fin n, (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r → b.bit i = false)
    (μ : Fin n → Bool) (hμ : isPrefixMask n r μ) :
    restrict b μ = List.replicate (restrict b μ).length false := by
  -- Show every element of restrict b μ is false
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro x hx
  unfold restrict at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨i, _hi_mem, hi⟩ := hx
  by_cases hμi : μ i
  · simp [hμi] at hi
    -- hi : b.bit i = x
    -- isPrefixMask: μ i = false when i.val ≥ n/4 + r. Since μ i = true, i.val < n/4 + r
    have : ¬ ((i : ℤ) ≥ ((n / 4 : ℕ) : ℤ) + r) := by
      intro hge
      have := hμ i hge
      rw [this] at hμi
      exact Bool.false_ne_true hμi
    have hlt : (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r := by linarith [not_le.mp this]
    have := hb i hlt
    rw [this] at hi
    exact hi.symm
  · simp [hμi] at hi

/-- Helper: For "good" b on suffix range (zero on suffix) and suffix mask μ, restrict b μ is all false. -/
private lemma restrict_good_suffix_eq_replicate {n : ℕ} (b : BinVec n) (r : ℤ)
    (hb : ∀ i : Fin n, ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (i.val : ℤ) → b.bit i = false)
    (μ : Fin n → Bool) (hμ : isSuffixMask n r μ) :
    restrict b μ = List.replicate (restrict b μ).length false := by
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro x hx
  unfold restrict at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨i, _hi_mem, hi⟩ := hx
  by_cases hμi : μ i
  · simp [hμi] at hi
    have : ¬ ((i : ℤ) < ((n / 4 + n / 2 : ℕ) : ℤ) + r) := by
      intro hlt
      have := hμ i hlt
      rw [this] at hμi
      exact Bool.false_ne_true hμi
    have hge : ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (i.val : ℤ) := by
      push_cast
      push_cast at this
      linarith
    have := hb i hge
    rw [this] at hi
    exact hi.symm
  · simp [hμi] at hi

theorem TraceFromZeroIsLengthBinomial :
    ∀ {n : ℕ} (δ : Workspace.Types.DelProb.DelProb) (r : ℤ)
      (b : Workspace.Types.BinVec.BinVec n),
      0 ≤ r + (n / 4 : ℤ) → r + (n / 4 : ℤ) ≤ (n / 2 : ℤ) →
      -- Prefix part (a): length-binomial collapse on the all-zero trace.
      ((∀ i : Fin n, (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r →
            b.bit i = false) →
        ∀ z : ℕ, ∀ (hz : z ≤ n),
          Workspace.Types.PartialDeletionProcess.prefixWeight n b δ r
              ⟨List.replicate z false,
                by rw [List.length_replicate]; exact hz⟩
            = Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r z) ∧
      -- Prefix part (b): vanishing on any non-all-zero trace.
      ((∀ i : Fin n, (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r →
            b.bit i = false) →
        ∀ (t : Workspace.Types.Trace.Trace n), (true ∈ t.bits) →
          Workspace.Types.PartialDeletionProcess.prefixWeight n b δ r t = 0) ∧
      -- Suffix part (c): symmetric length-binomial collapse.
      ((∀ i : Fin n, ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (i.val : ℤ) →
            b.bit i = false) →
        ∀ z : ℕ, ∀ (hz : z ≤ n),
          Workspace.Types.PartialDeletionProcess.suffixWeight n b δ r
              ⟨List.replicate z false,
                by rw [List.length_replicate]; exact hz⟩
            = Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r z) ∧
      -- Suffix part (d): vanishing on any non-all-zero trace.
      ((∀ i : Fin n, ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (i.val : ℤ) →
            b.bit i = false) →
        ∀ (t : Workspace.Types.Trace.Trace n), (true ∈ t.bits) →
          Workspace.Types.PartialDeletionProcess.suffixWeight n b δ r t = 0) := by
  intro n δ r b h_lo h_hi
  -- Helper: rewrite the int-cast hypotheses
  have h_lo' : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := by exact_mod_cast h_lo
  have h_hi' : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by exact_mod_cast h_hi
  -- Prefix part (b): vanishing on non-all-zero traces.
  have prefix_b : (∀ i : Fin n, (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r →
            b.bit i = false) →
        ∀ (t : Workspace.Types.Trace.Trace n), (true ∈ t.bits) →
          prefixWeight n b δ r t = 0 := by
    intro hb t hT
    unfold prefixWeight
    apply Finset.sum_eq_zero
    intro μ _
    -- show the indicator is 0
    by_cases hP : isPrefixMask n r μ ∧ restrict b μ = t.bits
    · -- Then restrict b μ = t.bits, but restrict b μ is all-false, so t.bits has no true.
      exfalso
      have hrep := restrict_good_prefix_eq_replicate b r hb μ hP.1
      rw [hP.2] at hrep
      -- t.bits = List.replicate ... false
      rw [hrep] at hT
      have heq : true = false := List.eq_of_mem_replicate hT
      exact Bool.noConfusion heq
    · simp [hP]
  -- Suffix part (d): vanishing on non-all-zero traces.
  have suffix_d : (∀ i : Fin n, ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (i.val : ℤ) →
            b.bit i = false) →
        ∀ (t : Workspace.Types.Trace.Trace n), (true ∈ t.bits) →
          suffixWeight n b δ r t = 0 := by
    intro hb t hT
    unfold suffixWeight
    apply Finset.sum_eq_zero
    intro μ _
    by_cases hP : isSuffixMask n r μ ∧ restrict b μ = t.bits
    · exfalso
      have hrep := restrict_good_suffix_eq_replicate b r hb μ hP.1
      rw [hP.2] at hrep
      rw [hrep] at hT
      have heq : true = false := List.eq_of_mem_replicate hT
      exact Bool.noConfusion heq
    · simp [hP]
  -- Prefix part (a): collapse on all-zero trace.
  have prefix_a : (∀ i : Fin n, (i.val : ℤ) < ((n / 4 : ℕ) : ℤ) + r →
            b.bit i = false) →
        ∀ z : ℕ, ∀ (hz : z ≤ n),
          prefixWeight n b δ r
              ⟨List.replicate z false,
                by rw [List.length_replicate]; exact hz⟩
            = prefixLengthWeight n δ r z := by
    intro hb z hz
    -- Get the marginal identity
    have hmarg := (DeletionLengthMarginal b δ r h_lo' h_hi' z).1
    -- The all-zero trace
    let t0 : Trace n := ⟨List.replicate z false, by rw [List.length_replicate]; exact hz⟩
    have ht0_len : t0.bits.length = z := by simp [t0]
    -- Show the tsum reduces to a single term: t = t0.
    have key : (∑' t : Trace n,
        (if t.bits.length = z then prefixWeight n b δ r t else 0))
        = (if t0.bits.length = z then prefixWeight n b δ r t0 else 0) := by
      apply tsum_eq_single (f := fun t => if t.bits.length = z then prefixWeight n b δ r t else 0) t0
      intro t ht_ne
      by_cases hlen : t.bits.length = z
      · simp only [hlen, if_true]
        by_cases hT : true ∈ t.bits
        · exact prefix_b hb t hT
        · exfalso
          apply ht_ne
          have h_all_false : t.bits = List.replicate z false := by
            apply List.eq_replicate_iff.mpr
            refine ⟨hlen, ?_⟩
            intro x hx
            rcases x with _ | _
            · rfl
            · exact absurd hx hT
          cases t with
          | mk bits hbits =>
            simp only at h_all_false
            subst h_all_false
            rfl
      · simp [hlen]
    rw [ht0_len] at key
    simp only [if_true] at key
    rw [key] at hmarg
    exact hmarg
  -- Suffix part (c): symmetric.
  have suffix_c : (∀ i : Fin n, ((n / 4 + n / 2 : ℕ) : ℤ) + r ≤ (i.val : ℤ) →
            b.bit i = false) →
        ∀ z : ℕ, ∀ (hz : z ≤ n),
          suffixWeight n b δ r
              ⟨List.replicate z false,
                by rw [List.length_replicate]; exact hz⟩
            = suffixLengthWeight n δ r z := by
    intro hb z hz
    have hmarg := (DeletionLengthMarginal b δ r h_lo' h_hi' z).2
    let t0 : Trace n := ⟨List.replicate z false, by rw [List.length_replicate]; exact hz⟩
    have ht0_len : t0.bits.length = z := by simp [t0]
    have key : (∑' t : Trace n,
        (if t.bits.length = z then suffixWeight n b δ r t else 0))
        = (if t0.bits.length = z then suffixWeight n b δ r t0 else 0) := by
      apply tsum_eq_single (f := fun t => if t.bits.length = z then suffixWeight n b δ r t else 0) t0
      intro t ht_ne
      by_cases hlen : t.bits.length = z
      · simp only [hlen, if_true]
        by_cases hT : true ∈ t.bits
        · exact suffix_d hb t hT
        · exfalso
          apply ht_ne
          have h_all_false : t.bits = List.replicate z false := by
            apply List.eq_replicate_iff.mpr
            refine ⟨hlen, ?_⟩
            intro x hx
            rcases x with _ | _
            · rfl
            · exact absurd hx hT
          cases t with
          | mk bits hbits =>
            simp only at h_all_false
            subst h_all_false
            rfl
      · simp [hlen]
    rw [ht0_len] at key
    simp only [if_true] at key
    rw [key] at hmarg
    exact hmarg
  exact ⟨prefix_a, prefix_b, suffix_c, suffix_d⟩
