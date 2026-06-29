import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.DeletionChannel
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

open scoped Classical
open BigOperators

namespace DeletionLengthMarginalProof

/-- Decidable equality for `Trace n`. -/
instance instDecEqTrace (n : ℕ) : DecidableEq (Workspace.Types.Trace.Trace n) := by
  intro t₁ t₂
  cases t₁ with | mk b₁ h₁ =>
  cases t₂ with | mk b₂ h₂ =>
  exact decidable_of_iff (b₁ = b₂) (by
    constructor
    · intro h; subst h; rfl
    · intro h; injection h)

/-- Two traces with the same bits are equal. -/
lemma trace_ext {n : ℕ} {t₁ t₂ : Workspace.Types.Trace.Trace n}
    (h : t₁.bits = t₂.bits) : t₁ = t₂ := by
  cases t₁; cases t₂; simp_all

/-- The list `restrict b m` has length at most `n`. -/
lemma length_restrict_le {n : ℕ} (b : BinVec n) (m : Fin n → Bool) :
    (restrict b m).length ≤ n := by
  unfold restrict
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- Build a `Trace n` from a `BinVec n` and a mask. -/
noncomputable def traceOfMask {n : ℕ} (b : BinVec n) (m : Fin n → Bool) :
    Workspace.Types.Trace.Trace n :=
  ⟨restrict b m, length_restrict_le b m⟩

@[simp] lemma traceOfMask_bits {n : ℕ} (b : BinVec n) (m : Fin n → Bool) :
    (traceOfMask b m).bits = restrict b m := rfl

/-- The length of `restrict b μ` equals the number of `i : Fin n` with `μ i = true`. -/
lemma length_restrict_eq_card {n : ℕ} (b : BinVec n) (μ : Fin n → Bool) :
    (restrict b μ).length = (Finset.univ.filter (fun i : Fin n => μ i = true)).card := by
  unfold restrict
  rw [List.length_filterMap_eq_countP]
  have hcountP :
      (List.finRange n).countP
          (fun i => (if μ i = true then some (b.bit i) else none).isSome)
        = (List.finRange n).countP (fun i => μ i) := by
    apply List.countP_congr
    intro i _
    by_cases hμ : μ i = true
    · simp [hμ]
    · simp [hμ]
  rw [hcountP]
  rw [List.countP_eq_length_filter]
  have hu : (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => μ i = true) =
      ((List.finRange n).filter (fun i : Fin n => μ i)).toFinset := by
    ext i
    simp [List.mem_finRange]
  rw [hu]
  rw [List.toFinset_card_of_nodup]
  exact (List.nodup_finRange n).filter _

/-- The set of traces produced as `traceOfMask b μ`. -/
noncomputable def traceImageSet {n : ℕ} (b : BinVec n) :
    Finset (Workspace.Types.Trace.Trace n) :=
  (Finset.univ : Finset (Fin n → Bool)).image (traceOfMask b)

lemma mem_traceImageSet {n : ℕ} (b : BinVec n) (t : Workspace.Types.Trace.Trace n) :
    t ∈ traceImageSet b ↔ ∃ μ : Fin n → Bool, traceOfMask b μ = t := by
  simp [traceImageSet]

/-- Key support lemma: prefixWeight is zero outside the trace image set. -/
lemma prefixWeight_zero_of_not_mem {n : ℕ} (b : BinVec n) (δ : DelProb) (r : ℤ)
    (t : Workspace.Types.Trace.Trace n) (ht : t ∉ traceImageSet b) :
    prefixWeight n b δ r t = 0 := by
  unfold prefixWeight
  apply Finset.sum_eq_zero
  intro μ _
  simp only [mem_traceImageSet] at ht
  push_neg at ht
  have hne : restrict b μ ≠ t.bits := by
    intro hr
    apply ht μ
    apply trace_ext
    rw [traceOfMask_bits, hr]
  rw [if_neg]
  · ring
  · intro ⟨_, h2⟩
    exact hne h2

lemma suffixWeight_zero_of_not_mem {n : ℕ} (b : BinVec n) (δ : DelProb) (r : ℤ)
    (t : Workspace.Types.Trace.Trace n) (ht : t ∉ traceImageSet b) :
    suffixWeight n b δ r t = 0 := by
  unfold suffixWeight
  apply Finset.sum_eq_zero
  intro μ _
  simp only [mem_traceImageSet] at ht
  push_neg at ht
  have hne : restrict b μ ≠ t.bits := by
    intro hr
    apply ht μ
    apply trace_ext
    rw [traceOfMask_bits, hr]
  rw [if_neg]
  · ring
  · intro ⟨_, h2⟩
    exact hne h2

/-- The keep-weight product factor for the prefix range. -/
noncomputable def prefixKeepWeight (n : ℕ) (δ : DelProb) (r : ℤ) (μ : Fin n → Bool) : ENNReal :=
  ∏ i : Fin n,
    (if ((i : ℤ) < ((n / 4 : ℕ) : ℤ) + r) then
        (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val)
      else 1)

/-- The keep-weight product factor for the suffix range. -/
noncomputable def suffixKeepWeight (n : ℕ) (δ : DelProb) (r : ℤ) (μ : Fin n → Bool) : ENNReal :=
  ∏ i : Fin n,
    (if ((i : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r) then
        (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val)
      else 1)

/-- prefixWeight rewritten using prefixKeepWeight. -/
lemma prefixWeight_eq_sum (n : ℕ) (b : BinVec n) (δ : DelProb) (r : ℤ) (t : Workspace.Types.Trace.Trace n) :
    prefixWeight n b δ r t =
      ∑ μ : Fin n → Bool,
        (if isPrefixMask n r μ ∧ restrict b μ = t.bits then (1 : ENNReal) else 0) *
          prefixKeepWeight n δ r μ := by
  rfl

lemma suffixWeight_eq_sum (n : ℕ) (b : BinVec n) (δ : DelProb) (r : ℤ) (t : Workspace.Types.Trace.Trace n) :
    suffixWeight n b δ r t =
      ∑ μ : Fin n → Bool,
        (if isSuffixMask n r μ ∧ restrict b μ = t.bits then (1 : ENNReal) else 0) *
          suffixKeepWeight n δ r μ := by
  rfl

/-- The set of `i : Fin n` whose integer index is less than `(n/4 : ℕ) + r`. -/
noncomputable def prefixIdxs (n : ℕ) (r : ℤ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℤ) < ((n / 4 : ℕ) : ℤ) + r)

/-- The set of `i : Fin n` whose integer index is at least `(3*(n/4) : ℕ) + r`. -/
noncomputable def suffixIdxs (n : ℕ) (r : ℤ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r)

/-- Cardinality of the prefix index set, given the range condition. -/
lemma prefixIdxs_card {n : ℕ} (r : ℤ) (h_lo : 0 ≤ r + ((n / 4 : ℕ) : ℤ))
    (h_hi : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) :
    (prefixIdxs n r).card = (r + ((n / 4 : ℕ) : ℤ)).toNat := by
  unfold prefixIdxs
  set k : ℕ := (r + ((n / 4 : ℕ) : ℤ)).toNat with hk_def
  have hk_eq : (k : ℤ) = r + ((n / 4 : ℕ) : ℤ) := Int.toNat_of_nonneg h_lo
  have hk_le_n : k ≤ n := by
    have hn2 : (n / 2 : ℕ) ≤ n := Nat.div_le_self n 2
    have hkn2 : (k : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by rw [hk_eq]; exact h_hi
    have : k ≤ n / 2 := by exact_mod_cast hkn2
    omega
  have hfilter_eq : ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℤ) < ((n / 4 : ℕ) : ℤ) + r))
      = ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℕ) < k)) := by
    apply Finset.filter_congr
    intro i _
    rw [show ((n / 4 : ℕ) : ℤ) + r = r + ((n / 4 : ℕ) : ℤ) from by ring, ← hk_eq]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h
  rw [hfilter_eq]
  have hcard : ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => (i : ℕ) < k))
      = (Finset.range k).attachFin (fun x hx => lt_of_lt_of_le (Finset.mem_range.mp hx) hk_le_n) := by
    ext ⟨i, hi⟩
    simp [Finset.attachFin]
  rw [hcard, Finset.card_attachFin, Finset.card_range]

lemma prefixIdxs_le_n {n : ℕ} (r : ℤ) (h_lo : 0 ≤ r + ((n / 4 : ℕ) : ℤ))
    (h_hi : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) :
    (r + ((n / 4 : ℕ) : ℤ)).toNat ≤ n := by
  set k : ℕ := (r + ((n / 4 : ℕ) : ℤ)).toNat
  have hk_eq : (k : ℤ) = r + ((n / 4 : ℕ) : ℤ) := Int.toNat_of_nonneg h_lo
  have hn2 : (n / 2 : ℕ) ≤ n := Nat.div_le_self n 2
  have hkn2 : (k : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by rw [hk_eq]; exact h_hi
  have : k ≤ n / 2 := by exact_mod_cast hkn2
  omega

lemma mem_prefixIdxs {n : ℕ} (r : ℤ) (i : Fin n) :
    i ∈ prefixIdxs n r ↔ (i : ℤ) < ((n / 4 : ℕ) : ℤ) + r := by
  unfold prefixIdxs
  simp

lemma mem_suffixIdxs {n : ℕ} (r : ℤ) (i : Fin n) :
    i ∈ suffixIdxs n r ↔ (i : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r := by
  unfold suffixIdxs
  simp

/-- prefixKeepWeight expressed as a product over prefixIdxs. -/
lemma prefixKeepWeight_eq_prod_prefixIdxs (n : ℕ) (δ : DelProb) (r : ℤ) (μ : Fin n → Bool) :
    prefixKeepWeight n δ r μ =
      ∏ i ∈ prefixIdxs n r,
        (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) := by
  unfold prefixKeepWeight prefixIdxs
  rw [Finset.prod_ite]
  simp

lemma suffixKeepWeight_eq_prod_suffixIdxs (n : ℕ) (δ : DelProb) (r : ℤ) (μ : Fin n → Bool) :
    suffixKeepWeight n δ r μ =
      ∏ i ∈ suffixIdxs n r,
        (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val) := by
  unfold suffixKeepWeight suffixIdxs
  rw [Finset.prod_ite]
  simp

lemma isPrefixMask_iff {n : ℕ} (r : ℤ) (μ : Fin n → Bool) :
    isPrefixMask n r μ ↔ ∀ i : Fin n, i ∉ prefixIdxs n r → μ i = false := by
  unfold isPrefixMask
  constructor
  · intro h i hi
    rw [mem_prefixIdxs] at hi
    push_neg at hi
    exact h i hi
  · intro h i hi
    apply h i
    rw [mem_prefixIdxs]
    push_neg
    exact hi

lemma isSuffixMask_iff {n : ℕ} (r : ℤ) (μ : Fin n → Bool) :
    isSuffixMask n r μ ↔ ∀ i : Fin n, i ∉ suffixIdxs n r → μ i = false := by
  unfold isSuffixMask
  constructor
  · intro h i hi
    rw [mem_suffixIdxs] at hi
    push_neg at hi
    exact h i hi
  · intro h i hi
    apply h i
    rw [mem_suffixIdxs]
    push_neg
    exact hi

lemma popcount_eq_popcount_prefix {n : ℕ} (r : ℤ) (μ : Fin n → Bool)
    (hμ : isPrefixMask n r μ) :
    (Finset.univ.filter (fun i : Fin n => μ i = true)).card =
      ((prefixIdxs n r).filter (fun i : Fin n => μ i = true)).card := by
  rw [isPrefixMask_iff] at hμ
  apply Finset.card_bij (fun i _ => i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter]
    refine ⟨?_, hi⟩
    by_contra h_not_in
    have := hμ i h_not_in
    rw [this] at hi
    exact Bool.false_ne_true hi
  · intros; simp_all
  · intro i hi
    simp only [Finset.mem_filter] at hi
    refine ⟨i, ?_, rfl⟩
    simp [hi.2]

lemma popcount_eq_popcount_suffix {n : ℕ} (r : ℤ) (μ : Fin n → Bool)
    (hμ : isSuffixMask n r μ) :
    (Finset.univ.filter (fun i : Fin n => μ i = true)).card =
      ((suffixIdxs n r).filter (fun i : Fin n => μ i = true)).card := by
  rw [isSuffixMask_iff] at hμ
  apply Finset.card_bij (fun i _ => i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter]
    refine ⟨?_, hi⟩
    by_contra h_not_in
    have := hμ i h_not_in
    rw [this] at hi
    exact Bool.false_ne_true hi
  · intros; simp_all
  · intro i hi
    simp only [Finset.mem_filter] at hi
    refine ⟨i, ?_, rfl⟩
    simp [hi.2]

lemma prefixKeepWeight_value {n : ℕ} (δ : DelProb) (r : ℤ) (μ : Fin n → Bool) :
    prefixKeepWeight n δ r μ =
      ENNReal.ofReal (1 - δ.val) ^ ((prefixIdxs n r).filter (fun i : Fin n => μ i = true)).card *
      ENNReal.ofReal δ.val ^ ((prefixIdxs n r).card - ((prefixIdxs n r).filter (fun i : Fin n => μ i = true)).card) := by
  rw [prefixKeepWeight_eq_prod_prefixIdxs]
  rw [show (∏ i ∈ prefixIdxs n r,
        (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val))
        = (∏ i ∈ (prefixIdxs n r).filter (fun i => μ i = true), ENNReal.ofReal (1 - δ.val)) *
          (∏ i ∈ (prefixIdxs n r).filter (fun i => ¬(μ i = true)), ENNReal.ofReal δ.val) from by
    rw [← Finset.prod_filter_mul_prod_filter_not (prefixIdxs n r) (fun i => μ i = true)
        (fun i => if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val)]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      have : μ i = false := by
        cases h : μ i
        · rfl
        · exfalso; exact hi.2 h
      simp [this]]
  rw [Finset.prod_const, Finset.prod_const]
  congr 2
  have hsub : (prefixIdxs n r).filter (fun i => ¬(μ i = true))
      = (prefixIdxs n r) \ ((prefixIdxs n r).filter (fun i => μ i = true)) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hsub]
  exact Finset.card_sdiff_of_subset (Finset.filter_subset (fun i : Fin n => μ i = true) (prefixIdxs n r))

lemma suffixKeepWeight_value {n : ℕ} (δ : DelProb) (r : ℤ) (μ : Fin n → Bool) :
    suffixKeepWeight n δ r μ =
      ENNReal.ofReal (1 - δ.val) ^ ((suffixIdxs n r).filter (fun i : Fin n => μ i = true)).card *
      ENNReal.ofReal δ.val ^ ((suffixIdxs n r).card - ((suffixIdxs n r).filter (fun i : Fin n => μ i = true)).card) := by
  rw [suffixKeepWeight_eq_prod_suffixIdxs]
  rw [show (∏ i ∈ suffixIdxs n r,
        (if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val))
        = (∏ i ∈ (suffixIdxs n r).filter (fun i => μ i = true), ENNReal.ofReal (1 - δ.val)) *
          (∏ i ∈ (suffixIdxs n r).filter (fun i => ¬(μ i = true)), ENNReal.ofReal δ.val) from by
    rw [← Finset.prod_filter_mul_prod_filter_not (suffixIdxs n r) (fun i => μ i = true)
        (fun i => if μ i then ENNReal.ofReal (1 - δ.val) else ENNReal.ofReal δ.val)]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      simp [hi.2]
    · apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_filter] at hi
      have : μ i = false := by
        cases h : μ i
        · rfl
        · exfalso; exact hi.2 h
      simp [this]]
  rw [Finset.prod_const, Finset.prod_const]
  congr 2
  have hsub : (suffixIdxs n r).filter (fun i => ¬(μ i = true))
      = (suffixIdxs n r) \ ((suffixIdxs n r).filter (fun i => μ i = true)) := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hsub]
  exact Finset.card_sdiff_of_subset (Finset.filter_subset (fun i : Fin n => μ i = true) (suffixIdxs n r))

/-- The total prefixWeight summed over all traces (no length filter). -/
lemma sum_prefixWeight_swap (n : ℕ) (b : BinVec n) (δ : DelProb) (r : ℤ) (z : ℕ) :
    (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then prefixWeight n b δ r t else 0))
      = ∑ μ : Fin n → Bool,
          (if isPrefixMask n r μ ∧ (restrict b μ).length = z then prefixKeepWeight n δ r μ else 0) := by
  -- Step 1: Reduce tsum to Finset sum over traceImageSet b
  have h_supp : ∀ t ∉ traceImageSet b, (if t.bits.length = z then prefixWeight n b δ r t else 0) = 0 := by
    intro t ht
    have := prefixWeight_zero_of_not_mem b δ r t ht
    by_cases hl : t.bits.length = z <;> simp [hl, this]
  rw [tsum_eq_sum h_supp]
  -- Step 2: For each t, expand the if-then-else and prefixWeight as a sum over μ.
  have hexpand : ∀ t : Workspace.Types.Trace.Trace n,
      (if t.bits.length = z then prefixWeight n b δ r t else 0)
        = ∑ μ : Fin n → Bool,
            (if t.bits.length = z ∧ isPrefixMask n r μ ∧ restrict b μ = t.bits then
              prefixKeepWeight n δ r μ else 0) := by
    intro t
    by_cases hl : t.bits.length = z
    · rw [if_pos hl, prefixWeight_eq_sum]
      apply Finset.sum_congr rfl
      intro μ _
      by_cases hp : isPrefixMask n r μ ∧ restrict b μ = t.bits
      · rw [if_pos hp, one_mul, if_pos ⟨hl, hp.1, hp.2⟩]
      · rw [if_neg hp, zero_mul, if_neg]
        intro ⟨_, h1, h2⟩
        exact hp ⟨h1, h2⟩
    · rw [if_neg hl]
      symm
      apply Finset.sum_eq_zero
      intro μ _
      rw [if_neg]
      intro ⟨h1, _⟩
      exact hl h1
  rw [Finset.sum_congr rfl (fun t _ => hexpand t)]
  -- Swap sums
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hpre : isPrefixMask n r μ
  · by_cases hlen : (restrict b μ).length = z
    · rw [if_pos ⟨hpre, hlen⟩]
      have ht_mem : traceOfMask b μ ∈ traceImageSet b := by
        rw [mem_traceImageSet]; exact ⟨μ, rfl⟩
      rw [Finset.sum_eq_single (traceOfMask b μ)]
      · -- At t = traceOfMask b μ:
        have ht_bits : (traceOfMask b μ).bits = restrict b μ := rfl
        rw [if_pos]
        constructor
        · rw [ht_bits]; exact hlen
        · exact ⟨hpre, rfl⟩
      · intro t ht hne
        rw [if_neg]
        intro ⟨_, _, h2⟩
        apply hne
        apply trace_ext
        exact h2.symm
      · intro h_notmem
        exact absurd ht_mem h_notmem
    · rw [if_neg (fun h => hlen h.2)]
      apply Finset.sum_eq_zero
      intro t ht
      rw [if_neg]
      intro ⟨h1, _, h2⟩
      rw [h2] at hlen
      exact hlen h1
  · rw [if_neg (fun h => hpre h.1)]
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    intro ⟨_, h1, _⟩
    exact hpre h1

lemma sum_suffixWeight_swap (n : ℕ) (b : BinVec n) (δ : DelProb) (r : ℤ) (z : ℕ) :
    (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then suffixWeight n b δ r t else 0))
      = ∑ μ : Fin n → Bool,
          (if isSuffixMask n r μ ∧ (restrict b μ).length = z then suffixKeepWeight n δ r μ else 0) := by
  have h_supp : ∀ t ∉ traceImageSet b, (if t.bits.length = z then suffixWeight n b δ r t else 0) = 0 := by
    intro t ht
    have := suffixWeight_zero_of_not_mem b δ r t ht
    by_cases hl : t.bits.length = z <;> simp [hl, this]
  rw [tsum_eq_sum h_supp]
  have hexpand : ∀ t : Workspace.Types.Trace.Trace n,
      (if t.bits.length = z then suffixWeight n b δ r t else 0)
        = ∑ μ : Fin n → Bool,
            (if t.bits.length = z ∧ isSuffixMask n r μ ∧ restrict b μ = t.bits then
              suffixKeepWeight n δ r μ else 0) := by
    intro t
    by_cases hl : t.bits.length = z
    · rw [if_pos hl, suffixWeight_eq_sum]
      apply Finset.sum_congr rfl
      intro μ _
      by_cases hp : isSuffixMask n r μ ∧ restrict b μ = t.bits
      · rw [if_pos hp, one_mul, if_pos ⟨hl, hp.1, hp.2⟩]
      · rw [if_neg hp, zero_mul, if_neg]
        intro ⟨_, h1, h2⟩
        exact hp ⟨h1, h2⟩
    · rw [if_neg hl]
      symm
      apply Finset.sum_eq_zero
      intro μ _
      rw [if_neg]
      intro ⟨h1, _⟩
      exact hl h1
  rw [Finset.sum_congr rfl (fun t _ => hexpand t)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hpre : isSuffixMask n r μ
  · by_cases hlen : (restrict b μ).length = z
    · rw [if_pos ⟨hpre, hlen⟩]
      have ht_mem : traceOfMask b μ ∈ traceImageSet b := by
        rw [mem_traceImageSet]; exact ⟨μ, rfl⟩
      rw [Finset.sum_eq_single (traceOfMask b μ)]
      · have ht_bits : (traceOfMask b μ).bits = restrict b μ := rfl
        rw [if_pos]
        constructor
        · rw [ht_bits]; exact hlen
        · exact ⟨hpre, rfl⟩
      · intro t ht hne
        rw [if_neg]
        intro ⟨_, _, h2⟩
        apply hne
        apply trace_ext
        exact h2.symm
      · intro h_notmem
        exact absurd ht_mem h_notmem
    · rw [if_neg (fun h => hlen h.2)]
      apply Finset.sum_eq_zero
      intro t ht
      rw [if_neg]
      intro ⟨h1, _, h2⟩
      rw [h2] at hlen
      exact hlen h1
  · rw [if_neg (fun h => hpre h.1)]
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    intro ⟨_, h1, _⟩
    exact hpre h1

/-- Count of masks in `Fin n → Bool` with `isPrefixMask n r μ` and popcount = z. -/
lemma mask_count_prefix_popcount (n : ℕ) (r : ℤ) (z : ℕ) :
    (Finset.univ.filter (fun μ : Fin n → Bool =>
      isPrefixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z)).card
      = (prefixIdxs n r).card.choose z := by
  -- Bijection: μ ↔ (prefixIdxs n r).filter (fun i => μ i = true)
  -- Specifically, for an isPrefixMask μ, the support of μ is a subset of prefixIdxs.
  -- A z-element subset T ⊆ prefixIdxs corresponds to μ_T : Fin n → Bool defined by μ_T i = (i ∈ T).
  set S : Finset (Fin n) := prefixIdxs n r
  -- Build the bijection.
  -- Direction 1: μ ↦ (S.filter (μ · = true))
  -- Direction 2: T : powersetCard z S ↦ (fun i => i ∈ T)
  have key : (Finset.univ.filter (fun μ : Fin n → Bool =>
      isPrefixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z)).card
      = (S.powersetCard z).card := by
    apply Finset.card_bij (fun μ _ => S.filter (fun i => μ i = true))
    · intro μ hμ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ
      simp only [Finset.mem_powersetCard]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      rw [← popcount_eq_popcount_prefix r μ hμ.1]
      exact hμ.2
    · intro μ₁ hμ₁ μ₂ hμ₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ₁ hμ₂
      funext i
      by_cases hi : i ∈ S
      · -- i ∈ S, so μ_j i can be true or false. Use heq.
        cases h₁ : μ₁ i
        · cases h₂ : μ₂ i
          · rfl
          · exfalso
            have h_in2 : i ∈ S.filter (fun i => μ₂ i = true) := by simp [hi, h₂]
            rw [← heq] at h_in2
            simp [hi, h₁] at h_in2
        · cases h₂ : μ₂ i
          · exfalso
            have h_in1 : i ∈ S.filter (fun i => μ₁ i = true) := by simp [hi, h₁]
            rw [heq] at h_in1
            simp [hi, h₂] at h_in1
          · rfl
      · -- i ∉ S = prefixIdxs. By isPrefixMask, μ_j i = false.
        rw [isPrefixMask_iff] at hμ₁ hμ₂
        rw [hμ₁.1 i hi, hμ₂.1 i hi]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hT_sub, hT_card⟩ := hT
      -- Use μ_T : Fin n → Bool defined by μ_T i = (i ∈ T)
      refine ⟨fun i => decide (i ∈ T), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · -- isPrefixMask
          rw [isPrefixMask_iff]
          intro i hi
          have : i ∉ T := fun h => hi (hT_sub h)
          simp [this]
        · -- popcount = z
          have heq : (Finset.univ.filter (fun i : Fin n => decide (i ∈ T) = true)) = T := by
            ext i
            simp
          rw [heq]
          exact hT_card
      · -- The image under the function is T
        ext i
        simp only [Finset.mem_filter, decide_eq_true_eq]
        constructor
        · intro ⟨_, h⟩; exact h
        · intro h
          exact ⟨hT_sub h, h⟩
  rw [key, Finset.card_powersetCard]

lemma mask_count_suffix_popcount (n : ℕ) (r : ℤ) (z : ℕ) :
    (Finset.univ.filter (fun μ : Fin n → Bool =>
      isSuffixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z)).card
      = (suffixIdxs n r).card.choose z := by
  set S : Finset (Fin n) := suffixIdxs n r
  have key : (Finset.univ.filter (fun μ : Fin n → Bool =>
      isSuffixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z)).card
      = (S.powersetCard z).card := by
    apply Finset.card_bij (fun μ _ => S.filter (fun i => μ i = true))
    · intro μ hμ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ
      simp only [Finset.mem_powersetCard]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      rw [← popcount_eq_popcount_suffix r μ hμ.1]
      exact hμ.2
    · intro μ₁ hμ₁ μ₂ hμ₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ₁ hμ₂
      funext i
      by_cases hi : i ∈ S
      · cases h₁ : μ₁ i
        · cases h₂ : μ₂ i
          · rfl
          · exfalso
            have h_in2 : i ∈ S.filter (fun i => μ₂ i = true) := by simp [hi, h₂]
            rw [← heq] at h_in2
            simp [hi, h₁] at h_in2
        · cases h₂ : μ₂ i
          · exfalso
            have h_in1 : i ∈ S.filter (fun i => μ₁ i = true) := by simp [hi, h₁]
            rw [heq] at h_in1
            simp [hi, h₂] at h_in1
          · rfl
      · rw [isSuffixMask_iff] at hμ₁ hμ₂
        rw [hμ₁.1 i hi, hμ₂.1 i hi]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hT_sub, hT_card⟩ := hT
      refine ⟨fun i => decide (i ∈ T), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rw [isSuffixMask_iff]
          intro i hi
          have : i ∉ T := fun h => hi (hT_sub h)
          simp [this]
        · have heq : (Finset.univ.filter (fun i : Fin n => decide (i ∈ T) = true)) = T := by
            ext i; simp
          rw [heq]; exact hT_card
      · ext i
        simp only [Finset.mem_filter, decide_eq_true_eq]
        constructor
        · intro ⟨_, h⟩; exact h
        · intro h
          exact ⟨hT_sub h, h⟩
  rw [key, Finset.card_powersetCard]

/-- Computation of the prefix marginal. -/
lemma prefix_marginal {n : ℕ} (b : BinVec n) (δ : DelProb) (r : ℤ)
    (h_lo : 0 ≤ r + ((n / 4 : ℕ) : ℤ))
    (h_hi : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) (z : ℕ) :
    (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then prefixWeight n b δ r t else 0))
      = ((Nat.choose (r + ((n / 4 : ℕ) : ℤ)).toNat z : ENNReal) *
          ENNReal.ofReal ((1 - δ.val) ^ z) *
          ENNReal.ofReal (δ.val ^ ((r + ((n / 4 : ℕ) : ℤ)).toNat - z))) := by
  rw [sum_prefixWeight_swap]
  -- Now LHS = ∑ μ, [isPrefixMask ∧ |restrict b μ|=z] * keepWeight
  -- Convert |restrict b μ|=z to popcount=z
  set k : ℕ := (r + ((n / 4 : ℕ) : ℤ)).toNat with hk_def
  set L : Finset (Fin n) := prefixIdxs n r
  have hL_card : L.card = k := prefixIdxs_card r h_lo h_hi
  -- Step 1: rewrite the sum using length_restrict_eq_card and prefixKeepWeight_value
  have hrewrite : ∀ μ : Fin n → Bool,
      (if isPrefixMask n r μ ∧ (restrict b μ).length = z then prefixKeepWeight n δ r μ else 0)
      = (if isPrefixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z then
          ENNReal.ofReal (1 - δ.val) ^ z * ENNReal.ofReal δ.val ^ (k - z) else 0) := by
    intro μ
    rw [length_restrict_eq_card]
    by_cases hp : isPrefixMask n r μ
    · by_cases hc : (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z
      · rw [if_pos ⟨hp, hc⟩, if_pos ⟨hp, hc⟩]
        rw [prefixKeepWeight_value]
        congr 1
        · rw [popcount_eq_popcount_prefix r μ hp] at hc; rw [← hc]
        · rw [popcount_eq_popcount_prefix r μ hp] at hc
          rw [hL_card, ← hc]
      · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc h.2)]
    · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1)]
  rw [Finset.sum_congr rfl (fun μ _ => hrewrite μ)]
  -- Step 2: factor out the constant
  rw [show (∑ μ : Fin n → Bool, (if isPrefixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z then
          ENNReal.ofReal (1 - δ.val) ^ z * ENNReal.ofReal δ.val ^ (k - z) else 0))
        = (Finset.univ.filter (fun μ : Fin n → Bool =>
            isPrefixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z)).card *
          (ENNReal.ofReal (1 - δ.val) ^ z * ENNReal.ofReal δ.val ^ (k - z)) from ?_]
  · -- Step 3: count and finish
    rw [mask_count_prefix_popcount, hL_card]
    rw [show ENNReal.ofReal (1 - δ.val) ^ z = ENNReal.ofReal ((1 - δ.val) ^ z) from
      (ENNReal.ofReal_pow (by linarith [δ.lt_one]) z).symm]
    rw [show ENNReal.ofReal δ.val ^ (k - z) = ENNReal.ofReal (δ.val ^ (k - z)) from
      (ENNReal.ofReal_pow δ.pos.le (k - z)).symm]
    ring
  · rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]

/-- Computation of the suffix marginal. -/
lemma suffix_marginal {n : ℕ} (b : BinVec n) (δ : DelProb) (r : ℤ)
    (h_lo : 0 ≤ r + ((n / 4 : ℕ) : ℤ))
    (h_hi : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) (z : ℕ) :
    (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then suffixWeight n b δ r t else 0))
      = ((Nat.choose (suffixIdxs n r).card z : ENNReal) *
          ENNReal.ofReal ((1 - δ.val) ^ z) *
          ENNReal.ofReal (δ.val ^ ((suffixIdxs n r).card - z))) := by
  rw [sum_suffixWeight_swap]
  set L : Finset (Fin n) := suffixIdxs n r
  have hrewrite : ∀ μ : Fin n → Bool,
      (if isSuffixMask n r μ ∧ (restrict b μ).length = z then suffixKeepWeight n δ r μ else 0)
      = (if isSuffixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z then
          ENNReal.ofReal (1 - δ.val) ^ z * ENNReal.ofReal δ.val ^ (L.card - z) else 0) := by
    intro μ
    rw [length_restrict_eq_card]
    by_cases hp : isSuffixMask n r μ
    · by_cases hc : (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z
      · rw [if_pos ⟨hp, hc⟩, if_pos ⟨hp, hc⟩]
        rw [suffixKeepWeight_value]
        congr 1
        · rw [popcount_eq_popcount_suffix r μ hp] at hc; rw [← hc]
        · rw [popcount_eq_popcount_suffix r μ hp] at hc; rw [← hc]
      · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc h.2)]
    · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1)]
  rw [Finset.sum_congr rfl (fun μ _ => hrewrite μ)]
  rw [show (∑ μ : Fin n → Bool, (if isSuffixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z then
          ENNReal.ofReal (1 - δ.val) ^ z * ENNReal.ofReal δ.val ^ (L.card - z) else 0))
        = (Finset.univ.filter (fun μ : Fin n → Bool =>
            isSuffixMask n r μ ∧ (Finset.univ.filter (fun i : Fin n => μ i = true)).card = z)).card *
          (ENNReal.ofReal (1 - δ.val) ^ z * ENNReal.ofReal δ.val ^ (L.card - z)) from ?_]
  · rw [mask_count_suffix_popcount]
    rw [show ENNReal.ofReal (1 - δ.val) ^ z = ENNReal.ofReal ((1 - δ.val) ^ z) from
      (ENNReal.ofReal_pow (by linarith [δ.lt_one]) z).symm]
    rw [show ENNReal.ofReal δ.val ^ (L.card - z) = ENNReal.ofReal (δ.val ^ (L.card - z)) from
      (ENNReal.ofReal_pow δ.pos.le (L.card - z)).symm]
    ring
  · rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]

/-- Cast bridges. -/
lemma nat_div_four_cast (n : ℕ) : ((n / 4 : ℕ) : ℤ) = (n : ℤ) / 4 := by
  push_cast
  omega

lemma nat_div_two_cast (n : ℕ) : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by
  push_cast
  omega

/-- Cardinality of the suffix index set: equals `n - n/2 - k.toNat`. -/
lemma suffixIdxs_card_correct {n : ℕ} (r : ℤ) (h_lo : 0 ≤ r + ((n / 4 : ℕ) : ℤ))
    (h_hi : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ)) :
    (suffixIdxs n r).card = n - n / 2 - (r + ((n / 4 : ℕ) : ℤ)).toNat := by
  unfold suffixIdxs
  set k : ℕ := (r + ((n / 4 : ℕ) : ℤ)).toNat with hk_def
  have hk_eq : (k : ℤ) = r + ((n / 4 : ℕ) : ℤ) := Int.toNat_of_nonneg h_lo
  -- k ≤ n/2 follows from h_hi
  have hk_le_n2 : k ≤ n / 2 := by
    have : (k : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by rw [hk_eq]; exact h_hi
    exact_mod_cast this
  -- n/2 + k ≤ n
  have h_bound : n / 2 + k ≤ n := by
    have hn2_le_n : n / 2 ≤ n := Nat.div_le_self n 2
    omega
  -- Convert the filter to use `i.val ≥ n/2 + k`.
  have hfilter_eq : ((Finset.univ : Finset (Fin n)).filter
      (fun i : Fin n => (i : ℤ) ≥ ((n / 4 + n / 2 : ℕ) : ℤ) + r))
      = ((Finset.univ : Finset (Fin n)).filter
          (fun i : Fin n => n / 2 + k ≤ (i : ℕ))) := by
    apply Finset.filter_congr
    intro i _
    -- We need (i : ℤ) ≥ (n/4 + n/2) + r ↔ n/2 + k ≤ i
    -- Using k = r + n/4, we have (n/4 + n/2) + r = n/2 + (n/4 + r) = n/2 + k
    have h1 : ((n / 4 + n / 2 : ℕ) : ℤ) + r = ((n / 2 : ℕ) : ℤ) + (k : ℤ) := by
      rw [hk_eq]
      have : ((n / 4 + n / 2 : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) + ((n / 4 : ℕ) : ℤ) := by
        push_cast; ring
      linarith
    rw [h1]
    constructor
    · intro h
      have h' : ((n / 2 + k : ℕ) : ℤ) ≤ (i : ℤ) := by
        have hcast : ((n / 2 + k : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) + (k : ℤ) := by
          push_cast; ring
        rw [hcast]; exact h
      exact_mod_cast h'
    · intro h
      have h' : ((n / 2 + k : ℕ) : ℤ) ≤ (i : ℤ) := by exact_mod_cast h
      have hcast : ((n / 2 + k : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) + (k : ℤ) := by
        push_cast; ring
      rw [hcast] at h'
      exact h'
  rw [hfilter_eq]
  -- Now compute card of {i : Fin n | n/2 + k ≤ i.val}
  have hcompl_card : ((Finset.univ : Finset (Fin n)).filter
        (fun i : Fin n => n / 2 + k ≤ (i : ℕ))).card =
      n - (n / 2 + k) := by
    -- Bijection with Finset.range (n - (n/2+k)) via i ↦ i - (n/2+k)
    have hcard : ((Finset.univ : Finset (Fin n)).filter
        (fun i : Fin n => n / 2 + k ≤ (i : ℕ))).card =
        (Finset.range (n - (n / 2 + k))).card := by
      apply Finset.card_bij (fun (i : Fin n) (_ : i ∈ _) => (i : ℕ) - (n / 2 + k))
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_range]
        omega
      · intro i hi j hj heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
        apply Fin.ext
        omega
      · intro b hb
        simp only [Finset.mem_range] at hb
        refine ⟨⟨b + (n / 2 + k), by omega⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · simp
    rw [hcard, Finset.card_range]
  rw [hcompl_card]
  omega

end DeletionLengthMarginalProof

theorem DeletionLengthMarginal :
    ∀ {n : ℕ} (b : Workspace.Types.BinVec.BinVec n)
      (δ : Workspace.Types.DelProb.DelProb)
      (r : ℤ) (_h_lo : 0 ≤ r + (n / 4 : ℤ))
      (_h_hi : r + (n / 4 : ℤ) ≤ (n / 2 : ℤ))
      (z : ℕ),
      (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then
          Workspace.Types.PartialDeletionProcess.prefixWeight n b δ r t
         else 0))
        = Workspace.Types.LengthsOnlyProcess.prefixLengthWeight n δ r z
      ∧
      (∑' t : Workspace.Types.Trace.Trace n,
        (if t.bits.length = z then
          Workspace.Types.PartialDeletionProcess.suffixWeight n b δ r t
         else 0))
        = Workspace.Types.LengthsOnlyProcess.suffixLengthWeight n δ r z := by
  intro n b δ r h_lo h_hi z
  -- Convert hypotheses to use ((n/4 : ℕ) : ℤ) and ((n/2 : ℕ) : ℤ).
  have h_lo' : 0 ≤ r + ((n / 4 : ℕ) : ℤ) := by
    rw [DeletionLengthMarginalProof.nat_div_four_cast]; exact h_lo
  have h_hi' : r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
    rw [DeletionLengthMarginalProof.nat_div_four_cast,
        DeletionLengthMarginalProof.nat_div_two_cast]
    exact h_hi
  have h_inrange : 0 ≤ r + ((n / 4 : ℕ) : ℤ) ∧
      r + ((n / 4 : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := ⟨h_lo', h_hi'⟩
  refine ⟨?_, ?_⟩
  · -- Prefix part
    rw [DeletionLengthMarginalProof.prefix_marginal b δ r h_lo' h_hi' z]
    -- Goal: rhs = prefixLengthWeight n δ r z
    unfold prefixLengthWeight
    rw [dif_pos h_inrange]
    unfold binomialPMF
    -- They are now equal modulo ofReal_pow rewriting
    rfl
  · -- Suffix part
    rw [DeletionLengthMarginalProof.suffix_marginal b δ r h_lo' h_hi' z]
    -- Goal: rhs = suffixLengthWeight n δ r z
    unfold suffixLengthWeight
    rw [dif_pos h_inrange]
    unfold binomialPMF
    rw [DeletionLengthMarginalProof.suffixIdxs_card_correct r h_lo' h_hi']
