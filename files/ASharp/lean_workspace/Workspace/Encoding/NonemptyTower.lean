import Workspace.Encoding.TowerFrag

open BigOperators
open Classical

namespace Workspace.Encoding.NonemptyTower

/-! # Section 3.3 — Lemma 3.8: if `W` is bad, any tower of fragments is nonempty.

**Source**: `@../arXiv-2412.03540v1.tex`, Section 3.3, the unnumbered lemma
"If `W` is bad, then any tower of fragments `T` of `(W,H)` for `H ∈ ℋ` is
nonempty, in that `u = ∑ᵢ |Tᵢ| > 0`" (paper lines ~459–488).

`W = (Wᵢ)` is **bad** if for every `H' ∈ ℋ`,
`∑_{x ∈ (⋃_{i<s} Wᵢ) ∩ H'} λ_{H'}(x) < 1 − 2^{−s}`.

**Lemma 3.8.** If `W` is bad, then for every tower of fragments `T` of `(W,H)`,
`∑_{i<s} |Tᵢ| > 0`.

## Faithful proof (paper, verbatim).

Assume `u = ∑ᵢ |Tᵢ| = 0`, so `Tᵢ = ∅` for all `i < s`. Then `Zᵢ = Tᵢ ∪ Wᵢ = Wᵢ`,
and `t`-feasibility of `Z = W` with `t = 0` provides a witness `(Ŵ, Ĥ, hĤ)` with
`Ŵᵢ ⊆ Wᵢ`, `|Ŵᵢ| = |Wᵢ| − 0 = |Wᵢ|` (hence `Ŵᵢ = Wᵢ`), and the cutoff prefix
`Rstep Ŵ Ĥ λ_Ĥ i = (Ĥᵢ)_{<b̂ᵢ} ⊆ Wᵢ`.

Write `λ = λ_Ĥ = lambda_vec Ĥ hĤ`, `Hᵢ = Hstep Ŵ Ĥ λ i` (the iterate; paper's
`Ĥ_{i+1}`), and `Uⱼ = ⋃_{i<j} Ŵᵢ`. We prove by induction on `j ≤ s`:

  **(equality)** `Hⱼ = Ĥ ∖ Uⱼ`, and
  **(halving)** `λ(Ĥ ∖ Uⱼ) ≤ 2^{−j} · λ(Ĥ)`.

The equality combines: `Hⱼ ⊆ Ĥ` and `Hⱼ` disjoint from `Uⱼ` (no premise needed),
with `Ĥ ∖ Uⱼ ⊆ Hⱼ` (uses `Rstep i ⊆ Ŵᵢ`). The halving step uses
`H_{j+1} = (Hⱼ)_{≥ b̂} ∖ Ŵⱼ`, the cutoff half-weight
`λ((Hⱼ)_{≥ b̂} ∩ Ŵⱼ) ≥ ½ λ((Hⱼ)_{≥ b̂})` (`cutoff_spec`), and `(Hⱼ)_{≥ b̂} ⊆ Hⱼ`:
`λ(H_{j+1}) = λ((Hⱼ)_{≥b̂} ∖ Ŵⱼ) = λ((Hⱼ)_{≥b̂}) − λ((Hⱼ)_{≥b̂} ∩ Ŵⱼ)
            ≤ ½ λ((Hⱼ)_{≥b̂}) ≤ ½ λ(Hⱼ)`.

Finally `λ(Uₛ ∩ Ĥ) = λ(Ĥ) − λ(Ĥ ∖ Uₛ) ≥ (1 − 2^{−s}) λ(Ĥ) ≥ 1 − 2^{−s}` (using
`λ(Ĥ) ≥ 1` and `2^{−s} ≤ 1`). Since `Ŵᵢ = Wᵢ`, `Uₛ ∩ Ĥ` carries the same weight
as the badness set, contradicting `W` bad at `Ĥ`.

## Faithfulness note on hypotheses.

`λ_{H'}` is a probability weight on `H'`: supported on `H'` (`hsupp`), summing to
`≥ 1` (`hsum`), and **non-negative** (`hnonneg`). The paper takes `λ_{H'}` to be a
genuine probability distribution, so non-negativity is part of the intended
object; it is needed for the monotonicity `S ⊆ T ⇒ λ(S) ≤ λ(T)` used throughout.
-/

variable {X : Type} [Fintype X] [DecidableEq X]

open Workspace.Encoding.Procedure
open Workspace.Encoding.TowerFrag

/-! ## Structural facts about the iteration `Hstep` relative to a witness. -/

/-- `Rset ∪ geSet = H`: the cutoff prefix and suffix together recover `H`. -/
lemma Rset_union_geSet (W H : Finset X) (lambda : X → ℝ) :
    Rset W H lambda ∪ geSet W H lambda = H := by
  unfold Rset geSet
  rw [← List.toFinset_append, List.take_append_drop, sortedOf_toFinset]

/-- `geSet = H ∖ Rset` (prefix/suffix complementarity). -/
lemma geSet_eq_sdiff_Rset (W H : Finset X) (lambda : X → ℝ) :
    geSet W H lambda = H \ Rset W H lambda := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨geSet_subset W H lambda hx, ?_⟩
    intro hxR
    exact (Finset.disjoint_left.mp (Rset_disjoint_geSet W H lambda)) hxR hx
  · intro x hx
    rw [Finset.mem_sdiff] at hx
    have hxH : x ∈ Rset W H lambda ∪ geSet W H lambda := by
      rw [Rset_union_geSet]; exact hx.1
    rcases Finset.mem_union.mp hxH with h | h
    · exact absurd h hx.2
    · exact h

/-- `Hstep j` is disjoint from `⋃_{i<j} Wᵢ`. (No `Rstep ⊆ W` premise needed.) -/
lemma Hstep_disjoint_biUnion (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (j : ℕ) :
    Disjoint (Hstep W H lambda j) ((Finset.range j).biUnion W) := by
  induction j with
  | zero => simp
  | succ k ih =>
    rw [Finset.disjoint_left]
    intro x hx hxU
    rw [Finset.mem_biUnion] at hxU
    obtain ⟨i, hi, hxWi⟩ := hxU
    rw [Finset.mem_range, Nat.lt_succ_iff_lt_or_eq] at hi
    -- `x ∈ Hstep (k+1) = geSet (W k) (Hstep k) λ \ (W k)`.
    rw [Hstep_succ, Finset.mem_sdiff] at hx
    rcases hi with hik | hik
    · -- `i < k`: `x ∈ Hstep (k+1) ⊆ Hstep k` is disjoint from `W i` (`i<k`).
      have hxk : x ∈ Hstep W H lambda k :=
        Hstep_succ_subset W H lambda k (by rw [Hstep_succ, Finset.mem_sdiff]; exact hx)
      have : x ∈ (Finset.range k).biUnion W := by
        rw [Finset.mem_biUnion]; exact ⟨i, Finset.mem_range.mpr hik, hxWi⟩
      exact (Finset.disjoint_left.mp ih) hxk this
    · -- `i = k`: `x ∉ W k` from the `\ (W k)`, contradiction with `x ∈ W i = W k`.
      subst hik
      exact hx.2 hxWi

/-- `H ∖ ⋃_{i<j} Wᵢ ⊆ Hstep j`, given `Rstep i ⊆ Wᵢ` for all `i < j`. -/
lemma sdiff_biUnion_subset_Hstep (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    {j : ℕ} (hR : ∀ i, i < j → Rstep W H lambda i ⊆ W i) :
    H \ ((Finset.range j).biUnion W) ⊆ Hstep W H lambda j := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hRk : ∀ i, i < k → Rstep W H lambda i ⊆ W i :=
      fun i hi => hR i (Nat.lt_succ_of_lt hi)
    have ihk := ih hRk
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxH, hxU⟩ := hx
    -- `x ∉ ⋃_{i<k+1}` ⇒ `x ∉ ⋃_{i<k}` and `x ∉ W k`.
    have hxUk : x ∉ (Finset.range k).biUnion W := by
      intro h
      apply hxU
      rw [Finset.mem_biUnion] at h ⊢
      obtain ⟨i, hi, hxi⟩ := h
      exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)), hxi⟩
    have hxWk : x ∉ W k := by
      intro h
      apply hxU
      rw [Finset.mem_biUnion]
      exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), h⟩
    -- `x ∈ H \ ⋃_{i<k} ⊆ Hstep k`.
    have hxHk : x ∈ Hstep W H lambda k := ihk (by rw [Finset.mem_sdiff]; exact ⟨hxH, hxUk⟩)
    -- `x ∉ Rstep k` (else `x ∈ W k`); so `x ∈ geSet (W k) (Hstep k) = Hstep k \ Rstep k`.
    have hxnotR : x ∉ Rstep W H lambda k := by
      intro h
      exact hxWk (hR k (Nat.lt_succ_self k) h)
    have hxgeSet : x ∈ geSet (W k) (Hstep W H lambda k) lambda := by
      rw [geSet_eq_sdiff_Rset, Finset.mem_sdiff]
      exact ⟨hxHk, hxnotR⟩
    -- `Hstep (k+1) = geSet (W k) (Hstep k) λ \ (W k)`, and `x ∉ W k`.
    rw [Hstep_succ, Finset.mem_sdiff]
    exact ⟨hxgeSet, hxWk⟩

/-- **`Hstep j = H ∖ ⋃_{i<j} Wᵢ`**, given `Rstep i ⊆ Wᵢ` for all `i < j`. -/
lemma Hstep_eq_sdiff_biUnion (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    {j : ℕ} (hR : ∀ i, i < j → Rstep W H lambda i ⊆ W i) :
    Hstep W H lambda j = H \ ((Finset.range j).biUnion W) := by
  apply Finset.Subset.antisymm
  · -- `Hstep j ⊆ H` and disjoint from `⋃_{i<j}`.
    intro x hx
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · have := Hstep_antitone W H lambda (Nat.zero_le j) hx
      simpa using this
    · exact fun h => (Finset.disjoint_left.mp (Hstep_disjoint_biUnion W H lambda j)) hx h
  · exact sdiff_biUnion_subset_Hstep W H lambda hR

/-! ## The cutoff half-weight property for `geSet`, in `wt` form. -/

/-- **Half-weight of the cutoff suffix** (`cutoff_spec`, re-expressed):
`λ((H)_{≥ b̂}) ≤ 2 · λ(Ŵ ∩ (H)_{≥ b̂})`. -/
lemma geSet_half_weight (W H : Finset X) (lambda : X → ℝ) :
    (∑ x ∈ geSet W H lambda, lambda x)
      ≤ 2 * (∑ x ∈ geSet W H lambda ∩ W, lambda x) := by
  have h := Workspace.Encoding.Lemma32.cutoff_spec W lambda (sortedOf H lambda)
  unfold Workspace.Encoding.Lemma32.SuffixHalfCond at h
  -- `geSet W H lambda = (sortedOf H lambda).drop (bIdx W H lambda) |>.toFinset`.
  unfold geSet bIdx
  linarith [h]

/-! ## The halving induction. -/

/-- One halving step of the induction:
`λ(Hstep (j+1)) ≤ ½ · λ(Hstep j)`. -/
lemma wt_Hstep_succ_le_half (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (hnonneg : ∀ x, 0 ≤ lambda x) (j : ℕ) :
    (∑ x ∈ Hstep W H lambda (j + 1), lambda x)
      ≤ (1 / 2) * (∑ x ∈ Hstep W H lambda j, lambda x) := by
  set G : Finset X := geSet (W j) (Hstep W H lambda j) lambda with hG
  -- `Hstep (j+1) = G \ W j`.
  have hstep : Hstep W H lambda (j + 1) = G \ (W j) := by rw [Hstep_succ]
  -- `λ(G \ W j) = λ(G) - λ(G ∩ W j)`.
  have hsdiff : (∑ x ∈ G \ (W j), lambda x)
      = (∑ x ∈ G, lambda x) - (∑ x ∈ G ∩ (W j), lambda x) := by
    have hsub : G ∩ (W j) ⊆ G := Finset.inter_subset_left
    have := Finset.sum_sdiff (f := lambda) hsub
    -- `∑_{G \ (G ∩ W j)} + ∑_{G ∩ W j} = ∑_G`, and `G \ (G ∩ W j) = G \ W j`.
    rw [Finset.sdiff_inter_self_left] at this
    linarith [this]
  -- half-weight: `λ(G) ≤ 2 λ(G ∩ W j)`.
  have hhalf : (∑ x ∈ G, lambda x) ≤ 2 * (∑ x ∈ G ∩ (W j), lambda x) :=
    geSet_half_weight (W j) (Hstep W H lambda j) lambda
  -- `G ⊆ Hstep j`, so `λ(G) ≤ λ(Hstep j)`.
  have hGsub : G ⊆ Hstep W H lambda j := geSet_subset _ _ _
  have hGle : (∑ x ∈ G, lambda x) ≤ (∑ x ∈ Hstep W H lambda j, lambda x) :=
    Finset.sum_le_sum_of_subset_of_nonneg hGsub (fun i _ _ => hnonneg i)
  rw [hstep, hsdiff]
  -- `λ(G) - λ(G ∩ W j) ≤ ½ λ(G) ≤ ½ λ(Hstep j)`.
  linarith [hhalf, hGle]

/-- **The halving induction**: `λ(Hstep j) ≤ 2^{−j} · λ(H)` for all `j`. -/
lemma wt_Hstep_le (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (hnonneg : ∀ x, 0 ≤ lambda x) (j : ℕ) :
    (∑ x ∈ Hstep W H lambda j, lambda x)
      ≤ (2 : ℝ) ^ (-(j : ℝ)) * (∑ x ∈ H, lambda x) := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hstep := wt_Hstep_succ_le_half W H lambda hnonneg k
    -- `2^{-(k+1)} = (1/2) * 2^{-k}`.
    have hpow : (2 : ℝ) ^ (-((k : ℝ) + 1)) = (1 / 2) * (2 : ℝ) ^ (-(k : ℝ)) := by
      rw [show (-((k : ℝ) + 1)) = (-(k : ℝ)) + (-1) by ring, Real.rpow_add (by norm_num)]
      rw [Real.rpow_neg_one]
      ring
    have hcast : (-(((k : ℕ) + 1 : ℕ) : ℝ)) = -((k : ℝ) + 1) := by push_cast; ring
    rw [hcast, hpow]
    -- chain: λ(Hstep (k+1)) ≤ ½ λ(Hstep k) ≤ ½ (2^{-k} λ(H)).
    have hnn : (0 : ℝ) ≤ 1 / 2 := by norm_num
    calc (∑ x ∈ Hstep W H lambda (k + 1), lambda x)
        ≤ (1 / 2) * (∑ x ∈ Hstep W H lambda k, lambda x) := hstep
      _ ≤ (1 / 2) * ((2 : ℝ) ^ (-(k : ℝ)) * (∑ x ∈ H, lambda x)) := by
          apply mul_le_mul_of_nonneg_left ih hnn
      _ = (1 / 2) * (2 : ℝ) ^ (-(k : ℝ)) * (∑ x ∈ H, lambda x) := by ring

/-! ## Lemma 3.8. -/

/-- **Lemma 3.8.** If `W` is bad, then every tower of fragments `T` of `(W,H)`
(for `H ∈ ℋ`) is nonempty: `∑_{i<s} |Tᵢ| > 0`. -/
theorem bad_implies_nonempty_tower (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (W : ℕ → Finset X) (H : Finset X) (hH : H ∈ ℋ)
    (hsupp : ∀ (H' : Finset X) (hH' : H' ∈ ℋ) x, x ∉ H' → lambda_vec H' hH' x = 0)
    (hnonneg : ∀ (H' : Finset X) (hH' : H' ∈ ℋ) x, 0 ≤ lambda_vec H' hH' x)
    (hsum : ∀ (H' : Finset X) (hH' : H' ∈ ℋ), 1 ≤ ∑ x ∈ H', lambda_vec H' hH' x)
    (hbad : ∀ (H' : Finset X) (hH' : H' ∈ ℋ),
      ∑ x ∈ (Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ W i)),
        lambda_vec H' hH' x < 1 - (2 : ℝ) ^ (-(s : ℝ)))
    (T : ℕ → Finset X)
    (hT : IsTowerOfFragments ℋ s lambda_vec W H T) :
    0 < ∑ i ∈ Finset.range s, (T i).card := by
  -- Suppose for contradiction the sum is `0`.
  by_contra hzero
  push_neg at hzero
  have hsum0 : (∑ i ∈ Finset.range s, (T i).card) = 0 := Nat.le_zero.mp hzero
  -- Each `|T i| = 0` for `i < s`, hence `T i = ∅`.
  have hTempty : ∀ i, i < s → T i = ∅ := by
    intro i hi
    have hcard0 : (T i).card = 0 := by
      have hmem : i ∈ Finset.range s := Finset.mem_range.mpr hi
      have hle : (T i).card ≤ ∑ i ∈ Finset.range s, (T i).card :=
        Finset.single_le_sum (f := fun i => (T i).card) (fun j _ => Nat.zero_le _) hmem
      omega
    exact Finset.card_eq_zero.mp hcard0
  -- Unfold the tower: `t`-feasibility of `Z i = T i ∪ W i` with `t i = |T i|`.
  obtain ⟨hfeas, _hcont, _hdisj⟩ := hT
  obtain ⟨Wh, Hh, hHh, hWcard, hRsub⟩ := hfeas
  set lam : X → ℝ := lambda_vec Hh hHh with hlam
  have hlamnn : ∀ x, 0 ≤ lam x := fun x => hnonneg Hh hHh x
  -- For `i < s`: `Z i = W i` (since `T i = ∅`), `Ŵ i = W i`, and `Rstep ⊆ W i`.
  have hZeq : ∀ i, i < s → T i ∪ W i = W i := by
    intro i hi; rw [hTempty i hi]; exact Finset.empty_union _
  have hWhsub : ∀ i, i < s → Wh i ⊆ W i := by
    intro i hi
    have h := (hWcard i hi).1
    simp only [] at h
    rw [hZeq i hi] at h; exact h
  have hWhcard : ∀ i, i < s → (Wh i).card = (W i).card := by
    intro i hi
    have h := (hWcard i hi).2
    simp only [] at h
    rw [hZeq i hi, hTempty i hi] at h
    simpa using h
  -- `Ŵ i = W i` for `i < s`.
  have hWheq : ∀ i, i < s → Wh i = W i := by
    intro i hi
    exact Finset.eq_of_subset_of_card_le (hWhsub i hi) (le_of_eq (hWhcard i hi).symm)
  -- `Rstep Ŵ Ĥ λ i ⊆ W i` for `i < s`.
  have hRWi : ∀ i, i < s → Rstep Wh Hh lam i ⊆ W i := by
    intro i hi
    have h := hRsub i hi
    simp only [] at h
    rw [hZeq i hi] at h; exact h
  -- For `i < s`, the iteration along `Ŵ` only refers to `W j` (j<i), where `Ŵ j = W j`,
  -- so `Rstep Wh Hh lam i ⊆ W i` is exactly the premise of `Hstep_eq_sdiff_biUnion`.
  -- Apply the equality `Hstep s = Ĥ ∖ ⋃_{i<s} Ŵ i` (using `Rstep i ⊆ Ŵ i`).
  have hRWh : ∀ i, i < s → Rstep Wh Hh lam i ⊆ Wh i := by
    intro i hi; rw [hWheq i hi]; exact hRWi i hi
  have hHstep_eq : Hstep Wh Hh lam s = Hh \ ((Finset.range s).biUnion Wh) :=
    Hstep_eq_sdiff_biUnion Wh Hh lam hRWh
  -- `⋃_{i<s} Ŵ i = ⋃_{i<s} W i` since `Ŵ i = W i` for `i<s`.
  have hbiU : (Finset.range s).biUnion Wh = (Finset.range s).biUnion W := by
    apply Finset.biUnion_congr rfl
    intro i hi; rw [hWheq i (Finset.mem_range.mp hi)]
  rw [hbiU] at hHstep_eq
  set U : Finset X := (Finset.range s).biUnion W with hU
  -- Halving bound at `j = s`: `λ(Hstep s) ≤ 2^{-s} λ(Ĥ)`.
  have hbound : (∑ x ∈ Hstep Wh Hh lam s, lam x)
      ≤ (2 : ℝ) ^ (-(s : ℝ)) * (∑ x ∈ Hh, lam x) :=
    wt_Hstep_le Wh Hh lam hlamnn s
  rw [hHstep_eq] at hbound
  -- `λ(Ĥ) = λ(Ĥ ∩ U) + λ(Ĥ \ U)`.
  have hsplit : (∑ x ∈ Hh, lam x)
      = (∑ x ∈ Hh ∩ U, lam x) + (∑ x ∈ Hh \ U, lam x) := by
    have hsub : Hh ∩ U ⊆ Hh := Finset.inter_subset_left
    have := Finset.sum_sdiff (f := lam) hsub
    rw [Finset.sdiff_inter_self_left] at this
    linarith [this]
  -- Lower bound on `λ(Ĥ ∩ U)`.
  set wH : ℝ := ∑ x ∈ Hh, lam x with hwH
  have hwHge1 : 1 ≤ wH := hsum Hh hHh
  -- `2^{-s} ≤ 1` since `s ≥ 0`.
  have hpowle1 : (2 : ℝ) ^ (-(s : ℝ)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    simp
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (-(s : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  -- `λ(Ĥ ∩ U) = λ(Ĥ) - λ(Ĥ \ U) ≥ (1 - 2^{-s}) λ(Ĥ) ≥ 1 - 2^{-s}`.
  have hInterGe : (1 : ℝ) - (2 : ℝ) ^ (-(s : ℝ)) ≤ (∑ x ∈ Hh ∩ U, lam x) := by
    -- `λ(Ĥ ∩ U) = wH - λ(Ĥ \ U)` and `λ(Ĥ \ U) ≤ 2^{-s} wH`.
    have hdiff : (∑ x ∈ Hh ∩ U, lam x) = wH - (∑ x ∈ Hh \ U, lam x) := by
      rw [hwH]; linarith [hsplit]
    rw [hdiff]
    -- `wH - 2^{-s} wH = (1 - 2^{-s}) wH ≥ (1 - 2^{-s}) · 1 = 1 - 2^{-s}`.
    have h1 : (∑ x ∈ Hh \ U, lam x) ≤ (2 : ℝ) ^ (-(s : ℝ)) * wH := hbound
    have h2 : (1 - (2 : ℝ) ^ (-(s : ℝ))) * 1 ≤ (1 - (2 : ℝ) ^ (-(s : ℝ))) * wH := by
      apply mul_le_mul_of_nonneg_left hwHge1
      linarith [hpowle1]
    nlinarith [h1, h2]
  -- Relate `λ(Ĥ ∩ U)` to the badness sum: the filter set has the same `λ`-weight.
  -- `filter (∃ i<s, x ∈ W i) = U` as element-sets, and `λ` supported on `Ĥ`.
  have hfilter_eq : Hh ∩ U = Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ W i) ∩ Hh := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hU,
      Finset.mem_biUnion, Finset.mem_range]
    constructor
    · rintro ⟨hxH, i, hi, hxi⟩; exact ⟨⟨i, hi, hxi⟩, hxH⟩
    · rintro ⟨⟨i, hi, hxi⟩, hxH⟩; exact ⟨hxH, i, hi, hxi⟩
  -- `λ` supported on `Ĥ`: `∑_{filter} λ = ∑_{filter ∩ Ĥ} λ`.
  have hsupp_lam : ∀ x, x ∉ Hh → lam x = 0 := fun x hx => hsupp Hh hHh x hx
  have hbadsum : (∑ x ∈ Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ W i), lam x)
      = (∑ x ∈ Hh ∩ U, lam x) := by
    rw [hfilter_eq]
    -- drop the elements outside `Ĥ` from the filter sum.
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · exact Finset.inter_subset_left
    · intro x hx
      rw [Finset.mem_sdiff, Finset.mem_inter] at hx
      -- `x ∈ filter`, `x ∉ filter ∩ Ĥ`; since `x ∈ filter`, `x ∉ Ĥ`, so `λ x = 0`.
      have hxF : x ∈ Finset.univ.filter (fun x => ∃ i, i < s ∧ x ∈ W i) := hx.1
      have hxnotH : x ∉ Hh := by
        intro hxH; exact hx.2 ⟨hxF, hxH⟩
      exact hsupp_lam x hxnotH
    · intro x _; rfl
  -- Contradiction with badness.
  have hbadH := hbad Hh hHh
  rw [hbadsum] at hbadH
  linarith [hInterGe, hbadH]

end Workspace.Encoding.NonemptyTower
