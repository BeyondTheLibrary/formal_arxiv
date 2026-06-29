import Mathlib

open BigOperators
open Classical

namespace Workspace.Encoding.Lemma32

/-! # Lemma 3.2 (`lem:large-wt-W`) — large-weight elements beyond the cutoff
have small intersection with `W`.

**Source**: `@../arXiv-2412.03540v1.tex`, Section 3.2, Definition (cutoff) and
Lemma `lem:large-wt-W`.

## Definition 3.1 (cutoff), faithfully.

Given `W, H ⊆ X` and a weight vector `λ : X → ℝ`, order the elements of `H`
as `h₁ ≥ h₂ ≥ ⋯ ≥ h_{|H|}` (descending by `λ`). Here this ordering is given by
a list `L` which enumerates `H` (`L.Nodup`, `L.toFinset = H`) and is sorted
descending (`List.Sorted (λ a b => λ a ≥ λ b) L`). For an index `b` the suffix
is `H_{≥b} = (L.drop b).toFinset` and the prefix is `H_{<b} = (L.take b).toFinset`.

The cutoff `b = b(W,H,λ)` is the SMALLEST index such that
`2 · λ(W ∩ H_{≥b}) ≥ λ(H_{≥b})` (i.e. `λ(W ∩ H_{≥b}) ≥ ½ λ(H_{≥b})`). Such a
`b` always exists because the empty suffix (`b = |H|`) satisfies the condition
`0 ≥ 0`. We use `Nat.find` to pick the least such `b`; this is the genuine
"smallest integer" of Definition 3.1.

## Lemma 3.2.

`|H_{<b} ∩ W| ≤ ½ |H_{<b}|`, stated over `ℕ` as `2 · |H_{<b} ∩ W| ≤ |H_{<b}|`.

## Proof (summation by parts, following the paper).

Index the prefix by `i ∈ {0,…,b-1}`. With `f k = (𝟙[L[k] ∈ W] − ½)·λ(L[k])`
and the partial (segment) sums `A i = ∑_{k=i}^{b-1} f k`, summation by parts
gives
  `|H_{<b}∩W| − ½|H_{<b}| = ∑_{i<b} A i · (1/λ(L[i]) − 1/λ(L[i−1]))`  (`1/λ(L[-1])=0`).
Each `A i = λ(W∩H_{[i,b)}) − ½λ(H_{[i,b)}) < 0` by minimality of `b` (the suffix
at `i<b` fails the half-condition while the suffix at `b` satisfies it), and each
weight difference `1/λ(L[i]) − 1/λ(L[i−1]) ≥ 0` by the descending ordering. Hence
the sum is `≤ 0`, giving the bound.
-/

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The half-weight condition for the suffix starting at index `b`:
`2·λ(W ∩ H_{≥b}) ≥ λ(H_{≥b})`. -/
def SuffixHalfCond (W : Finset X) (lambda : X → ℝ) (L : List X) (b : ℕ) : Prop :=
  2 * (∑ x ∈ (L.drop b).toFinset ∩ W, lambda x) ≥ ∑ x ∈ (L.drop b).toFinset, lambda x

noncomputable instance (W : Finset X) (lambda : X → ℝ) (L : List X) (b : ℕ) :
    Decidable (SuffixHalfCond W lambda L b) := Classical.dec _

/-- The empty suffix (`b = L.length`) always satisfies the half-condition. -/
lemma suffixHalfCond_length (W : Finset X) (lambda : X → ℝ) (L : List X) :
    SuffixHalfCond W lambda L L.length := by
  unfold SuffixHalfCond
  simp

/-- Existence of an index satisfying the suffix half-condition. -/
lemma exists_suffixHalfCond (W : Finset X) (lambda : X → ℝ) (L : List X) :
    ∃ b, SuffixHalfCond W lambda L b :=
  ⟨L.length, suffixHalfCond_length W lambda L⟩

/-- The cutoff index `b(W,H,λ)`: the smallest index with the suffix
half-condition (Definition 3.1). -/
noncomputable def cutoff (W : Finset X) (lambda : X → ℝ) (L : List X) : ℕ :=
  Nat.find (exists_suffixHalfCond W lambda L)

/-- `cutoff` satisfies the half-condition. -/
lemma cutoff_spec (W : Finset X) (lambda : X → ℝ) (L : List X) :
    SuffixHalfCond W lambda L (cutoff W lambda L) :=
  Nat.find_spec (exists_suffixHalfCond W lambda L)

/-- Minimality of `cutoff`: every smaller index fails the half-condition. -/
lemma cutoff_min (W : Finset X) (lambda : X → ℝ) (L : List X) {i : ℕ}
    (hi : i < cutoff W lambda L) : ¬ SuffixHalfCond W lambda L i :=
  Nat.find_min (exists_suffixHalfCond W lambda L) hi

/-- `cutoff ≤ L.length`. -/
lemma cutoff_le_length (W : Finset X) (lambda : X → ℝ) (L : List X) :
    cutoff W lambda L ≤ L.length :=
  Nat.find_le (suffixHalfCond_length W lambda L)

/-! ## Index helpers

We work with the descending list `L`.  For an index `i < L.length` the
`i`-th element is `L[i]`, its weight is `lam i = λ(L[i])`, and the
membership indicator in `W` is `ind i`.  Both extend by `0` past the end of
the list. -/

/-- The weight of the `i`-th element of `L` (0 past the end). -/
noncomputable def lam (lambda : X → ℝ) (L : List X) (i : ℕ) : ℝ :=
  ((L.map lambda).getD i 0)

/-- The `W`-membership indicator of the `i`-th element of `L` (0 past the end). -/
noncomputable def ind (W : Finset X) (L : List X) (i : ℕ) : ℝ :=
  ((L.map (fun x => if x ∈ W then (1 : ℝ) else 0)).getD i 0)

/-- Value of `lam` at an in-range index. -/
lemma lam_eq (lambda : X → ℝ) (L : List X) {i : ℕ} (hi : i < L.length) :
    lam lambda L i = lambda (L[i]'hi) := by
  unfold lam
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  exact List.getElem_map lambda

/-- Value of `ind` at an in-range index. -/
lemma ind_eq (W : Finset X) (L : List X) {i : ℕ} (hi : i < L.length) :
    ind W L i = (if (L[i]'hi) ∈ W then (1 : ℝ) else 0) := by
  unfold ind
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  exact List.getElem_map _

/-! ## The suffix deficit `Suf`

`Suf m = λ(W ∩ H_{≥m}) − ½ λ(H_{≥m})` where `H_{≥m} = (L.drop m).toFinset`.
The half-condition at `m` is exactly `Suf m ≥ 0`. -/

/-- The suffix deficit at drop-amount `m`. -/
noncomputable def Suf (W : Finset X) (lambda : X → ℝ) (L : List X) (m : ℕ) : ℝ :=
  (∑ x ∈ (L.drop m).toFinset ∩ W, lambda x)
    - 1 / 2 * (∑ x ∈ (L.drop m).toFinset, lambda x)

/-- The half-condition holds at `m` iff `Suf … m ≥ 0`. -/
lemma suffixHalfCond_iff_Suf (W : Finset X) (lambda : X → ℝ) (L : List X) (m : ℕ) :
    SuffixHalfCond W lambda L m ↔ 0 ≤ Suf W lambda L m := by
  unfold SuffixHalfCond Suf
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Splitting one element off the front of a suffix `(L.drop m).toFinset`,
using nodup so the head is fresh. -/
lemma drop_toFinset_insert (L : List X) (hnd : L.Nodup) {m : ℕ} (hm : m < L.length) :
    (L.drop m).toFinset = insert (L[m]'hm) ((L.drop (m + 1)).toFinset)
    ∧ (L[m]'hm) ∉ (L.drop (m + 1)).toFinset := by
  have hsplit : L.drop m = (L[m]'hm) :: L.drop (m + 1) :=
    List.drop_eq_getElem_cons hm
  have hnd_drop : (L.drop m).Nodup := hnd.sublist (List.drop_sublist m L)
  refine ⟨?_, ?_⟩
  · rw [hsplit, List.toFinset_cons]
  · rw [hsplit] at hnd_drop
    rw [List.nodup_cons] at hnd_drop
    simpa using hnd_drop.1

/-- Key telescoping identity: `Suf m − Suf (m+1) = (ind m − ½) · lam m`. -/
lemma Suf_sub_succ (W : Finset X) (lambda : X → ℝ) (L : List X) (hnd : L.Nodup)
    {m : ℕ} (hm : m < L.length) :
    Suf W lambda L m - Suf W lambda L (m + 1)
      = (ind W L m - 1 / 2) * lam lambda L m := by
  obtain ⟨hins, hnotin⟩ := drop_toFinset_insert L hnd hm
  unfold Suf
  -- mass split
  have hmass : (∑ x ∈ (L.drop m).toFinset, lambda x)
      = lambda (L[m]'hm) + (∑ x ∈ (L.drop (m + 1)).toFinset, lambda x) := by
    rw [hins, Finset.sum_insert hnotin]
  -- W-mass split
  have hwins : (L.drop m).toFinset ∩ W
      = if (L[m]'hm) ∈ W then insert (L[m]'hm) ((L.drop (m+1)).toFinset ∩ W)
        else ((L.drop (m+1)).toFinset ∩ W) := by
    rw [hins]; split_ifs with hmem
    · rw [Finset.insert_inter_of_mem hmem]
    · rw [Finset.insert_inter_of_notMem hmem]
  have hwmass : (∑ x ∈ (L.drop m).toFinset ∩ W, lambda x)
      = (if (L[m]'hm) ∈ W then lambda (L[m]'hm) else 0)
        + (∑ x ∈ (L.drop (m+1)).toFinset ∩ W, lambda x) := by
    rw [hwins]; split_ifs with hmem
    · rw [Finset.sum_insert (by simp [hnotin])]
    · simp
  rw [hmass, hwmass, lam_eq lambda L hm, ind_eq W L hm]
  split_ifs with hmem <;> ring

/-! ## Bridge: prefix Finset-sums as index-sums over `range b`. -/

/-- For a real list `M` and `b ≤ M.length`,
`(M.take b).sum = ∑ i ∈ range b, M.getD i 0`. -/
lemma take_sum_eq_range_getD (M : List ℝ) :
    ∀ b, b ≤ M.length → (M.take b).sum = ∑ i ∈ Finset.range b, M.getD i 0 := by
  intro b
  induction b with
  | zero => simp
  | succ k ih =>
    intro hk
    have hk' : k < M.length := hk
    rw [List.sum_take_succ M k hk', Finset.sum_range_succ, ih (le_of_lt hk'),
      List.getD_eq_getElem _ _ hk']

/-- Prefix Finset-sum of `h` over `(L.take b).toFinset` equals the index-sum of
`(L.map h).getD · 0` over `range b`, when `L` is nodup and `b ≤ L.length`. -/
lemma take_toFinset_sum_eq_range (L : List X) (hnd : L.Nodup) (h : X → ℝ)
    {b : ℕ} (hb : b ≤ L.length) :
    (∑ x ∈ (L.take b).toFinset, h x) = ∑ i ∈ Finset.range b, (L.map h).getD i 0 := by
  have hnd_take : (L.take b).Nodup := hnd.sublist (List.take_sublist b L)
  rw [List.sum_toFinset h hnd_take, List.map_take]
  rw [take_sum_eq_range_getD (L.map h) b (by simpa using hb)]

/-! ## Sign ingredients for the summation-by-parts. -/

/-- For `i < length`, `lam` is positive (weights are positive on `H`). -/
lemma lam_pos (lambda : X → ℝ) (L : List X) (H : Finset X) (hL : L.toFinset = H)
    (hpos : ∀ x ∈ H, 0 < lambda x) {i : ℕ} (hi : i < L.length) :
    0 < lam lambda L i := by
  rw [lam_eq lambda L hi]
  apply hpos
  rw [← hL]
  simp [List.mem_toFinset, List.getElem_mem]

/-- Segment sum telescopes: `∑_{i∈Ico j b} (Suf i − Suf (i+1)) = Suf j − Suf b`. -/
lemma segment_sum_eq (W : Finset X) (lambda : X → ℝ) (L : List X) {j b : ℕ}
    (hjb : j ≤ b) :
    (∑ i ∈ Finset.Ico j b, (Suf W lambda L i - Suf W lambda L (i + 1)))
      = Suf W lambda L j - Suf W lambda L b := by
  have h := Finset.sum_Ico_sub (Suf W lambda L) hjb
  have hneg : (∑ i ∈ Finset.Ico j b, (Suf W lambda L i - Suf W lambda L (i + 1)))
      = - (∑ i ∈ Finset.Ico j b, (Suf W lambda L (i + 1) - Suf W lambda L i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hneg, h]; ring

/-! ## Abstract summation by parts (Abel), segment form.

With `G 0 = 0`, `G (j+1) = g j`, `dg j = G (j+1) − G j`, and segment partial
sums `A j = ∑_{i∈Ico j b} fsec i`, we have
  `∑_{i<b} fsec i · g i = ∑_{j<b} dg j · A j`.
This is the summation-by-parts identity of the paper (with the convention
`1/λ(h₀) = 0` encoded by `G 0 = 0`). -/
lemma abel_segment (b : ℕ) (fsec g : ℕ → ℝ) :
    (∑ i ∈ Finset.range b, fsec i * g i)
      = ∑ j ∈ Finset.range b,
          (g j - (if j = 0 then 0 else g (j - 1)))
            * (∑ i ∈ Finset.Ico j b, fsec i) := by
  -- `G` is the shifted prefix with `G 0 = 0`, `G (j+1) = g j`.
  set G : ℕ → ℝ := fun j => if j = 0 then 0 else g (j - 1) with hG
  -- telescoping: `g i = ∑_{j∈range (i+1)} (G (j+1) - G j)`.
  have hg : ∀ i, g i = ∑ j ∈ Finset.range (i + 1), (G (j + 1) - G j) := by
    intro i
    rw [Finset.sum_range_sub G (i + 1)]
    simp [hG]
  -- the per-`j` summand `dg j = G (j+1) - G j`.
  have hdg : ∀ j, (g j - (if j = 0 then 0 else g (j - 1))) = G (j + 1) - G j := by
    intro j; simp [hG]
  -- rewrite the LHS, push `g i` as a telescoped sum, swap order.
  calc
    (∑ i ∈ Finset.range b, fsec i * g i)
        = ∑ i ∈ Finset.Ico 0 b,
            ∑ j ∈ Finset.Ico 0 (i + 1), fsec i * (G (j + 1) - G j) := by
          rw [Finset.range_eq_Ico]
          apply Finset.sum_congr rfl
          intro i _
          rw [hg i, Finset.mul_sum, Finset.range_eq_Ico]
    _ = ∑ j ∈ Finset.Ico 0 b,
            ∑ i ∈ Finset.Ico j b, fsec i * (G (j + 1) - G j) := by
          -- triangular swap (`Finset.sum_Ico_Ico_comm`).
          rw [← Finset.sum_Ico_Ico_comm 0 b (fun a c => fsec c * (G (a + 1) - G a))]
    _ = ∑ j ∈ Finset.range b,
            (g j - (if j = 0 then 0 else g (j - 1))) * (∑ i ∈ Finset.Ico j b, fsec i) := by
          rw [Finset.range_eq_Ico]
          apply Finset.sum_congr rfl
          intro j _
          rw [hdg j, ← Finset.sum_mul]
          ring

/-- Descending order ⇒ `lam` is antitone in the index. -/
lemma lam_antitone (lambda : X → ℝ) (L : List X)
    (hsorted : List.Pairwise (fun a b => lambda b ≤ lambda a) L)
    {p q : ℕ} (hpq : p < q) (hq : q < L.length) :
    lam lambda L q ≤ lam lambda L p := by
  have hp : p < L.length := lt_trans hpq hq
  rw [lam_eq lambda L hp, lam_eq lambda L hq]
  exact (List.pairwise_iff_getElem.mp hsorted) p q hp hq hpq

/-! ## Lemma 3.2 — large-weight elements beyond the cutoff. -/

/-- **Lemma 3.2 (`lem:large-wt-W`).**

Let `H ⊆ X`, `W ⊆ X`, `λ : X → ℝ` with `λ` positive on `H`.  Let `L` be the
descending ordering of `H` by `λ` (a duplicate-free enumeration of `H`, sorted
so that `λ` is non-increasing along `L`).  Let `b = cutoff W λ L` be the smallest
index with `2·λ(W ∩ H_{≥b}) ≥ λ(H_{≥b})` (Definition 3.1).  Then for the genuine
prefix `H_{<b} = (L.take b).toFinset`,
  `2 · |H_{<b} ∩ W| ≤ |H_{<b}|`,
i.e. `|H_{<b} ∩ W| ≤ ½ |H_{<b}|`.

The proof is the paper's summation-by-parts (Abel) argument. -/
theorem large_wt_W (W H : Finset X) (lambda : X → ℝ) (L : List X)
    (hnd : L.Nodup) (hL : L.toFinset = H)
    (hsorted : List.Pairwise (fun a b => lambda b ≤ lambda a) L)
    (hpos : ∀ x ∈ H, 0 < lambda x) :
    2 * (((L.take (cutoff W lambda L)).toFinset ∩ W).card)
      ≤ ((L.take (cutoff W lambda L)).toFinset).card := by
  set b := cutoff W lambda L with hb
  set P := (L.take b).toFinset with hP
  have hbn : b ≤ L.length := cutoff_le_length W lambda L
  -- abbreviations for the increment and weight-reciprocal sequences
  set fsec : ℕ → ℝ := fun i => Suf W lambda L i - Suf W lambda L (i + 1) with hfsec
  set g : ℕ → ℝ := fun i => 1 / lam lambda L i with hg
  -- (1) positivity of weights on the prefix indices
  have hlampos : ∀ i, i < b → 0 < lam lambda L i := by
    intro i hi
    exact lam_pos lambda L H hL hpos (lt_of_lt_of_le hi hbn)
  -- (2) on prefix indices, `fsec i * g i = ind i - 1/2`
  have hfg : ∀ i ∈ Finset.range b, fsec i * g i = ind W L i - 1 / 2 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hin : i < L.length := lt_of_lt_of_le hi hbn
    have hlam : 0 < lam lambda L i := hlampos i hi
    simp only [hfsec, hg]
    rw [Suf_sub_succ W lambda L hnd hin]
    field_simp
  -- (3) the Abel summation-by-parts identity from `abel_segment`
  have habel := abel_segment b fsec g
  -- (4) each Abel term is ≤ 0
  have hSuf_b : 0 ≤ Suf W lambda L b := by
    rw [← suffixHalfCond_iff_Suf]; exact cutoff_spec W lambda L
  have hSuf_lt : ∀ i, i < b → Suf W lambda L i < 0 := by
    intro i hi
    have hnot : ¬ SuffixHalfCond W lambda L i := cutoff_min W lambda L hi
    rw [suffixHalfCond_iff_Suf] at hnot
    linarith
  have hterm : ∀ j ∈ Finset.range b,
      (g j - (if j = 0 then 0 else g (j - 1))) * (∑ i ∈ Finset.Ico j b, fsec i) ≤ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    -- segment sum = Suf j - Suf b ≤ 0
    have hAj : (∑ i ∈ Finset.Ico j b, fsec i) = Suf W lambda L j - Suf W lambda L b := by
      simp only [hfsec]
      exact segment_sum_eq W lambda L (le_of_lt hj)
    have hAj_neg : (∑ i ∈ Finset.Ico j b, fsec i) ≤ 0 := by
      rw [hAj]; have := hSuf_lt j hj; linarith
    -- weight difference ≥ 0
    have hdg : 0 ≤ g j - (if j = 0 then 0 else g (j - 1)) := by
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        simp only [hg, if_true, sub_zero]
        have h0 : 0 < lam lambda L 0 := hlampos 0 hj
        exact le_of_lt (one_div_pos.mpr h0)
      · have hjne : j ≠ 0 := hjpos.ne'
        rw [if_neg hjne]
        simp only [hg]
        -- 1/lam (j-1) ≤ 1/lam j  since lam j ≤ lam (j-1), both > 0
        have hj1 : j - 1 < j := Nat.sub_lt hjpos one_pos
        have hjb : j < b := hj
        have hlamj : 0 < lam lambda L j := hlampos j hjb
        have hlamj1 : 0 < lam lambda L (j - 1) :=
          hlampos (j - 1) (lt_trans hj1 hjb)
        have hle : lam lambda L j ≤ lam lambda L (j - 1) := by
          have hjq : j < L.length := lt_of_lt_of_le hjb hbn
          exact lam_antitone lambda L hsorted hj1 hjq
        have : 1 / lam lambda L (j - 1) ≤ 1 / lam lambda L j :=
          one_div_le_one_div_of_le hlamj hle
        linarith
    -- product of (≥0) and (≤0) is ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos hdg hAj_neg
  -- (5) the deficit `∑ (ind - 1/2)` is ≤ 0
  have hdeficit : (∑ i ∈ Finset.range b, (ind W L i - 1 / 2)) ≤ 0 := by
    rw [← Finset.sum_congr rfl hfg]
    rw [habel]
    exact Finset.sum_nonpos hterm
  -- (6) convert the deficit to card form
  -- ∑ ind = (P ∩ W).card  and  b = P.card
  have hsum_ind : (∑ i ∈ Finset.range b, ind W L i)
      = ((P ∩ W).card : ℝ) := by
    have hbridge := take_toFinset_sum_eq_range L hnd
      (fun x => if x ∈ W then (1 : ℝ) else 0) hbn
    -- the index sum of `(L.map (fun x => if x∈W then 1 else 0)).getD · 0` is `∑ ind`
    have : (∑ i ∈ Finset.range b, ind W L i)
        = ∑ i ∈ Finset.range b,
            (L.map (fun x => if x ∈ W then (1 : ℝ) else 0)).getD i 0 := by
      apply Finset.sum_congr rfl; intro i _; rfl
    rw [this, ← hbridge]
    -- ∑ x ∈ P, (if x∈W then 1 else 0) = (P ∩ W).card
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard_P : ((P.card : ℝ)) = (b : ℝ) := by
    have hbridge := take_toFinset_sum_eq_range L hnd (fun _ => (1 : ℝ)) hbn
    have hlhs : (∑ _x ∈ P, (1 : ℝ)) = (P.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hrhs : (∑ i ∈ Finset.range b, (L.map (fun _ => (1 : ℝ))).getD i 0)
        = (b : ℝ) := by
      rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)) ?_]
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [List.getD_eq_getElem _ _ (by simp [lt_of_lt_of_le hi hbn])]
        simp
    rw [hP] at hlhs ⊢
    rw [← hlhs, hbridge, hrhs]
  -- (7) assemble
  have hsum_split : (∑ i ∈ Finset.range b, (ind W L i - 1 / 2))
      = (∑ i ∈ Finset.range b, ind W L i) - (b : ℝ) * (1 / 2) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum_split, hsum_ind] at hdeficit
  -- hdeficit : (P ∩ W).card - b * (1/2) ≤ 0
  rw [← hcard_P] at hdeficit
  -- now a pure inequality over ℝ between cards, transfer to ℕ
  have hfinal : (2 : ℝ) * ((P ∩ W).card : ℝ) ≤ (P.card : ℝ) := by linarith
  have := hfinal
  rw [hP] at this ⊢
  exact_mod_cast this

end Workspace.Encoding.Lemma32
