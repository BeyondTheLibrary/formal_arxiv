import Workspace.Encoding.Lemma32_LargeWeight

open BigOperators
open Classical

namespace Workspace.Encoding.Procedure

/-! # Section 3.2 — the iterative cutoff procedure and disjointness of the `Rᵢ`.

**Source**: `@../arXiv-2412.03540v1.tex`, Section 3.2, the paragraph immediately
before `\begin{defn}\label{def:feas}` (the procedure defining `bᵢ`, `Hᵢ`, `Rᵢ`).

This file builds on `Workspace.Encoding.Lemma32` (Definition 3.1 cutoff and
Lemma 3.2), which works relative to a *list* `L` enumerating `H` descending by
`λ`.  Here we supply a canonical such list (`sortedOf`), define the iteration
`H₁ = H`, `Hᵢ₊₁ = (Hᵢ)_{≥ bᵢ} ∖ Wᵢ`, the cutoff prefixes `Rᵢ = (Hᵢ)_{< bᵢ}`,
and prove the key structural fact used throughout §3.2–§3.3: **the `Rᵢ` are
pairwise disjoint**.

## The procedure (paper, verbatim).

Given `W = (W₁,…,W_s)` and `H ∈ ℋ`: set `H₁ = H`.  For `i ∈ [1,s]`, let
`bᵢ = b(Wᵢ, Hᵢ, λ_H)` (the cutoff of Definition 3.1) and define
`Hᵢ₊₁ = (Hᵢ)_{≥ bᵢ} ∖ Wᵢ`.  Define `Rᵢ(W,H) = (Hᵢ)_{< bᵢ}` and
`R(W,H) = ⋃ᵢ Rᵢ`.

## Indexing note.

The paper uses 1-based indexing (`H₁ = H`, `Rᵢ = (Hᵢ)_{<bᵢ}` for `i ∈ [1,s]`).
We use 0-based `ℕ` indexing internally: `Hstep 0 = H`, `Hstep (i+1) =
(Hstep i)_{≥} ∖ (W i)`, and `Rstep i = (Hstep i)_{<}`.  So `Hstep i` is the
paper's `H_{i+1}` and `Rstep i` is the paper's `R_{i+1}`.  The correspondence is
a uniform index shift and does not affect any statement (the disjointness claim
is `∀ i j, i ≠ j → Disjoint (Rstep i) (Rstep j)`, which is index-shift
invariant).  The weight `λ` is the fixed `λ_H` of the paper; we keep it as an
explicit parameter `lambda : X → ℝ`. -/

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## Canonical descending enumeration of a finset by `λ`.

We sort `H.toList` by the (decidable) relation `r a b := λ b ≤ λ a`, which is
total and transitive (it is the pullback of `≤` on `ℝ`).  `List.mergeSort` with
this relation yields a list that is duplicate-free, has `toFinset = H`, and is
`Pairwise (fun a b => λ b ≤ λ a)` (descending by `λ`) — exactly the three
hypotheses the `Lemma32` cutoff machinery requires. -/

/-- The descending-by-`λ` ordering relation on `X`. -/
def descRel (lambda : X → ℝ) (a b : X) : Prop := lambda b ≤ lambda a

noncomputable instance (lambda : X → ℝ) : DecidableRel (descRel lambda) := by
  intro a b; unfold descRel; infer_instance

instance (lambda : X → ℝ) : Std.Total (descRel lambda) :=
  ⟨fun a b => by unfold descRel; exact le_total (lambda b) (lambda a)⟩

instance (lambda : X → ℝ) : IsTrans X (descRel lambda) :=
  ⟨fun a b c hab hbc => by
    unfold descRel at *; exact le_trans hbc hab⟩

/-- Canonical descending enumeration of `H` by `λ`. -/
noncomputable def sortedOf (H : Finset X) (lambda : X → ℝ) : List X :=
  H.toList.mergeSort (fun a b => decide (descRel lambda a b))

/-- `sortedOf` is a permutation of `H.toList`. -/
lemma sortedOf_perm (H : Finset X) (lambda : X → ℝ) :
    (sortedOf H lambda).Perm H.toList :=
  List.mergeSort_perm _ _

/-- `sortedOf` is duplicate-free. -/
lemma sortedOf_nodup (H : Finset X) (lambda : X → ℝ) :
    (sortedOf H lambda).Nodup :=
  (sortedOf_perm H lambda).nodup_iff.mpr H.nodup_toList

/-- `sortedOf` enumerates exactly `H`. -/
lemma sortedOf_toFinset (H : Finset X) (lambda : X → ℝ) :
    (sortedOf H lambda).toFinset = H := by
  rw [List.toFinset_eq_of_perm _ _ (sortedOf_perm H lambda), Finset.toList_toFinset]

/-- `sortedOf` is sorted descending by `λ`. -/
lemma sortedOf_sorted (H : Finset X) (lambda : X → ℝ) :
    List.Pairwise (fun a b => lambda b ≤ lambda a) (sortedOf H lambda) := by
  have h := List.sorted_mergeSort' (descRel lambda) H.toList
  -- `sorted_mergeSort'` gives `Pairwise (descRel lambda)` for the mergeSort with
  -- `fun x1 x2 => decide (descRel lambda x1 x2)`, which is exactly `sortedOf`.
  simpa [sortedOf, descRel] using h

/-! ## Cutoff, prefix (`R`) and suffix as functions of `(W, H, λ)`. -/

/-- The cutoff index `bᵢ = b(W, H, λ)` (Definition 3.1), via the canonical
enumeration. -/
noncomputable def bIdx (W H : Finset X) (lambda : X → ℝ) : ℕ :=
  Lemma32.cutoff W lambda (sortedOf H lambda)

/-- The cutoff *prefix* `H_{<b} = (Hᵢ)_{<bᵢ}` (the paper's `Rᵢ`). -/
noncomputable def Rset (W H : Finset X) (lambda : X → ℝ) : Finset X :=
  ((sortedOf H lambda).take (bIdx W H lambda)).toFinset

/-- The cutoff *suffix* `H_{≥b} = (Hᵢ)_{≥bᵢ}`. -/
noncomputable def geSet (W H : Finset X) (lambda : X → ℝ) : Finset X :=
  ((sortedOf H lambda).drop (bIdx W H lambda)).toFinset

/-- **Lemma 3.2 re-exposed in `(W,H,λ)` form**: the cutoff prefix has at most
half its elements in `W`. -/
theorem large_wt_Rset (W H : Finset X) (lambda : X → ℝ)
    (hpos : ∀ x ∈ H, 0 < lambda x) :
    2 * ((Rset W H lambda ∩ W).card) ≤ (Rset W H lambda).card := by
  unfold Rset bIdx
  exact Lemma32.large_wt_W W H lambda (sortedOf H lambda)
    (sortedOf_nodup H lambda) (sortedOf_toFinset H lambda)
    (sortedOf_sorted H lambda) hpos

/-! ## Basic prefix/suffix facts.

`Rset ∪ geSet = H` and `Rset` is disjoint from `geSet` (prefix vs suffix of the
same nodup list). -/

/-- `Rset` is a subset of `H`. -/
lemma Rset_subset (W H : Finset X) (lambda : X → ℝ) :
    Rset W H lambda ⊆ H := by
  unfold Rset
  intro x hx
  rw [List.mem_toFinset] at hx
  have : x ∈ sortedOf H lambda := List.mem_of_mem_take hx
  rw [← sortedOf_toFinset H lambda, List.mem_toFinset]
  exact this

/-- `geSet` is a subset of `H`. -/
lemma geSet_subset (W H : Finset X) (lambda : X → ℝ) :
    geSet W H lambda ⊆ H := by
  unfold geSet
  intro x hx
  rw [List.mem_toFinset] at hx
  have : x ∈ sortedOf H lambda := List.mem_of_mem_drop hx
  rw [← sortedOf_toFinset H lambda, List.mem_toFinset]
  exact this

/-- Prefix and suffix of the same nodup list are disjoint as finsets. -/
lemma take_drop_disjoint (L : List X) (hnd : L.Nodup) (b : ℕ) :
    Disjoint (L.take b).toFinset (L.drop b).toFinset := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [List.mem_toFinset] at hx hx'
  -- `L = L.take b ++ L.drop b`; nodup of the append forbids a shared element.
  have hsplit : L = L.take b ++ L.drop b := (List.take_append_drop b L).symm
  have hnd' : ((L.take b) ++ (L.drop b)).Nodup := hsplit ▸ hnd
  exact (List.nodup_append.mp hnd').2.2 x hx x hx' rfl

/-- `Rset` (the cutoff prefix) is disjoint from `geSet` (the cutoff suffix). -/
lemma Rset_disjoint_geSet (W H : Finset X) (lambda : X → ℝ) :
    Disjoint (Rset W H lambda) (geSet W H lambda) := by
  unfold Rset geSet
  exact take_drop_disjoint (sortedOf H lambda) (sortedOf_nodup H lambda) _

/-! ## The iteration `H₁ = H`, `Hᵢ₊₁ = (Hᵢ)_{≥ bᵢ} ∖ Wᵢ`.

We use `W : ℕ → Finset X` for the family of subsets (the paper's tuple `W`).
`Hstep 0 = H` and `Hstep (i+1) = (Hstep i)_{≥} ∖ (W i)`. -/

/-- The iterated finset `Hᵢ`: `Hstep 0 = H`, `Hstep (i+1) = (Hstep i)_{≥} ∖ Wᵢ`. -/
noncomputable def Hstep (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ) :
    ℕ → Finset X
  | 0 => H
  | (i + 1) => geSet (W i) (Hstep W H lambda i) lambda \ (W i)

/-- The cutoff prefix at step `i`: `Rstep i = (Hᵢ)_{< bᵢ}` (the paper's `R_{i+1}`
under the indexing note above). -/
noncomputable def Rstep (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (i : ℕ) : Finset X :=
  Rset (W i) (Hstep W H lambda i) lambda

@[simp] lemma Hstep_zero (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ) :
    Hstep W H lambda 0 = H := rfl

@[simp] lemma Hstep_succ (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (i : ℕ) :
    Hstep W H lambda (i + 1)
      = geSet (W i) (Hstep W H lambda i) lambda \ (W i) := rfl

/-! ## Monotonicity of the iteration. -/

/-- One step shrinks: `Hᵢ₊₁ ⊆ (Hᵢ)_{≥}`. -/
lemma Hstep_succ_subset_geSet (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (i : ℕ) :
    Hstep W H lambda (i + 1) ⊆ geSet (W i) (Hstep W H lambda i) lambda := by
  rw [Hstep_succ]; exact Finset.sdiff_subset

/-- The suffix at step `i` sits inside `Hᵢ`. -/
lemma geSet_step_subset (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (i : ℕ) :
    geSet (W i) (Hstep W H lambda i) lambda ⊆ Hstep W H lambda i :=
  geSet_subset _ _ _

/-- One step shrinks all the way: `Hᵢ₊₁ ⊆ Hᵢ`. -/
lemma Hstep_succ_subset (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (i : ℕ) :
    Hstep W H lambda (i + 1) ⊆ Hstep W H lambda i :=
  Finset.Subset.trans (Hstep_succ_subset_geSet W H lambda i)
    (geSet_step_subset W H lambda i)

/-- Monotone decreasing: for `i ≤ j`, `Hⱼ ⊆ Hᵢ`. -/
lemma Hstep_antitone (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    {i j : ℕ} (hij : i ≤ j) :
    Hstep W H lambda j ⊆ Hstep W H lambda i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.mp hij
    exact subset_rfl
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with hlt | heq
    · -- i ≤ k
      have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
      exact Finset.Subset.trans (Hstep_succ_subset W H lambda k) (ih hik)
    · -- i = k + 1
      subst heq; exact subset_rfl

/-- For `i < j`, `Hⱼ ⊆ (Hᵢ)_{≥}` (the suffix at the earlier step contains every
later iterate). -/
lemma Hstep_lt_subset_geSet (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    {i j : ℕ} (hij : i < j) :
    Hstep W H lambda j ⊆ geSet (W i) (Hstep W H lambda i) lambda := by
  -- `i + 1 ≤ j`, so `Hⱼ ⊆ Hᵢ₊₁ ⊆ (Hᵢ)_{≥}`.
  have h1 : Hstep W H lambda j ⊆ Hstep W H lambda (i + 1) :=
    Hstep_antitone W H lambda hij
  exact Finset.Subset.trans h1 (Hstep_succ_subset_geSet W H lambda i)

/-! ## The `Rstep` are subsets of the corresponding iterate. -/

/-- `Rstep i ⊆ Hᵢ`. -/
lemma Rstep_subset_Hstep (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    (i : ℕ) :
    Rstep W H lambda i ⊆ Hstep W H lambda i :=
  Rset_subset _ _ _

/-! ## Main result: the cutoff prefixes `Rᵢ` are pairwise disjoint. -/

/-- For `i < j`: `Rⱼ` is disjoint from `Rᵢ`.

`Rⱼ ⊆ Hⱼ ⊆ (Hᵢ)_{≥ bᵢ}` (monotonicity, since `i < j`), while `Rᵢ = (Hᵢ)_{< bᵢ}`
is disjoint from `(Hᵢ)_{≥ bᵢ}` (prefix vs suffix of the same nodup list).  Hence
`Rᵢ ∩ Rⱼ = ∅`. -/
lemma Rstep_disjoint_of_lt (W : ℕ → Finset X) (H : Finset X) (lambda : X → ℝ)
    {i j : ℕ} (hij : i < j) :
    Disjoint (Rstep W H lambda i) (Rstep W H lambda j) := by
  -- `Rⱼ ⊆ (Hᵢ)_{≥}`.
  have hRj : Rstep W H lambda j ⊆ geSet (W i) (Hstep W H lambda i) lambda :=
    Finset.Subset.trans (Rstep_subset_Hstep W H lambda j)
      (Hstep_lt_subset_geSet W H lambda hij)
  -- `Rᵢ` disjoint from `(Hᵢ)_{≥}`.
  have hdisj : Disjoint (Rstep W H lambda i)
      (geSet (W i) (Hstep W H lambda i) lambda) :=
    Rset_disjoint_geSet (W i) (Hstep W H lambda i) lambda
  exact Finset.disjoint_of_subset_right hRj hdisj

/-- **Key structural fact (§3.2): the cutoff prefixes `Rᵢ(W,H)` are pairwise
disjoint.** -/
theorem Rstep_pairwise_disjoint (W : ℕ → Finset X) (H : Finset X)
    (lambda : X → ℝ) :
    ∀ i j, i ≠ j → Disjoint (Rstep W H lambda i) (Rstep W H lambda j) := by
  intro i j hij
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact Rstep_disjoint_of_lt W H lambda hlt
  · have hgt : j < i := lt_of_le_of_ne hge (by exact fun h => hij h.symm)
    exact (Rstep_disjoint_of_lt W H lambda hgt).symm

end Workspace.Encoding.Procedure
