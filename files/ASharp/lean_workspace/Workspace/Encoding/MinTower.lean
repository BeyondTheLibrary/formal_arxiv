import Workspace.Encoding.TowerFrag

open BigOperators
open Classical

namespace Workspace.Encoding.MinTower

/-! # Section 3.2 — the minimum tower of fragments.

**Source**: `@../arXiv-2412.03540v1.tex`, Section 3.2, Definition "Towers of
minimum fragments" (the paragraph defining `T(W,H)`).

Given `W = (W₁,…,W_s)` and `H ∈ ℋ`, the paper defines the **minimum tower of
fragments** `T(W,H)` as the tower of fragments of `(W,H)` whose size vector
`(|T₁|,…,|T_s|)` is *lexicographically minimal* among all towers of fragments of
`(W,H)` with `⋃ᵢ Tᵢ ⊆ H`.

This file builds on `Workspace.Encoding.TowerFrag` (Def 3.3/3.4 + Lemma 3.5):
- `TFeasible`, `IsTowerOfFragments`, and `exists_tower_of_fragments`.

Both `TFeasible` and `IsTowerOfFragments` only quantify over indices `i < s`, so
a tower of fragments is determined (as far as those predicates can see) by its
values on `Fin s`. We exploit this: we range over the *finite* set of tuples
`Fin s → Finset X` whose entries are subsets of `H` and that (after the
canonical `extend` back to `ℕ → Finset X`) are towers of fragments, take the
lexicographically minimal size vector among them via a finite argmin, and
`extend` the minimizer back to `ℕ → Finset X` to obtain `minTower`.

The paper's lexicographic order on `ℤ^s` ( `x ⪯ y` iff `x = y` or there is `i`
with `xᵢ < yᵢ` and `xⱼ = yⱼ` for `j < i` ) is exactly Mathlib's `Pi.Lex` order on
`Lex (Fin s → ℕ)` (`Fin s` is a finite well-order, `ℕ` is linearly ordered), so
`sizeVec` lands in `Lex (Fin s → ℕ)` and the minimum is its `LinearOrder`
minimum. -/

variable {X : Type} [Fintype X] [DecidableEq X]

open Workspace.Encoding.TowerFrag
open Workspace.Encoding.Procedure

/-! ## Canonical extend / restrict between `Fin s → Finset X` and `ℕ → Finset X`. -/

/-- Extend a tuple indexed by `Fin s` to a family indexed by `ℕ`, with `∅`
outside the range `[0, s)`. The predicates `TFeasible`/`IsTowerOfFragments` only
read indices `< s`, so this canonical extension loses no information they can
observe. -/
def extend (s : ℕ) (T : Fin s → Finset X) : ℕ → Finset X :=
  fun i => if h : i < s then T ⟨i, h⟩ else ∅

@[simp] lemma extend_apply_lt (s : ℕ) (T : Fin s → Finset X) {i : ℕ} (h : i < s) :
    extend s T i = T ⟨i, h⟩ := by
  unfold extend; rw [dif_pos h]

/-- `extend` of the restriction of `T` to `Fin s` agrees with `T` on every
index `< s`. -/
lemma extend_restrict_apply (s : ℕ) (T : ℕ → Finset X) {i : ℕ} (h : i < s) :
    extend s (fun j : Fin s => T j.val) i = T i := by
  rw [extend_apply_lt s _ h]

/-! ## `IsTowerOfFragments` only depends on indices `< s`. -/

/-- `TFeasible` only reads indices `< s` of `Z` and `t`: if two pairs `(Z,t)` and
`(Z',t')` agree on `[0,s)` then the `TFeasible` predicate is the same. -/
lemma tFeasible_congr {ℋ : Set (Finset X)} {s : ℕ}
    {lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ}
    {Z Z' : ℕ → Finset X} {t t' : ℕ → ℕ}
    (hZ : ∀ i, i < s → Z i = Z' i) (ht : ∀ i, i < s → t i = t' i) :
    TFeasible ℋ s lambda_vec Z t ↔ TFeasible ℋ s lambda_vec Z' t' := by
  unfold TFeasible
  constructor
  · rintro ⟨W', H, hH, hsub, hR⟩
    refine ⟨W', H, hH, ?_, ?_⟩
    · intro i hi
      obtain ⟨h1, h2⟩ := hsub i hi
      rw [← hZ i hi, ← ht i hi]
      exact ⟨h1, h2⟩
    · intro i hi
      rw [← hZ i hi]
      exact hR i hi
  · rintro ⟨W', H, hH, hsub, hR⟩
    refine ⟨W', H, hH, ?_, ?_⟩
    · intro i hi
      obtain ⟨h1, h2⟩ := hsub i hi
      rw [hZ i hi, ht i hi]
      exact ⟨h1, h2⟩
    · intro i hi
      rw [hZ i hi]
      exact hR i hi

/-- `IsTowerOfFragments` only reads indices `< s` of `T`: if two families `T`,
`T'` agree on `[0,s)` then the `IsTowerOfFragments` predicate is the same. -/
lemma isTower_congr {ℋ : Set (Finset X)} {s : ℕ}
    {lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ}
    {W : ℕ → Finset X} {H : Finset X} {T T' : ℕ → Finset X}
    (hT : ∀ i, i < s → T i = T' i) :
    IsTowerOfFragments ℋ s lambda_vec W H T ↔
      IsTowerOfFragments ℋ s lambda_vec W H T' := by
  unfold IsTowerOfFragments
  have hZ : ∀ i, i < s → (T i ∪ W i) = (T' i ∪ W i) := by
    intro i hi; rw [hT i hi]
  have ht : ∀ i, i < s → (T i).card = (T' i).card := by
    intro i hi; rw [hT i hi]
  rw [tFeasible_congr (s := s) (lambda_vec := lambda_vec) hZ ht]
  constructor
  · rintro ⟨hfeas, hcont, hdisj⟩
    refine ⟨hfeas, ?_, ?_⟩
    · intro i hi; rw [← hT i hi]; exact hcont i hi
    · intro i hi; rw [← hT i hi]; exact hdisj i hi
  · rintro ⟨hfeas, hcont, hdisj⟩
    refine ⟨hfeas, ?_, ?_⟩
    · intro i hi; rw [hT i hi]; exact hcont i hi
    · intro i hi; rw [hT i hi]; exact hdisj i hi

/-- **Invariance lemma (task item 1).** For any `T : ℕ → Finset X`, being a tower
of fragments is unchanged by restricting `T` to `Fin s` and re-extending with
`extend`: both sides only read indices `< s`, where `extend (T ∘ Fin.val)`
agrees with `T`. -/
theorem isTower_iff_extend_restrict {ℋ : Set (Finset X)} {s : ℕ}
    {lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ}
    {W : ℕ → Finset X} {H : Finset X} (T : ℕ → Finset X) :
    IsTowerOfFragments ℋ s lambda_vec W H T ↔
      IsTowerOfFragments ℋ s lambda_vec W H (extend s (fun i : Fin s => T i.val)) := by
  apply isTower_congr
  intro i hi
  rw [extend_restrict_apply s T hi]

/-! ## The finite set of tower-tuples. -/

variable (ℋ : Set (Finset X)) (s : ℕ)
  (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ) (W : ℕ → Finset X)
  (H : Finset X)

/-- The finite set of tower-tuples: tuples `T : Fin s → Finset X` whose every
entry is a subset of `H` and whose `extend` is a tower of fragments of `(W,H)`.
Filtering uses `Classical.dec` for the (undecidable) `IsTowerOfFragments`
predicate, which is fine under `open Classical`. -/
noncomputable def towerTuples : Finset (Fin s → Finset X) :=
  (Fintype.piFinset (fun _ => H.powerset)).filter
    (fun T => IsTowerOfFragments ℋ s lambda_vec W H (extend s T))

lemma mem_towerTuples {T : Fin s → Finset X} :
    T ∈ towerTuples ℋ s lambda_vec W H ↔
      (∀ i : Fin s, T i ⊆ H) ∧
        IsTowerOfFragments ℋ s lambda_vec W H (extend s T) := by
  unfold towerTuples
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hpow, htow⟩
    refine ⟨fun i => ?_, htow⟩
    have := hpow i
    rwa [Finset.mem_powerset] at this
  · rintro ⟨hsub, htow⟩
    refine ⟨fun i => ?_, htow⟩
    rw [Finset.mem_powerset]; exact hsub i

/-- `towerTuples` is nonempty: the restriction to `Fin s` of Lemma 3.5's witness
`fun i => Rstep W H lambda i \ W i` is a tower-tuple — each value is `⊆ H`, and
its `extend` is a tower of fragments by the invariance lemma. -/
theorem towerTuples_nonempty (hH : H ∈ ℋ) :
    (towerTuples ℋ s lambda_vec W H).Nonempty := by
  -- The candidate restricted tuple (using the witness `H`'s own weight `λ_H`).
  refine ⟨fun i : Fin s => Rstep W H (lambda_vec H hH) i.val \ W i.val, ?_⟩
  rw [mem_towerTuples]
  refine ⟨?_, ?_⟩
  · -- each value is `⊆ H`
    intro i
    have h1 : Rstep W H (lambda_vec H hH) i.val \ W i.val
        ⊆ Rstep W H (lambda_vec H hH) i.val :=
      Finset.sdiff_subset
    have h2 : Rstep W H (lambda_vec H hH) i.val ⊆ Hstep W H (lambda_vec H hH) i.val :=
      Rstep_subset_Hstep W H (lambda_vec H hH) i.val
    have h3 : Hstep W H (lambda_vec H hH) i.val ⊆ Hstep W H (lambda_vec H hH) 0 :=
      Hstep_antitone W H (lambda_vec H hH) (Nat.zero_le i.val)
    have h4 : Hstep W H (lambda_vec H hH) 0 = H := rfl
    exact (h1.trans h2).trans (h3.trans (le_of_eq h4))
  · -- its `extend` is a tower of fragments, by the invariance lemma applied to
    -- Lemma 3.5's full witness `fun i => Rstep W H (lambda_vec H hH) i \ W i`.
    have hbase : IsTowerOfFragments ℋ s lambda_vec W H
        (fun i => Rstep W H (lambda_vec H hH) i \ W i) :=
      exists_tower_of_fragments W H hH
    -- rewrite the base witness through the invariance lemma to the extended
    -- restriction of itself.
    rw [isTower_iff_extend_restrict (fun i => Rstep W H (lambda_vec H hH) i \ W i)]
      at hbase
    exact hbase

/-! ## The lex size order. -/

/-- The size vector of a tuple, as an element of `Lex (Fin s → ℕ)`. The
lexicographic `LinearOrder` on `Lex (Fin s → ℕ)` (Mathlib `Pi.Lex.linearOrder`,
since `Fin s` is a finite well-order and `ℕ` is linearly ordered) is exactly the
paper's `⪯` on `ℤ^s` restricted to size vectors. -/
def sizeVec (s : ℕ) (T : Fin s → Finset X) : Lex (Fin s → ℕ) :=
  toLex (fun i => (T i).card)

/-! ## The minimum tuple via finite argmin over `towerTuples`. -/

/-- A lex-minimal tower-tuple exists (finite argmin over `towerTuples`). -/
theorem exists_min_towerTuple (hH : H ∈ ℋ) :
    ∃ T₀ ∈ towerTuples ℋ s lambda_vec W H,
      ∀ T ∈ towerTuples ℋ s lambda_vec W H,
        sizeVec s T₀ ≤ sizeVec s T :=
  Finset.exists_min_image (towerTuples ℋ s lambda_vec W H) (sizeVec s)
    (towerTuples_nonempty ℋ s lambda_vec W H hH)

/-- The chosen lex-minimal tower-tuple. -/
noncomputable def minTuple (hH : H ∈ ℋ) : Fin s → Finset X :=
  Classical.choose (exists_min_towerTuple ℋ s lambda_vec W H hH)

lemma minTuple_spec (hH : H ∈ ℋ) :
    minTuple ℋ s lambda_vec W H hH ∈ towerTuples ℋ s lambda_vec W H ∧
      ∀ T ∈ towerTuples ℋ s lambda_vec W H,
        sizeVec s (minTuple ℋ s lambda_vec W H hH) ≤ sizeVec s T :=
  Classical.choose_spec (exists_min_towerTuple ℋ s lambda_vec W H hH)

/-- **The minimum tower of fragments** `T(W,H)`: extend the lex-minimal
tower-tuple back to a family indexed by `ℕ`. -/
noncomputable def minTower (hH : H ∈ ℋ) : ℕ → Finset X :=
  extend s (minTuple ℋ s lambda_vec W H hH)

/-! ## Exported interface (Lemma 3.6 / node 4b). -/

/-- **`minTower` is a tower of fragments** of `(W,H)`. -/
theorem minTower_isTower (hH : H ∈ ℋ) :
    IsTowerOfFragments ℋ s lambda_vec W H (minTower ℋ s lambda_vec W H hH) := by
  unfold minTower
  exact (mem_towerTuples ℋ s lambda_vec W H).mp (minTuple_spec ℋ s lambda_vec W H hH).1 |>.2

/-- **`minTower` is lexicographically minimal**: for every tower of fragments
`T'` of `(W,H)`, the size vector of `minTower` is `≤` the size vector of `T'` in
the lex order on `Lex (Fin s → ℕ)`. This is the paper's defining property of the
minimum tower of fragments. -/
theorem minTower_lex_le (hH : H ∈ ℋ) :
    ∀ T' : ℕ → Finset X, IsTowerOfFragments ℋ s lambda_vec W H T' →
      (toLex (fun i : Fin s => (minTower ℋ s lambda_vec W H hH i.val).card)
        : Lex (Fin s → ℕ)) ≤ toLex (fun i : Fin s => (T' i.val).card) := by
  intro T' hT'
  -- The tuple of `T'` restricted to `Fin s`.
  set Tt : Fin s → Finset X := fun i : Fin s => T' i.val with hTt
  -- `Tt ∈ towerTuples`: every value `⊆ H` (from containment) and its `extend`
  -- is a tower (by the invariance lemma applied to `T'`).
  have hmem : Tt ∈ towerTuples ℋ s lambda_vec W H := by
    rw [mem_towerTuples]
    refine ⟨?_, ?_⟩
    · -- each `Tt i = T' i ⊆ H`, from the containment part of `IsTowerOfFragments`.
      intro i
      have hcont := hT'.2.1 i.val i.isLt
      simpa [hTt] using hcont
    · -- `extend Tt` is a tower of fragments: this is exactly the invariance lemma
      -- applied to `T'`.
      have := (isTower_iff_extend_restrict (ℋ := ℋ) (s := s) (lambda_vec := lambda_vec)
        (W := W) (H := H) T').mp hT'
      simpa [hTt] using this
  -- Apply the argmin bound.
  have hle := (minTuple_spec ℋ s lambda_vec W H hH).2 Tt hmem
  -- Unfold `sizeVec`, `minTower`, `minTuple` to match the goal.
  -- `sizeVec s (minTuple ...) = toLex (fun i => (minTuple ... i).card)`.
  -- `minTower ... i.val = extend s (minTuple ...) i.val = minTuple ... i` (i.val < s).
  have hmin_eq : (fun i : Fin s => (minTower ℋ s lambda_vec W H hH i.val).card)
      = (fun i : Fin s => (minTuple ℋ s lambda_vec W H hH i).card) := by
    funext i
    unfold minTower
    rw [extend_apply_lt s _ i.isLt]
  rw [hmin_eq]
  -- Now both sides equal `sizeVec` images.
  show (sizeVec s (minTuple ℋ s lambda_vec W H hH) : Lex (Fin s → ℕ)) ≤ sizeVec s Tt
  exact hle

end Workspace.Encoding.MinTower
