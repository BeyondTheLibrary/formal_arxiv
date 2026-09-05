import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue

/-!
# An induced path inside an induced path is a contiguous slice of it

The paper says this in half a sentence — *"`R*` is a subpath of the even path `P*`"* (2.9,
2.11), *"the slice `p_i-⋯-p_j`"* — and immediately reads index arithmetic off it.  What is
actually true, and what this module proves, is:

> if `I` and `p` are both **induced** paths of the same graph and every vertex of `I` lies on
> `p`, then `I` (or its reverse) is literally the contiguous block `p[r], …, p[r+|I|-1]` of `p`.

The proof is pure index bookkeeping on top of `PathGlue.exists_pos_of_subpath`, which supplies
the position function `f : ℕ → ℕ` sending each index of `I` to its position on `p`:

* consecutive vertices of `I` are adjacent, and `p` is *induced*, so `f` moves by **exactly**
  one at each step (`hstep` below);
* `f` is injective, so the direction of that step cannot change — `const_direction`;
* hence `f t = f 0 + t` throughout, or `f t = f 0 - t` throughout, which are the two
  orientations of the conclusion.

`(p.drop r).take k` is the project's spelling of a slice (see `PathBasics`, "Sub-paths").

None of this corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.SubpathIsSlice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

variable {V : Type*}

/-- Rewriting the index of a `getElem`.  **Use this instead of `rw`**: rewriting an index
equation inside `l[i]'h` gives "motive is not type correct". -/
private theorem getElem_congr_idx {α : Type*} (l : List α) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (h : a = b) : (l[a]'ha) = (l[b]'hb) := by
  subst h; rfl

/-! ## The direction of a unit-step injection is constant -/

/-- **A unit-step injection `[0,n) → ℕ` is monotone or antitone.**  If `f` is injective on
`[0, n)` and every step changes its value by exactly one, then either it increases at every
step or it decreases at every step: the wrong-direction choice at step `t` would give
`f (t+1) = f (t-1)`, contradicting injectivity. -/
private theorem const_direction {f : ℕ → ℕ} {n : ℕ}
    (hinj : ∀ s t, s < n → t < n → f s = f t → s = t)
    (hstep : ∀ t, t + 1 < n → (f t + 1 = f (t + 1) ∨ f (t + 1) + 1 = f t)) :
    (∀ t, t < n → f t = f 0 + t) ∨ (∀ t, t < n → f t + t = f 0) := by
  by_cases hn : n ≤ 1
  · refine Or.inl (fun t ht => ?_)
    have ht0 : t = 0 := by omega
    subst ht0
    omega
  have h1 : 1 < n := by omega
  rcases hstep 0 (by omega) with hc | hc
  · refine Or.inl ?_
    have key : ∀ t, t + 1 < n → (f t = f 0 + t ∧ f (t + 1) = f 0 + (t + 1)) := by
      intro t
      induction t with
      | zero => intro _; exact ⟨by omega, by omega⟩
      | succ m ih =>
        intro hm
        obtain ⟨ha, hb⟩ := ih (by omega)
        refine ⟨hb, ?_⟩
        rcases hstep (m + 1) hm with hd | hd
        · omega
        · exfalso
          have hh : f (m + 1 + 1) = f m := by omega
          have := hinj (m + 1 + 1) m (by omega) (by omega) hh
          omega
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · omega
    · obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
      exact (key m ht).2
  · refine Or.inr ?_
    have key : ∀ t, t + 1 < n → (f t + t = f 0 ∧ f (t + 1) + (t + 1) = f 0) := by
      intro t
      induction t with
      | zero => intro _; exact ⟨by omega, by omega⟩
      | succ m ih =>
        intro hm
        obtain ⟨ha, hb⟩ := ih (by omega)
        refine ⟨hb, ?_⟩
        rcases hstep (m + 1) hm with hd | hd
        · exfalso
          have hh : f (m + 1 + 1) = f m := by omega
          have := hinj (m + 1 + 1) m (by omega) (by omega) hh
          omega
        · omega
    intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · omega
    · obtain ⟨m, rfl⟩ : ∃ m, t = m + 1 := ⟨t - 1, by omega⟩
      exact (key m ht).2

/-! ## The main statement -/

/-- **An induced path all of whose vertices lie on another induced path is a contiguous slice
of it**, in one orientation or the other. -/
theorem exists_slice_of_subpath {G : SimpleGraph V} {p I : List V}
    (hp : IsPathList G p) (hI : IsPathList G I) (hsub : ∀ z ∈ I, z ∈ p) :
    ∃ r : ℕ, r + I.length ≤ p.length ∧
      (I = (p.drop r).take I.length ∨ I.reverse = (p.drop r).take I.length) := by
  obtain ⟨f, hf1, hf2, hinj, hmono⟩ := PathGlue.exists_pos_of_subpath hp hI hsub
  have hIpos : 0 < I.length := PathBasics.path_length_pos hI
  have hstep : ∀ t, t + 1 < I.length → (f t + 1 = f (t + 1) ∨ f (t + 1) + 1 = f t) := by
    intro t ht
    have htlt : t < I.length := by omega
    have hadjI : G.Adj (I[t]'htlt) (I[t + 1]'ht) := PathBasics.path_adj_succ hI ht
    have e1 : (p[f t]'(hf1 t htlt)) = (I[t]'htlt) := hf2 t htlt (hf1 t htlt)
    have e2 : (p[f (t + 1)]'(hf1 (t + 1) ht)) = (I[t + 1]'ht) := hf2 (t + 1) ht (hf1 (t + 1) ht)
    rw [← e1, ← e2] at hadjI
    exact (PathBasics.path_adj_iff hp (hf1 t htlt) (hf1 (t + 1) ht)).mp hadjI
  rcases const_direction hinj hstep with hdir | hdir
  · -- `f` increases: the slice starts at `f 0`
    have hlast := hf1 (I.length - 1) (by omega)
    have hdlast := hdir (I.length - 1) (by omega)
    have hle : f 0 + I.length ≤ p.length := by omega
    have hlen : ((p.drop (f 0)).take I.length).length = I.length := by
      simp only [List.length_take, List.length_drop]; omega
    refine ⟨f 0, hle, Or.inl ?_⟩
    refine List.ext_getElem hlen.symm ?_
    intro t h1 h2
    have hgt : ((p.drop (f 0)).take I.length)[t]'h2 = (p[f 0 + t]'(by omega)) := by
      simp only [List.getElem_take, List.getElem_drop]
    rw [hgt, ← hf2 t h1 (hf1 t h1)]
    exact getElem_congr_idx p _ _ (hdir t h1)
  · -- `f` decreases: the slice starts at `f (|I| - 1)`
    have hlast := hf1 (I.length - 1) (by omega)
    have hfirst := hf1 0 hIpos
    have hdlast := hdir (I.length - 1) (by omega)
    have hd0 := hdir 0 hIpos
    have hle : f (I.length - 1) + I.length ≤ p.length := by omega
    have hlen : ((p.drop (f (I.length - 1))).take I.length).length = I.length := by
      simp only [List.length_take, List.length_drop]; omega
    refine ⟨f (I.length - 1), hle, Or.inr ?_⟩
    refine List.ext_getElem (by simp only [List.length_reverse]; exact hlen.symm) ?_
    intro t h1 h2
    have ht : t < I.length := by simpa using h1
    have hidx : I.length - 1 - t < I.length := by omega
    have hgt : ((p.drop (f (I.length - 1))).take I.length)[t]'h2
        = (p[f (I.length - 1) + t]'(by omega)) := by
      simp only [List.getElem_take, List.getElem_drop]
    have hdt := hdir (I.length - 1 - t) hidx
    simp only [List.getElem_reverse]
    rw [hgt, ← hf2 (I.length - 1 - t) hidx (hf1 _ hidx)]
    exact getElem_congr_idx p _ _ (by omega)

/-! ## Index transfer -/

/-- The index-level form of `exists_slice_of_subpath`: the vertices of `I` are exactly the
`p[k]` with `r ≤ k < r + |I|`.  This is the form the callers actually consume — orientation
is irrelevant to a membership question, so no case split is needed downstream. -/
theorem exists_index_of_subpath {G : SimpleGraph V} {p I : List V}
    (hp : IsPathList G p) (hI : IsPathList G I) (hsub : ∀ z ∈ I, z ∈ p) :
    ∃ r : ℕ, r + I.length ≤ p.length ∧
      (∀ x : V, x ∈ I ↔ ∃ (k : ℕ) (hk : k < p.length), r ≤ k ∧ k < r + I.length ∧
        (p[k]'hk) = x) ∧
      (I = (p.drop r).take I.length ∨ I.reverse = (p.drop r).take I.length) := by
  obtain ⟨r, hle, hor⟩ := exists_slice_of_subpath hp hI hsub
  refine ⟨r, hle, ?_, hor⟩
  intro x
  have hmemslice : x ∈ (p.drop r).take I.length ↔
      ∃ (k : ℕ) (hk : k < p.length), r ≤ k ∧ k < r + I.length ∧ (p[k]'hk) = x := by
    constructor
    · intro hx
      obtain ⟨t, ht, hteq⟩ := List.mem_iff_getElem.mp hx
      have htlen : t < I.length := by
        simp only [List.length_take, List.length_drop] at ht; omega
      refine ⟨r + t, by omega, by omega, by omega, ?_⟩
      rw [← hteq]
      simp only [List.getElem_take, List.getElem_drop]
    · rintro ⟨k, hk, h1, h2, rfl⟩
      refine List.mem_iff_getElem.mpr ⟨k - r, ?_, ?_⟩
      · simp only [List.length_take, List.length_drop]; omega
      · simp only [List.getElem_take, List.getElem_drop]
        exact getElem_congr_idx p _ _ (by omega)
  rcases hor with he | he
  · have hmem : x ∈ I ↔ x ∈ (p.drop r).take I.length := by rw [← he]
    exact hmem.trans hmemslice
  · have hmem : x ∈ I.reverse ↔ x ∈ (p.drop r).take I.length := by rw [← he]
    exact (List.mem_reverse.symm.trans hmem).trans hmemslice

end Workspace.ProofLemmas.SubpathIsSlice
