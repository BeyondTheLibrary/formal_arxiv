import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Workspace.Encoding.MinTower
import Workspace.Types.IsPSmall

open BigOperators
open Classical

namespace Workspace.Definitions.CoverCollection

/-! # Genuine min-tower cover collection from §3.2.

This file packages the *cover collection* `𝒰(W)` of paper §3.2, GROUNDED in the
genuine **minimum tower of fragments** (`Workspace.Encoding.MinTower.minTower`)
rather than a loose existential.  For a sample family `W : Fin s → Finset X` and
each `H ∈ ℋ`, the genuine cover element is

  `U(W,H) := ⋃_{i<s} minTower ℋ s λ (extend W) H hH i`,

i.e. the union of the fragments of the minimum tower of `(W,H)` (the paper's
`u`-set whose size is the total tower size).  The collection retains the
`1 ≤ |U|` filter (a genuine cover element is non-empty when `W` is *bad*, by
Lemma 3.8 `bad_implies_nonempty_tower`).

Grounding membership in the minimum tower is exactly what excludes the spurious
non-minimal elements that made the earlier loose definition unsound.

**Source**: `@../arXiv-2412.03540v1.tex`, Section 3.2 (towers of minimum
fragments).
-/

variable {X : Type} [Fintype X] [DecidableEq X]

open Workspace.Encoding.MinTower

/-- Lift a `Fin s`-indexed sample to a family indexed by `ℕ` (`∅` outside range).
This is `Workspace.Encoding.MinTower.extend`, re-exported for the cover. -/
noncomputable def liftW (s : ℕ) (W : Fin s → Finset X) : ℕ → Finset X :=
  Workspace.Encoding.MinTower.extend s W

@[simp] lemma liftW_apply_lt (s : ℕ) (W : Fin s → Finset X) {i : ℕ} (h : i < s) :
    liftW s W i = W ⟨i, h⟩ :=
  Workspace.Encoding.MinTower.extend_apply_lt s W h

/-- The genuine cover element of `(W, H)`: the biUnion of the fragments of the
minimum tower of `(liftW W, H)`. -/
noncomputable def genuineU
    (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (W : Fin s → Finset X) (H : Finset X) (hH : H ∈ ℋ) : Finset X :=
  (Finset.range s).biUnion (minTower ℋ s lambda_vec (liftW s W) H hH)

/-- **The genuine cover collection `𝒰(W)`** (paper §3.2): the non-empty
genuine min-tower cover elements `U(W,H)` over `H ∈ ℋ`. -/
noncomputable def coverCollection
    (ℋ : Set (Finset X)) (s : ℕ)
    (lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ)
    (W : Fin s → Finset X) : Finset (Finset X) :=
  (Finset.univ : Finset (Finset X)).filter
    (fun U => 1 ≤ U.card ∧ ∃ H : Finset X, ∃ hH : H ∈ ℋ,
      U = genuineU ℋ s lambda_vec W H hH)

lemma mem_coverCollection
    {ℋ : Set (Finset X)} {s : ℕ}
    {lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ}
    {W : Fin s → Finset X} {U : Finset X} :
    U ∈ coverCollection ℋ s lambda_vec W ↔
      1 ≤ U.card ∧ ∃ H : Finset X, ∃ hH : H ∈ ℋ,
        U = genuineU ℋ s lambda_vec W H hH := by
  unfold coverCollection
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Membership in `coverCollection` implies non-empty `U`. -/
lemma coverCollection_card_pos
    {ℋ : Set (Finset X)} {s : ℕ}
    {lambda_vec : (H : Finset X) → H ∈ ℋ → X → ℝ}
    {W : Fin s → Finset X} {U : Finset X}
    (hU : U ∈ coverCollection ℋ s lambda_vec W) :
    1 ≤ U.card :=
  (mem_coverCollection.mp hU).1

end Workspace.Definitions.CoverCollection
