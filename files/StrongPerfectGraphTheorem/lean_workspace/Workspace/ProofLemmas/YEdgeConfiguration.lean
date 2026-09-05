import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OptimalWheelChoice

/-!
# `Y`-complete edges versus `Y`-complete positions, and the parity of a run

Two bridges that every §§16–23 argument about the rim needs, and that neither `WheelParity`
(which counts *edges*) nor `SegmentBasics` (which handles *runs of vertices*) provides on its
own, because each is stated on only one side of the correspondence

  a `Y`-complete **edge** at cyclic position `m`  ⟷  positions `m` and `m+1` are both
  `Y`-complete **vertices**.

* `cycEdge_iff` is that correspondence.  The `←` direction is the one with content: it needs
  the adjacency of two cyclically consecutive vertices of a hole, which is where `IsHoleList`
  enters.  With it, every edge-count statement (`WheelParity.cycCount`,
  `OptimalWheelChoice.yEdgeCount`) can be converted into a statement about runs of
  `Y`-complete positions, and back.

* `run_odd_of_not_isOddWheel` is the reading of *"`(C,Y)` is not an odd wheel"* that the
  proofs actually use.  `Workspace.Types.Wheels.IsOddWheel` says *some segment has odd
  length*; combined with `SegmentBasics.isSegment_of_run` (which turns a maximal run into a
  genuine `IsSegment`, maximality clause and all) and
  `SegmentBasics.odd_pathLength_iff_even_length` (*"an odd segment has an even number of
  vertices"*), the negation says precisely:

  > **every maximal run of `Y`-complete positions has odd length.**

  That is the hypothesis the printed proof of 23.2 uses when it writes *"Since `(C,Y)` is not
  an odd wheel, there are vertices `x₀, z, x₁, c₁, c₂, c₃` of `C`, in order, … such that the
  `Y`-complete edges in `C` are `x₀z, zx₁, c₁c₂, c₂c₃"* — a run of odd length `L` carries
  `L − 1` (hence an even number of) `Y`-complete edges, so four such edges must split as
  `4` (one run of five vertices) or `2 + 2` (two runs of three).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.YEdgeConfiguration

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.WheelParity
open Workspace.ProofLemmas.SegmentBasics

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### Edges versus positions -/

/-- Two cyclically consecutive positions of a hole carry adjacent vertices. -/
theorem adj_of_succ_pos (hC : IsHoleList G C) (hn : 0 < C.length) (m : ℕ) :
    G.Adj (C[m % C.length]'(Nat.mod_lt _ hn)) (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) := by
  refine (HoleBasics.hole_adj_iff hC (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)).mpr (Or.inl ?_)
  rw [Nat.mod_add_mod]

/-- **The bridge.**  The cyclic edge `eₘ` of the rim is `Y`-complete exactly when both of its
ends — the vertices at cyclic positions `m` and `m+1` — are `Y`-complete. -/
theorem cycEdge_iff (hC : IsHoleList G C) {m : ℕ} :
    CycEdge G Y C m ↔ (CycVert G Y C m ∧ CycVert G Y C (m + 1)) := by
  have hn : 0 < C.length := by have := hC.1; omega
  constructor
  · rintro ⟨u, v, hu, hv, hadj, hcu, hcv⟩
    exact ⟨⟨u, hu, hcu⟩, ⟨v, hv, hcv⟩⟩
  · rintro ⟨⟨u, hu, hcu⟩, ⟨v, hv, hcv⟩⟩
    refine ⟨u, v, hu, hv, ?_, hcu, hcv⟩
    have hue : (C[m % C.length]'(Nat.mod_lt _ hn)) = u := by
      rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hu
      exact Option.some_inj.mp hu
    have hve : (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) = v := by
      rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hv
      exact Option.some_inj.mp hv
    rw [← hue, ← hve]
    exact adj_of_succ_pos hC hn m

/-- A `Y`-complete edge gives a `Y`-complete vertex at its first end. -/
theorem cycVert_of_cycEdge (hC : IsHoleList G C) {m : ℕ} (h : CycEdge G Y C m) :
    CycVert G Y C m := ((cycEdge_iff hC).mp h).1

/-- A `Y`-complete edge gives a `Y`-complete vertex at its second end. -/
theorem cycVert_succ_of_cycEdge (hC : IsHoleList G C) {m : ℕ} (h : CycEdge G Y C m) :
    CycVert G Y C (m + 1) := ((cycEdge_iff hC).mp h).2

/-! ### The parity of a maximal run -/

/-- **Every maximal run of `Y`-complete positions of the rim of a wheel that is not an odd
wheel has odd length.**

This is the working form of *"`(C,Y)` is not an odd wheel"*: `SegmentBasics.isSegment_of_run`
promotes the run to a genuine `Y`-segment, and an odd segment is one with an **even** number
of vertices, so `IsOddWheel` fails exactly when no run has even length. -/
theorem run_odd_of_not_isOddWheel (hC : IsHoleList G C)
    (hw : IsWheel G C Y) (hno : ¬ IsOddWheel G C Y)
    {k L : ℕ} (h1 : 1 ≤ L) (h2 : L + 1 ≤ C.length)
    (hall : ∀ t < L, CycVert G Y C (k + t))
    (hnext : ¬ CycVert G Y C (k + L))
    (hprev : ¬ CycVert G Y C (k + (C.length - 1))) :
    ¬ Even L := by
  intro hev
  have hlen : ((C.rotate k).take L).length = L := by
    simp only [List.length_take, List.length_rotate]
    omega
  refine hno ⟨hw, (C.rotate k).take L, isSegment_of_run hC h1 h2 hall hnext hprev, ?_⟩
  rw [odd_pathLength_iff_even_length (by rw [hlen]; exact h1), hlen]
  exact hev

/-- The same fact stated positively: a maximal run has odd length, so `L = 2 * j + 1`. -/
theorem run_odd' (hC : IsHoleList G C)
    (hw : IsWheel G C Y) (hno : ¬ IsOddWheel G C Y)
    {k L : ℕ} (h1 : 1 ≤ L) (h2 : L + 1 ≤ C.length)
    (hall : ∀ t < L, CycVert G Y C (k + t))
    (hnext : ¬ CycVert G Y C (k + L))
    (hprev : ¬ CycVert G Y C (k + (C.length - 1))) :
    L % 2 = 1 := by
  have := run_odd_of_not_isOddWheel hC hw hno h1 h2 hall hnext hprev
  rw [Nat.even_iff] at this
  omega

/-- The maximal run through a `Y`-complete position of the rim, with its odd length recorded.
This is the packaged form the classification argument consumes: it combines
`SegmentBasics.exists_run_of_cycVert` with `run_odd'`. -/
theorem exists_odd_run (hC : IsHoleList G C) (hw : IsWheel G C Y) (hno : ¬ IsOddWheel G C Y)
    {i j : ℕ} (hi : CycVert G Y C i) (hj : ¬ CycVert G Y C j) :
    ∃ (k L : ℕ), 1 ≤ L ∧ L + 1 ≤ C.length ∧ L % 2 = 1 ∧
      (∀ t < L, CycVert G Y C (k + t)) ∧
      ¬ CycVert G Y C (k + L) ∧ ¬ CycVert G Y C (k + (C.length - 1)) ∧
      (∃ t < L, (k + t) % C.length = i % C.length) := by
  obtain ⟨k, L, h1, h2, hall, hnext, hprev, hcov⟩ := exists_run_of_cycVert hC hi hj
  exact ⟨k, L, h1, h2, run_odd' hC hw hno h1 h2 hall hnext hprev, hall, hnext, hprev, hcov⟩

/-- A run of `Y`-complete positions of length `L` carries a `Y`-complete edge at each of its
first `L - 1` positions. -/
theorem cycEdge_of_run (hC : IsHoleList G C) {k L : ℕ}
    (hall : ∀ t < L, CycVert G Y C (k + t)) {t : ℕ} (ht : t + 1 < L) :
    CycEdge G Y C (k + t) := by
  refine (cycEdge_iff hC).mpr ⟨hall t (by omega), ?_⟩
  have e : k + t + 1 = k + (t + 1) := by omega
  rw [e]
  exact hall (t + 1) ht

/-- Conversely, the position just past the end of a maximal run carries no `Y`-complete
edge, and neither does the position just before its start. -/
theorem not_cycEdge_at_run_end (hC : IsHoleList G C) {k L : ℕ}
    (hnext : ¬ CycVert G Y C (k + L)) : ¬ CycEdge G Y C (k + L) :=
  fun h => hnext (cycVert_of_cycEdge hC h)

end Workspace.ProofLemmas.YEdgeConfiguration
