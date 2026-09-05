import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm175Minimal

/-!
# The optimal-counterexample choice in 17.5

The proof of 17.5 starts by choosing a counterexample in three stages: first
minimize the path, then the size of the union of the two anticonnected sets,
and finally the sum of their sizes.  This file carries out that finite choice.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Optimal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Minimal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A full counterexample to 17.5 with the graph and the external vertex held
fixed.  The path data and the even edge count are in `EvenRRConfig`. -/
structure Counterexample (G : SimpleGraph V) (z : V) where
  X : Set V
  Y : Set V
  core : EvenRRConfig G X Y z
  hXa : AnticonnectedSet G X
  hYa : AnticonnectedSet G Y
  hXYa : AnticonnectedSet G (X ∪ Y)
  hz : z ∉ X ∪ Y
  hzXY : VertexComplete G z (X ∪ Y)

/-- The three lexicographic minimality clauses called the optimality of
`P,X,Y` in the paper.  Cardinal minimality is enough for every proper-subset
comparison made in the proof because the vertex type is finite. -/
def IsOptimal {G : SimpleGraph V} {z : V} (c : Counterexample G z) : Prop :=
  (∀ d : Counterexample G z, d.core.p.length < c.core.p.length → False) ∧
  (∀ d : Counterexample G z, d.core.p.length = c.core.p.length →
    (d.X ∪ d.Y).ncard < (c.X ∪ c.Y).ncard → False) ∧
  (∀ d : Counterexample G z, d.core.p.length = c.core.p.length →
    (d.X ∪ d.Y).ncard = (c.X ∪ c.Y).ncard →
    d.X.ncard + d.Y.ncard < c.X.ncard + c.Y.ncard → False)

/-- A counterexample has an optimal representative in the order used in the
first paragraph of the proof of 17.5. -/
theorem exists_optimal {G : SimpleGraph V} {z : V}
    (c₀ : Counterexample G z) :
    ∃ c : Counterexample G z, IsOptimal c := by
  classical
  let HasPathLength : ℕ → Prop := fun n =>
    ∃ c : Counterexample G z, c.core.p.length = n
  have hexPath : ∃ n, HasPathLength n :=
    ⟨c₀.core.p.length, c₀, rfl⟩
  let pathSize := Nat.find hexPath
  obtain ⟨c₁, hc₁path⟩ := Nat.find_spec hexPath

  let HasUnionSize : ℕ → Prop := fun n =>
    ∃ c : Counterexample G z,
      c.core.p.length = pathSize ∧ (c.X ∪ c.Y).ncard = n
  have hexUnion : ∃ n, HasUnionSize n :=
    ⟨(c₁.X ∪ c₁.Y).ncard, c₁, hc₁path, rfl⟩
  let unionSize := Nat.find hexUnion
  obtain ⟨c₂, hc₂path, hc₂union⟩ := Nat.find_spec hexUnion

  let HasTotalSize : ℕ → Prop := fun n =>
    ∃ c : Counterexample G z,
      c.core.p.length = pathSize ∧
      (c.X ∪ c.Y).ncard = unionSize ∧
      c.X.ncard + c.Y.ncard = n
  have hexTotal : ∃ n, HasTotalSize n :=
    ⟨c₂.X.ncard + c₂.Y.ncard, c₂, hc₂path, hc₂union, rfl⟩
  let totalSize := Nat.find hexTotal
  obtain ⟨c, hcpath, hcunion, hctotal⟩ := Nat.find_spec hexTotal
  refine ⟨c, ?_, ?_, ?_⟩
  · intro d hd
    have hleast : pathSize ≤ d.core.p.length :=
      Nat.find_min' hexPath ⟨d, rfl⟩
    omega
  · intro d hdpath hdunion
    have hdpath' : d.core.p.length = pathSize := hdpath.trans hcpath
    have hleast : unionSize ≤ (d.X ∪ d.Y).ncard :=
      Nat.find_min' hexUnion ⟨d, hdpath', rfl⟩
    omega
  · intro d hdpath hdunion hdtotal
    have hdpath' : d.core.p.length = pathSize := hdpath.trans hcpath
    have hdunion' : (d.X ∪ d.Y).ncard = unionSize := hdunion.trans hcunion
    have hleast : totalSize ≤ d.X.ncard + d.Y.ncard :=
      Nat.find_min' hexTotal ⟨d, hdpath', hdunion', rfl⟩
    omega

/-- Printed claim (1) for the globally optimal counterexample: its first path
vertex is its only vertex complete to the first side. -/
theorem first_unique_of_optimal
    (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c) :
    ∀ w ∈ c.core.p, (VertexComplete G w c.X ↔ w = c.core.p₁) := by
  apply shortest_first_unique G hG c.X c.Y c.hXa c.hYa c.hXYa z c.hz c.hzXY c.core
  intro d hd
  let d' : Counterexample G z :=
    { X := c.X
      Y := c.Y
      core := d
      hXa := c.hXa
      hYa := c.hYa
      hXYa := c.hXYa
      hz := c.hz
      hzXY := c.hzXY }
  exact hopt.1 d' hd

end Workspace.ProofLemmas.Thm175Optimal
