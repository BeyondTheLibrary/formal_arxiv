import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# A path between two vertices with interior inside a prescribed connected set

`Workspace.ProofLemmas.InducedPathExtraction.exists_antipath_interior_in` is the paper's
*"let `Q` be an antipath between `u` and `v` with interior in `X`"*.  This module supplies the
**`G`-side twin**, which the paper uses just as often and which is what 24.5's opening move
(*"By 15.2, there is a path `Q` in `G` from `z` to `p₁`, such that none of its internal vertices
is in `X` or is `X`-complete"*) needs:

> if `S` is connected, `u, v ∉ S`, and each of `u, v` has a neighbour in `S`, then there is an
> induced path of `G` from `u` to `v` all of whose interior vertices lie in `S`.

The proof is the same three lines as the antipath version — attach `u` and then `v` to `S` with
`ConnectedSetUnionAttach.connectedSet_union_singleton`, extract an induced path with
`InducedPathExtraction.exists_isPathFrom_of_connected`, and read off the interior with
`PathBasics.mem_interior_iff_of_pathFrom`.  It lives in its own module only because
`InducedPathExtraction` is already promoted and in use by other nodes.

Everything is stated for an arbitrary `G`, so instantiating at `Gᶜ` recovers the antipath form.

No counterpart in the paper; this is infrastructure.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.PathInteriorIn

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- **A path with interior in a prescribed connected set.**  `S` connected, `u` and `v` outside
`S` each with a neighbour in `S`: then some induced path of `G` from `u` to `v` has all its
interior vertices in `S`. -/
theorem exists_path_interior_in {S : Set V} (hS : ConnectedSet G S) {u v : V}
    (huS : u ∉ S) (hvS : v ∉ S)
    (hu : ∃ x ∈ S, G.Adj u x) (hv : ∃ x ∈ S, G.Adj v x) :
    ∃ q : List V, IsPathFrom G q u v ∧ ∀ w ∈ SPGT.interior q, w ∈ S := by
  obtain ⟨a, haS, hua⟩ := hu
  obtain ⟨b, hbS, hvb⟩ := hv
  have h1 : ConnectedSet G (S ∪ {u}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hS ⟨a, haS, hua⟩
  have h2 : ConnectedSet G ((S ∪ {u}) ∪ {v}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton h1 ⟨b, Or.inl hbS, hvb⟩
  have humem : u ∈ (S ∪ {u}) ∪ {v} := Or.inl (Or.inr rfl)
  have hvmem : v ∈ (S ∪ {u}) ∪ {v} := Or.inr rfl
  obtain ⟨q, hq, hqmem⟩ := InducedPathExtraction.exists_isPathFrom_of_connected h2 humem hvmem
  refine ⟨q, hq, ?_⟩
  intro w hw
  rw [PathBasics.mem_interior_iff_of_pathFrom hq] at hw
  obtain ⟨hwq, hwu, hwv⟩ := hw
  rcases hqmem w hwq with h | h
  · rcases h with h | h
    · exact h
    · exact absurd h hwu
  · exact absurd h hwv

/-- The same statement with the interior condition packaged as *"every vertex of the path is
`u`, `v`, or in `S`"*, which is the form most call sites destructure. -/
theorem exists_path_mem_of_interior_in {S : Set V} (hS : ConnectedSet G S) {u v : V}
    (huS : u ∉ S) (hvS : v ∉ S)
    (hu : ∃ x ∈ S, G.Adj u x) (hv : ∃ x ∈ S, G.Adj v x) :
    ∃ q : List V, IsPathFrom G q u v ∧ (∀ w ∈ q, w = u ∨ w = v ∨ w ∈ S) := by
  obtain ⟨q, hq, hint⟩ := exists_path_interior_in hS huS hvS hu hv
  refine ⟨q, hq, ?_⟩
  intro w hw
  by_cases hwu : w = u
  · exact Or.inl hwu
  by_cases hwv : w = v
  · exact Or.inr (Or.inl hwv)
  · exact Or.inr (Or.inr (hint w
      ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hw, hwu, hwv⟩)))

end Workspace.ProofLemmas.PathInteriorIn
