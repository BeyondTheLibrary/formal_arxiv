import Mathlib

namespace Workspace.Types.Replication

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Replicating a vertex** (published paper, printed page 4, in the proof of 1.5).

The paper uses the operation without naming it formally:

> "a theorem of Lovász [16] shows that replicating a vertex of a perfect graph makes another
> perfect graph; so if we replace `z` by a set `Z` of `t − s` vertices all complete to `B₁`
> and to each other, and with no other neighbours in `Aᵢ ∪ B`, then the graph we make is
> perfect."

`replicateVertex G v` is the graph obtained from `G` by adding one new vertex
`w := Sum.inr ()` — a *copy* of `v` — whose neighbours are `v` itself together with all the
neighbours of `v`; i.e. `v` and `w` are adjacent twins. Concretely, on the vertex set
`V ⊕ Unit`:

* `Sum.inl a` and `Sum.inl b` are adjacent iff `G.Adj a b` (the old graph is unchanged);
* `Sum.inl a` and `w` are adjacent iff `a = v ∨ G.Adj a v`;
* `w` is not adjacent to itself.
-/
def replicateVertex (G : SimpleGraph V) (v : V) : SimpleGraph (V ⊕ Unit) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr _ => a = v ∨ G.Adj a v
    | Sum.inr _, Sum.inl b => b = v ∨ G.Adj b v
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (a | ⟨⟩) (b | ⟨⟩) h
    · exact h.symm
    · exact h
    · exact h
    · exact h
  loopless := by
    refine ⟨?_⟩
    rintro (a | ⟨⟩) h
    · exact G.irrefl h
    · exact h

end SPGT

end Workspace.Types.Replication
