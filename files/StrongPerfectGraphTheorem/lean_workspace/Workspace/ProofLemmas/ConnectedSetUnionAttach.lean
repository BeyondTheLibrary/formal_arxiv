import Mathlib
import Workspace.Types.Core

/-!
# Attaching one connected set to another

Infrastructure for the proof of 1.5.  The paper uses the following fact silently,
both in `G` (components of `A`) and in `Gᶜ` (anticomponents of `B`):

> a connected set together with another connected set that meets it or has an edge
> to it is again connected.

Stated for an arbitrary `G`, so that the *anti*connected version — the one that
supplies the maximality argument for an anticomponent `B₁` of `B` — is the same
  lemma applied to `Gᶜ`; no separate complement variant is needed.

`ConnectedSet G X` is `(G.induce X).Preconnected`, so `∅` counts as connected, as
the paper requires.

None of these lemmas has a counterpart in the paper; they are bookkeeping.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.ConnectedSetUnionAttach

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- A walk of `H|A` lifts to a walk of `H|B` whenever `A ⊆ B`. -/
private theorem reachable_induce_mono {H : SimpleGraph V} {A B : Set V}
    (hAB : A ⊆ B) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (hr : (H.induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (H.induce B).Reachable ⟨x, hAB hx⟩ ⟨y, hAB hy⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun z => ⟨z.1, hAB z.2⟩, fun {_ _} hab => hab⟩ : (H.induce A) →g (H.induce B)) p⟩

/-- If `P` and `Q` are connected and *linked* — either they meet, or some vertex of
`P` is adjacent to some vertex of `Q` — then `P ∪ Q` is connected. -/
theorem connectedSet_union {P Q : Set V}
    (hP : ConnectedSet G P) (hQ : ConnectedSet G Q)
    (hlink : (P ∩ Q).Nonempty ∨ ∃ p ∈ P, ∃ q ∈ Q, G.Adj p q) :
    ConnectedSet G (P ∪ Q) := by
  -- Extract a bridge: `p ∈ P` and `q ∈ Q` that are already joined inside `P ∪ Q`.
  obtain ⟨p, hp, q, hq, hbridge⟩ :
      ∃ p, ∃ hp : p ∈ P, ∃ q, ∃ hq : q ∈ Q,
        (G.induce (P ∪ Q)).Reachable ⟨p, Or.inl hp⟩ ⟨q, Or.inr hq⟩ := by
    rcases hlink with ⟨w, hwP, hwQ⟩ | ⟨p, hp, q, hq, hadj⟩
    · exact ⟨w, hwP, w, hwQ, by
        have : (⟨w, Or.inl hwP⟩ : ↥(P ∪ Q)) = ⟨w, Or.inr hwQ⟩ := rfl
        rw [this]⟩
    · exact ⟨p, hp, q, hq, SimpleGraph.Adj.reachable hadj⟩
  -- Every vertex of `P ∪ Q` reaches the bridge endpoint `p`.
  have key : ∀ u : ↥(P ∪ Q), (G.induce (P ∪ Q)).Reachable u ⟨p, Or.inl hp⟩ := by
    rintro ⟨u, hu⟩
    rcases hu with huP | huQ
    · exact reachable_induce_mono Set.subset_union_left huP hp (hP ⟨u, huP⟩ ⟨p, hp⟩)
    · exact (reachable_induce_mono Set.subset_union_right huQ hq
        (hQ ⟨u, huQ⟩ ⟨q, hq⟩)).trans hbridge.symm
  intro u v
  exact (key u).trans (key v).symm

/-- The special case `Q = {v}` of `connectedSet_union`: a connected set `P`
together with one further vertex `v` having a neighbour in `P` is connected.  This
is the form used at every call site (P3, P5(iii), §5.1). -/
theorem connectedSet_union_singleton {P : Set V} {v : V}
    (hP : ConnectedSet G P) (hv : ∃ p ∈ P, G.Adj v p) :
    ConnectedSet G (P ∪ {v}) := by
  obtain ⟨p, hp, hadj⟩ := hv
  refine connectedSet_union hP ?_ (Or.inr ⟨p, hp, v, rfl, hadj.symm⟩)
  -- a singleton is connected
  intro a b
  exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)

end Workspace.ProofLemmas.ConnectedSetUnionAttach
