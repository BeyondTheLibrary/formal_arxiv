import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm58StarBranchParityBuild

/-!
# The two tracks out of the star in 5.8 (2)

PAPER (proof of 5.8 (2), printed p. 26): *"Let `Q` be the path between `r₂` and `s₁` with
interior in `F ∪ V(R_{uv} \ {r₁})`.  Choose `w ∈ V(J)` such that `s₁ ∈ V(R_{uw})`.  Now `H` is a
subdivision of a 3-connected graph, so if we delete all edges of `H` incident with `u` except
`s₁`, the graph we produce is still connected.  Consequently there is a track of `H` from `u`
to `v` with first edge `s₁`; and hence there is a path `S₁` of `L(H)` from `s₁` to `r₂`,
vertex-disjoint from `V(R_{uv}) ∪ N_u` except for its ends.  Indeed, if we delete from `H` both
the vertex `w` and all edges incident with `u` except `s₂`, the graph remains connected; so
there is a path `S₂` of `L(H)` between `s₂` and `r₂`, vertex-disjoint from
`R_{uv} ∪ N_u ∪ V(R_{uw}) ∪ N_w` except for its ends.  Now `S₁` and `S₂` have the same parity
since `H` is bipartite.  Yet `S₁` can be completed via `r₂-Q-s₁` and `S₂` can be completed via
`r₂-Q-s₁-s₂`, a contradiction."*

The two completions are two holes of `G` whose lengths differ by exactly one, because the
second one runs through the extra vertex `s₂`.  This file glues the two holes together from
the data of the quoted sentence (`holes_of_two_tracks`) and states the existence of that data
as the remaining gap.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchParity

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- The data of the last two sentences of 5.8 (2).

`Q` is the interior of the path `r₂-Q-s₁` (its ends `y₀` and `y₁` are the neighbours of `t`
and of `s₁` on it), `S₁` runs from `s₁` to `t` and `S₂` from `s₂` to `t`, and the two of them
have the same parity because `H` is bipartite.  `Q ++ [s₁]` is the longer completion, used for
`S₂`. -/
structure TwoTrackCompletion (G : SimpleGraph V) (t s₁ s₂ : V)
    (S₁ S₂ Q : List V) (y₀ y₁ : V) : Prop where
  first : IsPathFrom G S₁ s₁ t
  second : IsPathFrom G S₂ s₂ t
  middle : IsPathFrom G Q y₀ y₁
  longer : IsPathFrom G (Q ++ [s₁]) y₀ s₁
  disj₁ : ∀ x ∈ S₁, x ∉ Q
  disj₂ : ∀ x ∈ S₂, x ∉ Q ++ [s₁]
  cross₁ : ∀ x ∈ S₁, ∀ y ∈ Q, (G.Adj x y ↔ (x = t ∧ y = y₀) ∨ (x = s₁ ∧ y = y₁))
  cross₂ : ∀ x ∈ S₂, ∀ y ∈ Q ++ [s₁],
    (G.Adj x y ↔ (x = t ∧ y = y₀) ∨ (x = s₂ ∧ y = s₁))
  len₁ : 4 ≤ S₁.length + Q.length
  len₂ : 4 ≤ S₂.length + (Q ++ [s₁]).length
  parity : S₁.length % 2 = S₂.length % 2

/-- The two completions of the quoted sentence are holes whose lengths differ by one. -/
theorem holes_of_two_tracks {t s₁ s₂ : V} {S₁ S₂ Q : List V} {y₀ y₁ : V}
    (hT : TwoTrackCompletion G t s₁ s₂ S₁ S₂ Q y₀ y₁) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧
      C.length % 2 ≠ D.length % 2 := by
  refine ⟨S₁ ++ Q, S₂ ++ (Q ++ [s₁]),
    PathGlue.glue_hole hT.first hT.middle hT.disj₁ hT.cross₁ hT.len₁,
    PathGlue.glue_hole hT.second hT.longer hT.disj₂ hT.cross₂ hT.len₂, ?_⟩
  have hp := hT.parity
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-- GAP — PAPER, proof of 5.8 (2), printed p. 26: *"Let `Q` be the path between `r₂` and `s₁`
with interior in `F ∪ V(R_{uv} \ {r₁})`. ... Consequently there is a track of `H` from `u` to
`v` with first edge `s₁`; and hence there is a path `S₁` of `L(H)` from `s₁` to `r₂`,
vertex-disjoint from `V(R_{uv}) ∪ N_u` except for its ends.  Indeed, if we delete from `H` both
the vertex `w` and all edges incident with `u` except `s₂`, the graph remains connected; so
there is a path `S₂` of `L(H)` between `s₂` and `r₂`, vertex-disjoint from
`R_{uv} ∪ N_u ∪ V(R_{uw}) ∪ N_w` except for its ends.  Now `S₁` and `S₂` have the same parity
since `H` is bipartite."*

`Q` is the interior of `r₂-Q-s₁`: it starts at the neighbour `y₀` of `t = r₂` on the branch and
ends at the neighbour `y₁ = p₁` of `s₁` in `F`.  The equal parity of `S₁` and `S₂` is the
bipartiteness of `H` read through
`BipartiteClosedWalkEven.even_trackLength_iff`: both tracks join `u` to `v`. -/
theorem exists_twoTrackCompletion
    (h : Context G m J n H K φ N F P p₁ p₂ c q)
    (hcq : c ∈ q) (R : List V) (r t : V)
    (hR : IsPathFrom G R r t)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hinter : N c ∩ {x : V | x ∈ R} = {r})
    (s₁ s₂ : V) (hs₁ : s₁ ∈ N c \ {r}) (hs₂ : s₂ ∈ N c \ {r})
    (ha : G.Adj p₁ s₁) (hna : ¬ G.Adj p₁ s₂) :
    ∃ (S₁ S₂ Q : List V) (y₀ y₁ : V),
      TwoTrackCompletion G t s₁ s₂ S₁ S₂ Q y₀ y₁ := by
  obtain ⟨S₁, S₂, Qm, y₀, y₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    Thm58StarBranchParityBuild.exists_completion_data h hcq R r t hR hRset hinter s₁ s₂
      hs₁ hs₂ ha hna
  exact ⟨S₁, S₂, Qm, y₀, y₁, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Workspace.ProofLemmas.Thm58StarBranchParity
