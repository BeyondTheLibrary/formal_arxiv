import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Thm58StarBranchLinkConfig
import Workspace.ProofLemmas.Thm58StarBranchMixed
import Workspace.ProofLemmas.Thm58StarBranchParity
import Workspace.Types.RousselRubio

/-! The remaining path constructions in 5.8 (2) and (6).

Each gap below produces the specific forbidden configuration used by the paper.
The deductions from these configurations, including the applications of 2.4, are proved
in `Thm58StarBranch`. None of these gaps asserts the full conclusion of 5.8.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58StarBranchGaps

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT
open Thm58StarBranchBasics Thm58StarBranchLinkConfig Thm58StarBranchMixed
open Thm58StarBranchParity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- GAP — 5.8 (2), printed p. 26: "Now S₁ and S₂ have the same parity since H is
bipartite. Yet S₁ can be completed via r₂-Q-s₁ and S₂ can be completed via
r₂-Q-s₁-s₂, a contradiction."

The missing construction chooses `Q`, then the two tracks after deleting the specified
edges at `c` and the branch vertex `w`. Their completions are the two holes below.
The extra vertex `s₂` makes their lengths have different parity. -/
theorem incident_parity_gap
    (h : Context G m J n H K φ N F P p₁ p₂ c q)
    (hcq : c ∈ q) (R : List V) (r t : V)
    (hR : IsPathFrom G R r t)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hinter : N c ∩ {x : V | x ∈ R} = {r})
    (s₁ s₂ : V) (hs₁ : s₁ ∈ N c \ {r}) (hs₂ : s₂ ∈ N c \ {r})
    (ha : G.Adj p₁ s₁) (hna : ¬ G.Adj p₁ s₂) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧
      C.length % 2 ≠ D.length % 2 := by
  obtain ⟨S₁, S₂, Q, y₀, y₁, hT⟩ :=
    exists_twoTrackCompletion h hcq R r t hR hRset hinter s₁ s₂ hs₁ hs₂ ha hna
  exact holes_of_two_tracks hT

/-- GAP — 5.8 (6), printed p. 28: "If pₙ has a unique neighbour (say r) in Rᵥ₁ᵥ₂,
then r can be linked onto the triangle T, contrary to 2.4."

The missing construction is the cycle avoiding `c`, together with a shortest track
from `c` to that cycle and the resulting three paths to `T`. The triangle is ordered
so that its first two vertices are nonneighbors of `r`. -/
theorem singleton_link_gap
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r : V) (hr : r ∈ edgeImage φ (trackEdges q)) (ha : G.Adj p₂ r)
    (hunique : ∀ x ∈ edgeImage φ (trackEdges q), G.Adj p₂ x → x = r) :
    ∃ a b d : V, VertexCanBeLinkedOntoTriangle G r a b d ∧
      ¬ G.Adj r a ∧ ¬ G.Adj r b := by
  obtain ⟨w, b, S, Rg, E, T, hL, h0, h1⟩ :=
    exists_starTrackLink_singleton h hcq r hr ha hunique
  exact ⟨apex hL 0, apex hL 1, apex hL 2, canBeLinked hL, h0, h1⟩

/-- GAP — 5.8 (6), printed p. 28: "If pₙ has two nonadjacent neighbours in Rᵥ₁ᵥ₂,
then pₙ can be linked onto the triangle T, contrary to 2.4."

This uses the same cycle and three paths as the unique-neighbor case, with the two
directions along the rung now attached directly to `p₂`. -/
theorem separated_neighbors_link_gap
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r s : V) (hr : r ∈ edgeImage φ (trackEdges q))
    (hs : s ∈ edgeImage φ (trackEdges q)) (hrs : r ≠ s)
    (hnadj : ¬ G.Adj r s) (har : G.Adj p₂ r) (has : G.Adj p₂ s) :
    ∃ a b d : V, VertexCanBeLinkedOntoTriangle G p₂ a b d ∧
      ¬ G.Adj p₂ a ∧ ¬ G.Adj p₂ b := by
  obtain ⟨w, b, S, Rg, E, T, hL, hw⟩ :=
    exists_starTrackLink_separated h hcq r s hr hs hrs hnadj har has
  exact ⟨apex hL 0, apex hL 1, apex hL 2, canBeLinked hL,
    last_not_adj_apex h hL hw 0, last_not_adj_apex h hL hw 1⟩

/-- GAP — 5.8 (6), printed p. 28: "In H there is a cycle C₂ using the branch between
v₁ and v₂, and using an edge in A and an edge in B. ... Hence a can be linked onto
the triangle formed by pₙ and its two neighbours in Rᵥ₁ᵥ₂, a contradiction."

The missing step splits `c` into adjacent vertices carrying the two nonempty parts of
its star and applies Menger's argument. The result is the indicated link, with `a`
chosen among the neighbors of `p₁` in the star. -/
theorem mixed_star_link_gap
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r s : V) (hr : r ∈ edgeImage φ (trackEdges q))
    (hs : s ∈ edgeImage φ (trackEdges q)) (hrs : G.Adj r s)
    (hneighbors : ∀ x ∈ K, G.Adj p₂ x ↔ x = r ∨ x = s)
    (hA : ∃ a ∈ N c, G.Adj p₁ a) (hB : ∃ b ∈ N c, ¬ G.Adj p₁ b) :
    ∃ a ∈ N c, G.Adj p₁ a ∧ VertexCanBeLinkedOntoTriangle G a p₂ r s := by
  have hpr : G.Adj p₂ r := (hneighbors r (image_subset hr)).mpr (Or.inl rfl)
  have hps : G.Adj p₂ s := (hneighbors s (image_subset hs)).mpr (Or.inr rfl)
  obtain ⟨a, D₁, D₂, T₁, T₂, hM⟩ :=
    exists_mixedSectors h hcq r s hr hs hrs hneighbors hA hB
  exact ⟨a, hM.aStar, hM.aAdj, mixed_link_of_sectors h hcq hr hs hrs hpr hps hM⟩

end Workspace.ProofLemmas.Thm58StarBranchGaps
