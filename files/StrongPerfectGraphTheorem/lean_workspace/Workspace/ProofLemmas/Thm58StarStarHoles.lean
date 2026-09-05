import Workspace.ProofLemmas.Thm58StarStarGeometry
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.BranchExternalEdge

/-!
# Completing a path of `L(H)` into a hole, in the star--star case of 5.8

Claims (3) and (4) of 5.8 finish by taking a path of `L(H)` whose two ends are neighbours of
the two ends of the outside path `P`, and closing it into a hole *"via `F`"*.  This file does
that once and for all:

* `hole_of_two_paths` glues a path of `L(H)` and the reverse of a second path into a hole,
  given that the only two edges between them join the corresponding ends;
* `Completion` is the data the paper produces (a path of `L(H)` from a neighbour of `p₁` to a
  neighbour of `p₂` with no other neighbour of `p₁` or `p₂` on it), and `hole_of_completion`
  turns it into the hole `S ++ P.reverse`;
* `holes_of_completions` reads two such paths of opposite parity as the paper's
  *"a contradiction"*: two holes of different parity.

The two geometric facts used all along are also here: a star of `H` is a clique of `G`
(`star_adj`), and an edge of `H` outside a branch meets the branch only at its two ends
(`adj_rung_imp`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarHoles

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ : Fin n}

/-! ## Gluing -/

/-- Two vertex-disjoint paths whose only edges between them join first end to first end and
last end to last end close into a hole. -/
theorem hole_of_two_paths {S Q : List V} {a₁ a₂ q₁ q₂ : V}
    (hS : IsPathFrom G S a₁ a₂) (hQ : IsPathFrom G Q q₁ q₂)
    (hdisj : ∀ x ∈ S, x ∉ Q)
    (hcross : ∀ x ∈ S, ∀ y ∈ Q, (G.Adj x y ↔ (x = a₂ ∧ y = q₂) ∨ (x = a₁ ∧ y = q₁)))
    (hlen : 4 ≤ S.length + Q.length) :
    IsHoleList G (S ++ Q.reverse) := by
  refine PathGlue.glue_hole hS (PathBasics.isPathFrom_reverse hQ) ?_ ?_ ?_
  · intro x hx hmem
    exact hdisj x hx (List.mem_reverse.mp hmem)
  · intro x hx y hy
    exact hcross x hx y (List.mem_reverse.mp hy)
  · simpa using hlen

/-! ## Two geometric facts -/

/-- A star of `H` is a clique of `G`: two distinct edges of `H` at a common vertex are adjacent
vertices of the line graph. -/
theorem star_adj (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d)) (d : Fin n)
    {x y : V} (hx : x ∈ N d) (hy : y ∈ N d) (hxy : x ≠ y) : G.Adj x y := by
  rw [hstar d] at hx hy
  obtain ⟨e, he, hed, rfl⟩ := hx
  obtain ⟨f, hf, hfd, rfl⟩ := hy
  have hef : (⟨e, he⟩ : H.edgeSet) ≠ ⟨f, hf⟩ := by
    intro hcon
    exact hxy (congrArg (fun z : H.edgeSet => (φ z : V)) hcon)
  exact φ.map_rel_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hef, d, hed.2, hfd.2⟩)

/-- An edge of `H` off the branch from `c₁` to `c₂` can meet the branch only at `c₁` or `c₂`.
Read in `G`: a vertex outside the rung that is adjacent to a vertex of the rung shares a star
with it, and that star is one of the two ends. -/
theorem adj_rung_imp (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {q : List (Fin n)} (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂)
    {x y : V} (hxK : x ∈ K) (hxR : x ∉ edgeImage φ (trackEdges q))
    (hy : y ∈ edgeImage φ (trackEdges q)) (hadj : G.Adj x y) :
    (x ∈ N c₁ ∧ y ∈ N c₁) ∨ (x ∈ N c₂ ∧ y ∈ N c₂) := by
  obtain ⟨e, he, rfl⟩ := exists_edge (φ := φ) hxK
  obtain ⟨f, hf, hfq, rfl⟩ := hy
  have heq : e ∉ trackEdges q := fun hc => hxR ⟨e, he, hc, rfl⟩
  have hL : H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff.mp hadj
  obtain ⟨-, w, hwe, hwf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hL
  have hw := BranchExternalEdge.external_edge_meets_branch_only_at_ends hq hfrom hfq he heq
    hwe hwf
  rcases hw with rfl | rfl
  · exact Or.inl ⟨by rw [hstar w]; exact ⟨e, he, ⟨he, hwe⟩, rfl⟩,
      by rw [hstar w]; exact ⟨f, hf, ⟨hf, hwf⟩, rfl⟩⟩
  · exact Or.inr ⟨by rw [hstar w]; exact ⟨e, he, ⟨he, hwe⟩, rfl⟩,
      by rw [hstar w]; exact ⟨f, hf, ⟨hf, hwf⟩, rfl⟩⟩

/-! ## Completion via `F` -/

/-- The data of the paper's *"can be completed via `F`"*: a path `S` of `L(H)` whose first end
is a neighbour of `p₁`, whose last end is a neighbour of `p₂`, which has no other neighbour of
`p₁` or `p₂` on it, and which avoids the set `E` of vertices that the internal vertices of the
outside path could attach to. -/
structure Completion (G : SimpleGraph V) (K E : Set V) (p₁ p₂ : V) (S : List V) (a₁ a₂ : V) :
    Prop where
  path : IsPathFrom G S a₁ a₂
  subK : ∀ x ∈ S, x ∈ K
  adj₁ : G.Adj p₁ a₁
  adj₂ : G.Adj p₂ a₂
  only₁ : ∀ x ∈ S, G.Adj p₁ x → x = a₁
  only₂ : ∀ x ∈ S, G.Adj p₂ x → x = a₂
  avoid : ∀ x ∈ S, x ∉ E
  ends_ne : a₁ ≠ a₂

variable (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

/-- A completion has at least two vertices, since its two ends are different. -/
theorem two_le_completion {E : Set V} {S : List V} {a₁ a₂ : V}
    (hc : Completion G K E p₁ p₂ S a₁ a₂) : 2 ≤ S.length := by
  have h0 : 0 < S.length := PathBasics.path_length_pos hc.path.1
  by_contra hcon
  have h1 : S.length = 1 := by omega
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
  subst hx
  have e₁ : x = a₁ := by simpa using hc.path.2.1
  have e₂ : x = a₂ := by simpa using hc.path.2.2
  exact hc.ends_ne (e₁ ▸ e₂ ▸ rfl)

/-- PAPER, proof of 5.8 (3) and (4): *"they can both be completed via `F`"*.  The completion of
`S` is the hole `S ++ P.reverse`. -/
theorem hole_of_completion {S : List V} {a₁ a₂ : V}
    (hc : Completion G K (N c₁ ∩ N c₂) p₁ p₂ S a₁ a₂) :
    IsHoleList G (S ++ P.reverse) := by
  have hFK : F ⊆ Kᶜ := h.ready.2.2.2.2.1
  refine hole_of_two_paths hc.path (path h) ?_ ?_ ?_
  · intro x hx hxP
    have hxF : x ∈ F := by rw [← vertices h]; exact hxP
    exact hFK hxF (hc.subK x hx)
  · intro x hx y hy
    constructor
    · intro hadj
      by_cases hy₁ : y = p₁
      · exact Or.inr ⟨hc.only₁ x hx (hy₁ ▸ hadj.symm), hy₁⟩
      by_cases hy₂ : y = p₂
      · exact Or.inl ⟨hc.only₂ x hx (hy₂ ▸ hadj.symm), hy₂⟩
      · exact absurd (mid_adj_mem h hy hy₁ hy₂ (hc.subK x hx) hadj.symm) (hc.avoid x hx)
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hc.adj₂.symm
      · exact hc.adj₁.symm
  · have := two_le_completion h hc
    have := two_le_length h
    omega

/-- PAPER, proof of 5.8 (3) and (4), last sentence: two completions of opposite parity give two
holes of different parity. -/
theorem holes_of_completions {S₁ S₂ : List V} {a₁ a₂ b₁ b₂ : V}
    (hc₁ : Completion G K (N c₁ ∩ N c₂) p₁ p₂ S₁ a₁ a₂)
    (hc₂ : Completion G K (N c₁ ∩ N c₂) p₁ p₂ S₂ b₁ b₂)
    (hpar : S₁.length % 2 ≠ S₂.length % 2) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  refine ⟨S₁ ++ P.reverse, S₂ ++ P.reverse, hole_of_completion h hc₁, hole_of_completion h hc₂,
    ?_⟩
  simp only [List.length_append, List.length_reverse]
  omega

end Workspace.ProofLemmas.Thm58StarStarHoles
