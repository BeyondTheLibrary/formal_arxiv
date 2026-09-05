import Workspace.ProofLemmas.Thm57Claim2DeletedWindow
import Workspace.ProofLemmas.Thm57Claim2WindowConn
import Workspace.ProofLemmas.Thm57Claim2Routes

/-! # The remaining connectivity steps in 5.7 (2)

These gaps concern only a subdivision and a subtrack of one branch. They do not assume
the forbidden-track hypothesis or any conclusion of 5.7.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2Connectivity

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.TrackSlice
open Workspace.ProofLemmas.Thm57Claim2DeletedWindow
open Workspace.ProofLemmas.Thm57Claim2WindowConn
open Workspace.ProofLemmas.Thm57Claim2Routes

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- GAP: PAPER (printed p. 23): *"Since `c₁,c₂` belong to the same branch of `H` and
`H` is cyclically 3-connected, it follows that there is a track in `H \ {c₁,c₂}`
from `a₁` to `a₂`."*

The connected part used here is outside the whole window. Its internal vertices form a
separate branch segment after the ends are removed. This is also the first connectivity
premise in the later application of 5.6 to `H'`. -/
theorem window_complement_connected (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {B : List W} (hB : IsBranch H B) {i j : ℕ} (hij : i < j) (hj : j < B.length) :
    ConnectedSet (H.deleteEdges (trackEdges (slice B i j)))
      (Outside (slice B i j) \ {B[i], B[j]}) :=
  complement_connected H hc3 hB hij hj

/-- GAP: PAPER (printed p. 23): *"Let `H'` be the graph obtained from `H` by deleting the
internal vertices and edges of `C`. ... By 5.6 applied to `H'` ..."*

This is the other connectivity premise of 5.6: deleting the ends of an edge outside `C`
incident with `c₁` or `c₂` leaves `H'` connected. Only the subdivision structure is used. -/
theorem window_complement_delete_incident_connected (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) {B : List W} (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length) {u v : W}
    (hedge : s(u, v) ∈ incidentEdges H B[i] ∪ incidentEdges H B[j])
    (hout : s(u, v) ∉ trackEdges (slice B i j)) :
    ConnectedSet (H.deleteEdges (trackEdges (slice B i j)))
      (Outside (slice B i j) \ {u, v}) :=
  complement_delete_incident_connected H hc3 hB hij hj hedge hout

/-- GAP: PAPER (printed p. 23): *"Now there is only one branch of `H` containing `c₁` and
`c₂`, since `J` is simple ... and so `C = B` and `c₁,c₂` are branch-vertices. Choose a
branch-vertex `b` ... and choose three paths `P₁,P₂,P₃` between `b` and `c₁,c₂,a`
respectively, pairwise disjoint except for `b`."*

Here `R` is the track through `P₁` and `P₂`, and `S` is the track through `P₁` and `P₃`.
Both avoid the edges of `C` and the two edges to `a`. These are the only consequences of
the three paths needed in the parity calculation. No assumption on `X` is used. -/
theorem common_neighbor_routes (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {B : List W} (hB : IsBranch H B) {i j : ℕ} (hij : i < j) (hj : j < B.length)
    (hlen : 3 ≤ (slice B i j).length) {a : W}
    (hadj₁ : H.Adj B[i] a) (hadj₂ : H.Adj B[j] a)
    (hout₁ : s(B[i], a) ∉ trackEdges (slice B i j))
    (hout₂ : s(B[j], a) ∉ trackEdges (slice B i j)) :
    ∃ R S : List W,
      IsTrackFrom H R B[i] B[j] ∧ IsTrackFrom H S B[i] a ∧
      3 ≤ R.length ∧ 3 ≤ S.length ∧ a ∉ R ∧ B[j] ∉ S ∧
      (∀ w ∈ R, w ∈ slice B i j → w = B[i] ∨ w = B[j]) ∧
      (∀ w ∈ S, w ∈ slice B i j → w = B[i]) ∧
      Disjoint (trackEdges R ∪ trackEdges S)
        (trackEdges (slice B i j) ∪ {s(B[i], a), s(B[j], a)}) :=
  common_neighbor_routes_core H hc3 hB hij hj hlen hadj₁ hadj₂ hout₁ hout₂

end Workspace.ProofLemmas.Thm57Claim2Connectivity
