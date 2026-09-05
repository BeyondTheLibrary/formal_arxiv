import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim2Window
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm57Claim2FiveSix
import Workspace.ProofLemmas.Thm57Claim2Connectivity
import Workspace.ProofLemmas.Thm57Claim2CommonNeighbor

/-!
# The parity split in 5.7 (2)

The elementary first result below turns a two-colouring into the paper's two notions of
biparity.  The other two results record the two long graph arguments in the parity split of
printed claim (2).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2Parity

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup
open Workspace.ProofLemmas.Thm57Claim2Window
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Any two vertices in a bipartite graph have either the same or different biparity. -/
theorem same_or_different_biparity (H : SimpleGraph W) (hbip : H.IsBipartite) (u v : W) :
    SameBiparity H u v ∨ DifferentBiparity H u v := by
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
  by_cases huv : col u = col v
  · left
    intro q hq
    exact (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hq).2 huv
  · right
    intro q hq
    apply Nat.not_even_iff_odd.mp
    intro heven
    exact huv
      ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hq).1 heven)

/-- PAPER (printed p. 22):

*"Suppose first that `c₁,c₂` have the same biparity. ... From the track
`Q₁-c₁-P₁-b-P₃-a-c₂` and the hypothesis it follows that `Q₁` is odd, a
contradiction."*

This is the first, same-biparity half of the parity argument.  The assumptions name the branch
window `C`, the two nonempty sets `A₁,A₂`, and the preceding sentence that every edge of
`X` outside `C` meets one of its ends. -/
theorem same_biparity_impossible (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet) (hnotrack : NoEvenTrack57 H X)
    (hdisj : TwoDisjointEdges H X) {B : List W} (hB : IsBranch H B) {i j : ℕ}
    (hij : i < j) (hj : j < B.length)
    (hA₁ : (ASet H X (slice B i j) B[i]).Nonempty)
    (hA₂ : (ASet H X (slice B i j) B[j]).Nonempty)
    (houtside : X \ trackEdges (slice B i j) ⊆
      incidentEdges H B[i] ∪ incidentEdges H B[j])
    (hsame : SameBiparity H B[i] B[j]) : False := by
  obtain ⟨a, hAeq₁, hAeq₂⟩ :=
    Workspace.ProofLemmas.Thm57Claim2SameEnds.common_outer_neighbor
      H hc3 X hnotrack hB hij hj hA₁ hA₂ houtside hsame
  let C := slice B i j
  have hC : IsTrackFrom H C B[i] B[j] := isTrackFrom_slice hB.1 hj (by omega)
  have hClen : 3 ≤ C.length := by
    have hlen : C.length = j - i + 1 := length_slice B hj (by omega)
    have heven := hsame C hC
    rw [trackLength, Nat.even_iff] at heven
    omega
  have he₁ : s(B[i], a) ∈ ASet H X C B[i] := by rw [hAeq₁]; simp
  have he₂ : s(B[j], a) ∈ ASet H X C B[j] := by rw [hAeq₂]; simp
  have hadj₁ : H.Adj B[i] a := he₁.1.1.1
  have hadj₂ : H.Adj B[j] a := he₂.1.1.1
  have haC : a ∉ C := by
    intro ha
    have haint := Workspace.ProofLemmas.Thm57Claim2DeletedWindow.outside_edge_ends
      hB hij hj he₁.1.1.1 he₁.2 a (Sym2.mem_mk_right _ _)
    rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem hC.2.1 hC.2.2 ha haint with h | h
    · exact hadj₁.ne h.symm
    · exact hadj₂.ne h.symm
  have houtpair : X \ trackEdges C ⊆ {s(B[i], a), s(B[j], a)} := by
    intro e he
    rcases houtside he with h | h
    · have hA : e ∈ ASet H X C B[i] := ⟨⟨h, he.1⟩, he.2⟩
      rw [hAeq₁] at hA
      exact Or.inl hA
    · have hA : e ∈ ASet H X C B[j] := ⟨⟨h, he.1⟩, he.2⟩
      rw [hAeq₂] at hA
      exact Or.inr hA
  have hCX : ∃ e ∈ trackEdges C, e ∈ X := by
    obtain ⟨e, he, f, hf, hdisjoint⟩ := hdisj
    by_cases heC : e ∈ trackEdges C
    · exact ⟨e, heC, he⟩
    by_cases hfC : f ∈ trackEdges C
    · exact ⟨f, hfC, hf⟩
    have hcommon : ∀ d ∈ X, d ∉ trackEdges C → a ∈ d := by
      intro d hd hdC
      rcases houtpair ⟨hd, hdC⟩ with h | h <;> rw [h] <;> simp
    exact (hdisjoint a ⟨hcommon e he heC, hcommon f hf hfC⟩).elim
  obtain ⟨R, S, hR, hS, hRlen, hSlen, haR, hc₂S, hRmeet, hSmeet, havoid⟩ :=
    Workspace.ProofLemmas.Thm57Claim2Connectivity.common_neighbor_routes
      H hc3 hB hij hj hClen hadj₁ hadj₂ he₁.2 he₂.2
  have hclean : ∀ e ∈ trackEdges R ∪ trackEdges S, e ∉ X := by
    intro e he heX
    have hnot := Set.disjoint_left.mp havoid he
    by_cases heC : e ∈ trackEdges C
    · exact hnot (Or.inl heC)
    · exact hnot (Or.inr (houtpair ⟨heX, heC⟩))
  exact Workspace.ProofLemmas.Thm57Claim2CommonNeighbor.two_routes_contradiction
    hnotrack hC hClen hsame hR hS (by omega) (by omega) haC haR hc₂S hRmeet hSmeet
    hadj₁ hadj₂ he₁.1.2 he₂.1.2
    (fun e he => hclean e (Or.inl he)) (fun e he => hclean e (Or.inr he)) hCX

/-- PAPER (printed p. 22):

*"Let `H'` be the graph obtained from `H` by deleting the internal vertices and edges of `C`.
... A similar statement holds with `c₁,c₂` exchanged. By 5.6 applied to `H'`, it follows
that `B₁ ∪ B₂ = ∅`."*

This is the different-biparity half of the parity argument.  The conclusion uses the definitions
of `B₁,B₂` from `Thm57Claim2Window`. -/
theorem different_biparity_exhaustion (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : NoEvenTrack57 H X) {B : List W} (hB : IsBranch H B) {i j : ℕ}
    (hij : i < j) (hj : j < B.length)
    (hA₁ : (ASet H X (slice B i j) B[i]).Nonempty)
    (hA₂ : (ASet H X (slice B i j) B[j]).Nonempty)
    (houtside : X \ trackEdges (slice B i j) ⊆
      incidentEdges H B[i] ∪ incidentEdges H B[j])
    (hdiff : DifferentBiparity H B[i] B[j]) :
    BSet H X (slice B i j) B[i] ∪ BSet H X (slice B i j) B[j] = ∅ := by
  apply Workspace.ProofLemmas.Thm57Claim2FiveSix.exhaustion_of_connectivity
    H hbip hc3 X hnotrack hB hij hj hA₁ hA₂ houtside hdiff
  · exact Workspace.ProofLemmas.Thm57Claim2Connectivity.window_complement_connected
      H hc3 hB hij hj
  · intro e he u v heq
    subst e
    apply Workspace.ProofLemmas.Thm57Claim2Connectivity.window_complement_delete_incident_connected
      H hc3 hB hij hj
    · rcases he with he | he
      · exact Or.inl he.1.1
      · exact Or.inr he.1.1
    · rcases he with he | he
      · exact he.2
      · exact he.2

end Workspace.ProofLemmas.Thm57Claim2Parity
