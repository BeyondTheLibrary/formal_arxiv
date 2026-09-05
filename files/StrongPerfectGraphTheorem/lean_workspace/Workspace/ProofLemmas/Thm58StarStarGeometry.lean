import Workspace.ProofLemmas.Thm58StarStarBasics
import Workspace.ProofLemmas.Thm58StarBranchGeometry

/-!
# The branch between the two star vertices in 5.8 (4)

When the two star vertices are joined by a branch, that branch is the paper's `R_{v₁v₂}`.
This file orients the branch from `c₁` to `c₂`, produces the rung `R` together with the two
vertices `r₁`, `r₂`, and shows that the only vertex the two stars can share is a vertex of the
rung.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGeometry

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics
open ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ : Fin n}

/-- The first and last edges of a track give the two singleton star intersections.  This is
`Thm58StarBranchGeometry.rung_intersections` with the star dictionary supplied directly. -/
theorem rung_intersections
    (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {Q : List (Fin n)} {a b : Fin n}
    (hfrom : IsTrackFrom H Q a b) (h2 : 2 ≤ Q.length) :
    ∃ (R : List V) (r s : V), IsPathFrom G R r s ∧
      {x : V | x ∈ R} = edgeImage φ (trackEdges Q) ∧
      N a ∩ {x : V | x ∈ R} = {r} ∧ N b ∩ {x : V | x ∈ R} = {s} := by
  let r := firstRungVertex φ Q hfrom.1 h2
  let s := lastRungVertex φ Q hfrom.1 h2
  have hRset : {x : V | x ∈ trackRung φ Q hfrom.1} = edgeImage φ (trackEdges Q) :=
    Set.ext (fun _ => mem_trackRung_iff φ hfrom.1)
  refine ⟨trackRung φ Q hfrom.1, r, s, trackRung_isPathFrom_ends φ hfrom h2,
    hRset, ?_, ?_⟩
  · rw [hstar a, hRset]
    ext x
    constructor
    · rintro ⟨⟨e, he, hea, rfl⟩, heR⟩
      have heQ := (image_mem_iff he).mp heR
      exact congrArg (fun e : H.edgeSet => (φ e : V))
        (Subtype.ext (edge_eq_firstTrackEdge hfrom h2 heQ hea.2))
    · rintro rfl
      exact ⟨⟨_, firstTrackEdge_mem hfrom.1 h2,
        ⟨firstTrackEdge_mem hfrom.1 h2, firstTrackEdge_contains hfrom h2⟩, rfl⟩,
        ⟨_, firstTrackEdge_mem hfrom.1 h2, firstTrackEdge_mem_trackEdges h2, rfl⟩⟩
  · rw [hstar b, hRset]
    ext x
    constructor
    · rintro ⟨⟨e, he, heb, rfl⟩, heR⟩
      have heQ := (image_mem_iff he).mp heR
      exact congrArg (fun e : H.edgeSet => (φ e : V))
        (Subtype.ext (edge_eq_lastTrackEdge hfrom h2 heQ heb.2))
    · rintro rfl
      exact ⟨⟨_, lastTrackEdge_mem hfrom.1 h2,
        ⟨lastTrackEdge_mem hfrom.1 h2, lastTrackEdge_contains hfrom h2⟩, rfl⟩,
        ⟨_, lastTrackEdge_mem hfrom.1 h2, lastTrackEdge_mem_trackEdges h2, rfl⟩⟩

variable (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

/-- A branch containing both star vertices can be oriented from `c₁` to `c₂`. -/
theorem orient_branch {q : List (Fin n)} (hq : IsBranch H q) (h₁ : c₁ ∈ q) (h₂ : c₂ ∈ q) :
    ∃ Q, IsBranch H Q ∧ IsTrackFrom H Q c₁ c₂ ∧ trackEdges Q = trackEdges q := by
  have hne := stars_ne h
  have hq2 : 2 ≤ q.length := by
    have hpos : 0 < q.length := List.length_pos_of_mem h₁
    by_contra hcon
    have : q.length = 1 := by omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp this
    simp only [List.mem_singleton] at h₁ h₂
    exact hne (h₁.trans h₂.symm)
  have hfrom := Thm57Claim2Structure.branch_from_ends hq hq2
  have hint₁ : c₁ ∉ trackInterior q := fun hi => hq.2.1 c₁ hi h.star₁
  have hint₂ : c₂ ∉ trackInterior q := fun hi => hq.2.1 c₂ hi h.star₂
  rcases SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 h₁ hint₁ with he₁ | he₁
  · refine ⟨q, hq, ?_, rfl⟩
    rcases SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 h₂ hint₂ with he₂ | he₂
    · exact absurd (he₁.trans he₂.symm) hne
    · rw [he₁, he₂]; exact hfrom
  · refine ⟨q.reverse, Thm57Claim2Structure.isBranch_reverse hq, ?_,
      SubdivisionCounting.trackEdges_reverse q⟩
    rcases SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 h₂ hint₂ with he₂ | he₂
    · refine ⟨(Thm57Claim2Structure.isBranch_reverse hq).1, ?_, ?_⟩
      · rw [List.head?_reverse, he₁]; exact hfrom.2.2
      · rw [List.getLast?_reverse, he₂]; exact hfrom.2.1
    · exact absurd (he₁.trans he₂.symm) hne

/-- The two stars can only meet on the branch joining them. -/
theorem stars_inter_subset_rung {q : List (Fin n)} (hq : IsBranch H q)
    (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length) :
    N c₁ ∩ N c₂ ⊆ edgeImage φ (trackEdges q) := by
  intro x hx
  obtain ⟨he, rfl⟩ := adj_of_star_inter h hx
  have hadj : H.Adj c₁ c₂ := (SimpleGraph.mem_edgeSet _).mp he
  have hpair : IsBranch H [c₁, c₂] := isBranch_pair h hadj
  have hpairFrom : IsTrackFrom H [c₁, c₂] c₁ c₂ := ⟨hpair.1, rfl, rfl⟩
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := h.ready.2.2.1.1
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J h.ready.2.1
  have hEq : trackEdges q = trackEdges [c₁, c₂] :=
    BranchClassification.trackEdges_eq_of_same_ends hι htrack hlen hrev hdisj hnew hcover
      hedges hdeg hq hq2 hfrom hpair (by simp) hpairFrom h.star₁ h.star₂ (Or.inl ⟨rfl, rfl⟩)
  refine ⟨s(c₁, c₂), he, ?_, rfl⟩
  rw [hEq]
  exact ⟨0, by simp, rfl⟩

end Workspace.ProofLemmas.Thm58StarStarGeometry
