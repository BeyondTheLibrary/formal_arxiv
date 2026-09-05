import Workspace.ProofLemmas.Thm57Claim2Window
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-! # The forbidden tracks in the two parity cases of 5.7 (2) -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2TrackParity

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup
open Workspace.ProofLemmas.Thm57Claim2Window
open Workspace.ProofLemmas.TrackSlice
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The two edges on either side of an internal track vertex have only that vertex in common. -/
theorem second_vertex_of_incident_edges {H : SimpleGraph W} {q : List W}
    (hq : IsTrackList H q) (hlen : 3 ≤ q.length) {c : W}
    (hfirst : c ∈ s(q[0], q[1])) (hsecond : c ∈ s(q[1], q[2])) : q[1] = c := by
  rcases Sym2.mem_iff.mp hfirst with h | h
  · rcases Sym2.mem_iff.mp hsecond with h' | h'
    · exact h'.symm
    · have heq := hq.2.1.getElem_inj_iff.mp (h.symm.trans h')
      omega
  · exact h.symm

/-- PAPER: *"only its end-edges are in `X` (because every edge in `X` either belongs to
`C` or is incident with one of `c₁,c₂`)"*.

This is the edge bookkeeping for a track outside `C` between its two ends. -/
theorem clean_outside_track {H : SimpleGraph W} {X : Set (Sym2 W)} {C q : List W}
    {c₁ c₂ : W} (hq : IsTrackFrom H q c₁ c₂) (hlen : 2 ≤ q.length)
    (houtside : X \ trackEdges C ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂)
    (havoid : Disjoint (trackEdges q) (trackEdges C)) :
    ∀ e ∈ trackEdges q, e ≠ s(q[0], q[1]) →
      e ≠ s(q[q.length - 2], q[q.length - 1]) → e ∉ X := by
  intro e he hfirst hlast heX
  have heC : e ∉ trackEdges C := fun h => Set.disjoint_left.mp havoid he h
  rcases houtside ⟨heX, heC⟩ with h | h
  · apply hfirst
    exact head_edge_unique hq.1 hlen he (by rw [track_head hq]; exact h.2)
  · apply hlast
    have hc₂ : q[q.length - 1]'(by omega) = c₂ := by
      have hlast := hq.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
      exact Option.some_injective _ hlast
    have heq := last_edge_unique hq.1 hlen he (by rw [hc₂]; exact h.2)
    rw [getElem_eq_of_index_eq q (show q.length - 2 + 1 = q.length - 1 by omega)] at heq
    exact heq

/-- PAPER: *"Since `c₁,c₂` have the same biparity, it follows that `T` is even; ...
it follows from the hypothesis ... that `T` has length 2."* -/
theorem same_biparity_track_short {H : SimpleGraph W} {X : Set (Sym2 W)}
    {C q : List W} {c₁ c₂ : W} (hnotrack : NoEvenTrack57 H X)
    (hsame : SameBiparity H c₁ c₂) (hq : IsTrackFrom H q c₁ c₂)
    (hlen : 2 ≤ q.length)
    (hfirst : s(q[0], q[1]) ∈ X)
    (hlast : s(q[q.length - 2], q[q.length - 1]) ∈ X)
    (houtside : X \ trackEdges C ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂)
    (havoid : Disjoint (trackEdges q) (trackEdges C)) : q.length = 3 := by
  have heven := hsame q hq
  have hclean := clean_outside_track hq hlen houtside havoid
  have hsmall : q.length < 5 := by
    by_contra h
    exact hnotrack ⟨q, by omega, hq.1, heven, hfirst, hlast, hclean⟩
  rw [trackLength, Nat.even_iff] at heven
  omega

/-- PAPER: *"There is no track `T` in `H'` with first edge in `A₁`, second edge in `B₁`
(and hence second vertex `c₁`), last vertex `c₂` and last edge in `A₂`; for any such track
would be even, ... and have length ≥ 4, and have only its end-edges in `X`."* -/
theorem no_first_second_last_track {H : SimpleGraph W} {X : Set (Sym2 W)}
    {C : List W} {c₁ c₂ : W} (hnotrack : NoEvenTrack57 H X)
    (hdiff : DifferentBiparity H c₁ c₂)
    (houtside : X \ trackEdges C ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂)
    {q : List W} (hlen : 3 ≤ q.length) (hq : IsTrackList H q)
    (havoid : Disjoint (trackEdges q) (trackEdges C))
    (hfirst : s(q[0], q[1]) ∈ ASet H X C c₁)
    (hsecond : s(q[1], q[2]) ∈ BSet H X C c₁)
    (hlast : q.getLast? = some c₂)
    (hend : s(q[q.length - 2], q[q.length - 1]) ∈ ASet H X C c₂) : False := by
  have hc₁ : q[1]'(by omega) = c₁ :=
    second_vertex_of_incident_edges hq hlen hfirst.1.1.2 hsecond.1.1.2
  have hc₂ : q[q.length - 1]'(by omega) = c₂ := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    exact Option.some_injective _ hlast
  have htail : IsTrackFrom H (slice q 1 (q.length - 1)) c₁ c₂ := by
    have h := isTrackFrom_slice hq (show q.length - 1 < q.length by omega)
      (show 1 ≤ q.length - 1 by omega)
    rwa [hc₁, hc₂] at h
  have hodd := hdiff _ htail
  rw [trackLength, length_slice q (show q.length - 1 < q.length by omega)
    (show 1 ≤ q.length - 1 by omega), Nat.odd_iff] at hodd
  have heven : Even (trackLength q) := by
    rw [trackLength, Nat.even_iff]
    omega
  have hne3 : q.length ≠ 3 := by
    intro h3
    have hlastedge : s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)) =
        s(q[1]'(by omega), q[2]'(by omega)) := by
      rw [getElem_eq_of_index_eq q (show q.length - 2 = 1 by omega),
        getElem_eq_of_index_eq q (show q.length - 1 = 2 by omega)]
    exact hsecond.1.2 (hlastedge ▸ hend.1.2)
  have hlong : 5 ≤ q.length := by omega
  apply hnotrack
  refine ⟨q, hlong, hq, heven, hfirst.1.2, hend.1.2, ?_⟩
  intro e he hnefirst hnelast heX
  have heC : e ∉ trackEdges C := fun h => Set.disjoint_left.mp havoid he h
  rcases houtside ⟨heX, heC⟩ with h | h
  · obtain ⟨k, hk, rfl⟩ := he
    have hmem : q[1]'(by omega) ∈ s(q[k]'(by omega), q[k + 1]'hk) := by
      rw [hc₁]
      exact h.2
    rcases Sym2.mem_iff.mp hmem with hmem | hmem
    · have hidx := hq.2.1.getElem_inj_iff.mp hmem
      have hk1 : k = 1 := by omega
      subst k
      exact hsecond.1.2 heX
    · have hidx := hq.2.1.getElem_inj_iff.mp hmem
      have hk0 : k = 0 := by omega
      subst k
      exact hnefirst rfl
  · apply hnelast
    have heq := last_edge_unique hq (by omega) he (by rw [hc₂]; exact h.2)
    rw [getElem_eq_of_index_eq q (show q.length - 2 + 1 = q.length - 1 by omega)] at heq
    exact heq

end Workspace.ProofLemmas.Thm57Claim2TrackParity
