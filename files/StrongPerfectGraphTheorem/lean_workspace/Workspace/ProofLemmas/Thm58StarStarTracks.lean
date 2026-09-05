import Workspace.ProofLemmas.Thm58StarStarHoles
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# From tracks of `H` to completions in the star--star case of 5.8

Claims (3) and (4) of 5.8 both produce their two paths of `L(H)` from tracks of `H`: the first
one runs from `v₁` to `v₂`, and the second one (the output of 5.6) reaches `v₁` only at its
second vertex, its first edge lying in `A₁` and its second edge in `B₁`.  This file turns such
a track into a `Thm58StarStarHoles.Completion`, and reads the paper's *"since `H` is bipartite,
`S₁` and `S₂` have opposite parity"* off a two-colouring of `H`.

The dictionary is the same in both cases: a vertex of the rung of a track lying in the star of
an *end* of the track is the corresponding end of the rung, and a vertex of the rung lying in
the star of the *second vertex* of the track is one of the first two vertices of the rung.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarTracks

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles
open ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ : Fin n}

/-! ## The second edge of a track -/

/-- The second edge of a track on at least three vertices. -/
def secondTrackEdge (Q : List (Fin n)) (h3 : 3 ≤ Q.length) : Sym2 (Fin n) :=
  s(Q[1]'(by omega), Q[2]'(by omega))

theorem secondTrackEdge_mem {Q : List (Fin n)} (hQ : IsTrackList H Q) (h3 : 3 ≤ Q.length) :
    secondTrackEdge Q h3 ∈ H.edgeSet := hQ.2.2 1 (by omega)

theorem secondTrackEdge_mem_trackEdges {Q : List (Fin n)} (h3 : 3 ≤ Q.length) :
    secondTrackEdge Q h3 ∈ trackEdges Q := ⟨1, by omega, rfl⟩

/-- The vertex of `L(H)` given by the second edge of a track. -/
def secondRungVertex (φ : H.lineGraph ≃g G.induce K) (Q : List (Fin n))
    (hQ : IsTrackList H Q) (h3 : 3 ≤ Q.length) : V :=
  (φ ⟨secondTrackEdge Q h3, secondTrackEdge_mem hQ h3⟩ : V)

/-! ## The star dictionary along a rung -/

/-- A vertex of the rung of `Q` lying in the star of the first end of `Q` is the first vertex
of the rung. -/
theorem eq_firstRungVertex (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {Q : List (Fin n)} {a b : Fin n} (hfrom : IsTrackFrom H Q a b) (h2 : 2 ≤ Q.length)
    {x : V} (hx : x ∈ N a) (hxR : x ∈ trackRung φ Q hfrom.1) :
    x = firstRungVertex φ Q hfrom.1 h2 := by
  rw [hstar a] at hx
  obtain ⟨e, he, hea, rfl⟩ := hx
  obtain ⟨f, hf, hfQ, hxf⟩ := (mem_trackRung_iff φ hfrom.1).mp hxR
  have hef : e = f := congrArg Subtype.val (φ.injective (Subtype.ext hxf))
  have hE : e = firstTrackEdge Q h2 :=
    edge_eq_firstTrackEdge hfrom h2 (hef ▸ hfQ) hea.2
  exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hE)

/-- A vertex of the rung of `Q` lying in the star of the last end of `Q` is the last vertex of
the rung. -/
theorem eq_lastRungVertex (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {Q : List (Fin n)} {a b : Fin n} (hfrom : IsTrackFrom H Q a b) (h2 : 2 ≤ Q.length)
    {x : V} (hx : x ∈ N b) (hxR : x ∈ trackRung φ Q hfrom.1) :
    x = lastRungVertex φ Q hfrom.1 h2 := by
  rw [hstar b] at hx
  obtain ⟨e, he, heb, rfl⟩ := hx
  obtain ⟨f, hf, hfQ, hxf⟩ := (mem_trackRung_iff φ hfrom.1).mp hxR
  have hef : e = f := congrArg Subtype.val (φ.injective (Subtype.ext hxf))
  have hE : e = lastTrackEdge Q h2 :=
    edge_eq_lastTrackEdge hfrom h2 (hef ▸ hfQ) heb.2
  exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hE)

/-- The first vertex of the rung lies in the star of the first end of the track. -/
theorem firstRungVertex_mem_star (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {Q : List (Fin n)} {a b : Fin n} (hfrom : IsTrackFrom H Q a b) (h2 : 2 ≤ Q.length) :
    firstRungVertex φ Q hfrom.1 h2 ∈ N a := by
  rw [hstar a]
  exact ⟨firstTrackEdge Q h2, firstTrackEdge_mem hfrom.1 h2,
    ⟨firstTrackEdge_mem hfrom.1 h2, firstTrackEdge_contains hfrom h2⟩, rfl⟩

/-- The last vertex of the rung lies in the star of the last end of the track. -/
theorem lastRungVertex_mem_star (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {Q : List (Fin n)} {a b : Fin n} (hfrom : IsTrackFrom H Q a b) (h2 : 2 ≤ Q.length) :
    lastRungVertex φ Q hfrom.1 h2 ∈ N b := by
  rw [hstar b]
  exact ⟨lastTrackEdge Q h2, lastTrackEdge_mem hfrom.1 h2,
    ⟨lastTrackEdge_mem hfrom.1 h2, lastTrackEdge_contains hfrom h2⟩, rfl⟩

/-- A vertex of the rung lying in the star of the *second* vertex of the track is one of the
first two vertices of the rung: the second vertex of the track lies on exactly the first two
edges of the track. -/
theorem eq_first_or_second (hstar : ∀ d : Fin n, N d = edgeImage φ (incidentEdges H d))
    {Q : List (Fin n)} (hQ : IsTrackList H Q) (h3 : 3 ≤ Q.length)
    {x : V} (hx : x ∈ N (Q[1]'(by omega))) (hxR : x ∈ trackRung φ Q hQ) :
    x = firstRungVertex φ Q hQ (by omega) ∨ x = secondRungVertex φ Q hQ h3 := by
  rw [hstar (Q[1]'(by omega))] at hx
  obtain ⟨e, he, hea, rfl⟩ := hx
  obtain ⟨f, hf, hfQ, hxf⟩ := (mem_trackRung_iff φ hQ).mp hxR
  have hef : e = f := congrArg Subtype.val (φ.injective (Subtype.ext hxf))
  obtain ⟨i, hi, hie⟩ := hef ▸ hfQ
  have hnd : Q.Nodup := hQ.2.1
  have hmem : Q[1]'(by omega) ∈ e := hea.2
  rw [hie] at hmem
  have hcase : (1 : ℕ) = i ∨ (1 : ℕ) = i + 1 := by
    rcases Sym2.mem_iff.mp hmem with hh | hh
    · exact Or.inl (hnd.getElem_inj_iff.mp hh)
    · exact Or.inr (hnd.getElem_inj_iff.mp hh)
  rcases hcase with hc | hc
  · refine Or.inr ?_
    subst hc
    exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hie)
  · refine Or.inl ?_
    have hi0 : i = 0 := by omega
    subst hi0
    exact congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hie)

/-! ## Completions built from tracks -/

variable (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

/-- A track ending at `c₂`, whose rung starts at a neighbour of `p₁` in the first star and ends
at a neighbour of `p₂`, is a completion in the sense of `Thm58StarStarHoles.Completion`. -/
theorem completion_of_rung {Q : List (Fin n)} {u : Fin n}
    (hfrom : IsTrackFrom H Q u c₂) (h2 : 2 ≤ Q.length)
    (hfirst₁ : firstRungVertex φ Q hfrom.1 h2 ∈ N c₁)
    (hadj₁ : G.Adj p₁ (firstRungVertex φ Q hfrom.1 h2))
    (hadj₂ : G.Adj p₂ (lastRungVertex φ Q hfrom.1 h2))
    (honly : ∀ x ∈ trackRung φ Q hfrom.1, x ∈ N c₁ → G.Adj p₁ x →
      x = firstRungVertex φ Q hfrom.1 h2)
    (havoid : ∀ x ∈ trackRung φ Q hfrom.1, x ∉ N c₁ ∩ N c₂) :
    Completion G K (N c₁ ∩ N c₂) p₁ p₂ (trackRung φ Q hfrom.1)
      (firstRungVertex φ Q hfrom.1 h2) (lastRungVertex φ Q hfrom.1 h2) := by
  refine ⟨trackRung_isPathFrom_ends φ hfrom h2, trackRung_subset_K φ Q hfrom.1,
    hadj₁, hadj₂, ?_, ?_, havoid, ?_⟩
  · intro x hx hadj
    exact honly x hx (first_adj_mem h (trackRung_subset_K φ Q hfrom.1 x hx) hadj) hadj
  · intro x hx hadj
    exact eq_lastRungVertex (star_eq h) hfrom h2
      (last_adj_mem h (trackRung_subset_K φ Q hfrom.1 x hx) hadj) hx
  · intro hcon
    refine havoid _ (firstRungVertex_mem φ hfrom.1 h2) ⟨hfirst₁, ?_⟩
    rw [hcon]
    exact lastRungVertex_mem_star (star_eq h) hfrom h2


/-- PAPER, proof of 5.8 (3) and (4): *"since `H` is bipartite, `S₁` and `S₂` have opposite
parity"*.  The first track joins `c₁` to `c₂`; the second one joins a neighbour `u` of `c₁` to
`c₂`, so the two lengths differ by one modulo two. -/
theorem opposite_parity {Q₁ Q₂ : List (Fin n)} {u : Fin n}
    (hQ₁ : IsTrackFrom H Q₁ c₁ c₂) (hQ₂ : IsTrackFrom H Q₂ u c₂) (hadj : H.Adj u c₁) :
    trackLength Q₁ % 2 ≠ trackLength Q₂ % 2 := by
  obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite h.ready.2.2.1.2
  have h₁ := BipartiteClosedWalkEven.even_trackLength_iff col hQ₁
  have h₂ := BipartiteClosedWalkEven.even_trackLength_iff col hQ₂
  have hne : col u ≠ col c₁ := col.valid hadj
  simp only [Nat.even_iff] at h₁ h₂
  rcases hb₁ : col c₁ <;> rcases hb₂ : col c₂ <;> rcases hbu : col u <;>
    simp only [hb₁, hb₂, hbu] at h₁ h₂ hne <;> simp_all


/-! ## The two tracks of the paper, in either orientation -/

/-- The data of the two tracks that claims (3) and (4) produce: a track `Q₁` from `c₁` to `c₂`
whose first edge is a neighbour of `p₁` and whose last edge is a neighbour of `p₂`, and a track
`Q₂` reaching `c₁` at its second vertex and `c₂` at its last, whose first edge is again a
neighbour of `p₁`, whose second edge is *not* (the paper's `B₁`), and whose last edge is a
neighbour of `p₂`.  Both tracks avoid the edge set `E`, which is empty in claim (3) and the
branch between the two star vertices in claim (4). -/
def TracksFound (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (p₁ p₂ : V) (c₁ c₂ : Fin n)
    (E : Set (Sym2 (Fin n))) : Prop :=
  ∃ (Q₁ Q₂ : List (Fin n)) (u : Fin n) (h₁ : 2 ≤ Q₁.length) (h₂ : 3 ≤ Q₂.length)
    (hQ₁ : IsTrackFrom H Q₁ c₁ c₂) (hQ₂ : IsTrackFrom H Q₂ u c₂),
    Q₂[1]'(by omega) = c₁ ∧
    (∀ e ∈ trackEdges Q₁, e ∉ E) ∧ (∀ e ∈ trackEdges Q₂, e ∉ E) ∧
    G.Adj p₁ (firstRungVertex φ Q₁ hQ₁.1 h₁) ∧
    G.Adj p₂ (lastRungVertex φ Q₁ hQ₁.1 h₁) ∧
    G.Adj p₁ (firstRungVertex φ Q₂ hQ₂.1 (by omega)) ∧
    ¬ G.Adj p₁ (secondRungVertex φ Q₂ hQ₂.1 h₂) ∧
    G.Adj p₂ (lastRungVertex φ Q₂ hQ₂.1 (by omega))

/-- The star--star hypotheses are symmetric in the two ends of the outside path. -/
theorem context_swap : Context G m J n H K φ N F P.reverse p₂ p₁ c₂ c₁ :=
  ⟨Thm58BranchBranch.ready_reverse h.ready, h.star₂, h.star₁, h.last, h.first⟩

/-- The two tracks give two completions of opposite parity. -/
theorem completions_of_tracks {E : Set (Sym2 (Fin n))}
    (hE : N c₁ ∩ N c₂ ⊆ edgeImage φ E) (ht : TracksFound G H K φ p₁ p₂ c₁ c₂ E) :
    ∃ (S₁ S₂ : List V) (a₁ a₂ b₁ b₂ : V),
      Completion G K (N c₁ ∩ N c₂) p₁ p₂ S₁ a₁ a₂ ∧
      Completion G K (N c₁ ∩ N c₂) p₁ p₂ S₂ b₁ b₂ ∧
      S₁.length % 2 ≠ S₂.length % 2 := by
  classical
  obtain ⟨Q₁, Q₂, u, h₁, h₂, hQ₁, hQ₂, hc, hd₁, hd₂, hp₁₁, hp₂₁, hp₁₂, hnp, hp₂₂⟩ := ht
  have h₂' : 2 ≤ Q₂.length := by omega
  have havoid : ∀ (Q : List (Fin n)) (hQ : IsTrackList H Q),
      (∀ e ∈ trackEdges Q, e ∉ E) → ∀ x ∈ trackRung φ Q hQ, x ∉ N c₁ ∩ N c₂ := by
    intro Q hQ hdisj x hx hmem
    obtain ⟨f, hf, hfQ, rfl⟩ := (mem_trackRung_iff φ hQ).mp hx
    exact hdisj f hfQ ((image_mem_iff hf).mp (hE hmem))
  have hfirst₂ : firstRungVertex φ Q₂ hQ₂.1 h₂' ∈ N c₁ := by
    rw [star_eq h c₁]
    refine ⟨firstTrackEdge Q₂ h₂', firstTrackEdge_mem hQ₂.1 h₂',
      ⟨firstTrackEdge_mem hQ₂.1 h₂', ?_⟩, rfl⟩
    rw [← hc]
    exact Sym2.mem_mk_right _ _
  refine ⟨trackRung φ Q₁ hQ₁.1, trackRung φ Q₂ hQ₂.1,
    firstRungVertex φ Q₁ hQ₁.1 h₁, lastRungVertex φ Q₁ hQ₁.1 h₁,
    firstRungVertex φ Q₂ hQ₂.1 h₂', lastRungVertex φ Q₂ hQ₂.1 h₂', ?_, ?_, ?_⟩
  · exact completion_of_rung h hQ₁ h₁ (firstRungVertex_mem_star (star_eq h) hQ₁ h₁) hp₁₁ hp₂₁
      (fun x hx hxN _ => eq_firstRungVertex (star_eq h) hQ₁ h₁ hxN hx) (havoid _ _ hd₁)
  · refine completion_of_rung h hQ₂ h₂' hfirst₂ hp₁₂ hp₂₂ ?_ (havoid _ _ hd₂)
    intro x hx hxN hadj
    have hxN' : x ∈ N (Q₂[1]'(by omega)) := by rw [hc]; exact hxN
    rcases eq_first_or_second (star_eq h) hQ₂.1 h₂ hxN' hx with hfirst | hsecond
    · exact hfirst
    · exact absurd (hsecond ▸ hadj) hnp
  · have hu : H.Adj u c₁ := by
      have h0 : Q₂[0]'(by omega) = u := PathBasics.getElem_zero_of_head? hQ₂.2.1 (by omega)
      have hadj := hQ₂.1.2.2 0 (by omega)
      rw [h0, hc] at hadj
      exact hadj
    rw [trackRung_length, trackRung_length]
    exact opposite_parity h hQ₁ hQ₂ hu

/-- PAPER, proof of 5.8 (3) and (4): *"(possibly after exchanging `v₁` and `v₂`) ... `S₁` and
`S₂` have opposite parity; but they can both be completed via `F`, a contradiction."*  The
exchange of `v₁` and `v₂` exchanges the two ends of the outside path as well, and either
orientation produces the two holes. -/
theorem holes_of_tracks {E : Set (Sym2 (Fin n))}
    (hE : N c₁ ∩ N c₂ ⊆ edgeImage φ E)
    (ht : TracksFound G H K φ p₁ p₂ c₁ c₂ E ∨ TracksFound G H K φ p₂ p₁ c₂ c₁ E) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  rcases ht with ht | ht
  · obtain ⟨S₁, S₂, a₁, a₂, b₁, b₂, hc₁, hc₂, hpar⟩ := completions_of_tracks h hE ht
    exact holes_of_completions h hc₁ hc₂ hpar
  · have h' := context_swap h
    have hE' : N c₂ ∩ N c₁ ⊆ edgeImage φ E := by
      rw [Set.inter_comm]; exact hE
    obtain ⟨S₁, S₂, a₁, a₂, b₁, b₂, hc₁, hc₂, hpar⟩ := completions_of_tracks h' hE' ht
    exact holes_of_completions h' hc₁ hc₂ hpar


end Workspace.ProofLemmas.Thm58StarStarTracks
