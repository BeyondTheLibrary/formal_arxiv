import Workspace.ProofLemmas.Thm57Claim2DeletedWindow

/-! # Applying 5.6 to the graph with the branch window removed -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2FiveSix

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup Workspace.ProofLemmas.Thm57Claim2Window
open Workspace.ProofLemmas.Thm57Claim2DeletedWindow
open Workspace.ProofLemmas.Thm57Claim2TrackParity
open Workspace.ProofLemmas.TrackSlice
open Workspace.ProofLemmas.BipartiteClosedWalkEven

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Deleting two vertices after taking an induced graph gives the same connectivity condition. -/
theorem connected_pair_induce {G : SimpleGraph W} {S : Set W} (u v : S)
    (h : ConnectedSet G (S \ {u.val, v.val})) :
    ConnectedSet (G.induce S) (({u, v} : Set S)ᶜ) := by
  intro a b
  have hmem : ∀ x : ↑(({u, v} : Set S)ᶜ), x.val.val ∈ S \ {u.val, v.val} := by
    intro x
    refine ⟨x.val.property, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff] using x.property
  have hrev : ∀ x : ↑(S \ {u.val, v.val}),
      (⟨x.val, x.property.1⟩ : S) ∈ ({u, v} : Set S)ᶜ := by
    intro x
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Subtype.ext_iff] using x.property.2
  exact (h ⟨a.val.val, hmem a⟩ ⟨b.val.val, hmem b⟩).map
    ({ toFun := fun x => ⟨⟨x.val, x.property.1⟩, hrev x⟩
       map_rel' := fun h => h } :
      G.induce (S \ {u.val, v.val}) →g
        (G.induce S).induce (({u, v} : Set S)ᶜ))

/-- PAPER: *"By 5.6 applied to `H'`, it follows that `B₁ ∪ B₂ = ∅`."*

The two connectivity assumptions are exactly the connectivity premises of 5.6. All edge
partitions, colours, and forbidden-track conditions are proved here. -/
theorem exhaustion_of_connectivity (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W))
    (hnotrack : NoEvenTrack57 H X) {B : List W} (hB : IsBranch H B) {i j : ℕ}
    (hij : i < j) (hj : j < B.length)
    (hA₁ : (ASet H X (slice B i j) B[i]).Nonempty)
    (hA₂ : (ASet H X (slice B i j) B[j]).Nonempty)
    (houtside : X \ trackEdges (slice B i j) ⊆
      incidentEdges H B[i] ∪ incidentEdges H B[j])
    (hdiff : DifferentBiparity H B[i] B[j])
    (hconn : ConnectedSet (H.deleteEdges (trackEdges (slice B i j)))
      (Outside (slice B i j) \ {B[i], B[j]}))
    (hAconn : ∀ e ∈ ASet H X (slice B i j) B[i] ∪ ASet H X (slice B i j) B[j],
      ∀ u v : W, e = s(u, v) →
        ConnectedSet (H.deleteEdges (trackEdges (slice B i j)))
          (Outside (slice B i j) \ {u, v})) :
    BSet H X (slice B i j) B[i] ∪ BSet H X (slice B i j) B[j] = ∅ := by
  classical
  let C := slice B i j
  have hC : IsTrackFrom H C B[i] B[j] := isTrackFrom_slice hB.1 hj (by omega)
  let u : Outside C := ⟨B[i], (ends_outside hC).1⟩
  let v : Outside C := ⟨B[j], (ends_outside hC).2⟩
  let A₁ : Set (Sym2 (Outside C)) := Sym2.map (Subtype.val : Outside C → W) ⁻¹' ASet H X C u.val
  let A₂ : Set (Sym2 (Outside C)) := Sym2.map (Subtype.val : Outside C → W) ⁻¹' ASet H X C v.val
  let B₁ : Set (Sym2 (Outside C)) := Sym2.map (Subtype.val : Outside C → W) ⁻¹' BSet H X C u.val
  let B₂ : Set (Sym2 (Outside C)) := Sym2.map (Subtype.val : Outside C → W) ⁻¹' BSet H X C v.val
  have hpart : ∀ c : Outside C,
      (Sym2.map (Subtype.val : Outside C → W) ⁻¹' ASet H X C c.val) ∪
        (Sym2.map (Subtype.val : Outside C → W) ⁻¹' BSet H X C c.val) = incidentEdges (outsideGraph H C) c := by
    intro c
    ext e
    rw [incident_lift_iff]
    change (((_ ∈ incidentEdges H c.val ∧ _ ∈ X) ∧ _ ∉ trackEdges C) ∨
      ((_ ∈ incidentEdges H c.val ∧ _ ∉ X) ∧ _ ∉ trackEdges C)) ↔ _
    simp only [Set.mem_diff]
    tauto
  have hdisjoint : ∀ c : Outside C,
      Disjoint (Sym2.map (Subtype.val : Outside C → W) ⁻¹' ASet H X C c.val)
        (Sym2.map (Subtype.val : Outside C → W) ⁻¹' BSet H X C c.val) := by
    intro c
    exact Set.disjoint_left.mpr (fun _ ha hb => hb.1.2 ha.1.2)
  have hAlift : ∀ c : Outside C, (ASet H X C c.val).Nonempty →
      (Sym2.map (Subtype.val : Outside C → W) ⁻¹' ASet H X C c.val).Nonempty := by
    rintro c ⟨e, he⟩
    obtain ⟨e', he'⟩ := lift_edge (outside_edge_ends hB hij hj he.1.1.1 he.2)
    exact ⟨e', by change Sym2.map (Subtype.val : Outside C → W) e' ∈ ASet H X C c.val; rwa [he']⟩
  have huA : A₁.Nonempty := hAlift u hA₁
  have hvA : A₂.Nonempty := hAlift v hA₂
  have hnadj : ¬ (outsideGraph H C).Adj u v := by
    intro h
    have h' := SimpleGraph.deleteEdges_adj.mp h
    exact h'.2 (end_edge_in_window hc3 hB hij hj h'.1)
  obtain ⟨col⟩ := exists_boolColoring_of_isBipartite hbip
  let col' : (outsideGraph H C).Coloring Bool :=
    { toFun := fun x => col x.val
      map_rel' := fun h => col.valid (SimpleGraph.deleteEdges_adj.mp h).1 }
  have hcols : col' u ≠ col' v := by
    intro h
    have heven := (even_trackLength_iff col hC).2 h
    exact (Nat.not_even_iff_odd.mpr (hdiff C hC)) heven
  have hnocover := no_common_end col' hnadj hcols huA hvA
    (fun _ h => (incident_lift_iff u _).2 ⟨h.1.1, h.2⟩)
    (fun _ h => (incident_lift_iff v _).2 ⟨h.1.1, h.2⟩)
  have hconn' : ConnectedSet (outsideGraph H C) (({u, v} : Set (Outside C))ᶜ) :=
    connected_pair_induce u v hconn
  have hAconn' : ∀ e ∈ A₁ ∪ A₂, ∀ a b : Outside C, e = s(a, b) →
      ConnectedSet (outsideGraph H C) (({a, b} : Set (Outside C))ᶜ) := by
    intro e he a b hab
    apply connected_pair_induce
    apply hAconn (Sym2.map (Subtype.val : Outside C → W) e)
    · exact he
    · rw [hab]
      rfl
  have hforbid : ∀ (a b : Outside C), DifferentBiparity H a.val b.val →
      (X \ trackEdges C ⊆ incidentEdges H a.val ∪ incidentEdges H b.val) →
      ¬ ∃ (q : List (Outside C)) (_hlen : 3 ≤ q.length),
        IsTrackList (outsideGraph H C) q ∧
        Sym2.map (Subtype.val : Outside C → W) s(q[0], q[1]) ∈ ASet H X C a.val ∧
        Sym2.map (Subtype.val : Outside C → W) s(q[1], q[2]) ∈ BSet H X C a.val ∧
        q.getLast? = some b ∧
        Sym2.map (Subtype.val : Outside C → W) s(q[q.length - 2], q[q.length - 1]) ∈ ASet H X C b.val := by
    rintro a b hdiff' hout ⟨q, hlen, hq, hf, hs, hl, he⟩
    obtain ⟨hqt, havoid⟩ := lift_track hq
    apply no_first_second_last_track hnotrack hdiff' hout (by simpa using hlen) hqt havoid
    · simpa only [List.getElem_map, Sym2.map_mk] using hf
    · simpa only [List.getElem_map, Sym2.map_mk] using hs
    · rw [List.getLast?_map, hl]
      rfl
    · simpa only [List.length_map, List.getElem_map, Sym2.map_mk] using he
  have hdiffrev : DifferentBiparity H v.val u.val := by
    intro q hq
    simpa only [trackLength, List.length_reverse] using hdiff q.reverse (isTrackFrom_reverse hq)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro e he
  have heE : e ∈ H.edgeSet ∧ e ∉ trackEdges C := by
    rcases he with he | he
    · exact ⟨he.1.1.1, he.2⟩
    · exact ⟨he.1.1.1, he.2⟩
  obtain ⟨e', he'⟩ := lift_edge (outside_edge_ends hB hij hj heE.1 heE.2)
  have hBne : B₁.Nonempty ∨ B₂.Nonempty := by
    rcases he with he | he
    · exact Or.inl ⟨e', by change Sym2.map (Subtype.val : Outside C → W) e' ∈ BSet H X C u.val; rwa [he']⟩
    · exact Or.inr ⟨e', by change Sym2.map (Subtype.val : Outside C → W) e' ∈ BSet H X C v.val; rwa [he']⟩
  rcases Workspace.Statements.S05.SPGT.thm_5_6 (outsideGraph H C) u v hnadj hconn'
      A₁ B₁ A₂ B₂ (hpart u) (hdisjoint u) (hpart v) (hdisjoint v)
      huA hvA hBne hAconn' hnocover with h | h
  · exact hforbid u v hdiff houtside h
  · exact hforbid v u hdiffrev (by simpa only [Set.union_comm] using houtside) h

end Workspace.ProofLemmas.Thm57Claim2FiveSix
