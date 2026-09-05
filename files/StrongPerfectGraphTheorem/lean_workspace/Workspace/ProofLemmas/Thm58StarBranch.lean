import Workspace.ProofLemmas.Thm58StarBranchGeometry
import Workspace.ProofLemmas.Thm58StarBranchGaps
import Workspace.Statements.S02.Thm_2_4

/-! Claims (2) and (6) of 5.8, with the remaining path constructions named explicitly. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT
open Thm58StarBranchBasics Thm58StarBranchGeometry Thm58StarBranchGaps

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- This is the contradiction with 2.4 used twice in the first part of claim (6). -/
theorem no_bad_link (hG : Berge G) {v a b d : V}
    (hl : VertexCanBeLinkedOntoTriangle G v a b d)
    (hna : ¬ G.Adj v a) (hnb : ¬ G.Adj v b) : False := by
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG v a b d hl with hh | hh | hh
  · exact hna hh.1
  · exact hna hh.1
  · exact hnb hh.1

variable (h : Context G m J n H K φ N F P p₁ p₂ c q)

include h

/-- Claim (2): once the star is incident with the branch, parity forces completeness
outside their unique common vertex. This gives alternative 2(a). -/
theorem incident (hcq : c ∈ q) : Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  classical
  obtain ⟨b, Q, hQ, hfrom, hQeq, hb⟩ := orient_incident h hcq
  have hQ2 : 2 ≤ Q.length := by
    have he := ThreeTracksLineGraphPrism.firstTrackEdge_mem_trackEdges (branch_two_le_length h)
    rw [← hQeq] at he
    obtain ⟨i, hi, _⟩ := he
    omega
  obtain ⟨R, r, s, hR, hRset, hinter, hlastinter⟩ := rung_intersections h hfrom hQ2
  have hRq : {x : V | x ∈ R} = edgeImage φ (trackEdges q) := by
    rw [hRset, hQeq]
  have hrmem : r ∈ N c ∩ edgeImage φ (trackEdges q) := by
    rw [← hRq, hinter]
    exact Set.mem_singleton r
  have hcomplete : ∀ x ∈ N c \ {r}, G.Adj p₁ x := by
    by_contra hn
    push Not at hn
    obtain ⟨s₂, hs₂, hns₂⟩ := hn
    obtain ⟨s₁, hs₁, has₁⟩ := first_outside_branch h
    have hs₁r : s₁ ∈ N c \ {r} :=
      ⟨hs₁.1, fun hh => hs₁.2 (hh ▸ hrmem.2)⟩
    obtain ⟨C, D, hC, hD, hparity⟩ :=
      incident_parity_gap h hcq R r s hR hRq hinter s₁ s₂ hs₁r hs₂ has₁ hns₂
    obtain ⟨u, hu⟩ := h.ready.1.1 C hC
    obtain ⟨v, hv⟩ := h.ready.1.1 D hD
    simp only [holeLength] at hu hv
    omega
  refine Or.inr ⟨c, b, Q, R, r, s, h.star, hb, hQ, hfrom, hR.1,
    hRset, hinter, hlastinter, Or.inl ⟨hcomplete, ?_, ?_⟩⟩
  · obtain ⟨x, hx, ha⟩ := last_outside_star h
    refine ⟨x, ⟨?_, ?_⟩, ha⟩
    · rw [hRq]; exact hx.1
    · exact fun hh => hx.2 (hh ▸ hrmem.1)
  · have hoverlap : N c ∩ edgeImage φ (trackEdges q) ⊆ {r} := by
      rw [← hRq, hinter]
    simpa only [hRq] using edges_except_overlap h hoverlap

/-- The two linking arguments in claim (6) leave exactly two adjacent rung neighbors. -/
theorem two_adjacent_neighbors (hcq : c ∉ q) :
    ∃ r s : V, r ∈ edgeImage φ (trackEdges q) ∧ s ∈ edgeImage φ (trackEdges q) ∧
      G.Adj r s ∧ ∀ x ∈ K, G.Adj p₂ x ↔ x = r ∨ x = s := by
  classical
  have hadj : ∀ r ∈ edgeImage φ (trackEdges q), ∀ s ∈ edgeImage φ (trackEdges q),
      r ≠ s → G.Adj p₂ r → G.Adj p₂ s → G.Adj r s := by
    intro r hr s hs hrs hpr hps
    by_contra hn
    obtain ⟨a, b, d, hl, hna, hnb⟩ :=
      separated_neighbors_link_gap h hcq r s hr hs hrs hn hpr hps
    exact no_bad_link h.ready.1 hl hna hnb
  obtain ⟨r, hr, hpr⟩ := last_outside_star h
  obtain ⟨s, hs, hps, hsr⟩ :
      ∃ s ∈ edgeImage φ (trackEdges q), G.Adj p₂ s ∧ s ≠ r := by
    by_contra hn
    have huniq : ∀ x ∈ edgeImage φ (trackEdges q), G.Adj p₂ x → x = r := by
      intro x hx hp
      by_contra hxr
      exact hn ⟨x, hx, hp, hxr⟩
    obtain ⟨a, b, d, hl, hna, hnb⟩ := singleton_link_gap h hcq r hr.1 hpr huniq
    exact no_bad_link h.ready.1 hl hna hnb
  have hrs := hadj r hr.1 s hs hsr.symm hpr hps
  refine ⟨r, s, hr.1, hs, hrs, ?_⟩
  intro x hxK
  constructor
  · intro hpx
    by_cases hxr : x = r
    · exact Or.inl hxr
    by_cases hxs : x = s
    · exact Or.inr hxs
    have hxR := last_adj_mem h hxK hpx
    rcases no_outside_triangle h hxK hr.1 hs hrs with hn | hn
    · exact (hn (hadj x hxR r hr.1 hxr hpx hpr)).elim
    · exact (hn (hadj x hxR s hs hxs hpx hps)).elim
  · rintro (rfl | rfl)
    · exact hpr
    · exact hps

/-- The last linking argument in claim (6) forces the first end to see the whole star. -/
theorem complete_star (hcq : c ∉ q) {r s : V}
    (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : G.Adj r s) (hneighbors : ∀ x ∈ K, G.Adj p₂ x ↔ x = r ∨ x = s) :
    ∀ x ∈ N c, G.Adj p₁ x := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨b, hb, hnb⟩ := hn
  obtain ⟨a₀, ha₀, hpa₀⟩ := first_outside_branch h
  obtain ⟨a, ha, hpa, hl⟩ := mixed_star_link_gap h hcq r s hr hs hrs hneighbors
    ⟨a₀, ha₀.1, hpa₀⟩ ⟨b, hb, hnb⟩
  have haK : a ∈ K := star_subset h c ha
  have hap : ¬ G.Adj a p₂ := by
    intro hap
    exact Set.disjoint_left.mp (star_disjoint_branch h hcq) ha (last_adj_mem h haK hap.symm)
  have harhs := no_outside_triangle h haK hr hs hrs
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G h.ready.1 a p₂ r s hl with hh | hh | hh
  · exact hap hh.1
  · exact hap hh.1
  · rcases harhs with hh' | hh'
    · exact hh' hh.1
    · exact hh' hh.2

/-- Claim (6): the adjacent pair is the full star of an internal vertex of the branch.
Together with completeness at `c`, this is alternative 1. -/
theorem nonincident (hcq : c ∉ q) : Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  obtain ⟨r, s, hr, hs, hrs, hneighbors⟩ := two_adjacent_neighbors h hcq
  obtain ⟨d, hd, hNd⟩ := adjacent_pair_star h hr hs hrs
  refine Or.inl ⟨c, d, no_common_branch h hcq hd,
    complete_star h hcq hr hs hrs hneighbors, ?_, ?_⟩
  · intro x hx
    apply (hneighbors x (star_subset h d hx)).mpr
    rwa [hNd] at hx
  · intro x hx y hy ha
    rcases edges_of_disjoint h (star_disjoint_branch h hcq) x hx y hy ha with hh | hh
    · exact Or.inl hh
    · refine Or.inr ⟨hh.1, ?_⟩
      rw [hNd]
      exact (hneighbors y hy).mp (hh.1 ▸ ha)

omit h in
/-- The edge-set hypotheses of the frozen local case imply the context used above. -/
theorem starBranch
    (hready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    (hc : c ∈ branchVertices H) (hq : IsBranch H q)
    (hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (φ ⟨e, he⟩ : V) ∈ attachments G (F \ {p₂}) K} ⊆ incidentEdges H c)
    (hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (φ ⟨e, he⟩ : V) ∈ attachments G (F \ {p₁}) K} ⊆ trackEdges q) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  classical
  have hfirst : attachments G (F \ {p₂}) K ⊆ N c := by
    rw [hready.2.2.2.1 c]
    exact attachments_subset_image hX₁
  have ctx : Context G m J n H K φ N F P p₁ p₂ c q :=
    ⟨hready, hc, hq, hfirst, attachments_subset_image hX₂⟩
  by_cases hcq : c ∈ q
  · exact incident ctx hcq
  · exact nonincident ctx hcq

end Workspace.ProofLemmas.Thm58StarBranch
