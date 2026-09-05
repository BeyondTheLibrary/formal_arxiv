import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.Thm57Claim2TrackParity
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.Statements.S05.Thm_5_6

/-! # Removing the branch window in 5.7 (2) -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2DeletedWindow

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup Workspace.ProofLemmas.Thm57Claim2Window
open Workspace.ProofLemmas.Thm57Claim2Structure Workspace.ProofLemmas.Thm57Claim2TrackParity
open Workspace.ProofLemmas.TrackSlice Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The vertices that remain when the interior of `C` is removed. -/
def Outside (C : List W) : Set W := {v | v ∉ trackInterior C}

/-- The paper's `H'`: remove the edges and internal vertices of `C`. -/
def outsideGraph (H : SimpleGraph W) (C : List W) : SimpleGraph (Outside C) :=
  (H.deleteEdges (trackEdges C)).induce (Outside C)

/-- Neither end of a track is an internal vertex. -/
theorem ends_outside {H : SimpleGraph W} {C : List W} {c₁ c₂ : W}
    (hC : IsTrackFrom H C c₁ c₂) : c₁ ∈ Outside C ∧ c₂ ∈ Outside C := by
  have hpos : 0 < C.length := List.length_pos_of_ne_nil hC.1.1
  have hh := track_head hC hpos
  have hl : C[C.length - 1]'(by omega) = c₂ := by
    have h := hC.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  constructor
  · intro h
    obtain ⟨k, hk, hkc⟩ := (mem_trackInterior_iff C c₁).mp h
    have hi := hC.1.2.1.getElem_inj_iff.mp (hkc.trans hh.symm)
    omega
  · intro h
    obtain ⟨k, hk, hkc⟩ := (mem_trackInterior_iff C c₂).mp h
    have hi := hC.1.2.1.getElem_inj_iff.mp (hkc.trans hl.symm)
    omega

/-- Every edge at an internal vertex of the window is an edge of the window. -/
theorem internal_incident_subset {H : SimpleGraph W} {B : List W} (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length) {w : W}
    (hw : w ∈ trackInterior (slice B i j)) :
    incidentEdges H w ⊆ trackEdges (slice B i j) := by
  obtain ⟨k, hk, hik, hkj, hkw⟩ := (mem_trackInterior_slice_iff hj (by omega)).mp hw
  intro e he
  have heB := incidentEdges_internal_subset hB (show 0 < k by omega)
    (show k + 1 < B.length by omega) (a := e) (by rwa [hkw])
  obtain ⟨l, hl, hel⟩ := heB
  have hmem : B[k]'hk ∈ s(B[l]'(by omega), B[l + 1]'hl) := by
    rw [hkw, ← hel]
    exact he.2
  have hkcase : k = l ∨ k = l + 1 := by
    rcases Sym2.mem_iff.mp hmem with h | h
    · exact Or.inl (hB.1.2.1.getElem_inj_iff.mp h)
    · exact Or.inr (hB.1.2.1.getElem_inj_iff.mp h)
  have hlen := length_slice B hj (show i ≤ j by omega)
  refine ⟨l - i, by omega, ?_⟩
  rw [getElem_slice B (by omega) (by omega), getElem_slice B (by omega) (by omega),
    getElem_eq_of_index_eq B (show i + (l - i) = l by omega),
    getElem_eq_of_index_eq B (show i + (l - i + 1) = l + 1 by omega)]
  exact hel

/-- Edges outside the window have both ends among the remaining vertices. -/
theorem outside_edge_ends {H : SimpleGraph W} {B : List W} (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length) {e : Sym2 W}
    (he : e ∈ H.edgeSet) (heC : e ∉ trackEdges (slice B i j)) :
    ∀ w ∈ e, w ∈ Outside (slice B i j) := by
  intro w hw hint
  exact heC (internal_incident_subset hB hij hj hint ⟨he, hw⟩)

/-- An edge joining the two ends of the window must itself belong to the window. -/
theorem end_edge_in_window {H : SimpleGraph W} (hc3 : CyclicallyThreeConnected H)
    {B : List W} (hB : IsBranch H B) {i j : ℕ} (hij : i < j) (hj : j < B.length)
    (hadj : H.Adj B[i] B[j]) : s(B[i], B[j]) ∈ trackEdges (slice B i j) := by
  have hed : s(B[i], B[j]) ∈ trackEdges B := by
    by_cases hi : i = 0
    · by_cases hjend : j = B.length - 1
      · by_cases hlen : B.length = 2
        · have hij' : j = i + 1 := by omega
          refine ⟨i, by omega, ?_⟩
          rw [getElem_eq_of_index_eq B hij']
        · obtain ⟨n, J, hJ, hsub⟩ := hc3
          have hends := Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
            J hJ H hsub B B[0] B[B.length - 1] hB
            (branch_from_ends hB (by omega)) (by unfold trackLength; omega)
          exact (hends.2.2.2 (by simpa [hi, hjend] using hadj)).elim
      · exact incidentEdges_internal_subset hB (by omega) (by omega)
          ⟨hadj, Sym2.mem_mk_right _ _⟩
    · exact incidentEdges_internal_subset hB (by omega) (by omega)
        ⟨hadj, Sym2.mem_mk_left _ _⟩
  obtain ⟨k, hk, heq⟩ := hed
  have hij' : j = i + 1 := by
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := hB.1.2.1.getElem_inj_iff.mp h1
      have := hB.1.2.1.getElem_inj_iff.mp h2
      omega
    · have := hB.1.2.1.getElem_inj_iff.mp h1
      have := hB.1.2.1.getElem_inj_iff.mp h2
      omega
  have hlen := length_slice B hj (show i ≤ j by omega)
  refine ⟨0, by omega, ?_⟩
  rw [getElem_slice B (by omega) (by omega), getElem_slice B (by omega) (by omega),
    getElem_eq_of_index_eq B (show i + 0 = i by omega),
    getElem_eq_of_index_eq B (show i + (0 + 1) = j by omega)]

/-- The incident edges of `H'`, read as edges of `H`. -/
theorem incident_lift_iff {H : SimpleGraph W} {C : List W} (c : Outside C)
    (e : Sym2 (Outside C)) :
    e ∈ incidentEdges (outsideGraph H C) c ↔
      Sym2.map Subtype.val e ∈ incidentEdges H c.val \ trackEdges C := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [incidentEdges, Set.mem_setOf_eq, Set.mem_diff, SimpleGraph.mem_edgeSet,
      outsideGraph, SimpleGraph.induce_adj, SimpleGraph.deleteEdges_adj, Sym2.map_mk,
      Sym2.mem_iff, Subtype.ext_iff]
    tauto

/-- An edge whose ends remain in the graph lifts to the induced vertex type. -/
theorem lift_edge {C : List W} {e : Sym2 W} (he : ∀ w ∈ e, w ∈ Outside C) :
    ∃ e' : Sym2 (Outside C), Sym2.map Subtype.val e' = e := by
  induction e using Sym2.ind with
  | _ u v =>
    exact ⟨s(⟨u, he u (by simp)⟩, ⟨v, he v (by simp)⟩), rfl⟩

/-- A track in `H'` lifts to a track of `H` using no edge of `C`. -/
theorem lift_track {H : SimpleGraph W} {C : List W} {q : List (Outside C)}
    (hq : IsTrackList (outsideGraph H C) q) :
    IsTrackList H (q.map Subtype.val) ∧
      Disjoint (trackEdges (q.map Subtype.val)) (trackEdges C) := by
  have hstep : ∀ k (hk : k + 1 < q.length),
      H.Adj (q[k]'(by omega)).val (q[k + 1]'hk).val ∧
      s((q[k]'(by omega)).val, (q[k + 1]'hk).val) ∉ trackEdges C := by
    intro k hk
    exact SimpleGraph.deleteEdges_adj.mp (hq.2.2 k hk)
  constructor
  · refine ⟨by intro h; exact hq.1 (List.map_eq_nil_iff.mp h), hq.2.1.map Subtype.val_injective, ?_⟩
    intro k hk
    simpa only [List.getElem_map] using (hstep k (by simpa using hk)).1
  · apply Set.disjoint_left.mpr
    rintro e ⟨k, hk, rfl⟩ heC
    apply (hstep k (by simpa using hk)).2
    simpa only [List.getElem_map] using heC

/-- Opposite colours and nonadjacency rule out one vertex meeting every edge in the two
nonempty stars. This is the paper's *"no vertex ... is incident with all edges in `A₁ ∪ A₂`"*. -/
theorem no_common_end {U : Type*} {G : SimpleGraph U} (col : G.Coloring Bool)
    {u v : U} (hnadj : ¬ G.Adj u v) (hcol : col u ≠ col v)
    {A₁ A₂ : Set (Sym2 U)} (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hsub₁ : A₁ ⊆ incidentEdges G u) (hsub₂ : A₂ ⊆ incidentEdges G v) :
    ¬ ∃ w, ∀ e ∈ A₁ ∪ A₂, w ∈ e := by
  rintro ⟨w, hw⟩
  obtain ⟨e₁, he₁⟩ := hA₁
  obtain ⟨e₂, he₂⟩ := hA₂
  have huv : u ≠ v := fun h => hcol (congrArg col h)
  have hwu : w ≠ u := by
    intro h
    have heq := (Sym2.mem_and_mem_iff huv).mp
      ⟨h ▸ hw e₂ (Or.inr he₂), (hsub₂ he₂).2⟩
    exact hnadj (by simpa [heq] using (hsub₂ he₂).1)
  have hwv : w ≠ v := by
    intro h
    have heq := (Sym2.mem_and_mem_iff huv).mp
      ⟨(hsub₁ he₁).2, h ▸ hw e₁ (Or.inl he₁)⟩
    exact hnadj (by simpa [heq] using (hsub₁ he₁).1)
  have heq₁ := (Sym2.mem_and_mem_iff hwu.symm).mp
    ⟨(hsub₁ he₁).2, hw e₁ (Or.inl he₁)⟩
  have heq₂ := (Sym2.mem_and_mem_iff hwv.symm).mp
    ⟨(hsub₂ he₂).2, hw e₂ (Or.inr he₂)⟩
  have hc₁ := col.valid (show G.Adj u w by simpa [heq₁] using (hsub₁ he₁).1)
  have hc₂ := col.valid (show G.Adj v w by simpa [heq₂] using (hsub₂ he₂).1)
  exact hcol (by cases hcu : col u <;> cases hcv : col v <;> cases hcw : col w <;> simp_all)

end Workspace.ProofLemmas.Thm57Claim2DeletedWindow
