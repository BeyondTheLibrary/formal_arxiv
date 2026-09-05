import Workspace.ProofLemmas.EnlargementFromNonlocalCycle
import Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-! Checking the new track's parity against an old track. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.EnlargementFromNonlocalParity

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
open Workspace.ProofLemmas.SubdivisionCounting

/-- The only common vertices of the old track and the added track are their
ends. Their edge lists form a hole, so the Berge hypothesis fixes the new parity. -/
theorem extension_parity {V W Z : Type*} {G : SimpleGraph V} (hG : Berge G)
    {H : SimpleGraph W} {D : SimpleGraph Z} {a b : W}
    {rho : W → Z} {p : List Z} {r : List W}
    (hext : IsBranchExtension H a b D rho p) (hnadj : ¬ H.Adj a b)
    (hr : IsTrackFrom H r a b) (hrlen : 3 ≤ trackLength r)
    {K : Set V} (φ : D.lineGraph ≃g G.induce K) (col : H.Coloring Bool) :
    Even (trackLength p) ↔ col a = col b := by
  have hrD : IsTrackFrom D (r.map rho) (rho a) (rho b) := by
    refine ⟨⟨?_, hr.1.2.1.map hext.inj, ?_⟩, ?_, ?_⟩
    · intro hn
      exact hr.1.1 (List.map_eq_nil_iff.mp hn)
    · intro i hi
      simp only [List.length_map] at hi
      simpa only [List.getElem_map] using hext.oldAdj _ _ (hr.1.2.2 i hi)
    · simp only [List.head?_map, hr.2.1, Option.map_some]
    · simp only [List.getLast?_map, hr.2.2, Option.map_some]
  have hmeet : ∀ z ∈ p, z ∈ r.map rho → z = rho a ∨ z = rho b := by
    intro z hz hzr
    apply SubdivisionCompose.mem_ends_of_mem hext.track.2.1 hext.track.2.2 hz
    intro hzi
    obtain ⟨w, _, hw⟩ := List.mem_map.mp hzr
    exact hext.newInterior z hzi ⟨w, hw⟩
  have edge_vertex : ∀ {l : List Z} {e : Sym2 Z}, e ∈ trackEdges l →
      ∀ z ∈ e, z ∈ l := by
    rintro l e ⟨i, hi, rfl⟩ z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl <;> exact List.getElem_mem _
  have hdisj : Disjoint (trackEdges p) (trackEdges (r.map rho)) := by
    rw [Set.disjoint_left, trackEdges_map]
    rintro e hep ⟨f, hfr, hfe⟩
    induction f using Sym2.ind with
    | _ u v =>
      have heq : s(rho u, rho v) = e := hfe
      have hfr' : H.Adj u v := by
        obtain ⟨i, hi, he⟩ := hfr
        rcases Sym2.eq_iff.mp he with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · rw [hu, hv]
          exact hr.1.2.2 i hi
        · rw [hu, hv]
          exact (hr.1.2.2 i hi).symm
      have hu : rho u = rho a ∨ rho u = rho b :=
        hmeet (rho u) (edge_vertex hep _ (heq ▸ Sym2.mem_mk_left _ _))
          (edge_vertex (show e ∈ trackEdges (r.map rho) by
            rw [trackEdges_map]; exact ⟨s(u, v), hfr, hfe⟩) _
            (heq ▸ Sym2.mem_mk_left _ _))
      have hv : rho v = rho a ∨ rho v = rho b :=
        hmeet (rho v) (edge_vertex hep _ (heq ▸ Sym2.mem_mk_right _ _))
          (edge_vertex (show e ∈ trackEdges (r.map rho) by
            rw [trackEdges_map]; exact ⟨s(u, v), hfr, hfe⟩) _
            (heq ▸ Sym2.mem_mk_right _ _))
      have hu' : u = a ∨ u = b := hu.imp (fun h => hext.inj h) (fun h => hext.inj h)
      have hv' : v = a ∨ v = b := hv.imp (fun h => hext.inj h) (fun h => hext.inj h)
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact H.irrefl hfr'
      · exact hnadj hfr'
      · exact hnadj hfr'.symm
      · exact H.irrefl hfr'
  have hp2 := hext.length
  have hr2 : 2 ≤ (r.map rho).length := by
    simp only [List.length_map]
    dsimp only [trackLength] at hrlen
    omega
  have hsum := EnlargementFromNonlocalCycle.even_sum hG φ hext.track hrD hp2 hr2
    hdisj hmeet (by simp only [trackLength, List.length_map] at *; omega)
  have hsame : Even (trackLength p) ↔ Even (trackLength r) := by
    simp only [Nat.even_iff, trackLength, List.length_map] at hsum ⊢
    omega
  exact hsame.trans (BipartiteClosedWalkEven.even_trackLength_iff col hr)

end Workspace.ProofLemmas.EnlargementFromNonlocalParity
