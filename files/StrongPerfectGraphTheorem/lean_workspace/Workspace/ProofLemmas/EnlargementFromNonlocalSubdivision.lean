import Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.TrackSlice

/-! Subdividing the skeleton edge added between two promoted vertices. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Workspace.ProofLemmas.EnlargementFromNonlocalSubdivision

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.NoCrossTrackBranch

/-- Once the two attachment vertices are in the skeleton, replace the new
skeleton edge by the added track and retain every old subdividing track. -/
theorem add_edge {m : ℕ} {W Z : Type*} (J : SimpleGraph (Fin m)) (H : SimpleGraph W)
    (ι : Fin m → W) (T : Fin m → Fin m → List W) (hs : SubData J H ι T)
    (a b : Fin m) (hab : a ≠ b) (hnadj : ¬ J.Adj a b)
    (D : SimpleGraph Z) (rho : W → Z) (p : List Z)
    (hext : IsBranchExtension H (ι a) (ι b) D rho p) :
    IsSubdivision (J ⊔ SimpleGraph.edge a b) D := by
  classical
  let R : Fin m → Fin m → List Z := fun u v =>
    if u = a ∧ v = b then p else if u = b ∧ v = a then p.reverse else (T u v).map rho
  have hR : R a b = p := by simp [R]
  have hRr : R b a = p.reverse := by simp [R, hab, hab.symm]
  have hRo : ∀ u v, J.Adj u v → R u v = (T u v).map rho := by
    intro u v huv
    have h1 : ¬ (u = a ∧ v = b) := by rintro ⟨rfl, rfl⟩; exact hnadj huv
    have h2 : ¬ (u = b ∧ v = a) := by rintro ⟨rfl, rfl⟩; exact hnadj huv.symm
    simp [R, h1, h2]
  have splitAdj : ∀ u v, (J ⊔ SimpleGraph.edge a b).Adj u v →
      J.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
    intro u v h
    rcases h with h | h
    · exact Or.inl h
    · rw [SimpleGraph.edge_adj] at h
      exact Or.inr h.1
  have hnedge : (J ⊔ SimpleGraph.edge a b).Adj a b :=
    Or.inr (by simp [SimpleGraph.edge_adj, hab])
  have hmaptrack : ∀ u v, J.Adj u v →
      IsTrackFrom D ((T u v).map rho) (rho (ι u)) (rho (ι v)) := by
    intro u v huv
    have h := hs.track u v huv
    refine ⟨⟨?_, h.1.2.1.map hext.inj, ?_⟩, ?_, ?_⟩
    · intro hn; exact h.1.1 (List.map_eq_nil_iff.mp hn)
    · intro i hi
      simp only [List.length_map] at hi
      simpa only [List.getElem_map] using hext.oldAdj _ _ (h.1.2.2 i hi)
    · simp only [List.head?_map, h.2.1, Option.map_some]
    · simp only [List.getLast?_map, h.2.2, Option.map_some]
  have havoid : ∀ u v, J.Adj u v → ∀ w ∈ trackInterior (T u v), rho w ∉ p := by
    intro u v huv w hw hwp
    by_cases hwi : rho w ∈ trackInterior p
    · exact hext.newInterior _ hwi ⟨w, rfl⟩
    · rcases SubdivisionCompose.mem_ends_of_mem hext.track.2.1 hext.track.2.2 hwp hwi
        with ha | hb
      · exact hs.new u v huv w hw ⟨a, (hext.inj ha).symm⟩
      · exact hs.new u v huv w hw ⟨b, (hext.inj hb).symm⟩
  have hnew : ∀ u v, (J ⊔ SimpleGraph.edge a b).Adj u v →
      ∀ z ∈ trackInterior (R u v), z ∉ Set.range (rho ∘ ι) := by
    intro u v huv z hz ⟨w, hw⟩
    rcases splitAdj u v huv with ho | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hRo u v ho, trackInterior_map] at hz
      obtain ⟨x, hx, he⟩ := List.mem_map.mp hz
      exact hs.new u v ho x hx ⟨w, hext.inj (hw.trans he.symm)⟩
    · rw [hR] at hz
      exact hext.newInterior z hz ⟨ι w, hw⟩
    · rw [hRr, TrackSlice.trackInterior_reverse, List.mem_reverse] at hz
      exact hext.newInterior z hz ⟨ι w, hw⟩
  refine ⟨rho ∘ ι, R, hext.inj.comp hs.inj, ?_, ?_, ?_, ?_, hnew, ?_, ?_⟩
  · intro u v huv
    rcases splitAdj u v huv with ho | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hRo u v ho]; exact hmaptrack u v ho
    · rw [hR]; exact hext.track
    · rw [hRr]; exact TrackSlice.isTrackFrom_reverse hext.track
  · intro u v huv
    rcases splitAdj u v huv with ho | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa only [hRo u v ho, trackLength, List.length_map] using hs.len u v ho
    · rw [hR]; have := hext.length; dsimp only [trackLength]; omega
    · rw [hRr]; have := hext.length; simp only [trackLength, List.length_reverse]; omega
  · intro u v huv
    rcases splitAdj u v huv with ho | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hRo u v ho, hRo v u ho.symm, hs.rev u v ho, List.map_reverse]
    · rw [hR, hRr]
    · rw [hR, hRr, List.reverse_reverse]
  · intro u v u' v' huv huv' hne z hz hz'
    rcases splitAdj u v huv with ho | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hRo u v ho, trackInterior_map] at hz
      obtain ⟨w, hw, he⟩ := List.mem_map.mp hz
      subst z
      rcases splitAdj u' v' huv' with ho' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hRo u' v' ho'] at hz'
        obtain ⟨w', hw', he'⟩ := List.mem_map.mp hz'
        exact hs.disj u v u' v' ho ho' hne w hw ((hext.inj he') ▸ hw')
      · rw [hR] at hz'; exact havoid u v ho w hw hz'
      · rw [hRr, List.mem_reverse] at hz'; exact havoid u v ho w hw hz'
    · rw [hR] at hz
      rcases splitAdj u' v' huv' with ho' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hRo u' v' ho'] at hz'
        obtain ⟨w, _, hw⟩ := List.mem_map.mp hz'
        exact hext.newInterior z hz ⟨w, hw⟩
      · exact hne rfl
      · exact hne Sym2.eq_swap
    · rw [hRr, TrackSlice.trackInterior_reverse, List.mem_reverse] at hz
      rcases splitAdj u' v' huv' with ho' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hRo u' v' ho'] at hz'
        obtain ⟨w, _, hw⟩ := List.mem_map.mp hz'
        exact hext.newInterior z hz ⟨w, hw⟩
      · exact hne Sym2.eq_swap
      · exact hne rfl
  · intro z
    rcases hext.cover z with ⟨w, rfl⟩ | hz
    · rcases hs.cover w with ⟨u, rfl⟩ | ⟨u, v, huv, hw⟩
      · exact Or.inl ⟨u, rfl⟩
      · right
        refine ⟨u, v, Or.inl huv, ?_⟩
        rw [hRo u v huv, trackInterior_map]
        exact List.mem_map.mpr ⟨w, hw, rfl⟩
    · right
      exact ⟨a, b, hnedge, by rwa [hR]⟩
  · ext e
    rw [hext.edges]
    simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro (⟨f, hf, he⟩ | he)
      · rw [hs.edges] at hf
        simp only [Set.mem_iUnion] at hf
        obtain ⟨u, v, huv, hf⟩ := hf
        refine ⟨u, v, Or.inl huv, ?_⟩
        rw [hRo u v huv, trackEdges_map]
        exact ⟨f, hf, he⟩
      · exact ⟨a, b, hnedge, by rwa [hR]⟩
    · rintro ⟨u, v, huv, he⟩
      rcases splitAdj u v huv with ho | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        rw [hRo u v ho, trackEdges_map] at he
        obtain ⟨f, hf, he⟩ := he
        refine ⟨f, ?_, he⟩
        rw [hs.edges]
        exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨ho, hf⟩⟩⟩
      · right; rwa [hR] at he
      · right; rwa [hRr, trackEdges_reverse] at he

end Workspace.ProofLemmas.EnlargementFromNonlocalSubdivision
