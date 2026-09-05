import Workspace.Types.Core
import Workspace.ProofLemmas.ColoringCliqueSandwich

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- Every finite bipartite simple graph is perfect. -/
theorem BipartitePerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (hK : K.IsBipartite) :
    SPGT.IsPerfect K := by
  classical
  intro X
  by_cases hX : Nonempty X
  · by_cases hEdge : ∃ u v : X, (K.induce X).Adj u v
    · obtain ⟨u, v, huv⟩ := hEdge
      have hcolor : (K.induce X).Colorable 2 := by
        obtain ⟨C⟩ := hK
        refine ⟨SimpleGraph.Coloring.mk (fun x => C x.1) ?_⟩
        intro a b hab
        exact C.valid hab
      refine ColoringCliqueSandwich (K.induce X) 2 hcolor ?_
      refine ⟨{u, v}, ?_, ?_⟩
      · rw [Finset.coe_insert, Finset.coe_singleton, SimpleGraph.isClique_pair]
        intro _
        exact huv
      · have huvne : u ≠ v := (K.induce X).ne_of_adj huv
        simpa using (Finset.card_pair huvne)
    · obtain ⟨x⟩ := hX
      have hcolor : (K.induce X).Colorable 1 := by
        refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 1)) ?_⟩
        intro u v huv
        exact (hEdge ⟨u, v, huv⟩).elim
      refine ColoringCliqueSandwich (K.induce X) 1 hcolor ?_
      exact ⟨{x}, by simpa using (SimpleGraph.isClique_singleton (G := K.induce X) x), by simp⟩
  · letI : IsEmpty X := ⟨fun x => hX ⟨x⟩⟩
    have hcolor : (K.induce X).Colorable 0 := SimpleGraph.Colorable.of_isEmpty 0
    refine ColoringCliqueSandwich (K.induce X) 0 hcolor ?_
    exact ⟨∅, by simpa using (SimpleGraph.isClique_empty (G := K.induce X)), by simp⟩

end Workspace.ProofLemmas
