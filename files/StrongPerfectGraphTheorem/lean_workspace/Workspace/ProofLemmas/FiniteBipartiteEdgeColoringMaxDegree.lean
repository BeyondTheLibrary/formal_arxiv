import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Workspace.ProofLemmas.BipartiteMaximumDegreeVertexCoveringMatching
import Workspace.ProofLemmas.DeleteCoveringMatchingMaxDegree
import Workspace.ProofLemmas.LineGraphColoringExtendByMatching

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas

/-- The maximum degree does not depend on the chosen decidability instance. -/
private lemma maxDegree_irrel {W : Type*} [Fintype W] (G : SimpleGraph W)
    (i₁ i₂ : DecidableRel G.Adj) :
    @SimpleGraph.maxDegree W G _ i₁ = @SimpleGraph.maxDegree W G _ i₂ := by
  rw [Subsingleton.elim i₁ i₂]

/-- A graph of maximum degree zero has no edges. -/
private lemma eq_bot_of_maxDegree_zero {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (h : G.maxDegree = 0) : G = ⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  intro huv
  have h1 : 0 < G.degree u := (SimpleGraph.degree_pos_iff_exists_adj G u).2 ⟨v, huv⟩
  have h2 := SimpleGraph.degree_le_maxDegree G u
  omega

/-- The line graph of an edgeless graph is colorable with no colors. -/
private lemma lineGraph_colorable_zero_of_eq_bot {W : Type*} (G : SimpleGraph W)
    (h : G = ⊥) : G.lineGraph.Colorable 0 := by
  subst h
  haveI : IsEmpty ((⊥ : SimpleGraph W).edgeSet) := by
    constructor
    rintro ⟨e, he⟩
    rw [SimpleGraph.edgeSet_bot] at he
    exact he
  exact SimpleGraph.Colorable.of_isEmpty 0

/-- König's edge-coloring theorem, in the form of an induction on a bound for
the maximum degree. -/
private lemma koenig_aux {W : Type*} [Fintype W] [DecidableEq W] (d : ℕ) :
    ∀ (G : SimpleGraph W) [DecidableRel G.Adj],
      G.IsBipartite → (∀ v : W, G.degree v ≤ d) → G.lineGraph.Colorable d := by
  induction d with
  | zero =>
      intro G inst hb hd
      have h0 : G.maxDegree = 0 :=
        Nat.le_zero.1 (SimpleGraph.maxDegree_le_of_forall_degree_le G 0 hd)
      exact lineGraph_colorable_zero_of_eq_bot G (eq_bot_of_maxDegree_zero G h0)
  | succ d ih =>
      intro G inst hb hd
      classical
      by_cases h0 : G.maxDegree = 0
      · exact (lineGraph_colorable_zero_of_eq_bot G
          (eq_bot_of_maxDegree_zero G h0)).mono (Nat.zero_le _)
      · have hpos : 0 < G.maxDegree := Nat.pos_of_ne_zero h0
        obtain ⟨M, hM, hcover⟩ :=
          BipartiteMaximumDegreeVertexCoveringMatching G hb hpos
        have hdrop := DeleteCoveringMatchingMaxDegree G M hM hcover
        have hbmax : G.maxDegree ≤ d + 1 :=
          SimpleGraph.maxDegree_le_of_forall_degree_le G _ hd
        have hb' : (G.deleteEdges M.edgeSet).IsBipartite :=
          SimpleGraph.Colorable.mono_left (SimpleGraph.deleteEdges_le _) hb
        have hd' : ∀ v : W, (G.deleteEdges M.edgeSet).degree v ≤ d := by
          intro v
          have h1 : (G.deleteEdges M.edgeSet).degree v
              ≤ (G.deleteEdges M.edgeSet).maxDegree :=
            SimpleGraph.degree_le_maxDegree _ v
          have h2 : (G.deleteEdges M.edgeSet).maxDegree ≤ G.maxDegree - 1 :=
            le_trans (le_of_eq (maxDegree_irrel _ _ _)) hdrop
          omega
        have hcol : (G.deleteEdges M.edgeSet).lineGraph.Colorable d :=
          ih (G.deleteEdges M.edgeSet) hb' hd'
        exact LineGraphColoringExtendByMatching G M d hM hcol

/-- König's edge-coloring theorem, expressed as a vertex coloring of the line graph. -/
theorem FiniteBipartiteEdgeColoringMaxDegree
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hH : H.IsBipartite) :
    H.lineGraph.Colorable H.maxDegree :=
  koenig_aux H.maxDegree H hH (fun v => SimpleGraph.degree_le_maxDegree H v)

end Workspace.ProofLemmas
