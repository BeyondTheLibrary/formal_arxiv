import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.Types.Gamma
import Workspace.PriorWorkProofs.EightFlow.EvenSubgraph

/-!
# Splitting a graph at a 0-edge-cut (a "closed" vertex set)

We split a graph `G` at a set `X` of vertices across which **no** edge crosses: every edge
of `G` has both ends inside `X` or both ends outside `X`
(`hclosed : ∀ e a b, G.IsLink e a b → (a ∈ X ↔ b ∈ X)`).  This is the 0-edge-cut condition.
We work with Mathlib's induced subgraph `Graph.induce X`.

* `induce_bridgeless` — the induced subgraph on a closed vertex set of a bridgeless graph is
  again bridgeless.
* `gamma_flow_of_closed_split` — if both sides of a 0-edge-cut carry a nowhere-zero `Γ`-flow
  (for every orientation), then so does `G`.  The glued map is the indicator-style piecewise
  `f e := if e ∈ E(G.induce S) then fA e else fB e`.
-/

open Set
open scoped Graph
open Workspace.Types.Gamma
open Workspace.Types.Orientation

namespace Workspace.PriorWorkProofs.EightFlow

open scoped Classical

variable {α β : Type*} {G : Graph α β}

/-! ## Elementary facts about a closed vertex set -/

/-- If an edge of `G` is an edge of the induced subgraph `G.induce X` and `p` is one of its ends
in `G`, then `p ∈ X`.  (The ends of an induced edge lie in `X`.) -/
theorem end_mem_of_edge_induce {X : Set α} {e : β} {p q : α}
    (he : e ∈ E(G.induce X)) (hpq : G.IsLink e p q) : p ∈ X := by
  rw [Graph.edgeSet_induce, Set.mem_setOf_eq] at he
  obtain ⟨x, y, hxy, hxX, hyX⟩ := he
  rcases hpq.eq_and_eq_or_eq_and_eq hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact hxX
  · exact hyX

/-! ## GOAL 1 — induced subgraph on a closed vertex set stays bridgeless -/

/-- A walk in `G - e'` between two vertices of a closed set `X` lifts to a walk in
`(G.induce X) - e'`: since no edge crosses `X`, every vertex the walk visits stays in `X`, and
every edge it uses has both ends in `X`, hence survives in the induced subgraph. -/
theorem reachable_induce_of_reachable_deleteEdges {X : Set α} {e' : β}
    (hclosed : ∀ e a b, G.IsLink e a b → (a ∈ X ↔ b ∈ X)) {u v : α} (hu : u ∈ X)
    (h : (G.deleteEdges {e'}).Reachable u v) :
    ((G.induce X).deleteEdges {e'}).Reachable u v := by
  suffices hsuf : ((G.induce X).deleteEdges {e'}).Reachable u v ∧ v ∈ X from hsuf.1
  induction h with
  | refl => exact ⟨Graph.Reachable.refl _ _, hu⟩
  | @tail b c hab hbc ih =>
      obtain ⟨hru, hbX⟩ := ih
      obtain ⟨f, hf⟩ := hbc
      rw [Graph.deleteEdges_isLink] at hf
      obtain ⟨hflink, hfne⟩ := hf
      have hcX : c ∈ X := (hclosed f b c hflink).mp hbX
      refine ⟨hru.tail ⟨f, ?_⟩, hcX⟩
      rw [Graph.deleteEdges_isLink]
      refine ⟨?_, hfne⟩
      rw [Graph.induce_isLink]
      exact ⟨hflink, hbX, hcX⟩

/-- **GOAL 1.** The induced subgraph on a closed vertex set of a bridgeless graph is bridgeless. -/
theorem induce_bridgeless {X : Set α} (hbr : G.Bridgeless)
    (hclosed : ∀ e a b, G.IsLink e a b → (a ∈ X ↔ b ∈ X)) :
    (G.induce X).Bridgeless := by
  apply Graph.bridgeless_of_forall_reachable
  intro e' _ a b hlink
  rw [Graph.induce_isLink] at hlink
  obtain ⟨hlinkG, haX, _hbX⟩ := hlink
  have he'G : e' ∈ E(G) := hlinkG.edge_mem
  have hnb : ¬ G.IsBridge e' := hbr.not_isBridge e'
  have hreach : (G.deleteEdges {e'}).Reachable a b := by
    by_contra hcon
    exact hnb ⟨a, b, hlinkG, hcon⟩
  exact reachable_induce_of_reachable_deleteEdges hclosed haX hreach

/-! ## GOAL 2 — flow gluing across a 0-edge-cut -/

/-- The characteristic-two edge-end sum at a vertex `v ∈ X` is unchanged when passing from `G` to
the induced subgraph `G.induce X`, provided the two maps agree on the edges incident to `v` in the
induced subgraph.  The index set `G.incidenceSet v` equals `(G.induce X).incidenceSet v` (no edge
crosses `X`), and the loop indicator agrees. -/
theorem endSum_restrict {A : Type*} [AddCommGroup A] {X : Set α} {v : α}
    (hclosed : ∀ e a b, G.IsLink e a b → (a ∈ X ↔ b ∈ X))
    (hv : v ∈ X) (g g' : β → A)
    (hagree : ∀ e ∈ (G.induce X).incidenceSet v, g e = g' e) :
    (∑ᶠ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • g e)
      = (∑ᶠ e ∈ (G.induce X).incidenceSet v,
          (if (G.induce X).IsLoopAt e v then (2 : ℕ) else 1) • g' e) := by
  refine finsum_mem_congr ?_ ?_
  · -- the two incidence sets coincide
    ext e
    rw [Graph.mem_incidenceSet, Graph.mem_incidenceSet]
    constructor
    · intro he
      obtain ⟨w, hlink⟩ := he
      have hwX : w ∈ X := (hclosed e v w hlink).mp hv
      exact ⟨w, by rw [Graph.induce_isLink]; exact ⟨hlink, hv, hwX⟩⟩
    · intro he
      obtain ⟨w, hlink⟩ := he
      rw [Graph.induce_isLink] at hlink
      exact ⟨w, hlink.1⟩
  · -- the summands agree pointwise on the induced incidence set
    intro e he
    have hg : g e = g' e := hagree e he
    have hiff : G.IsLoopAt e v ↔ (G.induce X).IsLoopAt e v := by
      show G.IsLink e v v ↔ (G.induce X).IsLink e v v
      rw [Graph.induce_isLink]
      exact ⟨fun h => ⟨h, hv, hv⟩, fun h => h.1⟩
    have hloop : (if G.IsLoopAt e v then (2 : ℕ) else 1)
        = (if (G.induce X).IsLoopAt e v then (2 : ℕ) else 1) := by
      by_cases hl : G.IsLoopAt e v
      · rw [if_pos hl, if_pos (hiff.mp hl)]
      · rw [if_neg hl, if_neg (fun h => hl (hiff.mpr h))]
    rw [hloop, hg]

/-- **GOAL 2.** Flow gluing across a 0-edge-cut.  If the two induced subgraphs on `S` and its
complement `V(G) \ S` (across which no edge crosses) each carry a nowhere-zero `Γ`-flow for every
orientation, then `G` carries a nowhere-zero `Γ`-flow. -/
theorem gamma_flow_of_closed_split (hV : V(G).Finite) (hE : E(G).Finite) {S : Set α}
    (hS : S ⊆ V(G)) (hclosed : ∀ e a b, G.IsLink e a b → (a ∈ S ↔ b ∈ S))
    (hA : ∀ O' : Orientation (G.induce S), ∃ f : β → Gamma,
            (G.induce S).IsFlow O' f ∧ (G.induce S).IsNowhereZero f)
    (hB : ∀ O' : Orientation (G.induce (V(G) \ S)), ∃ f : β → Gamma,
            (G.induce (V(G) \ S)).IsFlow O' f ∧ (G.induce (V(G) \ S)).IsNowhereZero f)
    (O : Orientation G) :
    ∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f := by
  classical
  have hTsub : (V(G) \ S) ⊆ V(G) := Set.diff_subset
  have hleS : G.induce S ≤ G := Graph.induce_le hS
  have hleT : G.induce (V(G) \ S) ≤ G := Graph.induce_le hTsub
  have hEGS : E(G.induce S).Finite := hE.subset (Graph.IsSubgraph.edgeSet_mono hleS)
  have hEGT : E(G.induce (V(G) \ S)).Finite := hE.subset (Graph.IsSubgraph.edgeSet_mono hleT)
  obtain ⟨fA, hfA_flow, hfA_nz⟩ := hA (O.restrict hleS)
  obtain ⟨fB, hfB_flow, hfB_nz⟩ := hB (O.restrict hleT)
  -- the closedness of the complement `V(G) \ S`
  have hclosedT : ∀ e a b, G.IsLink e a b → (a ∈ V(G) \ S ↔ b ∈ V(G) \ S) := by
    intro e a b hlink
    have ha : a ∈ V(G) := hlink.left_mem
    have hb : b ∈ V(G) := hlink.right_mem
    have hiff := hclosed e a b hlink
    simp only [Set.mem_diff]
    constructor
    · rintro ⟨_, haS⟩; exact ⟨hb, fun hbS => haS (hiff.mpr hbS)⟩
    · rintro ⟨_, hbS⟩; exact ⟨ha, fun haS => hbS (hiff.mp haS)⟩
  refine ⟨fun e => if e ∈ E(G.induce S) then fA e else fB e, ?_, ?_⟩
  · -- FLOW
    rw [charTwo_flow_iff_endSum_zero Gamma.add_self hE O]
    intro v hvV
    by_cases hvS : v ∈ S
    · -- v ∈ S: the endSum reduces to the endSum of `fA` on `G.induce S`, which is 0
      have hvGS : v ∈ V(G.induce S) := by rw [Graph.vertexSet_induce]; exact hvS
      have hagreeS : ∀ e ∈ (G.induce S).incidenceSet v,
          (fun e => if e ∈ E(G.induce S) then fA e else fB e) e = fA e := by
        intro e he
        have heE : e ∈ E(G.induce S) := ((Graph.mem_incidenceSet v e).mp he).edge_mem
        exact if_pos heE
      rw [endSum_restrict hclosed hvS
            (fun e => if e ∈ E(G.induce S) then fA e else fB e) fA hagreeS]
      exact (charTwo_flow_iff_endSum_zero Gamma.add_self hEGS (O.restrict hleS) fA).mp
              hfA_flow v hvGS
    · -- v ∉ S: v ∈ V(G) \ S; the endSum reduces to the endSum of `fB`
      have hvT : v ∈ V(G) \ S := ⟨hvV, hvS⟩
      have hvGT : v ∈ V(G.induce (V(G) \ S)) := by rw [Graph.vertexSet_induce]; exact hvT
      have hagreeT : ∀ e ∈ (G.induce (V(G) \ S)).incidenceSet v,
          (fun e => if e ∈ E(G.induce S) then fA e else fB e) e = fB e := by
        intro e he
        obtain ⟨w, hlinkT⟩ := (Graph.mem_incidenceSet v e).mp he
        rw [Graph.induce_isLink] at hlinkT
        have hlinkG : G.IsLink e v w := hlinkT.1
        have heNGS : e ∉ E(G.induce S) := by
          intro hcon
          exact hvS (end_mem_of_edge_induce hcon hlinkG)
        exact if_neg heNGS
      rw [endSum_restrict hclosedT hvT
            (fun e => if e ∈ E(G.induce S) then fA e else fB e) fB hagreeT]
      exact (charTwo_flow_iff_endSum_zero Gamma.add_self hEGT (O.restrict hleT) fB).mp
              hfB_flow v hvGT
  · -- NOWHERE-ZERO
    intro e he hcontra
    obtain ⟨a, b, hlink⟩ := Graph.exists_isLink_of_mem_edgeSet he
    have ha : a ∈ V(G) := hlink.left_mem
    have hb : b ∈ V(G) := hlink.right_mem
    have hiff := hclosed e a b hlink
    by_cases haS : a ∈ S
    · have hbS : b ∈ S := hiff.mp haS
      have heGS : e ∈ E(G.induce S) := by
        rw [Graph.edgeSet_induce, Set.mem_setOf_eq]; exact ⟨a, b, hlink, haS, hbS⟩
      have hcontra' : (if e ∈ E(G.induce S) then fA e else fB e) = 0 := hcontra
      rw [if_pos heGS] at hcontra'
      exact hfA_nz e heGS hcontra'
    · have hbS : b ∉ S := fun h => haS (hiff.mpr h)
      have heGT : e ∈ E(G.induce (V(G) \ S)) := by
        rw [Graph.edgeSet_induce, Set.mem_setOf_eq]
        exact ⟨a, b, hlink, ⟨ha, haS⟩, ⟨hb, hbS⟩⟩
      have heNGS : e ∉ E(G.induce S) := fun hcon => haS (end_mem_of_edge_induce hcon hlink)
      have hcontra' : (if e ∈ E(G.induce S) then fA e else fB e) = 0 := hcontra
      rw [if_neg heNGS] at hcontra'
      exact hfB_nz e heGT hcontra'

end Workspace.PriorWorkProofs.EightFlow
