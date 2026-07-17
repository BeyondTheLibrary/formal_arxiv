import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Bridge
import Workspace.Types.Cycle
import Workspace.Types.CycleDoubleCover
import Workspace.PriorWorkProofs.Jaeger.Moves
import Workspace.PriorWork.Fleischner
import Workspace.PriorWork.Veblen
import Workspace.PriorWorkProofs.Jaeger.EvenLift
import Workspace.PriorWorkProofs.EightFlow.DisconnectSplit

/-!
# Jaeger's reduction — the induction skeleton

Assembles the moves of `Moves.lean` and `EvenLift.lean` with the admitted classical inputs of
`Fleischner.lean`/`Veblen.lean` into a proof of **Jaeger's reduction** in the exact form of the
`Workspace.PriorWork.jaeger_cubic_reduction` axiom:

> if every finite bridgeless loopless cubic multigraph has a cycle double cover, then every
> finite bridgeless multigraph has a cycle double cover.

The proof is by strong induction on `E(G).ncard`, phrased polymorphically over all `α β` so the
induction hypothesis is available at every vertex/edge type. Each step applies one move:

* **Base** (`E(G) = ∅`): the empty CDC.
* **Move L** (a loop `ℓ`): delete `ℓ`, recurse, lift with `cdc_lift_loop`.
* **Move D2** (a degree-2 vertex): `reroute`, recurse, lift with `cdc_lift_reroute_degree_two`.
* **Move SP** (a degree-≥4 vertex): `fleischner_splitting_lemma` gives a bridgeless `reroute`;
  recurse; lift with `cdc_lift_reroute_split`.
* **Terminal** (loopless, every degree `0` or `3`): delete isolated vertices to get a cubic
  graph and apply `H`.
-/

open Set
open scoped Graph

namespace Workspace.PriorWorkProofs.Jaeger

open Workspace.Types.CycleDoubleCover Workspace.Types.Cycle

/-- In a loopless graph, an edge incident to `v` forces `v` to have positive degree. -/
private theorem degree_pos_of_mem_incidenceSet {α β : Type*} {G : Graph α β} {v : α} {e : β}
    (hll : G.IsLoopless) (hfin : (G.incidenceSet v).Finite) (he : e ∈ G.incidenceSet v) :
    0 < G.degree v := by
  rw [hll.degree_eq_ncard_incidenceSet]
  exact (Set.ncard_pos hfin).mpr ⟨e, he⟩

/-- **Terminal case of Jaeger's reduction.** A finite bridgeless loopless graph in which every
vertex has degree `0` or `3` has a cycle double cover: delete the isolated (degree-`0`) vertices
to obtain a cubic graph (with the same edge set), which is still finite, loopless and bridgeless,
and apply the loopless-cubic hypothesis `H`. Since no edge is lost, a CDC of the cubic graph is a
CDC of `G`. -/
private theorem terminal_hasCDC.{u, w}
    {α : Type u} {β : Type w} {G : Graph α β}
    (H : ∀ (α : Type u) (β : Type w) (G : Graph α β),
      V(G).Finite → E(G).Finite → G.IsLoopless → G.IsCubic → G.Bridgeless →
        G.HasCycleDoubleCover)
    (hV : V(G).Finite) (hE : E(G).Finite) (hbr : G.Bridgeless) (hll : G.IsLoopless)
    (hdeg : ∀ v ∈ V(G), G.degree v = 0 ∨ G.degree v = 3) :
    G.HasCycleDoubleCover := by
  classical
  set X : Set α := {v | G.degree v = 3} with hXdef
  have hmemX : ∀ a : α, a ∈ X ↔ G.degree a = 3 := fun a => Iff.rfl
  -- an edge end has degree `3`, hence lies in `X`
  have hendX : ∀ e a b, G.IsLink e a b → a ∈ X := by
    intro e a b hab
    have haV : a ∈ V(G) := hab.left_mem
    have hfin : (G.incidenceSet a).Finite := hE.subset (G.incidenceSet_subset_edgeSet a)
    have hpos : 0 < G.degree a :=
      degree_pos_of_mem_incidenceSet hll hfin ((G.mem_incidenceSet a e).2 hab.inc_left)
    rw [hmemX]
    rcases hdeg a haV with h0 | h3
    · omega
    · exact h3
  have hclosed : ∀ e a b, G.IsLink e a b → (a ∈ X ↔ b ∈ X) := fun e a b hab =>
    ⟨fun _ => hendX e b a hab.symm, fun _ => hendX e a b hab⟩
  have hXsub : X ⊆ V(G) := by
    intro v hv
    by_contra hvV
    rw [hmemX] at hv
    rw [Graph.degree_eq_zero_of_notMem hvV] at hv
    omega
  set G' : Graph α β := G.induce X with hG'def
  have hG'le : G' ≤ G := Graph.induce_le hXsub
  have hV' : V(G').Finite := by rw [hG'def, Graph.vertexSet_induce]; exact hV.subset hXsub
  have hE' : E(G').Finite := hE.subset (Graph.IsSubgraph.edgeSet_mono hG'le)
  have hll' : G'.IsLoopless := fun e x hl => hll e x (hl.mono hG'le)
  -- incidence sets agree for `X`-vertices, so `G'` is cubic
  have hinc_eq : ∀ v ∈ X, G'.incidenceSet v = G.incidenceSet v := by
    intro v hv
    ext e
    rw [Graph.mem_incidenceSet, Graph.mem_incidenceSet]
    constructor
    · intro h; exact h.mono hG'le
    · rintro ⟨w, hlink⟩
      have hwX : w ∈ X := hendX e w v hlink.symm
      exact ⟨w, by rw [hG'def, Graph.induce_isLink]; exact ⟨hlink, hv, hwX⟩⟩
  have hcubic : G'.IsCubic := by
    intro v hv
    rw [hG'def, Graph.vertexSet_induce] at hv
    rw [hll'.degree_eq_ncard_incidenceSet, hinc_eq v hv, ← hll.degree_eq_ncard_incidenceSet]
    exact (hmemX v).1 hv
  have hbr' : G'.Bridgeless :=
    Workspace.PriorWorkProofs.EightFlow.induce_bridgeless hbr hclosed
  obtain ⟨D, hD⟩ := H α β G' hV' hE' hll' hcubic hbr'
  -- `E(G') = E(G)`: both ends of every edge are in `X`
  have hEeq : E(G') = E(G) := by
    refine Set.eq_of_subset_of_subset (Graph.IsSubgraph.edgeSet_mono hG'le) ?_
    intro e he
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
    rw [Graph.edge_mem_iff_exists_isLink]
    exact ⟨a, b, by
      rw [hG'def, Graph.induce_isLink]
      exact ⟨hab, hendX e a b hab, hendX e b a hab.symm⟩⟩
  refine ⟨D, ?_, ?_⟩
  · intro C hC; exact (hD.isCycle_of_mem hC).mono hG'le
  · intro e he
    rw [← hEeq] at he
    exact hD.edgeMultiplicity_eq he

/-- **Jaeger's reduction to the loopless cubic case** — same statement as the
`Workspace.PriorWork.jaeger_cubic_reduction` axiom. Proved from the elementary moves
(`Moves.lean`, `EvenLift.lean`) and the admitted Fleischner/Veblen inputs. -/
theorem jaeger_cubic_reduction_proof.{u, w}
    (H : ∀ (α : Type u) (β : Type w) (G : Graph α β),
      V(G).Finite → E(G).Finite → G.IsLoopless → G.IsCubic → G.Bridgeless →
        G.HasCycleDoubleCover) :
    ∀ (α : Type u) (β : Type w) (G : Graph α β),
      V(G).Finite → E(G).Finite → G.Bridgeless → G.HasCycleDoubleCover := by
  -- Strong induction on the edge count, uniform over all `α β`.
  suffices key : ∀ n : ℕ, ∀ (α : Type u) (β : Type w) (G : Graph α β),
      V(G).Finite → E(G).Finite → E(G).ncard ≤ n → G.Bridgeless → G.HasCycleDoubleCover by
    intro α β G hV hE hbr
    exact key (E(G).ncard) α β G hV hE le_rfl hbr
  intro n
  induction n with
  | zero =>
    intro α β G _ hE hcard hbr
    have hEmpty : E(G) = ∅ := by
      rw [← Set.ncard_eq_zero hE]; omega
    exact ⟨0, (Graph.isCycleDoubleCover_zero_iff).2 hEmpty⟩
  | succ n ih =>
    intro α β G hV hE hcard hbr
    by_cases hEmpty : E(G) = ∅
    · exact ⟨0, (Graph.isCycleDoubleCover_zero_iff).2 hEmpty⟩
    -- `E(G)` is nonempty from here on.
    by_cases hLoop : ∃ ℓ x, G.IsLoopAt ℓ x
    · -- Move L — loop removal.
      obtain ⟨ℓ, x, hℓ⟩ := hLoop
      have hℓE : ℓ ∈ E(G) := hℓ.edge_mem
      have hpos : 0 < E(G).ncard := Set.ncard_pos hE |>.mpr ⟨ℓ, hℓE⟩
      have hbr' : (G.deleteEdges {ℓ}).Bridgeless := bridgeless_deleteEdge_loop hbr hℓ
      have hV' : V(G.deleteEdges {ℓ}).Finite := by
        rw [Graph.vertexSet_deleteEdges]; exact hV
      have hE' : E(G.deleteEdges {ℓ}).Finite := by
        rw [Graph.edgeSet_deleteEdges]; exact hE.diff
      have hcard' : E(G.deleteEdges {ℓ}).ncard ≤ n := by
        rw [Graph.edgeSet_deleteEdges, Set.ncard_diff_singleton_of_mem hℓE]; omega
      obtain ⟨D, hD⟩ := ih α β (G.deleteEdges {ℓ}) hV' hE' hcard' hbr'
      exact ⟨_, cdc_lift_loop hℓ hD⟩
    · -- `G` is loopless.
      have hll : G.IsLoopless := fun ℓ x h => hLoop ⟨ℓ, x, h⟩
      by_cases hD2 : ∃ (v v1 v2 : α) (e1 e2 : β),
          e1 ≠ e2 ∧ G.degree v = 2 ∧ G.IsLink e1 v v1 ∧ G.IsLink e2 v v2
      · -- Move D2 — degree-2 suppression.
        obtain ⟨v, v1, v2, e1, e2, hne, hdeg, he1, he2⟩ := hD2
        have he2E : e2 ∈ E(G) := he2.edge_mem
        have hpos : 0 < E(G).ncard := Set.ncard_pos hE |>.mpr ⟨e2, he2E⟩
        have hbr' : (reroute G v1 v2 e1 e2).Bridgeless :=
          bridgeless_reroute_of_degree_two hbr hll hdeg he1 he2 hne
        have hV' : V(reroute G v1 v2 e1 e2).Finite := by rw [vertexSet_reroute]; exact hV
        have hE' : E(reroute G v1 v2 e1 e2).Finite := by
          rw [edgeSet_reroute he1 he2 hne]; exact hE.diff
        have hcard' : E(reroute G v1 v2 e1 e2).ncard ≤ n := by
          rw [edgeSet_reroute he1 he2 hne, Set.ncard_diff_singleton_of_mem he2E]; omega
        obtain ⟨D, hD⟩ := ih α β (reroute G v1 v2 e1 e2) hV' hE' hcard' hbr'
        exact cdc_lift_reroute_degree_two hll hV hE hdeg he1 he2 hne hD
      · by_cases hD4 : ∃ v, 4 ≤ G.degree v
        · -- Move SP — degree-≥4 Fleischner split.
          obtain ⟨v, hdeg⟩ := hD4
          obtain ⟨v1, v2, e1, e2, hne, he1, he2, hbr'⟩ :=
            Workspace.PriorWork.fleischner_splitting_lemma G v hV hE hll hbr hdeg
          have he2E : e2 ∈ E(G) := he2.edge_mem
          have hpos : 0 < E(G).ncard := Set.ncard_pos hE |>.mpr ⟨e2, he2E⟩
          have hV' : V(reroute G v1 v2 e1 e2).Finite := by rw [vertexSet_reroute]; exact hV
          have hE' : E(reroute G v1 v2 e1 e2).Finite := by
            rw [edgeSet_reroute he1 he2 hne]; exact hE.diff
          have hcard' : E(reroute G v1 v2 e1 e2).ncard ≤ n := by
            rw [edgeSet_reroute he1 he2 hne, Set.ncard_diff_singleton_of_mem he2E]; omega
          obtain ⟨D, hD⟩ := ih α β (reroute G v1 v2 e1 e2) hV' hE' hcard' hbr'
          exact cdc_lift_reroute_split hll hV hE he1 he2 hne hD
        · -- Terminal — loopless, every vertex degree `0` or `3`: delete isolated vertices to
          -- obtain a finite bridgeless loopless CUBIC graph and apply `H`.
          -- Every vertex has degree `0` or `3`: `¬hD4` bounds degrees by `3`; `¬hD2` and
          -- looplessness rule out degree `2`; bridgelessness rules out degree `1`.
          have hdeg : ∀ v ∈ V(G), G.degree v = 0 ∨ G.degree v = 3 := by
            intro v hv
            have hfin : (G.incidenceSet v).Finite := hE.subset (G.incidenceSet_subset_edgeSet v)
            have hle3 : G.degree v ≤ 3 := by
              by_contra h; push_neg at h; exact hD4 ⟨v, h⟩
            have hne2 : G.degree v ≠ 2 := by
              intro h2
              have hcard : (G.incidenceSet v).ncard = 2 := by
                rw [← hll.degree_eq_ncard_incidenceSet]; exact h2
              obtain ⟨e1, e2, hne, hset⟩ := Set.ncard_eq_two.mp hcard
              have he1 : e1 ∈ G.incidenceSet v := by rw [hset]; exact Set.mem_insert _ _
              have he2 : e2 ∈ G.incidenceSet v := by
                rw [hset]; exact Set.mem_insert_of_mem _ rfl
              obtain ⟨v1, hlink1⟩ := (G.mem_incidenceSet v e1).1 he1
              obtain ⟨v2, hlink2⟩ := (G.mem_incidenceSet v e2).1 he2
              exact hD2 ⟨v, v1, v2, e1, e2, hne, h2, hlink1, hlink2⟩
            have hne1 : G.degree v ≠ 1 := by
              intro h1
              have hcard : (G.incidenceSet v).ncard = 1 := by
                rw [← hll.degree_eq_ncard_incidenceSet]; exact h1
              obtain ⟨e, hset⟩ := Set.ncard_eq_one.mp hcard
              have he : e ∈ G.incidenceSet v := by rw [hset]; exact Set.mem_singleton e
              obtain ⟨w, hlink⟩ := (G.mem_incidenceSet v e).1 he
              have hvw : v ≠ w := by
                intro h; rw [← h] at hlink; exact hll e v hlink
              have hbridge : G.IsBridge e := by
                refine ⟨v, w, hlink, ?_⟩
                intro hr
                have hadj : ∀ b, ¬ (G.deleteEdges {e}).Adj v b := by
                  rintro b ⟨f, hf⟩
                  rw [Graph.deleteEdges_isLink] at hf
                  obtain ⟨hfl, hfne⟩ := hf
                  have hfinc : f ∈ G.incidenceSet v := (G.mem_incidenceSet v f).2 hfl.inc_left
                  rw [hset] at hfinc
                  exact hfne hfinc
                rw [Graph.reachable_def, Relation.reflTransGen_iff_eq hadj] at hr
                exact hvw hr.symm
              exact hbr e hlink.edge_mem hbridge
            omega
          exact terminal_hasCDC H hV hE hbr hll hdeg

end Workspace.PriorWorkProofs.Jaeger
