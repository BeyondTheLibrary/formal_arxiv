import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.Types.Cycle
import Workspace.Types.CycleDoubleCover

/-!
# Jaeger's reduction — the elementary graph moves and their CDC-lifts

The elementary (Fleischner-free) moves of Jaeger's reduction of the Cycle Double Cover
conjecture to the loopless cubic bridgeless case, with the lemmas that lift a cycle double
cover (CDC) back along each move. Every move is edge-reduced: it reuses existing edge labels
and keeps every vertex, so it stays on the same vertex/edge types `α`, `β`.
-/

open Set
open scoped Graph
open scoped Classical

namespace Graph

variable {α β : Type*} {G : Graph α β} {v : α} {ℓ : β}

/-- The single-loop graph `bouquet v {ℓ}` is a subgraph of any graph in which `ℓ` is a
loop at `v`. -/
theorem IsLoopAt.bouquet_le (h : G.IsLoopAt ℓ v) :
    Graph.bouquet v ({ℓ} : Set β) ≤ G := by
  refine ⟨?_, ?_⟩
  · rw [Graph.vertexSet_bouquet]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    exact h.left_mem
  · intro f x y hf
    rw [Graph.bouquet_isLink] at hf
    obtain ⟨hfe, rfl, rfl⟩ := hf
    simp only [Set.mem_singleton_iff] at hfe
    subst hfe
    exact h

end Graph

namespace Workspace.PriorWorkProofs.Jaeger

open Workspace.Types.Cycle Workspace.Types.CycleDoubleCover

variable {α β : Type*} {G : Graph α β} {u v w : α} {e ℓ : β}

/-! ## Move L — loop removal -/

/-- The **loop-cycle** at `v`: the cycle consisting of the single loop `ℓ`. -/
def loopCycle (v : α) (ℓ : β) : Graph α β := Graph.bouquet v ({ℓ} : Set β)

@[simp] theorem edgeSet_loopCycle (v : α) (ℓ : β) : E(loopCycle v ℓ) = {ℓ} := by
  ext e
  rw [Graph.edge_mem_iff_exists_isLink]
  simp only [loopCycle, Graph.bouquet_isLink, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, y, he, -, -⟩; exact he
  · rintro rfl; exact ⟨v, v, rfl, rfl, rfl⟩

theorem mem_edgeSet_loopCycle (v : α) (ℓ : β) : ℓ ∈ E(loopCycle v ℓ) := by
  rw [edgeSet_loopCycle]; exact Set.mem_singleton ℓ

/-- The loop-cycle is a cycle of `G` when `ℓ` really is a loop at `v` in `G`. -/
theorem isCycle_loopCycle (h : G.IsLoopAt ℓ v) : G.IsCycle (loopCycle v ℓ) :=
  (Workspace.Types.Cycle.isCycle_bouquet_singleton v ℓ).of_self h.bouquet_le

/-- **Move L, the CDC lift.** If `ℓ` is a loop of `G` at `v` and `D` is a cycle double cover
of `G − ℓ`, then adjoining the loop-cycle **twice** to `D` yields a cycle double cover of `G`.
Every edge `≠ ℓ` keeps multiplicity `2`; `ℓ`, absent from `G − ℓ`, is covered exactly twice by
the two adjoined copies. -/
theorem cdc_lift_loop (h : G.IsLoopAt ℓ v) {D : Multiset (Graph α β)}
    (hD : (G.deleteEdges {ℓ}).IsCycleDoubleCover D) :
    G.IsCycleDoubleCover (loopCycle v ℓ ::ₘ loopCycle v ℓ ::ₘ D) := by
  have hℓE : ℓ ∈ E(loopCycle v ℓ) := mem_edgeSet_loopCycle v ℓ
  refine ⟨?_, ?_⟩
  · -- every member is a cycle of `G`
    intro C hC
    rw [Multiset.mem_cons, Multiset.mem_cons] at hC
    rcases hC with rfl | rfl | hC
    · exact isCycle_loopCycle h
    · exact isCycle_loopCycle h
    · exact (hD.isCycle_of_mem hC).mono Graph.deleteEdges_le
  · -- every edge of `G` has multiplicity 2
    intro e he
    by_cases he0 : e = ℓ
    · subst e
      -- ℓ is covered exactly by the two adjoined loop-cycles
      have hDℓ : D.edgeMultiplicity ℓ = 0 := by
        rw [Multiset.edgeMultiplicity_eq_zero_iff]
        intro C hCD hℓC
        -- members of D are subgraphs of `G − ℓ`, whose edge set excludes ℓ
        have hsub : E(C) ⊆ E(G.deleteEdges {ℓ}) :=
          Graph.IsSubgraph.edgeSet_mono (hD.le_of_mem hCD)
        have : ℓ ∈ E(G.deleteEdges {ℓ}) := hsub hℓC
        rw [Graph.edgeSet_deleteEdges] at this
        exact this.2 (Set.mem_singleton ℓ)
      rw [Multiset.edgeMultiplicity_cons_of_mem _ hℓE,
        Multiset.edgeMultiplicity_cons_of_mem _ hℓE, hDℓ]
    · -- e ≠ ℓ : the two loop-cycles miss it; it is covered twice inside `G − ℓ`
      have heNotLoop : e ∉ E(loopCycle v ℓ) := by
        rw [edgeSet_loopCycle]; simpa using he0
      have heG' : e ∈ E(G.deleteEdges {ℓ}) := by
        rw [Graph.edgeSet_deleteEdges]
        exact ⟨he, by simpa using he0⟩
      rw [Multiset.edgeMultiplicity_cons_of_notMem _ heNotLoop,
        Multiset.edgeMultiplicity_cons_of_notMem _ heNotLoop, hD.edgeMultiplicity_eq heG']

/-! ### Move L — bridgelessness is preserved

Deleting a loop cannot change reachability (a loop is an adjacency `v`–`v`, useless for
connecting distinct vertices), hence cannot create a bridge. -/

/-- Deleting a loop `ℓ` from `G` does not change reachability. -/
theorem reachable_deleteEdge_loop (h : G.IsLoopAt ℓ v) {x y : α} :
    (G.deleteEdges {ℓ}).Reachable x y ↔ G.Reachable x y := by
  constructor
  · exact fun hr => hr.mono Graph.deleteEdges_le
  · intro hr
    -- walk in G; every adjacency uses some edge; if that edge is ℓ the step is v–v, i.e.
    -- endpoints equal, so it can be dropped.
    induction hr with
    | refl => exact Graph.Reachable.refl _ _
    | @tail b c hab hbc ih =>
      obtain ⟨f, hf⟩ := hbc
      by_cases hfℓ : f = ℓ
      · -- the step b–c uses the loop ℓ; then b = c, so no progress is made
        have hf' : G.IsLink ℓ b c := hfℓ ▸ hf
        have hbc' : b = c := by
          rcases hf'.eq_and_eq_or_eq_and_eq h with ⟨hb, hc⟩ | ⟨hb, hc⟩ <;> rw [hb, hc]
        exact hbc' ▸ ih
      · exact ih.tail ⟨f, by rw [Graph.deleteEdges_isLink]; exact ⟨hf, by simpa using hfℓ⟩⟩

/-- **Move L preserves bridgelessness.** Deleting a loop from a bridgeless graph yields a
bridgeless graph. -/
theorem bridgeless_deleteEdge_loop (hbr : G.Bridgeless) (h : G.IsLoopAt ℓ v) :
    (G.deleteEdges {ℓ}).Bridgeless := by
  intro e he hb
  -- `e ≠ ℓ` since ℓ was deleted
  rw [Graph.edgeSet_deleteEdges] at he
  have heℓ : e ≠ ℓ := by simpa using he.2
  obtain ⟨x, y, hxy, hnr⟩ := hb
  -- e is an edge of G with the same ends
  have hxyG : G.IsLink e x y := Graph.deleteEdges_le.isLink_mono hxy
  refine hbr e he.1 ⟨x, y, hxyG, fun hrG => hnr ?_⟩
  -- reconnect x,y in (G-ℓ)-e using: reachability in G-e equals reachability in (G-e)-ℓ,
  -- because ℓ is still a loop in G-e (e ≠ ℓ).
  have hℓ' : (G.deleteEdges {e}).IsLoopAt ℓ v := by
    rw [Graph.deleteEdges_isLoopAt]
    exact ⟨h, by simpa using heℓ.symm⟩
  -- delete both edges; the two single-deletions commute up to the loop-reachability lemma
  have hcomm : (G.deleteEdges {ℓ}).deleteEdges {e} = (G.deleteEdges {e}).deleteEdges {ℓ} := by
    rw [Graph.deleteEdges_deleteEdges, Graph.deleteEdges_deleteEdges, Set.union_comm]
  rw [hcomm, reachable_deleteEdge_loop hℓ']
  exact hrG

/-! ## Moves D2 and SP — the edge-reduced reroute operation

The degree-2 suppression and the degree-≥4 Fleischner split share one edge-reduced graph
operation on the same types: pick two distinct edges `e₁ = v v₁`, `e₂ = v v₂` at the working
vertex `v`, **delete `e₂` and relabel `e₁` so that it now joins `v₁`–`v₂`** (a loop at `v₁`
when `v₁ = v₂`). Every vertex is kept and exactly one edge is removed. -/

/-- The edge-reduced **reroute** of `G` at `v₁, v₂` along `e₁, e₂`: delete `e₂` and make `e₁`
join `v₁`–`v₂`; all other edges and all vertices are unchanged. `IsLink` is given directly (no
`DecidableEq β` needed): `e₁` now links `{v₁, v₂}` when both lie in `V(G)`, `e₂` is gone, and
every other edge keeps its `G`-incidences. -/
def reroute (G : Graph α β) (v1 v2 : α) (e1 e2 : β) : Graph α β where
  vertexSet := V(G)
  IsLink f x y :=
    (f = e1 ∧ (v1 ∈ V(G) ∧ v2 ∈ V(G)) ∧ ((x = v1 ∧ y = v2) ∨ (x = v2 ∧ y = v1))) ∨
      (f ≠ e1 ∧ f ≠ e2 ∧ G.IsLink f x y)
  isLink_symm := by
    rintro f hf x y (⟨rfl, hm, hd⟩ | ⟨h1, h2, hxy⟩)
    · exact Or.inl ⟨rfl, hm, by tauto⟩
    · exact Or.inr ⟨h1, h2, hxy.symm⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro f x y a b (⟨hf1, hm, hd⟩ | ⟨h1, h2, hxy⟩) (⟨hf1', hm', hd'⟩ | ⟨h1', h2', hab⟩)
    · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hd' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    · exact absurd hf1 h1'
    · exact absurd hf1' h1
    · exact G.eq_or_eq_of_isLink_of_isLink hxy hab
  left_mem_of_isLink := by
    rintro f x y (⟨rfl, hm, hd⟩ | ⟨-, -, hxy⟩)
    · rcases hd with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hm.1
      · exact hm.2
    · exact hxy.left_mem

@[simp] theorem vertexSet_reroute (G : Graph α β) (v1 v2 : α) (e1 e2 : β) :
    V(reroute G v1 v2 e1 e2) = V(G) := rfl

theorem reroute_isLink (G : Graph α β) (v1 v2 : α) (e1 e2 : β) (f : β) (x y : α) :
    (reroute G v1 v2 e1 e2).IsLink f x y ↔
      (f = e1 ∧ (v1 ∈ V(G) ∧ v2 ∈ V(G)) ∧ ((x = v1 ∧ y = v2) ∨ (x = v2 ∧ y = v1))) ∨
        (f ≠ e1 ∧ f ≠ e2 ∧ G.IsLink f x y) := Iff.rfl

/-- The reroute removes exactly the edge `e₂`; every other edge of `G` survives (with `e₁`
possibly relabelled). Hence the edge count drops by one. -/
theorem edgeSet_reroute {v1 v2 : α} {e1 e2 : β} (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2)
    (hne : e1 ≠ e2) :
    E(reroute G v1 v2 e1 e2) = E(G) \ {e2} := by
  have hv1 : v1 ∈ V(G) := he1.right_mem
  have hv2 : v2 ∈ V(G) := he2.right_mem
  ext f
  rw [Graph.edge_mem_iff_exists_isLink]
  simp only [Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    rw [reroute_isLink] at hxy
    rcases hxy with ⟨rfl, -, -⟩ | ⟨-, h2, hg⟩
    · exact ⟨he1.edge_mem, hne⟩
    · exact ⟨hg.edge_mem, h2⟩
  · rintro ⟨hfG, hfe2⟩
    by_cases hfe1 : f = e1
    · subst hfe1
      exact ⟨v1, v2, by rw [reroute_isLink]; exact Or.inl ⟨rfl, ⟨hv1, hv2⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
    · obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet hfG
      exact ⟨x, y, by rw [reroute_isLink]; exact Or.inr ⟨hfe1, hfe2, hxy⟩⟩

/-! ### Reachability transfer for the reroute

`reroute_reachable_map` transports a walk of `K` into `reroute K` by sending the suppressed
vertex `v` to `v1`; `deleteEdges_reachable_pendant` is the analogue for deleting a pendant edge
`e2` at a vertex whose only incident edge is `e2`. -/

/-- Transport a walk of `K` into `reroute K v1 v2 e1 e2`, mapping the suppressed vertex `v`
(whose only incident edges are `e1 = v v1` and `e2 = v v2`) to `v1`. -/
private theorem reroute_reachable_map {α β : Type*} {K : Graph α β} {p v1 v2 : α} {e1 e2 : β}
    (hv1 : p ≠ v1) (hv2 : p ≠ v2) (he1 : K.IsLink e1 p v1) (he2 : K.IsLink e2 p v2)
    (hvonly : ∀ f x, K.IsLink f p x → f = e1 ∨ f = e2)
    {a b : α} (h : K.Reachable a b) :
    (reroute K v1 v2 e1 e2).Reachable (if a = p then v1 else a) (if b = p then v1 else b) := by
  induction h with
  | refl => exact Graph.Reachable.refl _ _
  | @tail c d hac hcd ih =>
    refine ih.trans ?_
    obtain ⟨f, hf⟩ := hcd
    have hv1V : v1 ∈ V(K) := he1.right_mem
    have hv2V : v2 ∈ V(K) := he2.right_mem
    by_cases hfe1 : f = e1
    · subst hfe1
      rcases hf.eq_and_eq_or_eq_and_eq he1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [if_pos rfl, if_neg (Ne.symm hv1)]
      · rw [if_neg (Ne.symm hv1), if_pos rfl]
    · by_cases hfe2 : f = e2
      · subst hfe2
        rcases hf.eq_and_eq_or_eq_and_eq he2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [if_pos rfl, if_neg (Ne.symm hv2)]
          exact Graph.IsLink.reachable (e := e1)
            (by rw [reroute_isLink]; exact Or.inl ⟨rfl, ⟨hv1V, hv2V⟩, Or.inl ⟨rfl, rfl⟩⟩)
        · rw [if_neg (Ne.symm hv2), if_pos rfl]
          exact Graph.IsLink.reachable (e := e1)
            (by rw [reroute_isLink]; exact Or.inl ⟨rfl, ⟨hv1V, hv2V⟩, Or.inr ⟨rfl, rfl⟩⟩)
      · have hcp : c ≠ p := fun h => (hvonly f d (h ▸ hf)).elim hfe1 hfe2
        have hdp : d ≠ p := fun h => (hvonly f c (h ▸ hf.symm)).elim hfe1 hfe2
        rw [if_neg hcp, if_neg hdp]
        exact Graph.IsLink.reachable (e := f)
          (by rw [reroute_isLink]; exact Or.inr ⟨hfe1, hfe2, hf⟩)

/-- Transport a walk of `K` into `K - e2`, where `v` is a vertex whose only incident edge is the
pendant `e2 = v v2`; the suppressed vertex `v` is sent to `v2`. -/
private theorem deleteEdges_reachable_pendant {α β : Type*} {K : Graph α β} {p v2 : α} {e2 : β}
    (hv2 : p ≠ v2) (he2 : K.IsLink e2 p v2)
    (hvonly : ∀ f x, K.IsLink f p x → f = e2)
    {a b : α} (h : K.Reachable a b) :
    (K.deleteEdges {e2}).Reachable (if a = p then v2 else a) (if b = p then v2 else b) := by
  induction h with
  | refl => exact Graph.Reachable.refl _ _
  | @tail c d hac hcd ih =>
    refine ih.trans ?_
    obtain ⟨f, hf⟩ := hcd
    by_cases hfe2 : f = e2
    · subst hfe2
      rcases hf.eq_and_eq_or_eq_and_eq he2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [if_pos rfl, if_neg (Ne.symm hv2)]
      · rw [if_neg (Ne.symm hv2), if_pos rfl]
    · have hcp : c ≠ p := fun h => hfe2 (hvonly f d (h ▸ hf))
      have hdp : d ≠ p := fun h => hfe2 (hvonly f c (h ▸ hf.symm))
      rw [if_neg hcp, if_neg hdp]
      exact Graph.IsLink.reachable (e := f)
        (by rw [Graph.deleteEdges_isLink]; exact ⟨hf, by simpa using hfe2⟩)

/-- **Move D2 / SP preserve bridgelessness (degree-2 form).** Suppressing a degree-2 vertex
by rerouting preserves bridgelessness. -/
theorem bridgeless_reroute_of_degree_two {v1 v2 : α} {e1 e2 : β}
    (hbr : G.Bridgeless) (hll : G.IsLoopless) (hdeg : G.degree v = 2)
    (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2) :
    (reroute G v1 v2 e1 e2).Bridgeless := by
  have hv1 : v ≠ v1 := fun h => hll e1 v (h ▸ he1)
  have hv2 : v ≠ v2 := fun h => hll e2 v (h ▸ he2)
  -- `v`'s only incident edges are `e1` and `e2`
  have hvonly : ∀ f x, G.IsLink f v x → f = e1 ∨ f = e2 := by
    intro f x hf
    have hcard2 : (G.incidenceSet v).ncard = 2 := by
      rw [← hll.degree_eq_ncard_incidenceSet]; exact hdeg
    have hfin : (G.incidenceSet v).Finite := Set.finite_of_ncard_ne_zero (by rw [hcard2]; norm_num)
    have hsub : ({e1, e2} : Set β) ⊆ G.incidenceSet v := by
      rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨(G.mem_incidenceSet v e1).2 he1.inc_left, (G.mem_incidenceSet v e2).2 he2.inc_left⟩
    have heq : G.incidenceSet v = ({e1, e2} : Set β) :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard2, Set.ncard_pair hne]) hfin).symm
    have hfinc : f ∈ G.incidenceSet v := (G.mem_incidenceSet v f).2 hf.inc_left
    rw [heq] at hfinc
    simpa using hfinc
  -- for the reroute, deleting an edge `≠ e1, e2` commutes with the reroute up to `≤`
  have hle_gen : ∀ f, f ≠ e1 → f ≠ e2 →
      reroute (G.deleteEdges {f}) v1 v2 e1 e2 ≤ (reroute G v1 v2 e1 e2).deleteEdges {f} := by
    intro f hfe1 hfe2
    refine ⟨fun x hx => hx, ?_⟩
    intro g x y hg
    rw [reroute_isLink] at hg
    rw [Graph.deleteEdges_isLink, reroute_isLink]
    rcases hg with ⟨rfl, hmem, hxy⟩ | ⟨hge1, hge2, hglink⟩
    · rw [Graph.vertexSet_deleteEdges] at hmem
      exact ⟨Or.inl ⟨rfl, hmem, hxy⟩, by simpa using hfe1.symm⟩
    · rw [Graph.deleteEdges_isLink] at hglink
      exact ⟨Or.inr ⟨hge1, hge2, hglink.1⟩, by simpa using hglink.2⟩
  -- deleting `e1` from the reroute agrees with deleting `{e1, e2}` from `G` up to `≤`
  have hle_e1 : G.deleteEdges ({e1} ∪ {e2}) ≤ (reroute G v1 v2 e1 e2).deleteEdges {e1} := by
    refine ⟨fun x hx => hx, ?_⟩
    intro g x y hg
    rw [Graph.deleteEdges_isLink] at hg
    obtain ⟨hglink, hgmem⟩ := hg
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hgmem
    rw [Graph.deleteEdges_isLink, reroute_isLink]
    exact ⟨Or.inr ⟨hgmem.1, hgmem.2, hglink⟩, by simpa using hgmem.1⟩
  apply Graph.bridgeless_of_forall_reachable
  intro f hf x y hlink
  rw [reroute_isLink] at hlink
  rcases hlink with ⟨hfeq, hmem, hxy⟩ | ⟨hfe1, hfe2, hglink⟩
  · -- `f = e1`, relabelled to join `v1`–`v2`
    rw [hfeq]
    have hnb : ¬ G.IsBridge e1 := hbr.not_isBridge e1
    have hr : (G.deleteEdges {e1}).Reachable v v1 := by
      by_contra hc; exact hnb ⟨v, v1, he1, hc⟩
    -- in `G - e1`, `v`'s only edge is the pendant `e2`
    have he2' : (G.deleteEdges {e1}).IsLink e2 v v2 := by
      rw [Graph.deleteEdges_isLink]; exact ⟨he2, by simpa using hne.symm⟩
    have hvonly' : ∀ g x, (G.deleteEdges {e1}).IsLink g v x → g = e2 := by
      intro g x hg
      rw [Graph.deleteEdges_isLink] at hg
      exact (hvonly g x hg.1).resolve_left (by simpa using hg.2)
    have hpend := deleteEdges_reachable_pendant hv2 he2' hvonly' hr.symm
    rw [if_neg hv1.symm, if_pos rfl] at hpend
    -- `(G - e1) - e2 = G.deleteEdges ({e1} ∪ {e2})`
    rw [Graph.deleteEdges_deleteEdges] at hpend
    have hbase : ((reroute G v1 v2 e1 e2).deleteEdges {e1}).Reachable v1 v2 := hpend.mono hle_e1
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hbase
    · exact hbase.symm
  · -- `f ≠ e1, e2`: `f` keeps its `G`-incidences
    have hfG : f ∈ E(G) := hglink.edge_mem
    have hnb : ¬ G.IsBridge f := hbr.not_isBridge f
    have hr : (G.deleteEdges {f}).Reachable x y := by
      by_contra hc; exact hnb ⟨x, y, hglink, hc⟩
    -- `x, y ≠ v` since `f` is not incident to `v`
    have hxv : x ≠ v := fun h => (hvonly f y (h ▸ hglink)).elim hfe1 hfe2
    have hyv : y ≠ v := fun h => (hvonly f x (h ▸ hglink.symm)).elim hfe1 hfe2
    have he1' : (G.deleteEdges {f}).IsLink e1 v v1 := by
      rw [Graph.deleteEdges_isLink]; exact ⟨he1, by simpa using hfe1.symm⟩
    have he2' : (G.deleteEdges {f}).IsLink e2 v v2 := by
      rw [Graph.deleteEdges_isLink]; exact ⟨he2, by simpa using hfe2.symm⟩
    have hvonly' : ∀ g x, (G.deleteEdges {f}).IsLink g v x → g = e1 ∨ g = e2 := by
      intro g x hg
      rw [Graph.deleteEdges_isLink] at hg
      exact hvonly g x hg.1
    have hmap := reroute_reachable_map hv1 hv2 he1' he2' hvonly' hr
    rw [if_neg hxv, if_neg hyv] at hmap
    exact hmap.mono (hle_gen f hfe1 hfe2)

/-! The CDC-lift lemmas for the reroute (`cdc_lift_reroute_degree_two`, `cdc_lift_reroute_split`)
require Veblen's cycle decomposition, so they are proved in `EvenLift.lean`. -/

end Workspace.PriorWorkProofs.Jaeger
