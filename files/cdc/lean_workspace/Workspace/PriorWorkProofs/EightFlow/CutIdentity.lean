import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.Types.Gamma
import Workspace.PriorWorkProofs.EightFlow.NashWilliams
import Workspace.PriorWorkProofs.EightFlow.EvenSubgraph

/-!
# The cut sum of a flow (handshake / double-counting)

For any characteristic-two `A`-flow `f` of a finite multigraph `G` and any `S ⊆ V(G)`, the sum of
`f` over the edge cut of `S` is zero (`flow_cutSum_zero`), by the classical double-counting
argument. The corollary `flow_two_cut` specialises to a two-edge cut `{e₁, e₂}`: `f e₁ + f e₂ = 0`.
-/

open Set
open scoped Graph
open scoped Classical
open Workspace.Types.Gamma
open Workspace.Types.Orientation

namespace Workspace.PriorWorkProofs.EightFlow

variable {α β : Type*} {G : Graph α β}

/-- Membership in the edge cut, unfolded. -/
private lemma mem_cutEdges_iff {S : Set α} {e : β} :
    e ∈ cutEdges G S ↔ e ∈ E(G) ∧ ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S :=
  Iff.rfl

/-- The per-edge contribution to the double count. For an edge `e ∈ E(G)`, the number of its ends
lying in `S` (each end counted, `f e` per end) equals `f e` iff `e` is a cut edge, and cancels
(`2 • f e = 0` in characteristic two) or vanishes otherwise. -/
private lemma cut_edge_end_sum {A : Type*} [AddCommGroup A] (hchar : ∀ a : A, a + a = 0)
    (O : Orientation G) (f : β → A) (S : Set α) {e : β} (he : e ∈ E(G)) :
    ((if O.tail e ∈ S then f e else 0) + (if O.head e ∈ S then f e else 0))
      = if e ∈ cutEdges G S then f e else 0 := by
  classical
  have hmem : e ∈ cutEdges G S ↔
      (O.tail e ∈ S ∧ O.head e ∉ S) ∨ (O.head e ∈ S ∧ O.tail e ∉ S) := by
    rw [mem_cutEdges_iff]
    constructor
    · rintro ⟨-, x, y, hlink, hx, hy⟩
      rcases (O.isLink_iff he).1 hlink with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · exact Or.inl ⟨by rw [ht]; exact hx, by rw [hh]; exact hy⟩
      · exact Or.inr ⟨by rw [hh]; exact hx, by rw [ht]; exact hy⟩
    · rintro (⟨ht, hh⟩ | ⟨hh, ht⟩)
      · exact ⟨he, O.tail e, O.head e, O.isLink_tail_head he, ht, hh⟩
      · exact ⟨he, O.head e, O.tail e, O.isLink_head_tail he, hh, ht⟩
  by_cases ht : O.tail e ∈ S
  · by_cases hh : O.head e ∈ S
    · have hcut : e ∉ cutEdges G S := by rw [hmem]; tauto
      rw [if_pos ht, if_pos hh, if_neg hcut]; exact hchar _
    · have hcut : e ∈ cutEdges G S := by rw [hmem]; tauto
      rw [if_pos ht, if_neg hh, if_pos hcut, add_zero]
  · by_cases hh : O.head e ∈ S
    · have hcut : e ∈ cutEdges G S := by rw [hmem]; tauto
      rw [if_neg ht, if_pos hh, if_pos hcut, zero_add]
    · have hcut : e ∉ cutEdges G S := by rw [hmem]; tauto
      rw [if_neg ht, if_neg hh, if_neg hcut, add_zero]

/-- **The cut sum of a flow vanishes** (handshake / double counting). For a flow `f` valued in a
characteristic-two group and any `S ⊆ V(G)`, the sum of `f` over the edges of the cut `∂S` is
zero. -/
theorem flow_cutSum_zero {A : Type*} [AddCommGroup A] (hchar : ∀ a : A, a + a = 0)
    (hV : V(G).Finite) (hE : E(G).Finite) (O : Orientation G) {f : β → A}
    (hf : G.IsFlow O f) {S : Set α} (hS : S ⊆ V(G)) :
    (∑ᶠ e ∈ cutEdges G S, f e) = 0 := by
  classical
  haveI hdec : DecidableEq α := Classical.decEq α
  have hSfin : S.Finite := hV.subset hS
  have hcut_sub : cutEdges G S ⊆ E(G) := fun e he => (mem_cutEdges_iff.1 he).1
  have hcutfin : (cutEdges G S).Finite := hE.subset hcut_sub
  have hflow := (Graph.isFlow_iff_finset_sum hE).1 hf
  -- Sum of tails over S, reorganised by edge.
  have hTS : (∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset with O.tail e = v, f e)
      = ∑ e ∈ hE.toFinset, if O.tail e ∈ S then f e else 0 := by
    calc (∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset with O.tail e = v, f e)
        = ∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset, (if O.tail e = v then f e else 0) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_filter]
      _ = ∑ e ∈ hE.toFinset, ∑ v ∈ hSfin.toFinset, (if O.tail e = v then f e else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ hE.toFinset, if O.tail e ∈ S then f e else 0 := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          simp only [Finset.sum_ite_eq, Set.Finite.mem_toFinset]
  -- Sum of heads over S, reorganised by edge.
  have hHS : (∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset with O.head e = v, f e)
      = ∑ e ∈ hE.toFinset, if O.head e ∈ S then f e else 0 := by
    calc (∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset with O.head e = v, f e)
        = ∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset, (if O.head e = v then f e else 0) := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.sum_filter]
      _ = ∑ e ∈ hE.toFinset, ∑ v ∈ hSfin.toFinset, (if O.head e = v then f e else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ hE.toFinset, if O.head e ∈ S then f e else 0 := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          simp only [Finset.sum_ite_eq, Set.Finite.mem_toFinset]
  -- The aggregated cut sum equals the double sum over vertices of S.
  have agg : (∑ e ∈ hE.toFinset, if e ∈ cutEdges G S then f e else 0)
      = ∑ v ∈ hSfin.toFinset,
          ((∑ e ∈ hE.toFinset with O.tail e = v, f e)
            + (∑ e ∈ hE.toFinset with O.head e = v, f e)) := by
    calc (∑ e ∈ hE.toFinset, if e ∈ cutEdges G S then f e else 0)
        = ∑ e ∈ hE.toFinset,
            ((if O.tail e ∈ S then f e else 0) + (if O.head e ∈ S then f e else 0)) := by
          refine Finset.sum_congr rfl (fun e he => ?_)
          rw [cut_edge_end_sum hchar O f S (hE.mem_toFinset.1 he)]
      _ = (∑ e ∈ hE.toFinset, if O.tail e ∈ S then f e else 0)
            + (∑ e ∈ hE.toFinset, if O.head e ∈ S then f e else 0) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset with O.tail e = v, f e)
            + (∑ v ∈ hSfin.toFinset, ∑ e ∈ hE.toFinset with O.head e = v, f e) := by
          rw [← hTS, ← hHS]
      _ = ∑ v ∈ hSfin.toFinset,
            ((∑ e ∈ hE.toFinset with O.tail e = v, f e)
              + (∑ e ∈ hE.toFinset with O.head e = v, f e)) := by
          rw [← Finset.sum_add_distrib]
  -- The double sum over vertices of S is zero: each vertex contributes tail = head, so 2•=0.
  have zero : (∑ v ∈ hSfin.toFinset,
      ((∑ e ∈ hE.toFinset with O.tail e = v, f e)
        + (∑ e ∈ hE.toFinset with O.head e = v, f e))) = 0 := by
    refine Finset.sum_eq_zero (fun v hv => ?_)
    have hvV : v ∈ V(G) := hS (hSfin.mem_toFinset.1 hv)
    rw [← hflow v hvV]
    exact hchar _
  have hzero : (∑ e ∈ hE.toFinset, if e ∈ cutEdges G S then f e else 0) = 0 := agg.trans zero
  -- Convert the target finsum into the finset sum we just showed is zero.
  have hfilter : hcutfin.toFinset = hE.toFinset.filter (· ∈ cutEdges G S) := by
    ext e
    simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨hcut_sub h, h⟩, fun h => h.2⟩
  rw [← hcutfin.coe_toFinset, finsum_mem_coe_finset, hfilter, Finset.sum_filter]
  exact hzero

/-- **Two-edge cut corollary.** If the cut of `S` is exactly the two-element set `{e₁, e₂}`, then
`f e₁ + f e₂ = 0`. -/
theorem flow_two_cut {A : Type*} [AddCommGroup A] (hchar : ∀ a : A, a + a = 0)
    (hV : V(G).Finite) (hE : E(G).Finite) (O : Orientation G) {f : β → A}
    (hf : G.IsFlow O f) {S : Set α} (hS : S ⊆ V(G)) {e₁ e₂ : β} (hne : e₁ ≠ e₂)
    (hcut : cutEdges G S = {e₁, e₂}) :
    f e₁ + f e₂ = 0 := by
  have h := flow_cutSum_zero hchar hV hE O hf hS
  rw [hcut] at h
  rwa [finsum_mem_pair hne] at h

end Workspace.PriorWorkProofs.EightFlow
