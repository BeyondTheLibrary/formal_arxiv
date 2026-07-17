import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.PriorWorkProofs.EightFlow.NashWilliams

open Set
open scoped Graph

namespace Workspace.PriorWorkProofs.EightFlow

variable {α β : Type*} {G : Graph α β}

/-- Membership in `cutEdges` unfolds to the defining conjunction. -/
theorem mem_cutEdges {G : Graph α β} {S : Set α} {e : β} :
    e ∈ cutEdges G S ↔ e ∈ E(G) ∧ ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S := Iff.rfl

/-! ### G1 — a walk crossing a cut uses a crossing edge -/

theorem exists_cross_of_reachable {H : Graph α β} {x y : α} (S : Set α)
    (hx : x ∈ S) (hy : y ∉ S) (h : H.Reachable x y) :
    ∃ e a b, H.IsLink e a b ∧ a ∈ S ∧ b ∉ S := by
  rw [Graph.reachable_def] at h
  revert hy
  induction h with
  | refl => intro hy; exact absurd hx hy
  | @tail b c hab hbc ih =>
      intro hc
      by_cases hb : b ∈ S
      · obtain ⟨e, he⟩ := hbc
        exact ⟨e, b, c, he, hb, hc⟩
      · exact ih hb

/-! ### G2 — connected ⇔ every nontrivial cut is nonempty -/

theorem exists_cross_of_connected (hconn : G.Connected) {S : Set α}
    (hSne : S.Nonempty) (hScompl : (V(G) \ S).Nonempty) (hS : S ⊆ V(G)) :
    ∃ e a b, G.IsLink e a b ∧ a ∈ S ∧ b ∉ S := by
  obtain ⟨a, ha⟩ := hSne
  obtain ⟨b, hbV, hbnS⟩ := hScompl
  have haV : a ∈ V(G) := hS ha
  have hr : G.Reachable a b := hconn.reachable haV hbV
  exact exists_cross_of_reachable S ha hbnS hr

theorem cutEdges_nonempty_of_connected (hconn : G.Connected) {S : Set α}
    (hSne : S.Nonempty) (hScompl : (V(G) \ S).Nonempty) (hS : S ⊆ V(G)) :
    (cutEdges G S).Nonempty := by
  obtain ⟨e, a, b, hab, haS, hbnS⟩ := exists_cross_of_connected hconn hSne hScompl hS
  exact ⟨e, by rw [mem_cutEdges]; exact ⟨hab.edge_mem, a, b, hab, haS, hbnS⟩⟩

theorem connected_of_cutEdges_pos (hne : V(G).Nonempty)
    (h : ∀ S : Set α, S.Nonempty → S ⊆ V(G) → (V(G) \ S).Nonempty → (cutEdges G S).Nonempty) :
    G.Connected := by
  obtain ⟨v₀, hv₀⟩ := hne
  by_cases hEq : ∀ y ∈ V(G), G.Reachable v₀ y
  · exact Graph.connected_of_forall_reachable hv₀ hEq
  · push_neg at hEq
    obtain ⟨w, hwV, hwnr⟩ := hEq
    set S₀ : Set α := {z ∈ V(G) | G.Reachable v₀ z} with hS₀
    have hv₀S : v₀ ∈ S₀ := by rw [hS₀]; exact ⟨hv₀, Graph.Reachable.rfl⟩
    have hS₀sub : S₀ ⊆ V(G) := by rw [hS₀]; intro z hz; exact hz.1
    have hwnS : w ∉ S₀ := by rw [hS₀]; intro hz; exact hwnr hz.2
    obtain ⟨e, he⟩ := h S₀ ⟨v₀, hv₀S⟩ hS₀sub ⟨w, hwV, hwnS⟩
    rw [mem_cutEdges] at he
    obtain ⟨_, a, b, hab, haS, hbnS⟩ := he
    rw [hS₀] at haS
    exfalso
    apply hbnS
    rw [hS₀]
    exact ⟨hab.right_mem, haS.2.tail ⟨e, hab⟩⟩

/-! ### G3 — bridgeless ⇔ no nontrivial 1-edge cut -/

theorem cutEdges_ne_one_of_bridgeless (hbr : G.Bridgeless) {S : Set α}
    (hSne : S.Nonempty) (hS : S ⊆ V(G)) (hScompl : (V(G) \ S).Nonempty) :
    (cutEdges G S).ncard ≠ 1 := by
  intro hone
  rw [Set.ncard_eq_one] at hone
  obtain ⟨e, heq⟩ := hone
  have hemem : e ∈ cutEdges G S := by rw [heq]; exact Set.mem_singleton e
  rw [mem_cutEdges] at hemem
  obtain ⟨heE, x, y, hxy, hxS, hynS⟩ := hemem
  have hbridge : G.IsBridge e := by
    refine ⟨x, y, hxy, ?_⟩
    intro hr
    obtain ⟨e', a, b, hab, haS, hbnS⟩ := exists_cross_of_reachable S hxS hynS hr
    rw [Graph.deleteEdges_isLink] at hab
    obtain ⟨hab', hne⟩ := hab
    have hmem' : e' ∈ cutEdges G S := by
      rw [mem_cutEdges]; exact ⟨hab'.edge_mem, a, b, hab', haS, hbnS⟩
    rw [heq] at hmem'
    exact hne hmem'
  exact hbr.not_isBridge e hbridge

/-! ### G4 — connected from 3-edge-connected -/

theorem connected_of_isEdgeConnected3 (h : IsEdgeConnected G 3) : G.Connected := by
  obtain ⟨h2V, hcut⟩ := h
  have hVne : V(G).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  refine connected_of_cutEdges_pos hVne ?_
  intro S hSne hSsub hScompl
  have h3 := hcut S hSne hSsub hScompl
  exact Set.nonempty_of_ncard_ne_zero (by omega)

/-! ### G5 — extraction of a two-edge cut -/

theorem exists_two_edge_cut (hE : E(G).Finite) (hbr : G.Bridgeless)
    (hconn : G.Connected) (hn3 : ¬ IsEdgeConnected G 3) (h2V : 2 ≤ V(G).ncard) :
    ∃ (S : Set α) (e₁ e₂ : β) (x y : α),
      S.Nonempty ∧ S ⊆ V(G) ∧ (V(G) \ S).Nonempty ∧
      e₁ ≠ e₂ ∧ cutEdges G S = {e₁, e₂} ∧
      G.IsLink e₁ x y ∧ x ∈ S ∧ y ∉ S ∧ x ≠ y ∧ e₂ ∈ E(G) := by
  have hn3' : ∃ S : Set α, S.Nonempty ∧ S ⊆ V(G) ∧ (V(G) \ S).Nonempty ∧
      (cutEdges G S).ncard < 3 := by
    by_contra hcon
    push_neg at hcon
    exact hn3 ⟨h2V, fun S hs hsub hcompl => hcon S hs hsub hcompl⟩
  obtain ⟨S, hSne, hSsub, hScompl, hlt⟩ := hn3'
  have hfin : (cutEdges G S).Finite := hE.subset (fun e he => (mem_cutEdges.mp he).1)
  have hpos : (cutEdges G S).Nonempty := cutEdges_nonempty_of_connected hconn hSne hScompl hSsub
  have hne1 : (cutEdges G S).ncard ≠ 1 := cutEdges_ne_one_of_bridgeless hbr hSne hSsub hScompl
  have h1 : 1 ≤ (cutEdges G S).ncard := (Set.ncard_pos hfin).mpr hpos
  have h2 : (cutEdges G S).ncard = 2 := by omega
  rw [Set.ncard_eq_two] at h2
  obtain ⟨e₁, e₂, hne12, heq⟩ := h2
  have he1mem : e₁ ∈ cutEdges G S := by rw [heq]; exact Set.mem_insert e₁ _
  rw [mem_cutEdges] at he1mem
  obtain ⟨he1E, x, y, hxy, hxS, hynS⟩ := he1mem
  have hxy_ne : x ≠ y := fun hxeqy => hynS (hxeqy ▸ hxS)
  have he2mem : e₂ ∈ cutEdges G S := by rw [heq]; exact Set.mem_insert_of_mem _ rfl
  have he2E : e₂ ∈ E(G) := (mem_cutEdges.mp he2mem).1
  exact ⟨S, e₁, e₂, x, y, hSne, hSsub, hScompl, hne12, heq, hxy, hxS, hynS, hxy_ne, he2E⟩

end Workspace.PriorWorkProofs.EightFlow
