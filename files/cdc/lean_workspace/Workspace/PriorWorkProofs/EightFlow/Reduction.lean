import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.Types.Gamma
import Workspace.PriorWorkProofs.Tutte.Basic
import Workspace.PriorWorkProofs.EightFlow.EvenSubgraph
import Workspace.PriorWorkProofs.EightFlow.NashWilliams
import Workspace.PriorWorkProofs.EightFlow.Doubling
import Workspace.PriorWorkProofs.EightFlow.CutIdentity
import Workspace.PriorWorkProofs.EightFlow.CutConnectivity
import Workspace.PriorWorkProofs.EightFlow.ContractSurgery
import Workspace.PriorWorkProofs.EightFlow.DisconnectSplit

/-!
# The reduction bridgeless ⟶ 3-edge-connected, and the 8-flow theorem (§3.7)

Proves `bridgeless_gamma_flow`: every finite bridgeless multigraph `G` has a nowhere-zero `Γ`-flow
(`Γ = 𝔽₂³`), by well-founded strong induction on `2 · |E(G)| + |V(G)|`. The cases are: `|V| ≤ 1`
(constant nonzero map, `gamma_flow_of_vertex_le_one`); disconnected (split at a `0`-edge-cut,
`gamma_flow_of_closed_split`); `3`-edge-connected (`gamma_flow_of_isEdgeConnected3`); and connected
but not `3`-edge-connected (contract an edge of a `2`-edge-cut and lift the recursive flow via
`flow_update_iff` and `flow_two_cut`).
-/

open Set
open scoped Graph
open Workspace.Types.Gamma
open Workspace.Types.Orientation
open Workspace.PriorWorkProofs.Tutte

namespace Workspace.PriorWorkProofs.EightFlow

variable {α β : Type*}

/-! ## A fixed nonzero element of `Γ = 𝔽₂³` -/

/-- A concrete nonzero element of `Γ = Fin 3 → F2`. -/
noncomputable def gammaOne : Gamma := fun i => if i = 0 then (1 : F2) else 0

lemma gammaOne_ne_zero : gammaOne ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [gammaOne] at h0

/-! ## The 3-edge-connected case (assembled from the Nash–Williams route) -/

/-- **Proposition 5, flow form.** Every `3`-edge-connected finite multigraph has a nowhere-zero
`Γ`-flow. Assembled from `doubling_covering` (three spanning trees covering `E` outside), the
spanning-tree even cover `spanning_tree_even_cover`, and the payoff
`three_even_subgraphs_cover_gamma_flow`. -/
theorem gamma_flow_of_isEdgeConnected3 (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hconn : IsEdgeConnected G 3) (O : Orientation G) :
    ∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f := by
  have hGc : G.Connected := connected_of_isEdgeConnected3 hconn
  obtain ⟨T₁, T₂, T₃, hT₁, hT₂, hT₃, hcov⟩ := doubling_covering G hV hE hconn
  obtain ⟨H₁, hH₁, hsub₁⟩ := spanning_tree_even_cover G hV hE hGc T₁ hT₁
  obtain ⟨H₂, hH₂, hsub₂⟩ := spanning_tree_even_cover G hV hE hGc T₂ hT₂
  obtain ⟨H₃, hH₃, hsub₃⟩ := spanning_tree_even_cover G hV hE hGc T₃ hT₃
  refine three_even_subgraphs_cover_gamma_flow hE O hH₁ hH₂ hH₃ ?_
  intro e he
  simp only [Set.mem_union]
  rcases hcov e he with h | h | h
  · exact Or.inl (Or.inl (hsub₁ ⟨he, h⟩))
  · exact Or.inl (Or.inr (hsub₂ ⟨he, h⟩))
  · exact Or.inr (hsub₃ ⟨he, h⟩)

/-! ## The degenerate case `|V(G)| ≤ 1` -/

/-- **Base case.** A finite bridgeless multigraph with at most one vertex has a nowhere-zero
`Γ`-flow: every edge is a loop (both ends are the unique vertex), so the constant map `γ₀ ≠ 0`
satisfies the characteristic-two flow criterion (a loop contributes `2 • γ₀ = 0`). -/
theorem gamma_flow_of_vertex_le_one (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hcard : V(G).ncard ≤ 1) (O : Orientation G) :
    ∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f := by
  classical
  have hsub : V(G).Subsingleton := by
    rw [Set.ncard_le_one_iff_eq hV] at hcard
    rcases hcard with h | ⟨a, h⟩
    · rw [h]; exact Set.subsingleton_empty
    · rw [h]; exact Set.subsingleton_singleton
  refine ⟨fun _ => gammaOne, ?_, ?_⟩
  · rw [charTwo_flow_iff_endSum_zero Gamma.add_self hE O]
    intro v hv
    have hzero : ∀ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • gammaOne = 0 := by
      intro e he
      rw [Graph.mem_incidenceSet] at he
      obtain ⟨w, hw⟩ := he
      have hvw : v = w := hsub hv hw.right_mem
      have hloop : G.IsLoopAt e v := by rw [Graph.IsLoopAt]; rw [hvw] at hw ⊢; exact hw
      rw [if_pos hloop, two_nsmul, Gamma.add_self]
    calc (∑ᶠ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • gammaOne)
        = ∑ᶠ e ∈ G.incidenceSet v, (0 : Gamma) := finsum_mem_congr rfl hzero
      _ = 0 := by simp
  · intro e _
    exact gammaOne_ne_zero

/-! ## The main reduction -/

/-- **The 8-flow theorem (Route B).** Every finite bridgeless multigraph has a nowhere-zero
`Γ`-flow, `Γ = 𝔽₂³`. Proved by strong induction on `2 · |E(G)| + |V(G)|`; the only admission on
the whole path is the Nash–Williams–Tutte axiom. This is exactly the shape of
`Workspace.PriorWork.kilpatrick_jaeger_nowhere_zero_gamma_flow`. -/
theorem bridgeless_gamma_flow (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hG : G.Bridgeless) (O : Orientation G) :
    ∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f := by
  classical
  rcases Nat.lt_or_ge (V(G).ncard) 2 with hlt2 | hge2
  · -- |V(G)| ≤ 1
    exact gamma_flow_of_vertex_le_one G hV hE (by omega) O
  · -- |V(G)| ≥ 2
    by_cases hconn : G.Connected
    · by_cases h3 : IsEdgeConnected G 3
      · exact gamma_flow_of_isEdgeConnected3 G hV hE h3 O
      · -- 2-edge-cut: contract e₁, recurse, lift
        obtain ⟨S, e₁, e₂, x, y, hSne, hSsub, hScompl, hne12, hcut, hxy, hxS, hyS, hxney, he₂⟩ :=
          exists_two_edge_cut hE hG hconn h3 hge2
        have he₁G : e₁ ∈ E(G) := hxy.edge_mem
        -- contract facts
        have hbrc : (contract G e₁ x y).Bridgeless := contract_bridgeless hG hxy
        have hVc : V(contract G e₁ x y).Finite := by
          rw [vertexSet_contract]; exact hV.image _
        have hEc : E(contract G e₁ x y).Finite := by
          rw [edgeSet_contract]; exact hE.diff
        -- measure facts for termination
        have hEclt : (E(G) \ {e₁}).ncard < E(G).ncard := by
          have h := edgeSet_contract_ncard_lt (G := G) (e₁ := e₁) (x := x) (y := y) hE he₁G
          rwa [edgeSet_contract] at h
        have hVcle : (mergeMap x y '' V(G)).ncard ≤ V(G).ncard := Set.ncard_image_le hV
        -- recurse on the contraction
        obtain ⟨g, hg_flow, hg_nz⟩ :=
          bridgeless_gamma_flow (contract G e₁ x y) hVc hEc hbrc (contractOrientation O e₁ x y)
        -- normalize g to vanish at e₁ (which is outside E(contract))
        have he₁notin : e₁ ∉ E(contract G e₁ x y) := by
          rw [edgeSet_contract]; simp
        set gc := Function.update g e₁ (0 : Gamma) with hgc
        have hgce : gc e₁ = 0 := by rw [hgc, Function.update_self]
        have hgc_flow : (contract G e₁ x y).IsFlow (contractOrientation O e₁ x y) gc := by
          rw [Graph.isFlow_iff_finset_sum hEc] at hg_flow ⊢
          intro v hv
          have hmem : e₁ ∉ hEc.toFinset := by rw [Set.Finite.mem_toFinset]; exact he₁notin
          have hagree : ∀ e ∈ hEc.toFinset, gc e = g e := by
            intro e he
            rw [hgc, Function.update_of_ne]
            rintro rfl; exact hmem he
          have hL : (∑ e ∈ hEc.toFinset with (contractOrientation O e₁ x y).tail e = v, gc e)
              = ∑ e ∈ hEc.toFinset with (contractOrientation O e₁ x y).tail e = v, g e :=
            Finset.sum_congr rfl (fun e he => hagree e (Finset.mem_of_mem_filter e he))
          have hR : (∑ e ∈ hEc.toFinset with (contractOrientation O e₁ x y).head e = v, gc e)
              = ∑ e ∈ hEc.toFinset with (contractOrientation O e₁ x y).head e = v, g e :=
            Finset.sum_congr rfl (fun e he => hagree e (Finset.mem_of_mem_filter e he))
          rw [hL, hR]; exact hg_flow v hv
        have hgc_nz : ∀ e ∈ E(contract G e₁ x y), gc e ≠ 0 := by
          intro e he
          have hne : e ≠ e₁ := by rintro rfl; exact he₁notin he
          rw [hgc, Function.update_of_ne hne]; exact hg_nz e he
        -- the lift: f is a flow on G
        set f := Function.update gc e₁ (rval O hE e₁ x gc) with hf
        have hf_flow : G.IsFlow O f :=
          (flow_update_iff hE e₁ x y hxy hxney hgce).mp hgc_flow
        -- nowhere-zero
        refine ⟨f, hf_flow, ?_⟩
        intro e he
        by_cases hee : e = e₁
        · rw [hee]
          -- f e₁ = f e₂ via the char-2 cut identity, and f e₂ = gc e₂ = g e₂ ≠ 0
          have h2 : f e₁ + f e₂ = 0 :=
            flow_two_cut Gamma.add_self hV hE O hf_flow hSsub hne12 hcut
          have he₂c : e₂ ∈ E(contract G e₁ x y) := by
            rw [edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff]; exact ⟨he₂, hne12.symm⟩
          have hfe2 : f e₂ = gc e₂ := by
            rw [hf, Function.update_of_ne (Ne.symm hne12)]
          have hge2 : gc e₂ ≠ 0 := hgc_nz e₂ he₂c
          have heq : f e₁ = f e₂ := by
            rw [← add_zero (f e₁), ← Gamma.add_self (f e₂), ← add_assoc, h2, zero_add]
          rw [heq, hfe2]; exact hge2
        · -- e ≠ e₁, e ∈ E(G): f e = gc e = g e ≠ 0
          have hfe : f e = gc e := by rw [hf, Function.update_of_ne hee]
          have hec : e ∈ E(contract G e₁ x y) := by
            rw [edgeSet_contract]; exact ⟨he, hee⟩
          rw [hfe]; exact hgc_nz e hec
    · -- disconnected: 0-edge-cut split
      have hVne : V(G).Nonempty := by
        rw [← Set.ncard_pos hV]; omega
      have hnot : ¬ ∀ (T : Set α), T.Nonempty → T ⊆ V(G) → (V(G) \ T).Nonempty →
          (cutEdges G T).Nonempty := by
        intro hall; exact hconn (connected_of_cutEdges_pos hVne hall)
      push_neg at hnot
      obtain ⟨S, hSne, hSsub, hScompl, hcutne⟩ := hnot
      -- closedness of S under adjacency
      have hclosed : ∀ e a b, G.IsLink e a b → (a ∈ S ↔ b ∈ S) := by
        intro e a b hlink
        constructor
        · intro ha; by_contra hb
          have : e ∈ cutEdges G S := ⟨hlink.edge_mem, a, b, hlink, ha, hb⟩
          rw [hcutne] at this; exact this
        · intro hb; by_contra ha
          have : e ∈ cutEdges G S := ⟨hlink.edge_mem, b, a, hlink.symm, hb, ha⟩
          rw [hcutne] at this; exact this
      have hclosed' : ∀ e a b, G.IsLink e a b → (a ∈ V(G) \ S ↔ b ∈ V(G) \ S) := by
        intro e a b hlink
        have ha : a ∈ V(G) := hlink.left_mem
        have hb : b ∈ V(G) := hlink.right_mem
        have := hclosed e a b hlink
        simp only [Set.mem_diff, ha, hb, true_and]
        tauto
      -- V-decrease facts (both sides strictly fewer vertices, |E| non-increasing)
      have hVS : V(G.induce S) = S := rfl
      have hVSc : V(G.induce (V(G) \ S)) = V(G) \ S := rfl
      have hSlt : S.ncard < V(G).ncard := by
        apply Set.ncard_lt_ncard _ hV
        obtain ⟨z, hz⟩ := hScompl
        exact ⟨hSsub, fun h => hz.2 (h hz.1)⟩
      have hSclt : (V(G) \ S).ncard < V(G).ncard := by
        apply Set.ncard_lt_ncard _ hV
        obtain ⟨w, hw⟩ := hSne
        refine ⟨Set.diff_subset, fun h => ?_⟩
        exact (h (hSsub hw)).2 hw
      have hES : (E(G.induce S)).ncard ≤ E(G).ncard :=
        Set.ncard_le_ncard ((Graph.induce_le hSsub).edgeSet_mono) hE
      have hESc : (E(G.induce (V(G) \ S))).ncard ≤ E(G).ncard :=
        Set.ncard_le_ncard ((Graph.induce_le Set.diff_subset).edgeSet_mono) hE
      have hVSn : (V(G.induce S)).ncard < V(G).ncard := by rw [hVS]; exact hSlt
      have hVScn : (V(G.induce (V(G) \ S))).ncard < V(G).ncard := by rw [hVSc]; exact hSclt
      -- solve each induced subgraph by the IH
      refine gamma_flow_of_closed_split hV hE hSsub hclosed ?hA ?hB O
      · intro O'
        exact bridgeless_gamma_flow (G.induce S)
          (by rw [hVS]; exact hV.subset hSsub)
          (hE.subset ((Graph.induce_le hSsub).edgeSet_mono))
          (induce_bridgeless hG hclosed) O'
      · intro O'
        exact bridgeless_gamma_flow (G.induce (V(G) \ S))
          (by rw [hVSc]; exact hV.diff)
          (hE.subset ((Graph.induce_le Set.diff_subset).edgeSet_mono))
          (induce_bridgeless hG hclosed') O'
termination_by 2 * E(G).ncard + V(G).ncard
decreasing_by
  all_goals simp_wf
  all_goals omega

end Workspace.PriorWorkProofs.EightFlow
