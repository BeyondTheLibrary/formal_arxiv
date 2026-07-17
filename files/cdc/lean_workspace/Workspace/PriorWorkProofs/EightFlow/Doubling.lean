import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.PriorWorkProofs.EightFlow.NashWilliams
import Workspace.PriorWork.NashWilliamsTutte

/-!
# Multigraph doubling and the doubling + projection step (Lemmas 3–4)

The graph-surgery infrastructure behind `three_spanning_trees_cover`: the edge-doubled multigraph
`double G : Graph α (β × Bool)` with its cut-size doubling and `6`-edge-connectivity, the
projection `π = Prod.fst` of a spanning tree of `2G` back to `G`, and the pigeonhole that every
edge lies outside some tree. Assembled into `doubling_covering`.
-/

open Set
open scoped Graph

namespace Workspace.PriorWorkProofs.EightFlow

variable {α β : Type*}

/-! ## A connected finite multigraph has at least `|V| - 1` edges -/

/-- The simple graph on the vertex subtype `↥V(H)` underlying a multigraph `H`: two distinct
vertices are adjacent iff they are joined by some edge of `H`. Parallel edges and loops are
collapsed, so its edge count is a *lower bound* proxy for `|E(H)|`. -/
def toSimpleGraph (H : Graph α β) : SimpleGraph ↥V(H) :=
  SimpleGraph.fromRel (fun a b => H.Adj a.1 b.1)

/-- Reachability in `H` lifts to reachability in `toSimpleGraph H`. -/
theorem toSimpleGraph_reachable (H : Graph α β) {x y : α} (hx : x ∈ V(H))
    (h : H.Reachable x y) : ∀ (hy : y ∈ V(H)),
      (toSimpleGraph H).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => intro hy; exact SimpleGraph.Reachable.refl _
  | @tail b c hxb hbc ih =>
      intro hc
      have hb : b ∈ V(H) := hbc.left_mem
      refine (ih hb).trans ?_
      by_cases hbc' : b = c
      · subst hbc'; exact SimpleGraph.Reachable.refl _
      · refine (show (toSimpleGraph H).Adj ⟨b, hb⟩ ⟨c, hc⟩ from ?_).reachable
        rw [toSimpleGraph, SimpleGraph.fromRel_adj]
        exact ⟨fun h => hbc' (Subtype.ext_iff.mp h), Or.inl hbc⟩

/-- `toSimpleGraph H` is connected whenever `H` is. -/
theorem toSimpleGraph_connected (H : Graph α β) (hconn : H.Connected) :
    (toSimpleGraph H).Connected := by
  obtain ⟨v₀, hv₀⟩ := hconn.nonempty
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨v₀, hv₀⟩⟩⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩
  exact toSimpleGraph_reachable H ha (hconn.reachable ha hb) hb

open Classical in
/-- A choice of `Sym2`-edge of `toSimpleGraph H` for each `β`-edge: the endpoints of `e`,
lifted to the vertex subtype (junk `s(v₀, v₀)` off `E(H)`). -/
noncomputable def emap (H : Graph α β) (v₀ : ↥V(H)) (e : β) : Sym2 ↥V(H) :=
  if h : ∃ x y, H.IsLink e x y then
    s(⟨h.choose, h.choose_spec.choose_spec.left_mem⟩,
      ⟨h.choose_spec.choose, h.choose_spec.choose_spec.right_mem⟩)
  else s(v₀, v₀)

/-- **Connected ⟹ `|V| ≤ |E| + 1`.** A connected multigraph with finitely many vertices and
edges has at least `|V(H)| - 1` edges. Proved by transporting to `toSimpleGraph H` and applying
`SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one`; the simple graph's edges inject (via
`emap`) into `E(H)`, so its edge count bounds `|E(H)|`. -/
theorem connected_ncard_le (H : Graph α β) (hV : V(H).Finite) (hE : E(H).Finite)
    (hconn : H.Connected) : V(H).ncard ≤ E(H).ncard + 1 := by
  classical
  haveI : Finite ↥V(H) := hV.to_subtype
  obtain ⟨v₀, hv₀⟩ := hconn.nonempty
  have hSc := (toSimpleGraph_connected H hconn).card_vert_le_card_edgeSet_add_one
  have hcard_v : Nat.card ↥V(H) = V(H).ncard := Nat.card_coe_set_eq _
  -- the simple-graph edge set embeds into the image of `E(H)` under `emap`
  have hsub : (toSimpleGraph H).edgeSet ⊆ (emap H ⟨v₀, hv₀⟩) '' E(H) := by
    intro s hs
    induction s using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeSet, toSimpleGraph, SimpleGraph.fromRel_adj] at hs
      obtain ⟨hne, hor⟩ := hs
      -- pick an edge joining a.1 and b.1 (either orientation)
      obtain ⟨e, hlink⟩ : ∃ e, H.IsLink e a.1 b.1 := by
        rcases hor with h | h
        · exact h
        · obtain ⟨e, he⟩ := h; exact ⟨e, he.symm⟩
      refine ⟨e, hlink.edge_mem, ?_⟩
      have hex : ∃ x y, H.IsLink e x y := ⟨a.1, b.1, hlink⟩
      have hspec := hex.choose_spec.choose_spec
      rw [emap, dif_pos hex]
      -- endpoints of `e` are `{a.1, b.1}` up to swap
      rcases hspec.eq_and_eq_or_eq_and_eq hlink with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · apply Sym2.eq_iff.mpr; left
        exact ⟨Subtype.ext h1, Subtype.ext h2⟩
      · apply Sym2.eq_iff.mpr; right
        exact ⟨Subtype.ext h1, Subtype.ext h2⟩
  have hfin_img : ((emap H ⟨v₀, hv₀⟩) '' E(H)).Finite := hE.image _
  have hbound : Nat.card ↥(toSimpleGraph H).edgeSet ≤ E(H).ncard := by
    rw [Nat.card_coe_set_eq]
    calc (toSimpleGraph H).edgeSet.ncard
        ≤ ((emap H ⟨v₀, hv₀⟩) '' E(H)).ncard := Set.ncard_le_ncard hsub hfin_img
      _ ≤ E(H).ncard := Set.ncard_image_le hE
  omega

/-! ## The edge-doubled multigraph `2G` -/

/-- The **edge-doubled** multigraph `2G := double G : Graph α (β × Bool)`: the vertex set is that
of `G`, and each edge is replaced by two parallel copies `(e, false)`, `(e, true)` with the same
incidence as `e`. The projection back to `G` is `Prod.fst`. -/
def double (G : Graph α β) : Graph α (β × Bool) where
  vertexSet := V(G)
  IsLink p x y := G.IsLink p.1 x y
  isLink_symm := by rintro p hp x y h; exact h.symm
  eq_or_eq_of_isLink_of_isLink := by rintro p x y v w h1 h2; exact h1.left_eq_or_eq h2
  left_mem_of_isLink := by rintro p x y h; exact h.left_mem

@[simp] lemma double_isLink (G : Graph α β) (p : β × Bool) (x y : α) :
    (double G).IsLink p x y ↔ G.IsLink p.1 x y := Iff.rfl

@[simp] lemma vertexSet_double (G : Graph α β) : V(double G) = V(G) := rfl

lemma vertexSet_double_finite (G : Graph α β) (hV : V(G).Finite) : V(double G).Finite := hV

/-- The edge set of `2G` is the preimage of `E(G)` under the projection: every copy of an edge of
`G`. -/
lemma edgeSet_double (G : Graph α β) : E(double G) = Prod.fst ⁻¹' E(G) := by
  ext p
  rw [Set.mem_preimage]
  constructor
  · intro hp
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet hp
    exact (show G.IsLink p.1 x y from hxy).edge_mem
  · intro hp
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet hp
    exact (show (double G).IsLink p x y from hxy).edge_mem

lemma edgeSet_double_finite (G : Graph α β) (hE : E(G).Finite) : E(double G).Finite := by
  rw [edgeSet_double]
  have hpre : Prod.fst ⁻¹' E(G) = E(G) ×ˢ (Set.univ : Set Bool) := by
    ext p; simp
  rw [hpre]
  exact hE.prod Set.finite_univ

/-- Each cut of `2G` is the preimage of the corresponding cut of `G`. -/
lemma cutEdges_double (G : Graph α β) (S : Set α) :
    cutEdges (double G) S = Prod.fst ⁻¹' (cutEdges G S) := by
  ext p
  simp only [cutEdges, Set.mem_preimage, Set.mem_sep_iff]
  constructor
  · rintro ⟨_, x, y, hxy, hxS, hyS⟩
    exact ⟨(show G.IsLink p.1 x y from hxy).edge_mem, x, y, hxy, hxS, hyS⟩
  · rintro ⟨_, x, y, hxy, hxS, hyS⟩
    exact ⟨(show (double G).IsLink p x y from hxy).edge_mem, x, y, hxy, hxS, hyS⟩

/-- **Lemma 3 (cut doubling).** Every cut of `2G` has exactly twice as many edges as the
corresponding cut of `G`. -/
lemma ncard_cutEdges_double (G : Graph α β) (S : Set α) :
    (cutEdges (double G) S).ncard = 2 * (cutEdges G S).ncard := by
  rw [cutEdges_double]
  have hpre : Prod.fst ⁻¹' (cutEdges G S) = (cutEdges G S) ×ˢ (Set.univ : Set Bool) := by
    ext p; simp
  rw [hpre, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool, mul_comm]

/-- **Lemma 3 (edge-connectivity doubling).** If `G` is `3`-edge-connected then `2G` is
`6`-edge-connected: each cut doubles. -/
lemma isEdgeConnected_double (G : Graph α β) (hconn : IsEdgeConnected G 3) :
    IsEdgeConnected (double G) 6 := by
  obtain ⟨hV2, hcut⟩ := hconn
  refine ⟨hV2, ?_⟩
  intro S hSne hSsub hScompl
  rw [ncard_cutEdges_double]
  have h3 := hcut S hSne hSsub hScompl
  omega

/-! ## Projecting a spanning tree of `2G` back to `G` -/

/-- The projection `π '' T` of an edge set of `2G` down to `G`. -/
def proj (T : Set (β × Bool)) : Set β := Prod.fst '' T

lemma mem_proj {T : Set (β × Bool)} {e : β} : e ∈ proj T ↔ ∃ b, (e, b) ∈ T := by
  simp only [proj, Set.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, by rw [Prod.mk.eta]; exact hp⟩
  · rintro ⟨b, hb⟩; exact ⟨(e, b), hb, rfl⟩

lemma proj_subset (G : Graph α β) {T : Set (β × Bool)} (hT : T ⊆ E(double G)) :
    proj T ⊆ E(G) := by
  intro e he
  rw [mem_proj] at he
  obtain ⟨b, hb⟩ := he
  have hmem : (e, b) ∈ E(double G) := hT hb
  rwa [edgeSet_double, Set.mem_preimage] at hmem

/-- A walk in `(2G).restrict T` projects to a walk in `G.restrict (π T)`. -/
lemma restrict_double_reachable (G : Graph α β) (T : Set (β × Bool)) {x y : α}
    (h : ((double G).restrict T).Reachable x y) :
    (G.restrict (proj T)).Reachable x y := by
  induction h with
  | refl => exact Graph.Reachable.rfl
  | @tail b c _ hbc ih =>
      refine ih.tail ?_
      obtain ⟨p, hp⟩ := hbc
      rw [Graph.restrict_isLink] at hp
      obtain ⟨hpT, hlink⟩ := hp
      refine ⟨p.1, ?_⟩
      rw [Graph.restrict_isLink]
      exact ⟨mem_proj.mpr ⟨p.2, by rw [Prod.mk.eta]; exact hpT⟩, hlink⟩

/-- The projection of a connected spanning subgraph of `2G` is a connected spanning subgraph of
`G`. -/
lemma restrict_double_connected (G : Graph α β) {T : Set (β × Bool)}
    (h : ((double G).restrict T).Connected) : (G.restrict (proj T)).Connected := by
  have hV1 : V((double G).restrict T) = V(G) := by
    rw [Graph.vertexSet_restrict, vertexSet_double]
  have hV2 : V(G.restrict (proj T)) = V(G) := Graph.vertexSet_restrict _ _
  obtain ⟨v₀, hv₀⟩ := h.nonempty
  rw [hV1] at hv₀
  refine Graph.connected_of_forall_reachable (x := v₀) (by rw [hV2]; exact hv₀) ?_
  intro y hy
  rw [hV2] at hy
  exact restrict_double_reachable G T (h.reachable (by rw [hV1]; exact hv₀) (by rw [hV1]; exact hy))

/-- **Lemma 4 (projection is a spanning tree).** The projection of a spanning tree of `2G` is a
spanning tree of `G`. The edge-count equality uses `connected_ncard_le` for the lower bound and
`Set.ncard_image_le` for the upper bound. -/
lemma isSpanningTree_proj (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    {T : Set (β × Bool)} (hT : IsSpanningTree (double G) T) : IsSpanningTree G (proj T) := by
  obtain ⟨hTsub, hTconn, hTcard⟩ := hT
  refine ⟨proj_subset G hTsub, restrict_double_connected G hTconn, ?_⟩
  have hTfin : T.Finite := (edgeSet_double_finite G hE).subset hTsub
  have hup : (proj T).ncard ≤ T.ncard := Set.ncard_image_le hTfin
  have hTcard' : T.ncard + 1 = V(G).ncard := by rwa [vertexSet_double] at hTcard
  have hpsub : proj T ⊆ E(G) := proj_subset G hTsub
  have hErestr : E(G.restrict (proj T)) = proj T := by
    rw [Graph.edgeSet_restrict, Set.inter_eq_right.mpr hpsub]
  have hVrestr : V(G.restrict (proj T)) = V(G) := Graph.vertexSet_restrict _ _
  have hlow : V(G).ncard ≤ (proj T).ncard + 1 := by
    have hc := connected_ncard_le (G.restrict (proj T)) (by rw [hVrestr]; exact hV)
      (by rw [hErestr]; exact hE.subset hpsub) (restrict_double_connected G hTconn)
    rwa [hVrestr, hErestr] at hc
  omega

/-- **The "≤ 2 of 3" pigeonhole.** Three pairwise edge-disjoint edge sets of `2G` project so that
every edge of `G` lies outside at least one projection: each edge has only two copies, and each
copy lies in at most one of the three disjoint sets. -/
lemma proj_cover (G : Graph α β) {T₁ T₂ T₃ : Set (β × Bool)}
    (h12 : Disjoint T₁ T₂) (h13 : Disjoint T₁ T₃) (h23 : Disjoint T₂ T₃) :
    ∀ e ∈ E(G), e ∉ proj T₁ ∨ e ∉ proj T₂ ∨ e ∉ proj T₃ := by
  intro e _
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  rw [mem_proj] at h1 h2 h3
  obtain ⟨b1, hb1⟩ := h1
  obtain ⟨b2, hb2⟩ := h2
  obtain ⟨b3, hb3⟩ := h3
  have hpigeon : b1 = b2 ∨ b1 = b3 ∨ b2 = b3 := by
    rcases b1 <;> rcases b2 <;> rcases b3 <;> tauto
  rcases hpigeon with h | h | h
  · exact (Set.disjoint_left.mp h12 hb1) (by rw [h]; exact hb2)
  · exact (Set.disjoint_left.mp h13 hb1) (by rw [h]; exact hb3)
  · exact (Set.disjoint_left.mp h23 hb2) (by rw [h]; exact hb3)

/-! ## The doubling + projection step (`three_spanning_trees_cover`) -/

/-- **Lemmas 3–4 assembled.** A `3`-edge-connected finite multigraph has three spanning trees
such that every edge lies outside at least one of them. Route: double to `2G` (`6`-edge-connected
by `isEdgeConnected_double`), apply the Nash–Williams axiom to get three edge-disjoint spanning
trees of `2G`, project them back to `G` (`isSpanningTree_proj`), and use the pigeonhole
`proj_cover`. This is exactly the statement of `three_spanning_trees_cover`. -/
theorem doubling_covering (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hconn : IsEdgeConnected G 3) :
    ∃ T₁ T₂ T₃ : Set β,
      IsSpanningTree G T₁ ∧ IsSpanningTree G T₂ ∧ IsSpanningTree G T₃ ∧
        ∀ e ∈ E(G), e ∉ T₁ ∨ e ∉ T₂ ∨ e ∉ T₃ := by
  have hconn6 : IsEdgeConnected (double G) 6 := isEdgeConnected_double G hconn
  obtain ⟨T₁, T₂, T₃, hT₁, hT₂, hT₃, h12, h13, h23⟩ :=
    Workspace.PriorWork.nash_williams_three_edge_disjoint_spanning_trees (double G)
      (vertexSet_double_finite G hV) (edgeSet_double_finite G hE) hconn6
  exact ⟨proj T₁, proj T₂, proj T₃,
    isSpanningTree_proj G hV hE hT₁, isSpanningTree_proj G hV hE hT₂,
    isSpanningTree_proj G hV hE hT₃, proj_cover G h12 h13 h23⟩

end Workspace.PriorWorkProofs.EightFlow
