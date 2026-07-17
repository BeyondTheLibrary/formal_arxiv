import Workspace.Types.Flow

/-!
# Tutte's group-flow theorem — foundational infrastructure

Graph/flow infrastructure for the group-flow theorem:

* **Flow count** `flowCount G O Γ : ℕ` — the number of nowhere-zero `Γ`-flows of `G`
  w.r.t. `O`, counted as *normalized* flows (nowhere-zero on `E(G)`, vanishing off it, so
  each observable flow has one representative), together with finiteness (`flowSet_finite`).
  This is the `n(G, Γ)` of the paper.

* **Edge deletion** `G − e := G.deleteEdges {e}` (a thin wrapper on Mathlib's
  `Graph.deleteEdges`), with its basic API.

* **Edge contraction** `contract G e x y` — `Graph α β` has no contraction operation, so it is
  defined from scratch via the vertex-merge map `y ↦ x` (keeping the vertex type `α`, so the
  whole flow API applies unchanged), with the flow correspondence driving the
  deletion–contraction recurrence (Lemma I.1.1).

* **Orientation reversal at one edge** and the **reverse-and-negate bijection** (Lemma B0):
  flipping one edge and negating its flow value is an involutive bijection on nowhere-zero
  flows, so flow existence and the flow count are orientation-independent.
-/

open Graph Workspace.Types.Orientation
open scoped Graph

namespace Workspace.PriorWorkProofs.Tutte

variable {α β : Type*} {G : Graph α β} {O : Orientation G}

/-! ## The flow count `n(G, Γ)` -/

/-- The set of **normalized** nowhere-zero `Γ`-flows of `G` w.r.t. `O`: flows that are
nowhere-zero on `E(G)` *and* vanish off `E(G)`. The off-edge normalization pins the
unobservable junk values of a total map `β → Γ`, making the count finite and giving one
canonical representative per observable flow. -/
def flowSet (G : Graph α β) (O : Orientation G) (Γ : Type*) [AddCommGroup Γ] : Set (β → Γ) :=
  {f | G.IsFlow O f ∧ G.IsNowhereZero f ∧ ∀ e ∉ E(G), f e = 0}

/-- The **flow count** `n(G, Γ)`: the number of nowhere-zero `Γ`-flows of `G` w.r.t. `O`
(counted as normalized flows). -/
noncomputable def flowCount (G : Graph α β) (O : Orientation G) (Γ : Type*) [AddCommGroup Γ] : ℕ :=
  Nat.card ↥(flowSet G O Γ)

/-- **Finiteness of the flow set** (foundational). If `G` has finitely many edges and `Γ`
is finite, the set of normalized nowhere-zero `Γ`-flows is finite. Proof: restriction to
`E(G)` injects `flowSet` into the finite type `↥E(G) → Γ`, because two normalized flows
that agree on `E(G)` agree everywhere (both vanish off `E(G)`). -/
theorem flowSet_finite {Γ : Type*} [AddCommGroup Γ] [Finite Γ] (hE : E(G).Finite) :
    (flowSet G O Γ).Finite := by
  haveI : Finite ↥E(G) := hE.to_subtype
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (fun F : ↥(flowSet G O Γ) => (fun e : ↥E(G) => (F : β → Γ) e.1)) ?_
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  apply Subtype.ext
  funext e
  by_cases he : e ∈ E(G)
  · exact congrFun h ⟨e, he⟩
  · exact (hf.2.2 e he).trans (hg.2.2 e he).symm

instance flowSet_finite_inst {Γ : Type*} [AddCommGroup Γ] [Finite Γ] [hE : Fact E(G).Finite] :
    Finite ↥(flowSet G O Γ) :=
  Set.finite_coe_iff.mpr (flowSet_finite hE.out)

/-- **Lemma I.2 (empty base case).** If `G` has no edges then the flow count is `1`: the
only normalized flow is the zero map (which is vacuously a nowhere-zero flow). -/
theorem flowCount_empty {Γ : Type*} [AddCommGroup Γ] (hE : E(G) = ∅) :
    flowCount G O Γ = 1 := by
  have hset : flowSet G O Γ = {(0 : β → Γ)} := by
    ext f
    simp only [flowSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, _, h3⟩
      funext e
      exact h3 e (by rw [hE]; exact Set.notMem_empty e)
    · rintro rfl
      refine ⟨G.isFlow_zero O, ?_, fun _ _ => rfl⟩
      intro e he
      rw [hE] at he
      exact absurd he (Set.notMem_empty e)
  unfold flowCount
  rw [hset]
  simp

/-! ## Edge deletion `G − e`

Mathlib provides `Graph.deleteEdges G F`. We specialize it to a single edge and record the
basic API used by the deletion–contraction recurrence. -/

/-- `deleteEdge G e = G − e`: delete the single edge `e` from `G`. -/
abbrev deleteEdge (G : Graph α β) (e : β) : Graph α β := G.deleteEdges {e}

@[simp] lemma deleteEdge_le (e : β) : deleteEdge G e ≤ G := Graph.deleteEdges_le

/-- The vertex set is unchanged by edge deletion. -/
@[simp] lemma vertexSet_deleteEdge (e : β) : V(deleteEdge G e) = V(G) := by
  simp [deleteEdge]

/-- The edge set of `G − e` is `E(G) \ {e}`. -/
@[simp] lemma edgeSet_deleteEdge (e : β) : E(deleteEdge G e) = E(G) \ {e} := by
  simp [deleteEdge]

/-- Incidence of an edge `e' ≠ e` is unchanged by deleting `e`. -/
lemma deleteEdge_isLink_of_ne {e e' : β} {x y : α} (hne : e' ≠ e) :
    (deleteEdge G e).IsLink e' x y ↔ G.IsLink e' x y := by
  simp [deleteEdge, hne]

/-- An orientation of `G` restricts to an orientation of `G − e`. -/
def deleteEdgeOrientation (O : Orientation G) (e : β) : Orientation (deleteEdge G e) :=
  O.restrict Graph.deleteEdges_le

/-! ## Edge contraction `G / e`

Mathlib's `Graph α β` has **no** edge-contraction operation. We define contraction of a
non-loop edge `e = xy` by *merging* `y` into `x` via the vertex map `m : α → α`,
`m z = if z = x' then y' else z`… concretely we merge `y` into `x` (map `y ↦ x`, identity
elsewhere) and drop the edge `e`. Keeping the vertex type `α` means every downstream notion
(orientations, flows, the flow count) applies to `contract G e x y` with no re-derivation. -/

section Contract
variable [DecidableEq α]

/-- The vertex-merge map underlying contraction: send `y` to `x`, fix everything else. -/
def mergeMap (x y : α) : α → α := fun z => if z = y then x else z

@[simp] lemma mergeMap_self (x y : α) : mergeMap x y y = x := by simp [mergeMap]

lemma mergeMap_of_ne (x : α) {y z : α} (h : z ≠ y) : mergeMap x y z = z := by
  simp [mergeMap, h]

/-- **Edge contraction** `G / e`, contracting the (non-loop) edge `e` with ends `x, y` by
identifying `y` with `x`. Every edge other than `e` is kept, with its ends pushed through the
merge map `mergeMap x y`; parallel copies of `e` become loops, as contraction requires. -/
@[simps isLink]
def contract (G : Graph α β) (e : β) (x y : α) : Graph α β where
  vertexSet := (mergeMap x y) '' V(G)
  IsLink e' a b :=
    e' ≠ e ∧ ∃ a' b', G.IsLink e' a' b' ∧ mergeMap x y a' = a ∧ mergeMap x y b' = b
  isLink_symm := by
    rintro e' _ a b ⟨hne, a', b', hL, ha, hb⟩
    exact ⟨hne, b', a', hL.symm, hb, ha⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e' a b v w ⟨_, a', b', hL, ha, hb⟩ ⟨_, v', w', hL', hv, hw⟩
    rcases hL.left_eq_or_eq hL' with h | h
    · left; rw [← ha, ← hv, h]
    · right; rw [← ha, ← hw, h]
  left_mem_of_isLink := by
    rintro e' a b ⟨_, a', b', hL, ha, _⟩
    exact ⟨a', hL.left_mem, ha⟩

@[simp] lemma vertexSet_contract (e : β) (x y : α) :
    V(contract G e x y) = (mergeMap x y) '' V(G) := rfl

/-- The edge set of `G / e` is `E(G) \ {e}`. -/
@[simp] lemma edgeSet_contract (e : β) (x y : α) :
    E(contract G e x y) = E(G) \ {e} := by
  ext e'
  rw [Graph.edgeSet_eq_setOf_exists_isLink]
  simp only [Set.mem_setOf_eq, contract_isLink, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, hne, a', b', hL, -, -⟩
    exact ⟨hL.edge_mem, hne⟩
  · rintro ⟨he'G, hne⟩
    obtain ⟨a', b', hL⟩ := G.exists_isLink_of_mem_edgeSet he'G
    exact ⟨_, _, hne, a', b', hL, rfl, rfl⟩

/-- The orientation `O` of `G` induces an orientation of `G / e` by pushing tails and heads
through the merge map. -/
def contractOrientation (O : Orientation G) (e : β) (x y : α) :
    Orientation (contract G e x y) where
  tail e' := mergeMap x y (O.tail e')
  head e' := mergeMap x y (O.head e')
  isLink_tail_head e' he' := by
    rw [edgeSet_contract] at he'
    obtain ⟨he'G, hne⟩ := he'
    exact ⟨by simpa using hne, O.tail e', O.head e', O.isLink_tail_head he'G, rfl, rfl⟩

/-! ### Deletion–contraction: supporting development

The lemmas below build the deletion–contraction recurrence `contract_flow_correspondence`.
They require decidable equality on the edge type `β` (for `Function.update` and `Finset`
operations); the final theorem does not, obtaining an instance via `Classical`. -/

section ContractFlowAux
variable [DecidableEq β]

/-- The intermediate set `S`: maps satisfying Kirchhoff everywhere, nowhere-zero on `E(G) \ {e}`,
value at `e` free, normalized to vanish off `E(G)`. -/
def SSet (G : Graph α β) (O : Orientation G) (e : β) (Γ : Type*) [AddCommGroup Γ] :
    Set (β → Γ) :=
  {f | G.IsFlow O f ∧ (∀ e' ∈ E(G), e' ≠ e → f e' ≠ 0) ∧ (∀ e' ∉ E(G), f e' = 0)}

/-- `S` is finite: restriction to `E(G)` injects it into the finite type `↥E(G) → Γ`. -/
theorem SSet_finite {Γ : Type*} [AddCommGroup Γ] [Finite Γ] (hE : E(G).Finite) (e : β) :
    (SSet G O e Γ).Finite := by
  haveI : Finite ↥E(G) := hE.to_subtype
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective
    (fun F : ↥(SSet G O e Γ) => (fun ee : ↥E(G) => (F : β → Γ) ee.1)) ?_
  rintro ⟨f, hf⟩ ⟨g, hg⟩ h
  apply Subtype.ext
  funext ee
  by_cases he : ee ∈ E(G)
  · exact congrFun h ⟨ee, he⟩
  · exact (hf.2.2 ee he).trans (hg.2.2 ee he).symm

/-- **P2.** The elements of `S` with `f e ≠ 0` are exactly the nowhere-zero flows of `G`. -/
theorem SSet_ne_eq_flowSet {Γ : Type*} [AddCommGroup Γ] (e : β) (heG : e ∈ E(G)) :
    {f ∈ SSet G O e Γ | f e ≠ 0} = flowSet G O Γ := by
  ext f
  simp only [SSet, flowSet, Set.mem_setOf_eq, Set.mem_sep_iff]
  constructor
  · rintro ⟨⟨hflow, hnz, hoff⟩, hfe⟩
    refine ⟨hflow, ?_, hoff⟩
    intro e' he'
    by_cases h : e' = e
    · rw [h]; exact hfe
    · exact hnz e' he' h
  · rintro ⟨hflow, hnz, hoff⟩
    exact ⟨⟨hflow, fun e' he' _ => hnz e' he', hoff⟩, hnz e heG⟩

lemma deleteEdgeOrientation_tail (e : β) : (deleteEdgeOrientation O e).tail = O.tail := rfl
lemma deleteEdgeOrientation_head (e : β) : (deleteEdgeOrientation O e).head = O.head := rfl

/-- If `f` vanishes at `e`, being a flow on `G` is the same as being a flow on `G - e`. -/
theorem isFlow_deleteEdge_of_zero {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β)
    {f : β → Γ} (hfe : f e = 0) :
    G.IsFlow O f ↔ (deleteEdge G e).IsFlow (deleteEdgeOrientation O e) f := by
  have hE' : E(deleteEdge G e).Finite := by rw [edgeSet_deleteEdge]; exact hE.diff
  have hsub : hE'.toFinset ⊆ hE.toFinset := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha ⊢
    rw [edgeSet_deleteEdge] at ha
    exact ha.1
  have key : ∀ (t : β → α) (v : α),
      (∑ a ∈ hE'.toFinset with t a = v, f a) = ∑ a ∈ hE.toFinset with t a = v, f a := by
    intro t v
    apply Finset.sum_subset (Finset.filter_subset_filter _ hsub)
    intro a ha hna
    simp only [Finset.mem_filter] at ha
    have hnotmem : a ∉ hE'.toFinset := fun hmem => hna (Finset.mem_filter.mpr ⟨hmem, ha.2⟩)
    rw [Set.Finite.mem_toFinset, edgeSet_deleteEdge] at hnotmem
    rw [Set.Finite.mem_toFinset] at ha
    have hae : a = e := by
      by_contra hne
      exact hnotmem ⟨ha.1, by simp [hne]⟩
    rw [hae]; exact hfe
  rw [Graph.isFlow_iff_finset_sum hE, Graph.isFlow_iff_finset_sum hE',
    deleteEdgeOrientation_tail, deleteEdgeOrientation_head, vertexSet_deleteEdge]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [key O.tail v, key O.head v]

/-- **P3.** The elements of `S` with `f e = 0` are exactly the nowhere-zero flows of `G - e`. -/
theorem SSet_eq_eq_flowSet_deleteEdge {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β) :
    {f ∈ SSet G O e Γ | f e = 0}
      = flowSet (deleteEdge G e) (deleteEdgeOrientation O e) Γ := by
  ext f
  simp only [SSet, flowSet, Graph.IsNowhereZero, Set.mem_setOf_eq, Set.mem_sep_iff,
    edgeSet_deleteEdge, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hflow, hnz, hoff⟩, hfe⟩
    refine ⟨(isFlow_deleteEdge_of_zero hE e hfe).mp hflow, ?_, ?_⟩
    · intro e' he'
      exact hnz e' he'.1 he'.2
    · intro e' he'
      by_cases hmem : e' ∈ E(G)
      · have : e' = e := by tauto
        rw [this]; exact hfe
      · exact hoff e' hmem
  · rintro ⟨hflow, hnz, hoff⟩
    have hfe : f e = 0 := hoff e (by simp)
    refine ⟨⟨(isFlow_deleteEdge_of_zero hE e hfe).mpr hflow, ?_, ?_⟩, hfe⟩
    · intro e' he'G he'ne
      exact hnz e' ⟨he'G, he'ne⟩
    · intro e' he'
      exact hoff e' (by tauto)

/-- **P4.** Partition of the finite set `S` by the predicate `f e = 0`. -/
theorem SSet_card_split {Γ : Type*} [AddCommGroup Γ] [Finite Γ] (hE : E(G).Finite) (e : β) :
    Nat.card ↥(SSet G O e Γ)
      = Nat.card ↥{f ∈ SSet G O e Γ | f e ≠ 0} + Nat.card ↥{f ∈ SSet G O e Γ | f e = 0} := by
  have hfin := SSet_finite (O := O) hE e (Γ := Γ)
  have hunion : SSet G O e Γ
      = {f ∈ SSet G O e Γ | f e ≠ 0} ∪ {f ∈ SSet G O e Γ | f e = 0} := by
    ext f; simp only [Set.mem_union, Set.mem_sep_iff]; tauto
  have hdisj : Disjoint {f ∈ SSet G O e Γ | f e ≠ 0} {f ∈ SSet G O e Γ | f e = 0} := by
    rw [Set.disjoint_left]; rintro f ⟨_, h1⟩ ⟨_, h2⟩; exact h1 h2
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  conv_lhs => rw [hunion]
  rw [Set.ncard_union_eq hdisj (hfin.subset (Set.sep_subset _ _))
    (hfin.subset (Set.sep_subset _ _))]

/-- Fact (i): the vertex set of `G / e` is `V(G) \ {y}`. -/
lemma vertexSet_contract_eq {x y : α} (hxV : x ∈ V(G)) (hne : x ≠ y) (e : β) :
    V(contract G e x y) = V(G) \ {y} := by
  rw [vertexSet_contract]
  ext w
  simp only [Set.mem_image, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    by_cases h : v = y
    · subst h; rw [mergeMap_self]; exact ⟨hxV, hne⟩
    · rw [mergeMap_of_ne _ h]; exact ⟨hv, h⟩
  · rintro ⟨hw, hwy⟩
    exact ⟨w, hw, mergeMap_of_ne _ hwy⟩

/-- The `toFinset` of `E(G) \ {e}` is the erasure of `e` from `hE.toFinset`. -/
lemma toFinset_diff_singleton (e : β) (hE : E(G).Finite) (hE'' : (E(G) \ {e}).Finite) :
    hE''.toFinset = hE.toFinset.erase e := by
  ext a
  simp only [Set.Finite.mem_toFinset, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_erase]
  tauto

/-- Filtered sums of a map vanishing at `e` are unchanged by erasing `e` from the index set. -/
lemma sum_filter_erase_of_zero {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β)
    {h : β → Γ} (he0 : h e = 0) (p : β → Prop) [DecidablePred p] :
    (∑ a ∈ hE.toFinset.erase e with p a, h a) = ∑ a ∈ hE.toFinset with p a, h a := by
  apply Finset.sum_subset (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
  intro a ha hna
  simp only [Finset.mem_filter, Finset.mem_erase] at ha hna
  have : a = e := by tauto
  rw [this]; exact he0

/-- `mergeMap x y u = x` iff `u ∈ {x, y}`. -/
lemma mergeMap_eq_left_iff {x y u : α} (hne : x ≠ y) :
    mergeMap x y u = x ↔ u = x ∨ u = y := by
  unfold mergeMap; split_ifs with h
  · subst h; simp
  · simp [h]

/-- For `w ∉ {x, y}`, `mergeMap x y u = w` iff `u = w`. -/
lemma mergeMap_eq_of_ne {x y w u : α} (hwx : w ≠ x) (hwy : w ≠ y) :
    mergeMap x y u = w ↔ u = w := by
  unfold mergeMap; split_ifs with h
  · subst h
    constructor
    · intro h2; exact (hwx h2.symm).elim
    · intro h2; exact (hwy h2.symm).elim
  · exact Iff.rfl

/-- The reconstruction value `r` forcing Kirchhoff at `x` for the extended map. -/
noncomputable def rval {Γ : Type*} [AddCommGroup Γ] (O : Orientation G) (hE : E(G).Finite)
    (e : β) (x : α) (g : β → Γ) : Γ :=
  if O.tail e = x
  then (∑ e' ∈ hE.toFinset with O.head e' = x, g e') - (∑ e' ∈ hE.toFinset with O.tail e' = x, g e')
  else (∑ e' ∈ hE.toFinset with O.tail e' = x, g e') - (∑ e' ∈ hE.toFinset with O.head e' = x, g e')

lemma contractOrientation_tail (e : β) (x y : α) (e' : β) :
    (contractOrientation O e x y).tail e' = mergeMap x y (O.tail e') := rfl

lemma contractOrientation_head (e : β) (x y : α) (e' : β) :
    (contractOrientation O e x y).head e' = mergeMap x y (O.head e') := rfl

/-- Bridge: a filtered sum of `Function.update g e r` equals the `g`-sum plus `r` at `e`. -/
lemma sum_filter_update_eq {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β)
    (heG : e ∈ E(G)) {g : β → Γ} (hge : g e = 0) (r : Γ) (q : β → Prop) [DecidablePred q] :
    (∑ e' ∈ hE.toFinset with q e', (Function.update g e r) e')
      = (∑ e' ∈ hE.toFinset with q e', g e') + (if q e then r else 0) := by
  have step : ∀ e' ∈ hE.toFinset.filter q,
      Function.update g e r e' = g e' + (if e' = e then r else 0) := by
    intro e' _
    by_cases h : e' = e
    · subst h; rw [Function.update_self, hge]; simp
    · rw [Function.update_of_ne h]; simp [h]
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq' (hE.toFinset.filter q) e (fun _ => r)]
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, heG, true_and]

/-- Bridge: a filtered sum of `Function.update f e 0` equals the `f`-sum minus `f e` at `e`. -/
lemma sum_filter_update_zero_eq {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β)
    (heG : e ∈ E(G)) (f : β → Γ) (q : β → Prop) [DecidablePred q] :
    (∑ e' ∈ hE.toFinset with q e', (Function.update f e 0) e')
      = (∑ e' ∈ hE.toFinset with q e', f e') - (if q e then f e else 0) := by
  have step : ∀ e' ∈ hE.toFinset.filter q,
      Function.update f e 0 e' = f e' + (if e' = e then - f e else 0) := by
    intro e' _
    by_cases h : e' = e
    · subst h; rw [Function.update_self]; simp
    · rw [Function.update_of_ne h]; simp [h]
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib,
    Finset.sum_ite_eq' (hE.toFinset.filter q) e (fun _ => - f e)]
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, heG, true_and]
  by_cases hq : q e <;> simp [hq, sub_eq_add_neg]

/-- Split a `mergeMap`-filtered sum at the merge target `x` into the `x`- and `y`-parts. -/
lemma sum_filter_mergeMap_left {Γ : Type*} [AddCommGroup Γ] (s : Finset β) (t : β → α)
    {x y : α} (hne : x ≠ y) (g : β → Γ) :
    (∑ e' ∈ s with mergeMap x y (t e') = x, g e')
      = (∑ e' ∈ s with t e' = x, g e') + (∑ e' ∈ s with t e' = y, g e') := by
  have hdisj : Disjoint (s.filter (fun e' => t e' = x)) (s.filter (fun e' => t e' = y)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter] at ha hb
    exact hne (ha.2.symm.trans hb.2)
  have hfilter : s.filter (fun e' => mergeMap x y (t e') = x)
      = s.filter (fun e' => t e' = x) ∪ s.filter (fun e' => t e' = y) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro e' _
    exact mergeMap_eq_left_iff hne
  rw [hfilter, Finset.sum_union hdisj]

/-- For `w ∉ {x, y}`, the `mergeMap`-filtered sum is the plain filtered sum. -/
lemma sum_filter_mergeMap_other {Γ : Type*} [AddCommGroup Γ] (s : Finset β) (t : β → α)
    {x y w : α} (hwx : w ≠ x) (hwy : w ≠ y) (g : β → Γ) :
    (∑ e' ∈ s with mergeMap x y (t e') = w, g e') = ∑ e' ∈ s with t e' = w, g e' := by
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro e' _
  exact mergeMap_eq_of_ne hwx hwy

/-- The contract edge finset is the erasure of `e`. -/
lemma toFinset_edgeSet_contract (e : β) (x y : α) (hE : E(G).Finite)
    (hE'' : E(contract G e x y).Finite) : hE''.toFinset = hE.toFinset.erase e := by
  ext a
  simp only [Set.Finite.mem_toFinset, edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff,
    Finset.mem_erase]
  tauto

/-- Reduction of the contraction flow condition to `mergeMap`-filtered sums over `hE.toFinset`. -/
lemma contract_flow_iff_sums {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β) (x y : α)
    {g : β → Γ} (hge : g e = 0) :
    (contract G e x y).IsFlow (contractOrientation O e x y) g
      ↔ ∀ w ∈ V(contract G e x y),
          (∑ e' ∈ hE.toFinset with mergeMap x y (O.tail e') = w, g e')
            = ∑ e' ∈ hE.toFinset with mergeMap x y (O.head e') = w, g e' := by
  have hE'' : E(contract G e x y).Finite := by rw [edgeSet_contract]; exact hE.diff
  rw [Graph.isFlow_iff_finset_sum hE'']
  simp only [contractOrientation_tail, contractOrientation_head]
  rw [toFinset_edgeSet_contract e x y hE hE'']
  apply forall_congr'; intro w
  simp only [sum_filter_erase_of_zero hE e hge]
  exact Iff.rfl

/-- **Core flow equivalence.** For `g` vanishing at `e`, `g` is a flow of `G / e` iff the
extension `update g e r` (with `r = rval`) is a flow of `G`. -/
lemma flow_update_iff {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β) (x y : α)
    (hxy : G.IsLink e x y) (hne : x ≠ y) {g : β → Γ} (hge : g e = 0) :
    (contract G e x y).IsFlow (contractOrientation O e x y) g
      ↔ G.IsFlow O (Function.update g e (rval O hE e x g)) := by
  classical
  have heG : e ∈ E(G) := hxy.edge_mem
  have hxV : x ∈ V(G) := hxy.left_mem
  rw [contract_flow_iff_sums hE e x y hge, Graph.isFlow_iff_finset_sum hE,
      vertexSet_contract_eq hxV hne]
  set R := rval O hE e x g with hR
  have hxy' := O.eq_and_eq_or_eq_and_eq hxy
  have htail_mem : O.tail e = x ∨ O.tail e = y := by
    rcases hxy' with ⟨a, _⟩ | ⟨a, _⟩
    · exact Or.inl a
    · exact Or.inr a
  have hhead_mem : O.head e = x ∨ O.head e = y := by
    rcases hxy' with ⟨_, b⟩ | ⟨_, b⟩
    · exact Or.inr b
    · exact Or.inl b
  have hIT : (if O.tail e = x then R else 0) + (if O.tail e = y then R else 0) = R := by
    rcases htail_mem with h | h <;> rw [h] <;> simp [hne, Ne.symm hne]
  have hIH : (if O.head e = x then R else 0) + (if O.head e = y then R else 0) = R := by
    rcases hhead_mem with h | h <;> rw [h] <;> simp [hne, Ne.symm hne]
  have hTvanish : ∀ v, v ≠ x → v ≠ y → (if O.tail e = v then R else 0) = 0 := by
    intro v hvx hvy
    rcases htail_mem with h | h <;> rw [h] <;> [exact if_neg (fun hc => hvx hc.symm);
      exact if_neg (fun hc => hvy hc.symm)]
  have hHvanish : ∀ v, v ≠ x → v ≠ y → (if O.head e = v then R else 0) = 0 := by
    intro v hvx hvy
    rcases hhead_mem with h | h <;> rw [h] <;> [exact if_neg (fun hc => hvx hc.symm);
      exact if_neg (fun hc => hvy hc.symm)]
  have kx : (∑ e' ∈ hE.toFinset with O.tail e' = x, g e')
              + (if O.tail e = x then R else 0)
            = (∑ e' ∈ hE.toFinset with O.head e' = x, g e')
              + (if O.head e = x then R else 0) := by
    rcases hxy' with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · rw [ht, hh, if_pos rfl, if_neg (Ne.symm hne), hR]
      simp only [rval]
      rw [if_pos ht]; abel
    · rw [ht, hh, if_neg (Ne.symm hne), if_pos rfl, hR]
      simp only [rval]
      rw [if_neg (by rw [ht]; exact Ne.symm hne)]; abel
  constructor
  · intro hL v hv
    rw [sum_filter_update_eq hE e heG hge R (fun e' => O.tail e' = v),
        sum_filter_update_eq hE e heG hge R (fun e' => O.head e' = v)]
    by_cases hvx : v = x
    · rw [hvx]; exact kx
    by_cases hvy : v = y
    · rw [hvy]
      have hmx := hL x (Set.mem_diff_singleton.mpr ⟨hxV, hne⟩)
      rw [sum_filter_mergeMap_left _ _ hne, sum_filter_mergeMap_left _ _ hne] at hmx
      have goalsub :
          ((∑ e' ∈ hE.toFinset with O.tail e' = y, g e') + (if O.tail e = y then R else 0))
            - ((∑ e' ∈ hE.toFinset with O.head e' = y, g e') + (if O.head e = y then R else 0))
          = (((∑ e' ∈ hE.toFinset with O.tail e' = x, g e')
                + (∑ e' ∈ hE.toFinset with O.tail e' = y, g e'))
              - ((∑ e' ∈ hE.toFinset with O.head e' = x, g e')
                + (∑ e' ∈ hE.toFinset with O.head e' = y, g e')))
            - (((∑ e' ∈ hE.toFinset with O.tail e' = x, g e') + (if O.tail e = x then R else 0))
                - ((∑ e' ∈ hE.toFinset with O.head e' = x, g e')
                  + (if O.head e = x then R else 0)))
            + ((if O.tail e = x then R else 0) + (if O.tail e = y then R else 0) - R)
            - ((if O.head e = x then R else 0) + (if O.head e = y then R else 0) - R) := by
        abel
      rw [← sub_eq_zero, goalsub, sub_eq_zero.mpr hmx, sub_eq_zero.mpr kx,
        sub_eq_zero.mpr hIT, sub_eq_zero.mpr hIH]
      abel
    · have hmv := hL v (Set.mem_diff_singleton.mpr ⟨hv, hvy⟩)
      rw [sum_filter_mergeMap_other _ _ hvx hvy, sum_filter_mergeMap_other _ _ hvx hvy] at hmv
      rw [hTvanish v hvx hvy, hHvanish v hvx hvy, add_zero, add_zero]
      exact hmv
  · intro hR2 w hw
    rw [Set.mem_diff_singleton] at hw
    obtain ⟨hwG, hwy⟩ := hw
    by_cases hwx : w = x
    · rw [hwx]
      rw [sum_filter_mergeMap_left _ _ hne, sum_filter_mergeMap_left _ _ hne]
      have hx := hR2 x hxV
      rw [sum_filter_update_eq hE e heG hge R (fun e' => O.tail e' = x),
          sum_filter_update_eq hE e heG hge R (fun e' => O.head e' = x)] at hx
      have hy := hR2 y (by
        rcases hxy' with ⟨_, hh⟩ | ⟨ht, _⟩
        · exact hh ▸ O.head_mem heG
        · exact ht ▸ O.tail_mem heG)
      rw [sum_filter_update_eq hE e heG hge R (fun e' => O.tail e' = y),
          sum_filter_update_eq hE e heG hge R (fun e' => O.head e' = y)] at hy
      have goalsub :
          ((∑ e' ∈ hE.toFinset with O.tail e' = x, g e')
              + (∑ e' ∈ hE.toFinset with O.tail e' = y, g e'))
            - ((∑ e' ∈ hE.toFinset with O.head e' = x, g e')
              + (∑ e' ∈ hE.toFinset with O.head e' = y, g e'))
          = (((∑ e' ∈ hE.toFinset with O.tail e' = x, g e') + (if O.tail e = x then R else 0))
                - ((∑ e' ∈ hE.toFinset with O.head e' = x, g e')
                  + (if O.head e = x then R else 0)))
            + (((∑ e' ∈ hE.toFinset with O.tail e' = y, g e') + (if O.tail e = y then R else 0))
                - ((∑ e' ∈ hE.toFinset with O.head e' = y, g e')
                  + (if O.head e = y then R else 0)))
            - ((if O.tail e = x then R else 0) + (if O.tail e = y then R else 0) - R)
            + ((if O.head e = x then R else 0) + (if O.head e = y then R else 0) - R) := by
        abel
      rw [← sub_eq_zero, goalsub, sub_eq_zero.mpr hx, sub_eq_zero.mpr hy,
        sub_eq_zero.mpr hIT, sub_eq_zero.mpr hIH]
      abel
    · rw [sum_filter_mergeMap_other _ _ hwx hwy, sum_filter_mergeMap_other _ _ hwx hwy]
      have hw2 := hR2 w hwG
      rw [sum_filter_update_eq hE e heG hge R (fun e' => O.tail e' = w),
          sum_filter_update_eq hE e heG hge R (fun e' => O.head e' = w),
          hTvanish w hwx hwy, hHvanish w hwx hwy, add_zero, add_zero] at hw2
      exact hw2

/-- For a flow `f`, the reconstruction value of `update f e 0` recovers `f e`. -/
lemma rval_update_zero_eq {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β) (x y : α)
    (hxy : G.IsLink e x y) (hne : x ≠ y) {f : β → Γ} (hf : G.IsFlow O f) :
    rval O hE e x (Function.update f e 0) = f e := by
  classical
  have heG : e ∈ E(G) := hxy.edge_mem
  have hxV : x ∈ V(G) := hxy.left_mem
  have hflowx := (Graph.isFlow_iff_finset_sum hE).mp hf x hxV
  unfold rval
  rw [sum_filter_update_zero_eq hE e heG f (fun e' => O.head e' = x),
      sum_filter_update_zero_eq hE e heG f (fun e' => O.tail e' = x)]
  rcases O.eq_and_eq_or_eq_and_eq hxy with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · rw [if_pos ht, ht, hh, if_pos rfl, if_neg (Ne.symm hne), ← hflowx]; abel
  · rw [if_neg (by rw [ht]; exact Ne.symm hne), ht, hh, if_neg (Ne.symm hne), if_pos rfl,
      ← hflowx]; abel

/-- If `g` vanishes at `e`, updating it to `0` at `e` is the identity. -/
lemma update_zero_eq_self {Γ : Type*} [Zero Γ] {g : β → Γ} {e : β} (h : g e = 0) :
    Function.update g e 0 = g := by
  funext a; by_cases ha : a = e
  · subst ha; rw [Function.update_self]; exact h.symm
  · rw [Function.update_of_ne ha]

/-- The forward map lands in `S`. -/
lemma toS_mem {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β) (x y : α)
    (hxy : G.IsLink e x y) (hne : x ≠ y)
    {g : β → Γ} (hg : g ∈ flowSet (contract G e x y) (contractOrientation O e x y) Γ) :
    Function.update g e (rval O hE e x g) ∈ SSet G O e Γ := by
  obtain ⟨hflow, hnz, hoff⟩ := hg
  have heG : e ∈ E(G) := hxy.edge_mem
  have hge : g e = 0 := hoff e (by rw [edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff]; simp)
  refine ⟨(flow_update_iff hE e x y hxy hne hge).mp hflow, ?_, ?_⟩
  · intro e' he'G he'ne
    rw [Function.update_of_ne he'ne]
    exact hnz e' (by rw [edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff]; exact ⟨he'G, he'ne⟩)
  · intro e' he'
    have hne' : e' ≠ e := fun h => he' (h ▸ heG)
    rw [Function.update_of_ne hne']
    exact hoff e' (by rw [edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff]; tauto)

/-- The inverse map lands in the flows of `G / e`. -/
lemma fromS_mem {Γ : Type*} [AddCommGroup Γ] (hE : E(G).Finite) (e : β) (x y : α)
    (hxy : G.IsLink e x y) (hne : x ≠ y) {f : β → Γ} (hf : f ∈ SSet G O e Γ) :
    Function.update f e 0 ∈ flowSet (contract G e x y) (contractOrientation O e x y) Γ := by
  obtain ⟨hflow, hnz, hoff⟩ := hf
  have heG : e ∈ E(G) := hxy.edge_mem
  have hge : (Function.update f e 0) e = 0 := by rw [Function.update_self]
  refine ⟨?_, ?_, ?_⟩
  · rw [flow_update_iff hE e x y hxy hne hge, rval_update_zero_eq hE e x y hxy hne hflow,
      Function.update_idem, Function.update_eq_self]
    exact hflow
  · intro e' he'
    rw [edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff] at he'
    rw [Function.update_of_ne he'.2]
    exact hnz e' he'.1 he'.2
  · intro e' he'
    rw [edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff] at he'
    by_cases h : e' = e
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]
      exact hoff e' (fun hc => he' ⟨hc, h⟩)

/-- **P1 (the hard bijection).** The flow count of `G / e` equals `Nat.card S`. -/
theorem flowCount_contract_eq_card_SSet {Γ : Type*} [AddCommGroup Γ] [Finite Γ]
    (hE : E(G).Finite) (e : β) (x y : α) (hxy : G.IsLink e x y) (hne : x ≠ y) :
    flowCount (contract G e x y) (contractOrientation O e x y) Γ = Nat.card ↥(SSet G O e Γ) := by
  unfold flowCount
  apply Nat.card_congr
  refine {
    toFun := fun F => ⟨Function.update (F : β → Γ) e (rval O hE e x (F : β → Γ)),
      toS_mem hE e x y hxy hne F.2⟩
    invFun := fun F => ⟨Function.update (F : β → Γ) e 0, fromS_mem hE e x y hxy hne F.2⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨g, hg⟩
    apply Subtype.ext
    have hge : g e = 0 :=
      hg.2.2 e (by rw [edgeSet_contract, Set.mem_diff, Set.mem_singleton_iff]; simp)
    simp only [Function.update_idem]
    exact update_zero_eq_self hge
  · rintro ⟨f, hf⟩
    apply Subtype.ext
    simp only
    rw [rval_update_zero_eq hE e x y hxy hne hf.1, Function.update_idem, Function.update_eq_self]

end ContractFlowAux

/-- **Lemma I.1.1 (deletion–contraction).** For a non-loop edge `e = xy`, the nowhere-zero
`Γ`-flows of `G / e` are in bijection with the maps on `G` that satisfy Kirchhoff everywhere and
are nowhere-zero off `e` (the set `S = SSet` of the paper). Splitting `S` by whether `f e = 0`
yields the deletion–contraction recurrence
`flowCount (G/e) = flowCount G + flowCount (G − e)`. -/
theorem contract_flow_correspondence {Γ : Type*} [AddCommGroup Γ] [Finite Γ]
    (hE : E(G).Finite) (e : β) (x y : α) (hxy : G.IsLink e x y) (hne : x ≠ y) :
    flowCount (contract G e x y) (contractOrientation O e x y) Γ
      = flowCount G O Γ + flowCount (deleteEdge G e) (deleteEdgeOrientation O e) Γ := by
  classical
  have heG : e ∈ E(G) := hxy.edge_mem
  rw [flowCount_contract_eq_card_SSet hE e x y hxy hne, SSet_card_split hE e]
  unfold flowCount
  rw [← SSet_ne_eq_flowSet e heG, ← SSet_eq_eq_flowSet_deleteEdge hE e]

end Contract

/-! ## Orientation reversal at one edge (Lemma B0)

Reversing a single edge `e₀` and negating the flow value there is an involutive bijection
between nowhere-zero `Γ`-flows for the two orientations. Hence flow existence and the flow
count are orientation-independent. -/

section Reversal
variable [DecidableEq β]

/-- Reverse the orientation of the single edge `e₀`, leaving every other edge alone. -/
def reverseEdge (O : Orientation G) (e₀ : β) : Orientation G where
  tail e := if e = e₀ then O.head e₀ else O.tail e
  head e := if e = e₀ then O.tail e₀ else O.head e
  isLink_tail_head e he := by
    by_cases h : e = e₀
    · subst h; simpa using (O.isLink_tail_head he).symm
    · simpa [h] using O.isLink_tail_head he

@[simp] lemma reverseEdge_tail (e₀ e : β) :
    (reverseEdge O e₀).tail e = if e = e₀ then O.head e₀ else O.tail e := rfl

@[simp] lemma reverseEdge_head (e₀ e : β) :
    (reverseEdge O e₀).head e = if e = e₀ then O.tail e₀ else O.head e := rfl

@[simp] lemma reverseEdge_tail_self (e₀ : β) : (reverseEdge O e₀).tail e₀ = O.head e₀ := by
  simp [reverseEdge_tail]

@[simp] lemma reverseEdge_head_self (e₀ : β) : (reverseEdge O e₀).head e₀ = O.tail e₀ := by
  simp [reverseEdge_head]

/-- Reversing the same edge twice returns the original orientation. -/
@[simp] lemma reverseEdge_reverseEdge (O : Orientation G) (e₀ : β) :
    reverseEdge (reverseEdge O e₀) e₀ = O := by
  apply Orientation.ext <;> funext e <;> by_cases h : e = e₀ <;> simp [reverseEdge, h]

variable {Γ : Type*} [AddCommGroup Γ]

/-- **Reverse-and-negate** on flow values: negate the value at `e₀`, keep all others. -/
def twist (e₀ : β) (f : β → Γ) : β → Γ := fun e => if e = e₀ then -f e else f e

@[simp] lemma twist_self (e₀ : β) (f : β → Γ) : twist e₀ f e₀ = -f e₀ := by simp [twist]

lemma twist_of_ne {e₀ e : β} (f : β → Γ) (h : e ≠ e₀) : twist e₀ f e = f e := by
  simp [twist, h]

/-- `twist` is an involution. -/
@[simp] lemma twist_twist (e₀ : β) (f : β → Γ) : twist e₀ (twist e₀ f) = f := by
  funext e
  by_cases h : e = e₀ <;> simp [twist, h]

lemma twist_eq_zero_iff {e₀ e : β} (f : β → Γ) : twist e₀ f e = 0 ↔ f e = 0 := by
  by_cases h : e = e₀ <;> simp [twist, h]

/-- Reversing edge `e₀` and negating its value preserves the flow (conservation) property:
the loss of `f e₀` from one side of Kirchhoff's law at an endpoint of `e₀` is exactly matched
by the gain of `-f e₀` on the other side. This is the core of Lemma B0. -/
theorem isFlow_reverseEdge_twist_iff (hE : E(G).Finite) (e₀ : β) (f : β → Γ) :
    G.IsFlow (reverseEdge O e₀) (twist e₀ f) ↔ G.IsFlow O f := by
  classical
  rw [Graph.isFlow_iff_finset_sum hE, Graph.isFlow_iff_finset_sum hE]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  have hnet :
      (∑ e ∈ hE.toFinset with (reverseEdge O e₀).tail e = v, twist e₀ f e)
        - (∑ e ∈ hE.toFinset with (reverseEdge O e₀).head e = v, twist e₀ f e)
      = (∑ e ∈ hE.toFinset with O.tail e = v, f e)
        - (∑ e ∈ hE.toFinset with O.head e = v, f e) := by
    simp only [Finset.sum_filter]
    rw [← sub_eq_zero]
    simp only [← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro e _
    by_cases h : e = e₀
    · subst h
      simp only [reverseEdge_tail_self, reverseEdge_head_self, twist_self]
      split_ifs <;> abel
    · simp only [reverseEdge_tail, reverseEdge_head, if_neg h, twist_of_ne f h]
      abel
  rw [← sub_eq_zero, hnet, sub_eq_zero]

/-- The `twist` of a normalized flow for `O` is a normalized flow for `reverseEdge O e₀`. -/
theorem twist_mem_flowSet (hE : E(G).Finite) (e₀ : β) {f : β → Γ}
    (hf : f ∈ flowSet G O Γ) : twist e₀ f ∈ flowSet G (reverseEdge O e₀) Γ := by
  obtain ⟨hflow, hnz, hoff⟩ := hf
  refine ⟨(isFlow_reverseEdge_twist_iff hE e₀ f).mpr hflow, ?_, ?_⟩
  · intro e he
    rw [Ne, twist_eq_zero_iff]
    exact hnz e he
  · intro e he
    rw [twist_eq_zero_iff]
    exact hoff e he

/-- **Lemma B0, count form.** The flow count is unchanged by reversing a single edge. -/
theorem flowCount_reverseEdge [Finite Γ] (hE : E(G).Finite) (e₀ : β) :
    flowCount G (reverseEdge O e₀) Γ = flowCount G O Γ := by
  apply Nat.card_congr
  exact
  { toFun := fun F => ⟨twist e₀ (F : β → Γ), by
      have := twist_mem_flowSet hE e₀ (O := reverseEdge O e₀) F.2
      rwa [reverseEdge_reverseEdge] at this⟩
    invFun := fun F => ⟨twist e₀ (F : β → Γ), twist_mem_flowSet hE e₀ F.2⟩
    left_inv := fun F => by apply Subtype.ext; simp
    right_inv := fun F => by apply Subtype.ext; simp }
