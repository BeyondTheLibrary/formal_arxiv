import Mathlib
import Workspace.Types.Orientation

/-!
# Flows on an oriented multigraph

Fix an orientation `O : Orientation G` of a multigraph `G : Graph α β`. If `A` is an abelian
group, an **`A`-flow** is a map `f : E(G) → A` such that at every vertex the sum of `f` over the
edges directed *out* of that vertex equals the sum over the edges directed *in*. It is
**nowhere-zero** if `f e ≠ 0` for every edge `e`. For an integer `k ≥ 2`, an **integer
`k`-flow** is an integer-valued flow `φ` with `0 < |φ e| < k` on every edge.

The conservation sums are `finsum`s over `E(G)`; on a finite edge set (the paper's setting,
supplied downstream via `E(G).Finite`) they agree with ordinary finite sums, see
`Graph.isFlow_iff_finset_sum`. A loop at `v` lies in both the out- and in-edge sets, so it
contributes to both sides.
-/

open Workspace.Types.Orientation
open scoped Graph

namespace Graph

variable {α β : Type*} {A : Type*} [AddCommGroup A] {G : Graph α β} {O : Orientation G}
  {f g : β → A} {v : α} {e : β} {φ : β → ℤ} {k : ℤ}

/-! ### Out- and in-edges at a vertex -/

/-- The edges of `G` directed **out of** `v` by `O`, i.e. the edges whose tail is `v`.
A loop at `v` belongs to this set. -/
def outEdgeSet (G : Graph α β) (O : Orientation G) (v : α) : Set β :=
  {e ∈ E(G) | O.tail e = v}

/-- The edges of `G` directed **in to** `v` by `O`, i.e. the edges whose head is `v`.
A loop at `v` belongs to this set. -/
def inEdgeSet (G : Graph α β) (O : Orientation G) (v : α) : Set β :=
  {e ∈ E(G) | O.head e = v}

@[simp]
lemma mem_outEdgeSet : e ∈ G.outEdgeSet O v ↔ e ∈ E(G) ∧ O.tail e = v := Iff.rfl

@[simp]
lemma mem_inEdgeSet : e ∈ G.inEdgeSet O v ↔ e ∈ E(G) ∧ O.head e = v := Iff.rfl

lemma outEdgeSet_subset_edgeSet : G.outEdgeSet O v ⊆ E(G) := fun _ he ↦ he.1

lemma inEdgeSet_subset_edgeSet : G.inEdgeSet O v ⊆ E(G) := fun _ he ↦ he.1

/-- Reversing the orientation swaps out-edges and in-edges. -/
@[simp]
lemma outEdgeSet_reverse : G.outEdgeSet O.reverse v = G.inEdgeSet O v := rfl

/-- Reversing the orientation swaps in-edges and out-edges. -/
@[simp]
lemma inEdgeSet_reverse : G.inEdgeSet O.reverse v = G.outEdgeSet O v := rfl

/-- A loop at `v` is directed out of `v`. -/
lemma IsLoopAt.mem_outEdgeSet (h : G.IsLoopAt e v) (O : Orientation G) :
    e ∈ G.outEdgeSet O v :=
  ⟨h.edge_mem, O.tail_eq_of_isLoopAt h⟩

/-- A loop at `v` is directed in to `v`. -/
lemma IsLoopAt.mem_inEdgeSet (h : G.IsLoopAt e v) (O : Orientation G) :
    e ∈ G.inEdgeSet O v :=
  ⟨h.edge_mem, O.head_eq_of_isLoopAt h⟩

/-! ### The out- and in-sums of a map at a vertex -/

/-- The sum of `f` over the edges of `G` directed out of `v`. -/
noncomputable def outSum (G : Graph α β) (O : Orientation G) (f : β → A) (v : α) : A :=
  ∑ᶠ e ∈ G.outEdgeSet O v, f e

/-- The sum of `f` over the edges of `G` directed in to `v`. -/
noncomputable def inSum (G : Graph α β) (O : Orientation G) (f : β → A) (v : α) : A :=
  ∑ᶠ e ∈ G.inEdgeSet O v, f e

@[simp]
lemma outSum_reverse : G.outSum O.reverse f v = G.inSum O f v := rfl

@[simp]
lemma inSum_reverse : G.inSum O.reverse f v = G.outSum O f v := rfl

/-! ### Flows -/

/-- `G.IsFlow O f` says that `f`, read through the orientation `O`, is a **flow**: at every
vertex, the sum of `f` over the out-edges equals the sum over the in-edges. Here `A` is an
arbitrary abelian group, so this is the paper's notion of an `A`-flow. -/
def IsFlow (G : Graph α β) (O : Orientation G) (f : β → A) : Prop :=
  ∀ v ∈ V(G), G.outSum O f v = G.inSum O f v

/-- `G.IsNowhereZero f` says that `f` takes no zero value on an edge of `G`. A *nowhere-zero
`A`-flow* is a map satisfying both this and `Graph.IsFlow`. -/
def IsNowhereZero (G : Graph α β) (f : β → A) : Prop :=
  ∀ e ∈ E(G), f e ≠ 0

/-- `G.IsIntegerKFlow O φ k` says that the integer-valued map `φ` is an **integer `k`-flow**:
a flow satisfying `0 < |φ e| < k` on every edge. The side condition `k ≥ 2` is stated by the
caller, not folded in here. -/
def IsIntegerKFlow (G : Graph α β) (O : Orientation G) (φ : β → ℤ) (k : ℤ) : Prop :=
  G.IsFlow O φ ∧ ∀ e ∈ E(G), 0 < |φ e| ∧ |φ e| < k

/-! ### Basic lemmas -/

/-- The zero map is a flow. -/
theorem isFlow_zero (G : Graph α β) (O : Orientation G) :
    G.IsFlow O (0 : β → A) := by
  intro v _
  simp [Graph.outSum, Graph.inSum]

/-- A map is a flow for `O` iff it is a flow for the reversed orientation. -/
theorem isFlow_reverse_iff : G.IsFlow O.reverse f ↔ G.IsFlow O f := by
  simp only [Graph.IsFlow, Graph.outSum_reverse, Graph.inSum_reverse]
  exact ⟨fun h v hv ↦ (h v hv).symm, fun h v hv ↦ (h v hv).symm⟩

alias ⟨IsFlow.of_reverse, IsFlow.reverse⟩ := Graph.isFlow_reverse_iff

/-- The negation of a flow is a flow (on a graph with finitely many edges). -/
theorem IsFlow.neg (hE : E(G).Finite) (hf : G.IsFlow O f) : G.IsFlow O (-f) := by
  intro v hv
  have hout : (G.outEdgeSet O v).Finite := hE.subset Graph.outEdgeSet_subset_edgeSet
  have hin : (G.inEdgeSet O v).Finite := hE.subset Graph.inEdgeSet_subset_edgeSet
  simp only [Graph.outSum, Graph.inSum, Pi.neg_apply, finsum_mem_neg_distrib _ hout,
    finsum_mem_neg_distrib _ hin]
  exact congrArg Neg.neg (hf v hv)

/-- The sum of two flows is a flow (on a graph with finitely many edges). -/
theorem IsFlow.add (hE : E(G).Finite) (hf : G.IsFlow O f) (hg : G.IsFlow O g) :
    G.IsFlow O (f + g) := by
  intro v hv
  have hout : (G.outEdgeSet O v).Finite := hE.subset Graph.outEdgeSet_subset_edgeSet
  have hin : (G.inEdgeSet O v).Finite := hE.subset Graph.inEdgeSet_subset_edgeSet
  simp only [Graph.outSum, Graph.inSum, Pi.add_apply, finsum_mem_add_distrib hout,
    finsum_mem_add_distrib hin]
  exact congrArg₂ (· + ·) (hf v hv) (hg v hv)

/-- An integer `k`-flow is in particular a flow. -/
theorem IsIntegerKFlow.isFlow (h : G.IsIntegerKFlow O φ k) : G.IsFlow O φ := h.1

/-- An integer `k`-flow is nowhere-zero. -/
theorem IsIntegerKFlow.isNowhereZero (h : G.IsIntegerKFlow O φ k) :
    G.IsNowhereZero φ := fun e he ↦ abs_pos.mp (h.2 e he).1

/-- The values of an integer `k`-flow on edges are bounded: `|φ e| < k`. -/
theorem IsIntegerKFlow.abs_lt (h : G.IsIntegerKFlow O φ k) (he : e ∈ E(G)) :
    |φ e| < k := (h.2 e he).2

/-- An integer `k`-flow for the reversed orientation is the same thing as one for `O`. -/
theorem isIntegerKFlow_reverse_iff :
    G.IsIntegerKFlow O.reverse φ k ↔ G.IsIntegerKFlow O φ k := by
  simp [Graph.IsIntegerKFlow, Graph.isFlow_reverse_iff]

/-! ### Finite reformulation

On a graph with finitely many edges the `finsum`s are ordinary `Finset.sum`s. -/

lemma outSum_eq_finset_sum (hE : E(G).Finite) (O : Orientation G) (f : β → A)
    (v : α) : G.outSum O f v = ∑ e ∈ (hE.subset (Graph.outEdgeSet_subset_edgeSet
      (O := O) (v := v))).toFinset, f e := by
  rw [Graph.outSum, ← finsum_mem_coe_finset]
  exact finsum_mem_congr (by simp) fun _ _ ↦ rfl

lemma inSum_eq_finset_sum (hE : E(G).Finite) (O : Orientation G) (f : β → A)
    (v : α) : G.inSum O f v = ∑ e ∈ (hE.subset (Graph.inEdgeSet_subset_edgeSet
      (O := O) (v := v))).toFinset, f e := by
  rw [Graph.inSum, ← finsum_mem_coe_finset]
  exact finsum_mem_congr (by simp) fun _ _ ↦ rfl

/-- Conservation as an identity of ordinary finite sums over the edge set, when `E(G)` is finite. -/
theorem isFlow_iff_finset_sum [DecidableEq α] (hE : E(G).Finite) :
    G.IsFlow O f ↔ ∀ v ∈ V(G),
      ∑ e ∈ hE.toFinset with O.tail e = v, f e = ∑ e ∈ hE.toFinset with O.head e = v, f e := by
  have key : ∀ (t : β → α) (v : α),
      (∑ᶠ e ∈ {e ∈ E(G) | t e = v}, f e) = ∑ e ∈ hE.toFinset with t e = v, f e := by
    intro t v
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_congr ?_ fun _ _ ↦ rfl
    ext e
    simp [Set.mem_setOf_eq, and_comm]
  simp only [Graph.IsFlow, Graph.outSum, Graph.inSum, Graph.outEdgeSet, Graph.inEdgeSet,
    key O.tail, key O.head]

end Graph
