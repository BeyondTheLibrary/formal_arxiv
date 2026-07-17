import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.LocalOrdering
import Workspace.Types.Gamma
import Workspace.Types.Flow

/-!
# The local shift `g` and its edge-difference `d`

Formalises the paper's shift construction (2): at each vertex `v` with locally ordered incident
edges `a, b, c` and `x = f(a)`, set `g_{v,a} = 0`, `g_{v,b} = x`, `g_{v,c} = 0`, and for `e = uv`
put `d_e = g_{u,e} + g_{v,e}`. Thus `g` is supported on the *second* listed edge, where its value
is the flow on the *first* (`g_edge_one`: `S.g v (ord.edge v 1) = S.flow (ord.edge v 0)`).

`LocalShift G` bundles the input data `flow : β → Γ` and `ord : LocalOrdering G`; `g` and `d`
are then `def`s, so the structure carries no axioms. `d` is defined as a `finsum` over the set
of ends `∑ᶠ w ∈ {w | G.Inc e w}, S.g w e`, symmetric by construction and equal to `g_{u,e} + g_{v,e}`
for a non-loop edge (`d_eq_add`). Values of `g` off the second listed edge, and at `v ∉ V(G)`,
are zero/junk and are only ever observed through the incident-edge sum (8) and through `d`.
-/

open Set Function
open scoped Graph
open Workspace.Types.Gamma
open Workspace.Types.LocalOrdering

namespace Workspace.Types.LocalShift

open Workspace.Types.LocalShift

variable {α β : Type*} {G : Graph α β} {e : β} {u v w : α}

/-- The input data of the paper's shift construction on a multigraph `G`: a `Γ`-valued map
`flow` on the edges (the paper's `f`; in the applications it is a nowhere-zero `Γ`-flow, but
that is a hypothesis of the lemmas, not part of this data) together with a local ordering
`ord` of the edges at each vertex (the paper's `a, b, c`).

The shift `g` and its edge-difference `d` are *definitions* on this data — see
`LocalShift.g` and `LocalShift.d` — so the structure carries no axioms. -/
@[ext]
structure LocalShift (G : Graph α β) where
  /-- The `Γ`-valued map on edges — the paper's `f`. -/
  flow : β → Gamma
  /-- The local ordering of the edges at each vertex — the paper's `a, b, c` at each `v`. -/
  ord : LocalOrdering G

namespace LocalShift

variable (S : LocalShift G)

/-! ## The shift `g` -/

open Classical in
/-- The paper's shift `g_{v,e}` of equation (2): supported on the second listed edge
`b = ord.edge v 1`, where its value is `flow (ord.edge v 0)`, and zero on every other edge. -/
noncomputable def g (S : LocalShift G) (v : α) (e : β) : Gamma :=
  if e = S.ord.edge v 1 then S.flow (S.ord.edge v 0) else 0

/-- The shift vanishes off the second listed edge at `v`. -/
@[simp]
lemma g_of_ne (h : e ≠ S.ord.edge v 1) : S.g v e = 0 := by
  simp [g, h]

/-- `g_{v,b} = x`: the shift on the **second** listed edge `b = ord.edge v 1` is the flow value
`x = flow a` on the **first** listed edge `a = ord.edge v 0`.  This is the substance of
equation (2). -/
@[simp]
lemma g_edge_one (v : α) : S.g v (S.ord.edge v 1) = S.flow (S.ord.edge v 0) := by
  simp [g]

/-- `g_{v,a} = 0`: the shift on the first listed edge vanishes. -/
@[simp]
lemma g_edge_zero (hv : v ∈ V(G)) : S.g v (S.ord.edge v 0) = 0 :=
  S.g_of_ne (S.ord.edge_ne_edge hv (by decide))

/-- `g_{v,c} = 0`: the shift on the third listed edge vanishes. -/
@[simp]
lemma g_edge_two (hv : v ∈ V(G)) : S.g v (S.ord.edge v 2) = 0 :=
  S.g_of_ne (S.ord.edge_ne_edge hv (by decide))

/-- `g v` is nonzero only on the second listed edge at `v`. -/
lemma eq_edge_one_of_g_ne_zero (h : S.g v e ≠ 0) : e = S.ord.edge v 1 := by
  by_contra hne
  exact h (S.g_of_ne hne)

/-- The support of `g v` is contained in the singleton `{ord.edge v 1}`. -/
lemma support_g_subset : Function.support (S.g v) ⊆ {S.ord.edge v 1} :=
  fun _ he ↦ S.eq_edge_one_of_g_ne_zero he

/-! ## Equation (8): the local sum of the shift

At a vertex `v` of `G` the three incident edges are `a, b, c` and they contribute
`0 + x + 0 = x` to the sum of `g_{v,·}`.  Note that no looplessness or cubicness hypothesis is
needed: the axioms of `LocalOrdering` already say that `a, b, c` enumerate `G.incidenceSet v`
without repetition, for every `v ∈ V(G)`. -/

/-- The edges incident to `v ∈ V(G)` are exactly the three listed edges `a, b, c`. -/
lemma incidenceSet_eq_triple (hv : v ∈ V(G)) :
    G.incidenceSet v = {S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} := by
  rw [← S.ord.range_edge hv]
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- **Equation (8).** The sum of the shift over the edges incident to a vertex `v` of `G` is
`x = flow (ord.edge v 0)`, since the three incident edges `a, b, c` contribute `0 + x + 0`. -/
theorem finsum_g_incidenceSet (hv : v ∈ V(G)) :
    (∑ᶠ e ∈ G.incidenceSet v, S.g v e) = S.flow (S.ord.edge v 0) := by
  classical
  have h01 : S.ord.edge v 0 ≠ S.ord.edge v 1 := S.ord.edge_ne_edge hv (by decide)
  have h02 : S.ord.edge v 0 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have h12 : S.ord.edge v 1 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have hcoe : ({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Set β)
      = (↑({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Finset β) : Set β) := by
    simp
  rw [S.incidenceSet_eq_triple hv, hcoe, finsum_mem_coe_finset]
  rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton]
  simp [S.g_edge_zero hv, S.g_edge_one v, S.g_edge_two hv]

/-! ## The edge-difference `d` -/

/-- The paper's `d_e = g_{u,e} + g_{v,e}` for an edge `e` with ends `u, v`.

To keep the definition manifestly symmetric in the two ends — the paper's formula does not
depend on which end is called `u` — we sum `g_{·,e}` over the *set of ends* of `e`.  For a
non-loop edge with ends `u ≠ v` this is exactly `g_{u,e} + g_{v,e}`; see `d_eq_add`. -/
noncomputable def d (S : LocalShift G) (e : β) : Gamma :=
  ∑ᶠ w ∈ {w | G.Inc e w}, S.g w e

lemma d_def (e : β) : S.d e = ∑ᶠ w ∈ {w | G.Inc e w}, S.g w e := rfl

/-- The set of ends of a non-loop edge `e` with ends `u ≠ v` is the pair `{u, v}`. -/
lemma setOf_inc_eq_pair (h : G.IsLink e u v) : {w | G.Inc e w} = ({u, v} : Set α) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨(Graph.isLink_iff_inc.1 h).2.2 x, ?_⟩
  rintro (rfl | rfl)
  exacts [h.inc_left, h.inc_right]

/-- **The paper's formula for `d`.** For an edge `e` whose ends `u, v` are distinct (i.e. `e` is
not a loop — automatic in a loopless graph), `d_e = g_{u,e} + g_{v,e}`. -/
theorem d_eq_add (h : G.IsLink e u v) (hne : u ≠ v) : S.d e = S.g u e + S.g v e := by
  rw [d_def, setOf_inc_eq_pair h, finsum_mem_pair hne]

/-- An edge that is not the second listed edge at either of its (distinct) ends has `d_e = 0`. -/
lemma d_eq_zero_of_ne (h : G.IsLink e u v) (hne : u ≠ v) (hu : e ≠ S.ord.edge u 1)
    (hv : e ≠ S.ord.edge v 1) : S.d e = 0 := by
  rw [S.d_eq_add h hne, S.g_of_ne hu, S.g_of_ne hv, add_zero]

end LocalShift

end Workspace.Types.LocalShift
