import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.Flow
import Workspace.Types.LocalShift

/-!
# The linear system `L` of Lemma 2.2

Formalises the linear-algebraic core of Lemma 2.2:

> `L : Γ^{V(G)} ⊕ 𝔽₂^{E(G)} ⟶ Γ^{E(G)}`,  `L(t, ε)_e = t_u + t_v + ε_e f(e)`  (`e = uv`),

so that the system (4), `t_u + t_v + ε_e f(e) = d_e`, is solvable exactly when `d` belongs to
`im L`. `SystemL G` bundles the two `Γ`-valued edge functions `flow` (the paper's `f`) and `rhs`
(the paper's `d`); the structure carries no axioms, and `L`, `HasSolution` and the bridge
between them are definitions and lemmas.

Design points, each justified by a lemma below:
* The codomain is `↥E(G) → Γ` (the paper's `Γ^{E(G)}`), not `β → Γ`, so `d ∈ im L` imposes no
  spurious condition on non-edges.
* The domain uses total functions `(α → Γ) × (β → 𝔽₂)`; only their restrictions to `V(G)`/`E(G)`
  affect `L` (`L_congr`), so the range is unchanged.
* `t_u + t_v` is the symmetric ends sum `∑ᶠ w ∈ {w | G.Inc e w}, t w`, equal to `t u + t v` for
  distinct ends (`L_apply_of_isLink`); the ends set is always finite (`setOf_inc_finite`), so no
  finiteness hypothesis on `G` is needed.
-/

open Set Function
open scoped Graph
open Workspace.Types.Gamma
open Workspace.Types.LocalShift

namespace Workspace.Types.SystemL

open Workspace.Types.SystemL

variable {α β : Type*} {G : Graph α β} {e : β} {u v : α}

/-! ## The set of ends of an edge is finite -/

/-- The set of ends of an edge is always finite: it is empty when `e ∉ E(G)`, and is the
(at most two element) pair of ends of `e` otherwise.  This is what makes the ends sum
`∑ᶠ w ∈ {w | G.Inc e w}, t w` additive and `𝔽₂`-homogeneous in `t` with **no** finiteness
hypothesis on `G`. -/
lemma setOf_inc_finite (G : Graph α β) (e : β) : {w | G.Inc e w}.Finite := by
  by_cases he : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := Graph.exists_isLink_of_mem_edgeSet he
    rw [LocalShift.setOf_inc_eq_pair h]
    exact (Set.finite_singleton y).insert x
  · have hemp : {w | G.Inc e w} = (∅ : Set α) := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hw => he hw.edge_mem
    rw [hemp]
    exact Set.finite_empty

/-! ## The data of the system -/

/-- The data of the paper's linear system (4) on a multigraph `G`: the edge function `f`
(`flow`) appearing in the term `ε_e f(e)`, and the right-hand side `d` (`rhs`).

No axioms: the map `L`, the solvability predicate `HasSolution` and the bridge between them
are definitions and lemmas on this data.  In particular `flow` is *not* required to be a flow
and `rhs` is *not* required to arise from a local shift — those are hypotheses of the lemmas
that use the system, not part of what it means to write the system down. -/
@[ext]
structure SystemL (G : Graph α β) where
  /-- The paper's `f`: the `Γ`-valued edge function in the term `ε_e f(e)`. -/
  flow : β → Gamma
  /-- The paper's `d`: the right-hand side of the system (4). -/
  rhs : β → Gamma

namespace SystemL

variable (Sys : SystemL G)

/-! ## The map `L` -/

/-- **The paper's map `L : Γ^{V(G)} ⊕ 𝔽₂^{E(G)} ⟶ Γ^{E(G)}`**, `L(t, ε)_e = t_u + t_v + ε_e f(e)`
(`e = uv`), as a bundled `𝔽₂`-linear map. The codomain is indexed by `↥E(G)`, the ends sum is
symmetric, and additivity/homogeneity hold unconditionally since the ends set is finite. -/
noncomputable def L : ((α → Gamma) × (β → F2)) →ₗ[F2] (↥E(G) → Gamma) where
  toFun p := fun e : ↥E(G) =>
    (∑ᶠ w ∈ {w | G.Inc (e : β) w}, p.1 w) + p.2 (e : β) • Sys.flow (e : β)
  map_add' p q := by
    funext e
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    rw [finsum_mem_add_distrib (setOf_inc_finite G (e : β)), add_smul]
    abel
  map_smul' c p := by
    funext e
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply, smul_add,
      smul_eq_mul]
    rw [← smul_finsum_mem (setOf_inc_finite G (e : β)), mul_smul]

/-- The defining formula for `L`: `L(t, ε)_e = (∑ over the ends w of e, t w) + ε_e • f(e)`. -/
@[simp]
lemma L_apply (p : (α → Gamma) × (β → F2)) (e : ↥E(G)) :
    Sys.L p e = (∑ᶠ w ∈ {w | G.Inc (e : β) w}, p.1 w) + p.2 (e : β) • Sys.flow (e : β) :=
  rfl

/-- **`L` in the paper's notation.** For an edge `e` with distinct ends `u ≠ v` (automatic when
`G` is loopless), `L(t, ε)_e = t_u + t_v + ε_e f(e)`. -/
lemma L_apply_of_isLink (p : (α → Gamma) × (β → F2)) (e : ↥E(G))
    (h : G.IsLink (e : β) u v) (hne : u ≠ v) :
    Sys.L p e = p.1 u + p.1 v + p.2 (e : β) • Sys.flow (e : β) := by
  rw [L_apply, LocalShift.setOf_inc_eq_pair h, finsum_mem_pair hne]

/-- **Justification for using total functions on the domain.** The value of `L` depends only on
the restriction of `t` to `V(G)` and of `ε` to `E(G)`; hence taking the domain to be
`(α → Γ) × (β → 𝔽₂)` rather than `(↥V(G) → Γ) × (↥E(G) → 𝔽₂)` does not change the range of
`L`, and so does not change the meaning of `rhs ∈ range L`. -/
lemma L_congr (p q : (α → Gamma) × (β → F2)) (ht : ∀ v ∈ V(G), p.1 v = q.1 v)
    (hε : ∀ e ∈ E(G), p.2 e = q.2 e) : Sys.L p = Sys.L q := by
  funext e
  rw [L_apply, L_apply, hε (e : β) e.2]
  congr 1
  exact finsum_mem_congr rfl fun w hw => ht w (Graph.Inc.vertex_mem hw)

/-! ## Solvability of the system (4) -/

/-- **The system (4).** `HasSolution` says that there are `t : V(G) → Γ` and `ε : E(G) → 𝔽₂`
(given here as total functions, cf. `L_congr`) with

  `t_u + t_v + ε_e f(e) = d_e`   for every **edge** `e = uv` of `G`.

Note the quantifier is over `e ∈ E(G)` only — no condition is imposed at `e ∉ E(G)`.  This is
the statement of the paper's Lemma 2.2. -/
def HasSolution : Prop :=
  ∃ t : α → Gamma, ∃ ε : β → F2,
    ∀ e ∈ E(G), (∑ᶠ w ∈ {w | G.Inc e w}, t w) + ε e • Sys.flow e = Sys.rhs e

lemma hasSolution_def :
    Sys.HasSolution ↔ ∃ t : α → Gamma, ∃ ε : β → F2,
      ∀ e ∈ E(G), (∑ᶠ w ∈ {w | G.Inc e w}, t w) + ε e • Sys.flow e = Sys.rhs e :=
  Iff.rfl

/-- The right-hand side `d` of the system, viewed as an element of the codomain `Γ^{E(G)}`
of `L`. -/
def rhsOn : ↥E(G) → Gamma := Set.restrict E(G) Sys.rhs

@[simp]
lemma rhsOn_apply (e : ↥E(G)) : Sys.rhsOn e = Sys.rhs (e : β) := rfl

/-- **The bridging lemma.** "(4) asks whether `d = (d_e)_e` belongs to `im L`": the system (4)
is solvable exactly when the restriction of `d` to `E(G)` lies in the range of `L`. -/
theorem hasSolution_iff_mem_range :
    Sys.HasSolution ↔ Sys.rhsOn ∈ LinearMap.range Sys.L := by
  constructor
  · rintro ⟨t, ε, h⟩
    refine ⟨(t, ε), ?_⟩
    funext e
    exact h (e : β) e.2
  · rintro ⟨⟨t, ε⟩, h⟩
    exact ⟨t, ε, fun e he => congrFun h ⟨e, he⟩⟩

/-- The paper's phrasing, with `im L` written as a `Submodule`. -/
theorem hasSolution_iff_mem_range_map :
    Sys.HasSolution ↔ Sys.rhsOn ∈ Set.range (Sys.L : ((α → Gamma) × (β → F2)) → (↥E(G) → Gamma)) :=
  Sys.hasSolution_iff_mem_range

/-! ## The system arising from a local shift

In the paper the system (4) is set up with `f` a nowhere-zero `Γ`-flow and `d` the
edge-difference `d_e = g_{u,e} + g_{v,e}` of the local shift built from `f` and a local
ordering.  This is the corresponding `SystemL`. -/

/-- The system (4) attached to a local shift `S`: take `f = S.flow` and `d = S.d`. -/
noncomputable def ofLocalShift (S : LocalShift G) : SystemL G where
  flow := S.flow
  rhs := S.d

@[simp]
lemma ofLocalShift_flow (S : LocalShift G) : (ofLocalShift S).flow = S.flow := rfl

@[simp]
lemma ofLocalShift_rhs (S : LocalShift G) : (ofLocalShift S).rhs = S.d := rfl

end SystemL

end Workspace.Types.SystemL
