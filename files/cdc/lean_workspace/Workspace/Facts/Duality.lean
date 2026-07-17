import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.MultigraphBasic
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.Types.LocalOrdering
import Workspace.Types.LocalShift
import Workspace.Types.SystemL
import Workspace.Facts.Construction

/-!
# §6 — the proof of Lemma 2.2: duality, condition (5), and the double count

This file states, one theorem per paper sentence, the facts 6a–6j of *"A Proof of the Cycle
Double Cover Conjecture"*, together with the headline `Lemma 2.2` they establish: the system
(4) has a solution.

The paper's linear map `L : Γ^{V(G)} ⊕ 𝔽₂^{E(G)} ⟶ Γ^{E(G)}`,
`L(t, ε)_e = t_u + t_v + ε_e f(e)` (`e = uv`), is `SystemL.L`. The local data `g_{v,e}` of
(2) and `d_e = g_{u,e} + g_{v,e}` are `S.g` and `S.d` for a `LocalShift G`; the paper's
`a, b, c` at `v` are `S.ord.edge v 0/1/2` and `x, y, z` the flow values there.

Three auxiliary definitions render notation not present in the imported type files:
`dualPairing` (the action `η(w) = Σ_e η_e(w_e)` of a dual family on `Γ^{E(G)}`), `dualSum`
(the same sum for a total `w : β → Γ`), `Cond5` (condition (5)), and `nonzeroInd φ` (the
`𝔽₂`-indicator `1_{φ ≠ 0}` of Fact 6h).

Every statement about a graph carries both `V(G).Finite` and `E(G).Finite`; they are
load-bearing on this file's `finsum`/`ncard`-based definitions (`fact_6i` is pure linear
algebra and carries neither).
-/

open Set

open scoped Graph

open Workspace.Types.Gamma
open Workspace.Types.Orientation
open Workspace.Types.LocalOrdering
open Workspace.Types.LocalShift
open Workspace.Types.SystemL
open Workspace.Facts.Construction

namespace Workspace.Facts.Duality

variable {α β : Type*} {G : Graph α β} {e : β} {u v : α}

/-! ## Auxiliary definitions

These render the paper's notation; none of them is available in the imported type files. -/

/-- **The action of a dual family on `Γ^{E(G)}`.** *A dual vector to `Γ^{E(G)}` is written as
a family `η = (η_e)_{e ∈ E(G)}` with `η_e ∈ Γ*`; it acts by `η(w) = Σ_e η_e(w_e)`.*

The dual family is a map `η : β → Γ*`; only its values on `E(G)` are ever consulted, since
the sum ranges over the subtype `↥E(G)`. -/
noncomputable def dualPairing {G : Graph α β} (η : β → GammaDual) (w : ↥E(G) → Gamma) : F2 :=
  ∑ᶠ e : ↥E(G), η (e : β) (w e)

/-- `Σ_{e ∈ E(G)} η_e(w_e)` for a **total** edge function `w : β → Γ`, such as the paper's
`d = (d_e)_e`, which is `LocalShift.d`. -/
noncomputable def dualSum (G : Graph α β) (η : β → GammaDual) (w : β → Gamma) : F2 :=
  ∑ᶠ e ∈ E(G), η e (w e)

/-- The bridge between the two spellings of `Σ_e η_e(w_e)`: pairing `η` with the restriction
of a total `w : β → Γ` to `E(G)` is summing `η_e(w_e)` over `E(G)`. -/
theorem dualPairing_restrict (η : β → GammaDual) (w : β → Gamma) :
    dualPairing η (Set.restrict E(G) w) = dualSum G η w := by
  rw [dualPairing, dualSum]
  exact finsum_subtype_eq_finsum_cond (f := fun e => η e (w e)) (· ∈ E(G))

/-- **Condition (5)** of the paper:

  `η_e(f(e)) = 0`  (`e ∈ E(G)`),      `Σ_{e ∋ v} η_e = 0`  (`v ∈ V(G)`).

By Fact 6c this says exactly that the dual family `η` annihilates `im L`. -/
def Cond5 (G : Graph α β) (f : β → Gamma) (η : β → GammaDual) : Prop :=
  (∀ e ∈ E(G), η e (f e) = 0) ∧ (∀ v ∈ V(G), (∑ᶠ e ∈ G.incidenceSet v, η e) = 0)

open Classical in
/-- The paper's `1_{η ≠ 0}`: the bit of `𝔽₂` recording whether a dual vector is nonzero. -/
noncomputable def nonzeroInd (φ : GammaDual) : F2 := if φ ≠ 0 then 1 else 0

/-- Characteristic two on the `𝔽₂`-vector space `Γ*`: every dual vector is its own inverse. -/
private lemma gammaDual_add_self (φ : GammaDual) : φ + φ = 0 := by
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.zero_apply]
  exact CharTwo.add_self_eq_zero (φ x)

/-! ## Private bookkeeping helpers (finsum double counting over the incidence relation) -/

/-- Summing `f` over a subset `s` of `t` is the same as summing the `s`-indicator of `f`
over `t`. -/
private lemma finsum_mem_subset_indicator {M : Type*} [AddCommMonoid M] {X : Type*}
    {s t : Set X} (hst : s ⊆ t) (f : X → M) :
    (∑ᶠ x ∈ s, f x) = ∑ᶠ x ∈ t, s.indicator f x := by
  rw [finsum_mem_def s f, finsum_mem_def t (s.indicator f), Set.indicator_indicator,
    Set.inter_eq_right.mpr hst]

open Classical in
/-- **The incidence double count.** Summing over edges and, for each edge, over its ends, is the
same as summing over vertices and, for each vertex, over its incident edges. -/
private lemma incidence_double_sum {M : Type*} [AddCommMonoid M] (hV : V(G).Finite)
    (hE : E(G).Finite) (F : β → α → M) :
    (∑ᶠ e ∈ E(G), ∑ᶠ w ∈ {w | G.Inc e w}, F e w)
      = ∑ᶠ v ∈ V(G), ∑ᶠ e ∈ G.incidenceSet v, F e v := by
  have h1 : ∀ e ∈ E(G), (∑ᶠ w ∈ {w | G.Inc e w}, F e w)
      = ∑ᶠ w ∈ V(G), {w | G.Inc e w}.indicator (F e) w := fun e _ =>
    finsum_mem_subset_indicator (fun w hw => Graph.Inc.vertex_mem hw) (F e)
  rw [finsum_mem_congr rfl h1, finsum_mem_comm _ hE hV]
  refine finsum_mem_congr rfl fun v hv => ?_
  rw [finsum_mem_subset_indicator (s := G.incidenceSet v) (t := E(G))
        (fun e he => he.edge_mem) (fun e => F e v)]
  refine finsum_mem_congr rfl fun e he => ?_
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Graph.mem_incidenceSet]

/-- A `finsum` over a set of a function supported at a single point of the set. -/
private lemma finsum_mem_eq_single' {M : Type*} [AddCommMonoid M] {X : Type*} {s : Set X}
    {g : X → M} {a : X} (ha : a ∈ s) (h : ∀ x ∈ s, x ≠ a → g x = 0) :
    (∑ᶠ x ∈ s, g x) = g a := by
  classical
  rw [finsum_mem_def, finsum_eq_single (s.indicator g) a ?_, Set.indicator_of_mem ha]
  intro x hx
  rcases em (x ∈ s) with hxs | hxs
  · rw [Set.indicator_of_mem hxs]; exact h x hxs hx
  · rw [Set.indicator_of_notMem hxs]

/-- **The bridge between dual families and functionals on `Γ^{E(G)}`.** Every `𝔽₂`-linear
functional `φ` on the codomain `↥E(G) → Γ` of `L` is `dualPairing η` for some dual family
`η`.  Construct `η_b` as `φ` precomposed with the coordinate insertion `Pi.single b` (for
`b ∈ E(G)`), and `0` off `E(G)`. -/
private lemma exists_eta_of_functional (hE : E(G).Finite)
    (φ : (↥E(G) → Gamma) →ₗ[F2] F2) :
    ∃ η : β → GammaDual, ∀ w : ↥E(G) → Gamma, dualPairing η w = φ w := by
  classical
  haveI : Fintype ↥E(G) := hE.fintype
  refine ⟨fun b => if h : b ∈ E(G) then
      φ ∘ₗ (LinearMap.single F2 (fun _ : ↥E(G) => Gamma) ⟨b, h⟩) else 0, ?_⟩
  intro w
  rw [dualPairing, finsum_eq_sum_of_fintype]
  have hterm : ∀ e : ↥E(G), (fun b => if h : b ∈ E(G) then
      φ ∘ₗ (LinearMap.single F2 (fun _ : ↥E(G) => Gamma) ⟨b, h⟩) else 0) (e : β) (w e)
      = φ (Pi.single e (w e)) := by
    intro e
    simp only [dif_pos e.2, LinearMap.comp_apply, LinearMap.coe_single]
  rw [Finset.sum_congr rfl (fun e _ => hterm e), ← map_sum, LinearMap.sum_single_apply]

/-! ## Fact 6a — the duality criterion -/

/-- **Fact 6a (duality criterion).** *`d ∈ im L` if and only if every family `η` which takes
the value zero on `im L` also satisfies `Σ_e η_e(d_e) = 0`.*

"`η` takes the value zero on `im L`" is `∀ p, Σ_e η_e(L(p)_e) = 0`; the conclusion is
`Σ_e η_e(d_e) = 0`.  Both are the pairing `dualPairing`. -/
theorem fact_6a (hV : V(G).Finite) (hE : E(G).Finite) (Sys : SystemL G) (d : ↥E(G) → Gamma) :
    d ∈ LinearMap.range Sys.L ↔
      ∀ η : β → GammaDual,
        (∀ p : (α → Gamma) × (β → F2), dualPairing η (Sys.L p) = 0) →
          dualPairing η d = 0 := by
  classical
  haveI : Fintype ↥E(G) := hE.fintype
  haveI : FiniteDimensional F2 (↥E(G) → Gamma) := inferInstance
  set U : Submodule F2 (↥E(G) → Gamma) := LinearMap.range Sys.L with hU
  constructor
  · intro hd η hη
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hd
    exact hη p
  · intro hRHS
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U d]
    intro φ hφ
    obtain ⟨η, hη⟩ := exists_eta_of_functional hE φ
    have hηann : ∀ p, dualPairing η (Sys.L p) = 0 := by
      intro p
      rw [hη]
      exact (Submodule.mem_dualAnnihilator φ).mp hφ (Sys.L p) (LinearMap.mem_range_self Sys.L p)
    rw [← hη d]
    exact hRHS η hηann

/-! ## Fact 6b — the expansion -/

/-- **Fact 6b (expansion).** *For every `(t, ε)`,*

  `Σ_e η_e(L(t,ε)_e) = Σ_v (Σ_{e ∋ v} η_e)(t_v) + Σ_e ε_e η_e(f(e))`.

Pure bookkeeping: expand `L(t,ε)_e = t_u + t_v + ε_e f(e)` by linearity of `η_e` and
exchange the order of summation.  No flow, looplessness or cubicness hypothesis is involved;
only the finiteness of the two index sets, which the exchange of summation needs. -/
theorem fact_6b (hV : V(G).Finite) (hE : E(G).Finite) (Sys : SystemL G)
    (η : β → GammaDual) (t : α → Gamma) (ε : β → F2) :
    dualPairing η (Sys.L (t, ε))
      = (∑ᶠ v ∈ V(G), (∑ᶠ e ∈ G.incidenceSet v, η e) (t v))
        + ∑ᶠ e ∈ E(G), ε e * η e (Sys.flow e) := by
  classical
  have hfe : Finite (↥E(G)) := hE.to_subtype
  have hpt : ∀ e : ↥E(G),
      η (e : β) (Sys.L (t, ε) e)
        = (∑ᶠ w ∈ {w | G.Inc (e : β) w}, η (e : β) (t w))
          + ε (e : β) * η (e : β) (Sys.flow (e : β)) := by
    intro e
    rw [Sys.L_apply, map_add]
    congr 1
    · exact AddMonoidHom.map_finsum_mem t (η (e : β)).toAddMonoidHom (setOf_inc_finite G (e : β))
    · rw [map_smul, smul_eq_mul]
  rw [dualPairing]
  simp_rw [hpt]
  rw [finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  congr 1
  · rw [finsum_subtype_eq_finsum_cond
        (f := fun e => ∑ᶠ w ∈ {w | G.Inc e w}, η e (t w)) (· ∈ E(G))]
    rw [incidence_double_sum hV hE (fun e w => η e (t w))]
    refine finsum_mem_congr rfl fun v hv => ?_
    have hfin : (G.incidenceSet v).Finite := hE.subset fun e he => he.edge_mem
    let ev : GammaDual →+ F2 :=
      { toFun := fun φ => φ (t v), map_zero' := rfl, map_add' := fun a b => rfl }
    exact (AddMonoidHom.map_finsum_mem η ev hfin).symm
  · exact finsum_subtype_eq_finsum_cond
      (f := fun e => ε e * η e (Sys.flow e)) (· ∈ E(G))

/-! ## Fact 6c — the annihilator of `im L`, i.e. condition (5) -/

/-- **Fact 6c (annihilator of `im L`).** *Since the `t_v` and the `ε_e` may be chosen
independently, the quantity in Fact 6b vanishes for every `(t, ε)` precisely when*

  `η_e(f(e)) = 0` (`e ∈ E(G)`),      `Σ_{e ∋ v} η_e = 0` (`v ∈ V(G)`).      (5)

The left-hand side is "`η` takes the value zero on `im L`" — by Fact 6b, exactly the
vanishing of the quantity displayed there. -/
theorem fact_6c (hV : V(G).Finite) (hE : E(G).Finite) (Sys : SystemL G) (η : β → GammaDual) :
    (∀ p : (α → Gamma) × (β → F2), dualPairing η (Sys.L p) = 0) ↔ Cond5 G Sys.flow η := by
  classical
  constructor
  · intro h
    have key : ∀ (t : α → Gamma) (ε : β → F2),
        (∑ᶠ v ∈ V(G), (∑ᶠ e ∈ G.incidenceSet v, η e) (t v))
          + (∑ᶠ e ∈ E(G), ε e * η e (Sys.flow e)) = 0 :=
      fun t ε => (fact_6b hV hE Sys η t ε).symm.trans (h (t, ε))
    refine ⟨fun e0 he0 => ?_, fun v0 hv0 => ?_⟩
    · have hk := key 0 (Pi.single e0 1)
      have h1 : (∑ᶠ v ∈ V(G), (∑ᶠ e ∈ G.incidenceSet v, η e) ((0 : α → Gamma) v)) = 0 := by
        refine (finsum_mem_congr rfl fun v hv => ?_).trans (finsum_mem_zero _)
        simp
      have h2 : (∑ᶠ e ∈ E(G), (Pi.single e0 (1 : F2) : β → F2) e * η e (Sys.flow e))
          = η e0 (Sys.flow e0) := by
        refine finsum_mem_eq_single' he0 (fun e he hne => ?_) |>.trans ?_
        · rw [Pi.single_eq_of_ne hne, zero_mul]
        · rw [Pi.single_eq_same, one_mul]
      rw [h1, h2, zero_add] at hk
      exact hk
    · refine LinearMap.ext fun γ => ?_
      have hk := key (Pi.single v0 γ) 0
      have h2 : (∑ᶠ e ∈ E(G), (0 : β → F2) e * η e (Sys.flow e)) = 0 := by
        refine (finsum_mem_congr rfl fun e he => ?_).trans (finsum_mem_zero _)
        simp
      have h1 : (∑ᶠ v ∈ V(G), (∑ᶠ e ∈ G.incidenceSet v, η e) ((Pi.single v0 γ : α → Gamma) v))
          = (∑ᶠ e ∈ G.incidenceSet v0, η e) γ := by
        refine finsum_mem_eq_single' hv0 (fun v hv hne => ?_) |>.trans ?_
        · rw [Pi.single_eq_of_ne hne, map_zero]
        · rw [Pi.single_eq_same]
      rw [h1, h2, add_zero] at hk
      rw [LinearMap.zero_apply]
      exact hk
  · rintro ⟨he0, hv0⟩ p
    rw [fact_6b hV hE Sys η p.1 p.2]
    have h1 : (∑ᶠ v ∈ V(G), (∑ᶠ e ∈ G.incidenceSet v, η e) (p.1 v)) = 0 := by
      refine (finsum_mem_congr rfl fun v hv => ?_).trans (finsum_mem_zero _)
      rw [hv0 v hv, LinearMap.zero_apply]
    have h2 : (∑ᶠ e ∈ E(G), p.2 e * η e (Sys.flow e)) = 0 := by
      refine (finsum_mem_congr rfl fun e he => ?_).trans (finsum_mem_zero _)
      rw [he0 e he, mul_zero]
    rw [h1, h2, zero_add]

/-! ## Fact 6d — the reduction -/

/-- **Fact 6d (reduction).** *Consequently, it suffices to prove that every family `η`
satisfying (5) also satisfies*

  `Σ_e η_e(d_e) = 0`.                                                        (6)

Combining Facts 6a and 6c: if (6) holds for every `η` obeying (5), then `d ∈ im L`, i.e. the
system (4) is solvable. -/
theorem fact_6d (hV : V(G).Finite) (hE : E(G).Finite) (Sys : SystemL G)
    (h : ∀ η : β → GammaDual, Cond5 G Sys.flow η → dualPairing η Sys.rhsOn = 0) :
    Sys.HasSolution := by
  rw [Sys.hasSolution_iff_mem_range, fact_6a hV hE Sys Sys.rhsOn]
  intro η hη
  exact h η ((fact_6c hV hE Sys η).mp hη)

/-! ## Facts 6e–6h — the local analysis at a vertex

Throughout this section `v` is a vertex of a finite loopless cubic graph `G`, `S` is a local
shift whose `flow` is a nowhere-zero `Γ`-flow (with respect to an orientation `O`), and
`η` is a dual family satisfying (5).  The paper's `a, b, c` are `S.ord.edge v 0`,
`S.ord.edge v 1`, `S.ord.edge v 2`, and `x = f(a)`, `y = f(b)`, `z = f(c)` are
`S.flow (S.ord.edge v i)` for `i = 0, 1, 2`.  The scalar `λ` is `η_b(x)`, i.e.
`η (S.ord.edge v 1) (S.flow (S.ord.edge v 0))`. -/

/-- **Fact 6e (local form of (5)).** *Conditions (5) at `v` become*

  `η_a + η_b + η_c = 0,   η_a(x) = 0,   η_b(y) = 0,   η_c(z) = 0`.           (7)

The first equation is the vertex condition `Σ_{e ∋ v} η_e = 0` of (5), read through the local
ordering: `a, b, c` enumerate the edges at `v` without repetition.  The other three are the
edge condition `η_e(f(e)) = 0` of (5) at `e = a, b, c`, since `x = f(a)`, `y = f(b)`,
`z = f(c)`. -/
theorem fact_6e (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (η : β → GammaDual) (h5 : Cond5 G S.flow η)
    (hv : v ∈ V(G)) :
    η (S.ord.edge v 0) + η (S.ord.edge v 1) + η (S.ord.edge v 2) = 0 ∧
      η (S.ord.edge v 0) (S.flow (S.ord.edge v 0)) = 0 ∧
      η (S.ord.edge v 1) (S.flow (S.ord.edge v 1)) = 0 ∧
      η (S.ord.edge v 2) (S.flow (S.ord.edge v 2)) = 0 := by
  classical
  obtain ⟨he0, hv0⟩ := h5
  refine ⟨?_, he0 _ (S.ord.edge_mem_edgeSet hv 0), he0 _ (S.ord.edge_mem_edgeSet hv 1),
    he0 _ (S.ord.edge_mem_edgeSet hv 2)⟩
  have h01 : S.ord.edge v 0 ≠ S.ord.edge v 1 := S.ord.edge_ne_edge hv (by decide)
  have h02 : S.ord.edge v 0 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have h12 : S.ord.edge v 1 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have hthis := hv0 v hv
  rw [S.incidenceSet_eq_triple hv] at hthis
  have hcoe : ({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Set β)
      = (↑({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Finset β) : Set β) := by simp
  rw [hcoe, finsum_mem_coe_finset, Finset.sum_insert (by simp [h01, h02]),
    Finset.sum_insert (by simp [h12]), Finset.sum_singleton] at hthis
  rw [add_assoc]
  exact hthis

/-- **The characteristic-two flow equation at a vertex (local derivation of §2).** In a loopless
graph, the sum of a `Γ`-flow over the edges incident to a vertex vanishes: the incident edges
split as the disjoint union of the out- and in-edges, whose sums are equal by conservation, and
`a + a = 0` in characteristic two. -/
private lemma flow_incidence_sum_zero (hE : E(G).Finite) (hloop : G.IsLoopless)
    (O : Orientation G) (f : β → Gamma) (hf : G.IsFlow O f) (hv : v ∈ V(G)) :
    (∑ᶠ e ∈ G.incidenceSet v, f e) = 0 := by
  have hout : (G.outEdgeSet O v).Finite := hE.subset Graph.outEdgeSet_subset_edgeSet
  have hin : (G.inEdgeSet O v).Finite := hE.subset Graph.inEdgeSet_subset_edgeSet
  have hunion : G.incidenceSet v = G.outEdgeSet O v ∪ G.inEdgeSet O v := by
    ext e
    simp only [Graph.mem_incidenceSet, Graph.mem_outEdgeSet, Graph.mem_inEdgeSet, Set.mem_union]
    constructor
    · intro hinc
      have he := hinc.edge_mem
      rcases (O.inc_iff he).1 hinc with h | h
      · exact Or.inl ⟨he, h.symm⟩
      · exact Or.inr ⟨he, h.symm⟩
    · rintro (⟨he, ht⟩ | ⟨he, hh⟩)
      · rw [← ht]; exact O.inc_tail he
      · rw [← hh]; exact O.inc_head he
  have hdisj : Disjoint (G.outEdgeSet O v) (G.inEdgeSet O v) := by
    rw [Set.disjoint_left]
    rintro e ⟨he, ht⟩ ⟨-, hh⟩
    have hla : G.IsLoopAt e (O.tail e) :=
      (O.isLoopAt_tail_iff_tail_eq_head he).2 (ht.trans hh.symm)
    rw [ht] at hla
    exact hloop e v hla
  rw [hunion, finsum_mem_union hdisj hout hin]
  have hcons := hf v hv
  rw [Graph.outSum, Graph.inSum] at hcons
  rw [hcons]
  exact Gamma.add_self _

/-- **Fact 6f.** *Set `λ = η_b(x)`. Since `η_c = η_a + η_b` and `z = x + y`, we get
`0 = η_c(z) = η_a(y) + η_b(x)` (using `η_a(x) = η_b(y) = 0`). Hence `η_a(y) = λ`.*

In the notation of the file: `η_a(y) = η (S.ord.edge v 0) (S.flow (S.ord.edge v 1))` and
`λ = η_b(x) = η (S.ord.edge v 1) (S.flow (S.ord.edge v 0))`. -/
theorem fact_6f (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (η : β → GammaDual) (h5 : Cond5 G S.flow η)
    (hv : v ∈ V(G)) :
    η (S.ord.edge v 0) (S.flow (S.ord.edge v 1))
      = η (S.ord.edge v 1) (S.flow (S.ord.edge v 0)) := by
  obtain ⟨hsum, hax, hby, hcz⟩ := fact_6e hV hE hloop hcubic O S hf hnz η h5 hv
  obtain ⟨hz, -, -, -, -⟩ :=
    cubic_flow_distinct hV hE hloop hcubic O S.flow hf hnz S.ord hv
  -- `η_c = η_a + η_b` from `η_a + η_b + η_c = 0` in characteristic two.
  have hηc : η (S.ord.edge v 2) = η (S.ord.edge v 0) + η (S.ord.edge v 1) := by
    have h : η (S.ord.edge v 2) + (η (S.ord.edge v 0) + η (S.ord.edge v 1)) = 0 := by
      rw [← hsum]; abel
    have hs2 : (η (S.ord.edge v 0) + η (S.ord.edge v 1))
        + (η (S.ord.edge v 0) + η (S.ord.edge v 1)) = 0 := gammaDual_add_self _
    calc η (S.ord.edge v 2)
        = (η (S.ord.edge v 2) + (η (S.ord.edge v 0) + η (S.ord.edge v 1)))
            + (η (S.ord.edge v 0) + η (S.ord.edge v 1)) := by rw [add_assoc, hs2, add_zero]
      _ = η (S.ord.edge v 0) + η (S.ord.edge v 1) := by rw [h, zero_add]
  -- Evaluate `η_c(z) = 0` with `z = x + y`.
  have key : η (S.ord.edge v 0) (S.flow (S.ord.edge v 1))
      + η (S.ord.edge v 1) (S.flow (S.ord.edge v 0)) = 0 := by
    have hexp := hcz
    rw [hηc, hz, LinearMap.add_apply, map_add, map_add, hax, hby, zero_add, add_zero] at hexp
    exact hexp
  -- In characteristic two, `p + q = 0 → p = q`.
  have hqq : η (S.ord.edge v 1) (S.flow (S.ord.edge v 0))
      + η (S.ord.edge v 1) (S.flow (S.ord.edge v 0)) = 0 := CharTwo.add_self_eq_zero _
  exact add_right_cancel (key.trans hqq.symm)

/-- **Fact 6g (equation (8)).** *By (2), only the edge `b` contributes at `v`, and therefore*

  `Σ_{e ∋ v} η_e(g_{v,e}) = η_b(x) = λ`.                                     (8)

Indeed `g_{v,a} = g_{v,c} = 0` and `g_{v,b} = x = f(a)` by (2). -/
theorem fact_6g (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (η : β → GammaDual) (h5 : Cond5 G S.flow η)
    (hv : v ∈ V(G)) :
    (∑ᶠ e ∈ G.incidenceSet v, η e (S.g v e))
      = η (S.ord.edge v 1) (S.flow (S.ord.edge v 0)) := by
  classical
  have h01 : S.ord.edge v 0 ≠ S.ord.edge v 1 := S.ord.edge_ne_edge hv (by decide)
  have h02 : S.ord.edge v 0 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have h12 : S.ord.edge v 1 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have hcoe : ({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Set β)
      = (↑({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Finset β) : Set β) := by simp
  rw [S.incidenceSet_eq_triple hv, hcoe, finsum_mem_coe_finset,
    Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton]
  simp [S.g_edge_zero hv, S.g_edge_one v, S.g_edge_two hv]

/-- **Fact 6i (unique annihilating dual vector).** *In the `3`-dimensional `𝔽₂`-space `Γ`, for
a `2`-dimensional subspace `W ≤ Γ` there is exactly one nonzero `η ∈ Γ*` with `η|_W = 0`.*

Pure linear algebra: no graph, no finiteness hypothesis. -/
theorem fact_6i (W : Submodule F2 Gamma) (hW : Module.finrank F2 W = 2) :
    ∃! φ : GammaDual, φ ≠ 0 ∧ ∀ w ∈ W, φ w = 0 := by
  have hV3 : Module.finrank F2 Gamma = 3 := Gamma.finrank_eq
  have hann : Module.finrank F2 (W.dualAnnihilator : Submodule F2 GammaDual) = 1 := by
    have hadd := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    rw [hW, hV3] at hadd
    omega
  obtain ⟨v, hv_ne, hv_span⟩ :=
    (finrank_eq_one_iff' (K := F2)
      (V := (W.dualAnnihilator : Submodule F2 GammaDual))).mp hann
  refine ⟨(v : GammaDual), ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact hv_ne (Submodule.coe_eq_zero.mp h)
  · exact (Submodule.mem_dualAnnihilator _).mp v.property
  · rintro φ ⟨hφ_ne, hφ_ann⟩
    have hφmem : φ ∈ W.dualAnnihilator := (Submodule.mem_dualAnnihilator _).mpr hφ_ann
    obtain ⟨c, hc⟩ := hv_span ⟨φ, hφmem⟩
    have hc_ne : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hc
      exact hφ_ne (congrArg Subtype.val hc).symm
    have hc1 : c = 1 := (by decide : ∀ x : F2, x ≠ 0 → x = 1) c hc_ne
    rw [hc1, one_smul] at hc
    exact (congrArg Subtype.val hc).symm

/-- `1_{φ ≠ 0} = 1` when `φ ≠ 0`. -/
private lemma nonzeroInd_eq_one {φ : GammaDual} (h : φ ≠ 0) : nonzeroInd φ = 1 := by
  unfold nonzeroInd; exact if_pos h

/-- `1_{φ ≠ 0} = 0` when `φ = 0`. -/
private lemma nonzeroInd_eq_zero {φ : GammaDual} (h : φ = 0) : nonzeroInd φ = 0 := by
  unfold nonzeroInd; exact if_neg (by simp [h])

/-- For two dual vectors each equal to `0` or a fixed nonzero `φ₀`, the `𝔽₂`-sum of their
three indicators (theirs and their sum's) vanishes. -/
private lemma nonzeroInd_add_pair {φ₀ p q : GammaDual} (hφ₀ : φ₀ ≠ 0)
    (hp : p = 0 ∨ p = φ₀) (hq : q = 0 ∨ q = φ₀) :
    nonzeroInd p + nonzeroInd q + nonzeroInd (p + q) = 0 := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rw [hp, hq]
  · rw [nonzeroInd_eq_zero rfl, nonzeroInd_eq_zero (add_zero 0)]; rfl
  · rw [nonzeroInd_eq_zero rfl, nonzeroInd_eq_one hφ₀, nonzeroInd_eq_one (by rwa [zero_add])]
    decide
  · rw [nonzeroInd_eq_one hφ₀, nonzeroInd_eq_zero rfl, nonzeroInd_eq_one (by rwa [add_zero])]
    decide
  · rw [nonzeroInd_eq_one hφ₀, nonzeroInd_eq_zero (gammaDual_add_self φ₀)]
    decide

/-- **Fact 6h (interpretation of `λ`).** *`λ` is the parity of the number of nonzero members
of `{η_a, η_b, η_c}`.*

If `λ = 0`, all three dual vectors vanish on the two-dimensional space `W = ⟨x, y⟩`; by the
uniqueness of Fact 6i each is `0` or the unique nonzero annihilator, and their sum being zero
forces it to occur zero or two times. If `λ = 1`, all three are nonzero. The parity
`#{e ∋ v : η_e ≠ 0}` is written as the `𝔽₂`-sum `Σ_{e ∋ v} 1_{η_e ≠ 0}` over the three
distinct edges at `v`. -/
theorem fact_6h (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (η : β → GammaDual) (h5 : Cond5 G S.flow η)
    (hv : v ∈ V(G)) :
    η (S.ord.edge v 1) (S.flow (S.ord.edge v 0))
      = ∑ᶠ e ∈ G.incidenceSet v, nonzeroInd (η e) := by
  classical
  obtain ⟨hsum, hax, hby, hcz⟩ := fact_6e hV hE hloop hcubic O S hf hnz η h5 hv
  obtain ⟨hzxy, hxne, hyne, hzne, hxyne⟩ :=
    cubic_flow_distinct hV hE hloop hcubic O S.flow hf hnz S.ord hv
  have h6f := fact_6f hV hE hloop hcubic O S hf hnz η h5 hv
  -- `η_c = η_a + η_b` from `η_a + η_b + η_c = 0` in characteristic two.
  have hηc : η (S.ord.edge v 2) = η (S.ord.edge v 0) + η (S.ord.edge v 1) := by
    have h : η (S.ord.edge v 2) + (η (S.ord.edge v 0) + η (S.ord.edge v 1)) = 0 := by
      rw [← hsum]; abel
    have hs2 : (η (S.ord.edge v 0) + η (S.ord.edge v 1))
        + (η (S.ord.edge v 0) + η (S.ord.edge v 1)) = 0 := gammaDual_add_self _
    calc η (S.ord.edge v 2)
        = (η (S.ord.edge v 2) + (η (S.ord.edge v 0) + η (S.ord.edge v 1)))
            + (η (S.ord.edge v 0) + η (S.ord.edge v 1)) := by rw [add_assoc, hs2, add_zero]
      _ = η (S.ord.edge v 0) + η (S.ord.edge v 1) := by rw [h, zero_add]
  -- Expand the RHS over the three incident edges.
  have h01 : S.ord.edge v 0 ≠ S.ord.edge v 1 := S.ord.edge_ne_edge hv (by decide)
  have h02 : S.ord.edge v 0 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have h12 : S.ord.edge v 1 ≠ S.ord.edge v 2 := S.ord.edge_ne_edge hv (by decide)
  have hcoe : ({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Set β)
      = (↑({S.ord.edge v 0, S.ord.edge v 1, S.ord.edge v 2} : Finset β) : Set β) := by simp
  rw [S.incidenceSet_eq_triple hv, hcoe, finsum_mem_coe_finset,
    Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
    Finset.sum_singleton]
  -- Case on `λ = η_b(x) ∈ 𝔽₂`.
  rcases (by decide : ∀ w : F2, w = 0 ∨ w = 1)
      (η (S.ord.edge v 1) (S.flow (S.ord.edge v 0))) with hL | hL
  · -- `λ = 0`: `η_a, η_b` annihilate `W = ⟨x, y⟩`, so each is `0` or the unique annihilator.
    set W : Submodule F2 Gamma :=
      Submodule.span F2 (Set.range ![S.flow (S.ord.edge v 0), S.flow (S.ord.edge v 1)]) with hWdef
    have hli : LinearIndependent F2
        ![S.flow (S.ord.edge v 0), S.flow (S.ord.edge v 1)] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      rcases (by decide : ∀ w : F2, w = 0 ∨ w = 1) s with rfl | rfl <;>
        rcases (by decide : ∀ w : F2, w = 0 ∨ w = 1) t with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · rw [zero_smul, one_smul, zero_add] at hst; exact absurd hst hyne
      · rw [one_smul, zero_smul, add_zero] at hst; exact absurd hst hxne
      · rw [one_smul, one_smul, ← hzxy] at hst; exact absurd hst hzne
    have hWrank : Module.finrank F2 W = 2 := by
      rw [hWdef, finrank_span_eq_card hli]; simp
    have hWann : ∀ φ : GammaDual, φ (S.flow (S.ord.edge v 0)) = 0 →
        φ (S.flow (S.ord.edge v 1)) = 0 → ∀ w ∈ W, φ w = 0 := by
      intro φ hφx hφy w hw
      have hle : W ≤ LinearMap.ker φ := by
        rw [hWdef, Submodule.span_le]
        rintro z ⟨i, rfl⟩
        fin_cases i
        · simpa [LinearMap.mem_ker] using hφx
        · simpa [LinearMap.mem_ker] using hφy
      exact LinearMap.mem_ker.mp (hle hw)
    obtain ⟨φ₀, hφ₀spec, huniq⟩ := fact_6i W hWrank
    have hφ₀ne : φ₀ ≠ 0 := hφ₀spec.1
    -- Package `η_a, η_b ∈ {0, φ₀}`.
    have hηa01 : η (S.ord.edge v 0) = 0 ∨ η (S.ord.edge v 0) = φ₀ := by
      by_cases h0 : η (S.ord.edge v 0) = 0
      · exact Or.inl h0
      · exact Or.inr (huniq _ ⟨h0, hWann _ hax (h6f.trans hL)⟩)
    have hηb01 : η (S.ord.edge v 1) = 0 ∨ η (S.ord.edge v 1) = φ₀ := by
      by_cases h0 : η (S.ord.edge v 1) = 0
      · exact Or.inl h0
      · exact Or.inr (huniq _ ⟨h0, hWann _ hL hby⟩)
    rw [hL, hηc, ← add_assoc]
    exact (nonzeroInd_add_pair hφ₀ne hηa01 hηb01).symm
  · -- `λ = 1`: all three of `η_a, η_b, η_c` are nonzero.
    have hηb_ne : η (S.ord.edge v 1) ≠ 0 := by
      intro h; rw [h] at hL; simp at hL
    have hηa_ne : η (S.ord.edge v 0) ≠ 0 := by
      intro h
      have hval := h6f.trans hL
      rw [h, LinearMap.zero_apply] at hval
      exact one_ne_zero hval.symm
    have hηc_ne : η (S.ord.edge v 2) ≠ 0 := by
      intro h
      have hcx : η (S.ord.edge v 2) (S.flow (S.ord.edge v 0)) = 1 := by
        rw [hηc, LinearMap.add_apply, hax, hL, zero_add]
      rw [h, LinearMap.zero_apply] at hcx
      exact one_ne_zero hcx.symm
    rw [hL, nonzeroInd_eq_one hηa_ne, nonzeroInd_eq_one hηb_ne, nonzeroInd_eq_one hηc_ne]
    decide

/-- **Fact 6h, equation (9).** *This together with (8) gives*

  `Σ_{e ∋ v} η_e(g_{v,e}) = Σ_{e ∋ v} 1_{η_e ≠ 0}`.                          (9)

Immediate from Fact 6g (equation (8)) and the `λ`-parity claim `fact_6h`. -/
theorem fact_6h_eq9 (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (η : β → GammaDual) (h5 : Cond5 G S.flow η)
    (hv : v ∈ V(G)) :
    (∑ᶠ e ∈ G.incidenceSet v, η e (S.g v e))
      = ∑ᶠ e ∈ G.incidenceSet v, nonzeroInd (η e) := by
  rw [fact_6g hV hE hloop hcubic O S hf hnz η h5 hv]
  exact fact_6h hV hE hloop hcubic O S hf hnz η h5 hv

/-! ## Fact 6j — the double count concluding (6) -/

/-- **Fact 6j, step 1.** *For `e = uv`, the definition `d_e = g_{u,e} + g_{v,e}` and linearity
of `η_e` give `η_e(d_e) = η_e(g_{u,e}) + η_e(g_{v,e})`.*

Looplessness is what makes the two ends `u`, `v` of `e` distinct, which is what
`LocalShift.d_eq_add` needs. -/
theorem fact_6j_edge (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (S : LocalShift G) (η : β → GammaDual) (h : G.IsLink e u v) :
    η e (S.d e) = η e (S.g u e) + η e (S.g v e) := by
  have huv : u ≠ v := Graph.isLoopless_iff_forall_isLink_ne.mp hloop e u v h
  rw [S.d_eq_add h huv, map_add]

/-- **Fact 6j, step 2 (the double count).** *Summing over all edges and grouping the two
endpoint terms at each vertex,*

  `Σ_e η_e(d_e) = Σ_v Σ_{e ∋ v} η_e(g_{v,e})`.

This is an exchange of the order of summation over the incident pairs `(v, e)`, needing only
the finiteness of `V(G)` and `E(G)`. -/
theorem fact_6j_double_count (hV : V(G).Finite) (hE : E(G).Finite) (S : LocalShift G)
    (η : β → GammaDual) :
    dualSum G η S.d = ∑ᶠ v ∈ V(G), ∑ᶠ e ∈ G.incidenceSet v, η e (S.g v e) := by
  rw [dualSum]
  have hpt : ∀ e ∈ E(G),
      η e (S.d e) = ∑ᶠ w ∈ {w | G.Inc e w}, η e (S.g w e) := by
    intro e he
    rw [S.d_def]
    exact AddMonoidHom.map_finsum_mem (fun w => S.g w e) (η e).toAddMonoidHom
      (setOf_inc_finite G e)
  rw [finsum_mem_congr rfl hpt,
    incidence_double_sum hV hE (fun e w => η e (S.g w e))]

/-- **Fact 6j, step 3.** *…and (9) gives
`Σ_v Σ_{e ∋ v} η_e(g_{v,e}) = Σ_v Σ_{e ∋ v} 1_{η_e ≠ 0}`.*

Apply equation (9) (`fact_6h_eq9`) at each vertex. -/
theorem fact_6j_eq9_sum (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (η : β → GammaDual) (h5 : Cond5 G S.flow η) :
    (∑ᶠ v ∈ V(G), ∑ᶠ e ∈ G.incidenceSet v, η e (S.g v e))
      = ∑ᶠ v ∈ V(G), ∑ᶠ e ∈ G.incidenceSet v, nonzeroInd (η e) := by
  refine finsum_mem_congr rfl fun v hv => ?_
  exact fact_6h_eq9 hV hE hloop hcubic O S hf hnz η h5 hv

/-- **Fact 6j, step 4.** *Each edge with `η_e ≠ 0` occurs twice in the last sum, once at each
endpoint. Hence it equals `2 Σ_e 1_{η_e ≠ 0} = 0` in `𝔽₂`.*

Looplessness is what makes "once at each endpoint" mean *twice*: a loop would be counted once
only.  The conclusion records both halves of the sentence — the value `2 • Σ_e 1_{η_e ≠ 0}`
and its vanishing in `𝔽₂`. -/
theorem fact_6j_two_mul (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (η : β → GammaDual) :
    (∑ᶠ v ∈ V(G), ∑ᶠ e ∈ G.incidenceSet v, nonzeroInd (η e))
        = (2 : ℕ) • (∑ᶠ e ∈ E(G), nonzeroInd (η e)) ∧
      ((2 : ℕ) • (∑ᶠ e ∈ E(G), nonzeroInd (η e)) : F2) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [← incidence_double_sum hV hE (fun e _ => nonzeroInd (η e))]
    have hinner : ∀ e ∈ E(G),
        (∑ᶠ w ∈ {w | G.Inc e w}, nonzeroInd (η e))
          = nonzeroInd (η e) + nonzeroInd (η e) := by
      intro e he
      obtain ⟨u, v, hl⟩ := G.exists_isLink_of_mem_edgeSet he
      have huv : u ≠ v := Graph.isLoopless_iff_forall_isLink_ne.mp hloop e u v hl
      rw [LocalShift.setOf_inc_eq_pair hl, finsum_mem_pair huv]
    rw [finsum_mem_congr rfl hinner, finsum_mem_add_distrib hE, two_nsmul]
  · rw [two_nsmul]
    exact CharTwo.add_self_eq_zero _

/-- **Fact 6j — equation (6).** *This proves (6):*

  `Σ_e η_e(d_e) = 0`.                                                        (6)

The chain is `fact_6j_double_count`, then `fact_6j_eq9_sum` (i.e. equation (9)), then
`fact_6j_two_mul`. -/
theorem fact_6j (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (η : β → GammaDual) (h5 : Cond5 G S.flow η) :
    dualSum G η S.d = 0 := by
  rw [fact_6j_double_count hV hE S η,
    fact_6j_eq9_sum hV hE hloop hcubic O S hf hnz η h5,
    (fact_6j_two_mul hV hE hloop η).1, (fact_6j_two_mul hV hE hloop η).2]

/-! ## Lemma 2.2 -/

/-- **Lemma 2.2.** *The system (4) has a solution.*

That is, for a finite loopless cubic multigraph `G` carrying a nowhere-zero `Γ`-flow `f` and a
local ordering — packaged as a `LocalShift G` with `S.flow = f` — the system

  `t_u + t_v + ε_e f(e) = d_e`   (`e = uv`),      `d_e = g_{u,e} + g_{v,e}`,   (4)

is solvable for `t : V(G) → Γ` and `ε : E(G) → 𝔽₂`.  By the duality criterion (Fact 6a) this
follows from equation (6) (`fact_6j`) via Fact 6d. -/
theorem lemma_2_2 (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) :
    (SystemL.ofLocalShift S).HasSolution := by
  apply fact_6d hV hE (SystemL.ofLocalShift S)
  intro η h5
  rw [SystemL.ofLocalShift_flow] at h5
  show dualPairing η (SystemL.ofLocalShift S).rhsOn = 0
  rw [SystemL.rhsOn, SystemL.ofLocalShift_rhs, dualPairing_restrict]
  exact fact_6j hV hE hloop hcubic O S hf hnz η h5

end Workspace.Facts.Duality
