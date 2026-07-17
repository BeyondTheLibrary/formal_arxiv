import Workspace.PriorWorkProofs.Tutte.Basic

/-!
# Tutte's group-flow theorem — Part I (deletion–contraction and group independence)

This file builds on `Workspace.PriorWorkProofs.Tutte.Basic` to prove:

* **Loop recurrence** (`flowCount_loop`): for a loop `e` at `x`,
  `flowCount G O Γ = (Nat.card Γ − 1) · flowCount (G−e) … Γ`.
* **Group independence, folded route** (`flowCount_eq_of_card_eq`): by strong induction on
  `E(G).ncard`, `Nat.card Γ = Nat.card Γ′ ⇒ flowCount G O Γ = flowCount G O′ Γ′`.
* **Corollary I.4** (`exists_flow_iff_of_card_eq`, `exists_flow_iff_zmod`): existence of a
  nowhere-zero `Γ`-flow depends only on `|Γ|`; in particular a nowhere-zero `A`-flow exists iff
  a nowhere-zero `(ZMod k)`-flow exists when `Nat.card A = k`.

The non-loop deletion–contraction recurrence is `contract_flow_correspondence` from `Basic`.
-/

open Graph Workspace.Types.Orientation
open scoped Graph

namespace Workspace.PriorWorkProofs.Tutte

variable {α β : Type*} {G : Graph α β} {O : Orientation G}

/-! ## Loop recurrence (Lemma I.1.2) -/

section Loop

variable {Γ : Type*} [AddCommGroup Γ]

/-- Updating a map at the deleted edge `e` does not affect being a flow of `G − e`, since the
edge `e` is not in `E(G − e)` and so never appears in any conservation sum. -/
theorem isFlow_deleteEdge_update_iff [DecidableEq β] (e : β) (g : β → Γ) (c : Γ) :
    (deleteEdge G e).IsFlow (deleteEdgeOrientation O e) (Function.update g e c) ↔
      (deleteEdge G e).IsFlow (deleteEdgeOrientation O e) g := by
  have hupd : ∀ (t : β → α) (v : α),
      (∑ᶠ e' ∈ {e' ∈ E(deleteEdge G e) | t e' = v}, Function.update g e c e')
        = ∑ᶠ e' ∈ {e' ∈ E(deleteEdge G e) | t e' = v}, g e' := by
    intro t v
    apply finsum_mem_congr rfl
    intro e' he'
    have : e' ∈ E(deleteEdge G e) := he'.1
    rw [edgeSet_deleteEdge] at this
    exact Function.update_of_ne this.2 _ _
  unfold Graph.IsFlow Graph.outSum Graph.inSum Graph.outEdgeSet Graph.inEdgeSet
  constructor <;> intro h v hv <;>
    · have := h v hv
      simpa only [hupd] using this

/-- **Loop flow-equivalence.** If `e` is a loop at `x`, then a map `f` is a flow of `G` iff it is
a flow of `G − e`: the loop contributes `f e` to both the out- and in-sums at `x`, cancelling. -/
theorem isFlow_deleteEdge_loop_iff [DecidableEq α] (hE : E(G).Finite) {e : β} {x : α}
    (hloop : G.IsLoopAt e x) (f : β → Γ) :
    (deleteEdge G e).IsFlow (deleteEdgeOrientation O e) f ↔ G.IsFlow O f := by
  classical
  have hE' : E(deleteEdge G e).Finite := by rw [edgeSet_deleteEdge]; exact hE.diff
  have hsub : E(deleteEdge G e) ⊆ E(G) := by rw [edgeSet_deleteEdge]; exact Set.diff_subset
  have htail : O.tail e = x := O.tail_eq_of_isLoopAt hloop
  have hhead : O.head e = x := O.head_eq_of_isLoopAt hloop
  have heG : e ∈ E(G) := hloop.edge_mem
  have hsetdiff : hE'.toFinset = hE.toFinset \ {e} := by
    ext a
    simp only [Set.Finite.mem_toFinset, edgeSet_deleteEdge, Set.mem_diff, Set.mem_singleton_iff,
      Finset.mem_sdiff, Finset.mem_singleton]
  rw [Graph.isFlow_iff_finset_sum hE', Graph.isFlow_iff_finset_sum hE]
  have hVeq : V(deleteEdge G e) = V(G) := vertexSet_deleteEdge e
  rw [hVeq]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  -- Tail/head functions agree with `O`.
  have htaileq : ∀ e', (deleteEdgeOrientation O e).tail e' = O.tail e' := fun _ => rfl
  have hheadeq : ∀ e', (deleteEdgeOrientation O e).head e' = O.head e' := fun _ => rfl
  simp only [htaileq, hheadeq, hsetdiff]
  -- Split each `G`-sum: `∑ over (s), if p then f = (if p e then f e else 0) + ∑ over (s\{e})`.
  have key : ∀ (t : β → α),
      (∑ e' ∈ hE.toFinset with t e' = v, f e')
        = (if t e = v then f e else 0) + ∑ e' ∈ hE.toFinset \ {e} with t e' = v, f e' := by
    intro t
    rw [Finset.sum_filter, Finset.sum_filter]
    have he_mem : e ∈ hE.toFinset := by rw [Set.Finite.mem_toFinset]; exact heG
    rw [← Finset.sum_erase_add _ _ he_mem, Finset.erase_eq, add_comm]
  rw [key O.tail, key O.head, htail, hhead]
  constructor
  · intro h; rw [h]
  · intro h; exact add_left_cancel h

/-- The number of nonzero elements of a finite additive group is `Nat.card Γ − 1`. -/
theorem card_ne_zero (Γ : Type*) [AddGroup Γ] [Finite Γ] :
    Nat.card {γ : Γ // γ ≠ (0 : Γ)} = Nat.card Γ - 1 := by
  classical
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

/-- **Loop recurrence (Lemma I.1.2).** For a loop `e` at `x`,
`flowCount G O Γ = (Nat.card Γ − 1) · flowCount (G − e) … Γ`.

The flows of `G` are in bijection with pairs `(g, γ)` where `g` is a flow of `G − e` and
`γ ≠ 0` is the free value on the loop. -/
theorem flowCount_loop [DecidableEq α] [DecidableEq β] [Finite Γ]
    (hE : E(G).Finite) {e : β} {x : α} (hloop : G.IsLoopAt e x) :
    flowCount G O Γ
      = (Nat.card Γ - 1) * flowCount (deleteEdge G e) (deleteEdgeOrientation O e) Γ := by
  classical
  have heG : e ∈ E(G) := hloop.edge_mem
  set Gd := deleteEdge G e
  set Od := deleteEdgeOrientation O e
  have hEdmem : ∀ e', e' ∈ E(Gd) ↔ e' ∈ E(G) ∧ e' ≠ e := by
    intro e'; simp [Gd]
  -- membership: forward first component
  have hfwd1 : ∀ F : ↥(flowSet G O Γ), Function.update (F : β → Γ) e 0 ∈ flowSet Gd Od Γ := by
    rintro ⟨f, hflow, hnz, hoff⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [isFlow_deleteEdge_update_iff]
      exact ((isFlow_deleteEdge_loop_iff hE hloop f).mpr hflow)
    · intro e' he'
      rw [hEdmem] at he'
      rw [Function.update_of_ne he'.2]
      exact hnz e' he'.1
    · intro e' he'
      rw [hEdmem, not_and_or, not_not] at he'
      by_cases hee : e' = e
      · rw [hee, Function.update_self]
      · rw [Function.update_of_ne hee]
        exact hoff e' (by tauto)
  -- membership: inverse
  have hinv : ∀ (P : ↥(flowSet Gd Od Γ) × {γ : Γ // γ ≠ (0:Γ)}),
      Function.update (P.1 : β → Γ) e (P.2 : Γ) ∈ flowSet G O Γ := by
    rintro ⟨⟨g, hgflow, hgnz, hgoff⟩, ⟨γ, hγ⟩⟩
    have hge : g e = 0 := hgoff e (by rw [hEdmem]; tauto)
    refine ⟨?_, ?_, ?_⟩
    · rw [← isFlow_deleteEdge_loop_iff hE hloop, isFlow_deleteEdge_update_iff]
      exact hgflow
    · intro e' he'
      by_cases hee : e' = e
      · rw [hee, Function.update_self]; exact hγ
      · rw [Function.update_of_ne hee]
        exact hgnz e' (by rw [hEdmem]; exact ⟨he', hee⟩)
    · intro e' he'
      have hee : e' ≠ e := by rintro rfl; exact he' heG
      rw [Function.update_of_ne hee]
      exact hgoff e' (by rw [hEdmem]; tauto)
  have hbij : Nat.card ↥(flowSet G O Γ)
      = Nat.card ↥(flowSet Gd Od Γ) * Nat.card {γ : Γ // γ ≠ (0:Γ)} := by
    rw [← Nat.card_prod]
    apply Nat.card_congr
    exact {
      toFun := fun F => (⟨Function.update (F : β → Γ) e 0, hfwd1 F⟩, ⟨(F : β → Γ) e,
        (F.2.2.1 e heG)⟩)
      invFun := fun P => ⟨Function.update (P.1 : β → Γ) e (P.2 : Γ), hinv P⟩
      left_inv := by
        rintro ⟨f, hf⟩
        apply Subtype.ext
        simp [Function.update_idem]
      right_inv := by
        rintro ⟨⟨g, hgflow, hgnz, hgoff⟩, ⟨γ, hγ⟩⟩
        have hge : g e = 0 := hgoff e (by rw [hEdmem]; tauto)
        apply Prod.ext
        · apply Subtype.ext
          simp [Function.update_idem, hge]
        · apply Subtype.ext
          simp }
  rw [flowCount, flowCount, hbij, card_ne_zero, mul_comm]

end Loop

/-! ## Group independence, folded route (Theorem I.3 / Corollary I.4) -/

section Independence

/-- Being a flow depends only on the values of the map on `E(G)`. -/
theorem isFlow_congr_on_edgeSet {Γ : Type*} [AddCommGroup Γ] {f g : β → Γ}
    (h : ∀ e ∈ E(G), f e = g e) : G.IsFlow O f ↔ G.IsFlow O g := by
  have hsum : ∀ (t : β → α) (v : α),
      (∑ᶠ e ∈ {e ∈ E(G) | t e = v}, f e) = ∑ᶠ e ∈ {e ∈ E(G) | t e = v}, g e := by
    intro t v
    exact finsum_mem_congr rfl fun e he => h e he.1
  unfold Graph.IsFlow Graph.outSum Graph.inSum Graph.outEdgeSet Graph.inEdgeSet
  constructor <;> intro hh v hv <;> · have := hh v hv; simpa only [hsum] using this

/-- Existence of a nowhere-zero `Γ`-flow is equivalent to the (normalized) flow set being
nonempty: any flow can be normalized to vanish off `E(G)` without changing its behaviour. -/
theorem flowSet_nonempty_iff {Γ : Type*} [AddCommGroup Γ] :
    (flowSet G O Γ).Nonempty ↔ ∃ f : β → Γ, G.IsFlow O f ∧ G.IsNowhereZero f := by
  classical
  constructor
  · rintro ⟨f, hflow, hnz, -⟩
    exact ⟨f, hflow, hnz⟩
  · rintro ⟨f, hflow, hnz⟩
    refine ⟨E(G).indicator f, ?_, ?_, ?_⟩
    · rw [isFlow_congr_on_edgeSet (f := E(G).indicator f) (g := f)]
      · exact hflow
      · intro e he; exact Set.indicator_of_mem he f
    · intro e he
      rw [Set.indicator_of_mem he f]; exact hnz e he
    · intro e he; exact Set.indicator_of_notMem he f

/-- Positivity of the flow count is equivalent to the existence of a nowhere-zero flow. -/
theorem flowCount_pos_iff {Γ : Type*} [AddCommGroup Γ] [Finite Γ] (hE : E(G).Finite) :
    0 < flowCount G O Γ ↔ ∃ f : β → Γ, G.IsFlow O f ∧ G.IsNowhereZero f := by
  rw [← flowSet_nonempty_iff]
  have hfin : (flowSet G O Γ).Finite := flowSet_finite hE
  rw [flowCount]
  constructor
  · intro h
    have : Nonempty ↥(flowSet G O Γ) := (Nat.card_pos_iff.mp h).1
    exact Set.nonempty_coe_sort.mp this
  · intro h
    haveI : Finite ↥(flowSet G O Γ) := hfin.to_subtype
    haveI : Nonempty ↥(flowSet G O Γ) := Set.nonempty_coe_sort.mpr h
    exact Nat.card_pos

/-- **Group independence, auxiliary form.** Strong induction on the number of edges: if
`Nat.card Γ = Nat.card Γ′` then the flow counts agree, for any orientations. -/
private theorem flowCount_eq_aux [DecidableEq α] :
    ∀ (n : ℕ) {G : Graph α β} (_hE : E(G).Finite) (_hn : E(G).ncard = n)
      (O O' : Orientation G) {Γ Γ' : Type*} [AddCommGroup Γ] [Finite Γ]
      [AddCommGroup Γ'] [Finite Γ'] (_hc : Nat.card Γ = Nat.card Γ'),
      flowCount G O Γ = flowCount G O' Γ' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro G hE hn O O' Γ Γ' _ _ _ _ hc
    classical
    rcases Set.eq_empty_or_nonempty E(G) with hEmpty | ⟨e, heG⟩
    · rw [flowCount_empty hEmpty, flowCount_empty hEmpty]
    · obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet heG
      by_cases hloop : x = y
      · subst hloop
        have hloopAt : G.IsLoopAt e x := hxy
        have hlt : E(deleteEdge G e).ncard < n := by
          rw [edgeSet_deleteEdge, ← hn]
          exact Set.ncard_diff_singleton_lt_of_mem heG hE
        have hEd : E(deleteEdge G e).Finite := by rw [edgeSet_deleteEdge]; exact hE.diff
        rw [flowCount_loop hE hloopAt, flowCount_loop hE hloopAt, hc]
        congr 1
        exact IH (E(deleteEdge G e).ncard) hlt hEd rfl
          (deleteEdgeOrientation O e) (deleteEdgeOrientation O' e) hc
      · have hlt1 : E(contract G e x y).ncard < n := by
          rw [edgeSet_contract, ← hn]
          exact Set.ncard_diff_singleton_lt_of_mem heG hE
        have hlt2 : E(deleteEdge G e).ncard < n := by
          rw [edgeSet_deleteEdge, ← hn]
          exact Set.ncard_diff_singleton_lt_of_mem heG hE
        have hEc : E(contract G e x y).Finite := by rw [edgeSet_contract]; exact hE.diff
        have hEd : E(deleteEdge G e).Finite := by rw [edgeSet_deleteEdge]; exact hE.diff
        have hrecΓ := contract_flow_correspondence (O := O) (Γ := Γ) hE e x y hxy hloop
        have hrecΓ' := contract_flow_correspondence (O := O') (Γ := Γ') hE e x y hxy hloop
        have ih_c : flowCount (contract G e x y) (contractOrientation O e x y) Γ
                  = flowCount (contract G e x y) (contractOrientation O' e x y) Γ' :=
          IH (E(contract G e x y).ncard) hlt1 hEc rfl
            (contractOrientation O e x y) (contractOrientation O' e x y) hc
        have ih_d : flowCount (deleteEdge G e) (deleteEdgeOrientation O e) Γ
                  = flowCount (deleteEdge G e) (deleteEdgeOrientation O' e) Γ' :=
          IH (E(deleteEdge G e).ncard) hlt2 hEd rfl
            (deleteEdgeOrientation O e) (deleteEdgeOrientation O' e) hc
        have key : flowCount G O Γ + flowCount (deleteEdge G e) (deleteEdgeOrientation O e) Γ
                 = flowCount G O' Γ' + flowCount (deleteEdge G e) (deleteEdgeOrientation O e) Γ := by
          rw [← hrecΓ, ih_c, hrecΓ', ih_d]
        exact Nat.add_right_cancel key

/-- **Group independence (folded route).** If `Nat.card Γ = Nat.card Γ′`, then the flow counts
of `G` agree, for any orientations `O, O′`. Proved by strong induction on `E(G).ncard`. -/
theorem flowCount_eq_of_card_eq [DecidableEq α] (hE : E(G).Finite) (O O' : Orientation G)
    {Γ Γ' : Type*} [AddCommGroup Γ] [Finite Γ] [AddCommGroup Γ'] [Finite Γ']
    (hc : Nat.card Γ = Nat.card Γ') : flowCount G O Γ = flowCount G O' Γ' :=
  flowCount_eq_aux E(G).ncard hE rfl O O' hc

/-- **Corollary I.4.** Existence of a nowhere-zero `Γ`-flow depends only on `|Γ|`. -/
theorem exists_flow_iff_of_card_eq [DecidableEq α] (hE : E(G).Finite) (O O' : Orientation G)
    {Γ Γ' : Type*} [AddCommGroup Γ] [Finite Γ] [AddCommGroup Γ'] [Finite Γ']
    (hc : Nat.card Γ = Nat.card Γ') :
    (∃ f : β → Γ, G.IsFlow O f ∧ G.IsNowhereZero f)
      ↔ (∃ f : β → Γ', G.IsFlow O' f ∧ G.IsNowhereZero f) := by
  rw [← flowCount_pos_iff hE, ← flowCount_pos_iff hE, flowCount_eq_of_card_eq hE O O' hc]

/-- **Corollary I.4, `ZMod k` bridge.** With `Nat.card A = k`, a nowhere-zero `A`-flow exists iff
a nowhere-zero `(ZMod k)`-flow exists (w.r.t. the same orientation `O`). This is the exact bridge
the final assembly consumes. -/
theorem exists_flow_iff_zmod [DecidableEq α] {A : Type*} [AddCommGroup A] [Finite A] {k : ℕ}
    [NeZero k] (hE : E(G).Finite) (O : Orientation G) (hA : Nat.card A = k) :
    (∃ f : β → A, G.IsFlow O f ∧ G.IsNowhereZero f)
      ↔ (∃ f : β → ZMod k, G.IsFlow O f ∧ G.IsNowhereZero f) := by
  have hcard : Nat.card A = Nat.card (ZMod k) := by rw [hA, Nat.card_zmod]
  exact exists_flow_iff_of_card_eq hE O O hcard

end Independence

end Workspace.PriorWorkProofs.Tutte
