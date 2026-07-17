import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.MultigraphBasic
import Workspace.Types.Orientation
import Workspace.Types.Flow

/-!
# Even subgraphs and the assembly of a nowhere-zero `Γ`-flow (§3.1, §3.6 step 4-5, §3.8)

The `𝔽₂`-indicator of an edge set `H` is a `ZMod 2`-flow of `G` iff `H` is an even subgraph
(`indicator_isFlow_iff`), via the characteristic-two flow criterion `charTwo_flow_iff_endSum_zero`.
Assembled with `three_even_subgraphs_cover_gamma_flow`: three even subgraphs covering `E(G)` yield
a nowhere-zero `Γ`-flow (`Γ = 𝔽₂³`).
-/

open Set
open scoped Graph
open Workspace.Types.Gamma
open Workspace.Types.Orientation

namespace Workspace.PriorWorkProofs.EightFlow

open scoped Classical

variable {α β : Type*} {G : Graph α β} {u v : α} {e : β} {H : Set β}

/-! ## The characteristic-two flow criterion -/

/-- **Characteristic-two flow criterion.** For a group `A` in which every element is its own
negative (`a + a = 0`), a map `f : β → A` is an `A`-flow with respect to an orientation `O` iff
for every vertex `v` the sum of `f` over the edge-ends at `v` — a loop counted **twice** —
vanishes. This is the group-general version of
`Workspace.Facts.Construction.gamma_flow_iff_endSum_zero`; the orientation drops out because in
characteristic two `x = y ↔ x + y = 0`. -/
theorem charTwo_flow_iff_endSum_zero {A : Type*} [AddCommGroup A] (hchar : ∀ a : A, a + a = 0)
    (hE : E(G).Finite) (O : Orientation G) (f : β → A) :
    G.IsFlow O f ↔
      ∀ v ∈ V(G),
        (∑ᶠ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • f e) = 0 := by
  classical
  have eq_iff : ∀ a b : A, (a = b) ↔ (a + b = 0) := by
    intro a b
    constructor
    · rintro rfl; exact hchar _
    · intro h
      have hh : a + b + b = b := by rw [h, zero_add]
      rwa [add_assoc, hchar, add_zero] at hh
  rw [Graph.isFlow_iff_finset_sum hE]
  refine forall_congr' (fun v => ?_)
  refine imp_congr_right (fun hv => ?_)
  set s := hE.toFinset with hs
  have hset : G.incidenceSet v = (↑(s.filter (fun e => G.Inc e v)) : Set β) := by
    ext e
    simp only [Graph.mem_incidenceSet, Finset.coe_filter, Set.mem_setOf_eq,
      Set.Finite.mem_toFinset, hs]
    exact ⟨fun h => ⟨h.edge_mem, h⟩, fun h => h.2⟩
  rw [hset, finsum_mem_coe_finset]
  have key : (∑ e ∈ s.filter (fun e => G.Inc e v),
        (if G.IsLoopAt e v then (2 : ℕ) else 1) • f e)
      = (∑ e ∈ s.filter (fun e => O.tail e = v), f e)
        + (∑ e ∈ s.filter (fun e => O.head e = v), f e) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have heE : e ∈ E(G) := by rw [hs, Set.Finite.mem_toFinset] at he; exact he
    have hinc : G.Inc e v ↔ O.tail e = v ∨ O.head e = v := by
      rw [O.inc_iff heE]; exact or_congr eq_comm eq_comm
    have hloop : G.IsLoopAt e v ↔ O.tail e = v ∧ O.head e = v := by
      constructor
      · intro h; exact ⟨O.tail_eq_of_isLoopAt h, O.head_eq_of_isLoopAt h⟩
      · rintro ⟨h1, h2⟩
        have hlink := O.isLink_tail_head heE
        rw [h1, h2] at hlink
        exact hlink
    by_cases h1 : O.tail e = v <;> by_cases h2 : O.head e = v <;>
      simp [hinc, hloop, h1, h2, two_nsmul, one_nsmul, two_mul]
  rw [key, eq_iff]

/-- The `ℤ₂` specialisation of `charTwo_flow_iff_endSum_zero`. -/
theorem zmod2_flow_iff_endSum_zero (hE : E(G).Finite) (O : Orientation G) (f : β → ZMod 2) :
    G.IsFlow O f ↔
      ∀ v ∈ V(G),
        (∑ᶠ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • f e) = 0 := by
  classical
  exact charTwo_flow_iff_endSum_zero (fun a => CharTwo.add_self_eq_zero a) hE O f

/-! ## Even subgraphs -/

/-- The **degree of `v` inside the edge set `H`**: the number of edge-ends at `v` that belong to
`H`, a loop counted **twice**. This mirrors `Graph.degree` restricted to `H`. -/
noncomputable def degreeWithin (G : Graph α β) (H : Set β) (v : α) : ℕ :=
  (G.incidenceSet v ∩ H).ncard + (G.loopSet v ∩ H).ncard

/-- `H` is an **even subgraph** of `G` if every vertex of `G` has even degree inside `H`
(loops counted twice). Equivalently (over `ℤ₂`) `H` is a cycle in the algebraic sense: an
element of the cycle space over `GF(2)`. -/
def IsEvenSubgraph (G : Graph α β) (H : Set β) : Prop :=
  ∀ v ∈ V(G), Even (degreeWithin G H v)

/-- The `𝔽₂`-**indicator** of an edge set `H`: the map sending edges of `H` to `1 : ZMod 2` and
everything else to `0`. -/
noncomputable def indicator (H : Set β) : β → ZMod 2 := H.indicator (fun _ => 1)

@[simp] lemma indicator_apply (H : Set β) (e : β) :
    indicator H e = if e ∈ H then 1 else 0 := by
  rw [indicator, Set.indicator_apply]

/-! ### The `endSum` of an indicator equals the within-degree -/

/-- At each vertex `v` the characteristic-two edge-end sum of the indicator of `H` equals the
`ℤ₂`-reduction of `degreeWithin G H v`: loops (which count twice) contribute `2 • 1 = 0`, so only
the parity of the number of `H`-edges at `v` survives. -/
theorem indicator_endSum_eq (hE : E(G).Finite) (H : Set β) (v : α) :
    (∑ᶠ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • indicator H e)
      = ((degreeWithin G H v : ℕ) : ZMod 2) := by
  classical
  have hIsub : G.incidenceSet v ⊆ E(G) := by
    intro e he; rw [Graph.mem_incidenceSet] at he; exact he.edge_mem
  have hI : (G.incidenceSet v).Finite := hE.subset hIsub
  -- turn the finsum into a finset sum
  rw [show G.incidenceSet v = (↑hI.toFinset : Set β) from hI.coe_toFinset.symm,
    finsum_mem_coe_finset]
  -- each term is the ℤ₂-cast of a natural-number multiplicity
  have hterm : ∀ e ∈ hI.toFinset,
      (if G.IsLoopAt e v then (2 : ℕ) else 1) • indicator H e
        = (((if e ∈ H then (if G.IsLoopAt e v then (2 : ℕ) else 1) else 0) : ℕ) : ZMod 2) := by
    intro e _
    by_cases hH : e ∈ H
    · simp only [indicator_apply, hH, if_true]
      by_cases hl : G.IsLoopAt e v <;> simp [hl, nsmul_eq_mul]
    · simp [indicator_apply, hH]
  rw [Finset.sum_congr rfl hterm, ← Nat.cast_sum]
  congr 1
  -- the natural-number sum equals the within-degree
  unfold degreeWithin
  -- split the multiplicity  (2 if loop else 1)  as  1 + (1 if loop)
  have hsplit : ∀ e ∈ hI.toFinset,
      (if e ∈ H then (if G.IsLoopAt e v then (2 : ℕ) else 1) else 0)
        = (if e ∈ H then 1 else 0) + (if (e ∈ H ∧ G.IsLoopAt e v) then 1 else 0) := by
    intro e _
    by_cases hH : e ∈ H <;> by_cases hl : G.IsLoopAt e v <;> simp [hH, hl]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  -- identify the two Finset.filter cards with the two ncards
  have hInc : (↑(hI.toFinset.filter (fun e => e ∈ H)) : Set β) = G.incidenceSet v ∩ H := by
    ext e
    simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff]
  have hLoop : (↑(hI.toFinset.filter (fun e => e ∈ H ∧ G.IsLoopAt e v)) : Set β)
      = G.loopSet v ∩ H := by
    ext e
    simp only [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      Graph.mem_loopSet]
    constructor
    · rintro ⟨hinc, hH, hl⟩; exact ⟨hl, hH⟩
    · rintro ⟨hl, hH⟩
      exact ⟨by rw [Graph.mem_incidenceSet]; exact hl.inc, hH, hl⟩
  simp only [Nat.cast_id]
  rw [← ncard_coe_finset, ← ncard_coe_finset, hInc, hLoop]

/-- **`ℤ₂`-flow ⇔ even subgraph.** The indicator of `H` is a `ZMod 2`-flow of `G` iff `H` is an
even subgraph. -/
theorem indicator_isFlow_iff (hE : E(G).Finite) (O : Orientation G) :
    G.IsFlow O (indicator H) ↔ IsEvenSubgraph G H := by
  rw [zmod2_flow_iff_endSum_zero hE]
  unfold IsEvenSubgraph
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [indicator_endSum_eq hE, ZMod.natCast_eq_zero_iff, ← even_iff_two_dvd]

/-- Even ⟹ flow: the indicator of an even subgraph is a `ℤ₂`-flow. -/
theorem IsEvenSubgraph.indicator_isFlow (hE : E(G).Finite) (O : Orientation G)
    (h : IsEvenSubgraph G H) : G.IsFlow O (indicator H) :=
  (indicator_isFlow_iff hE O).mpr h

/-- Flow ⟹ even: the support (over `E(G)`) of a `ℤ₂`-flow is an even subgraph. Here the flow `f`
equals the indicator of its support, so the biconditional applies. -/
theorem IsFlow.support_isEvenSubgraph (hE : E(G).Finite) (O : Orientation G) {f : β → ZMod 2}
    (hf : G.IsFlow O f) : IsEvenSubgraph G {e | f e = 1} := by
  have hfeq : f = indicator {e | f e = 1} := by
    funext e
    simp only [indicator_apply, Set.mem_setOf_eq]
    by_cases h : f e = 1
    · simp [h]
    · simp only [h, if_false]
      exact (by decide : ∀ x : ZMod 2, x ≠ 1 → x = 0) (f e) h
  rw [hfeq] at hf
  exact (indicator_isFlow_iff hE O).mp hf

/-! ## The assembly: three even covers give a nowhere-zero `Γ`-flow -/

/-- **A `Π`-valued map is a flow iff every coordinate is.** Being a flow is a coordinatewise
condition: `f : β → (ι → A)` is a flow iff each `fun e => f e i` is. This is what lets a
`Γ = 𝔽₂³`-flow be read as a triple of `ℤ₂`-flows. -/
theorem isFlow_pi_iff {ι : Type*} {A : Type*} [AddCommGroup A]
    (hE : E(G).Finite) (O : Orientation G) (f : β → (ι → A)) :
    G.IsFlow O f ↔ ∀ i, G.IsFlow O (fun e => f e i) := by
  classical
  simp only [Graph.isFlow_iff_finset_sum hE]
  constructor
  · intro h i v hv
    have h1 := congrFun (h v hv) i
    simpa only [Finset.sum_apply] using h1
  · intro h v hv
    funext i
    have h1 := h i v hv
    simpa only [Finset.sum_apply] using h1

/-- **The payoff (Prop. 5 steps 4–5, Cor. 8).** If three even subgraphs `H₁, H₂, H₃` cover the
edge set of `G`, then `f := fun e => ![𝟙_{H₁} e, 𝟙_{H₂} e, 𝟙_{H₃} e] : β → Γ` is a
**nowhere-zero `Γ`-flow**: it is a flow because each coordinate is the indicator of an even
subgraph (a `ℤ₂`-flow), and it is nowhere-zero because every edge lies in some `Hᵢ`, making the
corresponding coordinate `1 ≠ 0`.

This is the elementary "cover by three even subgraphs ⟹ nowhere-zero `ℤ₂³`-flow" implication;
producing the three even subgraphs for a bridgeless `G` is the job of `ThreeEvenCover.lean`. -/
theorem three_even_subgraphs_cover_gamma_flow (hE : E(G).Finite) (O : Orientation G)
    {H₁ H₂ H₃ : Set β} (h₁ : IsEvenSubgraph G H₁) (h₂ : IsEvenSubgraph G H₂)
    (h₃ : IsEvenSubgraph G H₃) (hcov : E(G) ⊆ H₁ ∪ H₂ ∪ H₃) :
    ∃ f : β → Gamma, G.IsFlow O f ∧ G.IsNowhereZero f := by
  classical
  refine ⟨fun e => ![indicator H₁ e, indicator H₂ e, indicator H₃ e], ?_, ?_⟩
  · -- flow: coordinatewise, each is the indicator of an even subgraph
    rw [isFlow_pi_iff hE]
    intro i
    fin_cases i
    · simpa using h₁.indicator_isFlow hE O
    · simpa using h₂.indicator_isFlow hE O
    · simpa using h₃.indicator_isFlow hE O
  · -- nowhere-zero: every edge is covered, so some coordinate is `1`
    intro e he
    rcases hcov he with (h | h) | h
    · intro hcon
      have := congrFun hcon 0
      simp only [Matrix.cons_val_zero, indicator_apply, h, if_true] at this
      exact one_ne_zero this
    · intro hcon
      have := congrFun hcon 1
      simp only [Matrix.cons_val_one, Matrix.head_cons, indicator_apply, h, if_true] at this
      exact one_ne_zero this
    · intro hcon
      have := congrFun hcon 2
      simp only [Matrix.cons_val, indicator_apply, h, if_true] at this
      exact one_ne_zero this

end Workspace.PriorWorkProofs.EightFlow
