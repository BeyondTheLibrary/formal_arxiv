import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.MultigraphBasic
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.Types.LocalOrdering
import Workspace.Types.LocalShift
import Workspace.Types.TwoElementAssignment

/-!
# Characteristic-two flows (§2) and the construction of the sets `P_e` (§5)

The facts of *"A Proof of the Cycle Double Cover Conjecture"* living in §2 (flows over
`Γ = 𝔽₂³`) and §5 (the construction of the palettes `P_e`).

For §2, being a `Γ`-flow is equivalent to the vanishing, at each vertex `v`, of the sum of
`f(e)` over the edge-*ends* at `v` — a loop counts twice, written literally as the scalar
`(if G.IsLoopAt e v then (2 : ℕ) else 1) • f e`, so the `if` is load-bearing. At a loopless
cubic vertex with incident edges `a, b, c` this reads `f(a) + f(b) + f(c) = 0`.

For §5 (`G` loopless cubic, `f` a nowhere-zero `Γ`-flow), the paper's local data — the
ordering `a, b, c` at each vertex, the shift `g_{v,e}` of (2), and `d_e = g_{u,e} + g_{v,e}` —
is packaged by `LocalShift G`, with derived `S.g` and `S.d`; `x, y, z` are the flow values at
`S.ord.edge v 0/1/2`. The local set of (3) at `(v, e, t)` is `{t + g_{v,e}, t + g_{v,e} + f(e)}`,
spelled out inline everywhere below.

Every statement about a graph carries both `V(G).Finite` and `E(G).Finite`, both load-bearing
on this file's `finsum`/`ncard`-based definitions (`fact_5b` is pure `𝔽₂` linear algebra and
carries neither).
-/

open Set

open scoped Graph

open Workspace.Types.Gamma
open Workspace.Types.Orientation
open Workspace.Types.LocalOrdering
open Workspace.Types.LocalShift

namespace Workspace.Facts.Construction

variable {α β : Type*} {G : Graph α β} {e : β} {u v : α}

/-- From `t = t + w` in an additive cancellative monoid, `w = 0`. -/
private lemma add_right_eq_zero_of_self_eq {t w : Gamma} (h : t = t + w) : w = 0 := by
  have hh : t + w = t + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel hh

/-- **Characteristic two.** In `Γ`, `A = B` iff `A + B = 0` (since `B + B = 0`). -/
private lemma gamma_eq_iff_add_eq_zero (A B : Gamma) : A = B ↔ A + B = 0 := by
  constructor
  · rintro rfl; exact Gamma.add_self A
  · intro h
    have hh : A + B + B = B := by rw [h, zero_add]
    rwa [add_assoc, Gamma.add_self, add_zero] at hh

/-! ## §2 — the characteristic-two facts -/

open Classical in
/-- **The characteristic-two fact (§2).** *Because `Γ` has characteristic two,
`f : E(G) → Γ` is a `Γ`-flow with respect to some (equivalently, every) orientation of
`G` if and only if for every vertex `v` the sum of `f(e)` over all edge-ends at `v` is
`0`.*

This is the "some" half together with the orientation-free reformulation: for the
given orientation `O`, being a flow is equivalent to a condition in which `O` does not
appear. The right-hand sum ranges over the edge-**ends** at `v`, so a loop at `v`
contributes `2 • f e = f e + f e`, which is `0` in characteristic two, and a non-loop
edge incident to `v` contributes `1 • f e = f e`. -/
theorem gamma_flow_iff_endSum_zero (hV : V(G).Finite) (hE : E(G).Finite)
    (O : Orientation G) (f : β → Gamma) :
    G.IsFlow O f ↔
      ∀ v ∈ V(G),
        (∑ᶠ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • f e) = 0 := by
  classical
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
  rw [key, gamma_eq_iff_add_eq_zero]

/-- **The "some ⟺ every" half of the §2 fact.** *`f` is a `Γ`-flow with respect to
some (equivalently, every) orientation of `G`.*

Since the orientation-free condition of `gamma_flow_iff_endSum_zero` does not mention
the orientation, being a `Γ`-flow does not depend on which orientation is chosen. -/
theorem gamma_flow_orientation_independent (hV : V(G).Finite) (hE : E(G).Finite)
    (O O' : Orientation G) (f : β → Gamma) (hf : G.IsFlow O f) : G.IsFlow O' f := by
  exact (gamma_flow_iff_endSum_zero hV hE O' f).mpr
    ((gamma_flow_iff_endSum_zero hV hE O f).mp hf)

/-- **The loopless cubic specialisation (§2).** *At a vertex `v` of a loopless cubic
graph whose three incident edges are `a, b, c`, the flow condition reads
`f(a) + f(b) + f(c) = 0`.*

The three edges `a, b, c` at `v` are `ord.edge v 0`, `ord.edge v 1`, `ord.edge v 2`
for a local ordering `ord`, whose axioms say exactly that they enumerate
`G.incidenceSet v` without repetition. -/
theorem cubic_flow_eq (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (f : β → Gamma) (hf : G.IsFlow O f)
    (ord : LocalOrdering G) (hv : v ∈ V(G)) :
    f (ord.edge v 0) + f (ord.edge v 1) + f (ord.edge v 2) = 0 := by
  classical
  have h := (gamma_flow_iff_endSum_zero hV hE O f).mp hf v hv
  have hsum : (∑ᶠ e ∈ G.incidenceSet v, (if G.IsLoopAt e v then (2 : ℕ) else 1) • f e)
      = ∑ᶠ e ∈ G.incidenceSet v, f e := by
    refine finsum_mem_congr rfl (fun e _ => ?_)
    rw [if_neg (hloop e v), one_nsmul]
  rw [hsum] at h
  have htriple : G.incidenceSet v = {ord.edge v 0, ord.edge v 1, ord.edge v 2} := by
    rw [← ord.range_edge hv]
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl | rfl); exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have h01 : ord.edge v 0 ≠ ord.edge v 1 := ord.edge_ne_edge hv (by decide)
  have h02 : ord.edge v 0 ≠ ord.edge v 2 := ord.edge_ne_edge hv (by decide)
  have h12 : ord.edge v 1 ≠ ord.edge v 2 := ord.edge_ne_edge hv (by decide)
  have hcoe : ({ord.edge v 0, ord.edge v 1, ord.edge v 2} : Set β)
      = (↑({ord.edge v 0, ord.edge v 1, ord.edge v 2} : Finset β) : Set β) := by simp
  rw [htriple, hcoe, finsum_mem_coe_finset, Finset.sum_insert (by simp [h01, h02]),
    Finset.sum_insert (by simp [h12]), Finset.sum_singleton] at h
  rw [← add_assoc] at h
  exact h

/-- **The local notation of §5.** *Write `x = f(a)`, `y = f(b)`, `z = f(c)`. By the
characteristic-two flow equation, `x + y + z = 0`, so `z = x + y`; moreover `x, y, z`
are all nonzero and `x ≠ y`.*

Here `f` is a **nowhere-zero** `Γ`-flow, which is what makes `x`, `y` and `z` nonzero;
`x ≠ y` then follows because `x + y = z ≠ 0`. -/
theorem cubic_flow_distinct (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (f : β → Gamma) (hf : G.IsFlow O f)
    (hnz : G.IsNowhereZero f) (ord : LocalOrdering G) (hv : v ∈ V(G)) :
    f (ord.edge v 2) = f (ord.edge v 0) + f (ord.edge v 1) ∧
      f (ord.edge v 0) ≠ 0 ∧ f (ord.edge v 1) ≠ 0 ∧ f (ord.edge v 2) ≠ 0 ∧
      f (ord.edge v 0) ≠ f (ord.edge v 1) := by
  have heq := cubic_flow_eq hV hE hloop hcubic O f hf ord hv
  have hc : f (ord.edge v 2) = f (ord.edge v 0) + f (ord.edge v 1) := by
    rw [gamma_eq_iff_add_eq_zero]
    calc f (ord.edge v 2) + (f (ord.edge v 0) + f (ord.edge v 1))
        = f (ord.edge v 0) + f (ord.edge v 1) + f (ord.edge v 2) := by abel
      _ = 0 := heq
  have ha : f (ord.edge v 0) ≠ 0 := hnz _ (ord.edge_mem_edgeSet hv 0)
  have hb : f (ord.edge v 1) ≠ 0 := hnz _ (ord.edge_mem_edgeSet hv 1)
  have hcz : f (ord.edge v 2) ≠ 0 := hnz _ (ord.edge_mem_edgeSet hv 2)
  have hab : f (ord.edge v 0) ≠ f (ord.edge v 1) := by
    intro hcon
    apply hcz
    rw [hc, hcon, Gamma.add_self]
  exact ⟨hc, ha, hb, hcz, hab⟩

/-! ## §5 — Facts 5a–5d -/

/-- **Fact 5a, part (i): the local computation.** *With the notation above, the three
sets in (3) are `{t, t+x}`, `{t+x, t+z}`, and `{t, t+z}`.*

The three sets of (3) at `v` are `{t + g_{v,e}, t + g_{v,e} + f(e)}` for
`e = a, b, c`, i.e. for `e = S.ord.edge v i` with `i = 0, 1, 2`; and
`x = S.flow (S.ord.edge v 0)`, `z = S.flow (S.ord.edge v 2)`. The computation uses
equation (2) (`g_{v,a} = 0`, `g_{v,b} = x`, `g_{v,c} = 0`) and the flow relation
`z = x + y`. -/
theorem fact_5a (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (hv : v ∈ V(G)) (t : Gamma) :
    (({t + S.g v (S.ord.edge v 0), t + S.g v (S.ord.edge v 0) + S.flow (S.ord.edge v 0)}
        : Set Gamma) = {t, t + S.flow (S.ord.edge v 0)}) ∧
    (({t + S.g v (S.ord.edge v 1), t + S.g v (S.ord.edge v 1) + S.flow (S.ord.edge v 1)}
        : Set Gamma) = {t + S.flow (S.ord.edge v 0), t + S.flow (S.ord.edge v 2)}) ∧
    (({t + S.g v (S.ord.edge v 2), t + S.g v (S.ord.edge v 2) + S.flow (S.ord.edge v 2)}
        : Set Gamma) = {t, t + S.flow (S.ord.edge v 2)}) := by
  obtain ⟨hc, _, _, _, _⟩ :=
    cubic_flow_distinct hV hE hloop hcubic O S.flow hf hnz S.ord hv
  refine ⟨?_, ?_, ?_⟩
  · rw [S.g_edge_zero hv]; simp
  · rw [S.g_edge_one v, hc, add_assoc]
  · rw [S.g_edge_two hv]; simp

/-- **Fact 5a, part (ii): every vector occurs in zero or two of the local sets.**
*Hence every vector of `Γ` occurs in zero or two of them.*

The count is over the edges `e` incident to `v` — there are exactly three of them, and
they are the paper's `a, b, c` — whose local set `{t + g_{v,e}, t + g_{v,e} + f(e)}`
contains the given vector `s`. `Set.encard` is used so that the count means what it
says with no finiteness side condition. This is condition (1) of Lemma 2.1, locally. -/
theorem fact_5a_zero_or_two (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (hv : v ∈ V(G)) (t : Gamma) (s : Gamma) :
    {e ∈ G.incidenceSet v | s ∈ ({t + S.g v e, t + S.g v e + S.flow e} : Set Gamma)}.encard
      ∈ ({0, 2} : Set ℕ∞) := by
  classical
  obtain ⟨ha1, hb1, hc1⟩ := fact_5a hV hE hloop hcubic O S hf hnz hv t
  obtain ⟨hc, hx0, hy0, hz0, hxy⟩ :=
    cubic_flow_distinct hV hE hloop hcubic O S.flow hf hnz S.ord hv
  set a := S.ord.edge v 0 with ha_def
  set b := S.ord.edge v 1 with hb_def
  set c := S.ord.edge v 2 with hc_def
  have hab : a ≠ b := S.ord.edge_ne_edge hv (by decide)
  have hac : a ≠ c := S.ord.edge_ne_edge hv (by decide)
  have hbc : b ≠ c := S.ord.edge_ne_edge hv (by decide)
  have hne01 : (t : Gamma) ≠ t + S.flow a := fun h => hx0 (add_right_eq_zero_of_self_eq h)
  have hne02 : (t : Gamma) ≠ t + S.flow c := fun h => hz0 (add_right_eq_zero_of_self_eq h)
  have hne12 : t + S.flow a ≠ t + S.flow c := by
    intro h
    apply hy0
    have h' : S.flow a = S.flow c := add_left_cancel h
    exact add_right_eq_zero_of_self_eq (h'.trans hc)
  have htriple : G.incidenceSet v = ({a, b, c} : Set β) := by
    rw [← S.ord.range_edge hv]
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp [ha_def, hb_def, hc_def]
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, ha_def.symm⟩, ⟨1, hb_def.symm⟩, ⟨2, hc_def.symm⟩]
  have hFmem : ∀ e, (e ∈ {e ∈ G.incidenceSet v |
        s ∈ ({t + S.g v e, t + S.g v e + S.flow e} : Set Gamma)}) ↔
      (e = a ∧ (s = t ∨ s = t + S.flow a))
        ∨ (e = b ∧ (s = t + S.flow a ∨ s = t + S.flow c))
        ∨ (e = c ∧ (s = t ∨ s = t + S.flow c)) := by
    intro e
    rw [Set.mem_sep_iff]
    constructor
    · rintro ⟨hmem, hs⟩
      rw [htriple] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, by rw [ha1] at hs; simpa using hs⟩
      · exact Or.inr (Or.inl ⟨rfl, by rw [hb1] at hs; simpa using hs⟩)
      · exact Or.inr (Or.inr ⟨rfl, by rw [hc1] at hs; simpa using hs⟩)
    · rintro (⟨rfl, hs⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩)
      · exact ⟨by rw [htriple]; simp, by rw [ha1]; simpa using hs⟩
      · exact ⟨by rw [htriple]; simp, by rw [hb1]; simpa using hs⟩
      · exact ⟨by rw [htriple]; simp, by rw [hc1]; simpa using hs⟩
  by_cases hs0 : s = t
  · have hn1 : ¬ s = t + S.flow a := by intro h; rw [hs0] at h; exact hne01 h
    have hn2 : ¬ s = t + S.flow c := by intro h; rw [hs0] at h; exact hne02 h
    have hFeq : {e ∈ G.incidenceSet v |
        s ∈ ({t + S.g v e, t + S.g v e + S.flow e} : Set Gamma)} = ({a, c} : Set β) := by
      ext e; rw [hFmem e]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro (⟨rfl, _⟩ | ⟨rfl, hor⟩ | ⟨rfl, _⟩)
        · exact Or.inl rfl
        · rcases hor with h | h; exacts [absurd h hn1, absurd h hn2]
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact Or.inl ⟨rfl, Or.inl hs0⟩
        · exact Or.inr (Or.inr ⟨rfl, Or.inl hs0⟩)
    rw [hFeq, Set.encard_pair hac]; simp
  · by_cases hs1 : s = t + S.flow a
    · have hn2 : ¬ s = t + S.flow c := by intro h; rw [hs1] at h; exact hne12 h
      have hFeq : {e ∈ G.incidenceSet v |
          s ∈ ({t + S.g v e, t + S.g v e + S.flow e} : Set Gamma)} = ({a, b} : Set β) := by
        ext e; rw [hFmem e]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro (⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, hor⟩)
          · exact Or.inl rfl
          · exact Or.inr rfl
          · rcases hor with h | h; exacts [absurd h hs0, absurd h hn2]
        · rintro (rfl | rfl)
          · exact Or.inl ⟨rfl, Or.inr hs1⟩
          · exact Or.inr (Or.inl ⟨rfl, Or.inl hs1⟩)
      rw [hFeq, Set.encard_pair hab]; simp
    · by_cases hs2 : s = t + S.flow c
      · have hFeq : {e ∈ G.incidenceSet v |
            s ∈ ({t + S.g v e, t + S.g v e + S.flow e} : Set Gamma)} = ({b, c} : Set β) := by
          ext e; rw [hFmem e]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro (⟨rfl, hor⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩)
            · rcases hor with h | h; exacts [absurd h hs0, absurd h hs1]
            · exact Or.inl rfl
            · exact Or.inr rfl
          · rintro (rfl | rfl)
            · exact Or.inr (Or.inl ⟨rfl, Or.inr hs2⟩)
            · exact Or.inr (Or.inr ⟨rfl, Or.inr hs2⟩)
        rw [hFeq, Set.encard_pair hbc]; simp
      · have hFeq : {e ∈ G.incidenceSet v |
            s ∈ ({t + S.g v e, t + S.g v e + S.flow e} : Set Gamma)} = (∅ : Set β) := by
          ext e; rw [hFmem e]
          simp only [Set.mem_empty_iff_false, iff_false]
          rintro (⟨rfl, hor⟩ | ⟨rfl, hor⟩ | ⟨rfl, hor⟩)
          · rcases hor with h | h; exacts [hs0 h, hs1 h]
          · rcases hor with h | h; exacts [hs1 h, hs2 h]
          · rcases hor with h | h; exacts [hs0 h, hs2 h]
        rw [hFeq, Set.encard_empty]; simp

/-- **Fact 5b (agreement criterion).** *For any `p ∈ Γ`, `{A, A+p} = {B, B+p}`
precisely when `A + B ∈ {0, p}`.*

Pure `𝔽₂` linear algebra: no graph is involved, hence no finiteness hypothesis. -/
theorem fact_5b (A B p : Gamma) :
    ({A, A + p} : Set Gamma) = {B, B + p} ↔ A + B ∈ ({0, p} : Set Gamma) := by
  rw [Set.pair_eq_pair_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · left; rw [h1]; exact Gamma.add_self B
    · right; rw [h1, add_comm B p, add_assoc, Gamma.add_self, add_zero]
  · rintro (h | h)
    · have hAB : A = B := (gamma_eq_iff_add_eq_zero A B).mpr h
      exact Or.inl ⟨hAB, by rw [hAB]⟩
    · have hA : A = B + p := by
        rw [gamma_eq_iff_add_eq_zero, ← add_assoc, h, Gamma.add_self]
      exact Or.inr ⟨hA, by rw [hA, add_assoc, Gamma.add_self, add_zero]⟩

/-- **Fact 5c (the system (4)).** *The local sets in (3) agree across every edge
precisely when there are `t_v ∈ Γ` and `ε_e ∈ 𝔽₂` satisfying
`t_u + t_v + ε_e f(e) = d_e` (`e = uv`).*

"The local sets agree across every edge" means: there is a family `t : V(G) → Γ` such
that for every edge `e` with ends `u` and `v`, the local set of (3) computed at `u`
equals the one computed at `v`. Obtained from Fact 5b with `A = t_u + g_{u,e}`,
`B = t_v + g_{v,e}`, `p = f(e)`, using `A + B = t_u + t_v + d_e`, the bit `ε_e`
recording whether that vector is `0` or `f(e)`. -/
theorem fact_5c (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) :
    (∃ t : α → Gamma, ∀ e ∈ E(G), ∀ u v, G.IsLink e u v →
        ({t u + S.g u e, t u + S.g u e + S.flow e} : Set Gamma)
          = {t v + S.g v e, t v + S.g v e + S.flow e}) ↔
      (∃ (t : α → Gamma) (ε : β → F2), ∀ e ∈ E(G), ∀ u v, G.IsLink e u v →
        t u + t v + ε e • S.flow e = S.d e) := by
  classical
  have hbit : ∀ a : F2, a = 0 ∨ a = 1 := by decide
  refine exists_congr (fun t => ?_)
  constructor
  · -- forward: sets agree ⟹ choose the bits ε
    intro hP
    have hex : ∀ e, ∃ w : F2, e ∈ E(G) → ∀ u v, G.IsLink e u v →
        t u + t v + w • S.flow e = S.d e := by
      intro e
      by_cases he : e ∈ E(G)
      · obtain ⟨u0, v0, hl0⟩ := G.exists_isLink_of_mem_edgeSet he
        have huv0 : u0 ≠ v0 := Graph.isLoopless_iff_forall_isLink_ne.mp hloop e u0 v0 hl0
        have hd0 : S.d e = S.g u0 e + S.g v0 e := S.d_eq_add hl0 huv0
        have hsets := hP e he u0 v0 hl0
        rw [fact_5b] at hsets
        have hABval : (t u0 + S.g u0 e) + (t v0 + S.g v0 e) = (t u0 + t v0) + S.d e := by
          rw [hd0]; abel
        rw [hABval] at hsets
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsets
        rcases hsets with h | h
        · refine ⟨0, fun _ u v hl => ?_⟩
          have htt : t u + t v = t u0 + t v0 := by
            rcases hl.eq_and_eq_or_eq_and_eq hl0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2]
            · rw [h1, h2]; abel
          rw [zero_smul, add_zero, htt]
          exact (gamma_eq_iff_add_eq_zero _ _).mpr h
        · refine ⟨1, fun _ u v hl => ?_⟩
          have htt : t u + t v = t u0 + t v0 := by
            rcases hl.eq_and_eq_or_eq_and_eq hl0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2]
            · rw [h1, h2]; abel
          rw [one_smul, htt, ← h, ← add_assoc, Gamma.add_self, zero_add]
      · exact ⟨0, fun h => absurd h he⟩
    choose ε hε using hex
    exact ⟨ε, fun e he u v hl => hε e he u v hl⟩
  · -- reverse: a solution of (4) makes the sets agree
    rintro ⟨ε, hQ⟩ e he u v hl
    have huv : u ≠ v := Graph.isLoopless_iff_forall_isLink_ne.mp hloop e u v hl
    have hd : S.d e = S.g u e + S.g v e := S.d_eq_add hl huv
    have heq := hQ e he u v hl
    rw [fact_5b]
    have hAB : (t u + S.g u e) + (t v + S.g v e) = ε e • S.flow e := by
      have hstep : (t u + S.g u e) + (t v + S.g v e) = (t u + t v) + S.d e := by rw [hd]; abel
      rw [hstep, ← heq, ← add_assoc, Gamma.add_self, zero_add]
    rw [hAB]
    rcases hbit (ε e) with h0 | h1
    · rw [h0, zero_smul]; simp
    · rw [h1, one_smul]; simp

/-- **Fact 5d (assembly).** *Given a solution `(t, ε)` of (4), define
`P_e = {t_v + g_{v,e}, t_v + g_{v,e} + f(e)}` using either endpoint `v` of `e`. Then
(4) makes this definition independent of the chosen endpoint; `f(e) ≠ 0` makes the two
elements distinct, so `|P_e| = 2`; and Fact 5a gives condition (1).*

The conclusion has two parts: **(a)** endpoint-independence of the recipe, and **(b)** that any
`P` defined edgewise by it is a two-element assignment in the sense of Lemma 2.1 (`|P_e| = 2`
because `f(e) ≠ 0`, and condition (1) by Fact 5a). Values of `P` off `E(G)` are unconstrained,
as `Graph.IsTwoElementAssignment` never inspects them. -/
theorem fact_5d (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (O : Orientation G) (S : LocalShift G) (hf : G.IsFlow O S.flow)
    (hnz : G.IsNowhereZero S.flow) (t : α → Gamma) (ε : β → F2)
    (h4 : ∀ e ∈ E(G), ∀ u v, G.IsLink e u v → t u + t v + ε e • S.flow e = S.d e) :
    (∀ e ∈ E(G), ∀ u v, G.Inc e u → G.Inc e v →
        ({t u + S.g u e, t u + S.g u e + S.flow e} : Set Gamma)
          = {t v + S.g v e, t v + S.g v e + S.flow e}) ∧
      (∀ P : β → Set Gamma,
        (∀ e ∈ E(G), ∃ v, G.Inc e v ∧ P e = {t v + S.g v e, t v + S.g v e + S.flow e}) →
        G.IsTwoElementAssignment P) := by
  classical
  have hbit : ∀ a : F2, a = 0 ∨ a = 1 := by decide
  -- The local set of (3) read at either end of an edge agree, by (4) and Fact 5b.
  have palette_agree : ∀ e ∈ E(G), ∀ u w, G.IsLink e u w →
      ({t u + S.g u e, t u + S.g u e + S.flow e} : Set Gamma)
        = {t w + S.g w e, t w + S.g w e + S.flow e} := by
    intro e he u w hl
    have huw : u ≠ w := Graph.isLoopless_iff_forall_isLink_ne.mp hloop e u w hl
    have hd : S.d e = S.g u e + S.g w e := S.d_eq_add hl huw
    have heq := h4 e he u w hl
    rw [fact_5b]
    have hAB : (t u + S.g u e) + (t w + S.g w e) = ε e • S.flow e := by
      have hstep : (t u + S.g u e) + (t w + S.g w e) = (t u + t w) + S.d e := by rw [hd]; abel
      rw [hstep, ← heq, ← add_assoc, Gamma.add_self, zero_add]
    rw [hAB]
    rcases hbit (ε e) with h0 | h1
    · rw [h0, zero_smul]; simp
    · rw [h1, one_smul]; simp
  -- endpoint independence
  have hindep : ∀ e ∈ E(G), ∀ u v, G.Inc e u → G.Inc e v →
      ({t u + S.g u e, t u + S.g u e + S.flow e} : Set Gamma)
        = {t v + S.g v e, t v + S.g v e + S.flow e} := by
    intro e he u v hu hv
    obtain ⟨y, hlyu⟩ := hu
    rcases hv.eq_or_eq_of_isLink hlyu with rfl | rfl
    · rfl
    · exact palette_agree e he u v hlyu
  refine ⟨hindep, ?_⟩
  intro P hP
  constructor
  · -- every palette has exactly two elements, since `f e ≠ 0`
    intro e he
    obtain ⟨w, hw, hPe⟩ := hP e he
    rw [hPe]
    have hfe : S.flow e ≠ 0 := hnz e he
    have hne : t w + S.g w e ≠ t w + S.g w e + S.flow e := by
      intro hcontra
      exact hfe (add_right_eq_zero_of_self_eq hcontra)
    exact Set.encard_pair hne
  · -- condition (1), by Fact 5a
    intro v hv s
    have hsetPeq : G.paletteIncidenceSet P v s
        = {e ∈ G.incidenceSet v |
            s ∈ ({t v + S.g v e, t v + S.g v e + S.flow e} : Set Gamma)} := by
      ext e
      simp only [Graph.mem_paletteIncidenceSet, Set.mem_sep_iff, Graph.mem_incidenceSet]
      constructor
      · rintro ⟨hinc, hs⟩
        obtain ⟨w, hw, hPe⟩ := hP e hinc.edge_mem
        rw [hPe] at hs
        exact ⟨hinc, by rwa [hindep e hinc.edge_mem w v hw hinc] at hs⟩
      · rintro ⟨hinc, hs⟩
        obtain ⟨w, hw, hPe⟩ := hP e hinc.edge_mem
        refine ⟨hinc, ?_⟩
        rw [hPe]
        rwa [hindep e hinc.edge_mem w v hw hinc]
    rw [hsetPeq]
    exact fact_5a_zero_or_two hV hE hloop hcubic O S hf hnz hv (t v) s

end Workspace.Facts.Construction
