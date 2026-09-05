import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
import Workspace.ProofLemmas.BranchClassification

/-!
# `FormsLineGraph` forces a choice of rungs to be edge-indexed

## The passage this module is about

PAPER (printed p. 39, the prose immediately following the proof of 8.1 — the sentence that
`StripSystems.FormsLineGraph` transcribes):

> *"For each **edge** `uv` of `J`, choose a `uv`-rung `R_{uv}`.  It follows from 8.1 and the final
> axiom above that the subgraph of `G` induced on the union of the vertex sets of these rungs is a
> line graph of a bipartite subdivision `H` of `J`.  For brevity we say that this choice of rungs
> forms `L(H)`."*

The quantifier is over **edges** `uv ∈ E(J)`, so `R_{uv}` and `R_{vu}` name **one** rung and *"the
union of the vertex sets of these rungs"* has one summand per edge.  The Lean encoding
`R : U → U → List V` indexes *ordered pairs*, and

```lean
FormsLineGraph G J S N R H :=
  (∀ u v, J.Adj u v → IsUVRung G J S N u v (R u v)) ∧
    IsAppearance G J H (⋃ (u) (v) (_ : J.Adj u v), {x | x ∈ R u v})
```

constrains `R u v` and `R v u` independently and unions over ordered pairs.  Section 8 uses the
sentence as a fact about *every* choice of rungs (8.4 printed p. 40: *"If every choice of rungs is
saturated …"*; 8.5 printed p. 43: *"Every choice of rungs is broad"*; 8.6 printed p. 46: *"For
every choice of rungs, forming `L(H)` say, …"*), so the gap matters.

## What this module says

The edge-indexing clause is **not** an extra assumption: it is a *consequence* of
`FormsLineGraph`.  Its faithful Lean form is

```lean
∀ u v, J.Adj u v → R v u = (R u v).reverse
```

and **not** `R u v = R v u`.  The on-the-nose equation is refuted on disk
(`ProofAttempts/Thm82RungChoice/Thm82RungChoice_scratch.lean`, `forced_pathLength_zero`): a rung is
a *directed* object in this encoding, since `IsUVRung G J S N u v L` pins `head L` as the unique
vertex of `L` in `N_u` while `IsUVRung G J S N v u L` pins `getLast L`; on one list those force
`head L = getLast L`, and `L.Nodup` then collapses `L` to a single vertex, i.e.
`pathLength (R u v) = 0` for **every** edge of `J`.  See the "rung-symmetry defect" entry of
`PROVING_NOTES.md` and `AMBIGUITIES.md`.

## Consequence for `Thm84EveryChoiceFormsLineGraph`

`Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph` carries
`hRsymm : ∀ u v, J.Adj u v → R v u = (R u v).reverse` as a **hypothesis**, and this module is its
*converse*.  The two together say `hRsymm` is exactly right — necessary **and** sufficient — so it
must **not** be dropped: the conclusion of `everyChoiceFormsLineGraph` is
`∃ H, FormsLineGraph G J S N R H`, and by the theorem below that conclusion *implies* `hRsymm`.
Dropping the hypothesis would make the statement false, not more faithful.  What the pair does buy
is that `hRsymm` costs a caller nothing whenever the caller already has a `FormsLineGraph`, which
is what the assembly of 8.4 needs (the frozen hypothesis `hsat` of `thm_8_4` supplies only
`FormsLineGraph` for its saturated choice of rungs).

## Proof

`rung_end_unique` below is the mathematical core and is proved here.  It says: **the only vertex of
`K` lying in `N_u ∩ S_{uv}` is the `u`-end of `R u v`** — where `K` is the union of the rung vertex
sets, the vertex set of `L(H)`.  The argument is the one recorded when the defect was found, run
through the (proved) rung-end dictionary `Thm84RungEndDictionary.rungEndDictionary`:

* let `z ∈ K` with `z ∈ N_u ∩ S_{uv}`, and let `e_z = φ⁻¹(z)` be the corresponding edge of `H`;
* `deg_J(u) ≥ 3`, so `u` has two `J`-neighbours `w ≠ x` other than `v`; axiom 6 of a strip system
  (*"`N_u ∩ S_{uv}` is complete to `N_u ∩ S_{uw}`"*) makes `z` adjacent in `G` to the `u`-ends of
  `R u w` and of `R u x`, which the dictionary identifies with the edges `E u w`, `E u x` of `H`
  at the branch-vertex `ι u`;
* so in `L(H)` the edge `e_z` meets both `E u w` and `E u x`.  If `ι u ∉ e_z` then `e_z` joins the
  far ends of `E u w` and `E u x`, giving a triangle of `H` — impossible, `H` is bipartite;
* hence `e_z ∈ δ_H(ι u) = {E u v' : v' a J-neighbour of u}`, so `z` is the `u`-end of some
  `R u v'`, so `z ∈ S_{uv'}`; the strips are pairwise disjoint, so `v' = v`.

`rung_ends_swap` is the immediate corollary that `R u v` and `R v u` have interchanged ends, and
`strip_inter_eq_union` records that `K ∩ S_{uv} = V(R u v) ∪ V(R v u)`, so the whole theorem
reduces to `V(R v u) ⊆ V(R u v)`.

**Status of `formsLineGraph_forces_rung_symmetry` itself: STATED, NOT PROVED.**  See the closing
comment of this module for the precise remaining gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.FormsLineGraphForcesRungSymmetry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm84RungEndDictionary

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The only vertex of `L(H)` lying in `N_u ∩ S_{uv}` is the `u`-end of the rung `R u v`.**

This is the mathematical core of the module; see the module doc-comment for the argument. -/
theorem rung_end_unique {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (u v : U) (huv : J.Adj u v) (z : V)
    (hzK : z ∈ ⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b})
    (hzN : z ∈ N u) (hzS : z ∈ S u v) :
    ∀ s t : V, IsPathFrom G (R u v) s t → z = s := by
  classical
  intro send tend hpend
  obtain ⟨φ, ι, E, hιInj, hRange, hEedge, hIncident, hEInj, hEnd⟩ :=
    Thm84RungEndDictionary.rungEndDictionary G J hJ S N hSN H R hForms
  have hbip : H.IsBipartite := hForms.2.1.2
  -- two `J`-neighbours `w ≠ x` of `u`, both different from `v`
  have hdeg : 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  obtain ⟨w, x, hw, hx, hwx⟩ := exists_two_mem (two_le_ncard_diff (a := v) hdeg)
  have huw : J.Adj u w := hw.1
  have hux : J.Adj u x := hx.1
  have hwv : w ≠ v := fun h => hw.2 (by rw [h]; rfl)
  have hxv : x ≠ v := fun h => hx.2 (by rw [h]; rfl)
  -- the `u`-ends of `R u w` and `R u x`
  obtain ⟨-, sw, tw, hpw, hSw, hNw, -⟩ := hForms.1 u w huw
  obtain ⟨-, sx, tx, hpx, hSx, hNx, -⟩ := hForms.1 u x hux
  have hswMem : sw ∈ R u w := List.mem_of_mem_head? hpw.2.1
  have hsxMem : sx ∈ R u x := List.mem_of_mem_head? hpx.2.1
  have hswN : sw ∈ N u := (hNw sw hswMem).mpr rfl
  have hsxN : sx ∈ N u := (hNx sx hsxMem).mpr rfl
  have hswS : sw ∈ S u w := hSw sw hswMem
  have hsxS : sx ∈ S u x := hSx sx hsxMem
  -- `z` is adjacent to both, by the sixth axiom of a strip system
  have hzw : G.Adj z sw :=
    StripSystemBasics.Nuv_complete hSN huv huw (Ne.symm hwv) z ⟨hzN, hzS⟩ sw ⟨hswN, hswS⟩
  have hzx : G.Adj z sx :=
    StripSystemBasics.Nuv_complete hSN huv hux (Ne.symm hxv) z ⟨hzN, hzS⟩ sx ⟨hsxN, hsxS⟩
  -- the three vertices lie in `K`
  have hswK : sw ∈ ⋃ (a : U) (b : U) (_ : J.Adj a b), {q : V | q ∈ R a b} := by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨u, w, huw, hswMem⟩
  have hsxK : sx ∈ ⋃ (a : U) (b : U) (_ : J.Adj a b), {q : V | q ∈ R a b} := by
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨u, x, hux, hsxMem⟩
  -- `φ` sends `E u w` to `sw` and `E u x` to `sx`
  have hEw : (↑(φ ⟨E u w, hEedge u w huw⟩) : V) = sw := hEnd u w huw _ sw tw hpw
  have hEx : (↑(φ ⟨E u x, hEedge u x hux⟩) : V) = sx := hEnd u x hux _ sx tx hpx
  -- the edge of `H` corresponding to `z`
  set ez : H.edgeSet := φ.symm ⟨z, hzK⟩ with hez
  have hφez : (↑(φ ez) : V) = z := by rw [hez, RelIso.apply_symm_apply]
  -- `ez` is adjacent in `L(H)` to `E u w` and to `E u x`
  have hAdjL : ∀ (c : U) (hc : J.Adj u c) (sc : V),
      (↑(φ ⟨E u c, hEedge u c hc⟩) : V) = sc → G.Adj z sc →
      H.lineGraph.Adj ez ⟨E u c, hEedge u c hc⟩ := by
    intro c hc sc hsc hadj
    refine φ.map_rel_iff.mp ?_
    show G.Adj (↑(φ ez) : V) (↑(φ ⟨E u c, hEedge u c hc⟩) : V)
    rw [hφez, hsc]
    exact hadj
  have hadjw := hAdjL w huw sw hEw hzw
  have hadjx := hAdjL x hux sx hEx hzx
  obtain ⟨hnew, αw, hαw1, hαw2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadjw
  obtain ⟨hnex, αx, hαx1, hαx2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadjx
  -- `E u w ≠ E u x`
  have hEwx : E u w ≠ E u x := by
    intro h
    exact hwx (hEInj u w x huw hux h)
  -- `ι u` lies on `E u w` and on `E u x`
  have hιw : ι u ∈ E u w := by
    have : E u w ∈ incidentEdges H (ι u) := by
      rw [hIncident u]; exact ⟨w, huw, rfl⟩
    exact this.2
  have hιx : ι u ∈ E u x := by
    have : E u x ∈ incidentEdges H (ι u) := by
      rw [hIncident u]; exact ⟨x, hux, rfl⟩
    exact this.2
  -- therefore `ι u ∈ ez`: otherwise `ez` joins the far ends of `E u w` and `E u x`, a triangle
  have hιez : ι u ∈ (ez : Sym2 W) := by
    by_contra hnot
    have hαwne : αw ≠ ι u := by rintro rfl; exact hnot hαw1
    have hαxne : αx ≠ ι u := by rintro rfl; exact hnot hαx1
    have heqw : E u w = s(ι u, αw) := eq_sym2_of_mem_mem (Ne.symm hαwne) hιw hαw2
    have heqx : E u x = s(ι u, αx) := eq_sym2_of_mem_mem (Ne.symm hαxne) hιx hαx2
    have hαne : αw ≠ αx := by
      rintro rfl; exact hEwx (heqw.trans heqx.symm)
    have hezeq : (ez : Sym2 W) = s(αw, αx) := eq_sym2_of_mem_mem hαne hαw1 hαx1
    have hAw : H.Adj (ι u) αw := (SimpleGraph.mem_edgeSet _).mp (heqw ▸ hEedge u w huw)
    have hAx : H.Adj (ι u) αx := (SimpleGraph.mem_edgeSet _).mp (heqx ▸ hEedge u x hux)
    have hAwx : H.Adj αw αx := (SimpleGraph.mem_edgeSet _).mp (hezeq ▸ ez.2)
    exact no_triangle_of_bipartite hbip hAw hAwx hAx
  -- so `ez` is one of the edges indexed by the `J`-neighbours of `u`
  have hezδ : (ez : Sym2 W) ∈ incidentEdges H (ι u) := ⟨ez.2, hιez⟩
  rw [hIncident u] at hezδ
  obtain ⟨v', hv', hezv'⟩ := hezδ
  -- `z` is the `u`-end of `R u v'`, hence lies in `S_{u v'}`, hence `v' = v`
  obtain ⟨-, s', t', hp', hS', -, -⟩ := hForms.1 u v' hv'
  have hzs' : z = s' := by
    have : (⟨E u v', hEedge u v' hv'⟩ : H.edgeSet) = ez := Subtype.ext hezv'.symm
    rw [← hEnd u v' hv' (hEedge u v' hv') s' t' hp', this, hφez]
  have hzS' : z ∈ S u v' := by
    rw [hzs']
    exact hS' s' (List.mem_of_mem_head? hp'.2.1)
  have hvv' : v = v' := by
    have hsym2 := StripSystemBasics.edge_eq_of_mem_strips hSN huv hv' hzS hzS'
    rcases Sym2.eq_iff.mp hsym2 with ⟨-, h⟩ | ⟨-, h2⟩
    · exact h
    · exact absurd huv (by rw [h2]; exact fun hc => J.irrefl hc)
  have hhead1 : (R u v).head? = some send := hpend.2.1
  have hhead2 : (R u v').head? = some s' := hp'.2.1
  rw [hvv'] at hhead1
  exact hzs'.trans (Option.some_injective _ (hhead2.symm.trans hhead1))

/-- **The two orientations of a rung have interchanged ends.**

The `u`-end of `R v u` is the `u`-end of `R u v`, and the `v`-end of `R u v` is the `v`-end of
`R v u`.  Immediate from `rung_end_unique`. -/
theorem rung_ends_swap {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (u v : U) (huv : J.Adj u v) :
    ∀ s t s' t' : V, IsPathFrom G (R u v) s t → IsPathFrom G (R v u) s' t' →
      t' = s ∧ s' = t := by
  intro s t s' t' hst hst'
  obtain ⟨-, s₀, t₀, hp, hSsub, hNu, hNv⟩ := hForms.1 u v huv
  obtain ⟨-, s₁, t₁, hq, hSsub', hNv', hNu'⟩ := hForms.1 v u huv.symm
  -- name the ends coherently
  have ht₀ : t₀ = t := Option.some_injective _ (hp.2.2.symm.trans hst.2.2)
  have ht₁ : t₁ = t' := Option.some_injective _ (hq.2.2.symm.trans hst'.2.2)
  have htMem : t ∈ R u v := Workspace.ProofLemmas.PathBasics.getLast_mem hst.2.2
  have ht'Mem : t' ∈ R v u := Workspace.ProofLemmas.PathBasics.getLast_mem hst'.2.2
  have hSvu : S v u = S u v := hSN.1 v u huv.symm
  constructor
  · -- `t'`, the `u`-end of `R v u`, lies in `K ∩ N_u ∩ S_{uv}`
    refine rung_end_unique G J hJ S N hSN H R hForms u v huv t' ?_ ?_ ?_ s t hst
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨v, u, huv.symm, ht'Mem⟩
    · exact (hNu' t' ht'Mem).mpr ht₁.symm
    · rw [← hSvu]; exact hSsub' t' ht'Mem
  · -- `t`, the `v`-end of `R u v`, lies in `K ∩ N_v ∩ S_{vu}`
    exact (rung_end_unique G J hJ S N hSN H R hForms v u huv.symm t
      (by simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨u, v, huv, htMem⟩)
      ((hNv t htMem).mpr ht₀.symm)
      (by rw [hSvu]; exact hSsub t htMem) s' t' hst').symm

/-- **`K ∩ S_{uv}` is exactly the union of the vertex sets of the two orientations.**

The strips are pairwise disjoint and every vertex of `K` lies on some rung, so the whole
edge-indexing statement reduces to the inclusion `V(R v u) ⊆ V(R u v)`. -/
theorem strip_inter_eq_union {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (u v : U) (huv : J.Adj u v) :
    (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}) ∩ S u v
      = {x : V | x ∈ R u v} ∪ {x : V | x ∈ R v u} := by
  have hSvu : S v u = S u v := hSN.1 v u huv.symm
  ext z
  constructor
  · rintro ⟨hzK, hzS⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hzK
    obtain ⟨a, b, hab, hzab⟩ := hzK
    obtain ⟨-, -, -, hp, hSsub, -, -⟩ := hForms.1 a b hab
    have hzSab : z ∈ S a b := hSsub z hzab
    have := StripSystemBasics.edge_eq_of_mem_strips hSN huv hab hzS hzSab
    rcases Sym2.eq_iff.mp this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [h1, h2]; exact hzab)
    · exact Or.inr (by rw [h1, h2]; exact hzab)
  · rintro (hz | hz)
    · obtain ⟨-, -, -, -, hSsub, -, -⟩ := hForms.1 u v huv
      exact ⟨by simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨u, v, huv, hz⟩,
        hSsub z hz⟩
    · obtain ⟨-, -, -, -, hSsub, -, -⟩ := hForms.1 v u huv.symm
      exact ⟨by simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact ⟨v, u, huv.symm, hz⟩,
        by rw [← hSvu]; exact hSsub z hz⟩

/-- Two induced paths with the same ordered ends and the same vertex set have the same order. -/
private theorem path_eq_of_same_vertices {G : SimpleGraph V} {p q : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hq : IsPathFrom G q a b)
    (hmem : ∀ x : V, x ∈ p ↔ x ∈ q) : p = q := by
  classical
  have hfin : p.toFinset = q.toFinset := by
    ext x
    simpa using hmem x
  have hlen : p.length = q.length := by
    rw [← List.toFinset_card_of_nodup hp.1.2.1, hfin,
      List.toFinset_card_of_nodup hq.1.2.1]
  apply List.ext_getElem hlen
  intro i hip hiq
  induction i using Nat.strong_induction_on with
  | h i ih =>
      rcases i with _ | i
      · have hp0 := PathBasics.getElem_zero_of_head? hp.2.1 (by omega : 0 < p.length)
        have hq0 := PathBasics.getElem_zero_of_head? hq.2.1 (by omega : 0 < q.length)
        rw [hp0, hq0]
      · have hiprev : i < p.length := by omega
        have hiqprev : i < q.length := by omega
        have heqprev : p[i]'hiprev = q[i]'hiqprev :=
          ih i (by omega) hiprev hiqprev
        have hadjq : G.Adj (q[i]'hiqprev) (q[i + 1]'hiq) :=
          PathBasics.path_adj_succ hq.1 (i := i) hiq
        have hqp : q[i + 1]'hiq ∈ p :=
          (hmem _).mpr (List.getElem_mem hiq)
        obtain ⟨j, hjp, hj⟩ := List.getElem_of_mem hqp
        have hadjp : G.Adj (p[i]'hiprev) (p[j]'hjp) := by
          rw [heqprev, hj]
          exact hadjq
        rcases (PathBasics.path_adj_iff hp.1 hiprev hjp).mp hadjp with hij | hji
        · have hjidx : j = i + 1 := hij.symm
          subst j
          exact hj
        · have hjlt : j < i + 1 := by omega
          have hjq : j < q.length := by omega
          have heqj : p[j]'hjp = q[j]'hjq := ih j hjlt hjp hjq
          have hdup : q[j]'hjq = q[i + 1]'hiq := by rw [← heqj, hj]
          have := hq.1.2.1.getElem_inj_iff.mp hdup
          omega

/-- **A choice of rungs that forms a line graph is edge-indexed.**

*"For each **edge** `uv` of `J`, choose a `uv`-rung `R_{uv}`"* (printed p. 39): reversing the
orientation of an edge of `J` reverses the chosen rung.

**STATED, NOT PROVED.**  `rung_end_unique` above settles the ends; the remaining gap is recorded in
the closing comment of this module. -/
theorem formsLineGraph_forces_rung_symmetry {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H) :
    ∀ u v : U, J.Adj u v → R v u = (R u v).reverse := by
  classical
  obtain ⟨φ⟩ := hForms.2.2
  obtain ⟨ι, B, hι, hrange, hB, hBverts, -⟩ :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.branchRungDictionaryAt
      G J hJ S N hSN H R hForms φ
  obtain ⟨ι₀, T, hι₀, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ :=
    hForms.2.1.1
  have hdeg : ∀ x : U, 3 ≤ (J.neighborSet x).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  intro u v huv
  obtain ⟨hBuv, hBuvFrom⟩ := hB u v huv
  obtain ⟨hBvu, hBvuFrom⟩ := hB v u huv.symm
  have hiuv : ι u ≠ ι v := fun h => huv.ne (hι h)
  have two_le_of_ends_ne : ∀ {q : List W} {c d : W},
      IsTrackFrom H q c d → c ≠ d → 2 ≤ q.length := by
    intro q c d hq hcd
    have hpos : 0 < q.length := List.length_pos_iff.mpr hq.1.1
    by_contra hlt
    have hlen1 : q.length = 1 := by omega
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hlen1
    have hwc : w = c := by simpa using hq.2.1
    have hwd : w = d := by simpa using hq.2.2
    exact hcd (hwc.symm.trans hwd)
  have hBuv2 : 2 ≤ (B u v).length := two_le_of_ends_ne hBuvFrom hiuv
  have hBvu2 : 2 ≤ (B v u).length := two_le_of_ends_ne hBvuFrom hiuv.symm
  have hiu : ι u ∈ branchVertices H := by
    rw [← hrange]
    exact ⟨u, rfl⟩
  have hiv : ι v ∈ branchVertices H := by
    rw [← hrange]
    exact ⟨v, rfl⟩
  have hBE : trackEdges (B u v) = trackEdges (B v u) :=
    Workspace.ProofLemmas.BranchClassification.trackEdges_eq_of_same_ends
      hι₀ htrack hlen hrev hdisj hnew hcover hedges hdeg
      hBuv hBuv2 hBuvFrom hBvu hBvu2 hBvuFrom hiu hiv (Or.inr ⟨rfl, rfl⟩)
  have hsets : {x : V | x ∈ R u v} = {x : V | x ∈ R v u} := by
    rw [← hBverts u v huv, ← hBverts v u huv.symm, hBE]
  obtain ⟨-, s, t, hp, -, -, -⟩ := hForms.1 u v huv
  obtain ⟨-, s', t', hq, -, -, -⟩ := hForms.1 v u huv.symm
  obtain ⟨ht', hs'⟩ := rung_ends_swap G J hJ S N hSN H R hForms u v huv
    s t s' t' hp hq
  have hqrev : IsPathFrom G (R v u).reverse s t := by
    have := PathBasics.isPathFrom_reverse hq
    simpa [ht', hs'] using this
  have hsame : R u v = (R v u).reverse := by
    apply path_eq_of_same_vertices hp hqrev
    intro x
    simpa only [List.mem_reverse] using (Set.ext_iff.mp hsets x)
  simpa using (congrArg List.reverse hsame).symm

/-- The membership form of the same fact, as carried by the four statements of
`Workspace.ProofLemmas.LineGraphDegree`. -/
theorem formsLineGraph_mem_symm {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H) :
    ∀ a b : U, J.Adj a b → ∀ y : V, y ∈ R b a → y ∈ R a b := by
  intro a b hab y hy
  rw [formsLineGraph_forces_rung_symmetry G J hJ S N hSN H R hForms a b hab] at hy
  exact List.mem_reverse.mp hy

end Workspace.ProofLemmas.FormsLineGraphForcesRungSymmetry

/-
## The remaining gap in `formsLineGraph_forces_rung_symmetry`

By `strip_inter_eq_union` the theorem is equivalent to `V(R v u) ⊆ V(R u v)` for every edge `uv`
of `J`, and by `rung_ends_swap` the two lists already have interchanged ends.  What is missing is
the *interior*: that no vertex of `K ∩ S_{uv}` lies off `R u v`.

The mathematical argument is the line-graph translation of *"the strip `S_{uv}` contributes exactly
the `uv`-branch of `H`"*.  Write `M = K ∩ S_{uv}` and `M_H = φ⁻¹(M) ⊆ E(H)`.  `rung_end_unique`
shows that `M` meets `N_u` only in the `u`-end of `R u v` and `N_v` only in its `v`-end, so — by
axioms 5 and 6 of a `J`-strip system — every vertex of `M` other than those two ends has *all* its
`G`-neighbours inside `M`.  Translated through `φ`, every edge in `M_H` other than `E u v` and
`E v u` has every edge of `H` meeting it again in `M_H`.  Since `H` is a subdivision of a
3-connected graph, `H` minus the two edges `E u v`, `E v u` has all of `E(H) \ δ_H(ι u) \ δ_H(ι v)`
in one "meeting"-component, so a single extra edge in `M_H` would drag in edges outside `S_{uv}`,
contradicting `M_H ⊆ φ⁻¹(S_{uv})`; hence `M_H = trackEdges (T u v)` and `M = V(R u v)`.

Formalizing that needs a connectivity fact about `H` that the workspace does not have:

```lean
  theorem lineGraph_connected_off_two_edges {W : Type*} (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) (e f : Sym2 W) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) :
    ∀ g ∈ H.edgeSet, g ≠ e → g ≠ f →
      ∃ p : List (Sym2 W), -- a walk in `L(H)` from `g` to any other edge of `H`
        True
```

i.e. that deleting two vertices from `L(H)` leaves it connected when `H` is cyclically
3-connected.  That is the natural companion of `TrackToRungPath` (which goes the other way, from a
track of `H` to an induced path of `G`) and is worth its own module; it is also what an eventual
proof of `Thm82BranchDelta` will need.

An alternative, purely counting route also exists but needs `Thm82BranchDelta` (itself unproved) in
a `∀`-edge form: `|E(H)| = Σ_{uv ∈ E(J)} trackLength (T u v) = Σ_{uv ∈ E(J)} |R u v|` while
`|K| = Σ_{uv ∈ E(J)} |K ∩ S_{uv}| ≥ Σ_{uv ∈ E(J)} |R u v|`, with equality forced by `|K| = |E(H)|`.
-/
