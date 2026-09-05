import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_7
import Workspace.Statements.S04.Thm_4_5

/-!
# 10.6, claim (3): a component attached only to `A` gives a balanced skew partition

This module is the paragraph of the printed proof of **10.6** (published version, printed
p. 62) that immediately follows claim (2):

> *"Suppose `F` is a component of `V(G) \ V(H)`, and all its attachments are in `A`.  Then
> `(V(G) \ A, A)` is a skew partition of `G`.  We must show that `G` admits a balanced skew
> partition.  Choose `b₂ ∈ B₂` and `a₃ ∈ A₃`.  Then `B₁ ∪ C₁ ∪ {b₂}` is connected, and all
> vertices in `A₁` have neighbours in it.  By 2.6, `(B₁ ∪ C₁ ∪ {b₂}, A₁)` is balanced, and so
> by 2.7.1, so is `(A₁, F)`.  By 4.5, `G` admits a balanced skew partition.  So we may assume
> there is no such `F`, and the same for `B`."*

The main results are

* `admitsBalancedSkewPartition_of_attachments_subset_A` — the paragraph as printed, and
* `admitsBalancedSkewPartition_of_attachments_subset_B` — its *"and the same for `B`"*.

## How the printed sentences map onto the Lean proof

* *"`(V(G) \ A, A)` is a skew partition"* is not used as such: the paper's very next sentence
  says the conclusion to be proved is `AdmitsBalancedSkewPartition G`, and 4.5 delivers that
  from the four sets of the partition directly, with no `IsSkewPartition` value in between.
  The four sets are the paper's skew partition refined once on each side: the `A`-side of the
  skew partition splits as `X := A₂ ∪ A₃` complete to `Y := A₁`, and its complement splits as
  `L := F` and `R := V(G) \ (A ∪ F)`, with no edges between `L` and `R` — that is exactly the
  reason `(V(G) \ A, A)` was a skew partition in the first place.
* *"Then `B₁ ∪ C₁ ∪ {b₂}` is connected"* is `connectedSet_side`.  The set is connected
  **through `b₂`**: `B₁` itself need not be connected, but `b₂ ∈ B₂` is complete to `B₁`, and
  every vertex of `C₁` reaches `B₁` along the tail of a `1`-rung through it.
* *"and all vertices in `A₁` have neighbours in it"* is `exists_adj_mem_side`: the vertex
  `a ∈ A₁` is the `A`-end of a `1`-rung through it, and its successor on that rung lies in
  `C₁` (or is the `B`-end, if the rung is a single edge).
* *"By 2.6"* is `_root_.Workspace.Statements.S02.SPGT.thm_2_6`, with the outside vertex `v` of
  2.6 taken to be the paper's `a₃ ∈ A₃`: that is what `a₃` is chosen for.
* *"by 2.7.1"* is the **first** conjunct of `_root_.Workspace.Statements.S02.SPGT.thm_2_7`.
* *"By 4.5"* is `_root_.Workspace.Statements.S04.SPGT.thm_4_5`, third alternative.
* *"and the same for `B`"* is `isHyperprism_swap`: exchanging the `A`-family and the
  `B`-family of a hyperprism again gives a hyperprism (every rung is simply run backwards),
  with the same `V(H)`.  So the `B`-case is literally the `A`-case re-run, which is what the
  paper's phrase asks for.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismSkewFromSide

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

private theorem dl {X Y : Set V} (h : Disjoint X Y) {x : V} (hx : x ∈ X) : x ∉ Y :=
  Set.disjoint_left.mp h hx

/-! ### The `A` ↔ `B` symmetry of a hyperprism

The nine sets of a hyperprism carry a symmetry the printed proof uses without comment, in the
phrase *"and the same for `B`"*: exchanging `Aᵢ` with `Bᵢ` again gives a hyperprism, because
an `i`-rung run backwards is an `i`-rung of the exchanged system, of the same length. -/

theorem hyperVerts_swap (A B C : Fin 3 → Set V) :
    hyperVerts B A C = hyperVerts A B C := by
  ext x
  simp only [hyperVerts, Set.mem_union]
  tauto

private theorem mem_S_swap {i : Fin 3} {v : V} (h : v ∈ B i ∪ A i ∪ C i) :
    v ∈ A i ∪ B i ∪ C i := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

/-- **Exchanging the `A`-family and the `B`-family of a hyperprism gives a hyperprism.** -/
theorem isHyperprism_swap (hH : IsHyperprism G A B C) : IsHyperprism G B A C := by
  obtain ⟨hne, hAB, hAC, hBC, hAA, hBB, hCC, hcr, hrung, hev⟩ := hH
  refine ⟨fun i => ⟨(hne i).2.1, (hne i).1, (hne i).2.2⟩, fun i j => (hAB j i).symm,
    fun i j => hBC i j, fun i j => hAC i j, fun i j hij => hBB i j hij,
    fun i j hij => hAA i j hij, hCC, ?_, ?_, ?_⟩
  · intro i j hij
    obtain ⟨h1, h2, h3⟩ := hcr i j hij
    refine ⟨h2, h1, ?_⟩
    intro u hu v hv hadj
    rcases h3 u (mem_S_swap hu) v (mem_S_swap hv) hadj with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr ⟨e1, e2⟩
    · exact Or.inl ⟨e1, e2⟩
  · intro i v hv
    obtain ⟨p, ⟨x, y, hx, hy, hpath, hint⟩, hvp⟩ := hrung i v (mem_S_swap hv)
    exact ⟨p.reverse, ⟨y, x, hy, hx, PathBasics.isPathFrom_reverse hpath,
      fun w hw => hint w (PathBasics.mem_interior_reverse.mp hw)⟩, List.mem_reverse.mpr hvp⟩
  · obtain ⟨p, ⟨x, y, hx, hy, hpath, hint⟩, hpev⟩ := hev
    refine ⟨p.reverse, ⟨y, x, hy, hx, PathBasics.isPathFrom_reverse hpath,
      fun w hw => hint w (PathBasics.mem_interior_reverse.mp hw)⟩, ?_⟩
    rw [PathBasics.pathLength_reverse]
    exact hpev

/-! ### Connectivity through a hub -/

private theorem reach_mono {S X : Set V} (hSX : S ⊆ X) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hr : (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (G.induce X).Reachable ⟨x, hSX hx⟩ ⟨y, hSX hy⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun z => ⟨z.1, hSX z.2⟩, fun {_ _} hab => hab⟩ : (G.induce S) →g (G.induce X)) p⟩

/-- A set is connected as soon as every one of its vertices lies in a connected subset that
also contains one fixed *hub* vertex. -/
private theorem connectedSet_of_hub {X : Set V} {b : V} (hbX : b ∈ X)
    (h : ∀ w ∈ X, ∃ S : Set V, S ⊆ X ∧ ConnectedSet G S ∧ w ∈ S ∧ b ∈ S) :
    ConnectedSet G X := by
  have key : ∀ u : ↥X, (G.induce X).Reachable u ⟨b, hbX⟩ := by
    rintro ⟨u, hu⟩
    obtain ⟨S, hSX, hS, hwS, hbS⟩ := h u hu
    exact reach_mono hSX hwS hbS (hS ⟨u, hwS⟩ ⟨b, hbS⟩)
  intro u v
  exact (key u).trans (key v).symm

private theorem connectedSet_singleton (G : SimpleGraph V) (v : V) :
    ConnectedSet G ({v} : Set V) := by
  intro a b
  exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)

/-! ### *"Then `B₁ ∪ C₁ ∪ {b₂}` is connected"* -/

/-- PAPER (printed p. 62): *"Choose `b₂ ∈ B₂` … Then `B₁ ∪ C₁ ∪ {b₂}` is connected."*

`Bᵢ` on its own need not be connected; `b` supplies the hub, being complete to `Bᵢ`, and each
vertex of `Cᵢ` reaches `Bᵢ` along the tail of an `i`-rung through it. -/
theorem connectedSet_side (hH : IsHyperprism G A B C) {i j : Fin 3} (hji : j ≠ i)
    {b : V} (hb : b ∈ B j) :
    ConnectedSet G (B i ∪ C i ∪ ({b} : Set V)) := by
  refine connectedSet_of_hub (Or.inr rfl) ?_
  rintro w ((hw | hw) | hw)
  · -- `w ∈ Bᵢ`: the single edge `w b`
    have hadj : G.Adj w b := complete_B hH (Ne.symm hji) w hw b hb
    refine ⟨{v : V | v ∈ [w, b]}, ?_,
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_pair hadj), by simp, by simp⟩
    intro z hz
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact Or.inl (Or.inl hw)
    · exact Or.inr rfl
  · -- `w ∈ Cᵢ`: the tail of an `i`-rung through `w`, plus `b`
    obtain ⟨p, x, y, hp, hwp⟩ := exists_rung_through hH i (Or.inr hw)
    have hwx : w ≠ x := by
      intro h; rw [h] at hw; exact dl (hH.2.2.1 i i) hp.1 hw
    have hwy : w ≠ y := by
      intro h; rw [h] at hw; exact dl (hH.2.2.2.1 i i) hp.2.1 hw
    have hwint : w ∈ SPGT.interior p :=
      (PathBasics.mem_interior_iff_of_pathFrom hp.2.2.1).mpr ⟨hwp, hwx, hwy⟩
    obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
      PathBasics.exists_getElem_of_mem_interior hp.2.2.1.1 hwint
    have hpos : 0 < p.length := by omega
    have hlast : p[p.length - 1]'(by omega) = y :=
      PathBasics.getElem_last_of_getLast? hp.2.2.1.2.2 hpos
    have hkl : k < p.length - 1 := by omega
    have hjl : p.length - 1 < p.length := by omega
    -- the stretch of the rung from `w` to its `B`-end
    have hQ : IsPathFrom G ((p.drop k).take (p.length - 1 - k + 1))
        (p[k]'(by omega)) (p[p.length - 1]'hjl) :=
      PathBasics.isPathFrom_slice hp.2.2.1.1 hkl hjl
    have hmemQ : ∀ z ∈ (p.drop k).take (p.length - 1 - k + 1), z ∈ B i ∪ C i := by
      intro z hz
      obtain ⟨m, hm, hm1, hm2, rfl⟩ :=
        (PathBasics.mem_slice_iff p (le_of_lt hkl) hjl).mp hz
      rcases (show m = p.length - 1 ∨ m < p.length - 1 by omega) with rfl | hlt
      · exact Or.inl (hlast ▸ hp.2.1)
      · refine Or.inr (hp.2.2.2 _ ?_)
        exact PathBasics.getElem_mem_interior hp.2.2.1.1 hm (by omega) (by omega)
    have hyQ : y ∈ {v : V | v ∈ (p.drop k).take (p.length - 1 - k + 1)} := by
      refine (PathBasics.mem_slice_iff p (le_of_lt hkl) hjl).mpr
        ⟨p.length - 1, hjl, by omega, le_rfl, hlast⟩
    refine ⟨{v : V | v ∈ (p.drop k).take (p.length - 1 - k + 1)} ∪ ({b} : Set V), ?_,
      ConnectedSetUnionAttach.connectedSet_union_singleton
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQ.1)
        ⟨y, hyQ, complete_B hH hji b hb y hp.2.1⟩, ?_, Or.inr rfl⟩
    · rintro z (hz | hz)
      · exact Or.inl (hmemQ z hz)
      · exact Or.inr hz
    · refine Or.inl ?_
      refine (PathBasics.mem_slice_iff p (le_of_lt hkl) hjl).mpr ⟨k, hk, le_rfl, by omega, hkw⟩
  · -- `w = b`
    rw [show w = b from hw]
    exact ⟨({b} : Set V), fun z hz => Or.inr hz, connectedSet_singleton G b, rfl, rfl⟩

/-! ### *"and all vertices in `A₁` have neighbours in it"* -/

/-- PAPER (printed p. 62): *"… and all vertices in `A₁` have neighbours in it."*

The vertex `a ∈ Aᵢ` is the `A`-end of an `i`-rung through it; its successor on that rung lies
in `Cᵢ`, unless the rung is a single edge, in which case the successor is the `B`-end. -/
theorem exists_adj_mem_side (hH : IsHyperprism G A B C) {i : Fin 3} (b : V)
    {a : V} (ha : a ∈ A i) :
    ∃ d ∈ B i ∪ C i ∪ ({b} : Set V), G.Adj a d := by
  obtain ⟨p, x, y, hp, hap⟩ := exists_rung_through hH i (Or.inl (Or.inl ha))
  have hax : a = x := rung_eq_A hH hp hap ha
  have h2 : 2 ≤ p.length := rung_two_le_length hH hp
  have hpos : 0 < p.length := by omega
  have h0 : p[0]'hpos = x := PathBasics.getElem_zero_of_head? hp.2.2.1.2.1 hpos
  have hadj : G.Adj (p[0]'hpos) (p[1]'(by omega)) :=
    PathBasics.path_adj_succ hp.2.2.1.1 (by omega)
  have hadja : G.Adj a (p[1]'(show 1 < p.length by omega)) := by
    rw [hax, ← h0]; exact hadj
  rcases (show p.length = 2 ∨ 3 ≤ p.length by omega) with hlen | hlen
  · -- a rung with two vertices: the successor is the `B`-end
    have hlast : p[p.length - 1]'(by omega) = y :=
      PathBasics.getElem_last_of_getLast? hp.2.2.1.2.2 hpos
    have he : (p[1]'(show 1 < p.length by omega)) = p[p.length - 1]'(by omega) :=
      (PathBasics.path_nodup hp.2.2.1.1).getElem_inj_iff.mpr (by omega)
    exact ⟨y, Or.inl (Or.inl hp.2.1), by rw [← hlast, ← he]; exact hadja⟩
  · -- otherwise the successor is an interior vertex, hence in `Cᵢ`
    have hint : (p[1]'(show 1 < p.length by omega)) ∈ SPGT.interior p :=
      PathBasics.getElem_mem_interior hp.2.2.1.1 (by omega) (by omega) (by omega)
    exact ⟨_, Or.inl (Or.inr (hp.2.2.2 _ hint)), hadja⟩

/-! ### The paragraph itself -/

/-- **Claim (3) of the printed proof of 10.6** (printed p. 62).

PAPER: *"Suppose `F` is a component of `V(G) \ V(H)`, and all its attachments are in `A`.
Then `(V(G) \ A, A)` is a skew partition of `G`.  We must show that `G` admits a balanced skew
partition.  Choose `b₂ ∈ B₂` and `a₃ ∈ A₃`.  Then `B₁ ∪ C₁ ∪ {b₂}` is connected, and all
vertices in `A₁` have neighbours in it.  By 2.6, `(B₁ ∪ C₁ ∪ {b₂}, A₁)` is balanced, and so by
2.7.1, so is `(A₁, F)`.  By 4.5, `G` admits a balanced skew partition."* -/
theorem admitsBalancedSkewPartition_of_attachments_subset_A [Fintype V] [DecidableEq V]
    (hG : Berge G) (hH : IsHyperprism G A B C) {F : Set V}
    (hF : IsComponent G (hyperVerts A B C)ᶜ F) (hFne : F.Nonempty)
    (hatt : attachments G F (hyperVerts A B C) ⊆ A 0 ∪ A 1 ∪ A 2) :
    AdmitsBalancedSkewPartition G := by
  -- *"Choose `b₂ ∈ B₂` and `a₃ ∈ A₃`."*
  obtain ⟨b₂, hb₂⟩ := (hH.1 1).2.1
  obtain ⟨a₃, ha₃⟩ := (hH.1 2).1
  have hFH : ∀ z ∈ F, z ∉ hyperVerts A B C := fun z hz => hF.1 hz
  -- `Aᵢ` and `Bᵢ`, `Cᵢ` all live inside `V(H)`
  have hAH : ∀ (k : Fin 3), ∀ z ∈ A k, z ∈ hyperVerts A B C :=
    fun k z hz => subset_hyperVerts k (Or.inl (Or.inl hz))
  have hBH : ∀ (k : Fin 3), ∀ z ∈ B k, z ∈ hyperVerts A B C :=
    fun k z hz => subset_hyperVerts k (Or.inl (Or.inr hz))
  have hCH : ∀ (k : Fin 3), ∀ z ∈ C k, z ∈ hyperVerts A B C :=
    fun k z hz => subset_hyperVerts k (Or.inr hz)
  -- `b₂` is not in `A`
  have hb₂A : b₂ ∉ A 0 ∪ A 1 ∪ A 2 := by
    rintro ((h | h) | h)
    · exact dl (hH.2.1 0 1) h hb₂
    · exact dl (hH.2.1 1 1) h hb₂
    · exact dl (hH.2.1 2 1) h hb₂
  ------------------------------------------------------------------
  -- Step 1: `D := B₁ ∪ C₁ ∪ {b₂}` is connected, and `A₁` attaches to it.
  ------------------------------------------------------------------
  have hDconn : ConnectedSet G (B 0 ∪ C 0 ∪ ({b₂} : Set V)) :=
    connectedSet_side hH (by decide) hb₂
  have hDattach : ∀ z ∈ A 0, ∃ d ∈ B 0 ∪ C 0 ∪ ({b₂} : Set V), G.Adj z d :=
    fun z hz => exists_adj_mem_side hH b₂ hz
  -- `D` lies inside `V(H)`, and misses `A`
  have hDH : ∀ z ∈ B 0 ∪ C 0 ∪ ({b₂} : Set V), z ∈ hyperVerts A B C := by
    rintro z ((h | h) | h)
    · exact hBH 0 z h
    · exact hCH 0 z h
    · rw [show z = b₂ from h]; exact hBH 1 b₂ hb₂
  have hDA : ∀ z ∈ B 0 ∪ C 0 ∪ ({b₂} : Set V), z ∉ A 0 ∪ A 1 ∪ A 2 := by
    rintro z ((h | h) | h)
    · rintro ((ha | ha) | ha)
      · exact dl (hH.2.1 0 0) ha h
      · exact dl (hH.2.1 1 0) ha h
      · exact dl (hH.2.1 2 0) ha h
    · rintro ((ha | ha) | ha)
      · exact dl (hH.2.2.1 0 0) ha h
      · exact dl (hH.2.2.1 1 0) ha h
      · exact dl (hH.2.2.1 2 0) ha h
    · rw [show z = b₂ from h]; exact hb₂A
  ------------------------------------------------------------------
  -- Step 2: *"By 2.6, `(B₁ ∪ C₁ ∪ {b₂}, A₁)` is balanced"*, with `v := a₃`.
  ------------------------------------------------------------------
  have hDdisj : Disjoint (B 0 ∪ C 0 ∪ ({b₂} : Set V)) (A 0) := by
    refine Set.disjoint_left.mpr ?_
    intro z hz
    exact fun hz0 => hDA z hz (Or.inl (Or.inl hz0))
  have ha₃out : a₃ ∉ (B 0 ∪ C 0 ∪ ({b₂} : Set V)) ∪ A 0 := by
    rintro (hz | hz)
    · rcases hz with (h | h) | h
      · exact notMem_S hH (show (2 : Fin 3) ≠ 0 by decide)
          (Or.inl (Or.inl ha₃)) (Or.inl (Or.inr h))
      · exact notMem_S hH (show (2 : Fin 3) ≠ 0 by decide)
          (Or.inl (Or.inl ha₃)) (Or.inr h)
      · rw [show a₃ = b₂ from h] at ha₃
        exact notMem_S hH (show (1 : Fin 3) ≠ 2 by decide)
          (Or.inl (Or.inr hb₂)) (Or.inl (Or.inl ha₃))
    · exact dl (hH.2.2.2.2.1 2 0 (by decide)) ha₃ hz
  have ha₃compl : VertexComplete G a₃ (A 0) :=
    complete_A hH (show (2 : Fin 3) ≠ 0 by decide) a₃ ha₃
  have ha₃anti : VertexAnticomplete G a₃ (B 0 ∪ C 0 ∪ ({b₂} : Set V)) := by
    intro z hz hadj
    have key : ∀ (l : Fin 3), (2 : Fin 3) ≠ l → z ∈ B l ∪ C l → False := by
      intro l hl hzl
      have hzS : z ∈ A l ∪ B l ∪ C l := by
        rcases hzl with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      rcases cross hH hl (show a₃ ∈ A 2 ∪ B 2 ∪ C 2 from Or.inl (Or.inl ha₃)) hzS hadj with
        ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hzl with h | h
        · exact dl (hH.2.1 l l) h2 h
        · exact dl (hH.2.2.1 l l) h2 h
      · exact dl (hH.2.1 2 2) ha₃ h1
    rcases hz with (h | h) | h
    · exact key 0 (by decide) (Or.inl h)
    · exact key 0 (by decide) (Or.inr h)
    · exact key 1 (by decide) (Or.inl (by rw [show z = b₂ from h]; exact hb₂))
  have hbal26 : SPGT.Balanced G (B 0 ∪ C 0 ∪ ({b₂} : Set V)) (A 0) :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hG (B 0 ∪ C 0 ∪ ({b₂} : Set V)) (A 0)
      hDdisj a₃ ha₃out ha₃compl ha₃anti
  ------------------------------------------------------------------
  -- Step 3: *"and so by 2.7.1, so is `(A₁, F)`"*.
  ------------------------------------------------------------------
  have hFsub : F ⊆ ((B 0 ∪ C 0 ∪ ({b₂} : Set V)) ∪ A 0)ᶜ := by
    intro z hz hcon
    refine hFH z hz ?_
    rcases hcon with h | h
    · exact hDH z h
    · exact hAH 0 z h
  have hDantiF : Anticomplete G (B 0 ∪ C 0 ∪ ({b₂} : Set V)) F := by
    intro d hd f hf hadj
    exact hDA d hd
      (hatt (show d ∈ attachments G F (hyperVerts A B C) from ⟨hDH d hd, f, hf, hadj⟩))
  have hbal27 : SPGT.Balanced G F (A 0) :=
    (_root_.Workspace.Statements.S02.SPGT.thm_2_7 G hG
      (B 0 ∪ C 0 ∪ ({b₂} : Set V)) (A 0) hbal26 F hFsub).1 hDconn hDattach hDantiF
  ------------------------------------------------------------------
  -- Step 4: *"By 4.5, `G` admits a balanced skew partition"*.
  ------------------------------------------------------------------
  -- `X = A₂ ∪ A₃`, `Y = A₁`, `L = F`, `R = V(G) \ (A ∪ F)`.
  have hXH : ∀ z ∈ A 1 ∪ A 2, z ∈ A 0 ∪ A 1 ∪ A 2 := by
    rintro z (h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hcover :
      (A 1 ∪ A 2) ∪ A 0 ∪ F ∪ ((A 0 ∪ A 1 ∪ A 2) ∪ F)ᶜ = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_univ, iff_true]
    tauto
  refine _root_.Workspace.Statements.S04.SPGT.thm_4_5 G hG (A 1 ∪ A 2) (A 0) F
    ((A 0 ∪ A 1 ∪ A 2) ∪ F)ᶜ hcover ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hFne ?_ ?_ ?_
    (Or.inr (Or.inr hbal27))
  · -- `Disjoint (A₂ ∪ A₃) A₁`
    refine Set.disjoint_left.mpr ?_
    rintro z (h | h) hz0
    · exact dl (hH.2.2.2.2.1 1 0 (by decide)) h hz0
    · exact dl (hH.2.2.2.2.1 2 0 (by decide)) h hz0
  · -- `Disjoint (A₂ ∪ A₃) F`
    refine Set.disjoint_left.mpr ?_
    rintro z (h | h) hzF
    · exact hFH z hzF (hAH 1 z h)
    · exact hFH z hzF (hAH 2 z h)
  · -- `Disjoint (A₂ ∪ A₃) R`
    exact Set.disjoint_left.mpr fun z hz hzR => hzR (Or.inl (hXH z hz))
  · -- `Disjoint A₁ F`
    exact Set.disjoint_left.mpr fun z hz hzF => hFH z hzF (hAH 0 z hz)
  · -- `Disjoint A₁ R`
    exact Set.disjoint_left.mpr fun z hz hzR => hzR (Or.inl (Or.inl (Or.inl hz)))
  · -- `Disjoint F R`
    exact Set.disjoint_left.mpr fun z hz hzR => hzR (Or.inr hz)
  · -- `A₂ ∪ A₃` is nonempty
    obtain ⟨z, hz⟩ := (hH.1 1).1
    exact ⟨z, Or.inl hz⟩
  · -- `A₁` is nonempty
    exact (hH.1 0).1
  · -- `R` is nonempty
    refine ⟨b₂, ?_⟩
    rintro (h | h)
    · exact hb₂A h
    · exact hFH b₂ h (hBH 1 b₂ hb₂)
  · -- there are no edges between `F` and `R`
    intro f hf z hz hadj
    refine hz ?_
    by_cases hzH : z ∈ hyperVerts A B C
    · exact Or.inl
        (hatt (show z ∈ attachments G F (hyperVerts A B C) from ⟨hzH, f, hf, hadj.symm⟩))
    · refine Or.inr ?_
      have hconn : ConnectedSet G (F ∪ ({z} : Set V)) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨f, hf, hadj.symm⟩
      have hsub : F ∪ ({z} : Set V) ⊆ (hyperVerts A B C)ᶜ := by
        rintro u (hu | hu)
        · exact hF.1 hu
        · rw [show u = z from hu]; exact hzH
      have heq := hF.2.2 (F ∪ ({z} : Set V)) Set.subset_union_left hsub hconn
      rw [← heq]
      exact Or.inr rfl
  · -- `A₂ ∪ A₃` is complete to `A₁`
    rintro z (hz | hz)
    · exact complete_A hH (show (1 : Fin 3) ≠ 0 by decide) z hz
    · exact complete_A hH (show (2 : Fin 3) ≠ 0 by decide) z hz

/-- **Claim (3) of the printed proof of 10.6, for the `B`-side** (printed p. 62): *"So we may
assume there is no such `F`, and the same for `B`."*

Obtained by re-running the `A`-argument on the hyperprism with its `A`-family and `B`-family
exchanged (`isHyperprism_swap`), which has the same `V(H)`. -/
theorem admitsBalancedSkewPartition_of_attachments_subset_B [Fintype V] [DecidableEq V]
    (hG : Berge G) (hH : IsHyperprism G A B C) {F : Set V}
    (hF : IsComponent G (hyperVerts A B C)ᶜ F) (hFne : F.Nonempty)
    (hatt : attachments G F (hyperVerts A B C) ⊆ B 0 ∪ B 1 ∪ B 2) :
    AdmitsBalancedSkewPartition G := by
  have hV : hyperVerts B A C = hyperVerts A B C := hyperVerts_swap A B C
  refine admitsBalancedSkewPartition_of_attachments_subset_A hG (isHyperprism_swap hH)
    (F := F) ?_ hFne ?_
  · rw [hV]; exact hF
  · rw [hV]; exact hatt

end Workspace.ProofLemmas.HyperprismSkewFromSide
