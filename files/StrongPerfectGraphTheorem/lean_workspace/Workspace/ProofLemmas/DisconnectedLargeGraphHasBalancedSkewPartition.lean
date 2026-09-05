import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Statements.S04.Thm_4_1

/-!
# A disconnected Berge graph on at least eight vertices has a balanced skew partition

PAPER (9.6, printed p. 55, the closing paragraph):

> *"Then `M₀, M₁, …, M_n` are pairwise disjoint and have union `M`.  **If `M₀` is nonempty then
> `G` is not connected, and since `|V(G)| ≥ 8` it therefore admits a balanced skew partition**,
> so we may assume that `M₀` is empty."*

This module states the emphasised sentence as a standalone lemma.  It is the missing ingredient
of the first `sorry` of `Workspace.ProofLemmas.Thm96Body.closing`: nothing of this shape exists
anywhere in `Workspace/ProofLemmas` — `SkewPartitionFromSeparator` only builds skew partitions
from a *separator* `X ∪ {X-complete vertices}`, never from disconnectedness.  The vocabulary
here (`ConnectedSet`, `AdmitsBalancedSkewPartition`) is that module's.

## The one hypothesis the printed sentence omits: `G` has an edge

The sentence as printed is **false** without the extra hypothesis `∃ u v, G.Adj u v`.  Take `G`
edgeless on eight vertices.  It is Berge (neither `G` nor `Ḡ = K₈` has any hole), it is not
connected, and `|V(G)| = 8`; but `Ḡ` is complete, so *every* subset of `V(G)` is anticonnected
and `G` admits no skew partition at all, balanced or otherwise.  See `AMBIGUITIES.md`.

In the situation of 9.6 the extra hypothesis is free: `G` contains a striation, and the rungs
of `S₁` are paths of odd (hence nonzero) length, so `V(S₁)` carries an edge.  The hypothesis is
therefore recorded here rather than smuggled in, and the calling site of `Thm96Body.closing`
supplies it from `IsStriation`.

## Why the three hypotheses suffice (the argument the authors compress into "therefore")

Let `uv` be an edge of `G`, in the component `C`.  Put `B = {u,v}` and `A = V(G) \ {u,v}`.  `B`
is not anticonnected (`u,v` are nonadjacent in `Ḡ`), so `(A,B)` is a skew partition as soon as
`A` is not connected, and then 4.1 applies — `{u}` is an anticomponent of `B` with one vertex —
giving a *balanced* skew partition.  `A` is not connected except when `G` has exactly two
components and `C = {u,v}`; in that case the other component `D` has `|D| ≥ 6` and is connected,
so it has an edge `xy`, and `({u,v} ∪ (D \ {x,y}), {x,y})` is a skew partition instead (`{u,v}`
is anticomplete to `D`, and `D \ {x,y} ≠ ∅`).  This is where `|V(G)| ≥ 8` is used.

## How the Lean proof below is organised

`key` is the common core: *any* edge `xy` such that two vertices `p, q` outside `{x,y}` are not
`G`-reachable from one another yields `(({x,y})ᶜ, {x,y})` as a skew partition, and `{x}` is an
anticomponent of `{x,y}` with one vertex, so 4.1 upgrades it to a balanced one.

The main proof supplies `key` with such a configuration.  Write `C` for the component of `u`.

* If `C` has a vertex `w ∉ {u,v}` — take the edge `uv`, `p := w` and `q :=` any vertex outside
  `C` (one exists because `G` is not connected).
* Otherwise `C = {u,v}`, so *every* vertex outside `{u,v}` is unreachable from `u`.
  * If some edge `xy` avoids `{u,v}` — take that edge, `p := u`, and `q` any of the `≥ 4`
    remaining vertices (this is the use of `|V(G)| ≥ 8`).
  * If no edge avoids `{u,v}` — every vertex `p ∉ {u,v}` is isolated (a neighbour inside
    `{u,v}` would put `p` in `C`), so take the edge `uv` and any two distinct `p, q ∉ {u,v}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.DisconnectedLargeGraphHasBalancedSkewPartition

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

/-! ### Bookkeeping helpers

None of this is in the paper; it is what the authors' *"therefore"* stands for. -/

section Helpers

variable {W : Type*}

/-- The inclusion of an induced subgraph into the ambient graph, as a graph homomorphism.
Used to push reachability inside `G|X` up to reachability in `G`. -/
private def valHom (H : SimpleGraph W) (X : Set W) : H.induce X →g H where
  toFun := Subtype.val
  map_rel' := fun h => h

/-- The identification of `G` with `G|V(G)`, as a graph homomorphism.  Used to turn a
`G`-walk into a `G|V(G)`-walk, so that `¬ ConnectedSet G Set.univ` yields two vertices that
are not `G`-reachable. -/
private def univHom (H : SimpleGraph W) : H →g H.induce (Set.univ : Set W) where
  toFun v := ⟨v, trivial⟩
  map_rel' := fun h => h

private theorem eq_of_reachable_isolated {H : SimpleGraph W} {a b : W}
    (hiso : ∀ z, ¬ H.Adj a z) (h : H.Reachable a b) : a = b := by
  obtain ⟨wk⟩ := h
  cases wk with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

/-- A set containing two distinct vertices one of which has no neighbour inside it is not
connected. -/
private theorem not_connectedSet_of_isolated {H : SimpleGraph W} {X : Set W} {a b : W}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) (hiso : ∀ z ∈ X, ¬ H.Adj a z) :
    ¬ ConnectedSet H X := by
  intro h
  have h' : (⟨a, ha⟩ : ↥X) = ⟨b, hb⟩ :=
    eq_of_reachable_isolated (fun z hz => hiso z.1 z.2 hz) (h ⟨a, ha⟩ ⟨b, hb⟩)
  exact hab (congrArg Subtype.val h')

/-- A list shorter than the vertex set misses a vertex. -/
private theorem exists_avoiding {W : Type*} [Fintype W] [DecidableEq W] (l : List W)
    (h : l.length < Fintype.card W) : ∃ q : W, q ∉ l := by
  by_contra hcon
  push_neg at hcon
  have hsub : (Finset.univ : Finset W) ⊆ l.toFinset := fun a _ => List.mem_toFinset.mpr (hcon a)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ] at h1
  have h2 := l.toFinset_card_le
  omega

end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The common core.**  If `xy` is an edge and two vertices `p, q` outside `{x,y}` are not
`G`-reachable from one another, then `((({x,y} : Set V))ᶜ, {x,y})` is a skew partition of `G`
whose second side has an anticomponent with one vertex, so 4.1 makes `G` admit a *balanced*
skew partition. -/
private theorem key {G : SimpleGraph V} (hB : Berge G)
    (x y : V) (hxy : G.Adj x y) (p q : V)
    (hpx : p ≠ x) (hpy : p ≠ y) (hqx : q ≠ x) (hqy : q ≠ y)
    (hnr : ¬ G.Reachable p q) : AdmitsBalancedSkewPartition G := by
  -- the only `Gᶜ`-edge that could exist inside `{x,y}` is `xy`, and `xy ∈ E(G)`
  have hnoedge : ∀ D : Set V, D ⊆ ({x, y} : Set V) → ∀ z ∈ D, ¬ Gᶜ.Adj x z := by
    intro D hD z hz hadj
    rcases (show z = x ∨ z = y from hD hz) with h | h
    · rw [h] at hadj; exact hadj.ne rfl
    · rw [h] at hadj; exact ((SimpleGraph.compl_adj G x y).mp hadj).2 hxy
  -- `A = {x,y}ᶜ` is not connected: it contains the unreachable pair `p, q`
  have hnotconn : ¬ ConnectedSet G (({x, y} : Set V)ᶜ) := by
    intro h
    have hp : p ∈ (({x, y} : Set V)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨hpx, hpy⟩
    have hq : q ∈ (({x, y} : Set V)ᶜ) := by
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨hqx, hqy⟩
    exact hnr (SimpleGraph.Reachable.map (valHom G _) (h ⟨p, hp⟩ ⟨q, hq⟩))
  -- `B = {x,y}` is not anticonnected: `x` has no `Gᶜ`-neighbour inside it
  have hnac : ¬ AnticonnectedSet G ({x, y} : Set V) :=
    not_connectedSet_of_isolated (H := Gᶜ) (show x ∈ ({x, y} : Set V) by simp)
      (show y ∈ ({x, y} : Set V) by simp) hxy.ne (hnoedge _ (subset_refl _))
  have hskew : IsSkewPartition G (({x, y} : Set V)ᶜ) ({x, y} : Set V) :=
    ⟨Set.compl_union_self _, disjoint_compl_left, hnotconn, hnac⟩
  -- `{x}` is an anticomponent of `{x,y}`
  have hcomp : IsAnticomponent G ({x, y} : Set V) ({x} : Set V) := by
    refine ⟨fun a ha => Or.inl ha, ?_, ?_⟩
    · intro a b
      have hab : a = b :=
        Subtype.ext ((show (a : V) = x from a.2).trans (show (b : V) = x from b.2).symm)
      rw [hab]
    · intro D hD1 hD2 hD3
      have hyD : y ∉ D := by
        intro hyD
        exact not_connectedSet_of_isolated (H := Gᶜ) (X := D) (hD1 rfl) hyD hxy.ne
          (hnoedge D hD2) hD3
      ext a
      constructor
      · intro haD
        rcases (show a = x ∨ a = y from hD2 haD) with h | h
        · exact h
        · rw [h] at haD; exact absurd haD hyD
      · intro ha
        exact hD1 ha
  exact _root_.Workspace.Statements.S04.SPGT.thm_4_1 G hB _ _ hskew
    (Or.inr ⟨({x} : Set V), hcomp, x, rfl⟩)

/-- **PAPER (9.6, printed p. 55):** *"If `M₀` is nonempty then `G` is not connected, and since
`|V(G)| ≥ 8` it therefore admits a balanced skew partition."*

`G` not connected is `¬ ConnectedSet G Set.univ` (`Core.ConnectedSet` is
`(G.induce X).Preconnected`), and `|V(G)| ≥ 8` is `8 ≤ Nat.card V`, both exactly as in
`Thm96Body.Setup`.

The hypothesis `hedge : ∃ u v, G.Adj u v` is not printed; without it the sentence is false (see
the module doc-comment).  `Berge G` is needed because the conclusion is a *balanced* skew
partition, obtained from the constructed skew partition by 4.1, which assumes `G` Berge. -/
theorem admitsBalancedSkewPartition_of_not_connected
    (G : SimpleGraph V) (hB : Berge G)
    (hcard : 8 ≤ Nat.card V)
    (hedge : ∃ u v : V, G.Adj u v)
    (hdisc : ¬ ConnectedSet G (Set.univ : Set V)) :
    AdmitsBalancedSkewPartition G := by
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨u, v, huv⟩ := hedge
  -- "G is not connected": two vertices of `G` that are not joined by a walk
  obtain ⟨p₀, q₀, hpq⟩ : ∃ a b : V, ¬ G.Reachable a b := by
    rw [ConnectedSet, SimpleGraph.Preconnected] at hdisc
    push_neg at hdisc
    obtain ⟨a, b, hab⟩ := hdisc
    exact ⟨a.1, b.1, fun h => hab (SimpleGraph.Reachable.map (univHom G) h)⟩
  -- some vertex is outside the component of `u`
  obtain ⟨z, hz⟩ : ∃ z : V, ¬ G.Reachable u z := by
    by_contra hcon
    push_neg at hcon
    exact hpq ((hcon p₀).symm.trans (hcon q₀))
  have hzu : z ≠ u := by
    intro h; rw [h] at hz; exact hz (SimpleGraph.Reachable.refl u)
  have hzv : z ≠ v := by
    intro h; rw [h] at hz; exact hz huv.reachable
  by_cases hcase1 : ∃ w : V, G.Reachable u w ∧ w ≠ u ∧ w ≠ v
  · -- the component of `u` has a third vertex `w`: `({u,v}ᶜ, {u,v})` already works
    obtain ⟨w, hw, hwu, hwv⟩ := hcase1
    exact key hB u v huv w z hwu hwv hzu hzv (fun hr => hz (hw.trans hr))
  · -- the component of `u` is exactly `{u,v}`
    push_neg at hcase1
    by_cases hcase2 : ∃ x y : V, G.Adj x y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v
    · -- there is an edge `xy` away from `{u,v}`: use `({x,y}ᶜ, {x,y})` instead
      obtain ⟨x, y, hxy, hxu, hxv, hyu, hyv⟩ := hcase2
      obtain ⟨q, hq⟩ := exists_avoiding [u, v, x, y] (by simp; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      obtain ⟨hqu, hqv, hqx, hqy⟩ := hq
      refine key hB x y hxy u q (Ne.symm hxu) (Ne.symm hyu) hqx hqy ?_
      intro hr
      exact hqv (hcase1 q hr hqu)
    · -- no edge avoids `{u,v}`, so every vertex outside `{u,v}` is isolated
      push_neg at hcase2
      obtain ⟨p, hp⟩ := exists_avoiding [u, v] (by simp; omega)
      obtain ⟨q, hq⟩ := exists_avoiding [u, v, p] (by simp; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hp hq
      obtain ⟨hpu, hpv⟩ := hp
      obtain ⟨hqu, hqv, hqp⟩ := hq
      have hiso : ∀ w : V, ¬ G.Adj p w := by
        intro w hadj
        have hwu : w ≠ u := by
          intro hwe
          rw [hwe] at hadj
          exact hpv (hcase1 p hadj.symm.reachable hpu)
        have hwv : w = v := hcase2 p w hadj hpu hpv hwu
        rw [hwv] at hadj
        exact hpv (hcase1 p (huv.reachable.trans hadj.symm.reachable) hpu)
      refine key hB u v huv p q hpu hpv hqu hqv ?_
      intro hr
      exact hqp (eq_of_reachable_isolated hiso hr).symm

end Workspace.ProofLemmas.DisconnectedLargeGraphHasBalancedSkewPartition
