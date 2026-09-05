import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose

/-!
# A cyclically 3-connected graph has no cutvertex, and its components have two attachments

The closing paragraph of the proof of 5.3 (printed p. 20) asserts, with no proof and no
citation:

> *"Suppose that there is a component `F` of `H \ V(J)`.  Since `H` is cyclically
> 3-connected, at least two vertices of `J` are attachments of `F`."*

Here `J` is a subgraph of `H` isomorphic to `K₃,₃`, so `V(J)` has six vertices.  The content of
the sentence is that a cyclically 3-connected graph has **no cutvertex**: deleting one vertex
leaves it connected.  Nothing in this file corresponds to a numbered result of the paper.

## The general fact

`CyclicallyThreeConnected H` unfolds to *"`H` is a subdivision of some 3-connected `J₀`"*, and
`Workspace.Types.Tracks.SPGT.IsKConnected J₀ 3` says in particular that deleting any single
vertex of `J₀` leaves it connected.  Connectivity is pushed from `J₀` up to `H` along the
subdivision: a walk of `J₀` avoiding a vertex expands, track by track, into a walk of `H`
avoiding the corresponding vertex.

Note carefully that `H` itself is **not** 3-connected — an internal vertex of a track has
degree `2`, so deleting its two neighbours isolates it.  What survives is 2-connectedness:
`connectedSet_compl_of_subsingleton` deletes at most one vertex, and that is best possible.

The two vertex classes of `H` behave differently and the proof splits accordingly:

* deleting a **branch-vertex** `ι u₀` leaves every track between two other branch-vertices
  intact, and `J₀ - u₀` is connected because `J₀` is 3-connected;
* deleting a **track-interior** vertex `v` of the track attached to the edge `u₀u₀'` of `J₀`
  breaks only that one track, and `J₀` minus the *edge* `u₀u₀'` is still connected — which is
  where 3-connectedness is used a second time, via *"every vertex of `J₀` has degree ≥ 3"*, to
  route out of `u₀` along some other edge.

## The attachment corollary

`two_attachments_of_component`: if `F` is a nonempty component of `Sᶜ` and `2 ≤ |S|`, then at
least two vertices of `S` have a neighbour in `F`.  Indeed if the attachment set `Att` had at
most one element, `H - Att` would be connected, while `F` is closed under `H`-adjacency inside
`Sᶜ` (maximality of the component) and inside `S \ Att` there is nothing adjacent to it — so
`Sᶜ ∪ (S \ Att) = Attᶜ` would be exhausted by `F`, forcing `S ⊆ Att` and `|S| ≤ 1`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.CyclicThreeConnectedAttachments

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {W : Type*}

/-! ### Reachability inside a prescribed set of vertices -/

/-- `RchIn H X a b` — both `a` and `b` lie in `X`, and they are joined by a walk of `H` all of
whose vertices lie in `X`.  This is `(H.induce X).Reachable` with the two subtype membership
proofs existentially quantified, which makes it composable without carrying them around. -/
def RchIn (H : SimpleGraph W) (X : Set W) (a b : W) : Prop :=
  ∃ (ha : a ∈ X) (hb : b ∈ X), (H.induce X).Reachable ⟨a, ha⟩ ⟨b, hb⟩

section Basic

variable {H : SimpleGraph W} {X : Set W} {a b c : W}

theorem RchIn.mem_left (h : RchIn H X a b) : a ∈ X := by
  obtain ⟨ha, -, -⟩ := h; exact ha

theorem RchIn.mem_right (h : RchIn H X a b) : b ∈ X := by
  obtain ⟨-, hb, -⟩ := h; exact hb

theorem RchIn.refl (ha : a ∈ X) : RchIn H X a a :=
  ⟨ha, ha, SimpleGraph.Reachable.refl _⟩

theorem RchIn.symm (h : RchIn H X a b) : RchIn H X b a := by
  obtain ⟨ha, hb, hr⟩ := h
  exact ⟨hb, ha, hr.symm⟩

theorem RchIn.trans (h₁ : RchIn H X a b) (h₂ : RchIn H X b c) : RchIn H X a c := by
  obtain ⟨ha, hb, hr₁⟩ := h₁
  obtain ⟨hb', hc, hr₂⟩ := h₂
  exact ⟨ha, hc, hr₁.trans hr₂⟩

theorem RchIn.of_adj (ha : a ∈ X) (hb : b ∈ X) (hadj : H.Adj a b) : RchIn H X a b :=
  ⟨ha, hb, SimpleGraph.Adj.reachable hadj⟩

end Basic

/-! ### Building `RchIn` out of chains and walks -/

section Build

variable {H : SimpleGraph W} {X : Set W}

private theorem rchIn_of_chain_head :
    ∀ (t : List W) (x : W), List.IsChain H.Adj (x :: t) →
      (∀ z ∈ x :: t, z ∈ X) → ∀ b ∈ x :: t, RchIn H X x b := by
  intro t
  induction t with
  | nil =>
    intro x _ hX b hb
    have hbx : b = x := by simpa using hb
    rw [hbx]
    exact RchIn.refl (hX x (by simp))
  | cons y rest ih =>
    intro x hch hX b hb
    have hxX : x ∈ X := hX x (by simp)
    have hyX : y ∈ X := hX y (by simp)
    rcases List.mem_cons.mp hb with hbx | hb'
    · rw [hbx]
      exact RchIn.refl hxX
    · exact (RchIn.of_adj hxX hyX hch.rel_head).trans
        (ih y hch.tail (fun z hz => hX z (List.mem_cons_of_mem _ hz)) b hb')

/-- Any two vertices of a chain contained in `X` are `RchIn`-connected. -/
theorem rchIn_of_chain (q : List W) (hch : List.IsChain H.Adj q)
    (hX : ∀ z ∈ q, z ∈ X) {a b : W} (ha : a ∈ q) (hb : b ∈ q) : RchIn H X a b := by
  cases q with
  | nil => simp at ha
  | cons x t =>
    exact (rchIn_of_chain_head t x hch hX a ha).symm.trans
      (rchIn_of_chain_head t x hch hX b hb)

/-- Transport a walk of an auxiliary graph `K` along a map `f` whose image lies in `X` and
which sends edges of `K` to `RchIn`-connections. -/
theorem rchIn_of_walk {U : Type*} {K : SimpleGraph U} (f : U → W)
    (hmem : ∀ z : U, f z ∈ X) (hedge : ∀ z w : U, K.Adj z w → RchIn H X (f z) (f w))
    {x y : U} (p : K.Walk x y) : RchIn H X (f x) (f y) := by
  induction p with
  | nil => exact RchIn.refl (hmem _)
  | cons hadj _ ih => exact (hedge _ _ hadj).trans ih

end Build

/-! ### Splitting a track at the deleted vertex

If at most one vertex is deleted, a track keeps a connected piece containing at least one of
its two ends, and every surviving vertex of the track is in one of those pieces. -/

/-- Let `A` contain at most one vertex.  Every vertex `w` of a track (a `Nodup` chain) that is
not in `A` is joined, inside the complement of `A`, to one of the two ends of the track. -/
theorem rchIn_track_of_mem {H : SimpleGraph W} {A : Set W} (hA : A.Subsingleton) {q : List W}
    (hch : List.IsChain H.Adj q) (hnd : q.Nodup) {e₁ e₂ : W}
    (hhead : q.head? = some e₁) (hlast : q.getLast? = some e₂)
    {w : W} (hwq : w ∈ q) (hwA : w ∉ A) :
    RchIn H Aᶜ w e₁ ∨ RchIn H Aᶜ w e₂ := by
  by_cases hdis : ∃ z ∈ q, z ∈ A
  · obtain ⟨z, hzq, hzA⟩ := hdis
    have hAz : ∀ a ∈ A, a = z := fun a ha => hA ha hzA
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hzq
    have hnd' := List.nodup_append.mp hnd
    have hzs : z ∉ s := fun hz => hnd'.2.2 z hz z List.mem_cons_self rfl
    have hzt : z ∉ t := (List.nodup_cons.mp hnd'.2.1).1
    rcases List.mem_append.mp hwq with hws | hwt
    · left
      have hus : e₁ ∈ s := by
        cases s with
        | nil => exact absurd hws (by simp)
        | cons a s' =>
          have hae : a = e₁ := by simpa using hhead
          rw [← hae]
          exact List.mem_cons_self
      refine rchIn_of_chain s hch.left_of_append ?_ hws hus
      intro y hy hyA
      exact hzs (hAz y hyA ▸ hy)
    · rcases List.mem_cons.mp hwt with hwz | hwt'
      · exact absurd (by rw [hwz]; exact hzA) hwA
      · right
        have htne : t ≠ [] := List.ne_nil_of_mem hwt'
        have hlast' : t.getLast? = some e₂ := by
          rw [List.getLast?_append_of_ne_nil s (List.cons_ne_nil z t),
            List.getLast?_cons_of_ne_nil htne] at hlast
          exact hlast
        refine rchIn_of_chain t hch.right_of_append.tail ?_ hwt'
          (List.mem_of_getLast? hlast')
        intro y hy hyA
        exact hzt (hAz y hyA ▸ hy)
  · left
    refine rchIn_of_chain q hch ?_ hwq (List.mem_of_head? hhead)
    intro y hy hyA
    exact hdis ⟨y, hy, hyA⟩

/-! ### Pushing connectivity of the subdivided graph up to its subdivision -/

section Branch

variable {H : SimpleGraph W} {X : Set W} {n : ℕ} {J : SimpleGraph (Fin n)}

/-- All branch-vertices other than `ι u₀` are `RchIn`-connected, given that every edge of `J`
avoiding `u₀` gives an `RchIn`-connection. -/
theorem branch_avoiding (hJ : IsKConnected J 3) (ι : Fin n → W) (u₀ : Fin n)
    (hmem : ∀ u : Fin n, u ≠ u₀ → ι u ∈ X)
    (hedge : ∀ z w : Fin n, J.Adj z w → z ≠ u₀ → w ≠ u₀ → RchIn H X (ι z) (ι w))
    {x y : Fin n} (hx : x ≠ u₀) (hy : y ≠ u₀) : RchIn H X (ι x) (ι y) := by
  have hc : (J.induce (({u₀} : Set (Fin n))ᶜ)).Connected :=
    hJ.2 ({u₀} : Set (Fin n)) (by rw [Set.ncard_singleton]; omega)
  obtain ⟨p⟩ := hc.preconnected ⟨x, hx⟩ ⟨y, hy⟩
  exact rchIn_of_walk (H := H) (X := X) (fun z : ↥(({u₀} : Set (Fin n))ᶜ) => ι (z : Fin n))
    (fun z => hmem _ z.2) (fun z w hzw => hedge z.1 w.1 hzw z.2 w.2) p

/-- All branch-vertices are `RchIn`-connected, given that every edge of `J` other than `cd`
gives an `RchIn`-connection.  The extra work over `branch_avoiding` is routing out of `c`:
`c` has degree `≥ 3` in `J`, so it has a neighbour other than `d`. -/
theorem branch_all (hJ : IsKConnected J 3) (ι : Fin n → W) (c d : Fin n)
    (hmem : ∀ u : Fin n, ι u ∈ X)
    (hedge : ∀ z w : Fin n, J.Adj z w → s(z, w) ≠ s(c, d) → RchIn H X (ι z) (ι w))
    (x y : Fin n) : RchIn H X (ι x) (ι y) := by
  have hgen : ∀ x' y' : Fin n, x' ≠ c → y' ≠ c → RchIn H X (ι x') (ι y') := by
    intro x' y' hx' hy'
    refine branch_avoiding hJ ι c (fun u _ => hmem u) ?_ hx' hy'
    intro z w hzw hz hw
    refine hedge z w hzw ?_
    intro he
    rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hz h1
    · exact hw h2
  obtain ⟨z, hzn, hzd⟩ : ∃ z : Fin n, J.Adj c z ∧ z ≠ d := by
    have h3 := SubdivisionCounting.three_le_degree_of_three_connected J hJ c
    obtain ⟨z, hz, hzd⟩ :=
      Set.exists_ne_of_one_lt_ncard (s := J.neighborSet c) (by omega) d
    exact ⟨z, hz, hzd⟩
  have hczr : RchIn H X (ι c) (ι z) := by
    refine hedge c z hzn ?_
    intro he
    rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact hzd h2
    · exact hzn.ne h2.symm
  have hzc : z ≠ c := hzn.ne'
  by_cases hx : x = c
  · by_cases hy : y = c
    · rw [hx, hy]
      exact RchIn.refl (hmem c)
    · rw [hx]
      exact hczr.trans (hgen z y hzc hy)
  · by_cases hy : y = c
    · rw [hy]
      exact (hczr.trans (hgen z x hzc hx)).symm
    · exact hgen x y hx hy

end Branch

/-! ### The main connectivity theorem -/

/-- **A cyclically 3-connected graph stays connected after deleting at most one vertex.**

This is the general fact behind the paper's *"Since `H` is cyclically 3-connected, at least two
vertices of `J` are attachments of `F`"* (5.3, printed p. 20).  `A` is the deleted set; it is
assumed to have at most one element (`A = ∅` is allowed and gives plain connectedness). -/
theorem connectedSet_compl_of_subsingleton {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) {A : Set W} (hA : A.Subsingleton) :
    ConnectedSet H Aᶜ := by
  obtain ⟨n, J, hJ, ι, T, hinj, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hc3
  have hn3 : 3 < n := by
    have h := hJ.1
    rwa [Fintype.card_fin] at h
  -- basic facts about the tracks of the subdivision
  have htrchain : ∀ x y : Fin n, J.Adj x y → List.IsChain H.Adj (T x y) := fun x y h =>
    List.isChain_iff_getElem.mpr (htrack x y h).1.2.2
  have htrnd : ∀ x y : Fin n, J.Adj x y → (T x y).Nodup := fun x y h => (htrack x y h).1.2.1
  have htrhead : ∀ x y : Fin n, J.Adj x y → (T x y).head? = some (ι x) := fun x y h =>
    (htrack x y h).2.1
  have htrlast : ∀ x y : Fin n, J.Adj x y → (T x y).getLast? = some (ι y) := fun x y h =>
    (htrack x y h).2.2
  -- every surviving vertex reaches a surviving branch-vertex
  have hreduce : ∀ w : W, w ∉ A → ∃ x : Fin n, RchIn H Aᶜ w (ι x) := by
    intro w hw
    rcases hcover w with ⟨x, hx⟩ | ⟨x, y, hxy, hint⟩
    · refine ⟨x, ?_⟩
      rw [← hx]
      exact RchIn.refl hw
    · have hwq : w ∈ T x y := SubdivisionCompose.mem_of_mem_trackInterior hint
      rcases rchIn_track_of_mem hA (htrchain x y hxy) (htrnd x y hxy)
        (htrhead x y hxy) (htrlast x y hxy) hwq hw with h | h
      · exact ⟨x, h⟩
      · exact ⟨y, h⟩
  -- all surviving branch-vertices are joined to each other
  have hbranch : ∀ x y : Fin n, ι x ∈ (Aᶜ : Set W) → ι y ∈ (Aᶜ : Set W) →
      RchIn H Aᶜ (ι x) (ι y) := by
    rcases hA.eq_empty_or_singleton with rfl | ⟨v, rfl⟩
    · -- nothing is deleted
      intro x y _ _
      refine branch_all hJ ι ⟨0, by omega⟩ ⟨0, by omega⟩ (fun u => by simp) ?_ x y
      intro z w hzw _
      refine rchIn_of_chain (T z w) (htrchain z w hzw) ?_
        (List.mem_of_head? (htrhead z w hzw)) (List.mem_of_getLast? (htrlast z w hzw))
      intro a _ ha
      simp at ha
    · by_cases hvr : v ∈ Set.range ι
      · -- the deleted vertex is a branch-vertex
        obtain ⟨u₀, hu₀⟩ := hvr
        intro x y hxX hyX
        have hbr : ∀ u : Fin n, ι u ∈ (({v} : Set W)ᶜ) → u ≠ u₀ := by
          intro u hu hcon
          exact hu (Set.mem_singleton_iff.mpr (by rw [hcon]; exact hu₀))
        refine branch_avoiding hJ ι u₀ ?_ ?_ (hbr x hxX) (hbr y hyX)
        · intro u hu hcon
          exact hu (hinj ((Set.mem_singleton_iff.mp hcon).trans hu₀.symm))
        · intro z w hzw hz hw
          refine rchIn_of_chain (T z w) (htrchain z w hzw) ?_
            (List.mem_of_head? (htrhead z w hzw)) (List.mem_of_getLast? (htrlast z w hzw))
          intro a ha hacon
          have hav : a = v := Set.mem_singleton_iff.mp hacon
          by_cases hintr : a ∈ trackInterior (T z w)
          · exact hnew z w hzw a hintr ⟨u₀, hu₀.trans hav.symm⟩
          · rcases SubdivisionCompose.mem_ends_of_mem (htrhead z w hzw) (htrlast z w hzw)
              ha hintr with h | h
            · exact hz (hinj (h.symm.trans (hav.trans hu₀.symm)))
            · exact hw (hinj (h.symm.trans (hav.trans hu₀.symm)))
      · -- the deleted vertex is internal to a track
        rcases hcover v with ⟨u, hu⟩ | ⟨c, d, hcd, hvint⟩
        · exact absurd ⟨u, hu.symm⟩ hvr
        intro x y _ _
        refine branch_all hJ ι c d ?_ ?_ x y
        · intro u hcon
          exact hvr ⟨u, Set.mem_singleton_iff.mp hcon⟩
        · intro z w hzw hne
          have hvnot : v ∉ T z w := hdisj c d z w hcd hzw (Ne.symm hne) v hvint
          refine rchIn_of_chain (T z w) (htrchain z w hzw) ?_
            (List.mem_of_head? (htrhead z w hzw)) (List.mem_of_getLast? (htrlast z w hzw))
          intro a ha hacon
          exact hvnot (Set.mem_singleton_iff.mp hacon ▸ ha)
  -- assemble
  intro pp qq
  obtain ⟨x, hxr⟩ := hreduce (pp : W) pp.2
  obtain ⟨y, hyr⟩ := hreduce (qq : W) qq.2
  have hfin : RchIn H Aᶜ (pp : W) (qq : W) :=
    hxr.trans ((hbranch x y hxr.mem_right hyr.mem_right).trans hyr.symm)
  obtain ⟨h1, h2, hr⟩ := hfin
  exact hr

/-- **A cyclically 3-connected graph has no cutvertex.** -/
theorem no_cutvertex_of_cyclicallyThreeConnected {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) (v : W) : ConnectedSet H (({v} : Set W)ᶜ) :=
  connectedSet_compl_of_subsingleton hc3 Set.subsingleton_singleton

/-- The `ncard` phrasing of `connectedSet_compl_of_subsingleton`. -/
theorem connectedSet_compl_of_ncard_le_one [Finite W] {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) {A : Set W} (hA : A.ncard ≤ 1) :
    ConnectedSet H Aᶜ :=
  connectedSet_compl_of_subsingleton hc3 (Set.ncard_le_one_iff_subsingleton.mp hA)

/-- A cyclically 3-connected graph is connected. -/
theorem connectedSet_univ_of_cyclicallyThreeConnected {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) : ConnectedSet H (Set.univ : Set W) := by
  have h := connectedSet_compl_of_subsingleton hc3 (A := (∅ : Set W)) Set.subsingleton_empty
  rwa [Set.compl_empty] at h

/-- A cyclically 3-connected graph is preconnected. -/
theorem preconnected_of_cyclicallyThreeConnected {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) : H.Preconnected := by
  intro a b
  obtain ⟨p⟩ := connectedSet_univ_of_cyclicallyThreeConnected hc3
    ⟨a, Set.mem_univ a⟩ ⟨b, Set.mem_univ b⟩
  exact ⟨p.map (⟨fun z => (z : W), fun {_ _} h => h⟩ :
    (H.induce (Set.univ : Set W)) →g H)⟩

/-! ### The attachment corollary -/

/-- **At least two vertices of `S` are attachments of a component of `Sᶜ`.**

This is the paper's *"Since `H` is cyclically 3-connected, at least two vertices of `J` are
attachments of `F`"* (closing paragraph of the proof of 5.3), with `S = V(J)`.  The two side
conditions are exactly what the argument needs and what the call site supplies: the component
is nonempty, and `S` has at least two vertices (in 5.3 it has six). -/
theorem two_attachments_of_component [Finite W] {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) (S F : Set W)
    (hF : IsComponent H Sᶜ F) (hFne : F.Nonempty) (hS : 2 ≤ S.ncard) :
    2 ≤ {w ∈ S | ∃ f ∈ F, H.Adj f w}.ncard := by
  by_contra hcon
  obtain ⟨Att, hAtt⟩ : ∃ Y : Set W, Y = {w ∈ S | ∃ f ∈ F, H.Adj f w} := ⟨_, rfl⟩
  have hmemAtt : ∀ y : W, y ∈ Att ↔ (y ∈ S ∧ ∃ f ∈ F, H.Adj f y) := by
    rw [hAtt]; intro y; exact Iff.rfl
  rw [← hAtt] at hcon
  have hle : Att.ncard ≤ 1 := by omega
  have hconn : ConnectedSet H Attᶜ := connectedSet_compl_of_ncard_le_one hc3 hle
  have hAttS : Att ⊆ S := fun w hw => ((hmemAtt w).mp hw).1
  have hFS : F ⊆ Sᶜ := hF.1
  have hFA : ∀ f, f ∈ F → f ∈ (Attᶜ : Set W) := fun f hf hfA => hFS hf (hAttS hfA)
  -- `F` is closed under `H`-adjacency inside the complement of the attachments
  have hclosed : ∀ x, x ∈ F → ∀ y, y ∈ (Attᶜ : Set W) → H.Adj x y → y ∈ F := by
    intro x hx y hy hadj
    by_cases hyS : y ∈ S
    · exact absurd ((hmemAtt y).mpr ⟨hyS, x, hx, hadj⟩) hy
    · have hconn' : ConnectedSet H (F ∪ {y}) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨x, hx, hadj.symm⟩
      have heq : F ∪ {y} = F :=
        hF.2.2 (F ∪ {y}) Set.subset_union_left
          (Set.union_subset hFS (Set.singleton_subset_iff.mpr hyS)) hconn'
      have hy' : y ∈ F ∪ {y} := Or.inr rfl
      rwa [heq] at hy'
  -- hence everything outside the attachments lies in `F`
  have hstay : ∀ (a b : ↥(Attᶜ : Set W)) (_ : (H.induce (Attᶜ : Set W)).Walk a b),
      (a : W) ∈ F → (b : W) ∈ F := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons u v w hadj _ ih => exact fun hu => ih (hclosed (u : W) hu (v : W) v.2 hadj)
  obtain ⟨f₀, hf₀⟩ := hFne
  have hall : ∀ z : ↥(Attᶜ : Set W), (z : W) ∈ F := by
    intro z
    obtain ⟨p⟩ := hconn ⟨f₀, hFA f₀ hf₀⟩ z
    exact hstay _ _ p hf₀
  have hSA : S ⊆ Att := by
    intro w hw
    by_contra hwA
    exact hFS (hall ⟨w, hwA⟩) hw
  have hcard := Set.ncard_le_ncard hSA (Set.toFinite _)
  omega

end Workspace.ProofLemmas.CyclicThreeConnectedAttachments
