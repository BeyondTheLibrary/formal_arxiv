import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# The rung-end dictionary for a choice of rungs forming `L(H)`

PAPER (printed p. 39, the prose immediately following the proof of 8.1): *"For each edge `uv` of
`J`, choose a `uv`-rung `R_uv`.  It follows from 8.1 and the final axiom above that the subgraph
of `G` induced on the union of the vertex sets of these rungs is a line graph of a bipartite
subdivision `H` of `J`."*

PAPER (printed p. 20, recorded there as a fact about subdivisions and used silently throughout
Section 8): *"If `H` is a subdivision of `J` then `V(J)` is the set of branch-vertices of `H`."*

Because the paper *builds* `H` out of the chosen rungs, it may afterwards write `u` for both a
vertex of `J` and the corresponding branch-vertex of `H`, and write `delta_H(u)` for the set of
edges of `H` at that branch-vertex -- one for each `J`-neighbour `v` of `u` -- identifying the
edge indexed by `v` with the vertex of `G` at the **`u`-end** of the rung `R_uv`.

## How the proof recovers the dictionary

`FormsLineGraph` carries no compatibility clause tying the subdivision or the isomorphism to
the rungs, so both have to be *produced*.  The route below uses no result of the paper beyond
the strip-system axioms themselves.

1. Let `s_uv` be the `u`-end of `R_uv` (the unique vertex of the rung in `N_u`), and let
   `E u v` be the edge of `H` that the isomorphism sends to `s_uv`.  Clause 6 of the conclusion
   then holds *by construction*.
2. For `v != v'` the strips `S_uv`, `S_uv'` are disjoint, so `s_uv != s_uv'`, so
   `E u v != E u v'` -- this is the injectivity clause.
3. The sixth axiom of a strip system makes `N_u ∩ S_uv` complete to `N_u ∩ S_uv'`, so the edges
   `E u v` (`v` a neighbour of `u`) pairwise meet in `H`.  `J` is 3-connected, so there are at
   least three of them; `H` is bipartite, so they cannot form a triangle, and therefore they
   share a common vertex `ι u`.  Every `E u v` contains it.
4. `ι u` has at least three neighbours in `H`, so it is a branch-vertex; and `ι` is injective,
   because a repetition would put two rung-ends belonging to strips on *disjoint* edges of `J`
   into a common edge of `H`, hence make them adjacent in `G`, contrary to the fifth axiom.
5. `H` is a subdivision of `J`, so its branch-vertices are exactly the images of `V(J)` under
   the subdivision's own labelling; comparing cardinalities gives `range ι = branchVertices H`.
6. Finally the two degree counts are squeezed:
   `deg_J(u) <= deg_H(ι u)` by step 3, while `deg_H(ι₀ p) <= deg_J(p)` because every edge of `H`
   at a branch-vertex is the first edge of one of the subdivision's tracks.  Summing over `V(J)`
   -- the two indexings differ by a permutation -- forces equality everywhere, so the injection
   `v ↦ E u v` from the `J`-neighbours of `u` into `delta_H(ι u)` is onto.  That is clause 4.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm84RungEndDictionary


open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.SubdivisionCounting

section Counting

variable {α : Type*} [Finite α]

theorem exists_two_mem {s : Set α} (hs : 2 ≤ s.ncard) : ∃ a b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  obtain ⟨a, ha⟩ : s.Nonempty := by rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hc : (s \ {a}).ncard = s.ncard - 1 := Set.ncard_diff_singleton_of_mem ha
  obtain ⟨b, hb⟩ : (s \ {a}).Nonempty := by rw [← Set.ncard_pos (Set.toFinite _)]; omega
  exact ⟨a, b, ha, hb.1, fun h => hb.2 (by rw [← h]; rfl)⟩

theorem two_le_ncard_diff {s : Set α} {a : α} (hs : 3 ≤ s.ncard) : 2 ≤ (s \ {a}).ncard := by
  by_cases h : a ∈ s
  · rw [Set.ncard_diff_singleton_of_mem h]; omega
  · rw [Set.diff_singleton_eq_self h]; omega

end Counting

section GeneralGraph

variable {W : Type*} {H : SimpleGraph W}

/-- Two distinct vertices lying on the same `Sym2` pin it down. -/
theorem eq_sym2_of_mem_mem {a b : W} {e : Sym2 W} (hab : a ≠ b) (ha : a ∈ e) (hb : b ∈ e) :
    e = s(a, b) := (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩

/-- A bipartite graph has no triangle. -/
theorem no_triangle_of_bipartite (hbip : H.IsBipartite) {a b c : W}
    (hab : H.Adj a b) (hbc : H.Adj b c) (hac : H.Adj a c) : False := by
  obtain ⟨col⟩ := hbip
  have h1 : col a ≠ col b := col.valid hab
  have h2 : col b ≠ col c := col.valid hbc
  have h3 : col a ≠ col c := col.valid hac
  have e1 : (col a : ℕ) ≠ (col b : ℕ) := fun h => h1 (Fin.ext h)
  have e2 : (col b : ℕ) ≠ (col c : ℕ) := fun h => h2 (Fin.ext h)
  have e3 : (col a : ℕ) ≠ (col c : ℕ) := fun h => h3 (Fin.ext h)
  have l1 := (col a).isLt
  have l2 := (col b).isLt
  have l3 := (col c).isLt
  omega

/-- The two ends of an edge of `H` are distinct. -/
theorem ne_of_mem_edge {a b : W} {e : Sym2 W} (he : e ∈ H.edgeSet) (hab : e = s(a, b)) :
    a ≠ b := by
  subst hab
  exact (SimpleGraph.mem_edgeSet _).mp he |>.ne

/-- Two distinct edges of `H` share at most one vertex. -/
theorem subsingleton_inter_of_ne {e f : Sym2 W} (hef : e ≠ f) {a b : W}
    (ha : a ∈ e) (ha' : a ∈ f) (hb : b ∈ e) (hb' : b ∈ f) : a = b := by
  by_contra hab
  exact hef ((eq_sym2_of_mem_mem hab ha hb).trans (eq_sym2_of_mem_mem hab ha' hb').symm)

/-- Three vertices on a single `Sym2` cannot be pairwise distinct. -/
theorem two_eq_of_three_mem {e : Sym2 W} {a b c : W} (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e) :
    a = b ∨ a = c ∨ b = c := by
  revert ha hb hc
  induction e using Sym2.ind with
  | _ p q => simp only [Sym2.mem_iff]; rintro (rfl | rfl) (rfl | rfl) (rfl | rfl) <;> tauto

/-- **Three pairwise-intersecting edges of a triangle-free graph share a vertex.** -/
theorem exists_common_of_three (hbip : H.IsBipartite) {e₁ e₂ e₃ : Sym2 W}
    (h1 : e₁ ∈ H.edgeSet) (h2 : e₂ ∈ H.edgeSet) (h3 : e₃ ∈ H.edgeSet)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (m12 : ∃ w, w ∈ e₁ ∧ w ∈ e₂) (m13 : ∃ w, w ∈ e₁ ∧ w ∈ e₃)
    (m23 : ∃ w, w ∈ e₂ ∧ w ∈ e₃) :
    ∃ w : W, w ∈ e₁ ∧ w ∈ e₂ ∧ w ∈ e₃ := by
  obtain ⟨a, ha1, ha2⟩ := m12
  obtain ⟨b, hb1, hb3⟩ := m13
  obtain ⟨c, hc2, hc3⟩ := m23
  by_cases hab : a = b
  · exact ⟨a, ha1, ha2, hab ▸ hb3⟩
  · exfalso
    have he1 : e₁ = s(a, b) := eq_sym2_of_mem_mem hab ha1 hb1
    have hca : c ≠ a := by
      rintro rfl
      exact h13 (he1.trans (eq_sym2_of_mem_mem hab hc3 hb3).symm)
    have hcb : c ≠ b := by
      rintro rfl
      exact h12 (he1.trans (eq_sym2_of_mem_mem hab ha2 hc2).symm)
    have he2 : e₂ = s(a, c) := eq_sym2_of_mem_mem (Ne.symm hca) ha2 hc2
    have he3 : e₃ = s(b, c) := eq_sym2_of_mem_mem (Ne.symm hcb) hb3 hc3
    refine no_triangle_of_bipartite hbip (a := a) (b := b) (c := c) ?_ ?_ ?_
    · exact (SimpleGraph.mem_edgeSet _).mp (he1 ▸ h1)
    · exact (SimpleGraph.mem_edgeSet _).mp (he3 ▸ h3)
    · exact (SimpleGraph.mem_edgeSet _).mp (he2 ▸ h2)

/-- **Once three pairwise-distinct edges share a vertex `w`, every edge meeting all three
contains `w`.** -/
theorem mem_of_meets_three {e₁ e₂ e₃ e : Sym2 W} {w : W}
    (h1 : e₁ ∈ H.edgeSet) (h2 : e₂ ∈ H.edgeSet) (h3 : e₃ ∈ H.edgeSet)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    (hw1 : w ∈ e₁) (hw2 : w ∈ e₂) (hw3 : w ∈ e₃)
    (m1 : ∃ x, x ∈ e ∧ x ∈ e₁) (m2 : ∃ x, x ∈ e ∧ x ∈ e₂)
    (m3 : ∃ x, x ∈ e ∧ x ∈ e₃) : w ∈ e := by
  by_contra hwe
  obtain ⟨x₁, hx1e, hx11⟩ := m1
  obtain ⟨x₂, hx2e, hx22⟩ := m2
  obtain ⟨x₃, hx3e, hx33⟩ := m3
  have hn1 : x₁ ≠ w := by rintro rfl; exact hwe hx1e
  have hn2 : x₂ ≠ w := by rintro rfl; exact hwe hx2e
  have hn3 : x₃ ≠ w := by rintro rfl; exact hwe hx3e
  have hE1 : e₁ = s(w, x₁) := eq_sym2_of_mem_mem (Ne.symm hn1) hw1 hx11
  have hE2 : e₂ = s(w, x₂) := eq_sym2_of_mem_mem (Ne.symm hn2) hw2 hx22
  have hE3 : e₃ = s(w, x₃) := eq_sym2_of_mem_mem (Ne.symm hn3) hw3 hx33
  rcases two_eq_of_three_mem hx1e hx2e hx3e with h | h | h
  · exact h12 (by rw [hE1, hE2, h])
  · exact h13 (by rw [hE1, hE3, h])
  · exact h23 (by rw [hE2, hE3, h])

/-- Every `Sym2` has a member. -/
theorem sym2_exists_mem (e : Sym2 W) : ∃ w : W, w ∈ e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

/-- `δ_H(w)` has as many members as `w` has neighbours. -/
theorem incidentEdges_ncard (w : W) :
    (incidentEdges H w).ncard = (H.neighborSet w).ncard := by
  have himg : incidentEdges H w = (fun x => s(w, x)) '' (H.neighborSet w) := by
    ext e
    constructor
    · rintro ⟨he, hw⟩
      obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hw
      exact ⟨x, (SimpleGraph.mem_edgeSet _).mp he, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(SimpleGraph.mem_edgeSet _).mpr hx, Sym2.mem_mk_left _ _⟩
  rw [himg]
  refine Set.ncard_image_of_injOn ?_
  intro a _ b _ hab
  exact (Sym2.congr_right).mp hab

/-- The last vertex of a track named by `IsTrackFrom`. -/
theorem track_getLast {q : List W} {a b : W} (h : IsTrackFrom H q a b) (hlen : 0 < q.length) :
    q[q.length - 1]'(by omega) = b := by
  have h' := h.2.2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
  exact Option.some_injective _ h'

end GeneralGraph

section SubdivisionDegree

variable {U W : Type*} [Finite U] {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W}
  {T : U → U → List W}

/-- **The degree of a branch-vertex of a subdivision is at most the degree in `J`.**

Every edge of `H` at `ι p` is the first edge of the track attached to an edge of `J` at `p`. -/
theorem degree_branch_le
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (p : U) :
    (H.neighborSet (ι p)).ncard ≤ (J.neighborSet p).ncard := by
  have hsub : H.neighborSet (ι p) ⊆
      (fun q => (T p q).getD 1 (ι p)) '' (J.neighborSet p) := by
    intro x hx
    have hxe : s(ι p, x) ∈ H.edgeSet := (SimpleGraph.mem_edgeSet _).mpr hx
    rw [hedges] at hxe
    simp only [Set.mem_iUnion] at hxe
    obtain ⟨c, d, hcd, i, hi, hie⟩ := hxe
    have hlen2 : 2 ≤ (T c d).length := by
      have := hlen c d hcd; simp only [trackLength] at this; omega
    rcases Sym2.eq_iff.mp hie with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · -- `ι p` is the `i`-th vertex; it must be the first
      have hi0 : i = 0 := by
        by_contra hne
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        exact hnew c d hcd _ (mem_trackInterior_getElem (T c d) j (by omega)) ⟨p, e1⟩
      subst hi0
      have hpc : p = c := hι (by rw [e1, track_head (htrack c d hcd) (by omega)])
      subst hpc
      refine ⟨d, hcd, ?_⟩
      show (T p d).getD 1 (ι p) = x
      rw [List.getD_eq_getElem _ _ (by omega), e2]
    · -- `ι p` is the `(i+1)`-st vertex; it must be the last
      have hilast : i + 2 = (T c d).length := by
        by_contra hne
        exact hnew c d hcd _ (mem_trackInterior_getElem (T c d) i (by omega)) ⟨p, e1⟩
      have hpd : p = d := by
        refine hι ?_
        rw [e1, ← track_getLast (htrack c d hcd) (by omega)]
        exact getElem_eq_of_index_eq (T c d) (by omega) _ _
      subst hpd
      refine ⟨c, hcd.symm, ?_⟩
      show (T p c).getD 1 (ι p) = x
      have hrv : (T p c) = (T c p).reverse := hrev c p hcd
      rw [List.getD_eq_getElem?_getD, hrv,
        List.getElem?_reverse (l := T c p) (i := 1) (by omega),
        show (T c p).length - 1 - 1 = i from by omega,
        List.getElem?_eq_getElem (show i < (T c p).length from by omega)]
      simp [e2]
  calc (H.neighborSet (ι p)).ncard
      ≤ ((fun q => (T p q).getD 1 (ι p)) '' (J.neighborSet p)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (J.neighborSet p).ncard := Set.ncard_image_le (Set.toFinite _)

end SubdivisionDegree

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem rungEndDictionary {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H) :
    ∃ (φ : H.lineGraph ≃g G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
      (ι : U → W) (E : U → U → Sym2 W),
      Function.Injective ι ∧
      Set.range ι = branchVertices H ∧
      (∀ u v : U, J.Adj u v → E u v ∈ H.edgeSet) ∧
      (∀ u : U, incidentEdges H (ι u) = {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = E u v}) ∧
      (∀ u v v' : U, J.Adj u v → J.Adj u v' → E u v = E u v' → v = v') ∧
      (∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
        IsPathFrom G (R u v) s t → (↑(φ ⟨E u v, he⟩) : V) = s) := by
  classical
  -- ## Setup
  set K : Set V := ⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b} with hK
  obtain ⟨hR, hbipsub, hiso⟩ := hForms
  obtain ⟨φ⟩ := hiso
  obtain ⟨hsub, hbip⟩ := hbipsub
  obtain ⟨ι₀, T, hι₀, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  -- every vertex of `J` has degree at least three
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    fun u => SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hUne : Nonempty U := by
    have := hJ.1
    exact Fintype.card_pos_iff.mp (by omega)
  -- ## The `u`-end of each rung
  have hhead : ∀ u v : U, J.Adj u v → ∃ s : V,
      (R u v).head? = some s ∧ s ∈ R u v ∧ s ∈ S u v ∧ s ∈ N u := by
    intro u v huv
    obtain ⟨-, s, t, hp, hsubR, hs, -⟩ := hR u v huv
    have hsR : s ∈ R u v := List.mem_of_mem_head? hp.2.1
    exact ⟨s, hp.2.1, hsR, hsubR s hsR, (hs s hsR).mpr rfl⟩
  have hVne : Nonempty V := by
    obtain ⟨u⟩ := hUne
    obtain ⟨v, hv⟩ : (J.neighborSet u).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; have := hdeg u; omega
    obtain ⟨s, -, -, -, -⟩ := hhead u v hv
    exact ⟨s⟩
  choose! sfun hsHead hsMem hsStrip hsN using hhead
  have hsK : ∀ u v : U, J.Adj u v → sfun u v ∈ K := by
    intro u v huv
    rw [hK]
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, v, huv, hsMem u v huv⟩
  -- ## The edge of `H` indexed by an edge of `J`
  obtain ⟨u₀⟩ := hUne
  set Emap : U → U → Sym2 W :=
    fun u v => if h : J.Adj u v then (↑(φ.symm ⟨sfun u v, hsK u v h⟩) : Sym2 W)
      else s(ι₀ u₀, ι₀ u₀) with hEmapDef
  have hEmap : ∀ (u v : U) (h : J.Adj u v),
      Emap u v = (↑(φ.symm ⟨sfun u v, hsK u v h⟩) : Sym2 W) := by
    intro u v h; rw [hEmapDef]; exact dif_pos h
  have hEedge : ∀ u v : U, J.Adj u v → Emap u v ∈ H.edgeSet := by
    intro u v h; rw [hEmap u v h]; exact (φ.symm ⟨sfun u v, hsK u v h⟩).2
  have hEφ : ∀ (u v : U) (h : J.Adj u v) (he : Emap u v ∈ H.edgeSet),
      (↑(φ ⟨Emap u v, he⟩) : V) = sfun u v := by
    intro u v h he
    have : (⟨Emap u v, he⟩ : H.edgeSet) = φ.symm ⟨sfun u v, hsK u v h⟩ :=
      Subtype.ext (hEmap u v h)
    rw [this, RelIso.apply_symm_apply]
  -- ## Distinct neighbours give distinct edges
  have hEdgeNe : ∀ u v v' : U, J.Adj u v → J.Adj u v' → v ≠ v' → s(u, v) ≠ s(u, v') := by
    intro u v v' huv huv' hne hcon
    rcases Sym2.eq_iff.mp hcon with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact hne h2
    · exact absurd huv (by rw [h2]; exact J.loopless.irrefl u)
  have hsne : ∀ u v v' : U, J.Adj u v → J.Adj u v' → v ≠ v' → sfun u v ≠ sfun u v' := by
    intro u v v' huv huv' hne hcon
    have hd := StripSystemBasics.strip_disjoint hSN huv huv' (hEdgeNe u v v' huv huv' hne)
    exact Set.disjoint_left.mp hd (hsStrip u v huv) (hcon ▸ hsStrip u v' huv')
  have hEne : ∀ u v v' : U, J.Adj u v → J.Adj u v' → v ≠ v' → Emap u v ≠ Emap u v' := by
    intro u v v' huv huv' hne heq
    have h1 : (φ.symm ⟨sfun u v, hsK u v huv⟩ : H.edgeSet)
        = φ.symm ⟨sfun u v', hsK u v' huv'⟩ :=
      Subtype.ext (by rw [← hEmap u v huv, ← hEmap u v' huv', heq])
    have h2 := congrArg Subtype.val (φ.symm.injective h1)
    exact hsne u v v' huv huv' hne h2
  -- ## Edges at a common `u` pairwise meet
  have hEmeet : ∀ u v v' : U, J.Adj u v → J.Adj u v' →
      ∃ w : W, w ∈ Emap u v ∧ w ∈ Emap u v' := by
    intro u v v' huv huv'
    rcases eq_or_ne v v' with rfl | hne
    · obtain ⟨w, hw⟩ := sym2_exists_mem (Emap u v)
      exact ⟨w, hw, hw⟩
    · have hadjG : G.Adj (sfun u v) (sfun u v') :=
        StripSystemBasics.Nuv_complete hSN huv huv' hne (sfun u v)
          ⟨hsN u v huv, hsStrip u v huv⟩ (sfun u v') ⟨hsN u v' huv', hsStrip u v' huv'⟩
      have hadjI : (G.induce K).Adj ⟨sfun u v, hsK u v huv⟩ ⟨sfun u v', hsK u v' huv'⟩ := hadjG
      have hadjL : H.lineGraph.Adj (φ.symm ⟨sfun u v, hsK u v huv⟩)
          (φ.symm ⟨sfun u v', hsK u v' huv'⟩) := φ.symm.map_rel_iff.mpr hadjI
      obtain ⟨-, w, hw1, hw2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadjL
      refine ⟨w, ?_, ?_⟩
      · rw [hEmap u v huv]; exact hw1
      · rw [hEmap u v' huv']; exact hw2
  -- ## The branch-vertex attached to `u`
  have hthree : ∀ u : U, ∃ v₁ v₂ v₃ : U, J.Adj u v₁ ∧ J.Adj u v₂ ∧ J.Adj u v₃ ∧
      v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
    intro u
    have hn := hdeg u
    obtain ⟨v₁, hv₁⟩ : (J.neighborSet u).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    have hc1 : (J.neighborSet u \ {v₁}).ncard = (J.neighborSet u).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem hv₁
    obtain ⟨v₂, hv₂⟩ : (J.neighborSet u \ {v₁}).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    have hc2 : ((J.neighborSet u \ {v₁}) \ {v₂}).ncard = (J.neighborSet u \ {v₁}).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem hv₂
    obtain ⟨v₃, hv₃⟩ : ((J.neighborSet u \ {v₁}) \ {v₂}).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    exact ⟨v₁, v₂, v₃, hv₁, hv₂.1, hv₃.1.1,
      fun h => hv₂.2 h.symm, fun h => hv₃.1.2 h.symm, fun h => hv₃.2 h.symm⟩
  have hIotaEx : ∀ u : U, ∃ w : W, ∀ v : U, J.Adj u v → w ∈ Emap u v := by
    intro u
    obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, h12, h13, h23⟩ := hthree u
    obtain ⟨w, hw1, hw2, hw3⟩ :=
      exists_common_of_three hbip (hEedge u v₁ hv₁) (hEedge u v₂ hv₂) (hEedge u v₃ hv₃)
        (hEne u v₁ v₂ hv₁ hv₂ h12) (hEne u v₁ v₃ hv₁ hv₃ h13) (hEne u v₂ v₃ hv₂ hv₃ h23)
        (hEmeet u v₁ v₂ hv₁ hv₂) (hEmeet u v₁ v₃ hv₁ hv₃) (hEmeet u v₂ v₃ hv₂ hv₃)
    refine ⟨w, fun v hv => ?_⟩
    exact mem_of_meets_three (hEedge u v₁ hv₁) (hEedge u v₂ hv₂) (hEedge u v₃ hv₃)
      (hEne u v₁ v₂ hv₁ hv₂ h12) (hEne u v₁ v₃ hv₁ hv₃ h13) (hEne u v₂ v₃ hv₂ hv₃ h23)
      hw1 hw2 hw3 (hEmeet u v v₁ hv hv₁) (hEmeet u v v₂ hv hv₂) (hEmeet u v v₃ hv hv₃)
  choose ι hιmem using hIotaEx
  -- the other end of `Emap u v`
  have hother : ∀ u v : U, J.Adj u v → ∃ x : W, Emap u v = s(ι u, x) := fun u v hv =>
    Sym2.mem_iff_exists.mp (hιmem u v hv)
  have hιbranch : ∀ u : U, ι u ∈ branchVertices H := by
    intro u
    obtain ⟨v₁, v₂, v₃, hv₁, hv₂, hv₃, h12, h13, h23⟩ := hthree u
    obtain ⟨x₁, hx₁⟩ := hother u v₁ hv₁
    obtain ⟨x₂, hx₂⟩ := hother u v₂ hv₂
    obtain ⟨x₃, hx₃⟩ := hother u v₃ hv₃
    have hadj : ∀ (v : U) (x : W), J.Adj u v → Emap u v = s(ι u, x) → H.Adj (ι u) x := by
      intro v x hv hx
      have := hEedge u v hv
      rw [hx] at this
      exact (SimpleGraph.mem_edgeSet _).mp this
    have hn12 : x₁ ≠ x₂ := by
      rintro rfl; exact hEne u v₁ v₂ hv₁ hv₂ h12 (hx₁.trans hx₂.symm)
    have hn13 : x₁ ≠ x₃ := by
      rintro rfl; exact hEne u v₁ v₃ hv₁ hv₃ h13 (hx₁.trans hx₃.symm)
    have hn23 : x₂ ≠ x₃ := by
      rintro rfl; exact hEne u v₂ v₃ hv₂ hv₃ h23 (hx₂.trans hx₃.symm)
    have hsubset : ({x₁, x₂, x₃} : Set W) ⊆ H.neighborSet (ι u) := by
      rintro y (rfl | rfl | rfl)
      · exact hadj v₁ _ hv₁ hx₁
      · exact hadj v₂ _ hv₂ hx₂
      · exact hadj v₃ _ hv₃ hx₃
    have hcard3 : ({x₁, x₂, x₃} : Set W).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨x₁, x₂, x₃, hn12, hn13, hn23, rfl⟩
    show 3 ≤ (H.neighborSet (ι u)).ncard
    calc (3 : ℕ) = ({x₁, x₂, x₃} : Set W).ncard := hcard3.symm
      _ ≤ (H.neighborSet (ι u)).ncard := Set.ncard_le_ncard hsubset (Set.toFinite _)
  have hιinj : Function.Injective ι := by
    intro u u' heq
    by_contra hne
    -- choose neighbours making `[u, v, u', w]` a `Nodup` list
    obtain ⟨v₁, v₂, hv₁, hv₂, h12⟩ :=
      exists_two_mem (two_le_ncard_diff (a := u') (hdeg u))
    obtain ⟨w₁, w₂, hw₁, hw₂, hw12⟩ :=
      exists_two_mem (two_le_ncard_diff (a := u) (hdeg u'))
    obtain ⟨v, w, hvmem, hwmem, hvw⟩ :
        ∃ v w : U, v ∈ J.neighborSet u \ {u'} ∧ w ∈ J.neighborSet u' \ {u} ∧ v ≠ w := by
      by_cases hc : v₁ = w₁
      · exact ⟨v₁, w₂, hv₁, hw₂, by rw [hc]; exact hw12⟩
      · exact ⟨v₁, w₁, hv₁, hw₁, hc⟩
    have huv : J.Adj u v := hvmem.1
    have hu'w : J.Adj u' w := hwmem.1
    have hvu' : v ≠ u' := fun h => hvmem.2 (by rw [h]; rfl)
    have hwu : w ≠ u := fun h => hwmem.2 (by rw [h]; rfl)
    have hnd : [u, v, u', w].Nodup := by
      have e1 : u ≠ v := huv.ne
      have e2 : u' ≠ w := hu'w.ne
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
        not_or, ne_eq]
      have e3 : u ≠ w := Ne.symm hwu
      have e4 : u ≠ u' := hne
      have e5 : v ≠ u' := hvu'
      have e6 : v ≠ w := hvw
      tauto
    -- the two rung-ends are in strips on disjoint edges of `J`, hence nonadjacent
    have hnotadj : ¬ G.Adj (sfun u v) (sfun u' w) :=
      StripSystemBasics.not_adj_of_disjoint_edges hSN huv hu'w hnd
        (hsStrip u v huv) (hsStrip u' w hu'w)
    have hsdiff : sfun u v ≠ sfun u' w := by
      intro hcon
      have hsymne : s(u, v) ≠ s(u', w) := by
        intro hcon2
        rcases Sym2.eq_iff.mp hcon2 with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hne h1
        · exact hwu h1.symm
      exact Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN huv hu'w hsymne)
        (hsStrip u v huv) (hcon ▸ hsStrip u' w hu'w)
    have hEdgeNe2 : (φ.symm ⟨sfun u v, hsK u v huv⟩ : H.edgeSet)
        ≠ φ.symm ⟨sfun u' w, hsK u' w hu'w⟩ := by
      intro hcon
      exact hsdiff (congrArg Subtype.val (φ.symm.injective hcon))
    have hmem1 : ι u ∈ ((φ.symm ⟨sfun u v, hsK u v huv⟩ : H.edgeSet) : Sym2 W) := by
      rw [← hEmap u v huv]; exact hιmem u v huv
    have hmem2 : ι u ∈ ((φ.symm ⟨sfun u' w, hsK u' w hu'w⟩ : H.edgeSet) : Sym2 W) := by
      rw [← hEmap u' w hu'w, heq]; exact hιmem u' w hu'w
    have hadjL : H.lineGraph.Adj (φ.symm ⟨sfun u v, hsK u v huv⟩)
        (φ.symm ⟨sfun u' w, hsK u' w hu'w⟩) :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hEdgeNe2, ι u, hmem1, hmem2⟩
    exact hnotadj (φ.symm.map_rel_iff.mp hadjL)
  have hbranchrange : branchVertices H = Set.range ι₀ :=
    Set.Subset.antisymm
      (SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges)
      (SubdivisionCounting.range_subset_branchVertices hι₀ htrack hlen hdisjint hnew hdeg)
  have hrangecard : ∀ f : U → W, Function.Injective f → (Set.range f).ncard = Nat.card U := by
    intro f hf
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hf, Set.ncard_univ]
  have hrange : Set.range ι = branchVertices H := by
    refine Set.eq_of_subset_of_ncard_le (fun w hw => ?_) ?_ (Set.toFinite _)
    · obtain ⟨u, rfl⟩ := hw
      exact hιbranch u
    · rw [hbranchrange, hrangecard ι₀ hι₀, hrangecard ι hιinj]
  -- ## Counting
  have hincl : ∀ u : U, {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = Emap u v} ⊆
      incidentEdges H (ι u) := by
    rintro u e ⟨v, hv, rfl⟩
    exact ⟨hEedge u v hv, hιmem u v hv⟩
  have hinjOn : ∀ u : U, Set.InjOn (Emap u) (J.neighborSet u) := by
    intro u v hv v' hv' heq
    by_contra h
    exact hEne u v v' hv hv' h heq
  have hle : ∀ u : U, (J.neighborSet u).ncard ≤ (H.neighborSet (ι u)).ncard := by
    intro u
    rw [← incidentEdges_ncard (H := H) (ι u)]
    exact Set.ncard_le_ncard_of_injOn (Emap u)
      (fun v hv => ⟨hEedge u v hv, hιmem u v hv⟩) (hinjOn u) (Set.toFinite _)
  -- the permutation of `V(J)` matching `ι` to the subdivision's own labelling
  have hsigmaEx : ∀ u : U, ∃ p : U, ι₀ p = ι u := by
    intro u
    have : ι u ∈ Set.range ι₀ := by rw [← hbranchrange]; exact hιbranch u
    exact this
  choose σ hσ using hsigmaEx
  have hσinj : Function.Injective σ := by
    intro a b hab
    exact hιinj (by rw [← hσ a, ← hσ b, hab])
  have hσbij : Function.Bijective σ := (Finite.injective_iff_bijective).mp hσinj
  have hsum : ∑ u : U, (H.neighborSet (ι u)).ncard
      = ∑ p : U, (H.neighborSet (ι₀ p)).ncard := by
    refine Fintype.sum_bijective σ hσbij _ _ ?_
    intro u
    rw [hσ u]
  have hsumle : ∑ u : U, (J.neighborSet u).ncard = ∑ u : U, (H.neighborSet (ι u)).ncard := by
    refine le_antisymm (Finset.sum_le_sum fun u _ => hle u) ?_
    rw [hsum]
    exact Finset.sum_le_sum fun p _ =>
      degree_branch_le hι₀ htrack hlen hrev hnew hedges p
  have hdegeq : ∀ u : U, (J.neighborSet u).ncard = (H.neighborSet (ι u)).ncard := by
    intro u
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsumle u (Finset.mem_univ u)
  have hcount : ∀ u : U, (incidentEdges H (ι u)).ncard = (J.neighborSet u).ncard := by
    intro u
    rw [incidentEdges_ncard, ← hdegeq u]
  have himg : ∀ u : U, {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = Emap u v}
      = (Emap u) '' (J.neighborSet u) := by
    intro u
    ext e
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨v, hv, rfl⟩
  refine ⟨φ, ι, Emap, hιinj, hrange, hEedge, ?_, ?_, ?_⟩
  · intro u
    refine (Set.eq_of_subset_of_ncard_le (hincl u) ?_ (Set.toFinite _)).symm
    rw [himg u, Set.ncard_image_of_injOn (hinjOn u), hcount u]
  · intro u v v' huv huv' heq
    by_contra hne
    exact hEne u v v' huv huv' hne heq
  · intro u v huv he s t hst
    rw [hEφ u v huv he]
    have h1 : (R u v).head? = some (sfun u v) := hsHead u v huv
    have h2 : (R u v).head? = some s := hst.2.1
    exact Option.some_injective _ (h1.symm.trans h2)

end Main

end Workspace.ProofLemmas.Thm84RungEndDictionary

