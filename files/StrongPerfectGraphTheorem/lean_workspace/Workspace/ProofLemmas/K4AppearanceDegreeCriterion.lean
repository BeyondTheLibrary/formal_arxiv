import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.LineGraphDegree
import Workspace.ProofLemmas.K4AppearanceEightVertices
import Workspace.ProofLemmas.K4TrackLengthDegeneracy

/-!
# A degree criterion excluding an appearance of `K₄`

If every eight-or-more-element vertex subset `K` of `Gx` contains a vertex whose number of
neighbours inside `K` is `< 2` or `> 4`, then `K₄` does not appear in `Gx`.

The reason.  An appearance of `K₄` is a bipartite subdivision `H` of `K₄`, a set `K : Set V` and
an isomorphism `φ : L(H) ≃g Gx|K`.

* `K4AppearanceEightVertices.eight_le_ncard_of_isAppearance` gives `8 ≤ K.ncard`, so the
  hypothesis applies to `K` and produces a bad vertex `v ∈ K`.
* Every vertex of `H` has degree `2` or `3`: degree `≥ 2` is
  `LineGraphDegree.two_le_degree_of_isSubdivision`, and degree `≤ 3` is
  `degree_le_three_of_isSubdivision` below (a branch-vertex `ι u` has one neighbour per track
  at `u`, and a track-interior vertex is not a branch-vertex by
  `SubdivisionCounting.branchVertices_subset_range`).
* Hence every vertex `e = s(a,b)` of `L(H)` has `L(H)`-degree between `2` and `4`
  (`lineGraph_degree_bounds`): its neighbours are the other edges at `a` and the other edges
  at `b`.
* `φ` preserves degrees, and the `Gx|K`-degree of a vertex `v ∈ K` is `(Gx.neighborSet v ∩ K).ncard`.

So every `v ∈ K` has between `2` and `4` neighbours inside `K`, contradicting the choice of `v`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.K4AppearanceDegreeCriterion

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

/-! ## Degrees in a subdivision -/

/-- **Every vertex of a subdivision of a graph of maximum degree `≤ 3` has degree `≤ 3`.**

A vertex of `H` is either an old vertex `ι u` — whose `H`-neighbours are the second vertices of
the tracks issuing from `u`, one per `J`-neighbour of `u` — or an internal vertex of a track,
which is not a branch-vertex of `H` at all. -/
theorem degree_le_three_of_isSubdivision {U W : Type*} [Finite U] {J : SimpleGraph U}
    {H : SimpleGraph W}
    (hsub : IsSubdivision J H) (hdeg : ∀ u : U, (J.neighborSet u).ncard ≤ 3) (w : W) :
    (H.neighborSet w).ncard ≤ 3 := by
  obtain ⟨ι, T, hinj, htrack, hlen, hrev, hdisj, hnew, hcover, hedge⟩ := hsub
  have hlen2 : ∀ p q : U, J.Adj p q → 2 ≤ (T p q).length := by
    intro p q hpq
    have := hlen p q hpq
    simp only [trackLength] at this
    omega
  -- the second vertex of the track `T p q` is the unique `H`-neighbour of `ι p` on it
  have hsecond : ∀ p q : U, J.Adj p q → ∀ x : W, s(ι p, x) ∈ trackEdges (T p q) →
      x = (T p q).getD 1 (ι p) := by
    intro p q hpq x hx
    obtain ⟨i, hi, heq⟩ := hx
    have h2 := hlen2 p q hpq
    have h0 : (T p q)[0]'(by omega) = ι p := track_head (htrack p q hpq) (by omega)
    have hnd : (T p q).Nodup := (htrack p q hpq).1.2.1
    rw [List.getD_eq_getElem _ _ (by omega)]
    rcases Sym2.eq_iff.mp heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hi0 : (0 : ℕ) = i := (hnd.getElem_inj_iff).mp (h0.trans e1)
      subst hi0
      exact e2
    · exfalso
      have : (0 : ℕ) = i + 1 := (hnd.getElem_inj_iff).mp (h0.trans e1)
      omega
  -- the last vertex of `T p q` is `ι q`
  have hlast : ∀ p q : U, ∀ _ : J.Adj p q, ∀ (h : 0 < (T p q).length),
      (T p q)[(T p q).length - 1]'(by omega) = ι q := by
    intro p q hpq h
    have h' := (htrack p q hpq).2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  rcases hcover w with ⟨u, rfl⟩ | ⟨u, v, huv, hw⟩
  · -- `w = ι u`
    have hkey : H.neighborSet (ι u) ⊆
        (fun v => (T u v).getD 1 (ι u)) '' (J.neighborSet u) := by
      intro x hx
      have hxe : s(ι u, x) ∈ H.edgeSet := (SimpleGraph.mem_edgeSet _).mpr hx
      rw [hedge] at hxe
      simp only [Set.mem_iUnion] at hxe
      obtain ⟨u', v', hu'v', hmem⟩ := hxe
      obtain ⟨i, hi, heq⟩ := hmem
      have h2 := hlen2 u' v' hu'v'
      have hnd : (T u' v').Nodup := (htrack u' v' hu'v').1.2.1
      rcases Sym2.eq_iff.mp heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · -- `ι u = (T u' v')[i]`; if `i ≠ 0` this is an internal vertex, impossible
        have hi0 : i = 0 := by
          by_contra hne
          obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          exact hnew u' v' hu'v' _ (mem_trackInterior_getElem _ j (by omega)) ⟨u, e1⟩
        subst hi0
        have h0 : (T u' v')[0]'(by omega) = ι u' := track_head (htrack u' v' hu'v') (by omega)
        have huu' : u = u' := hinj (e1.trans h0)
        subst huu'
        refine ⟨v', hu'v', ?_⟩
        exact (hsecond u v' hu'v' x ⟨0, hi, heq⟩).symm
      · -- `ι u = (T u' v')[i+1]`; if `i + 2 < length` this is an internal vertex
        have hend : i + 2 = (T u' v').length := by
          by_contra hne
          exact hnew u' v' hu'v' _ (mem_trackInterior_getElem _ i (by omega)) ⟨u, e1⟩
        have hlst : (T u' v')[i + 1]'(by omega) = ι v' := by
          rw [getElem_eq_of_index_eq _ (show i + 1 = (T u' v').length - 1 by omega)
            (by omega) (by omega)]
          exact hlast u' v' hu'v' (by omega)
        have huv' : u = v' := hinj (e1.trans hlst)
        subst huv'
        refine ⟨u', hu'v'.symm, ?_⟩
        have hrevmem : s(ι u, x) ∈ trackEdges (T u u') := by
          rw [hrev u' u hu'v', trackEdges_reverse]
          exact ⟨i, hi, heq⟩
        exact (hsecond u u' hu'v'.symm x hrevmem).symm
    calc (H.neighborSet (ι u)).ncard
        ≤ ((fun v => (T u v).getD 1 (ι u)) '' (J.neighborSet u)).ncard :=
          Set.ncard_le_ncard hkey (Set.Finite.image _ (Set.toFinite _))
      _ ≤ (J.neighborSet u).ncard := Set.ncard_image_le (Set.toFinite _)
      _ ≤ 3 := hdeg u
  · -- `w` is an internal vertex of a track, hence not a branch-vertex
    by_contra hcon
    have h3 : 3 ≤ (H.neighborSet w).ncard := by omega
    have hwb : w ∈ branchVertices H := h3
    have := branchVertices_subset_range htrack hrev hdisj hcover hedge hwb
    exact hnew u v huv w hw this

/-! ## Degrees in the line graph -/

section LineGraph

variable {W : Type*} {H : SimpleGraph W}

/-- The `L(H)`-neighbours of `s(a,b)`, listed by their far end: each is an edge `s(a,x)` with
`x` a neighbour of `a` other than `b`, or an edge `s(b,y)` with `y` a neighbour of `b` other
than `a`. -/
theorem lineGraph_neighborSet_val_subset {a b : W} (hab : s(a, b) ∈ H.edgeSet) :
    Subtype.val '' (H.lineGraph.neighborSet ⟨s(a, b), hab⟩) ⊆
      (fun x => s(a, x)) '' (H.neighborSet a \ {b}) ∪
      (fun y => s(b, y)) '' (H.neighborSet b \ {a}) := by
  rintro z ⟨f, hf, rfl⟩
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.lineGraph_adj_iff_exists] at hf
  obtain ⟨hne, w, hw1, hw2⟩ := hf
  have hw1' : w = a ∨ w = b := Sym2.mem_iff.mp hw1
  rcases hw1' with rfl | rfl
  · obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hw2
    have hyadj : H.Adj w y := by
      have := f.2
      rw [hy] at this
      exact this
    have hyb : y ≠ b := by
      rintro rfl
      exact hne (Subtype.ext hy.symm)
    exact Or.inl ⟨y, ⟨hyadj, hyb⟩, hy.symm⟩
  · obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hw2
    have hyadj : H.Adj w y := by
      have := f.2
      rw [hy] at this
      exact this
    have hya : y ≠ a := by
      rintro rfl
      exact hne (Subtype.ext (by rw [hy]; exact Sym2.eq_swap))
    exact Or.inr ⟨y, ⟨hyadj, hya⟩, hy.symm⟩

/-- **The `L(H)`-degree of an edge is at most `deg(a) - 1 + deg(b) - 1`**, hence at most `4`
when `H` has maximum degree `3`. -/
theorem lineGraph_degree_le_four [Fintype W] {a b : W} (hab : s(a, b) ∈ H.edgeSet)
    (hha : (H.neighborSet a).ncard ≤ 3) (hhb : (H.neighborSet b).ncard ≤ 3) :
    (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).ncard ≤ 4 := by
  have hadj : H.Adj a b := hab
  have hbmem : b ∈ H.neighborSet a := hadj
  have hamem : a ∈ H.neighborSet b := hadj.symm
  have hval : (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).ncard
      = (Subtype.val '' (H.lineGraph.neighborSet ⟨s(a, b), hab⟩)).ncard :=
    (Set.ncard_image_of_injective _ Subtype.val_injective).symm
  have hA : ((fun x => s(a, x)) '' (H.neighborSet a \ {b})).ncard ≤ 2 := by
    have h1 : ((fun x => s(a, x)) '' (H.neighborSet a \ {b})).ncard
        ≤ (H.neighborSet a \ {b}).ncard := Set.ncard_image_le (Set.toFinite _)
    have h2 : (H.neighborSet a \ {b}).ncard = (H.neighborSet a).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem hbmem
    omega
  have hB : ((fun y => s(b, y)) '' (H.neighborSet b \ {a})).ncard ≤ 2 := by
    have h1 : ((fun y => s(b, y)) '' (H.neighborSet b \ {a})).ncard
        ≤ (H.neighborSet b \ {a}).ncard := Set.ncard_image_le (Set.toFinite _)
    have h2 : (H.neighborSet b \ {a}).ncard = (H.neighborSet b).ncard - 1 :=
      Set.ncard_diff_singleton_of_mem hamem
    omega
  have hsub := lineGraph_neighborSet_val_subset hab
  have hle : (Subtype.val '' (H.lineGraph.neighborSet ⟨s(a, b), hab⟩)).ncard
      ≤ ((fun x => s(a, x)) '' (H.neighborSet a \ {b})).ncard
        + ((fun y => s(b, y)) '' (H.neighborSet b \ {a})).ncard := by
    refine le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
    exact Set.ncard_union_le _ _
  omega

/-- **The `L(H)`-degree of an edge is at least `2`** as soon as both of its ends have degree
at least `2`: take another edge at `a` and another edge at `b`. -/
theorem two_le_lineGraph_degree [Fintype W] {a b : W} (hab : s(a, b) ∈ H.edgeSet)
    (hha : 2 ≤ (H.neighborSet a).ncard) (hhb : 2 ≤ (H.neighborSet b).ncard) :
    2 ≤ (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).ncard := by
  have hadj : H.Adj a b := hab
  have hnab : a ≠ b := hadj.ne
  obtain ⟨x, hx, hxb⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (H.neighborSet a).ncard) b
  obtain ⟨y, hy, hya⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (H.neighborSet b).ncard) a
  have hax : H.Adj a x := hx
  have hby : H.Adj b y := hy
  have hax' : s(a, x) ∈ H.edgeSet := hax
  have hby' : s(b, y) ∈ H.edgeSet := hby
  set f₁ : H.edgeSet := ⟨s(a, x), hax'⟩ with hf₁
  set f₂ : H.edgeSet := ⟨s(b, y), hby'⟩ with hf₂
  have hne1 : f₁ ≠ (⟨s(a, b), hab⟩ : H.edgeSet) := by
    intro h
    have : s(a, x) = s(a, b) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp this with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hxb h2
    · exact hnab h1
  have hne2 : f₂ ≠ (⟨s(a, b), hab⟩ : H.edgeSet) := by
    intro h
    have : s(b, y) = s(a, b) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hnab h1.symm
    · exact hya h2
  have hmem1 : f₁ ∈ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ := by
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨fun h => hne1 h.symm, a, Sym2.mem_mk_left a b, Sym2.mem_mk_left a x⟩
  have hmem2 : f₂ ∈ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ := by
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨fun h => hne2 h.symm, b, Sym2.mem_mk_right a b, Sym2.mem_mk_left b y⟩
  have hf12 : f₁ ≠ f₂ := by
    intro h
    have : s(a, x) = s(b, y) := congrArg Subtype.val h
    rcases Sym2.eq_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hnab h1
    · exact hxb h2
  have hsub : ({f₁, f₂} : Set H.edgeSet) ⊆ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ := by
    rintro g (rfl | rfl)
    · exact hmem1
    · exact hmem2
  calc (2 : ℕ) = ({f₁, f₂} : Set H.edgeSet).ncard := (Set.ncard_pair hf12).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **The `L(H)`-degree of every vertex of `L(H)` is between `2` and `4`**, when `H` has all
degrees between `2` and `3`. -/
theorem lineGraph_degree_bounds [Fintype W]
    (hlo : ∀ w : W, 2 ≤ (H.neighborSet w).ncard)
    (hhi : ∀ w : W, (H.neighborSet w).ncard ≤ 3) (e : H.edgeSet) :
    2 ≤ (H.lineGraph.neighborSet e).ncard ∧ (H.lineGraph.neighborSet e).ncard ≤ 4 := by
  obtain ⟨z, hz⟩ := e
  revert hz
  induction z using Sym2.ind with
  | _ a b =>
    intro hz
    exact ⟨two_le_lineGraph_degree hz (hlo a) (hlo b),
      lineGraph_degree_le_four hz (hhi a) (hhi b)⟩

end LineGraph

/-! ## The criterion -/

variable {V : Type*}

/-- The degree of `v ∈ K` in `Gx|K` counts exactly the neighbours of `v` lying in `K`. -/
theorem induce_neighborSet_ncard (Gx : SimpleGraph V) {K : Set V} {v : V} (hv : v ∈ K) :
    ((Gx.induce K).neighborSet ⟨v, hv⟩).ncard = (Gx.neighborSet v ∩ K).ncard := by
  have himg : Subtype.val '' ((Gx.induce K).neighborSet ⟨v, hv⟩) = Gx.neighborSet v ∩ K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h2⟩, h1, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- **The degree criterion.**

If every vertex subset `K` of `Gx` with `8 ≤ K.ncard` contains a vertex whose number of
neighbours inside `K` is `< 2` or `> 4`, then `K₄` does not appear in `Gx`. -/
theorem no_appearance_of_degree_criterion [Fintype V] [DecidableEq V] (Gx : SimpleGraph V)
    (hcrit : ∀ K : Set V, 8 ≤ K.ncard →
      ∃ v ∈ K, (Gx.neighborSet v ∩ K).ncard < 2 ∨ 4 < (Gx.neighborSet v ∩ K).ncard) :
    ¬ Appears Gx (⊤ : SimpleGraph (Fin 4)) := by
  rintro ⟨n, H, K, happ⟩
  have h8 : 8 ≤ K.ncard := K4AppearanceEightVertices.eight_le_ncard_of_isAppearance Gx happ
  obtain ⟨hbsub, ⟨φ⟩⟩ := happ
  have hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H := hbsub.1
  -- degree bounds in `H`
  have hk4deg : ∀ u : Fin 4, ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard ≤ 3 := by
    intro u
    have h1 : (⊤ : SimpleGraph (Fin 4)).neighborSet u = ({u} : Set (Fin 4))ᶜ := by
      ext x
      simp [SimpleGraph.mem_neighborSet, SimpleGraph.top_adj, eq_comm]
    have h2 := Set.ncard_add_ncard_compl ({u} : Set (Fin 4))
    rw [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
    rw [h1]
    omega
  have hhi : ∀ w : Fin n, (H.neighborSet w).ncard ≤ 3 :=
    degree_le_three_of_isSubdivision hsub hk4deg
  have hlo : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard :=
    LineGraphDegree.two_le_degree_of_isSubdivision k4_three_connected hsub
  -- the bad vertex
  obtain ⟨v, hvK, hbad⟩ := hcrit K h8
  set e : H.edgeSet := φ.symm ⟨v, hvK⟩ with he
  have hφe : φ e = ⟨v, hvK⟩ := by rw [he]; simp
  have htrans : ((Gx.induce K).neighborSet ⟨v, hvK⟩).ncard
      = (H.lineGraph.neighborSet e).ncard := by
    rw [← hφe, neighborSet_image_of_iso φ e,
      Set.ncard_image_of_injective _ (EquivLike.injective φ)]
  obtain ⟨hge, hle⟩ := lineGraph_degree_bounds hlo hhi e
  rw [← htrans, induce_neighborSet_ncard Gx hvK] at hge hle
  omega

/-!
## Counting the degree-`4` and degree-`3` vertices of an appearance

`K4TrackLengthDegeneracy.bedges H` is the set of edges of `H` both of whose ends are
branch-vertices.  We show

* `deg_four_eq_branch_edges` — the vertices of `K` with exactly four neighbours in `K` are in
  bijection with `bedges H`;
* `two_mul_deg_four_add_deg_three` — `2 · #deg₄ + #deg₃ = 12`.

Both come from the exact degree dictionary: `deg_{L(H)} s(a,b) = deg_H a + deg_H b - 2`, and
`deg_H` is `3` on branch-vertices and `2` elsewhere.  The `12` is the handshake count
`∑_{w branch} deg_H w = 4 · 3`, the left side of which counts each edge once per branch end.
-/

open Workspace.ProofLemmas.K4TrackLengthDegeneracy (bedges)

/-! ### Exact line-graph degrees -/

section ExactDegree

variable {W : Type*} {H : SimpleGraph W}

/-- The `L(H)`-neighbours of `s(a,b)` are **exactly** the other edges at `a` together with the
other edges at `b`. -/
theorem lineGraph_neighborSet_val_eq {a b : W} (hab : s(a, b) ∈ H.edgeSet) :
    Subtype.val '' (H.lineGraph.neighborSet ⟨s(a, b), hab⟩) =
      (fun x => s(a, x)) '' (H.neighborSet a \ {b}) ∪
      (fun y => s(b, y)) '' (H.neighborSet b \ {a}) := by
  refine Set.Subset.antisymm (lineGraph_neighborSet_val_subset hab) ?_
  have hadj : H.Adj a b := hab
  have hnab : a ≠ b := hadj.ne
  rintro z (⟨x, ⟨hx, hxb⟩, rfl⟩ | ⟨y, ⟨hy, hya⟩, rfl⟩)
  · have hax : s(a, x) ∈ H.edgeSet := hx
    refine ⟨⟨s(a, x), hax⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, a, Sym2.mem_mk_left a b, Sym2.mem_mk_left a x⟩
    intro hcon
    have hz : s(a, b) = s(a, x) := congrArg Subtype.val hcon
    rcases Sym2.eq_iff.mp hz with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact hxb h2.symm
    · exact hnab h2.symm
  · have hby : s(b, y) ∈ H.edgeSet := hy
    refine ⟨⟨s(b, y), hby⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborSet, SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, b, Sym2.mem_mk_right a b, Sym2.mem_mk_left b y⟩
    intro hcon
    have hz : s(a, b) = s(b, y) := congrArg Subtype.val hcon
    rcases Sym2.eq_iff.mp hz with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hnab h1
    · exact hya h1.symm

/-- **`deg_{L(H)} s(a,b) = (deg_H a - 1) + (deg_H b - 1)`.** -/
theorem lineGraph_degree_eq [Fintype W] {a b : W} (hab : s(a, b) ∈ H.edgeSet) :
    (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).ncard
      = ((H.neighborSet a).ncard - 1) + ((H.neighborSet b).ncard - 1) := by
  have hadj : H.Adj a b := hab
  have hnab : a ≠ b := hadj.ne
  have hbmem : b ∈ H.neighborSet a := hadj
  have hamem : a ∈ H.neighborSet b := hadj.symm
  have hinjA : Set.InjOn (fun x => s(a, x)) (H.neighborSet a \ {b}) := by
    rintro x ⟨hx, -⟩ x' ⟨-, -⟩ h
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exfalso
      have hxa : H.Adj a x := hx
      rw [h2] at hxa
      exact H.irrefl hxa
  have hinjB : Set.InjOn (fun y => s(b, y)) (H.neighborSet b \ {a}) := by
    rintro y ⟨hy, -⟩ y' ⟨-, -⟩ h
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exfalso
      have hyb : H.Adj b y := hy
      rw [h2] at hyb
      exact H.irrefl hyb
  have hdisj : Disjoint ((fun x => s(a, x)) '' (H.neighborSet a \ {b}))
      ((fun y => s(b, y)) '' (H.neighborSet b \ {a})) := by
    rw [Set.disjoint_left]
    rintro z ⟨x, ⟨-, hxb⟩, rfl⟩ ⟨y, ⟨-, -⟩, hz⟩
    rcases Sym2.eq_iff.mp hz with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hnab h1.symm
    · exact hxb h1.symm
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, lineGraph_neighborSet_val_eq hab,
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.InjOn.ncard_image hinjA,
    Set.InjOn.ncard_image hinjB, Set.ncard_diff_singleton_of_mem hbmem,
    Set.ncard_diff_singleton_of_mem hamem]

/-- The edges of `H` at `w` are in bijection with the neighbours of `w`. -/
theorem ncard_edges_at (H : SimpleGraph W) (w : W) :
    {e : ↥H.edgeSet | w ∈ (↑e : Sym2 W)}.ncard = (H.neighborSet w).ncard := by
  have h1 : Subtype.val '' {e : ↥H.edgeSet | w ∈ (↑e : Sym2 W)}
      = (fun x => s(w, x)) '' (H.neighborSet w) := by
    ext f
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp he
      refine ⟨y, ?_, hy.symm⟩
      have h2 := e.2
      rw [hy] at h2
      exact h2
    · rintro ⟨x, hx, rfl⟩
      have hx' : s(w, x) ∈ H.edgeSet := hx
      exact ⟨⟨s(w, x), hx'⟩, Sym2.mem_mk_left w x, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, h1]
  refine Set.InjOn.ncard_image ?_
  intro x _ y _ hxy
  rcases Sym2.eq_iff.mp hxy with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact h2
  · exact h2.trans h1

/-- A vertex of a graph all of whose degrees are `≤ 3` is a branch-vertex exactly when its
degree is `3`. -/
theorem mem_branchVertices_iff (hhi : ∀ w : W, (H.neighborSet w).ncard ≤ 3) (w : W) :
    w ∈ branchVertices H ↔ (H.neighborSet w).ncard = 3 := by
  have h := hhi w
  constructor
  · intro hw
    have h3 : 3 ≤ (H.neighborSet w).ncard := hw
    omega
  · intro hw
    show 3 ≤ (H.neighborSet w).ncard
    omega

/-- **`deg_{L(H)} e = 2 + (number of branch-vertex ends of e)`**, when all degrees of `H` are
`2` or `3`. -/
theorem lineGraph_degree_eq_two_add [Fintype W] [DecidableEq W]
    (hlo : ∀ w : W, 2 ≤ (H.neighborSet w).ncard)
    (hhi : ∀ w : W, (H.neighborSet w).ncard ≤ 3)
    (Bv : Finset W) (hBv : ∀ w : W, w ∈ Bv ↔ w ∈ branchVertices H) (e : ↥H.edgeSet) :
    (H.lineGraph.neighborSet e).ncard
      = 2 + (Bv.filter (fun w => w ∈ (↑e : Sym2 W))).card := by
  obtain ⟨z, hz⟩ := e
  revert hz
  induction z using Sym2.ind with
  | _ a b =>
    intro hz
    have hadj : H.Adj a b := hz
    have hnab : a ≠ b := hadj.ne
    have hd := lineGraph_degree_eq hz
    have h3 : ∀ w : W, w ∈ Bv → (H.neighborSet w).ncard = 3 := fun w hw =>
      (mem_branchVertices_iff hhi w).mp ((hBv w).mp hw)
    have h2 : ∀ w : W, w ∉ Bv → (H.neighborSet w).ncard = 2 := by
      intro w hw
      have hnb : w ∉ branchVertices H := fun h => hw ((hBv w).mpr h)
      have hlo' := hlo w
      have hhi' := hhi w
      have : ¬ (3 ≤ (H.neighborSet w).ncard) := hnb
      omega
    by_cases ha : a ∈ Bv <;> by_cases hb : b ∈ Bv
    · have hf : Bv.filter (fun w => w ∈ (s(a, b) : Sym2 W)) = {a, b} := by
        ext w
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩; exact h
        · rintro (rfl | rfl)
          exacts [⟨ha, Or.inl rfl⟩, ⟨hb, Or.inr rfl⟩]
      rw [hd, hf, Finset.card_pair hnab, h3 a ha, h3 b hb]
    · have hf : Bv.filter (fun w => w ∈ (s(a, b) : Sym2 W)) = {a} := by
        ext w
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨hwB, (rfl | rfl)⟩
          · rfl
          · exact absurd hwB hb
        · rintro rfl; exact ⟨ha, Or.inl rfl⟩
      rw [hd, hf, Finset.card_singleton, h3 a ha, h2 b hb]
    · have hf : Bv.filter (fun w => w ∈ (s(a, b) : Sym2 W)) = {b} := by
        ext w
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_singleton]
        constructor
        · rintro ⟨hwB, (rfl | rfl)⟩
          · exact absurd hwB ha
          · rfl
        · rintro rfl; exact ⟨hb, Or.inr rfl⟩
      rw [hd, hf, Finset.card_singleton, h2 a ha, h3 b hb]
    · have hf : Bv.filter (fun w => w ∈ (s(a, b) : Sym2 W)) = ∅ := by
        ext w
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.notMem_empty, iff_false, not_and]
        rintro hwB (rfl | rfl)
        · exact ha hwB
        · exact hb hwB
      rw [hd, hf, Finset.card_empty, h2 a ha, h2 b hb]

end ExactDegree

/-! ### Set-cardinality bookkeeping -/

theorem ncard_setOf_eq_card_filter {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    {x : α | P x}.ncard = (Finset.univ.filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp

/-- **The handshake count, abstractly.**  `Bv` is a four-element set of "branch" points, every
one of which lies on exactly three "edges" `a : α`, and every edge carries at most two branch
points.  Then `2·#(edges with two branch ends) + #(edges with one) = 12`. -/
private theorem count_aux {α β : Type*} [Fintype α] [DecidableEq β] (Bv : Finset β)
    (hcard : Bv.card = 4) (inc : α → β → Prop) [∀ a w, Decidable (inc a w)]
    (hrow : ∀ w ∈ Bv, (Finset.univ.filter (fun a : α => inc a w)).card = 3)
    (hcol : ∀ a : α, (Bv.filter (fun w => inc a w)).card ≤ 2) :
    2 * (Finset.univ.filter (fun a : α => (Bv.filter (fun w => inc a w)).card = 2)).card
      + (Finset.univ.filter (fun a : α => (Bv.filter (fun w => inc a w)).card = 1)).card
      = 12 := by
  have hdc : ∑ w ∈ Bv, (Finset.univ.filter (fun a : α => inc a w)).card
      = ∑ a : α, (Bv.filter (fun w => inc a w)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hL : ∑ w ∈ Bv, (Finset.univ.filter (fun a : α => inc a w)).card = 12 := by
    rw [Finset.sum_congr rfl hrow, Finset.sum_const, hcard]
    simp
  have key : ∀ a : α, (Bv.filter (fun w => inc a w)).card
      = 2 * (if (Bv.filter (fun w => inc a w)).card = 2 then 1 else 0)
        + (if (Bv.filter (fun w => inc a w)).card = 1 then 1 else 0) := by
    intro a
    have := hcol a
    split_ifs <;> omega
  have hR : ∑ a : α, (Bv.filter (fun w => inc a w)).card
      = 2 * (Finset.univ.filter (fun a : α => (Bv.filter (fun w => inc a w)).card = 2)).card
        + (Finset.univ.filter (fun a : α => (Bv.filter (fun w => inc a w)).card = 1)).card := by
    rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.card_filter, ← Finset.card_filter]
  omega

/-! ### Transport along the appearance -/

variable {V : Type*}

/-- The `Gx|K`-degree of the vertex `φ e` is the `L(H)`-degree of the edge `e`. -/
theorem lineGraph_degree_eq_induce {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (Gx : SimpleGraph V) (φ : H.lineGraph ≃g Gx.induce K) (e : ↥H.edgeSet) :
    (Gx.neighborSet ((φ e : ↥K) : V) ∩ K).ncard = (H.lineGraph.neighborSet e).ncard := by
  have hmem : ((φ e : ↥K) : V) ∈ K := (φ e).2
  rw [← induce_neighborSet_ncard Gx hmem]
  have he : (⟨((φ e : ↥K) : V), hmem⟩ : ↥K) = φ e := Subtype.ext rfl
  rw [he, neighborSet_image_of_iso φ e, Set.ncard_image_of_injective _ (EquivLike.injective φ)]

/-- Counting the vertices of `K` of a given `Gx|K`-degree is the same as counting the edges of
`H` of that `L(H)`-degree. -/
theorem ncard_deg_eq {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (Gx : SimpleGraph V) (φ : H.lineGraph ≃g Gx.induce K) (k : ℕ) :
    {v ∈ K | (Gx.neighborSet v ∩ K).ncard = k}.ncard
      = {e : ↥H.edgeSet | (H.lineGraph.neighborSet e).ncard = k}.ncard := by
  have hinj : Function.Injective (fun e : ↥H.edgeSet => ((φ e : ↥K) : V)) := by
    intro x y hxy
    exact (EquivLike.injective φ) (Subtype.ext hxy)
  have himg : (fun e : ↥H.edgeSet => ((φ e : ↥K) : V)) ''
      {e : ↥H.edgeSet | (H.lineGraph.neighborSet e).ncard = k}
      = {v ∈ K | (Gx.neighborSet v ∩ K).ncard = k} := by
    ext v
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨(φ e).2, by rw [lineGraph_degree_eq_induce Gx φ e]; exact he⟩
    · rintro ⟨hvK, hv⟩
      refine ⟨φ.symm ⟨v, hvK⟩, ?_, ?_⟩
      · show (H.lineGraph.neighborSet (φ.symm ⟨v, hvK⟩)).ncard = k
        rw [← lineGraph_degree_eq_induce Gx φ (φ.symm ⟨v, hvK⟩)]
        simp only [RelIso.apply_symm_apply]
        exact hv
      · simp
  rw [← himg, Set.ncard_image_of_injective _ hinj]

/-! ### The two counting lemmas -/

/-- Every vertex of `K₄` has degree `≤ 3` (indeed exactly `3`). -/
theorem k4_degree_le_three (u : Fin 4) :
    ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard ≤ 3 := by
  have h1 : (⊤ : SimpleGraph (Fin 4)).neighborSet u = ({u} : Set (Fin 4))ᶜ := by
    ext x
    simp [SimpleGraph.mem_neighborSet, SimpleGraph.top_adj, eq_comm]
  have h2 := Set.ncard_add_ncard_compl ({u} : Set (Fin 4))
  rw [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  rw [h1]
  omega

/-- The branch-vertices of a bipartite subdivision of `K₄` are its four `K₄`-vertices. -/
theorem branchVertices_ncard {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H) :
    (branchVertices H).ncard = 4 := by
  obtain ⟨ι, T, hinj, htrack, hlen, hrev, hdisj, hnew, hcover, hedge⟩ := hH.1
  have hdeg : ∀ u : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    fun u => three_le_degree_of_three_connected _ k4_three_connected u
  have h1 : Set.range ι ⊆ branchVertices H :=
    range_subset_branchVertices hinj htrack hlen hdisj hnew hdeg
  have h2 : branchVertices H ⊆ Set.range ι :=
    branchVertices_subset_range htrack hrev hdisj hcover hedge
  rw [Set.Subset.antisymm h2 h1, Set.ncard_range_of_injective hinj]
  simp

/-- The `L(H)`-degree of an edge is `4` exactly when both its ends are branch-vertices. -/
theorem lineGraph_degree_eq_four_iff {n : ℕ} {H : SimpleGraph (Fin n)}
    (hlo : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard)
    (hhi : ∀ w : Fin n, (H.neighborSet w).ncard ≤ 3) (e : ↥H.edgeSet) :
    (H.lineGraph.neighborSet e).ncard = 4 ↔ ∀ x ∈ (↑e : Sym2 (Fin n)), x ∈ branchVertices H := by
  obtain ⟨z, hz⟩ := e
  revert hz
  induction z using Sym2.ind with
  | _ a b =>
    intro hz
    have hd := lineGraph_degree_eq hz
    have hbr : ∀ w : Fin n, w ∈ branchVertices H ↔ (H.neighborSet w).ncard = 3 :=
      mem_branchVertices_iff hhi
    have hla := hlo a
    have hlb := hlo b
    have hha := hhi a
    have hhb := hhi b
    constructor
    · intro h4 x hx
      rw [hd] at h4
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact (hbr x).mpr (by omega)
      · exact (hbr x).mpr (by omega)
    · intro hall
      have ha := (hbr a).mp (hall a (Sym2.mem_mk_left a b))
      have hb := (hbr b).mp (hall b (Sym2.mem_mk_right a b))
      rw [hd, ha, hb]

/-- **The degree-`4` vertices of an appearance of `K₄` correspond to the branch-to-branch edges
of the subdivision.** -/
theorem deg_four_eq_branch_edges {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (Gx : SimpleGraph V) (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (φ : H.lineGraph ≃g Gx.induce K) :
    {v ∈ K | (Gx.neighborSet v ∩ K).ncard = 4}.ncard = (bedges H).ncard := by
  have hhi : ∀ w : Fin n, (H.neighborSet w).ncard ≤ 3 :=
    degree_le_three_of_isSubdivision hH.1 k4_degree_le_three
  have hlo : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard :=
    LineGraphDegree.two_le_degree_of_isSubdivision k4_three_connected hH.1
  rw [ncard_deg_eq Gx φ 4]
  have himg : Subtype.val '' {e : ↥H.edgeSet | (H.lineGraph.neighborSet e).ncard = 4}
      = bedges H := by
    ext f
    constructor
    · rintro ⟨e, he, rfl⟩
      exact ⟨e.2, (lineGraph_degree_eq_four_iff hlo hhi e).mp he⟩
    · rintro ⟨hf, hbr⟩
      exact ⟨⟨f, hf⟩, (lineGraph_degree_eq_four_iff hlo hhi ⟨f, hf⟩).mpr hbr, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- **`2 · #{degree-4 vertices} + #{degree-3 vertices} = 12`** for an appearance of `K₄`.

The left-hand side is the handshake count `∑_{w a branch-vertex of H} deg_H w = 4 · 3`. -/
theorem two_mul_deg_four_add_deg_three {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (Gx : SimpleGraph V) (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (φ : H.lineGraph ≃g Gx.induce K) :
    2 * {v ∈ K | (Gx.neighborSet v ∩ K).ncard = 4}.ncard
      + {v ∈ K | (Gx.neighborSet v ∩ K).ncard = 3}.ncard = 12 := by
  classical
  haveI : Fintype ↥H.edgeSet := Fintype.ofFinite _
  have hhi : ∀ w : Fin n, (H.neighborSet w).ncard ≤ 3 :=
    degree_le_three_of_isSubdivision hH.1 k4_degree_le_three
  have hlo : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard :=
    LineGraphDegree.two_le_degree_of_isSubdivision k4_three_connected hH.1
  -- the four branch-vertices, as a `Finset`
  obtain ⟨Bv, hBv, hBvcard⟩ :
      ∃ Bv : Finset (Fin n), (∀ w : Fin n, w ∈ Bv ↔ w ∈ branchVertices H) ∧ Bv.card = 4 := by
    refine ⟨Finset.univ.filter (fun w => w ∈ branchVertices H), by simp, ?_⟩
    rw [← ncard_setOf_eq_card_filter, Set.setOf_mem_eq]
    exact branchVertices_ncard hH
  have hpt : ∀ e : ↥H.edgeSet, (H.lineGraph.neighborSet e).ncard
      = 2 + (Bv.filter (fun w => w ∈ (↑e : Sym2 (Fin n)))).card :=
    lineGraph_degree_eq_two_add hlo hhi Bv hBv
  -- every edge carries at most two branch ends
  have hcol : ∀ e : ↥H.edgeSet, (Bv.filter (fun w => w ∈ (↑e : Sym2 (Fin n)))).card ≤ 2 := by
    intro e
    have h := hpt e
    have hb := lineGraph_degree_bounds hlo hhi e
    omega
  -- every branch vertex lies on exactly three edges
  have hrow : ∀ w ∈ Bv, (Finset.univ.filter (fun e : ↥H.edgeSet =>
      w ∈ (↑e : Sym2 (Fin n)))).card = 3 := by
    intro w hw
    rw [← ncard_setOf_eq_card_filter, ncard_edges_at H w]
    exact (mem_branchVertices_iff hhi w).mp ((hBv w).mp hw)
  have hmain := count_aux Bv hBvcard
    (fun (e : ↥H.edgeSet) (w : Fin n) => w ∈ (↑e : Sym2 (Fin n))) hrow hcol
  have h4 : Finset.univ.filter (fun e : ↥H.edgeSet =>
        (Bv.filter (fun w => w ∈ (↑e : Sym2 (Fin n)))).card = 2)
      = Finset.univ.filter (fun e : ↥H.edgeSet => (H.lineGraph.neighborSet e).ncard = 4) := by
    refine Finset.filter_congr ?_
    intro e _
    have := hpt e
    omega
  have h3 : Finset.univ.filter (fun e : ↥H.edgeSet =>
        (Bv.filter (fun w => w ∈ (↑e : Sym2 (Fin n)))).card = 1)
      = Finset.univ.filter (fun e : ↥H.edgeSet => (H.lineGraph.neighborSet e).ncard = 3) := by
    refine Finset.filter_congr ?_
    intro e _
    have := hpt e
    omega
  rw [h4, h3] at hmain
  rw [ncard_deg_eq Gx φ 4, ncard_deg_eq Gx φ 3, ncard_setOf_eq_card_filter,
    ncard_setOf_eq_card_filter]
  exact hmain

end Workspace.ProofLemmas.K4AppearanceDegreeCriterion
