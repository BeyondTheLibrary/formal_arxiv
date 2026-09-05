import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup

/-!
# Deleting a branch from a subdivision, and restricting the appearance

This is Lemma 3 of the rung-replacement plan for the proof of 7.5 (printed p. 37):

> PAPER: *"So if in `L(H)` we replace `Rb₁b₂` by `R′` we obtain another appearance of `J` in
> `G`, say `L(H′)`, where `H′` is obtained from `H` by replacing the branch `Bb₁b₂` by some new
> branch `B′` joining the same two vertices."*

The first half of the surgery is to *remove* the old branch `q`: delete its edges and its
internal vertices.  Write `W₀` for the vertices of `H` that are not internal to `q`, and let
`H₀` be the graph on `W₀` keeping every edge of `H` that is not an edge of `q`.  Both the
vertex deletion and the edge deletion are needed: a branch of length one has no internal
vertex, but its single edge must still go.

The point of the module is the residual appearance.  Write `rungOf φ q` for the set of vertices
of `G` labelling the edges of `q` (the paper's `V(Rb₁b₂)`), and `K₀ = K \ rungOf φ q`.  Then
`φ` restricts to an isomorphism `H₀.lineGraph ≃g G.induce K₀` which gives every retained edge
the vertex of `G` it already had.  Given that, the two endpoint cliques of the residual
appearance are the old ones with `r₁`, resp. `r₂`, removed.

The one hypothesis that is not bookkeeping is `hclosed`: *every edge of `H` that is not an edge
of `q` avoids the interior of `q`*.  It is what makes the edge deletion and the vertex deletion
agree, and it holds because an internal vertex of a branch of a subdivision has degree two with
both edges on the branch (proved in
`Workspace.ProofLemmas.RungReplacementBranchFacts.edges_off_branch_avoid_interior`).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RungReplacementDelete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup

variable {V W : Type*}

/-- The vertices of `H` that survive the deletion of the branch `q`: everything except the
internal vertices of `q`. -/
@[reducible] def resVerts (q : List W) : Type _ := {w : W // w ∉ trackInterior q}

/-- `H` with the branch `q` removed: the internal vertices of `q` are gone, and so are the
edges of `q`. -/
def resGraph (H : SimpleGraph W) (q : List W) : SimpleGraph (resVerts q) where
  Adj x y := H.Adj x.val y.val ∧ s(x.val, y.val) ∉ trackEdges q
  symm := by
    rintro x y ⟨h1, h2⟩
    exact ⟨h1.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => H.irrefl h.1⟩

@[simp] theorem resGraph_adj {H : SimpleGraph W} {q : List W} (x y : resVerts q) :
    (resGraph H q).Adj x y ↔ H.Adj x.val y.val ∧ s(x.val, y.val) ∉ trackEdges q := Iff.rfl

open Classical in
/-- A total map `W → resVerts q`, the identity off the interior of the deleted branch.

The internal vertices of `q` disappear from the new subdivision, so the relabelling `ι` of the
old vertices has nothing to send them to; the paper never refers to them again.  Sending them
to a fixed retained vertex keeps `ι` total, which is what the frozen interface asks for. -/
noncomputable def resEmb (q : List W) (b : W) (hb : b ∉ trackInterior q) (w : W) :
    resVerts q :=
  if h : w ∉ trackInterior q then ⟨w, h⟩ else ⟨b, hb⟩

theorem resEmb_of_notMem (q : List W) (b : W) (hb : b ∉ trackInterior q) {w : W}
    (hw : w ∉ trackInterior q) : resEmb q b hb w = ⟨w, hw⟩ := by
  classical
  exact dif_pos hw

/-- The set of vertices of `G` labelling the edges of the track `q`; this is definitionally
`Workspace.ProofLemmas.RungReplacementLabelled.rungSet`, repeated here because that module
imports this one. -/
def rungOf (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (q : List W) : Set V :=
  {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet), e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)}

/-! ### `Sym2` bookkeeping for the subtype `W₀` -/

theorem sym2_val_injective (q : List W) :
    Function.Injective (Sym2.map (Subtype.val : resVerts q → W)) :=
  Sym2.map.injective Subtype.val_injective

/-- An edge of `H` all of whose ends survive the deletion comes from an edge of the residual
vertex type. -/
theorem exists_sym2_lift {q : List W} (e : Sym2 W)
    (h : ∀ w ∈ e, w ∉ trackInterior q) :
    ∃ f : Sym2 (resVerts q), Sym2.map Subtype.val f = e := by
  induction e using Sym2.ind with
  | _ x y =>
    exact ⟨s(⟨x, h x (by simp)⟩, ⟨y, h y (by simp)⟩), rfl⟩

theorem mem_resGraph_edgeSet {H : SimpleGraph W} {q : List W} (f : Sym2 (resVerts q)) :
    f ∈ (resGraph H q).edgeSet ↔
      Sym2.map Subtype.val f ∈ H.edgeSet ∧ Sym2.map Subtype.val f ∉ trackEdges q := by
  induction f using Sym2.ind with
  | _ x y => exact Iff.rfl

/-! ### The residual appearance -/

variable (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
  (φ : H.lineGraph ≃g G.induce K) (q : List W)

/-- The vertex of `G` labelling a retained edge is the vertex it already had. -/
theorem resLabel_mem {f : Sym2 (resVerts q)} (hf : f ∈ (resGraph H q).edgeSet) :
    (↑(φ ⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩) : V)
      ∈ K \ rungOf G H K φ q := by
  refine ⟨(φ ⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩).2, ?_⟩
  rintro ⟨e, he, heq, hval⟩
  have : (⟨e, he⟩ : H.edgeSet) =
      ⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩ := by
    apply (EquivLike.injective φ)
    exact Subtype.ext hval.symm
  have h2 : e = Sym2.map Subtype.val f := congrArg Subtype.val this
  exact ((mem_resGraph_edgeSet f).mp hf).2 (h2 ▸ heq)

/-- **Lemma 3: deleting the branch keeps an appearance.**  The old isomorphism restricts to the
residual graph, and every retained edge keeps its label. -/
theorem exists_resIso
    (hclosed : ∀ e ∈ H.edgeSet, e ∉ trackEdges q → ∀ w ∈ e, w ∉ trackInterior q) :
    ∃ φ₀ : (resGraph H q).lineGraph ≃g G.induce (K \ rungOf G H K φ q),
      ∀ (f : Sym2 (resVerts q)) (hf : f ∈ (resGraph H q).edgeSet),
        (↑(φ₀ ⟨f, hf⟩) : V)
          = (↑(φ ⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hf).1⟩) : V) := by
  classical
  set K₀ : Set V := K \ rungOf G H K φ q with hK₀
  -- the labelling map
  let F : (resGraph H q).edgeSet → ↥K₀ := fun f =>
    ⟨(↑(φ ⟨Sym2.map Subtype.val f.1, ((mem_resGraph_edgeSet f.1).mp f.2).1⟩) : V),
      resLabel_mem G H K φ q f.2⟩
  have hFinj : Function.Injective F := by
    intro a b hab
    have hab0 : ((F a : ↥K₀) : V) = ((F b : ↥K₀) : V) := congrArg Subtype.val hab
    have hab' : (↑(φ ⟨Sym2.map Subtype.val a.1, ((mem_resGraph_edgeSet a.1).mp a.2).1⟩) : V)
        = (↑(φ ⟨Sym2.map Subtype.val b.1, ((mem_resGraph_edgeSet b.1).mp b.2).1⟩) : V) := hab0
    have h1 : (⟨Sym2.map Subtype.val a.1, ((mem_resGraph_edgeSet a.1).mp a.2).1⟩ : H.edgeSet)
        = ⟨Sym2.map Subtype.val b.1, ((mem_resGraph_edgeSet b.1).mp b.2).1⟩ :=
      (EquivLike.injective φ) (Subtype.ext hab')
    exact Subtype.ext (sym2_val_injective q (Subtype.ext_iff.mp h1))
  have hFsurj : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨hxK, hxr⟩ := hx
    set e : H.edgeSet := φ.symm ⟨x, hxK⟩ with he
    have hφe : (↑(φ e) : V) = x := by rw [he, RelIso.apply_symm_apply]
    have henot : (e : Sym2 W) ∉ trackEdges q := by
      intro hcon
      exact hxr ⟨(e : Sym2 W), e.2, hcon, hφe.symm⟩
    obtain ⟨f, hfval⟩ := exists_sym2_lift (q := q) (e : Sym2 W) (hclosed _ e.2 henot)
    have hfe : f ∈ (resGraph H q).edgeSet := by
      rw [mem_resGraph_edgeSet, hfval]
      exact ⟨e.2, henot⟩
    refine ⟨⟨f, hfe⟩, ?_⟩
    apply Subtype.ext
    show (↑(φ ⟨Sym2.map Subtype.val f, _⟩) : V) = x
    rw [show (⟨Sym2.map Subtype.val f, ((mem_resGraph_edgeSet f).mp hfe).1⟩ : H.edgeSet)
      = e from Subtype.ext hfval]
    exact hφe
  let eqv : (resGraph H q).edgeSet ≃ ↥K₀ := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  refine ⟨⟨eqv, ?_⟩, fun f hf => rfl⟩
  intro a b
  show (G.induce K₀).Adj (F a) (F b) ↔ (resGraph H q).lineGraph.Adj a b
  have hstep : (G.induce K₀).Adj (F a) (F b) ↔
      H.lineGraph.Adj ⟨Sym2.map Subtype.val a.1, ((mem_resGraph_edgeSet a.1).mp a.2).1⟩
        ⟨Sym2.map Subtype.val b.1, ((mem_resGraph_edgeSet b.1).mp b.2).1⟩ := by
    rw [← φ.map_rel_iff]
    simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
    rfl
  rw [hstep, SimpleGraph.lineGraph_adj_iff_exists, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hv1, hv2⟩
    obtain ⟨v1, hv1', rfl⟩ := Sym2.mem_map.mp hv1
    obtain ⟨v2, hv2', hv2eq⟩ := Sym2.mem_map.mp hv2
    have hvv : v2 = v1 := Subtype.val_injective hv2eq
    rw [hvv] at hv2'
    exact ⟨fun h => hne (Subtype.ext (by rw [h])), v1, hv1', hv2'⟩
  · rintro ⟨hne, v, hv1, hv2⟩
    refine ⟨fun h => hne (Subtype.ext (sym2_val_injective q (congrArg Subtype.val h))), ?_⟩
    exact ⟨v.val, Sym2.mem_map.mpr ⟨v, hv1, rfl⟩, Sym2.mem_map.mpr ⟨v, hv2, rfl⟩⟩

end Workspace.ProofLemmas.RungReplacementDelete
