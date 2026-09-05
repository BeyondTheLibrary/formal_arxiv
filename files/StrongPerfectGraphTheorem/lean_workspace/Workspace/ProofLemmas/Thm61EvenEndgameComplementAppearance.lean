import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm101ThetaOfPrism
import Workspace.ProofLemmas.Thm101ThetaAddBranch
import Workspace.ProofLemmas.Thm101ThetaBipartite
import Workspace.ProofLemmas.Thm101ThetaBranchVerticesAreK4
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm61Claim1Helpers
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.Thm61Setup

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.ThetaData
open Workspace.ProofLemmas.Thm61Setup

private def shortThetaTrack : Fin 3 → List (Fin 6)
  | 0 => [0, 2, 3, 1]
  | 1 => [0, 4, 5, 1]
  | 2 => [0, 1]

/-- The fixed seven-edge theta used in the short `K₄` complement construction. -/
def shortTheta : SimpleGraph (Fin 6) :=
  SimpleGraph.fromEdgeSet (⋃ i : Fin 3, trackEdges (shortThetaTrack i))

theorem shortThetaDatum : IsThetaDatum shortTheta 0 1 shortThetaTrack := by
  classical
  unfold IsThetaDatum
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hnd : (shortThetaTrack i).Nodup := by fin_cases i <;> decide
    have hedge : ∀ k : ℕ, (hk : k + 1 < (shortThetaTrack i).length) →
        shortTheta.Adj (shortThetaTrack i)[k] (shortThetaTrack i)[k + 1] := by
      intro k hk
      apply (SimpleGraph.mem_edgeSet shortTheta).mp
      rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
      constructor
      · exact Set.mem_iUnion.mpr ⟨i, ⟨k, hk, rfl⟩⟩
      · rw [Sym2.mem_diagSet_iff_eq]
        exact fun h => (by omega : k ≠ k + 1) (hnd.getElem_inj_iff.mp h)
    refine ⟨⟨?_, hnd, hedge⟩, ?_, ?_⟩
    · fin_cases i <;> decide
    · fin_cases i <;> decide
    · fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide
  · intro i j hij v hv
    fin_cases i <;> fin_cases j <;>
      simp_all [shortThetaTrack, trackInterior] <;> aesop
  · intro i v hv
    fin_cases i <;> simp_all [shortThetaTrack, trackInterior] <;> aesop
  · intro v
    fin_cases v
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨0, by simp [shortThetaTrack, trackInterior]⟩)
    · exact Or.inr (Or.inr ⟨0, by simp [shortThetaTrack, trackInterior]⟩)
    · exact Or.inr (Or.inr ⟨1, by simp [shortThetaTrack, trackInterior]⟩)
    · exact Or.inr (Or.inr ⟨1, by simp [shortThetaTrack, trackInterior]⟩)
  · rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    apply sdiff_eq_left.mpr
    rw [Set.disjoint_left]
    intro e he hdiag
    simp only [Set.mem_iUnion] at he
    obtain ⟨i, hi⟩ := he
    obtain ⟨k, hk, hke⟩ := hi
    rw [hke, Sym2.mem_diagSet_iff_eq] at hdiag
    have hnd : (shortThetaTrack i).Nodup := by
      fin_cases i <;> decide
    exact (by omega : k ≠ k + 1) (hnd.getElem_inj_iff.mp hdiag)

/-- Build a line-graph isomorphism from compatible finite indexings of the host edges and the
vertices of an induced subgraph. -/
noncomputable def lineGraphIsoInduceOfEdgeIndex {V W I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] (G : SimpleGraph V) (H : SimpleGraph W)
    (edge : I ≃ H.edgeSet) (w : I → V) (hwinj : Function.Injective w)
    (hrel : ∀ i j : I, H.lineGraph.Adj (edge i) (edge j) ↔ G.Adj (w i) (w j)) :
    H.lineGraph ≃g G.induce (Set.range w) := by
  classical
  let w' : I → Set.range w := fun i => ⟨w i, ⟨i, rfl⟩⟩
  have hw'bij : Function.Bijective w' := by
    constructor
    · intro i j hij
      exact hwinj (congrArg Subtype.val hij)
    · rintro ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩
  let we : I ≃ Set.range w := Equiv.ofBijective w' hw'bij
  exact
    { toEquiv := edge.symm.trans we
      map_rel_iff' := by
        intro e f
        have hr := hrel (edge.symm e) (edge.symm f)
        simpa [we, w'] using hr.symm }

private def shortThetaEdgeVal : Fin 7 → Sym2 (Fin 6)
  | 0 => s(0, 2)
  | 1 => s(2, 3)
  | 2 => s(3, 1)
  | 3 => s(0, 4)
  | 4 => s(4, 5)
  | 5 => s(5, 1)
  | 6 => s(0, 1)

private theorem shortThetaEdgeVal_mem (i : Fin 7) : shortThetaEdgeVal i ∈ shortTheta.edgeSet := by
  fin_cases i
  · change s(0, 2) ∈ shortTheta.edgeSet
    rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Set.mem_iUnion.mpr ⟨0, ⟨0, by decide, by simp [shortThetaTrack]⟩⟩, by simp⟩
  · change s(2, 3) ∈ shortTheta.edgeSet
    rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Set.mem_iUnion.mpr ⟨0, ⟨1, by decide, by simp [shortThetaTrack]⟩⟩, by simp⟩
  · change s(3, 1) ∈ shortTheta.edgeSet
    rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Set.mem_iUnion.mpr ⟨0, ⟨2, by decide, by simp [shortThetaTrack]⟩⟩, by simp⟩
  · change s(0, 4) ∈ shortTheta.edgeSet
    rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Set.mem_iUnion.mpr ⟨1, ⟨0, by decide, by simp [shortThetaTrack]⟩⟩, by simp⟩
  · change s(4, 5) ∈ shortTheta.edgeSet
    rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Set.mem_iUnion.mpr ⟨1, ⟨1, by decide, by simp [shortThetaTrack]⟩⟩, by simp⟩
  · change s(5, 1) ∈ shortTheta.edgeSet
    rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Set.mem_iUnion.mpr ⟨1, ⟨2, by decide, by simp [shortThetaTrack]⟩⟩, by simp⟩
  · change s(0, 1) ∈ shortTheta.edgeSet
    rw [shortTheta, SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨Set.mem_iUnion.mpr ⟨2, ⟨0, by decide, by simp [shortThetaTrack]⟩⟩, by simp⟩

private def shortThetaEdge (i : Fin 7) : shortTheta.edgeSet :=
  ⟨shortThetaEdgeVal i, shortThetaEdgeVal_mem i⟩

private def shortK4EdgePattern {W : Type*} (b b₁ b₂ u v : W) (e₃ : Sym2 W) :
    Fin 7 → Sym2 W
  | 0 => s(b₂, v)
  | 1 => s(b, b₁)
  | 2 => s(b₂, u)
  | 3 => s(b₁, u)
  | 4 => s(b, b₂)
  | 5 => s(b₁, v)
  | 6 => e₃

private theorem shortThetaEdge_bijective : Function.Bijective shortThetaEdge := by
  classical
  constructor
  · intro i j hij
    have hv : shortThetaEdgeVal i = shortThetaEdgeVal j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [shortThetaEdgeVal]
  · intro e
    have he : (e : Sym2 (Fin 6)) ∈ ⋃ i : Fin 3, trackEdges (shortThetaTrack i) := by
      have he' := e.property
      change (e : Sym2 (Fin 6)) ∈
        (SimpleGraph.fromEdgeSet (⋃ i : Fin 3, trackEdges (shortThetaTrack i))).edgeSet at he'
      rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
      exact he'.1
    simp only [Set.mem_iUnion] at he
    obtain ⟨i, k, hk, hke⟩ := he
    fin_cases i
    · change k + 1 < 4 at hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · refine ⟨0, Subtype.ext ?_⟩
        simpa [shortThetaEdge, shortThetaEdgeVal] using hke.symm
      · refine ⟨1, Subtype.ext ?_⟩
        simpa [shortThetaEdge, shortThetaEdgeVal] using hke.symm
      · refine ⟨2, Subtype.ext ?_⟩
        simpa [shortThetaEdge, shortThetaEdgeVal] using hke.symm
    · change k + 1 < 4 at hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · refine ⟨3, Subtype.ext ?_⟩
        simpa [shortThetaEdge, shortThetaEdgeVal] using hke.symm
      · refine ⟨4, Subtype.ext ?_⟩
        simpa [shortThetaEdge, shortThetaEdgeVal] using hke.symm
      · refine ⟨5, Subtype.ext ?_⟩
        simpa [shortThetaEdge, shortThetaEdgeVal] using hke.symm
    · change k + 1 < 2 at hk
      have hk0 : k = 0 := by omega
      subst k
      refine ⟨6, Subtype.ext ?_⟩
      simpa [shortThetaEdge, shortThetaEdgeVal] using hke.symm

private noncomputable def shortThetaEdgeEquiv : Fin 7 ≃ shortTheta.edgeSet :=
  Equiv.ofBijective shortThetaEdge shortThetaEdge_bijective

/-- Seven labelled vertices with the complementary theta-line adjacency pattern form the base
appearance used before the antipath is attached. -/
noncomputable def shortThetaIsoInduce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Fin 7 → V) (hwinj : Function.Injective w)
    (hrel : ∀ i j : Fin 7,
      shortTheta.lineGraph.Adj (shortThetaEdge i) (shortThetaEdge j) ↔ G.Adj (w i) (w j)) :
    shortTheta.lineGraph ≃g G.induce (Set.range w) :=
  lineGraphIsoInduceOfEdgeIndex G shortTheta shortThetaEdgeEquiv w hwinj hrel

theorem shortThetaIsoInduce_apply {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Fin 7 → V) (hwinj : Function.Injective w)
    (hrel : ∀ i j : Fin 7,
      shortTheta.lineGraph.Adj (shortThetaEdge i) (shortThetaEdge j) ↔ G.Adj (w i) (w j))
    (i : Fin 7) :
    (↑(shortThetaIsoInduce G w hwinj hrel (shortThetaEdge i)) : V) = w i := by
  classical
  simp only [shortThetaIsoInduce, lineGraphIsoInduceOfEdgeIndex]
  change w (shortThetaEdgeEquiv.symm (shortThetaEdge i)) = w i
  have hi : shortThetaEdge i = shortThetaEdgeEquiv i := rfl
  rw [hi]
  rw [shortThetaEdgeEquiv.symm_apply_apply]

private theorem shortThetaIsoInduce_eq_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Fin 7 → V) (hwinj : Function.Injective w)
    (hrel : ∀ i j : Fin 7,
      shortTheta.lineGraph.Adj (shortThetaEdge i) (shortThetaEdge j) ↔ G.Adj (w i) (w j))
    (e : shortTheta.edgeSet) (i : Fin 7) :
    (↑(shortThetaIsoInduce G w hwinj hrel e) : V) = w i ↔ e = shortThetaEdge i := by
  constructor
  · intro h
    apply (EquivLike.injective (shortThetaIsoInduce G w hwinj hrel))
    apply Subtype.ext
    simpa [shortThetaIsoInduce_apply G w hwinj hrel i] using h
  · rintro rfl
    exact shortThetaIsoInduce_apply G w hwinj hrel i

private theorem shortThetaEdge_incident_two (e : shortTheta.edgeSet)
    (h : (2 : Fin 6) ∈ (e : Sym2 (Fin 6))) :
    e = shortThetaEdge 0 ∨ e = shortThetaEdge 1 := by
  obtain ⟨i, rfl⟩ := shortThetaEdge_bijective.2 e
  fin_cases i <;> simp_all [shortThetaEdge, shortThetaEdgeVal]

private theorem shortThetaEdge_incident_five (e : shortTheta.edgeSet)
    (h : (5 : Fin 6) ∈ (e : Sym2 (Fin 6))) :
    e = shortThetaEdge 4 ∨ e = shortThetaEdge 5 := by
  obtain ⟨i, rfl⟩ := shortThetaEdge_bijective.2 e
  fin_cases i <;> simp_all [shortThetaEdge, shortThetaEdgeVal]

private theorem shortTheta_not_adj_two_five : ¬ shortTheta.Adj 2 5 := by
  intro h
  obtain ⟨i, hi⟩ := shortThetaEdge_bijective.2
    (⟨s(2, 5), (SimpleGraph.mem_edgeSet shortTheta).mpr h⟩ : shortTheta.edgeSet)
  fin_cases i <;> simp_all [shortThetaEdge, shortThetaEdgeVal]

/-- Under a line-graph appearance, two represented host edges are adjacent in the complement
exactly when the two edges are disjoint. -/
theorem compl_adj_image_iff_disjoint {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (e f : H.edgeSet) :
    Gᶜ.Adj (↑(φ e) : V) (↑(φ f) : V) ↔ DisjointEdges (e : Sym2 W) (f : Sym2 W) := by
  rw [SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hvalne, hnadj⟩ v ⟨hve, hvf⟩
    have hef : e ≠ f := by
      intro hef
      exact hvalne (congrArg (fun q : H.edgeSet => (↑(φ q) : V)) hef)
    apply hnadj
    exact φ.map_adj_iff.mpr
      (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hef, v, hve, hvf⟩)
  · intro hdis
    have hef : e ≠ f := by
      intro hef
      subst f
      rcases e with ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y => exact hdis x ⟨Sym2.mem_mk_left x y, Sym2.mem_mk_left x y⟩
    refine ⟨?_, ?_⟩
    · intro hval
      exact hef ((EquivLike.injective φ) (Subtype.ext hval))
    · intro hadj
      obtain ⟨-, v, hve, hvf⟩ :=
        SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_adj_iff.mp hadj)
      exact hdis v ⟨hve, hvf⟩

/-- An `X_i` edge misses exactly the omitted vertex `y_i` among `Y`, expressed in the
complement and through the line-graph labelling. -/
theorem compl_adj_image_of_extraEdges_iff {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (K Y : Set V)
    (φ : H.lineGraph ≃g G.induce K) {e : Sym2 W} {y x : V}
    (heE : e ∈ H.edgeSet) (he : e ∈ extraEdges G H K φ Y y) (hxY : x ∈ Y)
    (hxK : x ∉ K) :
    Gᶜ.Adj x (↑(φ ⟨e, heE⟩) : V) ↔ x = y := by
  rcases he with ⟨⟨heE', hc⟩, hn⟩
  have hy_not : ¬ G.Adj (↑(φ ⟨e, heE⟩) : V) y := by
    intro hy
    apply hn
    refine ⟨heE, ?_⟩
    intro z hz
    by_cases hzy : z = y
    · simpa [hzy] using hy
    · exact hc z ⟨hz, by simpa using hzy⟩
  rw [SimpleGraph.compl_adj]
  constructor
  · rintro ⟨-, hnadj⟩
    by_contra hxy
    exact hnadj (hc x ⟨hxY, by simpa using hxy⟩).symm
  · rintro rfl
    refine ⟨?_, fun h => hy_not h.symm⟩
    intro hyK
    exact hxK (hyK ▸ (φ ⟨e, heE⟩).property)

/-- A `Y`-complete edge has no complementary adjacency to a vertex of `Y`. -/
theorem not_compl_adj_image_of_completeEdges {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (K Y : Set V)
    (φ : H.lineGraph ≃g G.induce K) {e : Sym2 W} {x : V}
    (heE : e ∈ H.edgeSet) (he : e ∈ completeEdges G H K φ Y) (hxY : x ∈ Y) :
    ¬ Gᶜ.Adj x (↑(φ ⟨e, heE⟩) : V) := by
  intro h
  exact ((SimpleGraph.compl_adj G _ _).mp h).2 (he.2 x hxY).symm

/-- The disjointness graph of the seven edges in the short `K₄` configuration is the line
graph of `shortTheta`. -/
theorem shortK4EdgePattern_disjoint {W : Type*}
    (b b₁ b₂ u v : W) (e₃ : Sym2 W)
    (hnd : [b, b₁, b₂, u, v].Nodup)
    (hd0 : DisjointEdges e₃ s(b₂, v))
    (hd2 : DisjointEdges e₃ s(b₂, u))
    (hd3 : DisjointEdges e₃ s(b₁, u))
    (hd5 : DisjointEdges e₃ s(b₁, v))
    (hm1 : MeetEdges e₃ s(b, b₁))
    (hm4 : MeetEdges e₃ s(b, b₂)) :
    ∀ i j : Fin 7,
      shortTheta.lineGraph.Adj (shortThetaEdge i) (shortThetaEdge j) ↔
        DisjointEdges (shortK4EdgePattern b b₁ b₂ u v e₃ i)
          (shortK4EdgePattern b b₁ b₂ u v e₃ j) := by
  rcases List.nodup_cons.mp hnd with ⟨hb, hnd₁⟩
  rcases List.nodup_cons.mp hnd₁ with ⟨hb₁, hnd₂⟩
  rcases List.nodup_cons.mp hnd₂ with ⟨hb₂, hndu⟩
  rcases List.nodup_cons.mp hndu with ⟨hu, -⟩
  simp only [List.mem_cons, List.mem_singleton, not_or] at hb hb₁ hb₂ hu
  rcases hb with ⟨hbb₁, hbb₂, hbu, hbv⟩
  rcases hb₁ with ⟨hb₁b₂, hb₁u, hb₁v⟩
  rcases hb₂ with ⟨hb₂u, hb₂v⟩
  have hbv' : b ≠ v := hbv.1
  have hb₁v' : b₁ ≠ v := hb₁v.1
  have hb₂v' : b₂ ≠ v := hb₂v.1
  have huv : u ≠ v := hu.1
  have hsymm : ∀ {e f : Sym2 W}, DisjointEdges e f → DisjointEdges f e := by
    intro e f h x hx
    exact h x ⟨hx.2, hx.1⟩
  have hd0' : DisjointEdges s(b₂, v) e₃ := hsymm hd0
  have hd2' : DisjointEdges s(b₂, u) e₃ := hsymm hd2
  have hd3' : DisjointEdges s(b₁, u) e₃ := hsymm hd3
  have hd5' : DisjointEdges s(b₁, v) e₃ := hsymm hd5
  have hm1' : ¬ DisjointEdges s(b, b₁) e₃ := by
    intro h
    exact hm1 (hsymm h)
  have hm4' : ¬ DisjointEdges s(b, b₂) e₃ := by
    intro h
    exact hm4 (hsymm h)
  have hnb₂ : b₂ ∉ e₃ := by
    intro h
    exact hd0 b₂ ⟨h, by simp⟩
  have hnv : v ∉ e₃ := by
    intro h
    exact hd0 v ⟨h, by simp⟩
  have hnu : u ∉ e₃ := by
    intro h
    exact hd2 u ⟨h, by simp⟩
  have hnb₁ : b₁ ∉ e₃ := by
    intro h
    exact hd3 b₁ ⟨h, by simp⟩
  have hbmem : b ∈ e₃ := by
    by_contra hb
    apply hm1'
    intro x hx
    have hxb : x = b ∨ x = b₁ := by simpa using hx.1
    rcases hxb with rfl | rfl
    · exact hb hx.2
    · exact hnb₁ hx.2
  have hself : ¬ DisjointEdges e₃ e₃ := by
    intro h
    induction e₃ using Sym2.ind with
    | _ x y => exact h x ⟨Sym2.mem_mk_left x y, Sym2.mem_mk_left x y⟩
  clear hsymm
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [shortThetaEdge, shortThetaEdgeVal, shortK4EdgePattern,
      SimpleGraph.lineGraph_adj_iff_exists, DisjointEdges, MeetEdges,
      hbb₁, hbb₂, hbu, hbv', hb₁b₂, hb₁u, hb₁v', hb₂u, hb₂v', huv,
      hd0, hd0', hd2, hd2', hd3, hd3', hd5, hd5', hm1, hm1', hm4, hm4', hself,
      hnb₁, hnb₂, hnu, hnv, hbmem] <;>
    aesop

private theorem shortK4EdgePattern_injective {W : Type*}
    (b b₁ b₂ u v : W) (e₃ : Sym2 W)
    (hnd : [b, b₁, b₂, u, v].Nodup)
    (hd0 : DisjointEdges e₃ s(b₂, v))
    (hd2 : DisjointEdges e₃ s(b₂, u))
    (hd3 : DisjointEdges e₃ s(b₁, u))
    (hd5 : DisjointEdges e₃ s(b₁, v))
    (hne1 : e₃ ≠ s(b, b₁)) (hne4 : e₃ ≠ s(b, b₂)) :
    Function.Injective (shortK4EdgePattern b b₁ b₂ u v e₃) := by
  rcases List.nodup_cons.mp hnd with ⟨hb, hnd₁⟩
  rcases List.nodup_cons.mp hnd₁ with ⟨hb₁, hnd₂⟩
  rcases List.nodup_cons.mp hnd₂ with ⟨hb₂, hndu⟩
  rcases List.nodup_cons.mp hndu with ⟨hu, -⟩
  simp only [List.mem_cons, List.mem_singleton, not_or] at hb hb₁ hb₂ hu
  rcases hb with ⟨hbb₁, hbb₂, hbu, hbv⟩
  rcases hb₁ with ⟨hb₁b₂, hb₁u, hb₁v⟩
  rcases hb₂ with ⟨hb₂u, hb₂v⟩
  have hbv' : b ≠ v := hbv.1
  have hb₁v' : b₁ ≠ v := hb₁v.1
  have hb₂v' : b₂ ≠ v := hb₂v.1
  have huv : u ≠ v := hu.1
  have hne_of_disjoint : ∀ {e f : Sym2 W}, DisjointEdges e f → e ≠ f := by
    intro e f h hef
    subst f
    induction e using Sym2.ind with
    | _ x y => exact h x ⟨Sym2.mem_mk_left x y, Sym2.mem_mk_left x y⟩
  have hne0 : e₃ ≠ s(b₂, v) := hne_of_disjoint hd0
  have hne2 : e₃ ≠ s(b₂, u) := hne_of_disjoint hd2
  have hne3 : e₃ ≠ s(b₁, u) := hne_of_disjoint hd3
  have hne5 : e₃ ≠ s(b₁, v) := hne_of_disjoint hd5
  clear hne_of_disjoint
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [shortK4EdgePattern, Sym2.eq_iff, hbb₁, hbb₂, hbu, hbv',
      hb₁b₂, hb₁u, hb₁v', hb₂u, hb₂v', huv,
      hne0, hne2, hne3, hne5, hne1, hne4] at hij ⊢ <;>
    aesop

/-- Attaching an even positive path to the two internal degree-two vertices of the fixed
theta produces the odd long branch of an overshadowed `K₄` appearance.  The hypotheses are
phrased entirely in terms of the seven labelled line-graph vertices, so applications need no
finite-graph computation. -/
theorem shortK4OvershadowedAppearance {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) (J : SimpleGraph (Fin m))
    (hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (w : Fin 7 → V) (hwinj : Function.Injective w)
    (hrel : ∀ i j : Fin 7,
      shortTheta.lineGraph.Adj (shortThetaEdge i) (shortThetaEdge j) ↔ G.Adj (w i) (w j))
    (Q : List V) (y₁ y₂ : V) (hQ : IsPathFrom G Q y₁ y₂) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (hQK : ∀ x ∈ Q, x ∉ Set.range w)
    (h01 : G.Adj (w 0) (w 1)) (h45 : G.Adj (w 4) (w 5))
    (hy₁0 : G.Adj y₁ (w 0)) (hy₁1 : G.Adj y₁ (w 1))
    (hy₂4 : G.Adj y₂ (w 4)) (hy₂5 : G.Adj y₂ (w 5))
    (hother : ∀ x ∈ Q, ∀ i : Fin 7, G.Adj x (w i) →
      (x = y₁ ∧ (i = 0 ∨ i = 1)) ∨ (x = y₂ ∧ (i = 4 ∨ i = 5)))
    (a : V) (ha0 : G.Adj a (w 0)) (ha1 : G.Adj a (w 1))
    (ha4 : G.Adj a (w 4)) (ha5 : G.Adj a (w 5)) :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
        (ψ : H.lineGraph ≃g G.induce K),
      IsAppearance G J H K ∧ IsOvershadowedAppearance G H K ψ := by
  classical
  let K₀ : Set V := Set.range w
  let φ₀ : shortTheta.lineGraph ≃g G.induce K₀ :=
    shortThetaIsoInduce G w hwinj hrel
  have hzinc : ∀ e : shortTheta.edgeSet,
      (2 : Fin 6) ∈ (e : Sym2 (Fin 6)) ↔
        ((↑(φ₀ e) : V) = w 0 ∨ (↑(φ₀ e) : V) = w 1) := by
    intro e
    constructor
    · intro he
      rcases shortThetaEdge_incident_two e he with rfl | rfl
      · exact Or.inl (shortThetaIsoInduce_apply G w hwinj hrel 0)
      · exact Or.inr (shortThetaIsoInduce_apply G w hwinj hrel 1)
    · rintro (he | he)
      · have := (shortThetaIsoInduce_eq_iff G w hwinj hrel e 0).mp he
        rw [this]
        simp [shortThetaEdge, shortThetaEdgeVal]
      · have := (shortThetaIsoInduce_eq_iff G w hwinj hrel e 1).mp he
        rw [this]
        simp [shortThetaEdge, shortThetaEdgeVal]
  have hz'inc : ∀ e : shortTheta.edgeSet,
      (5 : Fin 6) ∈ (e : Sym2 (Fin 6)) ↔
        ((↑(φ₀ e) : V) = w 4 ∨ (↑(φ₀ e) : V) = w 5) := by
    intro e
    constructor
    · intro he
      rcases shortThetaEdge_incident_five e he with rfl | rfl
      · exact Or.inl (shortThetaIsoInduce_apply G w hwinj hrel 4)
      · exact Or.inr (shortThetaIsoInduce_apply G w hwinj hrel 5)
    · rintro (he | he)
      · have := (shortThetaIsoInduce_eq_iff G w hwinj hrel e 4).mp he
        rw [this]
        simp [shortThetaEdge, shortThetaEdgeVal]
      · have := (shortThetaIsoInduce_eq_iff G w hwinj hrel e 5).mp he
        rw [this]
        simp [shortThetaEdge, shortThetaEdgeVal]
  have hother' : ∀ x ∈ Q, ∀ k ∈ K₀, G.Adj x k →
      (x = y₁ ∧ (k = w 0 ∨ k = w 1)) ∨ (x = y₂ ∧ (k = w 4 ∨ k = w 5)) := by
    intro x hx k hk hxk
    obtain ⟨i, rfl⟩ := hk
    rcases hother x hx i hxk with ⟨hxy, rfl | rfl⟩ | ⟨hxy, rfl | rfl⟩
    · exact Or.inl ⟨hxy, Or.inl rfl⟩
    · exact Or.inl ⟨hxy, Or.inr rfl⟩
    · exact Or.inr ⟨hxy, Or.inl rfl⟩
    · exact Or.inr ⟨hxy, Or.inr rfl⟩
  obtain ⟨H, ρ, p, _, hext, hplen⟩ :=
    Workspace.ProofLemmas.Thm101ThetaAddBranch G K₀ 6 shortTheta φ₀ 2 5
      (by decide) shortTheta_not_adj_two_five
      Q y₁ y₂ (w 0) (w 1) (w 4) (w 5) hQ hQK
      ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨4, rfl⟩ ⟨5, rfl⟩ h01 h45
      hy₁0 hy₁1 hy₂4 hy₂5 hother' hzinc hz'inc
  rcases hext with ⟨hρ, hhom, hpfrom, hp2, hpint, hpcover, hpedges⟩
  have hext' : IsThetaBranchExtension shortTheta 2 5 H ρ p :=
    ⟨hρ, hhom, hpfrom, hp2, hpint, hpcover, hpedges⟩
  obtain ⟨ψ, hold, hnew⟩ :=
    Workspace.ProofLemmas.thetaBranchExtensionLabelledIso G K₀ 6 shortTheta φ₀ 2 5
      shortTheta_not_adj_two_five
      Q y₁ y₂ (w 0) (w 1) (w 4) (w 5) hQ hQK
      hy₁0 hy₁1 hy₂4 hy₂5 hother' hzinc hz'inc
      (6 + (Q.length - 1)) H ρ p hext' hplen
  have hbranchK4 :=
    Workspace.ProofLemmas.Thm101ThetaBranchVerticesAreK4
      shortTheta 0 1 shortThetaTrack shortThetaDatum
      2 5 (by simp [shortThetaTrack, trackInterior])
      (by simp [shortThetaTrack, trackInterior]) H ρ p hext'
  have hQlen2 : 2 ≤ Q.length := by
    have hpos : 0 < Q.length := List.length_pos_of_ne_nil hQ.1.1
    by_contra hnot
    have hlen : Q.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hh := hQ.2.1
    have hl := hQ.2.2
    simp only [List.head?_cons, List.getLast?_singleton] at hh hl
    have hh' : x = y₁ := Option.some.inj hh
    have hl' : x = y₂ := Option.some.inj hl
    exact hy (hh'.symm.trans hl')
  have hQlen3 : 3 ≤ Q.length := by
    rw [Nat.even_iff] at hQeven
    simp only [pathLength] at hQeven
    omega
  have hpLength : trackLength p = Q.length := by
    simp only [trackLength]
    omega
  have hpOdd : Odd (trackLength p) := by
    rw [Nat.odd_iff, hpLength]
    rw [Nat.even_iff] at hQeven
    simp only [pathLength] at hQeven
    omega
  have hpLong : 3 ≤ trackLength p := by rw [hpLength]; exact hQlen3
  have hpBranch : IsBranch H p := by
    have hρ25 : ρ (2 : Fin 6) ≠ ρ 5 := fun h =>
      (show (2 : Fin 6) ≠ 5 by decide) (hρ h)
    apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch hpfrom
    · exact hρ25
    · intro v hv hvB
      rw [hbranchK4.1] at hvB
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvB
      rcases hvB with h | h | h | h
      · exact hpint v hv ⟨0, h.symm⟩
      · exact hpint v hv ⟨1, h.symm⟩
      · exact hpint v hv ⟨2, h.symm⟩
      · exact hpint v hv ⟨5, h.symm⟩
    · rw [hbranchK4.1]; simp
    · rw [hbranchK4.1]; simp
  have hpar : ∀ i : Fin 3,
      trackLength (shortThetaTrack i) % 2 = trackLength (shortThetaTrack 0) % 2 := by
    intro i
    fin_cases i <;> decide
  have hpmod : (1 + trackLength p) % 2 = 2 % 2 := by
    rw [hpLength]
    rw [Nat.even_iff] at hQeven
    simp only [pathLength] at hQeven
    omega
  have hbip : H.IsBipartite :=
    Workspace.ProofLemmas.thetaExtensionIsBipartiteOfParity
      shortTheta 0 1 shortThetaTrack shortThetaDatum
      2 5 1 2 (by decide) (by decide) rfl rfl H ρ p hext' hpar hpmod
  obtain ⟨jiso⟩ := hJiso
  have hsubJ : IsSubdivision J H :=
    Workspace.ProofLemmas.Thm85Five8Transported.isSubdivision_of_iso jiso.symm hbranchK4.2
  have happ : IsAppearance G J H (K₀ ∪ {x : V | x ∈ Q}) :=
    ⟨⟨hsubJ, hbip⟩, ⟨ψ⟩⟩
  have left_exception : ∀ e : Sym2 (Fin (6 + (Q.length - 1))),
      e ∈ incidentEdges H (ρ 2) \
          {e : Sym2 (Fin (6 + (Q.length - 1))) |
            ∃ he : e ∈ H.edgeSet, G.Adj a (↑(ψ ⟨e, he⟩) : V)} →
      e = s(p[0]'(by omega), p[1]'(by omega)) := by
    intro e he
    have hep : e ∈ trackEdges p := by
      have heEdge := he.1.1
      rw [hpedges] at heEdge
      rcases heEdge with ⟨e₀, he₀, hemapEq⟩ | hep
      · have hmem : (2 : Fin 6) ∈ e₀ := by
          have hinc : ρ 2 ∈ Sym2.map ρ e₀ := by rw [hemapEq]; exact he.1.2
          obtain ⟨c, hc, hcρ⟩ := Sym2.mem_map.mp hinc
          have hc2 : c = 2 := hρ hcρ
          simpa [hc2] using hc
        let e₀' : shortTheta.edgeSet := ⟨e₀, he₀⟩
        have heMap : Sym2.map ρ e₀ ∈ H.edgeSet := by rw [hemapEq]; exact he.1.1
        rcases shortThetaEdge_incident_two e₀' hmem with hidx | hidx
        · apply False.elim
          apply he.2
          refine ⟨he.1.1, ?_⟩
          have hlab := hold e₀' heMap
          have hphi : (↑(φ₀ e₀') : V) = w 0 :=
            (shortThetaIsoInduce_eq_iff G w hwinj hrel e₀' 0).2 hidx
          have hlab0 := hlab.trans hphi
          have hedgeEq :
              (⟨Sym2.map ρ (e₀' : Sym2 (Fin 6)), heMap⟩ : H.edgeSet) =
                ⟨e, he.1.1⟩ := Subtype.ext hemapEq
          have hlab' : (↑(ψ ⟨e, he.1.1⟩) : V) = w 0 := by
            rw [← hedgeEq]
            exact hlab0
          rwa [hlab']
        · apply False.elim
          apply he.2
          refine ⟨he.1.1, ?_⟩
          have hlab := hold e₀' heMap
          have hphi : (↑(φ₀ e₀') : V) = w 1 :=
            (shortThetaIsoInduce_eq_iff G w hwinj hrel e₀' 1).2 hidx
          have hlab0 := hlab.trans hphi
          have hedgeEq :
              (⟨Sym2.map ρ (e₀' : Sym2 (Fin 6)), heMap⟩ : H.edgeSet) =
                ⟨e, he.1.1⟩ := Subtype.ext hemapEq
          have hlab' : (↑(ψ ⟨e, he.1.1⟩) : V) = w 1 := by
            rw [← hedgeEq]
            exact hlab0
          rwa [hlab']
      · exact hep
    exact Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdge_at_head hpfrom hp2 hep he.1.2
  have right_exception : ∀ e : Sym2 (Fin (6 + (Q.length - 1))),
      e ∈ incidentEdges H (ρ 5) \
          {e : Sym2 (Fin (6 + (Q.length - 1))) |
            ∃ he : e ∈ H.edgeSet, G.Adj a (↑(ψ ⟨e, he⟩) : V)} →
      e = s(p[p.length - 2]'(by omega), p[p.length - 1]'(by omega)) := by
    intro e he
    have hep : e ∈ trackEdges p := by
      have heEdge := he.1.1
      rw [hpedges] at heEdge
      rcases heEdge with ⟨e₀, he₀, hemapEq⟩ | hep
      · have hmem : (5 : Fin 6) ∈ e₀ := by
          have hinc : ρ 5 ∈ Sym2.map ρ e₀ := by rw [hemapEq]; exact he.1.2
          obtain ⟨c, hc, hcρ⟩ := Sym2.mem_map.mp hinc
          have hc5 : c = 5 := hρ hcρ
          simpa [hc5] using hc
        let e₀' : shortTheta.edgeSet := ⟨e₀, he₀⟩
        have heMap : Sym2.map ρ e₀ ∈ H.edgeSet := by rw [hemapEq]; exact he.1.1
        rcases shortThetaEdge_incident_five e₀' hmem with hidx | hidx
        · apply False.elim
          apply he.2
          refine ⟨he.1.1, ?_⟩
          have hlab := hold e₀' heMap
          have hphi : (↑(φ₀ e₀') : V) = w 4 :=
            (shortThetaIsoInduce_eq_iff G w hwinj hrel e₀' 4).2 hidx
          have hlab0 := hlab.trans hphi
          have hedgeEq :
              (⟨Sym2.map ρ (e₀' : Sym2 (Fin 6)), heMap⟩ : H.edgeSet) =
                ⟨e, he.1.1⟩ := Subtype.ext hemapEq
          have hlab' : (↑(ψ ⟨e, he.1.1⟩) : V) = w 4 := by
            rw [← hedgeEq]
            exact hlab0
          rwa [hlab']
        · apply False.elim
          apply he.2
          refine ⟨he.1.1, ?_⟩
          have hlab := hold e₀' heMap
          have hphi : (↑(φ₀ e₀') : V) = w 5 :=
            (shortThetaIsoInduce_eq_iff G w hwinj hrel e₀' 5).2 hidx
          have hlab0 := hlab.trans hphi
          have hedgeEq :
              (⟨Sym2.map ρ (e₀' : Sym2 (Fin 6)), heMap⟩ : H.edgeSet) =
                ⟨e, he.1.1⟩ := Subtype.ext hemapEq
          have hlab' : (↑(ψ ⟨e, he.1.1⟩) : V) = w 5 := by
            rw [← hedgeEq]
            exact hlab0
          rwa [hlab']
      · exact hep
    exact Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdge_at_last hpfrom hp2 hep he.1.2
  refine ⟨6 + (Q.length - 1), H, K₀ ∪ {x : V | x ∈ Q}, ψ, happ, ?_⟩
  refine ⟨p, ρ 2, ρ 5, hpBranch, hpfrom, hpOdd, hpLong, a, ?_, ?_⟩
  · intro e he f hf
    exact (left_exception e he).trans (left_exception f hf).symm
  · intro e he f hf
    exact (right_exception e he).trans (right_exception f hf).symm

/-- The short-`K₄` constructor in the edge language used by claim 6.1(12). -/
theorem shortK4ComplementAppearanceOfEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) (J : SimpleGraph (Fin m))
    (hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (Q : List V) (y₁ y₂ : V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q)) (hYout : ∀ x ∈ Y, x ∉ K)
    (b b₁ b₂ u v : Fin n) (e₁ e₂ e₃ f₁ f₂ d₁ d₂ g : Sym2 (Fin n))
    (hnd : [b, b₁, b₂, u, v].Nodup)
    (he₁E : e₁ ∈ H.edgeSet) (he₂E : e₂ ∈ H.edgeSet) (he₃E : e₃ ∈ H.edgeSet)
    (hf₁E : f₁ ∈ H.edgeSet) (hf₂E : f₂ ∈ H.edgeSet)
    (hd₁E : d₁ ∈ H.edgeSet) (hd₂E : d₂ ∈ H.edgeSet) (hgE : g ∈ H.edgeSet)
    (he₁eq : e₁ = s(b, b₁)) (he₂eq : e₂ = s(b, b₂))
    (hf₁eq : f₁ = s(b₁, u)) (hf₂eq : f₂ = s(b₂, u))
    (hd₁eq : d₁ = s(b₁, v)) (hd₂eq : d₂ = s(b₂, v))
    (he₃d₂ : DisjointEdges e₃ d₂) (he₃f₂ : DisjointEdges e₃ f₂)
    (he₃f₁ : DisjointEdges e₃ f₁) (he₃d₁ : DisjointEdges e₃ d₁)
    (he₃m₁ : MeetEdges e₃ e₁) (he₃m₂ : MeetEdges e₃ e₂)
    (he₃ne₁ : e₃ ≠ e₁) (he₃ne₂ : e₃ ≠ e₂)
    (hd₂X₁ : d₂ ∈ extraEdges G H K φ Y y₁)
    (he₁X₁ : e₁ ∈ extraEdges G H K φ Y y₁)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y)
    (hf₁X : f₁ ∈ completeEdges G H K φ Y)
    (he₂X₂ : e₂ ∈ extraEdges G H K φ Y y₂)
    (hd₁X₂ : d₁ ∈ extraEdges G H K φ Y y₂)
    (he₃X : e₃ ∈ completeEdges G H K φ Y)
    (hgd₂ : DisjointEdges g d₂) (hge₁ : DisjointEdges g e₁)
    (hge₂ : DisjointEdges g e₂) (hgd₁ : DisjointEdges g d₁) :
    ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
        (ψ : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ J H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' ψ := by
  classical
  subst e₁
  subst e₂
  subst f₁
  subst f₂
  subst d₁
  subst d₂
  let edge : Fin 7 → H.edgeSet := fun i =>
    ⟨shortK4EdgePattern b b₁ b₂ u v e₃ i, by
      fin_cases i <;> simp only [shortK4EdgePattern] <;> assumption⟩
  let w : Fin 7 → V := fun i => (↑(φ (edge i)) : V)
  have hedgeInj : Function.Injective edge := by
    intro i j hij
    apply shortK4EdgePattern_injective b b₁ b₂ u v e₃ hnd
      he₃d₂ he₃f₂ he₃f₁ he₃d₁ he₃ne₁ he₃ne₂
    exact congrArg Subtype.val hij
  have hwinj : Function.Injective w := by
    intro i j hij
    apply hedgeInj
    apply (EquivLike.injective φ)
    exact Subtype.ext hij
  have hpattern := shortK4EdgePattern_disjoint b b₁ b₂ u v e₃ hnd
    he₃d₂ he₃f₂ he₃f₁ he₃d₁ he₃m₁ he₃m₂
  have hrel : ∀ i j : Fin 7,
      shortTheta.lineGraph.Adj (shortThetaEdge i) (shortThetaEdge j) ↔
        Gᶜ.Adj (w i) (w j) := by
    intro i j
    rw [compl_adj_image_iff_disjoint G H K φ (edge i) (edge j)]
    simpa only [edge] using hpattern i j
  have hQK : ∀ x ∈ Q, x ∉ Set.range w := by
    intro x hx hxr
    obtain ⟨i, rfl⟩ := hxr
    exact hYout (w i) ((hQY (w i)).mp hx) (φ (edge i)).property
  have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
  have hy₂Y : y₂ ∈ Y := (hQY y₂).mp (List.mem_of_mem_getLast? hQ.2.2)
  have hy₁0 : Gᶜ.Adj y₁ (w 0) := by
    have h := (compl_adj_image_of_extraEdges_iff G H K Y φ hd₂E hd₂X₁
      hy₁Y (hYout y₁ hy₁Y)).2 rfl
    simpa only [w, edge, shortK4EdgePattern] using h
  have hy₁1 : Gᶜ.Adj y₁ (w 1) := by
    have h := (compl_adj_image_of_extraEdges_iff G H K Y φ he₁E he₁X₁
      hy₁Y (hYout y₁ hy₁Y)).2 rfl
    simpa only [w, edge, shortK4EdgePattern] using h
  have hy₂4 : Gᶜ.Adj y₂ (w 4) := by
    have h := (compl_adj_image_of_extraEdges_iff G H K Y φ he₂E he₂X₂
      hy₂Y (hYout y₂ hy₂Y)).2 rfl
    simpa only [w, edge, shortK4EdgePattern] using h
  have hy₂5 : Gᶜ.Adj y₂ (w 5) := by
    have h := (compl_adj_image_of_extraEdges_iff G H K Y φ hd₁E hd₁X₂
      hy₂Y (hYout y₂ hy₂Y)).2 rfl
    simpa only [w, edge, shortK4EdgePattern] using h
  have hother : ∀ x ∈ Q, ∀ i : Fin 7, Gᶜ.Adj x (w i) →
      (x = y₁ ∧ (i = 0 ∨ i = 1)) ∨ (x = y₂ ∧ (i = 4 ∨ i = 5)) := by
    intro x hx i hxi
    have hxY := (hQY x).mp hx
    have hxK := hYout x hxY
    fin_cases i
    · left
      refine ⟨?_, Or.inl rfl⟩
      exact (compl_adj_image_of_extraEdges_iff G H K Y φ hd₂E hd₂X₁ hxY hxK).1
        (by simpa only [w, edge, shortK4EdgePattern] using hxi)
    · left
      refine ⟨?_, Or.inr rfl⟩
      exact (compl_adj_image_of_extraEdges_iff G H K Y φ he₁E he₁X₁ hxY hxK).1
        (by simpa only [w, edge, shortK4EdgePattern] using hxi)
    · exact False.elim ((not_compl_adj_image_of_completeEdges G H K Y φ hf₂E hf₂X hxY)
        (by simpa only [w, edge, shortK4EdgePattern] using hxi))
    · exact False.elim ((not_compl_adj_image_of_completeEdges G H K Y φ hf₁E hf₁X hxY)
        (by simpa only [w, edge, shortK4EdgePattern] using hxi))
    · right
      refine ⟨?_, Or.inl rfl⟩
      exact (compl_adj_image_of_extraEdges_iff G H K Y φ he₂E he₂X₂ hxY hxK).1
        (by simpa only [w, edge, shortK4EdgePattern] using hxi)
    · right
      refine ⟨?_, Or.inr rfl⟩
      exact (compl_adj_image_of_extraEdges_iff G H K Y φ hd₁E hd₁X₂ hxY hxK).1
        (by simpa only [w, edge, shortK4EdgePattern] using hxi)
    · exact False.elim ((not_compl_adj_image_of_completeEdges G H K Y φ he₃E he₃X hxY)
        (by simpa only [w, edge, shortK4EdgePattern] using hxi))
  have h01 : Gᶜ.Adj (w 0) (w 1) := by
    rw [compl_adj_image_iff_disjoint G H K φ (edge 0) (edge 1)]
    exact (hpattern 0 1).1 (by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨?_, 2, by simp [shortThetaEdge, shortThetaEdgeVal],
        by simp [shortThetaEdge, shortThetaEdgeVal]⟩
      intro h
      have := congrArg Subtype.val h
      simp [shortThetaEdge, shortThetaEdgeVal] at this)
  have h45 : Gᶜ.Adj (w 4) (w 5) := by
    rw [compl_adj_image_iff_disjoint G H K φ (edge 4) (edge 5)]
    exact (hpattern 4 5).1 (by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      refine ⟨?_, 5, by simp [shortThetaEdge, shortThetaEdgeVal],
        by simp [shortThetaEdge, shortThetaEdgeVal]⟩
      intro h
      have := congrArg Subtype.val h
      simp [shortThetaEdge, shortThetaEdgeVal] at this)
  let a : V := (↑(φ ⟨g, hgE⟩) : V)
  have ha0 : Gᶜ.Adj a (w 0) := by
    rw [compl_adj_image_iff_disjoint G H K φ ⟨g, hgE⟩ (edge 0)]
    simpa only [edge, shortK4EdgePattern] using hgd₂
  have ha1 : Gᶜ.Adj a (w 1) := by
    rw [compl_adj_image_iff_disjoint G H K φ ⟨g, hgE⟩ (edge 1)]
    simpa only [edge, shortK4EdgePattern] using hge₁
  have ha4 : Gᶜ.Adj a (w 4) := by
    rw [compl_adj_image_iff_disjoint G H K φ ⟨g, hgE⟩ (edge 4)]
    simpa only [edge, shortK4EdgePattern] using hge₂
  have ha5 : Gᶜ.Adj a (w 5) := by
    rw [compl_adj_image_iff_disjoint G H K φ ⟨g, hgE⟩ (edge 5)]
    simpa only [edge, shortK4EdgePattern] using hgd₁
  exact shortK4OvershadowedAppearance Gᶜ m J hJiso w hwinj hrel Q y₁ y₂ hQ hy
    hQeven hQK h01 h45 hy₁0 hy₁1 hy₂4 hy₂5 hother a ha0 ha1 ha4 ha5

end Workspace.ProofLemmas.Thm61EvenEndgameComplementAppearance
