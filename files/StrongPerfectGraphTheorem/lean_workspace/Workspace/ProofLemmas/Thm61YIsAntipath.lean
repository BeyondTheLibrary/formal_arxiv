import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.Thm61Setup

/-!
# 6.1, setup: a minimal `Y` is the vertex set of an antipath

PAPER (proof of 6.1, printed p. 29), the second, third and fourth sentences:

> *"Let `X` be the set of all `Y`-complete vertices in `L(H)`.  Choose two vertices of `L(H)`,
> both incident in `H` with the same branch-vertex of `H`, and both not in `X`.  Then there is
> an antipath joining them with interior in `Y`, and the common neighbours of the interior of
> this antipath do not saturate `L(H)`.  From the minimality of `Y` it follows that this
> antipath contains all vertices in `Y`.  Consequently, `Y` is the vertex set of an antipath
> with ends `y₁, y₂`, say.  From the hypothesis, `|Y| ≥ 2`, since the neighbours of any vertex
> in `Y` saturate `L(H)`, so `y₁, y₂` are distinct."*

Unwound, the argument is:

* `X` does not saturate `L(H)`, so some branch-vertex `v` of `H` has two edges `e ≠ f` in
  `δ_H(v)` outside `X`; as vertices of `L(H)` they are adjacent (they share the end `v`), and
  neither is `Y`-complete.
* `Y` is anticonnected, so there is an antipath of `G` from `e` to `f` (as vertices of `G`,
  through `φ`) all of whose internal vertices lie in `Y`; write `Y'` for the set of those
  internal vertices.  Since `e` and `f` are *adjacent* in `G`, this antipath has length `≥ 2`,
  i.e. `Y'` is nonempty.
* `Y'` is anticonnected (the interior of a path is a path) and neither `e` nor `f` is
  `Y'`-complete — `e` is nonadjacent to the first internal vertex and `f` to the last — so the
  set of `Y'`-complete vertices of `L(H)` fails to saturate `L(H)` at the branch-vertex `v`.
* By the minimality of `Y`, `Y'` is not a *proper* subset of `Y`; since `Y' ⊆ Y`, `Y' = Y`.  So
  `Y` is exactly the vertex set of the interior of that antipath, which is itself an antipath,
  with ends `y₁, y₂` the first and last internal vertices.
* Finally `Y` is not a singleton: each `y ∈ Y` is major, i.e. the set of its neighbours in
  `L(H)` — which for `Y = {y}` is exactly `X` — saturates `L(H)`, contrary to hypothesis.  Hence
  the interior has at least two vertices and `y₁ ≠ y₂`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61YIsAntipath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup

/-- The first vertex of a list, read off from `head?`. -/
private theorem getElem_zero_of_head? {V : Type*} {q : List V} {u : V} (h : q.head? = some u)
    (hq : 0 < q.length) : q[0]'hq = u := by
  cases q with
  | nil => simp at hq
  | cons a t => simpa using h

/-- The last vertex of a list, read off from `getLast?`. -/
private theorem getElem_last_of_getLast? {V : Type*} {q : List V} {w : V}
    (h : q.getLast? = some w) (hq : 0 < q.length) : q[q.length - 1]'(by omega) = w := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
  simpa using h

/-- A path between two **adjacent** (hence distinct) vertices has at least three vertices:
a two-vertex path would make its ends adjacent, and a one-vertex path would identify them. -/
private theorem three_le_length {V : Type*} {G : SimpleGraph V} {q : List V} {u w : V}
    (hq : IsPathFrom G q u w) (hne : u ≠ w) (hnadj : ¬ G.Adj u w) : 3 ≤ q.length := by
  obtain ⟨hp, hh, hl⟩ := hq
  rcases q with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hh
  · simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.getLast?_singleton, Option.some.injEq] at hl
    exact absurd (hh ▸ hl ▸ rfl) hne
  · simp only [List.head?_cons, Option.some.injEq] at hh
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hl
    subst hh; subst hl
    exact absurd (by simpa using (hp.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)) hnadj
  · simp

/-- **6.1, setup.**  A minimal anticonnected set of major vertices whose common neighbours do
not saturate `L(H)` is the vertex set of an antipath with two distinct ends `y₁, y₂`. -/
theorem minimal_Y_is_vertex_set_of_antipath
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, VertexComplete G (↑(φ ⟨e, he⟩) : V) Y})
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          VertexComplete G (↑(φ ⟨e, he⟩) : V) Y₁}) :
    ∃ (y₁ y₂ : V) (Q : List V),
      IsAntipathFrom G Q y₁ y₂ ∧ (∀ v : V, v ∈ Q ↔ v ∈ Y) ∧ y₁ ≠ y₂ := by
  classical
  replace hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y) := hnotsat
  replace hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁) := hmin
  -- *"From the hypothesis, `|Y| ≥ 2`, since the neighbours of any vertex in `Y` saturate
  -- `L(H)`"*: `Y` cannot be a singleton.
  have hnotsingleton : ∀ y : V, Y ≠ ({y} : Set V) := by
    intro y hYy
    have hyY : y ∈ Y := by rw [hYy]; rfl
    obtain ⟨-, hsat⟩ := hYmajor y hyY
    apply hnotsat
    have hEq : completeEdges G H K φ Y
        = {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj y (↑(φ ⟨e, he⟩) : V)} := by
      rw [hYy]
      ext e
      constructor
      · rintro ⟨he, hc⟩
        exact ⟨he, (G.adj_comm _ _).mp (hc y rfl)⟩
      · rintro ⟨he, hadj⟩
        exact ⟨he, by rintro x rfl; exact (G.adj_comm _ _).mp hadj⟩
    rw [hEq]
    exact hsat
  -- *"Choose two vertices of `L(H)`, both incident in `H` with the same branch-vertex of `H`,
  -- and both not in `X`."*
  have hex : ∃ v ∈ branchVertices H,
      (incidentEdges H v \ completeEdges G H K φ Y).Nontrivial := by
    by_contra hc
    apply hnotsat
    intro v hv
    rw [← Set.not_nontrivial_iff]
    exact fun hnt => hc ⟨v, hv, hnt⟩
  obtain ⟨v, hv, e, hemem, f, hfmem, hef⟩ := hex
  obtain ⟨⟨heE, hve⟩, heX⟩ := hemem
  obtain ⟨⟨hfE, hvf⟩, hfX⟩ := hfmem
  set u : V := (↑(φ ⟨e, heE⟩) : V) with hudef
  set w : V := (↑(φ ⟨f, hfE⟩) : V) with hwdef
  -- The two edges share the end `v`, so they are adjacent in `L(H)`, hence in `G`.
  have hadjuw : G.Adj u w := by
    have hlg : H.lineGraph.Adj ⟨e, heE⟩ ⟨f, hfE⟩ := by
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨fun hcon => hef (congrArg Subtype.val hcon), v, hve, hvf⟩
    exact φ.map_rel_iff.mpr hlg
  have huY : u ∉ Y := fun hc => (hYmajor u hc).1 (φ ⟨e, heE⟩).2
  have hwY : w ∉ Y := fun hc => (hYmajor w hc).1 (φ ⟨f, hfE⟩).2
  -- Neither `e` nor `f` is `Y`-complete, i.e. each has a `Ḡ`-neighbour in `Y`.
  have hunc : ∃ a ∈ Y, Gᶜ.Adj u a := by
    by_contra hc
    refine heX ⟨heE, fun x hx => ?_⟩
    by_contra hadj
    exact hc ⟨x, hx, (G.compl_adj u x).mpr ⟨by rintro rfl; exact huY hx, hadj⟩⟩
  have hwnc : ∃ a ∈ Y, Gᶜ.Adj w a := by
    by_contra hc
    refine hfX ⟨hfE, fun x hx => ?_⟩
    by_contra hadj
    exact hc ⟨x, hx, (G.compl_adj w x).mpr ⟨by rintro rfl; exact hwY hx, hadj⟩⟩
  -- *"Then there is an antipath joining them with interior in `Y`."*
  obtain ⟨q, hq, hqint⟩ :=
    PathInteriorIn.exists_path_interior_in (G := Gᶜ) hYanti huY hwY hunc hwnc
  have hpos : 0 < q.length := List.length_pos_iff.mpr hq.1.1
  have hu0 : q[0]'hpos = u := getElem_zero_of_head? hq.2.1 hpos
  have hwl : q[q.length - 1]'(by omega) = w := getElem_last_of_getLast? hq.2.2 hpos
  have h3 : 3 ≤ q.length :=
    three_le_length (G := Gᶜ) hq hadjuw.ne (fun hcon => ((G.compl_adj u w).mp hcon).2 hadjuw)
  -- *"the common neighbours of the interior of this antipath do not saturate `L(H)`"*
  have hintpath := PathGlue.isPathFrom_interior (G := Gᶜ) hq.1 h3
  have hq1mem : (q[1]'(by omega)) ∈ ({x : V | x ∈ SPGT.interior q} : Set V) :=
    List.mem_of_mem_head? hintpath.2.1
  have hq2mem : (q[q.length - 2]'(by omega)) ∈ ({x : V | x ∈ SPGT.interior q} : Set V) :=
    List.mem_of_mem_getLast? hintpath.2.2
  have hnadj1 : ¬ G.Adj u (q[1]'(by omega)) := by
    have hadj : Gᶜ.Adj (q[0]'hpos) (q[1]'(by omega)) :=
      (hq.1.2.2 0 1 hpos (by omega)).mpr (Or.inl rfl)
    rw [hu0] at hadj
    exact ((G.compl_adj _ _).mp hadj).2
  have hnadj2 : ¬ G.Adj w (q[q.length - 2]'(by omega)) := by
    have hadj : Gᶜ.Adj (q[q.length - 2]'(by omega)) (q[q.length - 1]'(by omega)) :=
      (hq.1.2.2 (q.length - 2) (q.length - 1) (by omega) (by omega)).mpr (Or.inl (by omega))
    rw [hwl] at hadj
    exact fun hcon => ((G.compl_adj _ _).mp hadj).2 hcon.symm
  have heY' : e ∉ completeEdges G H K φ {x : V | x ∈ SPGT.interior q} := by
    rintro ⟨he', hc⟩
    exact hnadj1 (hc _ hq1mem)
  have hfY' : f ∉ completeEdges G H K φ {x : V | x ∈ SPGT.interior q} := by
    rintro ⟨hf', hc⟩
    exact hnadj2 (hc _ hq2mem)
  have hnotsat' :
      ¬ SaturatesLineGraph H (completeEdges G H K φ {x : V | x ∈ SPGT.interior q}) := by
    intro hsat
    exact hef (hsat v hv ⟨⟨heE, hve⟩, heY'⟩ ⟨⟨hfE, hvf⟩, hfY'⟩)
  -- *"From the minimality of `Y` it follows that this antipath contains all vertices in `Y`."*
  have hY'sub : {x : V | x ∈ SPGT.interior q} ⊆ Y := fun x hx => hqint x hx
  have hY'anti : AnticonnectedSet G {x : V | x ∈ SPGT.interior q} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList (G := Gᶜ) hintpath.1
  have hY'eq : {x : V | x ∈ SPGT.interior q} = Y := by
    by_contra hne'
    exact hnotsat' (hmin _ (Set.ssubset_iff_subset_ne.mpr ⟨hY'sub, hne'⟩) hY'anti)
  -- *"`|Y| ≥ 2` … so `y₁, y₂` are distinct."*
  have h4 : 4 ≤ q.length := by
    by_contra hc
    have hlen1 : (SPGT.interior q).length = 1 := by
      rw [PathBasics.interior_length]; omega
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hlen1
    apply hnotsingleton z
    rw [← hY'eq, hz]
    ext x
    simp
  refine ⟨q[1]'(by omega), q[q.length - 2]'(by omega), SPGT.interior q, hintpath, ?_, ?_⟩
  · intro x
    rw [← hY'eq]
    exact Iff.rfl
  · exact PathBasics.path_ne_of_ne_index hq.1 (by omega) (by omega) (by omega)

end Workspace.ProofLemmas.Thm61YIsAntipath
