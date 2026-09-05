import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# "We may assume `V(G) = …`, by deleting any other vertices"

§2 uses this reduction three times — in the proofs of 2.9, 2.10 and 2.11 — always in order to
build an auxiliary graph on a restricted vertex set and then read holes and antiholes of that
auxiliary graph back in `G`.

**Do not realise the deletion as `G.induce W`.**  That changes the vertex type to `↥W`, and
moving `AnticonnectedSet G X` inside then needs the `induce`-re-association
`(G.induce S).induce T ≃g G.induce (Subtype.val '' T)`, which this Mathlib checkout does not
have (see `lean_knowledge.md`).

Instead **isolate**: `restrictTo G W` keeps every edge of `G` inside `W` and makes every vertex
outside `W` isolated.  The vertex type never changes, so every statement about `G` transfers by
a one-line adjacency rewrite, and the key fact still holds:

* no hole of `restrictTo G W` can use a vertex outside `W` — such a vertex has degree `0`, while
  a hole vertex has degree `2` (`mem_of_mem_hole`);
* no hole of `(restrictTo G W)ᶜ` can use a vertex outside `W` either — there such a vertex is
  adjacent to *everything*, while a hole of length `≥ 4` gives it only two neighbours
  (`mem_of_mem_compl_hole`).

Those two facts are exactly what the paper gets out of deleting the other vertices, and they are
what make *"`C` necessarily uses `y`"* and *"the ends of `Q` belong to `X ∪ {pₙ}`"* go through.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.RestrictGraph

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-! ## The construction -/

/-- `restrictTo G W` is `G` with every vertex outside `W` isolated.  On `W` it agrees with `G`,
so it is the paper's `G|W` realised without changing the vertex type. -/
def restrictTo (G : SimpleGraph V) (W : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ W ∧ y ∈ W
  symm := by
    rintro x y ⟨h, hx, hy⟩
    exact ⟨h.symm, hy, hx⟩
  loopless := by
    constructor
    rintro x ⟨h, -, -⟩
    exact G.irrefl h

variable {G : SimpleGraph V} {W X : Set V} {x y : V} {c q : List V}

theorem adj_iff : (restrictTo G W).Adj x y ↔ (G.Adj x y ∧ x ∈ W ∧ y ∈ W) := Iff.rfl

/-- Inside `W`, the restriction has exactly the edges of `G`. -/
theorem adj_of_mem (hx : x ∈ W) (hy : y ∈ W) : (restrictTo G W).Adj x y ↔ G.Adj x y :=
  ⟨fun h => h.1, fun h => ⟨h, hx, hy⟩⟩

/-- Inside `W`, the complement of the restriction has exactly the non-edges of `G`. -/
theorem compl_adj_of_mem (hx : x ∈ W) (hy : y ∈ W) :
    (restrictTo G W)ᶜ.Adj x y ↔ Gᶜ.Adj x y := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun hg => h ⟨hg, hx, hy⟩⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, fun hg => h hg.1⟩

/-- A vertex outside `W` is isolated. -/
theorem not_adj_of_notMem (hx : x ∉ W) : ¬ (restrictTo G W).Adj x y := fun h => hx h.2.1

/-- A vertex outside `W` is adjacent, in the complement, to every other vertex. -/
theorem compl_adj_of_notMem (hx : x ∉ W) (hne : x ≠ y) : (restrictTo G W)ᶜ.Adj x y :=
  ⟨hne, not_adj_of_notMem hx⟩

/-! ## Every hole, and every antihole, stays inside `W` -/

/-- On a cycle of length `≥ 4` there is always an index `j` that is neither `i` nor either of
its two cyclic neighbours.  This is what turns "degree `2` in a hole" into a contradiction. -/
private theorem far_index {len i : ℕ} (h4 : 4 ≤ len) (hi : i < len) :
    ∃ j, j < len ∧ j ≠ i ∧ ¬ (j = (i + 1) % len ∨ i = (j + 1) % len) := by
  rcases lt_or_ge (i + 2) len with h | h
  · refine ⟨i + 2, by omega, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (show i + 1 < len by omega)]
    rcases lt_or_ge (i + 3) len with h3 | h3
    · rw [Nat.mod_eq_of_lt (show i + 2 + 1 < len by omega)]; omega
    · rw [show i + 2 + 1 = len by omega, Nat.mod_self]; omega
  · rcases (by omega : i = len - 2 ∨ i = len - 1) with rfl | rfl
    · refine ⟨0, by omega, by omega, ?_⟩
      rw [show len - 2 + 1 = len - 1 by omega, Nat.mod_eq_of_lt (show len - 1 < len by omega),
        Nat.mod_eq_of_lt (show (0 : ℕ) + 1 < len by omega)]
      omega
    · refine ⟨1, by omega, by omega, ?_⟩
      rw [show len - 1 + 1 = len by omega, Nat.mod_self,
        Nat.mod_eq_of_lt (show (1 : ℕ) + 1 < len by omega)]
      omega

/-- **A vertex with no neighbours at all cannot lie on a hole of the complement**: in `Kᶜ` it is
adjacent to every other vertex, while a hole of length `≥ 4` gives it only two neighbours.  This
is the general form of `mem_of_mem_compl_hole`, and is what the auxiliary graphs of §2 need for
their *"`C` necessarily uses `y`"* steps (there the isolated vertex is an old vertex outside the
kept set, sitting in `G₀ = (restrictTo G W) +ᵥ S`). -/
theorem notMem_compl_hole_of_isolated {U : Type*} {K : SimpleGraph U} {l : List U}
    (hl : IsHoleList Kᶜ l) {z : U} (hz : ∀ u, ¬ K.Adj z u) : z ∉ l := by
  obtain ⟨h4, hnd, hadj⟩ := hl
  intro hzl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hzl
  obtain ⟨j, hj, hji, hnot⟩ := far_index h4 hi
  have hne : ((l)[i]'hi) ≠ ((l)[j]'hj) := fun h => hji (hnd.getElem_inj_iff.mp h).symm
  exact hnot ((hadj i j hi hj).mp ⟨hne, fun h => hz _ h⟩)

/-- **A hole of `restrictTo G W` lives inside `W`**: a vertex outside `W` is isolated, so it
cannot have the two neighbours a hole vertex has. -/
theorem mem_of_mem_hole (hc : IsHoleList (restrictTo G W) c) : ∀ z ∈ c, z ∈ W := by
  obtain ⟨h4, hnd, hadj⟩ := hc
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  have hpos : 0 < c.length := by omega
  have hj : (i + 1) % c.length < c.length := Nat.mod_lt _ hpos
  exact ((hadj i ((i + 1) % c.length) hi hj).mpr (Or.inl rfl)).2.1

/-- **An antihole of `restrictTo G W` lives inside `W`**: a vertex outside `W` is adjacent in
the complement to *every* other vertex, so it cannot sit on a hole of length `≥ 4`. -/
theorem mem_of_mem_compl_hole (hc : IsHoleList (restrictTo G W)ᶜ c) : ∀ z ∈ c, z ∈ W := by
  obtain ⟨h4, hnd, hadj⟩ := hc
  intro z hz
  by_contra hzW
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  obtain ⟨j, hj, hji, hnot⟩ := far_index h4 hi
  -- `((c)[i]'hi)`, not `c[i]'hi`: a bare `c[` is a single lexer atom (Mathlib cycle notation).
  have hne : ((c)[i]'hi) ≠ ((c)[j]'hj) := fun h => hji (hnd.getElem_inj_iff.mp h).symm
  exact hnot ((hadj i j hi hj).mp (compl_adj_of_notMem hzW hne))

/-! ## Transfer of holes, antiholes, paths and Berge-ness -/

/-- A hole of the restriction is a hole of `G`. -/
theorem isHoleList_of_restrict (hc : IsHoleList (restrictTo G W) c) : IsHoleList G c := by
  have hmem := mem_of_mem_hole hc
  obtain ⟨h4, hnd, hadj⟩ := hc
  refine ⟨h4, hnd, fun i j hi hj => ?_⟩
  rw [← adj_of_mem (G := G) (W := W) (hmem _ (List.getElem_mem hi)) (hmem _ (List.getElem_mem hj))]
  exact hadj i j hi hj

/-- An antihole of the restriction is an antihole of `G`. -/
theorem isHoleList_compl_of_restrict (hc : IsHoleList (restrictTo G W)ᶜ c) :
    IsHoleList Gᶜ c := by
  have hmem := mem_of_mem_compl_hole hc
  obtain ⟨h4, hnd, hadj⟩ := hc
  refine ⟨h4, hnd, fun i j hi hj => ?_⟩
  rw [← compl_adj_of_mem (G := G) (W := W) (hmem _ (List.getElem_mem hi))
    (hmem _ (List.getElem_mem hj))]
  exact hadj i j hi hj

/-- **The restriction of a Berge graph is Berge.** -/
theorem berge_restrictTo (hG : Berge G) : Berge (restrictTo G W) :=
  ⟨fun c hc => hG.1 c (isHoleList_of_restrict hc),
   fun c hc => hG.2 c (isHoleList_compl_of_restrict hc)⟩

/-- A list inside `W` is a path of the restriction exactly when it is a path of `G`. -/
theorem isPathList_iff_of_subset (h : ∀ z ∈ q, z ∈ W) :
    IsPathList (restrictTo G W) q ↔ IsPathList G q := by
  constructor
  · rintro ⟨hne, hnd, hadj⟩
    refine ⟨hne, hnd, fun i j hi hj => ?_⟩
    rw [← adj_of_mem (G := G) (W := W) (h _ (List.getElem_mem hi)) (h _ (List.getElem_mem hj))]
    exact hadj i j hi hj
  · rintro ⟨hne, hnd, hadj⟩
    refine ⟨hne, hnd, fun i j hi hj => ?_⟩
    rw [adj_of_mem (G := G) (W := W) (h _ (List.getElem_mem hi)) (h _ (List.getElem_mem hj))]
    exact hadj i j hi hj

/-- Naming the ends is unaffected. -/
theorem isPathFrom_iff_of_subset (h : ∀ z ∈ q, z ∈ W) {u v : V} :
    IsPathFrom (restrictTo G W) q u v ↔ IsPathFrom G q u v := by
  unfold IsPathFrom
  rw [isPathList_iff_of_subset h]

/-- The same for *anti*paths: inside `W` the two complements agree. -/
theorem isPathList_compl_iff_of_subset (h : ∀ z ∈ q, z ∈ W) :
    IsPathList (restrictTo G W)ᶜ q ↔ IsPathList Gᶜ q := by
  constructor
  · rintro ⟨hne, hnd, hadj⟩
    refine ⟨hne, hnd, fun i j hi hj => ?_⟩
    rw [← compl_adj_of_mem (G := G) (W := W) (h _ (List.getElem_mem hi))
      (h _ (List.getElem_mem hj))]
    exact hadj i j hi hj
  · rintro ⟨hne, hnd, hadj⟩
    refine ⟨hne, hnd, fun i j hi hj => ?_⟩
    rw [compl_adj_of_mem (G := G) (W := W) (h _ (List.getElem_mem hi))
      (h _ (List.getElem_mem hj))]
    exact hadj i j hi hj

/-- Naming the ends of an antipath is unaffected. -/
theorem isAntipathFrom_iff_of_subset (h : ∀ z ∈ q, z ∈ W) {u v : V} :
    IsAntipathFrom (restrictTo G W) q u v ↔ IsAntipathFrom G q u v := by
  unfold IsAntipathFrom IsPathFrom
  rw [isPathList_compl_iff_of_subset h]

/-- **Anticonnectedness transfers**, because on `W` the two complements agree.  This is the
step that `G.induce W` cannot do without the missing `induce_induce`. -/
theorem anticonnectedSet_restrictTo (hXW : X ⊆ W) :
    AnticonnectedSet (restrictTo G W) X ↔ AnticonnectedSet G X := by
  have hEq : ((restrictTo G W)ᶜ).induce X = (Gᶜ).induce X := by
    ext a b
    exact compl_adj_of_mem (G := G) (W := W) (hXW a.2) (hXW b.2)
  show ((restrictTo G W)ᶜ.induce X).Preconnected ↔ ((Gᶜ).induce X).Preconnected
  rw [hEq]

/-- `X`-completeness transfers for vertices of `W`. -/
theorem vertexComplete_restrictTo (hXW : X ⊆ W) (hx : x ∈ W) :
    VertexComplete (restrictTo G W) x X ↔ VertexComplete G x X := by
  constructor
  · intro h z hz
    exact (h z hz).1
  · intro h z hz
    exact ⟨h z hz, hx, hXW hz⟩

end Workspace.ProofLemmas.RestrictGraph
