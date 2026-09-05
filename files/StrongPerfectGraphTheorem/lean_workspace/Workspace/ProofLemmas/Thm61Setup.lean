import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# 6.1, setup: the three sets `X`, `X₁`, `X₂`

PAPER (proof of 6.1, printed p. 29), the closing sentences of the opening paragraph:

> *"Now for `i = 1, 2`, `Y \ {yᵢ}` is anticonnected; let `Xᵢ` be the set of `Y \ {yᵢ}`-complete
> vertices in `L(H)` that are not in `X`.  So `X ∪ Xᵢ` is the set of all `Y \ {yᵢ}`-complete
> vertices in `L(H)`.  From the minimality of `Y`, both `X ∪ X₁` and `X ∪ X₂` saturate `L(H)`.
> In terms of `H`, we see that `X, X₁, X₂` are mutually disjoint subsets of `E(H)`, and for
> every branch-vertex `b` of `H` and for `i = 1, 2`, at most one edge of `H` incident with `b`
> does not belong to `X ∪ Xᵢ`."*

The last clause is exactly `SaturatesLineGraph H (X ∪ Xᵢ)` (unfolding
`Appearances.SaturatesLineGraph`), so it is not stated separately.

`completeEdges G H K φ Z` is the set of `Z`-complete vertices of `L(H)`, read back through `φ`
as a set of edges of `H`; it is *definitionally* the set written out in the statement of 6.1.
Thus `X = completeEdges … Y` and `Xᵢ = extraEdges … Y yᵢ`.

Everything here is proved.  The only genuinely geometric input is that `Y \ {yᵢ}` is
anticonnected, which holds because `Y` is the vertex set of the antipath `Q` between `y₁` and
`y₂`, and deleting an *end* of a path leaves a path.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- **`X`** (printed p. 29): *"Let `X` be the set of all `Y`-complete vertices in `L(H)`."*
More generally, for any set `Z` of vertices of `G`, the set of `Z`-complete vertices of `L(H)`,
read back through `φ` as a set of edges of `H`. -/
def completeEdges {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Z : Set V) : Set (Sym2 W) :=
  {e : Sym2 W | ∃ he : e ∈ H.edgeSet, VertexComplete G (↑(φ ⟨e, he⟩) : V) Z}

/-- **`Xᵢ`** (printed p. 29): *"let `Xᵢ` be the set of `Y \ {yᵢ}`-complete vertices in `L(H)`
that are not in `X`."* -/
def extraEdges {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y : V) : Set (Sym2 W) :=
  completeEdges G H K φ (Y \ {y}) \ completeEdges G H K φ Y

/-- Deleting an *end* of an antipath leaves an antipath, so the rest of its vertex set is still
anticonnected.  (Printed p. 29: *"Now for `i = 1, 2`, `Y \ {yᵢ}` is anticonnected"*.) -/
private theorem anticonnected_diff_head {V : Type*} {G : SimpleGraph V} {Y : Set V} {Q : List V}
    {u : V} (hp : IsPathList Gᶜ Q) (hhead : Q.head? = some u) (hlen : 1 < Q.length)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) : AnticonnectedSet G (Y \ {u}) := by
  have hset : {z : V | z ∈ Q.drop 1} = Y \ {u} := by
    obtain ⟨t, rfl⟩ : ∃ t : List V, Q = u :: t := by
      cases Q with
      | nil => simp at hhead
      | cons a t => exact ⟨t, by simp at hhead; rw [hhead]⟩
    have hnd := hp.2.1
    have hut : u ∉ t := by
      simpa using (List.nodup_cons.mp hnd).1
    ext z
    simp only [List.drop_succ_cons, List.drop_zero, Set.mem_setOf_eq, Set.mem_diff,
      Set.mem_singleton_iff]
    constructor
    · intro hz
      exact ⟨(hQY z).mp (List.mem_cons_of_mem _ hz), fun h => hut (h ▸ hz)⟩
    · rintro ⟨hzY, hzu⟩
      rcases List.mem_cons.mp ((hQY z).mpr hzY) with h | h
      · exact absurd h hzu
      · exact h
  have := InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (G := Gᶜ) (PathBasics.isPathList_drop hp (k := 1) hlen)
  rw [hset] at this
  exact this

/-- **6.1, setup.**  `X`, `X₁`, `X₂` are mutually disjoint subsets of `E(H)`, and both
`X ∪ X₁` and `X ∪ X₂` saturate `L(H)`. -/
theorem X_Xi_facts
    {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂) :
    completeEdges G H K φ Y ⊆ H.edgeSet ∧
    extraEdges G H K φ Y y₁ ⊆ H.edgeSet ∧
    extraEdges G H K φ Y y₂ ⊆ H.edgeSet ∧
    Disjoint (completeEdges G H K φ Y) (extraEdges G H K φ Y y₁) ∧
    Disjoint (completeEdges G H K φ Y) (extraEdges G H K φ Y y₂) ∧
    Disjoint (extraEdges G H K φ Y y₁) (extraEdges G H K φ Y y₂) ∧
    SaturatesLineGraph H (completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁) ∧
    SaturatesLineGraph H (completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂) := by
  obtain ⟨hp, hhead, hlast⟩ := hQ
  -- `y₁` and `y₂` are members of `Y`.
  have hy₁Q : y₁ ∈ Q := List.mem_of_mem_head? hhead
  have hy₂Q : y₂ ∈ Q := List.mem_of_mem_getLast? hlast
  have hy₁Y : y₁ ∈ Y := (hQY y₁).mp hy₁Q
  have hy₂Y : y₂ ∈ Y := (hQY y₂).mp hy₂Q
  -- `Q` has at least two vertices, since its two ends are distinct.
  have hlen : 1 < Q.length := by
    rcases Nat.lt_or_ge 1 Q.length with h | h
    · exact h
    · exfalso
      have h1 : Q.length = 1 := by
        rcases Nat.eq_zero_or_pos Q.length with h0 | h0
        · exact absurd (List.eq_nil_of_length_eq_zero h0) hp.1
        · omega
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
      rw [ha] at hy₁Q hy₂Q
      exact hy ((List.eq_of_mem_singleton hy₁Q).trans (List.eq_of_mem_singleton hy₂Q).symm)
  -- `Y \ {y₁}` and `Y \ {y₂}` are anticonnected.
  have hanti₁ : AnticonnectedSet G (Y \ {y₁}) := anticonnected_diff_head hp hhead hlen hQY
  have hanti₂ : AnticonnectedSet G (Y \ {y₂}) := by
    refine anticonnected_diff_head (Q := Q.reverse) (PathBasics.isPathList_reverse hp) ?_ ?_ ?_
    · rw [List.head?_reverse]; exact hlast
    · simpa using hlen
    · intro v; rw [List.mem_reverse]; exact hQY v
  -- `Y \ {yᵢ}` is a proper subset of `Y`.
  have hss₁ : Y \ {y₁} ⊂ Y := Set.diff_singleton_ssubset.mpr hy₁Y
  have hss₂ : Y \ {y₂} ⊂ Y := Set.diff_singleton_ssubset.mpr hy₂Y
  -- Monotonicity: a `Y`-complete vertex is `Z`-complete for any `Z ⊆ Y`.
  have hmono : ∀ Z : Set V, Z ⊆ Y →
      completeEdges G H K φ Y ⊆ completeEdges G H K φ Z := by
    rintro Z hZ e ⟨he, hc⟩
    exact ⟨he, fun x hx => hc x (hZ hx)⟩
  -- *"So `X ∪ Xᵢ` is the set of all `Y \ {yᵢ}`-complete vertices in `L(H)`."*
  have hunion : ∀ y : V,
      completeEdges G H K φ Y ∪ extraEdges G H K φ Y y
        = completeEdges G H K φ (Y \ {y}) := by
    intro y
    rw [extraEdges, Set.union_diff_self]
    exact Set.union_eq_self_of_subset_left (hmono (Y \ {y}) Set.diff_subset)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro e ⟨he, -⟩; exact he
  · rintro e ⟨⟨he, -⟩, -⟩; exact he
  · rintro e ⟨⟨he, -⟩, -⟩; exact he
  · exact Set.disjoint_sdiff_right
  · exact Set.disjoint_sdiff_right
  · -- An edge that is both `Y \ {y₁}`-complete and `Y \ {y₂}`-complete is `Y`-complete.
    rw [Set.disjoint_left]
    rintro e ⟨⟨he, hc₁⟩, hnot⟩ ⟨⟨he₂, hc₂⟩, -⟩
    refine hnot ⟨he, ?_⟩
    intro x hx
    by_cases hxy₁ : x = y₁
    · exact hc₂ x ⟨hx, by simp [hxy₁, hy]⟩
    · exact hc₁ x ⟨hx, by simpa using hxy₁⟩
  · rw [hunion y₁]; exact hmin _ hss₁ hanti₁
  · rw [hunion y₂]; exact hmin _ hss₂ hanti₂

end Workspace.ProofLemmas.Thm61Setup
