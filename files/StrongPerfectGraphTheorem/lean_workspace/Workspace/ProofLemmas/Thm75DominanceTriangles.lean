import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.AppearanceVertexTypeTransport
import Workspace.Statements.S07.Thm_7_4

/-!
# `Bc₁c₂`-dominance, read as a condition on triangles

Everything §7 does with dominance goes through 7.3 and 7.4, and **both of those are stated about
prisms**: their hypothesis and conclusion are *"`y` has at least two neighbours in the triangle
`{a₁, a₂, a₃}`"*.  `Thm75Setup.IsDominantFor`, on the other hand, is the paper's literal
*"nonadjacent to at most one vertex of `Nc`"*, i.e. `(Nc \ N(y)).Subsingleton`.

The paper moves between the two silently, in claim (1) (*"By 7.3 it follows that `X` contains at
least two members of `{a₁, a₂, r₁}`"*) and again in the rung-replacement paragraph (*"since `y`
has two neighbours in both triangles of the first prism, it also has two neighbours in the
triangles of the second"*, from which it concludes *"`y` is `Bc₁c₂`-dominant with respect to
`L(H′)`"*).

The two are equivalent exactly when `|Nc| ≥ 3`, which holds because `c₁` and `c₂` are
branch-vertices.  This module proves the equivalence and the cardinality bound.

Everything here is proved; nothing is `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Thm75DominanceTriangles

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup

variable {V : Type*}

/-- **"At most one non-neighbour in `N`" is "at least two neighbours in every triangle of `N`".**

`≥` needs `|N| ≥ 3`; `≤` does not. -/
theorem subsingleton_diff_iff_triangles {G : SimpleGraph V} {N : Set V} {y : V}
    (h3 : 3 ≤ N.ncard) :
    (N \ G.neighborSet y).Subsingleton ↔
      ∀ x ∈ N, ∀ z ∈ N, ∀ w ∈ N, x ≠ z → x ≠ w → z ≠ w →
        2 ≤ (({x, z, w} : Set V) ∩ G.neighborSet y).ncard := by
  constructor
  · intro h x hx z hz w hw hxz hxw hzw
    have key : ∀ u v : V, u ∈ N → v ∈ N → u ≠ v → ¬ G.Adj y u → ¬ G.Adj y v → False := by
      intro u v hu hv huv hnu hnv
      exact huv (h ⟨hu, hnu⟩ ⟨hv, hnv⟩)
    show 1 < _
    refine (Set.one_lt_ncard (Set.toFinite _)).mpr ?_
    by_cases hax : G.Adj y x
    · by_cases haz : G.Adj y z
      · exact ⟨x, ⟨by simp, hax⟩, z, ⟨by simp, haz⟩, hxz⟩
      · by_cases haw : G.Adj y w
        · exact ⟨x, ⟨by simp, hax⟩, w, ⟨by simp, haw⟩, hxw⟩
        · exact (key z w hz hw hzw haz haw).elim
    · by_cases haz : G.Adj y z
      · by_cases haw : G.Adj y w
        · exact ⟨z, ⟨by simp, haz⟩, w, ⟨by simp, haw⟩, hzw⟩
        · exact (key x w hx hw hxw hax haw).elim
      · exact (key x z hx hz hxz hax haz).elim
  · intro htri u hu v hv
    by_contra huv
    obtain ⟨w, hwN, hw⟩ : (N \ ({u, v} : Set V)).Nonempty := by
      rw [Set.diff_nonempty]
      intro hcon
      have hle := Set.ncard_le_ncard hcon (Set.toFinite _)
      rw [Set.ncard_pair huv] at hle
      omega
    have hwu : u ≠ w := by
      intro hcon
      exact hw (by rw [← hcon]; exact Or.inl rfl)
    have hwv : v ≠ w := by
      intro hcon
      exact hw (by rw [← hcon]; exact Or.inr rfl)
    have h2 := htri u hu.1 v hv.1 w hwN huv hwu hwv
    have hsub : ({u, v, w} : Set V) ∩ G.neighborSet y ⊆ {w} := by
      rintro t ⟨ht, htn⟩
      rcases ht with rfl | rfl | rfl
      · exact absurd htn hu.2
      · exact absurd htn hv.2
      · rfl
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    omega

/-- The clique `N_c` of a branch-vertex `c` has at least three vertices. -/
theorem three_le_nset_ncard [Finite V] {W : Type*} [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W)
    (K : Set V) (φ : H.lineGraph ≃g G.induce K) (c : W) (hc : c ∈ branchVertices H) :
    3 ≤ (NSet G H K φ c).ncard := by
  classical
  have hcard : 3 ≤ (H.neighborSet c).ncard := hc
  obtain ⟨w₁, hw₁⟩ : (H.neighborSet c).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hd1 : (H.neighborSet c \ {w₁}).ncard = (H.neighborSet c).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hw₁
  obtain ⟨w₂, hw₂⟩ : (H.neighborSet c \ {w₁}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hd2 : ((H.neighborSet c \ {w₁}) \ {w₂}).ncard = (H.neighborSet c \ {w₁}).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hw₂
  obtain ⟨w₃, hw₃⟩ : ((H.neighborSet c \ {w₁}) \ {w₂}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have he₁ : s(c, w₁) ∈ H.edgeSet := hw₁
  have he₂ : s(c, w₂) ∈ H.edgeSet := hw₂.1
  have he₃ : s(c, w₃) ∈ H.edgeSet := hw₃.1.1
  have hn12 : w₁ ≠ w₂ := fun h => hw₂.2 (by rw [← h]; rfl)
  have hn13 : w₁ ≠ w₃ := fun h => hw₃.1.2 (by rw [← h]; rfl)
  have hn23 : w₂ ≠ w₃ := fun h => hw₃.2 (by rw [← h]; rfl)
  set x₁ : V := (↑(φ ⟨s(c, w₁), he₁⟩) : V) with hx₁
  set x₂ : V := (↑(φ ⟨s(c, w₂), he₂⟩) : V) with hx₂
  set x₃ : V := (↑(φ ⟨s(c, w₃), he₃⟩) : V) with hx₃
  have hne : ∀ (u v : W) (hu : s(c, u) ∈ H.edgeSet) (hv : s(c, v) ∈ H.edgeSet), u ≠ v →
      (↑(φ ⟨s(c, u), hu⟩) : V) ≠ (↑(φ ⟨s(c, v), hv⟩) : V) := by
    intro u v hu hv huv hcon
    exact huv (Sym2.congr_right.mp
      (Thm75Claim2Transport.phi_inj φ hu hv hcon))
  have hsub : ({x₁, x₂, x₃} : Set V) ⊆ NSet G H K φ c := by
    rintro t (rfl | rfl | rfl)
    · exact ⟨_, he₁, ⟨he₁, by simp⟩, rfl⟩
    · exact ⟨_, he₂, ⟨he₂, by simp⟩, rfl⟩
    · exact ⟨_, he₃, ⟨he₃, by simp⟩, rfl⟩
  have h3card : ({x₁, x₂, x₃} : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨x₁, x₂, x₃, hne _ _ he₁ he₂ hn12, hne _ _ he₁ he₃ hn13,
      hne _ _ he₂ he₃ hn23, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- The form in which §7 actually uses the equivalence: `IsDominantFor` in terms of triangles. -/
theorem isDominantFor_iff_triangles [Finite V] {W : Type*} [Finite W] {G : SimpleGraph V}
    {H : SimpleGraph W} {K : Set V} (φ : H.lineGraph ≃g G.induce K) {c₁ c₂ : W}
    (hc₁ : c₁ ∈ branchVertices H) (hc₂ : c₂ ∈ branchVertices H) (y : V) :
    IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y ↔
      ((∀ x ∈ NSet G H K φ c₁, ∀ z ∈ NSet G H K φ c₁, ∀ w ∈ NSet G H K φ c₁,
          x ≠ z → x ≠ w → z ≠ w → 2 ≤ (({x, z, w} : Set V) ∩ G.neighborSet y).ncard) ∧
       (∀ x ∈ NSet G H K φ c₂, ∀ z ∈ NSet G H K φ c₂, ∀ w ∈ NSet G H K φ c₂,
          x ≠ z → x ≠ w → z ≠ w → 2 ≤ (({x, z, w} : Set V) ∩ G.neighborSet y).ncard)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(subsingleton_diff_iff_triangles (three_le_nset_ncard G H K φ c₁ hc₁)).mp h1,
      (subsingleton_diff_iff_triangles (three_le_nset_ncard G H K φ c₂ hc₂)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(subsingleton_diff_iff_triangles (three_le_nset_ncard G H K φ c₁ hc₁)).mpr h1,
      (subsingleton_diff_iff_triangles (three_le_nset_ncard G H K φ c₂ hc₂)).mpr h2⟩

/-!
# Dominance survives the rung replacement of the proof of 7.5

PAPER (proof of 7.5, printed p. 37):

*"Now suppose that `b₁b₂` and `c₁c₂` are different edges of `J`.  Then `Bc₁c₂` is still a branch
of `H′`, and we claim that every `y ∈ Y` is `Bc₁c₂`-dominant with respect to `L(H′)`.  For let
`e, f` be two edges of `J` incident with `c₁` and different from `c₁c₂`.  By 7.1 there are three
tracks of `J` from `c₁` to `c₂`, vertex-disjoint except for their ends, and one of them is the
edge `c₁c₂`, and the first edges of the other two are `e` and `f`.  There are three tracks
corresponding to these in `H`, and their line graph is a prism in `L(H)`.  There also correspond
three tracks in `H′`, yielding a prism in `L(H′)`.  Since `Rb₁b₂ ≠ Rc₁c₂`, it follows that
`Rb₁b₂` is incident with at most one of `c₁, c₂`, so these two prisms are related as in 7.4.
Hence by 7.4, since `y` has two neighbours in both triangles of the first prism, it also has two
neighbours in the triangles of the second.  This proves that `y` is `Bc₁c₂`-dominant with respect
to `L(H′)`."*

Because *"`Rb₁b₂` is incident with at most one of `c₁, c₂`"*, exactly one of the two cliques
changes, and it changes by **swapping a single vertex**: `N′ = (N \ {t}) ∪ {t'}`, where `t` is
the vertex of `N` carried by the replaced rung and `t'` is the corresponding end of the new
rung.  (If `Rb₁b₂` is incident with neither, both cliques are unchanged and there is nothing to
prove.)

So the whole content of the paragraph, once 7.1 and the track-to-prism dictionary have supplied
the two prisms, is the statement below: **a single-vertex swap in one of the two cliques
preserves dominance.**  It is proved from 7.4 exactly as the paper says, through the
triangle reading of dominance (`Thm75DominanceTriangles`).

The hypothesis `hprism` is where the caller discharges *"By 7.1 there are three tracks … their
line graph is a prism in `L(H)` … There also correspond three tracks in `H′`, yielding a prism in
`L(H′)`"*.

Everything here is proved; nothing is `sorry`.
-/

section DominanceSwap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **A single-vertex swap in one clique preserves dominance**, given the two prisms that 7.1
supplies.  This is the printed paragraph of p. 37, with the prisms as a hypothesis. -/
theorem dominance_after_single_swap (G : SimpleGraph V) (hG : Berge G) (N₁ N₂ : Set V)
    (t t' : V) (ht : t ∈ N₁) (h3 : 3 ≤ (N₁ \ {t}).ncard) (h3N₂ : 3 ≤ N₂.ncard)
    (hprism : ∀ x ∈ N₁ \ {t}, ∀ z ∈ N₁ \ {t}, x ≠ z →
      ∃ (b : Fin 3 → V) (P₁ P₂ P₃ P₁' : List V),
        b 0 ∈ N₂ ∧ b 1 ∈ N₂ ∧ b 2 ∈ N₂ ∧ b 0 ≠ b 1 ∧ b 0 ≠ b 2 ∧ b 1 ≠ b 2 ∧
        FormPrism G ![t, x, z] b P₁ P₂ P₃ ∧
        Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength P₃) ∧
        2 ≤ pathLength P₁ ∧ 2 ≤ pathLength P₂ ∧ 2 ≤ pathLength P₃ ∧
        IsPathFrom G P₁' t' (b 0) ∧ FormPrism G ![t', x, z] b P₁' P₂ P₃)
    (y : V) (hy : IsDominantFor G N₁ N₂ y) :
    ((((N₁ \ {t}) ∪ {t'}) \ G.neighborSet y).Subsingleton) := by
  classical
  have hsub1 : N₁ \ {t} ⊆ N₁ := Set.diff_subset
  have h3N₁ : 3 ≤ N₁.ncard := le_trans h3 (Set.ncard_le_ncard hsub1 (Set.toFinite _))
  have htri₁ := (subsingleton_diff_iff_triangles (G := G) (N := N₁) (y := y) h3N₁).mp hy.1
  have htri₂ := (subsingleton_diff_iff_triangles (G := G) (N := N₂) (y := y) h3N₂).mp hy.2
  -- the new triangles, i.e. those through `t'`
  have key : ∀ x ∈ N₁ \ {t}, ∀ z ∈ N₁ \ {t}, x ≠ z →
      2 ≤ (({t', x, z} : Set V) ∩ G.neighborSet y).ncard := by
    intro x hx z hz hxz
    obtain ⟨b, P₁, P₂, P₃, P₁', hb0, hb1, hb2, hb01, hb02, hb12, hpr, he1, he2, he3,
      hl1, hl2, hl3, hP₁', hpr'⟩ := hprism x hx z hz hxz
    have hmaj : MajorForPrism G ![t, x, z] b y := by
      constructor
      · have := htri₁ t ht x hx.1 z hz.1 (fun hcon => hx.2 (by rw [← hcon]; rfl))
          (fun hcon => hz.2 (by rw [← hcon]; rfl)) hxz
        simpa using this
      · have := htri₂ (b 0) hb0 (b 1) hb1 (b 2) hb2 hb01 hb02 hb12
        simpa using this
    have h74 := Workspace.Statements.S07.SPGT.thm_7_4 G hG ![t, x, z] b P₁ P₂ P₃ hpr
      he1 he2 he3 hl1 hl2 hl3 t' P₁' hP₁' (by simpa using hpr') y hmaj
    simpa using h74
  -- assemble via the triangle reading of dominance
  have h3' : 3 ≤ ((N₁ \ {t}) ∪ {t'}).ncard :=
    le_trans h3 (Set.ncard_le_ncard Set.subset_union_left (Set.toFinite _))
  refine (subsingleton_diff_iff_triangles (G := G) (N := (N₁ \ {t}) ∪ {t'}) (y := y) h3').mpr ?_
  intro x hx z hz w hw hxz hxw hzw
  by_cases hxt : x = t'
  · subst hxt
    have hz' : z ∈ N₁ \ {t} := hz.resolve_right (fun h => hxz (by simp at h; rw [h]))
    have hw' : w ∈ N₁ \ {t} := hw.resolve_right (fun h => hxw (by simp at h; rw [h]))
    exact key z hz' w hw' hzw
  · by_cases hzt : z = t'
    · subst hzt
      have hx' : x ∈ N₁ \ {t} := hx.resolve_right (fun h => hxt (by simpa using h))
      have hw' : w ∈ N₁ \ {t} := hw.resolve_right (fun h => hzw (by simp at h; rw [h]))
      have hset : ({x, z, w} : Set V) = {z, x, w} := Set.insert_comm x z {w}
      rw [hset]
      exact key x hx' w hw' hxw
    · by_cases hwt : w = t'
      · subst hwt
        have hx' : x ∈ N₁ \ {t} := hx.resolve_right (fun h => hxt (by simpa using h))
        have hz' : z ∈ N₁ \ {t} := hz.resolve_right (fun h => hzt (by simpa using h))
        have hset : ({x, z, w} : Set V) = {w, x, z} := by
          ext u; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset]
        exact key x hx' z hz' hxz
      · -- no `t'` in the triangle: it is an old triangle of `N₁`
        have hx' : x ∈ N₁ := (hx.resolve_right (fun h => hxt (by simpa using h))).1
        have hz' : z ∈ N₁ := (hz.resolve_right (fun h => hzt (by simpa using h))).1
        have hw' : w ∈ N₁ := (hw.resolve_right (fun h => hwt (by simpa using h))).1
        exact htri₁ x hx' z hz' w hw' hxz hxw hzw

end DominanceSwap

end Thm75DominanceTriangles
