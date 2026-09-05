import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm61Setup

/-!
# 6.1, claim (2): no `X₁`-`X₂`-`X`-`X` four-cycle through a branch-vertex

PAPER (proof of 6.1, printed p. 31), the first claim of the odd case:

> *"(2) If `Q` is odd then there is no cycle of `H` with edge-set `{h₁, h₂, h₃, h₄}` in order,
> such that the common end of `h₁` and `h₂` is a branch-vertex, `h₁ ∈ X₁`, `h₂ ∈ X₂`, and
> `h₃, h₄ ∈ X`.*
>
> *For if there is such a cycle, then `Q` can be completed to an odd antihole via
> `y₂-h₂-h₄-f-h₃-h₁-y₁` (where `f` is a third edge of `H` such that `h₁, h₂, f` have a common
> end), a contradiction.  This proves (2)."*

The cycle is given by its four vertices `u, v, w, x` in order, so that
`h₁ = uv`, `h₂ = vw`, `h₃ = wx`, `h₄ = xu`, and the common end of `h₁, h₂` is `v`.

Two things the printed sentence leaves implicit and which are supplied here:

* **`f` exists and is disjoint from `h₃` and `h₄`.**  `v` is a branch-vertex, so it has a third
  neighbour `t ∉ {u, w}`; and `t ≠ x` because `H` is bipartite (`u` has the colour opposite to
  `v`, and `x` — being adjacent to `u` — has the same colour as `v`).
* **`f ∈ X`.**  Both `X ∪ X₁` and `X ∪ X₂` saturate `L(H)` (`Thm61Setup.X_Xi_facts`).  At the
  branch-vertex `v`, the edge `h₂ ∈ X₂` lies outside `X ∪ X₁`, so every *other* edge at `v` —
  in particular `f` — lies in `X ∪ X₁`; symmetrically `h₁ ∈ X₁` forces `f ∈ X ∪ X₂`.  As `X₁`
  and `X₂` are disjoint, `f ∈ X`.

The antihole is then `Q ++ [h₂, h₄, f, h₃, h₁]` read in `Gᶜ`; since `Q` is odd it has an even
number of vertices, so the antihole has an odd number of vertices, contradicting `Berge G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm61Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup

variable {V : Type*}

/-- A five-element list with the four consecutive edges present and the six non-consecutive
pairs absent is a path. -/
private theorem isPathList_five {G : SimpleGraph V} {a b c d e : V}
    (hnd : [a, b, c, d, e].Nodup)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d e)
    (n1 : ¬ G.Adj a c) (n2 : ¬ G.Adj a d) (n3 : ¬ G.Adj a e)
    (n4 : ¬ G.Adj b d) (n5 : ¬ G.Adj b e) (n6 : ¬ G.Adj c e) :
    IsPathList G [a, b, c, d, e] := by
  have key : ∀ i j : ℕ, i < 5 → j < 5 →
      ∀ (hi : i < [a, b, c, d, e].length) (hj : j < [a, b, c, d, e].length),
        (G.Adj ([a, b, c, d, e][i]'hi) ([a, b, c, d, e][j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi5 hj5
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true h1 (by first | omega | simp | tauto)
      | exact iff_of_true h2 (by first | omega | simp | tauto)
      | exact iff_of_true h3 (by first | omega | simp | tauto)
      | exact iff_of_true h4 (by first | omega | simp | tauto)
      | exact iff_of_true h1.symm (by first | omega | simp | tauto)
      | exact iff_of_true h2.symm (by first | omega | simp | tauto)
      | exact iff_of_true h3.symm (by first | omega | simp | tauto)
      | exact iff_of_true h4.symm (by first | omega | simp | tauto)
      | exact iff_of_false n1 (by first | omega | simp | tauto)
      | exact iff_of_false n2 (by first | omega | simp | tauto)
      | exact iff_of_false n3 (by first | omega | simp | tauto)
      | exact iff_of_false n4 (by first | omega | simp | tauto)
      | exact iff_of_false n5 (by first | omega | simp | tauto)
      | exact iff_of_false n6 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n2 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n3 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n4 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n5 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n6 h.symm) (by first | omega | simp | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩

/-- Nodupness of a five-element list from the ten pairwise inequalities. -/
private theorem nodup_five {a b c d e : V} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : a ≠ e)
    (h5 : b ≠ c) (h6 : b ≠ d) (h7 : b ≠ e) (h8 : c ≠ d) (h9 : c ≠ e) (h10 : d ≠ e) :
    [a, b, c, d, e].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
    not_or, ne_eq, and_true]
  tauto

/-- **6.1(2)** *"If `Q` is odd then there is no cycle of `H` with edge-set `{h₁, h₂, h₃, h₄}` in
order, such that the common end of `h₁` and `h₂` is a branch-vertex, `h₁ ∈ X₁`, `h₂ ∈ X₂`, and
`h₃, h₄ ∈ X`."* -/
theorem thm_6_1_claim2
    (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} (H : SimpleGraph (Fin n)) (hHbip : H.IsBipartite)
    (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (u v w x : Fin n) (hnd : [u, v, w, x].Nodup)
    (ha₁ : H.Adj u v) (ha₂ : H.Adj v w) (ha₃ : H.Adj w x) (ha₄ : H.Adj x u)
    (hbv : v ∈ branchVertices H)
    (hX₁ : s(u, v) ∈ extraEdges G H K φ Y y₁)
    (hX₂ : s(v, w) ∈ extraEdges G H K φ Y y₂)
    (hX₃ : s(w, x) ∈ completeEdges G H K φ Y)
    (hX₄ : s(x, u) ∈ completeEdges G H K φ Y) :
    False := by
  obtain ⟨-, -, -, hd₁, hd₂, hd₁₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  -- The four cycle vertices are pairwise distinct.
  have huv : u ≠ v := ha₁.ne
  have hvw : v ≠ w := ha₂.ne
  have hwx : w ≠ x := ha₃.ne
  have hxu : x ≠ u := ha₄.ne
  have huw : u ≠ w := by simp at hnd; tauto
  have hvx : v ≠ x := by simp at hnd; tauto
  -- *"`f` is a third edge of `H` such that `h₁, h₂, f` have a common end"*.
  have hdeg : 3 ≤ (H.neighborSet v).ncard := hbv
  have hext : ∃ t : Fin n, H.Adj v t ∧ t ≠ u ∧ t ≠ w := by
    by_contra hcon
    push_neg at hcon
    have hsub : H.neighborSet v ⊆ ({u, w} : Set (Fin n)) := by
      intro z hz
      rcases eq_or_ne z u with rfl | hzu
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (by simpa using hcon z hz hzu)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({u, w} : Set (Fin n)).ncard ≤ 2 := by
      simpa using Set.ncard_insert_le u ({w} : Set (Fin n))
    omega
  obtain ⟨t, hvt, htu, htw⟩ := hext
  -- *"since `H` is bipartite"*: `v` and `x` have the same colour, so `t ≠ x`.
  have htx : t ≠ x := by
    obtain ⟨col⟩ := hHbip
    intro hcon
    have c1 : col u ≠ col v := col.valid ha₁
    have c4 : col x ≠ col u := col.valid ha₄
    have c5 : col v ≠ col t := col.valid hvt
    have e1 : (col u).val ≠ (col v).val := fun h => c1 (Fin.ext h)
    have e4 : (col x).val ≠ (col u).val := fun h => c4 (Fin.ext h)
    have e5 : (col v).val ≠ (col t).val := fun h => c5 (Fin.ext h)
    have e6 : (col t).val = (col x).val := by rw [hcon]
    have b1 := (col u).isLt
    have b2 := (col v).isLt
    have b3 := (col t).isLt
    have b4 := (col x).isLt
    omega
  -- The five edges of `H` involved.
  have he₁ : s(u, v) ∈ H.edgeSet := H.mem_edgeSet.mpr ha₁
  have he₂ : s(v, w) ∈ H.edgeSet := H.mem_edgeSet.mpr ha₂
  have he₃ : s(w, x) ∈ H.edgeSet := H.mem_edgeSet.mpr ha₃
  have he₄ : s(x, u) ∈ H.edgeSet := H.mem_edgeSet.mpr ha₄
  have heF : s(v, t) ∈ H.edgeSet := H.mem_edgeSet.mpr hvt
  -- Pairwise distinctness of the five edges.
  have hFne₂ : s(v, t) ≠ s(v, w) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hFne₁ : s(v, t) ≠ s(u, v) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hFne₃ : s(v, t) ≠ s(w, x) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hFne₄ : s(v, t) ≠ s(x, u) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hne₂₄ : s(v, w) ≠ s(x, u) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hne₂₃ : s(v, w) ≠ s(w, x) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hne₂₁ : s(v, w) ≠ s(u, v) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hne₄₃ : s(x, u) ≠ s(w, x) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hne₄₁ : s(x, u) ≠ s(u, v) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  have hne₃₁ : s(w, x) ≠ s(u, v) := by
    intro h; rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst_vars <;> simp_all
  -- *"`f ∈ X`"*: `f` is the third edge at the branch-vertex `v`.
  have hincF : s(v, t) ∈ incidentEdges H v := ⟨heF, by simp⟩
  have hinc₁ : s(u, v) ∈ incidentEdges H v := ⟨he₁, by simp⟩
  have hinc₂ : s(v, w) ∈ incidentEdges H v := ⟨he₂, by simp⟩
  have h₂notX : s(v, w) ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hd₂ hX₂
  have h₂notX₁ : s(v, w) ∉ extraEdges G H K φ Y y₁ := fun h =>
    (Set.disjoint_left.mp hd₁₂ h) hX₂
  have h₁notX : s(u, v) ∉ completeEdges G H K φ Y := Set.disjoint_right.mp hd₁ hX₁
  have h₁notX₂ : s(u, v) ∉ extraEdges G H K φ Y y₂ := Set.disjoint_left.mp hd₁₂ hX₁
  have hFX₁ : s(v, t) ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    by_contra hcon
    refine hFne₂ (hsat₁ v hbv ⟨hincF, hcon⟩ ⟨hinc₂, ?_⟩)
    simp only [Set.mem_union, not_or]
    exact ⟨h₂notX, h₂notX₁⟩
  have hFX₂ : s(v, t) ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂ := by
    by_contra hcon
    refine hFne₁ (hsat₂ v hbv ⟨hincF, hcon⟩ ⟨hinc₁, ?_⟩)
    simp only [Set.mem_union, not_or]
    exact ⟨h₁notX, h₁notX₂⟩
  have hFX : s(v, t) ∈ completeEdges G H K φ Y := by
    rcases hFX₁ with h | h
    · exact h
    · rcases hFX₂ with h' | h'
      · exact h'
      · exact absurd h' (Set.disjoint_left.mp hd₁₂ h)
  -- Read the five edges through `φ`.
  obtain ⟨⟨he₁', hc₁⟩, hn₁⟩ := hX₁
  obtain ⟨⟨he₂', hc₂⟩, hn₂⟩ := hX₂
  obtain ⟨he₃', hc₃⟩ := hX₃
  obtain ⟨he₄', hc₄⟩ := hX₄
  obtain ⟨heF', hcF⟩ := hFX
  set z₁ : V := (↑(φ ⟨s(u, v), he₁'⟩) : V) with hz₁def
  set z₂ : V := (↑(φ ⟨s(v, w), he₂'⟩) : V) with hz₂def
  set z₃ : V := (↑(φ ⟨s(w, x), he₃'⟩) : V) with hz₃def
  set z₄ : V := (↑(φ ⟨s(x, u), he₄'⟩) : V) with hz₄def
  set zf : V := (↑(φ ⟨s(v, t), heF'⟩) : V) with hzfdef
  -- Adjacency of two `φ`-images is exactly "the two edges are distinct and meet".
  have hφne : ∀ (e e' : Sym2 (Fin n)) (he : e ∈ H.edgeSet) (he' : e' ∈ H.edgeSet),
      e ≠ e' → (↑(φ ⟨e, he⟩) : V) ≠ (↑(φ ⟨e', he'⟩) : V) :=
    fun e e' he he' hne h => hne (congrArg Subtype.val (φ.toEquiv.injective (Subtype.ext h)))
  -- `y₁, y₂ ∈ Y`, and they lie outside `K`.
  have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
  have hy₂Y : y₂ ∈ Y := (hQY y₂).mp (List.mem_of_mem_getLast? hQ.2.2)
  have hy₁K : y₁ ∉ K := (hYmajor y₁ hy₁Y).1
  have hy₂K : y₂ ∉ K := (hYmajor y₂ hy₂Y).1
  have hz₁ny₁ : z₁ ≠ y₁ := fun h => hy₁K (h ▸ (φ ⟨s(u, v), he₁'⟩).2)
  have hz₂ny₂ : z₂ ≠ y₂ := fun h => hy₂K (h ▸ (φ ⟨s(v, w), he₂'⟩).2)
  -- `h₁` misses exactly `y₁`; `h₂` misses exactly `y₂`.
  have hnadj₁ : ¬ G.Adj z₁ y₁ := by
    intro hcon
    refine hn₁ ⟨he₁', ?_⟩
    intro z hz
    by_cases hzy : z = y₁
    · exact hzy ▸ hcon
    · exact hc₁ z ⟨hz, by simpa using hzy⟩
  have hnadj₂ : ¬ G.Adj z₂ y₂ := by
    intro hcon
    refine hn₂ ⟨he₂', ?_⟩
    intro z hz
    by_cases hzy : z = y₂
    · exact hzy ▸ hcon
    · exact hc₂ z ⟨hz, by simpa using hzy⟩
  -- None of the five lies in `Y`.
  have hz₁Y : z₁ ∉ Y := fun h => G.irrefl (hc₁ z₁ ⟨h, by simpa using hz₁ny₁⟩)
  have hz₂Y : z₂ ∉ Y := fun h => G.irrefl (hc₂ z₂ ⟨h, by simpa using hz₂ny₂⟩)
  have hz₃Y : z₃ ∉ Y := fun h => G.irrefl (hc₃ z₃ h)
  have hz₄Y : z₄ ∉ Y := fun h => G.irrefl (hc₄ z₄ h)
  have hzfY : zf ∉ Y := fun h => G.irrefl (hcF zf h)
  -- The five vertices are pairwise distinct.
  have d24 : z₂ ≠ z₄ := hφne _ _ he₂' he₄' hne₂₄
  have d2f : z₂ ≠ zf := hφne _ _ he₂' heF' (fun h => hFne₂ h.symm)
  have d23 : z₂ ≠ z₃ := hφne _ _ he₂' he₃' hne₂₃
  have d21 : z₂ ≠ z₁ := hφne _ _ he₂' he₁' hne₂₁
  have d4f : z₄ ≠ zf := hφne _ _ he₄' heF' (fun h => hFne₄ h.symm)
  have d43 : z₄ ≠ z₃ := hφne _ _ he₄' he₃' hne₄₃
  have d41 : z₄ ≠ z₁ := hφne _ _ he₄' he₁' hne₄₁
  have df3 : zf ≠ z₃ := hφne _ _ heF' he₃' hFne₃
  have df1 : zf ≠ z₁ := hφne _ _ heF' he₁' hFne₁
  have d31 : z₃ ≠ z₁ := hφne _ _ he₃' he₁' hne₃₁
  -- The four non-meeting pairs: the edges of the antipath in `Gᶜ`.
  have hdis₂₄ : ¬ G.Adj z₂ z₄ := by
    intro hcon
    have hlg : H.lineGraph.Adj ⟨s(v, w), he₂'⟩ ⟨s(x, u), he₄'⟩ := φ.map_adj_iff.mp hcon
    obtain ⟨-, z, hz, hz'⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
    have ha : z ∈ s(v, w) := hz
    have hb : z ∈ s(x, u) := hz'
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;> subst_vars <;> simp_all
  have hdis₄f : ¬ G.Adj z₄ zf := by
    intro hcon
    have hlg : H.lineGraph.Adj ⟨s(x, u), he₄'⟩ ⟨s(v, t), heF'⟩ := φ.map_adj_iff.mp hcon
    obtain ⟨-, z, hz, hz'⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
    have ha : z ∈ s(x, u) := hz
    have hb : z ∈ s(v, t) := hz'
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;> subst_vars <;> simp_all
  have hdisf₃ : ¬ G.Adj zf z₃ := by
    intro hcon
    have hlg : H.lineGraph.Adj ⟨s(v, t), heF'⟩ ⟨s(w, x), he₃'⟩ := φ.map_adj_iff.mp hcon
    obtain ⟨-, z, hz, hz'⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
    have ha : z ∈ s(v, t) := hz
    have hb : z ∈ s(w, x) := hz'
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;> subst_vars <;> simp_all
  have hdis₃₁ : ¬ G.Adj z₃ z₁ := by
    intro hcon
    have hlg : H.lineGraph.Adj ⟨s(w, x), he₃'⟩ ⟨s(u, v), he₁'⟩ := φ.map_adj_iff.mp hcon
    obtain ⟨-, z, hz, hz'⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
    have ha : z ∈ s(w, x) := hz
    have hb : z ∈ s(u, v) := hz'
    simp only [Sym2.mem_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with h | h <;> subst_vars <;> simp_all
  -- The six meeting pairs: the non-edges of the antipath.
  have hadj₂f : G.Adj z₂ zf :=
    φ.map_adj_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨fun h => hFne₂ (congrArg Subtype.val h).symm, v,
        Sym2.mem_mk_left v w, Sym2.mem_mk_left v t⟩)
  have hadj₂₃ : G.Adj z₂ z₃ :=
    φ.map_adj_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨fun h => hne₂₃ (congrArg Subtype.val h), w,
        Sym2.mem_mk_right v w, Sym2.mem_mk_left w x⟩)
  have hadj₂₁ : G.Adj z₂ z₁ :=
    φ.map_adj_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨fun h => hne₂₁ (congrArg Subtype.val h), v,
        Sym2.mem_mk_left v w, Sym2.mem_mk_right u v⟩)
  have hadj₄₃ : G.Adj z₄ z₃ :=
    φ.map_adj_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨fun h => hne₄₃ (congrArg Subtype.val h), x,
        Sym2.mem_mk_left x u, Sym2.mem_mk_right w x⟩)
  have hadj₄₁ : G.Adj z₄ z₁ :=
    φ.map_adj_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨fun h => hne₄₁ (congrArg Subtype.val h), u,
        Sym2.mem_mk_right x u, Sym2.mem_mk_left u v⟩)
  have hadjf₁ : G.Adj zf z₁ :=
    φ.map_adj_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr
      ⟨fun h => hFne₁ (congrArg Subtype.val h), v,
        Sym2.mem_mk_left v t, Sym2.mem_mk_right u v⟩)
  -- `[z₂, z₄, zf, z₃, z₁]` is an antipath from `z₂` to `z₁`.
  have hnd5 : [z₂, z₄, zf, z₃, z₁].Nodup :=
    nodup_five d24 d2f d23 d21 d4f d43 d41 df3 df1 d31
  have hRpath : IsPathFrom Gᶜ [z₂, z₄, zf, z₃, z₁] z₂ z₁ :=
    ⟨isPathList_five hnd5 ⟨d24, hdis₂₄⟩ ⟨d4f, hdis₄f⟩ ⟨df3, hdisf₃⟩ ⟨d31, hdis₃₁⟩
      (fun h => h.2 hadj₂f) (fun h => h.2 hadj₂₃) (fun h => h.2 hadj₂₁)
      (fun h => h.2 hadj₄₃) (fun h => h.2 hadj₄₁) (fun h => h.2 hadjf₁),
     rfl, rfl⟩
  -- `Q` misses all five.
  have hdisjQ : ∀ q ∈ Q, q ∉ [z₂, z₄, zf, z₃, z₁] := by
    intro q hq hmem
    have hqY : q ∈ Y := (hQY q).mp hq
    have h5 : q = z₂ ∨ q = z₄ ∨ q = zf ∨ q = z₃ ∨ q = z₁ := by simpa using hmem
    rcases h5 with rfl | rfl | rfl | rfl | rfl
    · exact hz₂Y hqY
    · exact hz₄Y hqY
    · exact hzfY hqY
    · exact hz₃Y hqY
    · exact hz₁Y hqY
  -- The only `Gᶜ`-edges between `Q` and the antipath are `y₂-z₂` and `y₁-z₁`.
  have hcross : ∀ q ∈ Q, ∀ y ∈ [z₂, z₄, zf, z₃, z₁],
      (Gᶜ.Adj q y ↔ (q = y₂ ∧ y = z₂) ∨ (q = y₁ ∧ y = z₁)) := by
    intro q hq y hymem
    have hqY : q ∈ Y := (hQY q).mp hq
    have h5 : y = z₂ ∨ y = z₄ ∨ y = zf ∨ y = z₃ ∨ y = z₁ := by simpa using hymem
    rcases h5 with rfl | rfl | rfl | rfl | rfl
    · by_cases hqy₂ : q = y₂
      · subst hqy₂
        exact iff_of_true ⟨fun h => hz₂ny₂ h.symm, fun h => hnadj₂ h.symm⟩ (Or.inl ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hcon => hcon.2 (hc₂ q ⟨hqY, by simpa using hqy₂⟩).symm) ?_
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hqy₂ h
        · exact d21 h
    · refine iff_of_false (fun hcon => hcon.2 (hc₄ q hqY).symm) ?_
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact d24 h.symm
      · exact d41 h
    · refine iff_of_false (fun hcon => hcon.2 (hcF q hqY).symm) ?_
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact d2f h.symm
      · exact df1 h
    · refine iff_of_false (fun hcon => hcon.2 (hc₃ q hqY).symm) ?_
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact d23 h.symm
      · exact d31 h
    · by_cases hqy₁ : q = y₁
      · subst hqy₁
        exact iff_of_true ⟨fun h => hz₁ny₁ h.symm, fun h => hnadj₁ h.symm⟩ (Or.inr ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hcon => hcon.2 (hc₁ q ⟨hqY, by simpa using hqy₁⟩).symm) ?_
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact d21 h.symm
        · exact hqy₁ h
  have hQpos : 0 < Q.length := List.length_pos_of_ne_nil hQ.1.1
  have hhole : IsHoleList Gᶜ (Q ++ [z₂, z₄, zf, z₃, z₁]) :=
    PathGlue.glue_hole hQ hRpath hdisjQ hcross
      (by simp only [List.length_cons, List.length_nil]; omega)
  have heven := hG.2 _ hhole
  simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at heven
  rw [Nat.even_iff] at heven
  rw [pathLength, Nat.odd_iff] at hQodd
  omega

end Workspace.ProofLemmas.Thm61Claim2
