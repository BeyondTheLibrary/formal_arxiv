import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm61Setup

/-!
# 6.1, claim (3): every edge in `X` meets one of a meeting `X₁`/`X₂` pair

PAPER (proof of 6.1, printed p. 31), the second claim of the odd case:

> *"(3) If `Q` is odd and `h₁ ∈ X₁` meets `h₂ ∈ X₂`, then every edge in `X` meets at least one
> of `h₁, h₂`.*
>
> *For if `h₁ ∈ X₁` meets `h₂ ∈ X₂`, and `f ∈ X` meets neither of `h₁, h₂`, then `Q` can be
> completed to an odd antihole via `y₂-h₂-f-h₁-y₁`, a contradiction.  This proves (3)."*

`X = completeEdges G H K φ Y`, `X₁ = extraEdges G H K φ Y y₁` and
`X₂ = extraEdges G H K φ Y y₂` (see `Workspace.ProofLemmas.Thm61Setup`).

The antihole is `Q ++ [h₂, f, h₁]` read in `Gᶜ` (the three edges being read as vertices of
`L(H)` through `φ`):

* `h₁` is complete to `Y \ {y₁}` and non-adjacent to `y₁`, `h₂` is complete to `Y \ {y₂}` and
  non-adjacent to `y₂`, and `f` is complete to all of `Y`;
* `f` is non-adjacent in `G` to each of `h₁, h₂` exactly because it meets neither of them, while
  `h₁, h₂` are adjacent in `G` exactly because they do meet.

Since `Q` is odd it has an even number of vertices, so the antihole has an odd number of
vertices — contradicting `Berge G`.  This is the exact mirror of claim (8)
(`Workspace.ProofLemmas.Thm61Claim8`), which runs the same argument with the two-vertex tail
`[h₂, h₁]` in the even case.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup

variable {V : Type*}

/-- A three-vertex induced path. -/
private theorem isPathList_three {G : SimpleGraph V} {x y z : V}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : ¬ G.Adj x z) (hxzne : x ≠ z) :
    IsPathList G [x, y, z] := by
  have hxy' : x ≠ y := hxy.ne
  have hyz' : y ≠ z := hyz.ne
  refine ⟨by simp, by simp [hxy', hyz', hxzne], ?_⟩
  have key : ∀ i j : ℕ, i < 3 → j < 3 →
      ∀ (hi : i < [x, y, z].length) (hj : j < [x, y, z].length),
      (G.Adj ([x, y, z][i]'hi) ([x, y, z][j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi3 hj3
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
      first
        | exact iff_of_false (fun h => G.irrefl h) (by first | omega | tauto)
        | exact iff_of_true hxy (by first | omega | tauto)
        | exact iff_of_true hyz (by first | omega | tauto)
        | exact iff_of_true hxy.symm (by first | omega | tauto)
        | exact iff_of_true hyz.symm (by first | omega | tauto)
        | exact iff_of_false hxz (by first | omega | tauto)
        | exact iff_of_false (fun h => hxz h.symm) (by first | omega | tauto)
  intro i j hi hj
  exact key i j (by simpa using hi) (by simpa using hj) hi hj

/-- **6.1(3)** *"If `Q` is odd and `h₁ ∈ X₁` meets `h₂ ∈ X₂`, then every edge in `X` meets at
least one of `h₁, h₂`."* -/
theorem thm_6_1_claim3
    (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (h₁ h₂ f : Sym2 (Fin n))
    (hh₁ : h₁ ∈ extraEdges G H K φ Y y₁) (hh₂ : h₂ ∈ extraEdges G H K φ Y y₂)
    (hmeet : MeetEdges h₁ h₂)
    (hf : f ∈ completeEdges G H K φ Y) :
    MeetEdges f h₁ ∨ MeetEdges f h₂ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnm₁, hnm₂⟩ := hcon
  -- *"`f ∈ X` meets neither of `h₁, h₂`"*
  have hdisj₁ : DisjointEdges f h₁ := not_not.mp hnm₁
  have hdisj₂ : DisjointEdges f h₂ := not_not.mp hnm₂
  obtain ⟨⟨he₁, hc₁⟩, hn₁⟩ := hh₁
  obtain ⟨⟨he₂, hc₂⟩, hn₂⟩ := hh₂
  obtain ⟨hef, hcf⟩ := hf
  set z₁ : V := (↑(φ ⟨h₁, he₁⟩) : V) with hz₁def
  set z₂ : V := (↑(φ ⟨h₂, he₂⟩) : V) with hz₂def
  set zf : V := (↑(φ ⟨f, hef⟩) : V) with hzfdef
  -- `y₁` and `y₂` are members of `Y`.
  have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
  have hy₂Y : y₂ ∈ Y := (hQY y₂).mp (List.mem_of_mem_getLast? hQ.2.2)
  -- Both `y₁, y₂` are major, hence outside `K = V(L(H))`, while `z₁, z₂, zf ∈ K`.
  have hz₁K : z₁ ∈ K := (φ ⟨h₁, he₁⟩).2
  have hz₂K : z₂ ∈ K := (φ ⟨h₂, he₂⟩).2
  have hzfK : zf ∈ K := (φ ⟨f, hef⟩).2
  have hy₁K : y₁ ∉ K := (hYmajor y₁ hy₁Y).1
  have hy₂K : y₂ ∉ K := (hYmajor y₂ hy₂Y).1
  have hz₁ny₁ : z₁ ≠ y₁ := fun h => hy₁K (h ▸ hz₁K)
  have hz₂ny₂ : z₂ ≠ y₂ := fun h => hy₂K (h ▸ hz₂K)
  have hzfny₁ : zf ≠ y₁ := fun h => hy₁K (h ▸ hzfK)
  -- `h₁ ∈ X₁` is complete to `Y \ {y₁}` but not to `Y`, so it misses exactly `y₁`.
  have hadj₁₂ : G.Adj z₁ y₂ := hc₁ y₂ ⟨hy₂Y, by simpa using hy.symm⟩
  have hadj₂₁ : G.Adj z₂ y₁ := hc₂ y₁ ⟨hy₁Y, by simpa using hy⟩
  have hnadj₁ : ¬ G.Adj z₁ y₁ := by
    intro hcon'
    refine hn₁ ⟨he₁, ?_⟩
    intro x hx
    by_cases hxy : x = y₁
    · exact hxy ▸ hcon'
    · exact hc₁ x ⟨hx, by simpa using hxy⟩
  have hnadj₂ : ¬ G.Adj z₂ y₂ := by
    intro hcon'
    refine hn₂ ⟨he₂, ?_⟩
    intro x hx
    by_cases hxy : x = y₂
    · exact hxy ▸ hcon'
    · exact hc₂ x ⟨hx, by simpa using hxy⟩
  -- `f ∈ X` is complete to all of `Y`.
  have hadjf₁ : G.Adj zf y₁ := hcf y₁ hy₁Y
  have hadjf₂ : G.Adj zf y₂ := hcf y₂ hy₂Y
  -- None of `z₁, z₂, zf` lies in `Y`.
  have hz₁Y : z₁ ∉ Y := fun h => G.irrefl (hc₁ z₁ ⟨h, by simpa using hz₁ny₁⟩)
  have hz₂Y : z₂ ∉ Y := fun h => G.irrefl (hc₂ z₂ ⟨h, by simpa using hz₂ny₂⟩)
  have hzfY : zf ∉ Y := fun h => G.irrefl (hcf zf h)
  -- The three vertices are pairwise distinct.
  have hz₁z₂ : z₁ ≠ z₂ := fun h => hnadj₁ (h ▸ hadj₂₁)
  have hzfz₁ : zf ≠ z₁ := fun h => hnadj₁ (h ▸ hadjf₁)
  have hzfz₂ : zf ≠ z₂ := fun h => hnadj₂ (h ▸ hadjf₂)
  -- Two edges of `H` that do not meet are non-adjacent in `L(H)`, hence in `G`.
  have hnadjf₁ : ¬ G.Adj zf z₁ := by
    intro hcon'
    have hlg : H.lineGraph.Adj ⟨f, hef⟩ ⟨h₁, he₁⟩ := φ.map_adj_iff.mp hcon'
    obtain ⟨-, w, hw₁, hw₂⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
    exact hdisj₁ w ⟨hw₁, hw₂⟩
  have hnadjf₂ : ¬ G.Adj zf z₂ := by
    intro hcon'
    have hlg : H.lineGraph.Adj ⟨f, hef⟩ ⟨h₂, he₂⟩ := φ.map_adj_iff.mp hcon'
    obtain ⟨-, w, hw₁, hw₂⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
    exact hdisj₂ w ⟨hw₁, hw₂⟩
  -- `h₁` and `h₂` do meet, so they are adjacent in `L(H)`, hence in `G`.
  have hsub₁₂ : (⟨h₁, he₁⟩ : H.edgeSet) ≠ ⟨h₂, he₂⟩ := by
    intro h
    exact hz₁z₂ (congrArg (fun w : H.edgeSet => (↑(φ w) : V)) h)
  have hadjz : G.Adj z₂ z₁ := by
    have hw : ∃ w : Fin n, w ∈ h₁ ∧ w ∈ h₂ := by
      by_contra hw'
      push_neg at hw'
      exact hmeet (fun w hw'' => hw' w hw''.1 hw''.2)
    obtain ⟨w, hw₁, hw₂⟩ := hw
    have hlg : H.lineGraph.Adj ⟨h₁, he₁⟩ ⟨h₂, he₂⟩ :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hsub₁₂, w, hw₁, hw₂⟩
    exact (φ.map_adj_iff.mpr hlg).symm
  -- `[z₂, zf, z₁]` is an antipath.
  have hRpath : IsPathFrom Gᶜ [z₂, zf, z₁] z₂ z₁ :=
    ⟨isPathList_three
      (show Gᶜ.Adj z₂ zf from ⟨hzfz₂.symm, fun h => hnadjf₂ h.symm⟩)
      (show Gᶜ.Adj zf z₁ from ⟨hzfz₁, hnadjf₁⟩)
      (fun h => h.2 hadjz) hz₁z₂.symm, rfl, rfl⟩
  -- `Q` misses `z₁, z₂, zf`.
  have hdisjQ : ∀ x ∈ Q, x ∉ [z₂, zf, z₁] := by
    intro x hx hmem
    have hxY : x ∈ Y := (hQY x).mp hx
    rcases List.mem_cons.mp hmem with h | h
    · exact hz₂Y (h ▸ hxY)
    · rcases List.mem_cons.mp h with h' | h'
      · exact hzfY (h' ▸ hxY)
      · rcases List.mem_cons.mp h' with h'' | h''
        · exact hz₁Y (h'' ▸ hxY)
        · simp at h''
  -- The only edges between `Q` and `[z₂, zf, z₁]` in `Gᶜ` are `y₂-z₂` and `y₁-z₁`.
  have hcross : ∀ x ∈ Q, ∀ y ∈ [z₂, zf, z₁],
      (Gᶜ.Adj x y ↔ (x = y₂ ∧ y = z₂) ∨ (x = y₁ ∧ y = z₁)) := by
    intro x hx y hymem
    have hxY : x ∈ Y := (hQY x).mp hx
    have hyz : y = z₂ ∨ y = zf ∨ y = z₁ := by
      rcases List.mem_cons.mp hymem with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h' | h'
        · exact Or.inr (Or.inl h')
        · rcases List.mem_cons.mp h' with h'' | h''
          · exact Or.inr (Or.inr h'')
          · simp at h''
    rcases hyz with rfl | rfl | rfl
    · -- `y = z₂`: adjacent in `Gᶜ` exactly to `y₂`.
      by_cases hxy₂ : x = y₂
      · subst hxy₂
        exact iff_of_true ⟨fun h => hz₂ny₂ h.symm, fun h => hnadj₂ h.symm⟩ (Or.inl ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hcon' => hcon'.2 (hc₂ x ⟨hxY, by simpa using hxy₂⟩).symm) ?_
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hxy₂ h
        · exact hz₁z₂ h.symm
    · -- `y = zf`: never adjacent in `Gᶜ`, since `f` is `Y`-complete.
      refine iff_of_false (fun hcon' => hcon'.2 (hcf x hxY).symm) ?_
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact hzfz₂ h
      · exact hzfz₁ h
    · -- `y = z₁`: adjacent in `Gᶜ` exactly to `y₁`.
      by_cases hxy₁ : x = y₁
      · subst hxy₁
        exact iff_of_true ⟨fun h => hz₁ny₁ h.symm, fun h => hnadj₁ h.symm⟩ (Or.inr ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hcon' => hcon'.2 (hc₁ x ⟨hxY, by simpa using hxy₁⟩).symm) ?_
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hz₁z₂ h
        · exact hxy₁ h
  -- `Q` has at least two vertices, since its ends are distinct.
  have hQlen : 2 ≤ Q.length := by
    by_contra hcon'
    push_neg at hcon'
    have h1 : Q.length = 1 := by
      rcases Nat.eq_zero_or_pos Q.length with h0 | h0
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hQ.1.1
      · omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    have hy₁Q : y₁ ∈ Q := List.mem_of_mem_head? hQ.2.1
    have hy₂Q : y₂ ∈ Q := List.mem_of_mem_getLast? hQ.2.2
    rw [ha] at hy₁Q hy₂Q
    exact hy ((List.eq_of_mem_singleton hy₁Q).trans (List.eq_of_mem_singleton hy₂Q).symm)
  have hhole : IsHoleList Gᶜ (Q ++ [z₂, zf, z₁]) :=
    PathGlue.glue_hole hQ hRpath hdisjQ hcross (by simp; omega)
  have heven := hG.2 _ hhole
  simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at heven
  rw [Nat.even_iff] at heven
  rw [pathLength, Nat.odd_iff] at hQodd
  omega

end Workspace.ProofLemmas.Thm61Claim3
