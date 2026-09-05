import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm61Setup

/-!
# 6.1, claim (8): every edge in `X₁` meets every edge in `X₂`

PAPER (proof of 6.1, printed p. 31), the first claim of the even case:

> *"(8) Every edge in `X₁` meets every edge in `X₂`.*
>
> *For if `h₁ ∈ X₁` does not meet some `h₂ ∈ X₂`, then `Q` can be completed to an odd antihole
> via `y₂-h₂-h₁-y₁`, a contradiction.  This proves (8)."*

`X₁ = extraEdges G H K φ Y y₁` and `X₂ = extraEdges G H K φ Y y₂` (see
`Workspace.ProofLemmas.Thm61Setup`).  The antihole is `Q ++ [h₂, h₁]` read in `Gᶜ`: `h₁` (as a
vertex of `L(H)`, i.e. through `φ`) is complete to `Y \ {y₁}` and non-adjacent to `y₁`, `h₂` is
complete to `Y \ {y₂}` and non-adjacent to `y₂`, and `h₁, h₂` are non-adjacent in `G` exactly
because the two edges do not meet in `H`.  Since `Q` is even it has an odd number of vertices,
so the antihole has an odd number of vertices — contradicting `Berge G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim8

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup

/-- **6.1(8)** *"Every edge in `X₁` meets every edge in `X₂`."* -/
theorem thm_6_1_claim8
    {V : Type*} (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h₁ h₂ : Sym2 (Fin n))
    (hh₁ : h₁ ∈ extraEdges G H K φ Y y₁) (hh₂ : h₂ ∈ extraEdges G H K φ Y y₂) :
    MeetEdges h₁ h₂ := by
  intro hdisj
  obtain ⟨⟨he₁, hc₁⟩, hn₁⟩ := hh₁
  obtain ⟨⟨he₂, hc₂⟩, hn₂⟩ := hh₂
  set z₁ : V := (↑(φ ⟨h₁, he₁⟩) : V) with hz₁def
  set z₂ : V := (↑(φ ⟨h₂, he₂⟩) : V) with hz₂def
  -- `y₁` and `y₂` are members of `Y`.
  have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
  have hy₂Y : y₂ ∈ Y := (hQY y₂).mp (List.mem_of_mem_getLast? hQ.2.2)
  -- Both `y₁, y₂` are major, hence outside `K = V(L(H))`, while `z₁, z₂ ∈ K`.
  have hz₁K : z₁ ∈ K := (φ ⟨h₁, he₁⟩).2
  have hz₂K : z₂ ∈ K := (φ ⟨h₂, he₂⟩).2
  have hy₁K : y₁ ∉ K := (hYmajor y₁ hy₁Y).1
  have hy₂K : y₂ ∉ K := (hYmajor y₂ hy₂Y).1
  have hz₁ny₁ : z₁ ≠ y₁ := fun h => hy₁K (h ▸ hz₁K)
  have hz₁ny₂ : z₁ ≠ y₂ := fun h => hy₂K (h ▸ hz₁K)
  have hz₂ny₁ : z₂ ≠ y₁ := fun h => hy₁K (h ▸ hz₂K)
  have hz₂ny₂ : z₂ ≠ y₂ := fun h => hy₂K (h ▸ hz₂K)
  -- `h₁ ∈ X₁` is complete to `Y \ {y₁}` but not to `Y`, so it misses exactly `y₁`.
  have hadj₁₂ : G.Adj z₁ y₂ := hc₁ y₂ ⟨hy₂Y, by simpa using hy.symm⟩
  have hadj₂₁ : G.Adj z₂ y₁ := hc₂ y₁ ⟨hy₁Y, by simpa using hy⟩
  have hnadj₁ : ¬ G.Adj z₁ y₁ := by
    intro hcon
    refine hn₁ ⟨he₁, ?_⟩
    intro x hx
    by_cases hxy : x = y₁
    · exact hxy ▸ hcon
    · exact hc₁ x ⟨hx, by simpa using hxy⟩
  have hnadj₂ : ¬ G.Adj z₂ y₂ := by
    intro hcon
    refine hn₂ ⟨he₂, ?_⟩
    intro x hx
    by_cases hxy : x = y₂
    · exact hxy ▸ hcon
    · exact hc₂ x ⟨hx, by simpa using hxy⟩
  -- Neither `z₁` nor `z₂` lies in `Y` (each is complete to a set containing itself otherwise).
  have hz₁Y : z₁ ∉ Y := fun h => G.irrefl (hc₁ z₁ ⟨h, by simpa using hz₁ny₁⟩)
  have hz₂Y : z₂ ∉ Y := fun h => G.irrefl (hc₂ z₂ ⟨h, by simpa using hz₂ny₂⟩)
  -- The two edges are distinct, since they do not meet.
  have hnonempty : ∀ e : Sym2 (Fin n), ∃ w : Fin n, w ∈ e := by
    intro e
    induction e using Sym2.ind with
    | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩
  have hne : h₁ ≠ h₂ := by
    rintro rfl
    obtain ⟨w, hw⟩ := hnonempty h₁
    exact hdisj w ⟨hw, hw⟩
  have hzne : z₁ ≠ z₂ := by
    intro h
    exact hne (congrArg Subtype.val (φ.toEquiv.injective (Subtype.ext h)))
  -- `h₁` and `h₂` do not meet, so they are non-adjacent in `L(H)`, hence in `G`.
  have hnadjz : ¬ G.Adj z₁ z₂ := by
    intro hcon
    have hlg : H.lineGraph.Adj ⟨h₁, he₁⟩ ⟨h₂, he₂⟩ := φ.map_adj_iff.mp hcon
    obtain ⟨-, w, hw₁, hw₂⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hlg
    exact hdisj w ⟨hw₁, hw₂⟩
  -- `[z₂, z₁]` is an antipath.
  have hRpath : IsPathFrom Gᶜ [z₂, z₁] z₂ z₁ :=
    ⟨PathBasics.isPathList_pair
      (show Gᶜ.Adj z₂ z₁ from ⟨hzne.symm, fun h => hnadjz h.symm⟩), rfl, rfl⟩
  -- `Q` misses `z₁, z₂`.
  have hdisjQ : ∀ x ∈ Q, x ∉ [z₂, z₁] := by
    intro x hx hmem
    have hxY : x ∈ Y := (hQY x).mp hx
    rcases List.mem_cons.mp hmem with h | h
    · exact hz₂Y (h ▸ hxY)
    · rcases List.mem_cons.mp h with h' | h'
      · exact hz₁Y (h' ▸ hxY)
      · simp at h'
  -- The only edges between `Q` and `[z₂, z₁]` in `Gᶜ` are `y₂-z₂` and `y₁-z₁`.
  have hcross : ∀ x ∈ Q, ∀ y ∈ [z₂, z₁],
      (Gᶜ.Adj x y ↔ (x = y₂ ∧ y = z₂) ∨ (x = y₁ ∧ y = z₁)) := by
    intro x hx y hymem
    have hyz : y = z₂ ∨ y = z₁ := by
      rcases List.mem_cons.mp hymem with h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h' | h'
        · exact Or.inr h'
        · simp at h'
    by_cases hxy₁ : x = y₁
    · subst hxy₁
      rcases hyz with rfl | rfl
      · refine iff_of_false (fun hcon => hcon.2 hadj₂₁.symm) ?_
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hy h
        · exact hzne h.symm
      · refine iff_of_true ⟨fun h => hz₁ny₁ h.symm, fun h => hnadj₁ h.symm⟩ (Or.inr ⟨rfl, rfl⟩)
    by_cases hxy₂ : x = y₂
    · subst hxy₂
      rcases hyz with rfl | rfl
      · refine iff_of_true ⟨fun h => hz₂ny₂ h.symm, fun h => hnadj₂ h.symm⟩ (Or.inl ⟨rfl, rfl⟩)
      · refine iff_of_false (fun hcon => hcon.2 hadj₁₂.symm) ?_
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hzne h
        · exact hxy₁ h
    · -- `x` is an internal vertex of `Q`, hence in `Y \ {y₁, y₂}`, hence adjacent to both.
      have hxY : x ∈ Y := (hQY x).mp hx
      refine iff_of_false ?_ ?_
      · intro hcon
        rcases hyz with rfl | rfl
        · exact hcon.2 (hc₂ x ⟨hxY, by simpa using hxy₂⟩).symm
        · exact hcon.2 (hc₁ x ⟨hxY, by simpa using hxy₁⟩).symm
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact hxy₂ h
        · exact hxy₁ h
  -- `Q` has at least two vertices, since its ends are distinct.
  have hQlen : 2 ≤ Q.length := by
    by_contra hcon
    push_neg at hcon
    have h1 : Q.length = 1 := by
      rcases Nat.eq_zero_or_pos Q.length with h0 | h0
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hQ.1.1
      · omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
    have hy₁Q : y₁ ∈ Q := List.mem_of_mem_head? hQ.2.1
    have hy₂Q : y₂ ∈ Q := List.mem_of_mem_getLast? hQ.2.2
    rw [ha] at hy₁Q hy₂Q
    exact hy ((List.eq_of_mem_singleton hy₁Q).trans (List.eq_of_mem_singleton hy₂Q).symm)
  have hhole : IsHoleList Gᶜ (Q ++ [z₂, z₁]) :=
    PathGlue.glue_hole hQ hRpath hdisjQ hcross (by simp; omega)
  have heven := hG.2 _ hhole
  simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at heven
  rw [Nat.even_iff] at heven
  have hple : Even (pathLength Q) := hQeven
  rw [pathLength, Nat.even_iff] at hple
  omega

end Workspace.ProofLemmas.Thm61Claim8
