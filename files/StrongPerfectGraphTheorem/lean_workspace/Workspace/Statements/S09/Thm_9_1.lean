/-  Proof attempt for statement 9.1 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.  Reproduces the printed proof
    (`paper/proofs/9_1.md`, printed p. 48) step for step. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.Thm91KnotOddness

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S09

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

namespace SPGT

/-! ### Two shape-lemmas used to read off the knot conditions -/

section Helpers

variable {V : Type*}

/-- Complementary adjacency to a vertex off the list. -/
private theorem Thm91_compl_adj_iff {G : SimpleGraph V} {u z : V} (hne : u ≠ z) :
    Gᶜ.Adj u z ↔ ¬ G.Adj z u := by
  rw [SimpleGraph.compl_adj, SimpleGraph.adj_comm]
  simp [hne]

/-- PAPER: *"`a₁, b₁, a₂, b₂` are all `Y`-complete, from the last condition in the definition
of a knot"* — the last condition says every nonedge between an antipath and `{aᵢ, bᵢ}` uses an
*end* of the antipath, so the interior is seen completely. -/
private theorem Thm91_vertexComplete_interior {G : SimpleGraph V} {Q : List V} {x y w : V}
    (hQ : IsPathFrom Gᶜ Q x y) (h : ∀ u ∈ Q, ¬ G.Adj u w → (u = x ∨ u = y)) :
    VertexComplete G w {z : V | z ∈ SPGT.interior Q} := by
  intro z hz
  obtain ⟨hzQ, hzx, hzy⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hz
  by_contra hadj
  rcases h z hzQ (fun hh => hadj hh.symm) with h1 | h1
  · exact hzx h1
  · exact hzy h1

/-- Dually: an edge from a path to a vertex that only its two ends can carry misses the
interior of the path. -/
private theorem Thm91_no_interior_adj {G : SimpleGraph V} {P : List V} {a b w : V}
    (hP : IsPathFrom G P a b) (h : ∀ u ∈ P, G.Adj u w → (u = a ∨ u = b)) :
    ∀ z ∈ SPGT.interior P, ¬ G.Adj z w := by
  intro z hz hadj
  obtain ⟨hzP, hza, hzb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hz
  rcases h z hzP hadj with h1 | h1
  · exact hza h1
  · exact hzb h1

end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **9.1** (printed p. 48)

PAPER: *"Let `(P₁,P₂,Q₁,Q₂)` be a knot in a Berge graph `G`.  Then all four of `P₁,P₂,Q₁,Q₂`
have odd length; and either both `P₁,P₂` have length 1, or both `Q₁,Q₂` have length 1."*

The lengths are `Core.pathLength` (the number of edges; for an antipath, the number of edges
of its complement — the same number). -/
theorem thm_9_1 (G : SimpleGraph V) (hG : Berge G) (P₁ P₂ Q₁ Q₂ : List V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂) :
    (Odd (pathLength P₁) ∧ Odd (pathLength P₂) ∧
      Odd (pathLength Q₁) ∧ Odd (pathLength Q₂)) ∧
    ((pathLength P₁ = 1 ∧ pathLength P₂ = 1) ∨
      (pathLength Q₁ = 1 ∧ pathLength Q₂ = 1)) := by
  -- PAPER: *"Define `aᵢ, bᵢ, xᵢ, yᵢ (i = 1,2)` as usual."*
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hP1, hP2, hQ1, hQ2,
    d12, d1q1, d1q2, d2q1, d2q2, dq12,
    lP1, lP2, lQ1, lQ2, hanti, hcomp, hE11, hE12, hE21, hE22, hN11, hN12, hN31, hN42⟩ := hknot
  have hGc : Berge Gᶜ := HoleBasics.berge_compl.mpr hG
  -- ends as list members
  have ha₁P₁ : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP1).1
  have hb₁P₁ : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP1).2
  have ha₂P₂ : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP2).1
  have hb₂P₂ : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP2).2
  have hx₁Q₁ : x₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ1).1
  have hy₁Q₁ : y₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ1).2
  have hx₂Q₂ : x₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ2).1
  have hy₂Q₂ : y₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ2).2
  -- the four pairs of ends are distinct (all four have length ≥ 1)
  have ha₁b₁ : a₁ ≠ b₁ := PathBasics.isPathFrom_ends_ne hP1 lP1
  have ha₂b₂ : a₂ ≠ b₂ := PathBasics.isPathFrom_ends_ne hP2 lP2
  have hx₁y₁ : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hQ1 lQ1
  have hx₂y₂ : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hQ2 lQ2
  -- ==========================================================================
  -- PAPER: *"Certainly `P₁` is odd since `x₁-a₁-P₁-b₁-y₂-x₁` is a hole, and similarly the
  -- other three are odd."*
  -- ==========================================================================
  have oddP₁ : Odd (pathLength P₁) := by
    refine Thm91.odd_of_two_attachments hG hP1 lP1
      (fun h => d1q1 x₁ h hx₁Q₁) (fun h => d1q2 y₂ h hy₂Q₂) (hcomp x₁ hx₁Q₁ y₂ hy₂Q₂) ?_ ?_
    · intro z hz
      rw [SimpleGraph.adj_comm, hE11 z hz x₁ (by simp)]
      simp [hx₁y₁]
    · intro z hz
      rw [SimpleGraph.adj_comm, hE12 z hz y₂ (by simp)]
      simp [hx₂y₂.symm]
  have oddP₂ : Odd (pathLength P₂) := by
    refine Thm91.odd_of_two_attachments hG hP2 lP2
      (fun h => d2q1 x₁ h hx₁Q₁) (fun h => d2q2 x₂ h hx₂Q₂) (hcomp x₁ hx₁Q₁ x₂ hx₂Q₂) ?_ ?_
    · intro z hz
      rw [SimpleGraph.adj_comm, hE21 z hz x₁ (by simp)]
      simp [hx₁y₁]
    · intro z hz
      rw [SimpleGraph.adj_comm, hE22 z hz x₂ (by simp)]
      simp [hx₂y₂]
  -- the two antipaths: the mirror hole `b₁-x₁-Q₁-y₁-a₂-b₁` of `Gᶜ`
  have hb₁a₂c : Gᶜ.Adj b₁ a₂ :=
    (SimpleGraph.compl_adj G b₁ a₂).mpr
      ⟨fun h => d12 b₁ hb₁P₁ (h ▸ ha₂P₂), hanti b₁ hb₁P₁ a₂ ha₂P₂⟩
  have hb₁b₂c : Gᶜ.Adj b₁ b₂ :=
    (SimpleGraph.compl_adj G b₁ b₂).mpr
      ⟨fun h => d12 b₁ hb₁P₁ (h ▸ hb₂P₂), hanti b₁ hb₁P₁ b₂ hb₂P₂⟩
  have oddQ₁ : Odd (pathLength Q₁) := by
    refine Thm91.odd_of_two_attachments hGc hQ1 lQ1
      (d1q1 b₁ hb₁P₁) (d2q1 a₂ ha₂P₂) hb₁a₂c ?_ ?_
    · intro z hz
      rw [Thm91_compl_adj_iff (fun h => d1q1 b₁ hb₁P₁ (by rw [h]; exact hz)), hN11 z hz b₁ (by simp)]
      simp [ha₁b₁.symm]
    · intro z hz
      rw [Thm91_compl_adj_iff (fun h => d2q1 a₂ ha₂P₂ (by rw [h]; exact hz)), hN31 z hz a₂ (by simp)]
      simp [ha₂b₂]
  have oddQ₂ : Odd (pathLength Q₂) := by
    refine Thm91.odd_of_two_attachments hGc hQ2 lQ2
      (d1q2 b₁ hb₁P₁) (d2q2 b₂ hb₂P₂) hb₁b₂c ?_ ?_
    · intro z hz
      rw [Thm91_compl_adj_iff (fun h => d1q2 b₁ hb₁P₁ (by rw [h]; exact hz)), hN12 z hz b₁ (by simp)]
      simp [ha₁b₁.symm]
    · intro z hz
      rw [Thm91_compl_adj_iff (fun h => d2q2 b₂ hb₂P₂ (by rw [h]; exact hz)), hN42 z hz b₂ (by simp)]
      simp [ha₂b₂.symm]
  refine ⟨⟨oddP₁, oddP₂, oddQ₁, oddQ₂⟩, ?_⟩
  -- ==========================================================================
  -- PAPER: *"Suppose one of `P₁, P₂` has length `> 1` and one of `Q₁, Q₂` has length `> 1`."*
  -- ==========================================================================
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hcP, hcQ⟩ := hcon
  have hlongP : 3 ≤ pathLength P₁ ∨ 3 ≤ pathLength P₂ := by
    by_contra h
    push_neg at h
    obtain ⟨k₁, hk₁⟩ := oddP₁
    obtain ⟨k₂, hk₂⟩ := oddP₂
    exact hcP ⟨by omega, by omega⟩
  have hlongQ : 3 ≤ pathLength Q₁ ∨ 3 ≤ pathLength Q₂ := by
    by_contra h
    push_neg at h
    obtain ⟨k₁, hk₁⟩ := oddQ₁
    obtain ⟨k₂, hk₂⟩ := oddQ₂
    exact hcQ ⟨by omega, by omega⟩
  -- `a₂` has no neighbour in the interior of `P₁`, and `a₁` none in that of `P₂`
  have hcP₁ : ∀ w ∈ SPGT.interior P₁, ¬ G.Adj a₂ w := fun w hw hadj =>
    hanti w (PathBasics.interior_subset hw) a₂ ha₂P₂ hadj.symm
  have hcP₂ : ∀ w ∈ SPGT.interior P₂, ¬ G.Adj a₁ w := fun w hw hadj =>
    hanti a₁ ha₁P₁ w (PathBasics.interior_subset hw) hadj
  -- PAPER: *"By exchanging `P₁, P₂` or `Q₁, Q₂` we may therefore assume that `P₁, Q₁` both
  -- have length `> 1`."*  The four exchanged configurations are run out in turn.
  rcases hlongP with hPlong | hPlong <;> rcases hlongQ with hQlong | hQlong
  -- ---------------------------------------------------------------- (P₁, Q₁)
  · refine Thm91.no_long_path_and_antipath hG hP1 oddP₁ hPlong hQ1 hQlong d1q1 ?_ ?_ ?_
      hcP₁ ?_ ?_ ?_ ?_ ?_ ?_
    · refine Thm91_vertexComplete_interior hQ1 (fun u hu hn => ?_)
      rcases (hN11 u hu a₁ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact absurd h ha₁b₁
    · refine Thm91_vertexComplete_interior hQ1 (fun u hu hn => ?_)
      rcases (hN11 u hu b₁ (by simp)).mp hn with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm ha₁b₁
      · exact Or.inl h
    · refine Thm91_vertexComplete_interior hQ1 (fun u hu hn => ?_)
      rcases (hN31 u hu a₂ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact absurd h ha₂b₂
    · exact (hE11 a₁ ha₁P₁ x₁ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
    · exact (hE11 b₁ hb₁P₁ y₁ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)
    · intro hadj
      rcases (hE11 a₁ ha₁P₁ y₁ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact hx₁y₁ h.symm
      · exact ha₁b₁ h
    · intro hadj
      rcases (hE11 b₁ hb₁P₁ x₁ (by simp)).mp hadj.symm with ⟨h, -⟩ | ⟨-, h⟩
      · exact ha₁b₁ h.symm
      · exact hx₁y₁ h
    · refine Thm91_no_interior_adj hP1 (fun u hu hadj => ?_)
      rcases (hE11 u hu x₁ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact absurd h hx₁y₁
    · refine Thm91_no_interior_adj hP1 (fun u hu hadj => ?_)
      rcases (hE11 u hu y₁ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₁y₁
      · exact Or.inr h
  -- ---------------------------------------------------------------- (P₁, Q₂)
  · refine Thm91.no_long_path_and_antipath hG hP1 oddP₁ hPlong hQ2 hQlong d1q2 ?_ ?_ ?_
      hcP₁ ?_ ?_ ?_ ?_ ?_ ?_
    · refine Thm91_vertexComplete_interior hQ2 (fun u hu hn => ?_)
      rcases (hN12 u hu a₁ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact absurd h ha₁b₁
    · refine Thm91_vertexComplete_interior hQ2 (fun u hu hn => ?_)
      rcases (hN12 u hu b₁ (by simp)).mp hn with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm ha₁b₁
      · exact Or.inl h
    · refine Thm91_vertexComplete_interior hQ2 (fun u hu hn => ?_)
      rcases (hN42 u hu a₂ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact absurd h ha₂b₂
    · exact (hE12 a₁ ha₁P₁ x₂ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
    · exact (hE12 b₁ hb₁P₁ y₂ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)
    · intro hadj
      rcases (hE12 a₁ ha₁P₁ y₂ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact hx₂y₂ h.symm
      · exact ha₁b₁ h
    · intro hadj
      rcases (hE12 b₁ hb₁P₁ x₂ (by simp)).mp hadj.symm with ⟨h, -⟩ | ⟨-, h⟩
      · exact ha₁b₁ h.symm
      · exact hx₂y₂ h
    · refine Thm91_no_interior_adj hP1 (fun u hu hadj => ?_)
      rcases (hE12 u hu x₂ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact absurd h hx₂y₂
    · refine Thm91_no_interior_adj hP1 (fun u hu hadj => ?_)
      rcases (hE12 u hu y₂ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₂y₂
      · exact Or.inr h
  -- ---------------------------------------------------------------- (P₂, Q₁)
  · refine Thm91.no_long_path_and_antipath hG hP2 oddP₂ hPlong hQ1 hQlong d2q1 ?_ ?_ ?_
      hcP₂ ?_ ?_ ?_ ?_ ?_ ?_
    · refine Thm91_vertexComplete_interior hQ1 (fun u hu hn => ?_)
      rcases (hN31 u hu a₂ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact absurd h ha₂b₂
    · refine Thm91_vertexComplete_interior hQ1 (fun u hu hn => ?_)
      rcases (hN31 u hu b₂ (by simp)).mp hn with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm ha₂b₂
      · exact Or.inl h
    · refine Thm91_vertexComplete_interior hQ1 (fun u hu hn => ?_)
      rcases (hN11 u hu a₁ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact absurd h ha₁b₁
    · exact (hE21 a₂ ha₂P₂ x₁ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
    · exact (hE21 b₂ hb₂P₂ y₁ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)
    · intro hadj
      rcases (hE21 a₂ ha₂P₂ y₁ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact hx₁y₁ h.symm
      · exact ha₂b₂ h
    · intro hadj
      rcases (hE21 b₂ hb₂P₂ x₁ (by simp)).mp hadj.symm with ⟨h, -⟩ | ⟨-, h⟩
      · exact ha₂b₂ h.symm
      · exact hx₁y₁ h
    · refine Thm91_no_interior_adj hP2 (fun u hu hadj => ?_)
      rcases (hE21 u hu x₁ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact absurd h hx₁y₁
    · refine Thm91_no_interior_adj hP2 (fun u hu hadj => ?_)
      rcases (hE21 u hu y₁ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h.symm hx₁y₁
      · exact Or.inr h
  -- ---------------------------------------------------------------- (P₂, Q₂)
  -- Here the knot attaches `a₂` to `y₂` and `b₂` to `x₂`, so the antipath is traversed
  -- backwards; `Q₂.reverse` is the antipath `y₂-Q₂-x₂`, with the same interior.
  · have hQ2r : IsPathFrom Gᶜ Q₂.reverse y₂ x₂ := PathBasics.isPathFrom_reverse hQ2
    have hQ2rlen : 3 ≤ pathLength Q₂.reverse := by
      rwa [PathBasics.pathLength_reverse]
    refine Thm91.no_long_path_and_antipath hG hP2 oddP₂ hPlong hQ2r hQ2rlen
      (fun w hw hmem => d2q2 w hw (List.mem_reverse.mp hmem)) ?_ ?_ ?_
      hcP₂ ?_ ?_ ?_ ?_ ?_ ?_
    · refine Thm91_vertexComplete_interior hQ2r (fun u hu hn => ?_)
      rcases (hN42 u (List.mem_reverse.mp hu) a₂ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inr h
      · exact absurd h ha₂b₂
    · refine Thm91_vertexComplete_interior hQ2r (fun u hu hn => ?_)
      rcases (hN42 u (List.mem_reverse.mp hu) b₂ (by simp)).mp hn with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h.symm ha₂b₂
      · exact Or.inl h
    · refine Thm91_vertexComplete_interior hQ2r (fun u hu hn => ?_)
      rcases (hN12 u (List.mem_reverse.mp hu) a₁ (by simp)).mp hn with ⟨-, h⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact absurd h ha₁b₁
    · exact (hE22 a₂ ha₂P₂ y₂ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)
    · exact (hE22 b₂ hb₂P₂ x₂ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)
    · intro hadj
      rcases (hE22 a₂ ha₂P₂ x₂ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact hx₂y₂ h
      · exact ha₂b₂ h
    · intro hadj
      rcases (hE22 b₂ hb₂P₂ y₂ (by simp)).mp hadj.symm with ⟨h, -⟩ | ⟨-, h⟩
      · exact ha₂b₂ h.symm
      · exact hx₂y₂ h.symm
    · refine Thm91_no_interior_adj hP2 (fun u hu hadj => ?_)
      rcases (hE22 u hu y₂ (by simp)).mp hadj with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact absurd h.symm hx₂y₂
    · refine Thm91_no_interior_adj hP2 (fun u hu hadj => ?_)
      rcases (hE22 u hu x₂ (by simp)).mp hadj with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h hx₂y₂
      · exact Or.inr h


end SPGT

end Workspace.Statements.S09
