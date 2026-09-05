import Workspace.ProofLemmas.Thm93CaseTwoSixOnePairs
import Workspace.ProofLemmas.Thm93CaseTwoSixOneDict
import Workspace.ProofLemmas.Thm61EvenFinalK4
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Dictionary lemmas for the non-major vertex of case (2) of 9.3

The complement lane of 9.3 applies 5.8 to the single vertex `f`.  This module collects the
purely bookkeeping facts that the analysis of its outcome needs: the complement neighbourhoods
inside `K` of the eight labelled vertices of the knot, the transfer of an "exact neighbour set"
statement from `G̅` back to `G`, and the identification of a branch of `H` from its two ends.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Workspace.ProofLemmas.Thm93CaseTwoNonmajorDict

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93CaseTwoSixOnePairs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Transferring an "exact neighbour set" statement from `G̅` to `G`.

If `f` lies outside `K`, is `G̅`-complete to `S`, has all its `G̅`-neighbours in `K` inside `T`,
and `a` is a vertex of `K` whose `G̅`-neighbours inside `W` are exactly `S ∩ W`, then `f` and
`a` have the same neighbours in `W`, provided `T ∩ W ⊆ S` and `a ∉ W`. -/
theorem same_of_sets {G : SimpleGraph V} {K : Set V} {f a : V} (hfK : f ∉ K)
    {S T W : Set V}
    (hsup : ∀ w ∈ S, Gᶜ.Adj f w)
    (hsub : ∀ w ∈ K, Gᶜ.Adj f w → w ∈ T)
    (hTW : ∀ w ∈ W, w ∈ T → w ∈ S)
    (ha : ∀ w ∈ W, (Gᶜ.Adj a w ↔ w ∈ S))
    (hW : W ⊆ K) (haW : a ∉ W) :
    ∀ w ∈ W, (G.Adj f w ↔ G.Adj a w) := by
  intro w hw
  have hwK : w ∈ K := hW hw
  have hfw : f ≠ w := fun h => hfK (h ▸ hwK)
  have haw : a ≠ w := fun h => haW (h ▸ hw)
  have hf : Gᶜ.Adj f w ↔ w ∈ S := by
    refine ⟨fun h => hTW w hw (hsub w hwK h), fun h => hsup w h⟩
  have h1 : G.Adj f w ↔ ¬ (w ∈ S) := by
    rw [← hf]
    simp only [SimpleGraph.compl_adj, not_and, not_not]
    exact ⟨fun h h' => h, fun h => h hfw⟩
  have h2 : G.Adj a w ↔ ¬ (w ∈ S) := by
    rw [← ha w hw]
    simp only [SimpleGraph.compl_adj, not_and, not_not]
    exact ⟨fun h h' => h, fun h => h haw⟩
  rw [h1, h2]


section Neighbourhoods

variable {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V} {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K : Set V}

/-- The `G̅`-neighbourhoods of the eight labelled vertices of a knot whose two paths have
length `1`, each read off the part of `K` that avoids the label's own path or antipath.

These are just the knot axioms, one vertex at a time; in the language of the degenerate
appearance carried by the knot they are the four triangles `N(c₁), …, N(c₄)`. -/
theorem knot_compl_neighbours
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hL : Labels P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K) :
    ((∀ w ∈ ({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gᶜ.Adj b₁ w ↔ w ∈ ({a₂, b₂, x₁, x₂} : Set V))) ∧
      (∀ w ∈ ({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gᶜ.Adj a₁ w ↔ w ∈ ({a₂, b₂, y₁, y₂} : Set V))) ∧
      (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gᶜ.Adj a₂ w ↔ w ∈ ({a₁, b₁, y₁, x₂} : Set V))) ∧
      (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gᶜ.Adj b₂ w ↔ w ∈ ({a₁, b₁, x₁, y₂} : Set V)))) ∧
    ((∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gᶜ.Adj x₁ w ↔ w ∈ ({b₁, b₂} : Set V))) ∧
      (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gᶜ.Adj y₁ w ↔ w ∈ ({a₁, a₂} : Set V))) ∧
      (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} : Set V),
        (Gᶜ.Adj x₂ w ↔ w ∈ ({b₁, a₂} : Set V))) ∧
      (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} : Set V),
        (Gᶜ.Adj y₂ w ↔ w ∈ ({a₁, b₂} : Set V)))) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hanti, hcomp, hE11, hE12, hE21, hE22,
    hN11, hN12, hN21, hN22⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  obtain ⟨⟨d1, d2, d3, d4, d5, d6, d7⟩, ⟨d8, d9, d10, d11, d12, d13⟩,
    ⟨d14, d15, d16, d17, d18⟩, ⟨d19, d20, d21, d22⟩,
    ⟨d23, d24, d25, d26, d27, d28⟩⟩ := all_ne hL
  have hP1mem : ∀ w ∈ P₁, w = a₁ ∨ w = b₁ := by
    intro w hw; rw [hL.P₁_eq] at hw; simpa using hw
  have hP2mem : ∀ w ∈ P₂, w = a₂ ∨ w = b₂ := by
    intro w hw; rw [hL.P₂_eq] at hw; simpa using hw
  have ha₁P : a₁ ∈ P₁ := by rw [hL.P₁_eq]; simp
  have hb₁P : b₁ ∈ P₁ := by rw [hL.P₁_eq]; simp
  have ha₂P : a₂ ∈ P₂ := by rw [hL.P₂_eq]; simp
  have hb₂P : b₂ ∈ P₂ := by rw [hL.P₂_eq]; simp
  have hna : ∀ u ∈ P₁, ∀ v ∈ P₂, ¬ G.Adj u v := fun u hu v hv => hanti u hu v hv
  have hna' : ∀ u ∈ P₁, ∀ v ∈ P₂, ¬ G.Adj v u := fun u hu v hv hh => hanti u hu v hv hh.symm

  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP2mem w hw with h | h
        · rw [h]
          simp [SimpleGraph.compl_adj, hna b₁ hb₁P a₂ ha₂P, d8]
        · rw [h]
          simp [SimpleGraph.compl_adj, hna b₁ hb₁P b₂ hb₂P, d9]
      · have hq := hL.Q₁_ne w hw
        have hn : ¬ G.Adj b₁ w ↔ w = x₁ := by
          rw [SimpleGraph.adj_comm, hN11 w hw b₁ (by simp)]
          constructor
          · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
            · exact absurd he (Ne.symm d1)
            · exact hw'
          · intro hw'; exact Or.inr ⟨rfl, hw'⟩
        simp [SimpleGraph.compl_adj, hn, Ne.symm hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]
    · have hq := hL.Q₂_ne w hw
      have hn : ¬ G.Adj b₁ w ↔ w = x₂ := by
        rw [SimpleGraph.adj_comm, hN12 w hw b₁ (by simp)]
        constructor
        · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
          · exact absurd he (Ne.symm d1)
          · exact hw'
        · intro hw'; exact Or.inr ⟨rfl, hw'⟩
      simp [SimpleGraph.compl_adj, hn, Ne.symm hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1]
  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP2mem w hw with h | h
        · rw [h]
          simp [SimpleGraph.compl_adj, hna a₁ ha₁P a₂ ha₂P, d2]
        · rw [h]
          simp [SimpleGraph.compl_adj, hna a₁ ha₁P b₂ hb₂P, d3]
      · have hq := hL.Q₁_ne w hw
        have hn : ¬ G.Adj a₁ w ↔ w = y₁ := by
          rw [SimpleGraph.adj_comm, hN11 w hw a₁ (by simp)]
          constructor
          · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
            · exact hw'
            · exact absurd he d1
          · intro hw'; exact Or.inl ⟨rfl, hw'⟩
        simp [SimpleGraph.compl_adj, hn, Ne.symm hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.2]
    · have hq := hL.Q₂_ne w hw
      have hn : ¬ G.Adj a₁ w ↔ w = y₂ := by
        rw [SimpleGraph.adj_comm, hN12 w hw a₁ (by simp)]
        constructor
        · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
          · exact hw'
          · exact absurd he d1
        · intro hw'; exact Or.inl ⟨rfl, hw'⟩
      simp [SimpleGraph.compl_adj, hn, Ne.symm hq.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.2]
  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP1mem w hw with h | h
        · rw [h]
          simp [SimpleGraph.compl_adj, hna' a₁ ha₁P a₂ ha₂P, (Ne.symm d2)]
        · rw [h]
          simp [SimpleGraph.compl_adj, hna' b₁ hb₁P a₂ ha₂P, (Ne.symm d8)]
      · have hq := hL.Q₁_ne w hw
        have hn : ¬ G.Adj a₂ w ↔ w = y₁ := by
          rw [SimpleGraph.adj_comm, hN21 w hw a₂ (by simp)]
          constructor
          · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
            · exact hw'
            · exact absurd he d14
          · intro hw'; exact Or.inl ⟨rfl, hw'⟩
        simp [SimpleGraph.compl_adj, hn, Ne.symm hq.2.2.1, hq.1, hq.2.1, hq.2.2.2.2.1]
    · have hq := hL.Q₂_ne w hw
      have hn : ¬ G.Adj a₂ w ↔ w = x₂ := by
        rw [SimpleGraph.adj_comm, hN22 w hw a₂ (by simp)]
        constructor
        · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
          · exact hw'
          · exact absurd he d14
        · intro hw'; exact Or.inl ⟨rfl, hw'⟩
      simp [SimpleGraph.compl_adj, hn, Ne.symm hq.2.2.1, hq.1, hq.2.1, hq.2.2.2.2.2]
  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP1mem w hw with h | h
        · rw [h]
          simp [SimpleGraph.compl_adj, hna' a₁ ha₁P b₂ hb₂P, (Ne.symm d3)]
        · rw [h]
          simp [SimpleGraph.compl_adj, hna' b₁ hb₁P b₂ hb₂P, (Ne.symm d9)]
      · have hq := hL.Q₁_ne w hw
        have hn : ¬ G.Adj b₂ w ↔ w = x₁ := by
          rw [SimpleGraph.adj_comm, hN21 w hw b₂ (by simp)]
          constructor
          · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
            · exact absurd he (Ne.symm d14)
            · exact hw'
          · intro hw'; exact Or.inr ⟨rfl, hw'⟩
        simp [SimpleGraph.compl_adj, hn, Ne.symm hq.2.2.2.1, hq.1, hq.2.1, hq.2.2.2.2.2]
    · have hq := hL.Q₂_ne w hw
      have hn : ¬ G.Adj b₂ w ↔ w = y₂ := by
        rw [SimpleGraph.adj_comm, hN22 w hw b₂ (by simp)]
        constructor
        · rintro (⟨he, hw'⟩ | ⟨he, hw'⟩)
          · exact absurd he (Ne.symm d14)
          · exact hw'
        · intro hw'; exact Or.inr ⟨rfl, hw'⟩
      simp [SimpleGraph.compl_adj, hn, Ne.symm hq.2.2.2.1, hq.1, hq.2.1, hq.2.2.2.2.1]

  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP1mem w hw with h | h
        · rw [h]
          have e : G.Adj x₁ a₁ := ((hE11 a₁ ha₁P x₁ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, d1, d3]
        · rw [h]
          have e : ¬ G.Adj x₁ b₁ := by
            intro hh
            rcases (hE11 b₁ hb₁P x₁ (by simp)).mp hh.symm with ⟨he, -⟩ | ⟨-, he⟩
            · exact d1 he.symm
            · exact d23 he
          simp [SimpleGraph.compl_adj, e, Ne.symm d10]
      · rcases hP2mem w hw with h | h
        · rw [h]
          have e : G.Adj x₁ a₂ := ((hE21 a₂ ha₂P x₁ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, Ne.symm d8, d14]
        · rw [h]
          have e : ¬ G.Adj x₁ b₂ := by
            intro hh
            rcases (hE21 b₂ hb₂P x₁ (by simp)).mp hh.symm with ⟨he, -⟩ | ⟨-, he⟩
            · exact d14 he.symm
            · exact d23 he
          simp [SimpleGraph.compl_adj, e, Ne.symm d19]
    · have hq := hL.Q₂_ne w hw
      have e : G.Adj x₁ w := hcomp x₁ hL.x₁_mem w hw
      simp [SimpleGraph.compl_adj, e, hq.2.1, hq.2.2.2.1]
  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP1mem w hw with h | h
        · rw [h]
          have e : ¬ G.Adj y₁ a₁ := by
            intro hh
            rcases (hE11 a₁ ha₁P y₁ (by simp)).mp hh.symm with ⟨-, he⟩ | ⟨he, -⟩
            · exact d23 he.symm
            · exact d1 he
          simp [SimpleGraph.compl_adj, e, Ne.symm d5]
        · rw [h]
          have e : G.Adj y₁ b₁ := ((hE11 b₁ hb₁P y₁ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, Ne.symm d1, d8]
      · rcases hP2mem w hw with h | h
        · rw [h]
          have e : ¬ G.Adj y₁ a₂ := by
            intro hh
            rcases (hE21 a₂ ha₂P y₁ (by simp)).mp hh.symm with ⟨-, he⟩ | ⟨he, -⟩
            · exact d23 he.symm
            · exact d14 he
          simp [SimpleGraph.compl_adj, e, Ne.symm d16]
        · rw [h]
          have e : G.Adj y₁ b₂ := ((hE21 b₂ hb₂P y₁ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, Ne.symm d3, Ne.symm d14]
    · have hq := hL.Q₂_ne w hw
      have e : G.Adj y₁ w := hcomp y₁ hL.y₁_mem w hw
      simp [SimpleGraph.compl_adj, e, hq.1, hq.2.2.1]
  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP1mem w hw with h | h
        · rw [h]
          have e : G.Adj x₂ a₁ := ((hE12 a₁ ha₁P x₂ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, d1, d2]
        · rw [h]
          have e : ¬ G.Adj x₂ b₁ := by
            intro hh
            rcases (hE12 b₁ hb₁P x₂ (by simp)).mp hh.symm with ⟨he, -⟩ | ⟨-, he⟩
            · exact d1 he.symm
            · exact d28 he
          simp [SimpleGraph.compl_adj, e, Ne.symm d12]
      · rcases hP2mem w hw with h | h
        · rw [h]
          have e : ¬ G.Adj x₂ a₂ := by
            intro hh
            rcases (hE22 a₂ ha₂P x₂ (by simp)).mp hh.symm with ⟨-, he⟩ | ⟨he, -⟩
            · exact d28 he
            · exact d14 he
          simp [SimpleGraph.compl_adj, e, Ne.symm d17]
        · rw [h]
          have e : G.Adj x₂ b₂ := ((hE22 b₂ hb₂P x₂ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, Ne.symm d9, Ne.symm d14]
    · have hq := hL.Q₁_ne w hw
      have e : G.Adj x₂ w := (hcomp w hw x₂ hL.x₂_mem).symm
      simp [SimpleGraph.compl_adj, e, hq.2.1, hq.2.2.1]
  · intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · rcases hP1mem w hw with h | h
        · rw [h]
          have e : ¬ G.Adj y₂ a₁ := by
            intro hh
            rcases (hE12 a₁ ha₁P y₂ (by simp)).mp hh.symm with ⟨-, he⟩ | ⟨he, -⟩
            · exact d28 he.symm
            · exact d1 he
          simp [SimpleGraph.compl_adj, e, Ne.symm d7]
        · rw [h]
          have e : G.Adj y₂ b₁ := ((hE12 b₁ hb₁P y₂ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, Ne.symm d1, d9]
      · rcases hP2mem w hw with h | h
        · rw [h]
          have e : G.Adj y₂ a₂ := ((hE22 a₂ ha₂P y₂ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm
          simp [SimpleGraph.compl_adj, e, Ne.symm d2, d14]
        · rw [h]
          have e : ¬ G.Adj y₂ b₂ := by
            intro hh
            rcases (hE22 b₂ hb₂P y₂ (by simp)).mp hh.symm with ⟨he, -⟩ | ⟨-, he⟩
            · exact d14 he.symm
            · exact d28 he.symm
          simp [SimpleGraph.compl_adj, e, Ne.symm d22]
    · have hq := hL.Q₁_ne w hw
      have e : G.Adj y₂ w := (hcomp w hw y₂ hL.y₂_mem).symm
      simp [SimpleGraph.compl_adj, e, hq.1, hq.2.2.2.1]

end Neighbourhoods

section Branches

/-- A branch is determined by its two ends, in either orientation. -/
theorem branch_edges_eq {m n : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {H : SimpleGraph (Fin n)} (hsub : IsSubdivision J H)
    {B C : List (Fin n)} {d₁ d₂ d₁' d₂' : Fin n}
    (hB : IsBranch H B) (hB2 : 2 ≤ B.length) (hBfrom : IsTrackFrom H B d₁ d₂)
    (hC : IsBranch H C) (hC2 : 2 ≤ C.length) (hCfrom : IsTrackFrom H C d₁' d₂')
    (hd₁ : d₁ ∈ branchVertices H) (hd₂ : d₂ ∈ branchVertices H)
    (hmatch : (d₁' = d₁ ∧ d₂' = d₂) ∨ (d₁' = d₂ ∧ d₂' = d₁)) :
    trackEdges B = trackEdges C := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  exact BranchClassification.trackEdges_eq_of_same_ends hι htrack hlen hrev hdisj hnew hcover
    hedges (SubdivisionCounting.three_le_degree_of_three_connected J hJ) hB hB2 hBfrom hC hC2
    hCfrom hd₁ hd₂ hmatch

/-- Two adjacent branch-vertices are joined by the one-edge branch. -/
theorem isBranch_pair {n : ℕ} {H : SimpleGraph (Fin n)} {u v : Fin n}
    (hadj : H.Adj u v) (hu : u ∈ branchVertices H) (hv : v ∈ branchVertices H) :
    IsBranch H [u, v] ∧ IsTrackFrom H [u, v] u v ∧
      trackEdges ([u, v] : List (Fin n)) = ({s(u, v)} : Set (Sym2 (Fin n))) := by
  have hlist : IsTrackList H [u, v] := by
    refine ⟨by simp, by simp [hadj.ne], ?_⟩
    intro i hi
    have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
    subst hi0
    simpa using hadj
  have hfrom : IsTrackFrom H [u, v] u v := ⟨hlist, by simp, by simp⟩
  have hint : ∀ w ∈ trackInterior ([u, v] : List (Fin n)), w ∉ branchVertices H := by
    intro w hw
    simp [trackInterior] at hw
  have hedges : trackEdges ([u, v] : List (Fin n)) = ({s(u, v)} : Set (Sym2 (Fin n))) := by
    ext e
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi0 : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
      subst hi0
      simp
    · intro he
      refine ⟨0, by simp, ?_⟩
      simpa using he
  exact ⟨Thm82BranchDelta.isBranch_of_ends_branch hfrom hadj.ne hint hu hv, hfrom, hedges⟩

/-- The image under `φ` of a one-edge branch is a single vertex of `K`. -/
theorem image_singleton_edge {n : ℕ} {D : SimpleGraph V} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g D.induce K) {e : Sym2 (Fin n)} (he : e ∈ H.edgeSet) :
    {x : V | ∃ (e' : Sym2 (Fin n)) (he' : e' ∈ H.edgeSet),
        e' ∈ ({e} : Set (Sym2 (Fin n))) ∧ x = (↑(phi ⟨e', he'⟩) : V)} =
      ({(↑(phi ⟨e, he⟩) : V)} : Set V) := by
  ext x
  constructor
  · rintro ⟨e', he', hmem, rfl⟩
    have : e' = e := hmem
    subst this
    rfl
  · intro hx
    exact ⟨e, he, rfl, hx⟩

end Branches

end Workspace.ProofLemmas.Thm93CaseTwoNonmajorDict
