import Workspace.ProofLemmas.Thm61EvenEndgameClaim12

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim12Common

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61EvenEndgameClaim12
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- In claim (12), "`b` is a triad". Apply the four-edge-track argument with `b` and `v`
interchanged. Every complete edge at `b` meets the third edge at `v`, so bipartiteness makes
that complete edge unique. This also applies when `v = b₃`. -/
theorem triad_at_b
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hbip : H.IsBipartite) (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (h9 : Claim9 G H K φ Y y₁ y₂)
    {b b₁ b₂ u v : Fin n} {e₁ e₂ d₁ d₂ f₁ g : Sym2 (Fin n)}
    (hbV : b ∈ branchVertices H)
    (he₁ : e₁ ∈ incidentEdges H b) (he₁X : e₁ ∈ extraEdges G H K φ Y y₁)
    (he₂ : e₂ ∈ incidentEdges H b) (he₂X : e₂ ∈ extraEdges G H K φ Y y₂)
    (hd₁ : d₁ ∈ incidentEdges H b₁) (hd₁X : d₁ ∈ extraEdges G H K φ Y y₂)
    (hd₂ : d₂ ∈ incidentEdges H b₂) (hd₂X : d₂ ∈ extraEdges G H K φ Y y₁)
    (hf₁X : f₁ ∈ completeEdges G H K φ Y)
    (he₁eq : e₁ = s(b, b₁)) (he₂eq : e₂ = s(b, b₂))
    (hd₁eq : d₁ = s(b₁, v)) (hd₂eq : d₂ = s(b₂, v))
    (hf₁eq : f₁ = s(b₁, u))
    (hbb₁ : b ≠ b₁) (hbb₂ : b ≠ b₂) (hb₁b₂ : b₁ ≠ b₂)
    (hv₁ : v ≠ b₁) (hv₂ : v ≠ b₂) (hub : u ≠ b) (huv : u ≠ v)
    (hg : g ∈ incidentEdges H v) (hgd₁ : g ≠ d₁) (hgd₂ : g ≠ d₂) :
    Triad G H K φ Y b := by
  classical
  have h9swap : Claim9 G H K φ Y y₂ y₁ := by
    intro Z hZ P hP hlen heven hfirst hlast hint f hf
    apply h9 Z _ P hP hlen heven hfirst hlast hint f hf
    rcases hZ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hd₁v : d₁ ∈ incidentEdges H v := ⟨hd₁.1, by rw [hd₁eq]; simp⟩
  have hd₂v : d₂ ∈ incidentEdges H v := ⟨hd₂.1, by rw [hd₂eq]; simp⟩
  have he₁b₁ : e₁ ∈ incidentEdges H b₁ := ⟨he₁.1, by rw [he₁eq]; simp⟩
  have he₂b₂ : e₂ ∈ incidentEdges H b₂ := ⟨he₂.1, by rw [he₂eq]; simp⟩
  have hde₁ : d₁ = s(v, b₁) := hd₁eq.trans Sym2.eq_swap
  have hde₂ : d₂ = s(v, b₂) := hd₂eq.trans Sym2.eq_swap
  have hed₁ : e₁ = s(b₁, b) := he₁eq.trans Sym2.eq_swap
  have hed₂ : e₂ = s(b₂, b) := he₂eq.trans Sym2.eq_swap
  have hvf₁ : v ∉ f₁ := by simp [hf₁eq, hv₁, huv.symm]
  have hother := claim12_other_edge_at_v G n H K hbip φ Y hmin y₂ y₁ Q.reverse
    (Workspace.ProofLemmas.PathBasics.isAntipathFrom_reverse hQ)
    (fun x => by simpa using hQY x) hy.symm h9swap
    hd₁v hd₁X hd₂v hd₂X hg hgd₁ hgd₂ he₁b₁ he₁X he₂b₂ he₂X hf₁X
    hde₁ hde₂ hed₁ hed₂ hf₁eq hv₁ hv₂ hb₁b₂ hbb₁ hbb₂ hub hvf₁
  have hbg : b ∉ g := by
    intro hbg
    have hbb₁A : H.Adj b b₁ := H.mem_edgeSet.mp (he₁eq ▸ he₁.1)
    have hb₁vA : H.Adj b₁ v := H.mem_edgeSet.mp (hd₁eq ▸ hd₁.1)
    have hbve : b ≠ v := by
      intro h
      have heq : e₁ = d₁ := by rw [he₁eq, hd₁eq, h, Sym2.eq_swap]
      have hdis := (X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy).2.2.2.2.2.1
      exact Set.disjoint_left.mp hdis (heq ▸ he₁X) hd₁X
    have hgeq : g = s(b, v) := eq_sym2_of_mem_mem hbve hbg hg.2
    exact no_triangle_of_bipartite hbip hbb₁A hb₁vA
      (H.mem_edgeSet.mp (hgeq ▸ hg.1))
  refine ⟨hbV, ?_⟩
  intro a ha c hc
  apply meeting_edges_at_vertex_subsingleton hbip hg.1 hbg
  · exact ⟨ha.1, (hother a ha.1
      (fun h => he₁X.2 (h ▸ ha.2)) (fun h => he₂X.2 (h ▸ ha.2))).2⟩
  · exact ⟨hc.1, (hother c hc.1
      (fun h => he₁X.2 (h ▸ hc.2)) (fun h => he₂X.2 (h ▸ hc.2))).2⟩

end Workspace.ProofLemmas.Thm61Claim12Common
