import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm58Setup
import Workspace.ProofLemmas.Thm58StarBranch
import Workspace.ProofLemmas.Thm58StarStar
import Workspace.ProofLemmas.Thm58BranchBranchEndNeighbors

/-!
# The four local-set combinations in the proof of 5.8

After the minimal path has been chosen, each of `X₁` and `X₂` is local.  A local set is either
contained in the edges at a branch-vertex or in the edges of a branch.  The four lemmas below
are exactly the four combinations.  Together they are the paper's claims (2)--(7).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58LocalCases

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

section Common

variable
    (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K)
    (N : Fin n → Set V)
    (F : Set V)
    (P : List V) (p₁ p₂ : V)

/-- GAP — PAPER claims (3) and (4), printed pp. 26--27: if `X₁` and `X₂` are both contained
in vertex stars, the nonadjacent-star and adjacent-star arguments give the conclusion. -/
theorem starStar
    (hready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    (c₁ c₂ : Fin n) (hc₁ : c₁ ∈ branchVertices H) (hc₂ : c₂ ∈ branchVertices H)
    (hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₂}) K} ⊆ incidentEdges H c₁)
    (hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₁}) K} ⊆ incidentEdges H c₂) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ ∨
      Thm58Setup.Outcome G n H K φ N P.reverse p₂ p₁ :=
  Thm58StarStar.starStar hready hc₁ hc₂ hX₁ hX₂

/-- GAP — PAPER claims (2) and (6), printed pp. 26 and 27: if `X₁` is contained in a vertex
star and `X₂` in a branch, the incident and nonincident cases give the conclusion. -/
theorem starBranch
    (hready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    (c : Fin n) (hc : c ∈ branchVertices H) (q : List (Fin n)) (hq : IsBranch H q)
    (hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₂}) K} ⊆ incidentEdges H c)
    (hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₁}) K} ⊆ trackEdges q) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  exact Thm58StarBranch.starBranch hready hc hq hX₁ hX₂

/-- GAP — the index-reversed form of PAPER claims (2) and (6), printed pp. 26 and 27: if
`X₁` is contained in a branch and `X₂` in a vertex star, the same arguments give the
conclusion after reversing `P`. -/
theorem branchStar
    (hready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    (q : List (Fin n)) (hq : IsBranch H q) (c : Fin n) (hc : c ∈ branchVertices H)
    (hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₂}) K} ⊆ trackEdges q)
    (hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₁}) K} ⊆ incidentEdges H c) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ ∨
      Thm58Setup.Outcome G n H K φ N P.reverse p₂ p₁ :=
  Or.inr (Thm58StarBranch.starBranch (Thm58BranchBranch.ready_reverse hready) hc hq hX₂ hX₁)

/-- GAP — PAPER claims (5) and (7), printed pp. 27--28: if `X₁` and `X₂` are both contained
in branches, the intersecting-branch and two-branch arguments give the conclusion. -/
theorem branchBranch
    (hready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    (q₁ q₂ : List (Fin n)) (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₂}) K} ⊆ trackEdges q₁)
    (hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₁}) K} ⊆ trackEdges q₂) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  apply Thm58BranchBranch.branchBranch hready q₁ q₂ hq₁ hq₂ hX₁ hX₂
  · intro c hc hstar
    exact starBranch G m J n H K φ N F P p₁ p₂ hready c hc q₂ hq₂ hstar hX₂
  · intro c hc hstar
    exact starBranch G m J n H K φ N F P.reverse p₂ p₁
      (Thm58BranchBranch.ready_reverse hready) c hc q₁ hq₁ hstar hX₁

end Common

end Workspace.ProofLemmas.Thm58LocalCases
