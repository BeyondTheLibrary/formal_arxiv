import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
import Workspace.ProofLemmas.Thm75Claim2Five82Dominance

/-!
# Reversing the names of the two distinguished branch ends

PAPER (proof of 7.5, claim (2), printed p. 37): *"(This is without loss of generality, because
in this case 2, there is symmetry between `b₁ = c₁` and `b₂ = c₂`.)"*

Nothing in the statement of 7.5 distinguishes `c₁` from `c₂`: reversing the distinguished
branch and exchanging the two names gives the same appearance data.  This module records that
symmetry once, so that the case `b₁ = c₂, b₂ = c₁` of the 5.8.2 analysis can be handled by the
same lemmas as the case `b₁ = c₁, b₂ = c₂`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim2Five82Reverse

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
open Workspace.ProofLemmas.Thm75Claim2Five82Dominance

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}

/-- The same appearance, with its distinguished branch traversed in the other direction. -/
def BranchAppearance.rev (a : BranchAppearance G J) : BranchAppearance G J where
  m := a.m
  H := a.H
  K := a.K
  φ := a.φ
  happ := a.happ
  B := a.B.reverse
  c₁ := a.c₂
  c₂ := a.c₁
  hbranch := Workspace.ProofLemmas.Thm57Claim2Structure.isBranch_reverse a.hbranch
  hfrom := Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse a.hfrom
  hodd := by
    have h : trackLength a.B.reverse = trackLength a.B := by simp [trackLength]
    rw [h]; exact a.hodd
  hlen := by
    have h : trackLength a.B.reverse = trackLength a.B := by simp [trackLength]
    rw [h]; exact a.hlen

@[simp] theorem rev_K (a : BranchAppearance G J) : (BranchAppearance.rev a).K = a.K := rfl

@[simp] theorem rev_leftClique (a : BranchAppearance G J) :
    (BranchAppearance.rev a).leftClique = a.rightClique := rfl

@[simp] theorem rev_rightClique (a : BranchAppearance G J) :
    (BranchAppearance.rev a).rightClique = a.leftClique := rfl

@[simp] theorem rev_rung (a : BranchAppearance G J) : (BranchAppearance.rev a).rung = a.rung := by
  show {x : V | ∃ (e : Sym2 (Fin a.m)) (he : e ∈ a.H.edgeSet),
      e ∈ trackEdges a.B.reverse ∧ x = (↑(a.φ ⟨e, he⟩) : V)} = _
  rw [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
  rfl

/-- `OneCliqueReplacement` is symmetric under exchanging the two distinguished ends on both
sides: its first alternative is preserved, and the two nontrivial alternatives swap. -/
theorem oneCliqueReplacement_swap {N₁ N₂ N₁' N₂' : Set V}
    (h : OneCliqueReplacement G N₁ N₂ N₁' N₂') : OneCliqueReplacement G N₂ N₁ N₂' N₁' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h2, h1⟩
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- The same-branch witness for the reversed names. -/
def sameBranchReplacementDataRev {N₁ N₂ K Rset T F : Set V} {a : BranchAppearance G J}
    (d : SameBranchReplacementData G N₁ N₂ K Rset T F a) :
    SameBranchReplacementData G N₂ N₁ K Rset T F (BranchAppearance.rev a) where
  r₁ := d.r₂
  r₂ := d.r₁
  p₁ := d.p₂
  p₂ := d.p₁
  P := d.P.reverse
  hP := Workspace.ProofLemmas.PathBasics.isPathFrom_reverse d.hP
  hPF := fun x hx => d.hPF x (List.mem_reverse.mp hx)
  hr₁ := d.hr₂
  hr₂ := d.hr₁
  h₁ := d.h₂
  h₂ := d.h₁
  hno := by
    intro x hx y hy hadj
    rcases d.hno x (List.mem_reverse.mp hx) y hy hadj with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  hno_T := d.hno_T.symm
  hleft := d.hright
  hright := d.hleft
  hrung := by
    rw [rev_rung, d.hrung]
    ext x
    simp

end Workspace.ProofLemmas.Thm75Claim2Five82Reverse
