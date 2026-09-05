import Workspace.ProofLemmas.HyperprismLocalEnlargementCore
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.Statements.S10.Thm_10_3
import Workspace.Statements.S10.Thm_10_5
import Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iStep

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementInterior

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.Thm106Assembly

/-- The data needed to carry out the paper's instruction to add the first vertex of an
outside path to an `A`-set and its remaining vertices to the matching `C`-set. -/
def ExtensionData {V : Type*} (G : SimpleGraph V) (A B C : Fin 3 → Set V) : Prop :=
  ∃ (p : List V) (u : V),
    u ∈ p ∧ p.Nodup ∧
    (∀ z ∈ p, z ∉ hyperVerts A B C) ∧
    (∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A k, G.Adj u a) ∧
    (∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
      ∀ y ∈ A k ∪ B k ∪ C k, G.Adj z y → z = u ∧ y ∈ A k) ∧
    (let A' := fun k : Fin 3 => if k = 0 then A k ∪ {u} else A k
     let C' := fun k : Fin 3 =>
       if k = 0 then C k ∪ {z : V | z ∈ p ∧ z ≠ u} else C k
     ∃ q : List V, IsRungOfHyperprism G A' B C' 0 q ∧ ∀ z ∈ p, z ∈ q)

/-- PAPER (10.6, claim (2), printed p. 61):
*"From the minimality of `F` it follows that `F={f₁,…,fₙ}`. Since this holds for all
choices of `R₃` ... `f₁` is complete to `A₃` ... [and] complete to `A₂` ... ."*

Together with 10.3, these sentences produce the extension data, up to permuting the strips
and exchanging the two ends of every strip.  This lemma isolates that varying-rung argument;
the construction of the larger hyperprism from the data is proved below. -/
theorem interiorAttachmentProducesExtensionData
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hK4 : NoK4 G)
    (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hInterior : ∃ (i : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) ∧ x ∈ C i) :
    (∃ σ : Equiv.Perm (Fin 3),
      ExtensionData G (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k))) ∨
    (∃ σ : Equiv.Perm (Fin 3),
      ExtensionData G (fun k => B (σ k)) (fun k => A (σ k)) (fun k => C (σ k))) := by
  rcases Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3iStep.interiorProducesExtData
      hG hK4 hNoBalanced hH hF hInterior with ⟨σ, h⟩ | ⟨σ, h⟩
  · exact Or.inl ⟨σ, h⟩
  · exact Or.inr ⟨σ, h⟩

/-- An interior attachment yields the strict enlargement displayed in claim (2). -/
theorem interiorAttachment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hK4 : NoK4 G)
    (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hInterior : ∃ (i : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) ∧ x ∈ C i) :
    BiggerHyperprism G A B C := by
  rcases interiorAttachmentProducesExtensionData G A B C F hG hK4 hNoBalanced hH hF
      hInterior with h | h
  · obtain ⟨σ, p, u, hup, hnd, hout, hcomplete, hcross, hrung⟩ := h
    have hH' := Workspace.ProofLemmas.HyperprismTwoAttachments.isHyperprism_perm hG hH σ
    have hbig := Workspace.ProofLemmas.HyperprismLocalEnlargementCore.leftExtensionAtZero
      G (fun k => A (σ k)) (fun k => B (σ k)) (fun k => C (σ k)) hH'
      p u hup hnd hout hcomplete hcross hrung
    exact biggerHyperprism_perm hbig
  · obtain ⟨σ, p, u, hup, hnd, hout, hcomplete, hcross, hrung⟩ := h
    have hHswap := Workspace.ProofLemmas.HyperprismTwoAttachments.isHyperprism_swap hH
    have hH' := Workspace.ProofLemmas.HyperprismTwoAttachments.isHyperprism_perm hG hHswap σ
    have hbig := Workspace.ProofLemmas.HyperprismLocalEnlargementCore.leftExtensionAtZero
      G (fun k => B (σ k)) (fun k => A (σ k)) (fun k => C (σ k)) hH'
      p u hup hnd hout hcomplete hcross hrung
    exact biggerHyperprism_swap (biggerHyperprism_perm hbig)

end Workspace.ProofLemmas.HyperprismLocalEnlargementInterior
