import Workspace.ProofLemmas.HyperprismLocalEnlargementTwoEnded
import Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality
import Workspace.ProofLemmas.HyperprismLocalEnlargementRegroup
import Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oData
import Workspace.Statements.S10.Thm_10_5

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementOdd

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.Thm106Assembly

/-- PAPER (10.6, odd case, printed p. 62): the paragraph beginning
*"Hence for all `1≤i≤3` ..."* and ending
*"and similarly `B'ᵢ` is complete to `B''ᵢ`."*

The conclusion is the data immediately before the final displayed construction.  The
old vertices have already been split, regrouped, and permuted so that the outside path
is to be inserted in row zero.  The construction from this data is separate below. -/
theorem oddCaseProducesExtensionData
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hK4 : NoK4 G)
    (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) → x ∉ C k)
    {i j : Fin 3} (hij : i ≠ j) {xA xB : V}
    (hxAatt : xA ∈ attachments G F (hyperVerts A B C)) (hxAA : xA ∈ A i)
    (hxBatt : xB ∈ attachments G F (hyperVerts A B C)) (hxBB : xB ∈ B j)
    (hPath : ∃ f : List V,
      f ≠ [] ∧ (∀ v ∈ f, v ∈ F) ∧
      IsPathFrom G (xA :: (f ++ [xB])) xA xB ∧
      (∀ v ∈ f, G.Adj xA v ↔ f.head? = some v) ∧
      (∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v) ∧
      F = {v : V | v ∈ f} ∧ Odd f.length) :
    ∃ (A₀ B₀ C₀ : Fin 3 → Set V) (p : List V) (u v : V),
      IsHyperprism G A₀ B₀ C₀ ∧
      hyperVerts A₀ B₀ C₀ = hyperVerts A B C ∧
      u ∈ p ∧ v ∈ p ∧ u ≠ v ∧ p.Nodup ∧
      (∀ z ∈ p, z ∉ hyperVerts A₀ B₀ C₀) ∧
      (∀ (k : Fin 3), k ≠ 0 → ∀ a ∈ A₀ k, G.Adj u a) ∧
      (∀ (k : Fin 3), k ≠ 0 → ∀ b ∈ B₀ k, G.Adj v b) ∧
      (∀ z ∈ p, ∀ (k : Fin 3), k ≠ 0 →
        ∀ y ∈ A₀ k ∪ B₀ k ∪ C₀ k, G.Adj z y →
          (z = u ∧ y ∈ A₀ k) ∨ (z = v ∧ y ∈ B₀ k)) ∧
      (let A' := fun k : Fin 3 => if k = 0 then A₀ k ∪ {u} else A₀ k
       let B' := fun k : Fin 3 => if k = 0 then B₀ k ∪ {v} else B₀ k
       let C' := fun k : Fin 3 => if k = 0 then
         C₀ k ∪ {z : V | z ∈ p ∧ z ≠ u ∧ z ≠ v} else C₀ k
       ∃ q : List V, IsRungOfHyperprism G A' B' C' 0 q ∧ ∀ z ∈ p, z ∈ q) := by
  classical
  obtain ⟨f, hfne, hfF, hfull, hleft, hright, hFeq, hodd⟩ := hPath
  obtain ⟨σ, hσ0, hσ1⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j := by
    rcases fin3_cases i with rfl | rfl | rfl <;>
      rcases fin3_cases j with rfl | rfl | rfl
    all_goals try { exact absurd rfl hij }
    all_goals decide
  have hH' := HyperprismTwoAttachments.isHyperprism_perm hG hH σ
  have hF' := minimalBad_perm σ hF
  have hNoC' : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F
        (hyperVerts (fun r => A (σ r)) (fun r => B (σ r)) (fun r => C (σ r))) →
      x ∉ C (σ k) := by
    intro k x hx
    exact hNoC (σ k) x (by rwa [hyperVerts_perm] at hx)
  obtain ⟨A₀, B₀, C₀, p, u, v, hH₀, hverts, hrest⟩ :=
    Workspace.ProofLemmas.HyperprismLocalEnlargementhyp3oData.oddDataAtZeroOne
      G (fun r => A (σ r)) (fun r => B (σ r)) (fun r => C (σ r)) F hG hK4
      hNoBalanced hH' hF' hNoC' (by simpa [hσ0] using hxAA) (by simpa [hσ1] using hxBB)
      f hfne hfF hfull hleft hright hFeq hodd
  exact ⟨A₀, B₀, C₀, p, u, v, hH₀, by rwa [hyperVerts_perm] at hverts, hrest⟩

/-- The odd attachment path yields the final displayed enlargement in claim (2). -/
theorem oddAttachmentPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hK4 : NoK4 G)
    (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ (k : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) → x ∉ C k)
    {i j : Fin 3} (hij : i ≠ j) {xA xB : V}
    (hxAatt : xA ∈ attachments G F (hyperVerts A B C)) (hxAA : xA ∈ A i)
    (hxBatt : xB ∈ attachments G F (hyperVerts A B C)) (hxBB : xB ∈ B j)
    (hPath : ∃ f : List V,
      f ≠ [] ∧ (∀ v ∈ f, v ∈ F) ∧
      IsPathFrom G (xA :: (f ++ [xB])) xA xB ∧
      (∀ v ∈ f, G.Adj xA v ↔ f.head? = some v) ∧
      (∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v) ∧
      F = {v : V | v ∈ f} ∧ Odd f.length) :
    BiggerHyperprism G A B C := by
  obtain ⟨A₀, B₀, C₀, p, u, v, hH₀, hverts, hup, hvp, huv, hnd, hout,
      huComplete, hvComplete, hcross, hrung⟩ :=
    oddCaseProducesExtensionData G A B C F hG hK4 hNoBalanced hH hF hNoC hij
      hxAatt hxAA hxBatt hxBB hPath
  have hbig := Workspace.ProofLemmas.HyperprismLocalEnlargementTwoEnded.twoEndedExtensionAtZero
    G A₀ B₀ C₀ hH₀ p u v hup hvp huv hnd hout huComplete hvComplete hcross hrung
  obtain ⟨Anew, Bnew, Cnew, hHnew, hstrict⟩ := hbig
  exact ⟨Anew, Bnew, Cnew, hHnew, by rwa [hverts] at hstrict⟩

end Workspace.ProofLemmas.HyperprismLocalEnlargementOdd
