import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.ProofLemmas.HyperprismLocalEnlargementEven
import Workspace.ProofLemmas.HyperprismLocalEnlargementInterior
import Workspace.ProofLemmas.HyperprismLocalEnlargementOdd
import Workspace.Types.Decompositions

set_option autoImplicit false

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementGaps

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup
open Workspace.ProofLemmas.Thm106Assembly

/-- PAPER (10.6, claim (2), printed pp. 60–61):
*"But then we can add `f₁` to `A₁` and `{f₂,…,fₙ}` to `C₁`, contradicting the
maximality of the hyperprism."*

This is the first enlargement block, under the hypotheses obtained when an attachment lies in
the interior of a strip. -/
theorem interiorAttachmentYieldsBigger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hK4 : NoK4 G)
    (hNoBalanced : ¬ AdmitsBalancedSkewPartition G)
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hInterior : ∃ (i : Fin 3) (x : V),
      x ∈ attachments G F (hyperVerts A B C) ∧ x ∈ C i) :
    BiggerHyperprism G A B C := by
  exact Workspace.ProofLemmas.HyperprismLocalEnlargementInterior.interiorAttachment
    G A B C F hG hK4 hNoBalanced hH hF hInterior

/-- PAPER (10.6, claim (2), printed pp. 61–62):
*"But then the nine sets [displayed in the paper] form a hyperprism, contrary to the
maximality of `V(H)`. This completes the argument when `n` is even."*

The displayed construction is packaged as a strictly larger hyperprism. -/
theorem evenAttachmentPathYieldsBigger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V)
    (hG : Berge G) (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    (hNoC : ∀ x ∈ attachments G F (hyperVerts A B C), ∀ k : Fin 3, x ∉ C k)
    (i j : Fin 3) (hij : i ≠ j) (xA xB : V)
    (hxAatt : xA ∈ attachments G F (hyperVerts A B C)) (hxAA : xA ∈ A i)
    (hxBatt : xB ∈ attachments G F (hyperVerts A B C)) (hxBB : xB ∈ B j)
    (hPath : ∃ f : List V,
      f ≠ [] ∧ (∀ v ∈ f, v ∈ F) ∧
      IsPathFrom G (xA :: (f ++ [xB])) xA xB ∧
      (∀ v ∈ f, G.Adj xA v ↔ f.head? = some v) ∧
      (∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v) ∧
      F = {v : V | v ∈ f} ∧ Even f.length) :
    BiggerHyperprism G A B C := by
  exact Workspace.ProofLemmas.HyperprismLocalEnlargementEven.evenAttachmentPath
    G A B C F hG hH hF hNoC i j hij xA xB hxAatt hxAA hxBatt hxBB hPath

/-- PAPER (10.6, claim (2), printed p. 62):
*"But then [the displayed nine sets] is a hyperprism, contrary to the maximality of
`V(H)`. This proves (2)."*

The displayed construction in the odd path case is packaged as a strictly larger
hyperprism. -/
theorem oddAttachmentPathYieldsBigger
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
  exact Workspace.ProofLemmas.HyperprismLocalEnlargementOdd.oddAttachmentPath
    G A B C F hG hK4 hNoBalanced hH hF hNoC hij hxAatt hxAA hxBatt hxBB hPath

end Workspace.ProofLemmas.HyperprismLocalEnlargementGaps
