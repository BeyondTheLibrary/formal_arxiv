import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm85LineGraphBridge
import Workspace.ProofLemmas.Thm85Claim2Cases
import Workspace.ProofLemmas.Thm85Claim2PerChoice
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath

/-!
# 8.5, claim (2): the same conclusion for *every* choice of rungs

PAPER (proof of 8.5, claim (2), printed p. 42): *"… and since it holds for all choices of the
rungs `R_vw`, we deduce that `X \ S_uv = N_v \ S_uv`."*

The printed proof runs the whole 5.8-argument again for each choice of rungs; this module does
exactly that, packaging *"make a choice of rungs, form `L(H)`, apply 5.8, discard 5.8.1 and the
last three subcases of 5.8.2"* into one statement that takes an arbitrary choice of rungs as
input.  The only thing the choice has to satisfy is that it carries two prescribed attachments
of `F` whose pair is not local.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm85Claim2AllChoices

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]

/-- **The conclusion of the first half of claim (2), for an arbitrary choice of rungs.**

Given any choice of rungs carrying two attachments `c₁ ∈ R_{v e₁}`, `c₂ ∈ R_{v e₂}` of `F`
whose pair is not local, there is a neighbour `u₀` of `v` such that on every other rung at `v`
the attachments of `F` are exactly the vertices of `N_v`. -/
theorem allChoices
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (v : U)
    (hXv : attachments G F (stripSystemVertices J S) ⊆
      ⋃ (a : U) (_ : J.Adj a v), S a v)
    (R : U → U → List V) (hR : ∀ a b : U, J.Adj a b → IsUVRung G J S N a b (R a b))
    (hRsymm : ∀ a b : U, J.Adj a b → R b a = (R a b).reverse)
    (c1 c2 : V) (e1 e2 : U) (he1 : J.Adj v e1) (he2 : J.Adj v e2)
    (hc1X : c1 ∈ attachments G F (stripSystemVertices J S))
    (hc2X : c2 ∈ attachments G F (stripSystemVertices J S))
    (hc1R : c1 ∈ R v e1) (hc2R : c2 ∈ R v e2)
    (hpair : ¬ LocalForStripSystem J S N ({c1, c2} : Set V)) :
    ∃ u0 : U, J.Adj v u0 ∧
      ∀ w : U, J.Adj v w → w ≠ u0 → ∀ z ∈ R v w,
        (z ∈ attachments G F (stripSystemVertices J S) ↔ z ∈ N v) := by
  classical
  obtain ⟨n, H, hForms⟩ :=
    Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph
      G hG J hJ S N hSN R hR hRsymm
  obtain ⟨phi⟩ := hForms.2.2
  let K : Set V := ⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b}
  have hc1K : c1 ∈ K := by
    simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨v, e1, he1, hc1R⟩
  have hc2K : c2 ∈ K := by
    simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨v, e2, he2, hc2R⟩
  have hFormsK : FormsLineGraph G J S N R H := hForms
  have hphiK : H.lineGraph ≃g G.induce K := phi
  obtain ⟨e, e', he, he', hphie, hphie', hepair⟩ :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.exists_nonlocal_preimage_pair
      G J hJ S N hSN H R hFormsK hphiK v e1 v e2 he1 he2 c1 c2 hc1R hc2R hpair
  have heatt : (↑(hphiK ⟨e, he⟩) : V) ∈ attachments G F K := by
    rw [hphie]; exact ⟨hc1K, hc1X.2⟩
  have he'att : (↑(hphiK ⟨e', he'⟩) : V) ∈ attachments G F K := by
    rw [hphie']; exact ⟨hc2K, hc2X.2⟩
  have hnotlocal : ¬ LocalForLineGraph H
      {f : Sym2 (Fin n) | ∃ hf : f ∈ H.edgeSet,
        (↑(hphiK ⟨f, hf⟩) : V) ∈ attachments G F K} :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.attachmentEdges_not_local_of_pair
      G H K F hphiK e e' he he' heatt he'att hepair
  have hKsub : K ⊆ stripSystemVertices J S :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.rungUnion_subset_stripSystemVertices
      G J S N R hR
  have hFK : F ⊆ Kᶜ := fun z hzF hzK => (hFcompl hzF) (hKsub hzK)
  have hclaim := hclaim1 n H R K hphiK rfl hFormsK
  have hnomajor : ∀ y ∈ F, ¬ MajorForLineGraph G H K hphiK y := by
    intro y hy hmajor
    exact hclaim.1 y hy hmajor.2
  let Nc : Fin n → Set V := fun c =>
    {z : V | ∃ (f : Sym2 (Fin n)) (hf : f ∈ H.edgeSet),
      f ∈ incidentEdges H c ∧ z = (↑(hphiK ⟨f, hf⟩) : V)}
  obtain ⟨Q, p1, p2, hQ, hQF, hout⟩ :=
    Workspace.ProofLemmas.Thm85Five8Transported.thm85Five8Transported
      G hG J hJ n H K hFormsK.2.1 hphiK Nc (fun _ => rfl) F hFK hFconn hnotlocal hnomajor
  rcases hout with hfirst | hbranch
  · obtain ⟨d1, d2, hnb, hd1, hd2, hattach⟩ := hfirst
    exact absurd
      (Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath
        G hG J hJ n H K hFormsK.2 hphiK Nc
          (fun _ => rfl) Q p1 p2 hQ (fun z hzQ => hFK (hQF z hzQ)) d1 d2 hnb hd1 hd2
          hattach hclaim.2) hnoenl
  · obtain ⟨b1, b2, q, Rline, r1, r2, hb1, hb2, hq, hqfrom, hRline, hRimage,
        hr1, hr2, hcases⟩ := hbranch
    have hcaseA :=
      Workspace.ProofLemmas.Thm85Claim2Cases.branch_outcome_forces_first_case
        G J hJ S N hSN H R hFormsK hphiK Nc (fun _ => rfl) F v hXv Q p1 p2 hQ hQF
        b1 b2 q Rline r1 r2 hb1 hb2 hq hqfrom hr1 hr2 hcases
    exact Workspace.ProofLemmas.Thm85Claim2PerChoice.per_choice_attachments_at_v
      G J hJ S N hSN F hFmin v hXv H R hFormsK hphiK Nc (fun _ => rfl) Q p1 p2 hQ hQF
      b1 b2 q Rline r1 r2 hb1 hb2 hq hqfrom hRimage hr1 hr2 hcaseA

end Workspace.ProofLemmas.Thm85Claim2AllChoices
