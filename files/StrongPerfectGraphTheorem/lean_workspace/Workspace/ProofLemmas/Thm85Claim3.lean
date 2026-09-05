import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm85RungChoice
import Workspace.ProofLemmas.Thm85LineGraphBridge
import Workspace.ProofLemmas.Thm85Claim3Analysis
import Workspace.ProofLemmas.Thm85Claim3Closing
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath

/-!
# 8.5, claim (3)

PAPER (printed p. 42, proof of 8.5, immediately after (2)):

*"Let `K = {uv ∈ E(J) : X ∩ S_uv ≠ ∅}`.*

*(3) There are two disjoint edges in `K`.*

*For make a choice of rungs `R_uv` (`uv ∈ E(J)`) such that `X ∩ V(R_uv) ≠ ∅` for each
`uv ∈ K`, forming `L(H)`.  If there are no two disjoint edges in `K`, then by (1) and 5.8, it
follows that either `X ∩ V(L(H))` is local (with respect to `L(H)`) or 5.8.2.a holds, and in
either case there is a branch `D` of `H` with an end `d` such that every edge of `X ∩ E(H)`
either is in `E(D)` or is incident with `d`.  In particular, every branch containing an edge of
`X` is incident with `d`, and so `d` meets all edges of `J` in `K`, contrary to (2).  This
proves (3)."*

Two edges of `J` are *disjoint* when they have no end in common (`Tracks.DisjointEdges`,
printed p. 22); for the two edges `uv`, `u'v'` this is the four ends being distinct, which is
the form `[u, v, u', v'].Nodup` used by the `J`-strip system axioms themselves.

**Status: this module is a work item — the theorem below is stated but not yet proved.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85Claim3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT

/-- **Claim (3) of the proof of 8.5** (printed p. 42): *"There are two disjoint edges in `K`"*,
where `K = {uv ∈ E(J) : X ∩ S_uv ≠ ∅}` and `X` is the set of attachments of `F` in `V(S,N)`.

`hclaim1` is claim (1) and `hclaim2` is claim (2). -/
theorem thm85Claim3 {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V) (φ : H.lineGraph ≃g G.induce K'),
          IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' φ)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmajor : ∀ f ∈ F, ¬ MajorForStripSystem G J S N f)
    (hXnotlocal :
      ¬ LocalForStripSystem J S N (attachments G F (stripSystemVertices J S)))
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (hclaim2 : ¬ ∃ v : U, attachments G F (stripSystemVertices J S) ⊆
        ⋃ (u : U) (_ : J.Adj u v), S u v) :
    ∃ u v u' v' : U, J.Adj u v ∧ J.Adj u' v' ∧ [u, v, u', v'].Nodup ∧
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty ∧
      (attachments G F (stripSystemVertices J S) ∩ S u' v').Nonempty := by
  classical
  by_contra hcon
  let X : Set V := attachments G F (stripSystemVertices J S)
  have hnodisjoint : ∀ a b c d : U, J.Adj a b → J.Adj c d → [a, b, c, d].Nodup →
      ¬ ((X ∩ S a b).Nonempty ∧ (X ∩ S c d).Nonempty) := by
    intro a b c d hab hcd hnd hboth
    exact hcon ⟨a, b, c, d, hab, hcd, hnd, hboth.1, hboth.2⟩
  obtain ⟨R, hR, hRsymm, hmeet⟩ :=
    Workspace.ProofLemmas.Thm85RungChoice.exists_rung_family_meeting hSN X
  obtain ⟨n, H, hForms⟩ :=
    Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph
      G hG J hJ S N hSN R hR hRsymm
  obtain ⟨phi⟩ := hForms.2.2
  let K : Set V := ⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b}
  have hFormsK : FormsLineGraph G J S N R H := hForms
  have hphiK : H.lineGraph ≃g G.induce K := phi
  have hKsub : K ⊆ stripSystemVertices J S :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.rungUnion_subset_stripSystemVertices
      G J S N R hR
  have hFK : F ⊆ Kᶜ := fun z hzF hzK => (hFcompl hzF) (hKsub hzK)
  have hclaim := hclaim1 n H R K hphiK rfl hFormsK
  have hnomajor : ∀ y ∈ F, ¬ MajorForLineGraph G H K hphiK y := by
    intro y hy hmajor
    exact hclaim.1 y hy hmajor.2
  let Nc : Fin n → Set V := fun c =>
    {z : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ z = (↑(hphiK ⟨e, he⟩) : V)}
  by_cases hlocal : LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(hphiK ⟨e, he⟩) : V) ∈ attachments G F K}
  · obtain ⟨d, hd⟩ :=
      Workspace.ProofLemmas.Thm85Claim3Analysis.common_end_of_local_choice
        G J hJ S N hSN F R (by simpa [X] using hmeet) H hFormsK hphiK hlocal
    apply hclaim2
    refine ⟨d, Workspace.ProofLemmas.Thm85RungChoice.subset_iUnion_of_common_end
      hSN X ?_ d ?_⟩
    · intro z hz
      exact hz.1
    · simpa [X] using hd
  · obtain ⟨P, p1, p2, hP, hPF, hout⟩ :=
      Workspace.ProofLemmas.Thm85Five8Transported.thm85Five8Transported
        G hG J hJ n H K hFormsK.2.1 hphiK Nc (fun _ => rfl) F hFK hFconn hlocal hnomajor
    rcases hout with hfirst | hbranch
    · obtain ⟨c1, c2, hnb, hc1, hc2, hattach⟩ := hfirst
      apply hnoenl
      exact Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath
        G hG J hJ n H K hFormsK.2 hphiK Nc (fun _ => rfl) P p1 p2 hP
          (fun z hzP => hFK (hPF z hzP)) c1 c2 hnb hc1 hc2 hattach hclaim.2
    · obtain ⟨b1, b2, q, Rline, r1, r2, hb1, hb2, hq, hqfrom, hRline, hRimage,
          hr1, hr2, hcases⟩ := hbranch
      obtain ⟨d, hd⟩ :=
        Workspace.ProofLemmas.Thm85Claim3Closing.common_end_of_branch_outcome
          G J hJ S N hSN F hFmin (by simpa [X] using hnodisjoint) R
            (by simpa [X] using hmeet) H hFormsK hphiK Nc (fun _ => rfl) P p1 p2 hP hPF
            b1 b2 q Rline r1 r2 hb1 hb2 hq hqfrom hRline hRimage hr1 hr2 hcases
      apply hclaim2
      refine ⟨d, Workspace.ProofLemmas.Thm85RungChoice.subset_iUnion_of_common_end
        hSN X ?_ d ?_⟩
      · intro z hz
        exact hz.1
      · simpa [X] using hd

end Workspace.ProofLemmas.Thm85Claim3
