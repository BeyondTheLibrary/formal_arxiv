import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm82RungFamily
import Workspace.ProofLemmas.TwoPrescribedSymmetricRungFamily
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm85RungChoice
import Workspace.ProofLemmas.Thm85LineGraphBridge
import Workspace.ProofLemmas.Thm85Claim2Cases
import Workspace.ProofLemmas.Thm85Claim2Closing
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath

/-!
# 8.5, claim (2)

PAPER (printed p. 42, proof of 8.5):

*"(2) There is no `v ∈ V(J)` such that `X ⊆ ⋃(S_uv : uv ∈ E(J))`.*

*For assume that `v` is such a vertex.  Consequently, for every vertex `w ∈ V(J)` except at
most one, only one strip meets both `N_w` and `X`.  Since `X` is not local, there exists
`x ∈ X ∩ S_uv \ N_v` for some edge `uv` of `J`.  Since `X ⊄ S_uv`, there exists
`x' ∈ X ∩ S_{u'v}` for some edge `u'v` of `J` with `u' ≠ u`.  For `w ∈ V(J)`, `x` belongs to
`N_w` only if `w = u`, and `x'` belongs to `N_w` only if `w ∈ {v, u'}`; and since `x, x'` do
not belong to the same strip it follows that `{x, x'}` is not local with respect to the strip
system.  Make a choice of rungs `R_ij` (`ij ∈ E(J)`) such that `x ∈ V(R_uv)` and
`x' ∈ V(R_{u'v})`, forming `L(H)`.  Then `{x, x'}` is not local with respect to `L(H)`, so by
(1) we can apply 5.8.  Suppose that 5.8.1 holds.  Then there is an appearance `L(H')` in `G`
of some `J`-enlargement `J'`, with `L(H)` an induced subgraph of `L(H')`.  Moreover, if
`J' = K₃,₃` then `J = K₄`, and so `L(H)` is nondegenerate and therefore so is `L(H')`.  Since
`J' ≠ K₄` it follows that `L(H')` is nondegenerate, contrary to hypothesis.  So 5.8.1 does not
hold, and therefore 5.8.2 holds.  Since for every vertex `w ∈ V(J)` except at most one, only
one strip meets both `N_w` and `X`, it follows that 5.8.2.a holds, and there is a branch `D` of
`H` with an end `d` such that `δ_H(d) \ E(D) = (X ∩ E(H)) \ E(D)`.  Since `x` and `x'` are
disjoint edges in `X ∩ E(H)`, they are not both incident with `d`, and so one of them is in
`E(D \ d)`.  The branch containing `x'` does not meet `x`, so `D` is the branch between `u` and
`v`, and `d = v`.  Hence `x'` is incident with `v` in `H`, and `δ_H(v) ⊆ X ∪ E(D)`.
Consequently, for all neighbours `w ≠ u` of `v` in `J`, `X` contains the vertex of `R_vw` that
belongs to `N_v`, and contains no other vertex of `R_vw`.  This restores the symmetry between
`u'` and the other neighbours of `v` different from `u`; and since it holds for all choices of
the rungs `R_vw`, we deduce that `X \ S_uv = N_v \ S_uv`.  The minimality of `F` implies that
there is a path `P` with `V(P) = F`, with ends `p₁, p₂` such that `p₁` is complete to
`N_v \ N_{vu}`, and no other vertex of `P` has any neighbours in `N_v \ N_{vu}`, and `p₂` is
adjacent to `x`, and no other vertex of `P` has any neighbours in `S_uv \ N_v`.  But then we can
add `p₁` to `N_v` and `F` to `S_uv`, contradicting the maximality of `(S,N)`.  This proves
(2)."*

**Status: this module is a work item — the theorem below is stated but not yet proved.**  Its
proof is the printed paragraph above; it consumes claim (1) (via
`Workspace.ProofLemmas.Thm85Claim1`), statement 5.8, the minimality of `F` and the maximality
of the strip system.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT

/-- **Claim (2) of the proof of 8.5** (printed p. 42):
*"There is no `v ∈ V(J)` such that `X ⊆ ⋃(S_uv : uv ∈ E(J))`."*

`X` is the set of attachments of `F` in `V(S,N)`, and the union is over the edges of `J`
incident with `v`.  `hFmin` is the minimality of `F` (printed p. 42, *"We may assume that `F`
is minimal (connected) with this property"*), and `hclaim1` is claim (1). -/
theorem thm85Claim2 {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
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
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H)) :
    ¬ ∃ v : U, attachments G F (stripSystemVertices J S) ⊆
        ⋃ (u : U) (_ : J.Adj u v), S u v := by
  classical
  rintro ⟨v, hXv⟩
  obtain ⟨u, u', x, x', huv, hu'v, huu', hxX, hxS, hxNv, hx'X, hx'S, hx'notS,
      hpair⟩ :=
    Workspace.ProofLemmas.Thm85RungChoice.exists_nonlocal_pair hSN
      (attachments G F (stripSystemVertices J S)) hXnotlocal v hXv
  obtain ⟨Puv, hPuv, hxPuv⟩ := StripSystemBasics.exists_rung hSN huv hxS
  obtain ⟨Pu'v, hPu'v, hx'Pu'v⟩ := StripSystemBasics.exists_rung hSN hu'v hx'S
  have hPvu : IsUVRung G J S N v u Puv.reverse :=
    Workspace.ProofLemmas.Thm82RungFamily.rung_reverse hSN hPuv
  have hPvu' : IsUVRung G J S N v u' Pu'v.reverse :=
    Workspace.ProofLemmas.Thm82RungFamily.rung_reverse hSN hPu'v
  obtain ⟨R, hR, hRsymm, hRvu, hRvu'⟩ :=
    Workspace.ProofLemmas.TwoPrescribedSymmetricRungFamily G J S N hSN
      v u u' huv.symm hu'v.symm huu' Puv.reverse Pu'v.reverse hPvu hPvu'
  have hxR : x ∈ R v u := by
    rw [hRvu, List.mem_reverse]
    exact hxPuv
  have hx'R : x' ∈ R v u' := by
    rw [hRvu', List.mem_reverse]
    exact hx'Pu'v
  obtain ⟨n, H, hForms⟩ :=
    Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph
      G hG J hJ S N hSN R hR hRsymm
  obtain ⟨phi⟩ := hForms.2.2
  let K : Set V := ⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b}
  have hxK : x ∈ K := by
    simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨v, u, huv.symm, hxR⟩
  have hx'K : x' ∈ K := by
    simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨v, u', hu'v.symm, hx'R⟩
  have hFormsK : FormsLineGraph G J S N R H := hForms
  have hphiK : H.lineGraph ≃g G.induce K := phi
  obtain ⟨e, e', he, he', hphie, hphie', hepair⟩ :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.exists_nonlocal_preimage_pair
      G J hJ S N hSN H R hFormsK hphiK v u v u' huv.symm hu'v.symm x x' hxR hx'R hpair
  have heatt : (↑(hphiK ⟨e, he⟩) : V) ∈ attachments G F K := by
    rw [hphie]
    exact ⟨hxK, hxX.2⟩
  have he'att : (↑(hphiK ⟨e', he'⟩) : V) ∈ attachments G F K := by
    rw [hphie']
    exact ⟨hx'K, hx'X.2⟩
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
  · obtain ⟨c1, c2, hnb, hc1, hc2, hattach⟩ := hfirst
    apply hnoenl
    exact Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath
      G hG J hJ n H K hFormsK.2 hphiK Nc
        (fun _ => rfl) Q p1 p2 hQ (fun z hzQ => hFK (hQF z hzQ)) c1 c2 hnb hc1 hc2
        hattach hclaim.2
  · obtain ⟨b1, b2, q, Rline, r1, r2, hb1, hb2, hq, hqfrom, hRline, hRimage,
        hr1, hr2, hcases⟩ := hbranch
    have hcaseA :=
      Workspace.ProofLemmas.Thm85Claim2Cases.branch_outcome_forces_first_case
        G J hJ S N hSN H R hFormsK hphiK Nc (fun _ => rfl) F v hXv Q p1 p2 hQ hQF
        b1 b2 q Rline r1 r2 hb1 hb2 hq hqfrom hr1 hr2 hcases
    have hidentity :=
      Workspace.ProofLemmas.Thm85Claim2Closing.first_case_attachment_identity
        G J hJ S N hSN F v u u' x x' huv hu'v huu' hxX hxS hxNv hx'X hx'S hx'notS
        hXv H R hFormsK hphiK hxR hx'R Nc (fun _ => rfl) Q p1 p2 hQ hQF b1 b2 q Rline
        r1 r2 hb1 hb2 hq hqfrom hRline hRimage hr1 hr2 hcaseA
        hG hnoenl hFcompl hFconn hFmin hclaim1
    exact Workspace.ProofLemmas.Thm85Claim2Closing.attachment_identity_contradicts_maximality
      G J S N hSN hmax F hFcompl hFne hFconn hFmin u v huv x hxX hxS hxNv hidentity hJ

end Workspace.ProofLemmas.Thm85Claim2
