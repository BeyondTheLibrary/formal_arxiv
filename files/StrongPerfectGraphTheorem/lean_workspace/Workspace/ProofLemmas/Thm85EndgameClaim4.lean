import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm85LineGraphBridge
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameClaim6
import Workspace.ProofLemmas.Thm85EndgameBranchEdge
import Workspace.ProofLemmas.Thm85EndgameTraversalCore
import Workspace.ProofLemmas.Thm85EndgamePathEnds
import Workspace.ProofLemmas.Thm85EndgameTraversalUnique

/-!
# 8.5, claim (4): existence of the traversal

PAPER (printed p. 43):

*"(4) For every broad choice of rungs `R_uv` (`uv ∈ E(J)`), there is a unique pair `(i,j)` of
adjacent vertices of `J` such that: … For by (1) we can apply 5.8, and since the choice of
rungs is broad, the minimality of `F` implies that one of 5.8.2.b, 5.8.2.c, 5.8.2.d holds.
Hence there is an edge `ij` as in (4). …"*

The proof runs as follows.

* The choice of rungs is broad, so two vertices of `X` lie in the strips of two disjoint edges
  of `J`; that pair is not local, so neither is the attachment set of `F` in the line graph
  `L(H)` formed by the choice.  Claim (1) says that no member of `F` is major for `L(H)`, so
  5.8 applies.
* Outcome 5.8.1 produces an appearance of a `J`-enlargement, contrary to hypothesis.
* In the remaining outcome, 5.8 supplies a branch of `H`;
  `Thm85EndgameBranchEdge.branch_edge_data` reads it as an edge `ij` of `J`.
* In each of the four subcases the path `P` of 5.8 has two attachments in the strips of two
  edges that are not both inside one strip and not both inside one `N_w`, so the attachment set
  of `V(P)` is not local, and the minimality of `F` gives `V(P) = F`.
* Subcase 5.8.2.a is then excluded: it confines every attachment of `F` to `N_i ∪ S_ij`, so
  every edge of `J` whose selected rung meets `X` has `i` as an end, contradicting broadness.
* The other three subcases give the same three bullets, assembled by
  `Thm85EndgameTraversalCore.traversal_of_unified`.

Uniqueness of the pair is the separate work item
`Thm85EndgameTraversalUnique.traversal_unique`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.Thm85EndgameClaim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-- Two vertices lying in the strips of two disjoint edges of `J` form a non-local pair. -/
theorem pair_not_local {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V}
    {N : U → Set V} (hSN : IsJStripSystem G J S N)
    {a b c d : U} (hab : J.Adj a b) (hcd : J.Adj c d) (hnd : [a, b, c, d].Nodup)
    {x y : V} (hx : x ∈ S a b) (hy : y ∈ S c d) :
    ¬ LocalForStripSystem J S N ({x, y} : Set V) := by
  classical
  have hedge : s(a, b) ≠ s(c, d) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> simp at hnd
  rintro (⟨w, hw⟩ | ⟨u, v, huv, hsub⟩)
  · have hxw : x ∈ N w := hw (by simp)
    have hyw : y ∈ N w := hw (by simp)
    have hwab : w = a ∨ w = b := by
      by_contra hc
      push_neg at hc
      have h0 : x ∈ S a b ∩ N w := ⟨hx, hxw⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN hab hc.1 hc.2] at h0
      exact h0
    have hwcd : w = c ∨ w = d := by
      by_contra hc
      push_neg at hc
      have h0 : y ∈ S c d ∩ N w := ⟨hy, hyw⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN hcd hc.1 hc.2] at h0
      exact h0
    rcases hwab with rfl | rfl <;> rcases hwcd with h | h <;> subst h <;> simp at hnd
  · exact hedge ((StripSystemBasics.edge_eq_of_mem_strips hSN huv hab (hsub (by simp)) hx).symm.trans
      (StripSystemBasics.edge_eq_of_mem_strips hSN huv hcd (hsub (by simp)) hy))

/-- In a 3-connected graph every vertex has a neighbour outside any prescribed pair. -/
theorem exists_adj_ne₂ [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3) (a b c : U) :
    ∃ w : U, J.Adj a w ∧ w ≠ b ∧ w ≠ c := by
  classical
  have h3 : 3 ≤ (J.neighborSet a).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  by_contra hcon
  push_neg at hcon
  have hsub : J.neighborSet a ⊆ ({b, c} : Set U) := by
    intro w hw
    by_cases hb : w = b
    · exact Or.inl hb
    · exact Or.inr (hcon w hw hb)
  have hle : (J.neighborSet a).ncard ≤ ({b, c} : Set U).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have : ({b, c} : Set U).ncard ≤ 2 := by
    refine le_trans (Set.ncard_insert_le _ _) ?_
    simp [Set.ncard_singleton]
  omega


/-- **Claim (4) of the proof of 8.5** (printed p. 43), existence and uniqueness of the
traversal of a broad choice of rungs. -/
theorem claim4 [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ)
    (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hfne : f₁ ≠ fn)
    (hPF : F = {x : V | x ∈ P}) (R : U → U → List V)
    (hBroad : BroadChoice G J S N
      (attachments G F (stripSystemVertices J S)) R) :
    HasUniqueTraversal G J N F f₁ fn R := by
  classical
  obtain ⟨hRchoice, e1, e2, e3, e4, hE1, hE2, hnd4, hx1, hx2⟩ := hBroad
  obtain ⟨x1, hx1X, hx1R⟩ := hx1
  obtain ⟨x2, hx2X, hx2R⟩ := hx2
  have hRfam := hRchoice.1
  have hRsymm := hRchoice.2
  obtain ⟨n, H, hForms⟩ :=
    Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph
      G hG J hJ S N hSN R hRfam hRsymm
  obtain ⟨phi⟩ := hForms.2.2
  let K : Set V := ⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b}
  have hphiK : H.lineGraph ≃g G.induce K := phi
  have hmemK : ∀ (a b : U), J.Adj a b → ∀ z : V, z ∈ R a b → z ∈ K := by
    intro a b hab z hz
    simp only [K, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨a, b, hab, hz⟩
  have hx1K : x1 ∈ K := hmemK e1 e2 hE1 x1 hx1R
  have hx2K : x2 ∈ K := hmemK e3 e4 hE2 x2 hx2R
  have hx1S : x1 ∈ S e1 e2 :=
    StripSystemBasics.rung_subset_strip (hRfam e1 e2 hE1) x1 hx1R
  have hx2S : x2 ∈ S e3 e4 :=
    StripSystemBasics.rung_subset_strip (hRfam e3 e4 hE2) x2 hx2R
  have hpair : ¬ LocalForStripSystem J S N ({x1, x2} : Set V) :=
    pair_not_local hSN hE1 hE2 hnd4 hx1S hx2S
  obtain ⟨ee, ee', hee, hee', hphie, hphie', hepair⟩ :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.exists_nonlocal_preimage_pair
      G J hJ S N hSN H R hForms hphiK e1 e2 e3 e4 hE1 hE2 x1 x2 hx1R hx2R hpair
  have heatt : (↑(hphiK ⟨ee, hee⟩) : V) ∈ attachments G F K := by
    rw [hphie]; exact ⟨hx1K, hx1X.2⟩
  have he'att : (↑(hphiK ⟨ee', hee'⟩) : V) ∈ attachments G F K := by
    rw [hphie']; exact ⟨hx2K, hx2X.2⟩
  have hnotlocal : ¬ LocalForLineGraph H
      {f : Sym2 (Fin n) | ∃ hf : f ∈ H.edgeSet,
        (↑(hphiK ⟨f, hf⟩) : V) ∈ attachments G F K} :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.attachmentEdges_not_local_of_pair
      G H K F hphiK ee ee' hee hee' heatt he'att hepair
  have hKsub : K ⊆ stripSystemVertices J S :=
    Workspace.ProofLemmas.Thm85LineGraphBridge.rungUnion_subset_stripSystemVertices
      G J S N R hRfam
  have hFK : F ⊆ Kᶜ := fun z hzF hzK => (hFcompl hzF) (hKsub hzK)
  have hclaim := hclaim1 n H R K hphiK rfl hForms
  have hnomajor : ∀ y ∈ F, ¬ MajorForLineGraph G H K hphiK y := by
    intro y hy hmajor
    exact hclaim.1 y hy hmajor.2
  let Nc : Fin n → Set V := fun c =>
    {z : V | ∃ (f : Sym2 (Fin n)) (hf : f ∈ H.edgeSet),
      f ∈ incidentEdges H c ∧ z = (↑(hphiK ⟨f, hf⟩) : V)}
  obtain ⟨Q, p1, p2, hQ, hQF, hout⟩ :=
    Workspace.ProofLemmas.Thm85Five8Transported.thm85Five8Transported
      G hG J hJ n H K hForms.2.1 hphiK Nc (fun _ => rfl) F hFK hFconn hnotlocal hnomajor
  rcases hout with hfirst | hbranch
  · exfalso
    obtain ⟨c1, c2, hnb, hc1, hc2, hattach⟩ := hfirst
    exact hnoenl
      (Workspace.ProofLemmas.EnlargementFromNonlocalAttachmentPath.enlargementFromNonlocalAttachmentPath
        G hG J hJ n H K hForms.2 hphiK Nc
          (fun _ => rfl) Q p1 p2 hQ (fun z hzQ => hFK (hQF z hzQ)) c1 c2 hnb hc1 hc2
          hattach hclaim.2)
  obtain ⟨b1, b2, q, Rline, r1, r2, hb1, hb2, hqb, hqfrom, hRlinePath, hRimage,
    hr1, hr2, hcases⟩ := hbranch
  obtain ⟨i, j, hij, hNc1, hNc2, hhead1, hhead2, hRlineEq⟩ :=
    Workspace.ProofLemmas.Thm85EndgameBranchEdge.branch_edge_data
      G J hJ S N hSN H R hForms hRsymm hphiK Nc (fun _ => rfl)
      b1 b2 q Rline r1 r2 hb1 hb2 hqb hqfrom hRimage hr1 hr2
  -- the two distinguished vertices of the branch lie on the rung `R_ij`
  have hr1mem : r1 ∈ Nc b1 ∧ r1 ∈ {x : V | x ∈ Rline} := by
    have : r1 ∈ Nc b1 ∩ {x : V | x ∈ Rline} := by rw [hr1]; rfl
    exact this
  have hr2mem : r2 ∈ Nc b2 ∧ r2 ∈ {x : V | x ∈ Rline} := by
    have : r2 ∈ Nc b2 ∩ {x : V | x ∈ Rline} := by rw [hr2]; rfl
    exact this
  have hr1ij : r1 ∈ R i j := by rw [hRlineEq] at hr1mem; exact hr1mem.2
  have hr2ij : r2 ∈ R i j := by rw [hRlineEq] at hr2mem; exact hr2mem.2
  have hp1F : p1 ∈ F := hQF p1 (List.mem_of_mem_head? hQ.2.1)
  have hp2F : p2 ∈ F := hQF p2 (List.mem_of_getLast? hQ.2.2)
  -- `N_i` meets the rung `R_ij` only in `r₁`
  have huniq1 : ∀ z ∈ R i j, z ∈ N i → z = r1 := by
    intro z hz hzN
    exact Workspace.ProofLemmas.Thm85EndgameTraversalCore.rung_N_unique
      (hRfam i j hij) hz hzN hr1ij (hNc1 hr1mem.1)
  have huniq2 : ∀ z ∈ R i j, z ∈ N j → z = r2 := by
    intro z hz hzN
    exact Workspace.ProofLemmas.Thm85EndgameTraversalCore.rung_N_unique
      (hRfam j i hij.symm) (by rw [hRsymm i j hij, List.mem_reverse]; exact hz) hzN
      (by rw [hRsymm i j hij, List.mem_reverse]; exact hr2ij) (hNc2 hr2mem.1)
  -- a rung at an edge different from `ij` misses `R_ij`
  have hnotij : ∀ (a b : U), J.Adj a b → s(a, b) ≠ s(i, j) → ∀ z : V, z ∈ R a b →
      z ∉ R i j := by
    intro a b hab hne z hz hzij
    exact hne (StripSystemBasics.edge_eq_of_mem_strips hSN hab hij
      (StripSystemBasics.rung_subset_strip (hRfam a b hab) z hz)
      (StripSystemBasics.rung_subset_strip (hRfam i j hij) z hzij))
  -- minimality of `F`, given a non-local pair of attachments of `V(Q)`
  have hQfromPair : ∀ y1 y2 : V, y1 ∈ stripSystemVertices J S → y2 ∈ stripSystemVertices J S →
      (∃ f ∈ ({z : V | z ∈ Q} : Set V), G.Adj y1 f) →
      (∃ f ∈ ({z : V | z ∈ Q} : Set V), G.Adj y2 f) →
      ¬ LocalForStripSystem J S N ({y1, y2} : Set V) → {z : V | z ∈ Q} = F := by
    intro y1 y2 hy1 hy2 ha1 ha2 hnl
    refine hFmin {z : V | z ∈ Q} (fun z hz => hQF z hz)
      (Workspace.ProofLemmas.KiteTailBasics.connectedSet_of_isPathList hQ.1) ?_
    intro hlocal
    have hm1 : y1 ∈ attachments G {z : V | z ∈ Q} (stripSystemVertices J S) := ⟨hy1, ha1⟩
    have hm2 : y2 ∈ attachments G {z : V | z ∈ Q} (stripSystemVertices J S) := ⟨hy2, ha2⟩
    refine hnl ?_
    rcases hlocal with ⟨w, hw⟩ | ⟨u, v, huv, hw⟩
    · exact Or.inl ⟨w, by rintro z (rfl | rfl); exacts [hw hm1, hw hm2]⟩
    · exact Or.inr ⟨u, v, huv, by rintro z (rfl | rfl); exacts [hw hm1, hw hm2]⟩
  -- the four subcases, reduced to two shapes
  have hnr1 : ∀ y : V, y ∉ R i j → y ≠ r1 := by
    intro y hy hc
    rw [hc] at hy
    exact hy hr1ij
  have hnr2 : ∀ y : V, y ∉ R i j → y ≠ r2 := by
    intro y hy hc
    rw [hc] at hy
    exact hy hr2ij
  have hsplit :
      ((∀ x ∈ Nc b1, x ∉ R i j → G.Adj p1 x) ∧ (∀ x ∈ Nc b2, x ∉ R i j → G.Adj p2 x) ∧
        (∀ x ∈ Q, ∀ y ∈ K, y ∉ R i j → G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1) ∨ (x = p2 ∧ y ∈ Nc b2))) ∨
      ((∀ x ∈ Nc b1, x ∉ R i j → G.Adj p1 x) ∧
        (∃ z : V, z ∈ R i j ∧ z ≠ r1 ∧ G.Adj p2 z) ∧
        (∀ x ∈ Q, ∀ y ∈ K, y ≠ r1 → G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1) ∨ (x = p2 ∧ y ∈ R i j))) := by
    rcases hcases with hA | hB | hC | hD
    · refine Or.inr ⟨?_, ?_, ?_⟩
      · intro x hx hxn
        exact hA.1 x ⟨hx, hnr1 x hxn⟩
      · obtain ⟨z, hz, hadj⟩ := hA.2.1
        have hzR : z ∈ R i j := by
          have hz1 : z ∈ {y : V | y ∈ Rline} := hz.1
          rw [hRlineEq] at hz1
          exact hz1
        exact ⟨z, hzR, hz.2, hadj⟩
      · intro x hxQ y hyK hyr hadj
        rcases hA.2.2 x hxQ y hyK hyr hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2.1⟩
        · refine Or.inr ⟨h1, ?_⟩
          have h3 : y ∈ {z : V | z ∈ Rline} := h2.1
          rw [hRlineEq] at h3
          exact h3
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · intro x hx hxn
        exact hB.1 x ⟨hx, hnr1 x hxn⟩
      · intro x hx hxn
        exact hB.2.1 x ⟨hx, hnr2 x hxn⟩
      · intro x hxQ y hyK hyn hadj
        rcases hB.2.2.1 x hxQ y hyK hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2.1⟩
        · exact Or.inr ⟨h1, h2.1⟩
        · exact absurd h2 (hnr1 y hyn)
        · exact absurd h2 (hnr2 y hyn)
    · have hQsingle : ∀ z ∈ Q, z = p1 :=
        Workspace.ProofLemmas.Thm85EndgamePathEnds.eq_of_ends_eq hQ hC.1
      refine Or.inl ⟨?_, ?_, ?_⟩
      · intro x hx hxn
        refine hC.2.1 x ⟨Or.inl hx, ?_⟩
        rintro (hc | hc)
        · exact hnr1 x hxn hc
        · exact hnr2 x hxn hc
      · intro x hx hxn
        rw [← hC.1]
        refine hC.2.1 x ⟨Or.inr hx, ?_⟩
        rintro (hc | hc)
        · exact hnr1 x hxn hc
        · exact hnr2 x hxn hc
      · intro x hxQ y hyK hyn hadj
        have hxp : x = p1 := hQsingle x hxQ
        rw [hxp] at hadj
        rcases hC.2.2.1 y hyK hadj with h | h
        · rcases h with h | h
          · exact Or.inl ⟨hxp, h⟩
          · refine Or.inr ⟨?_, h⟩
            rw [hxp, hC.1]
        · exfalso
          refine hyn ?_
          have h3 : y ∈ {z : V | z ∈ Rline} := h
          rw [hRlineEq] at h3
          exact h3
    · refine Or.inl ⟨?_, ?_, ?_⟩
      · intro x hx hxn
        exact hD.2.1 x ⟨hx, hnr1 x hxn⟩
      · intro x hx hxn
        exact hD.2.2.1 x ⟨hx, hnr2 x hxn⟩
      · intro x hxQ y hyK hyn hadj
        rcases hD.2.2.2.1 x hxQ y hyK (hnr1 y hyn) hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2.1⟩
        · exact Or.inr ⟨h1, h2.1⟩
  -- in both shapes the first end of the path is complete to the `N_i`-ends off `R_ij`
  have hA1 : ∀ x ∈ Nc b1, x ∉ R i j → G.Adj p1 x := by
    rcases hsplit with h | h
    exacts [h.1, h.1]
  -- a neighbour `w ≠ j` of `i` and a neighbour `w' ∉ {i,w}` of `j`
  obtain ⟨w, hiw, hwj⟩ := Workspace.ProofLemmas.Thm85EndgameClaim6.exists_adj_ne hJ i j
  obtain ⟨w', hjw', hw'i, hw'w⟩ := exists_adj_ne₂ hJ j i w
  obtain ⟨s1, hs1R, hs1N, hs1Nc⟩ := hhead1 w hiw
  obtain ⟨s2, hs2R, hs2N, hs2Nc⟩ := hhead2 w' hjw'
  have hiwne : s(i, w) ≠ s(i, j) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hwj h2
    · exact hij.ne h1
  have hjw'ne : s(j, w') ≠ s(i, j) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hij.ne h1.symm
    · exact hw'i h2
  have hs1nij : s1 ∉ R i j := hnotij i w hiw hiwne s1 hs1R
  have hs2nij : s2 ∉ R i j := hnotij j w' hjw' hjw'ne s2 hs2R
  have hs1S : s1 ∈ S i w := StripSystemBasics.rung_subset_strip (hRfam i w hiw) s1 hs1R
  have hs2S : s2 ∈ S j w' := StripSystemBasics.rung_subset_strip (hRfam j w' hjw') s2 hs2R
  have hs1V : s1 ∈ stripSystemVertices J S :=
    StripSystemBasics.strip_subset_vertices hiw hs1S
  have hs2V : s2 ∈ stripSystemVertices J S :=
    StripSystemBasics.strip_subset_vertices hjw' hs2S
  have hp1Q : p1 ∈ ({z : V | z ∈ Q} : Set V) := List.mem_of_mem_head? hQ.2.1
  have hp2Q : p2 ∈ ({z : V | z ∈ Q} : Set V) := List.mem_of_getLast? hQ.2.2
  have hs1adj : G.Adj s1 p1 := (hA1 s1 hs1Nc hs1nij).symm
  rcases hsplit with ⟨hU1, hU2, hU3⟩ | ⟨-, hex, hedgesA⟩
  · -- the three surviving subcases
    have hs2adj : G.Adj s2 p2 := (hU2 s2 hs2Nc hs2nij).symm
    have hnd : [i, w, j, w'].Nodup := by
      have h1 : i ≠ w := hiw.ne
      have h2 : i ≠ j := hij.ne
      have h3 : i ≠ w' := fun h => hw'i h.symm
      have h4 : w ≠ j := hwj
      have h5 : w ≠ w' := fun h => hw'w h.symm
      have h6 : j ≠ w' := hjw'.ne
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or]
      tauto
    have hQeqF : {z : V | z ∈ Q} = F :=
      hQfromPair s1 s2 hs1V hs2V ⟨p1, hp1Q, hs1adj⟩ ⟨p2, hp2Q, hs2adj⟩
        (pair_not_local hSN hiw hjw' hnd hs1S hs2S)
    have hFQ : F = {z : V | z ∈ Q} := hQeqF.symm
    have hU3' : ∀ x ∈ Q, ∀ y ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b}),
        y ∉ R i j → G.Adj x y → (x = p1 ∧ y ∈ Nc b1) ∨ (x = p2 ∧ y ∈ Nc b2) := hU3
    have hPQ : ∀ v : V, v ∈ P ↔ v ∈ Q := by
      intro v
      constructor
      · intro hv
        have hvF : v ∈ F := by
          rw [hPF]
          exact hv
        rw [← hQeqF] at hvF
        exact hvF
      · intro hv
        have hvF : v ∈ F := by
          rw [← hQeqF]
          exact hv
        rw [hPF] at hvF
        exact hvF
    have hends :=
      Workspace.ProofLemmas.Thm85EndgamePathEnds.ends_eq_of_vertex_set_eq hP hQ hPQ
    have htrav : IsTraversal G J N F f₁ fn R i j ∨ IsTraversal G J N F f₁ fn R j i := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [← h1, ← h2]
        exact Workspace.ProofLemmas.Thm85EndgameTraversalCore.traversal_of_unified
          hSN hRfam hFQ hp1F hp2F hij hNc1 hNc2 hhead1 hU1 hU3' hhead2 hU2
      · right
        rw [← h2, ← h1]
        refine Workspace.ProofLemmas.Thm85EndgameTraversalCore.traversal_of_unified
          hSN hRfam hFQ hp2F hp1F hij.symm hNc2 hNc1 hhead2 ?_ ?_ hhead1 ?_
        · intro x hx hxn
          exact hU2 x hx (by rw [hRsymm i j hij, List.mem_reverse] at hxn; exact hxn)
        · intro x hxQ y hyK hyn hadj
          rcases hU3 x hxQ y hyK
            (by rw [hRsymm i j hij, List.mem_reverse] at hyn; exact hyn) hadj with h | h
          · exact Or.inr h
          · exact Or.inl h
        · intro x hx hxn
          exact hU1 x hx (by rw [hRsymm i j hij, List.mem_reverse] at hxn; exact hxn)
    rcases htrav with h | h
    · exact ⟨i, j, h, fun i' j' h' =>
        Workspace.ProofLemmas.Thm85EndgameTraversalUnique.traversal_unique
          G hG J hJ S N hSN F f₁ fn hclaim1 hfne R hRchoice i j i' j' h h'⟩
    · exact ⟨j, i, h, fun i' j' h' =>
        Workspace.ProofLemmas.Thm85EndgameTraversalUnique.traversal_unique
          G hG J hJ S N hSN F f₁ fn hclaim1 hfne R hRchoice j i i' j' h h'⟩
  · -- subcase 5.8.2.a, excluded by broadness
    exfalso
    obtain ⟨z, hzij, hzr1, hzadj⟩ := hex
    have hzS : z ∈ S i j := StripSystemBasics.rung_subset_strip (hRfam i j hij) z hzij
    have hzV : z ∈ stripSystemVertices J S :=
      StripSystemBasics.strip_subset_vertices hij hzS
    have hnl : ¬ LocalForStripSystem J S N ({s1, z} : Set V) := by
      rintro (⟨c, hc⟩ | ⟨u, v, huv, hc⟩)
      · have hs1c : s1 ∈ N c := hc (by simp)
        have hzc : z ∈ N c := hc (by simp)
        have hciw : c = i ∨ c = w := by
          by_contra hcon
          push_neg at hcon
          have h0 : s1 ∈ S i w ∩ N c := ⟨hs1S, hs1c⟩
          rw [StripSystemBasics.strip_inter_N_eq_empty hSN hiw hcon.1 hcon.2] at h0
          exact h0
        have hcij : c = i ∨ c = j := by
          by_contra hcon
          push_neg at hcon
          have h0 : z ∈ S i j ∩ N c := ⟨hzS, hzc⟩
          rw [StripSystemBasics.strip_inter_N_eq_empty hSN hij hcon.1 hcon.2] at h0
          exact h0
        rcases hciw with rfl | rfl
        · exact hzr1 (huniq1 z hzij hzc)
        · rcases hcij with h | h
          · exact hiw.ne h.symm
          · exact hwj h
      · exact hiwne ((StripSystemBasics.edge_eq_of_mem_strips hSN huv hiw
          (hc (by simp)) hs1S).symm.trans
          (StripSystemBasics.edge_eq_of_mem_strips hSN huv hij (hc (by simp)) hzS))
    have hQeqF : {z : V | z ∈ Q} = F :=
      hQfromPair s1 z hs1V hzV ⟨p1, hp1Q, hs1adj⟩ ⟨p2, hp2Q, hzadj.symm⟩ hnl
    -- every attachment of `F` in `K` lies in `N_i ∪ S_ij`
    have hall : ∀ (a b : U), J.Adj a b →
        ∀ y : V, y ∈ R a b → y ∈ attachments G F (stripSystemVertices J S) → i = a ∨ i = b := by
      intro a b hab y hyR hyX
      obtain ⟨-, f, hfF, hadj⟩ := hyX
      have hyS : y ∈ S a b := StripSystemBasics.rung_subset_strip (hRfam a b hab) y hyR
      have hfQ : f ∈ Q := by
        rw [← hQeqF] at hfF
        exact hfF
      have hcase : y ∈ N i ∨ y ∈ S i j := by
        by_cases hyr : y = r1
        · refine Or.inr ?_
          rw [hyr]
          exact StripSystemBasics.rung_subset_strip (hRfam i j hij) r1 hr1ij
        · rcases hedgesA f hfQ y (hmemK a b hab y hyR) hyr hadj.symm with ⟨-, h2⟩ | ⟨-, h2⟩
          · exact Or.inl (hNc1 h2)
          · exact Or.inr (StripSystemBasics.rung_subset_strip (hRfam i j hij) y h2)
      rcases hcase with h | h
      · by_contra hcon
        push_neg at hcon
        have h0 : y ∈ S a b ∩ N i := ⟨hyS, h⟩
        rw [StripSystemBasics.strip_inter_N_eq_empty hSN hab hcon.1 hcon.2] at h0
        exact h0
      · rcases Sym2.eq_iff.mp
          (StripSystemBasics.edge_eq_of_mem_strips hSN hab hij hyS h) with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact Or.inl h1.symm
        · exact Or.inr h2.symm
    have h1 := hall e1 e2 hE1 x1 hx1R hx1X
    have h2 := hall e3 e4 hE2 x2 hx2R hx2X
    rcases h1 with rfl | rfl <;> rcases h2 with h | h <;> subst h <;> simp at hnd4

end Workspace.ProofLemmas.Thm85EndgameClaim4
