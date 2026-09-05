import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm85RungChoice
import Workspace.ProofLemmas.Thm85Claim2PerChoice
import Workspace.ProofLemmas.Thm85Claim2AllChoices
import Workspace.ProofLemmas.Thm85Claim2Maximality

/-!
# 8.5, claim (2): the remaining first-case reconstruction

These two lemmas isolate the two sentence groups that remain after 5.8.2 has been reduced to
its first subcase.  They are kept separate so the graph/branch identification and the final
maximal-strip enlargement can be proved independently.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85Claim2Closing

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT

/-- PAPER (proof of 8.5, claim (2), printed p. 42):

*"The branch containing `x'` does not meet `x`, so `D` is the branch between `u` and `v`, and
`d=v`. Hence `x'` is incident with `v` in `H`, and `delta_H(v) ⊆ X ∪ E(D)`. Consequently,
for all neighbours `w ≠ u` of `v` in `J`, `X` contains the vertex of `R_vw` that belongs to
`N_v`, and contains no other vertex of `R_vw`. This restores the symmetry between `u'` and the
other neighbours of `v` different from `u`; and since it holds for all choices of the rungs
`R_vw`, we deduce that `X \ S_uv = N_v \ S_uv`."* -/
theorem first_case_attachment_identity
    {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (v u u' : U) (x x' : V)
    (huv : J.Adj u v) (hu'v : J.Adj u' v) (huu' : u ≠ u')
    (hxX : x ∈ attachments G F (stripSystemVertices J S))
    (hxS : x ∈ S u v) (hxNv : x ∉ N v)
    (hx'X : x' ∈ attachments G F (stripSystemVertices J S))
    (hx'S : x' ∈ S u' v) (hx'notS : x' ∉ S u v)
    (hXv : attachments G F (stripSystemVertices J S) ⊆
      ⋃ (a : U) (_ : J.Adj a v), S a v)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}))
    (hxR : x ∈ Rchoice v u) (hx'R : x' ∈ Rchoice v u')
    (Nc : W → Set V)
    (hNc : ∀ c : W, Nc c =
      {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ z = (↑(phi ⟨e, he⟩) : V)})
    (P : List V) (p1 p2 : V) (hP : IsPathFrom G P p1 p2) (hPF : ∀ z ∈ P, z ∈ F)
    (b1 b2 : W) (q : List W) (Rline : List V) (r1 r2 : V)
    (hb1 : b1 ∈ branchVertices H) (hb2 : b2 ∈ branchVertices H)
    (hq : IsBranch H q) (hqfrom : IsTrackFrom H q b1 b2)
    (hRline : IsPathList G Rline)
    (hRimage : {z : V | z ∈ Rline} =
      {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ z = (↑(phi ⟨e, he⟩) : V)})
    (hr1 : Nc b1 ∩ {z : V | z ∈ Rline} = {r1})
    (hr2 : Nc b2 ∩ {z : V | z ∈ Rline} = {r2})
    (hfirst :
      (∀ z ∈ Nc b1 \ {r1}, G.Adj p1 z) ∧
      (∃ z ∈ {y : V | y ∈ Rline} \ {r1}, G.Adj p2 z) ∧
      (∀ z ∈ P, ∀ y ∈
        (⋃ (a : U) (b : U) (_ : J.Adj a b), {t : V | t ∈ Rchoice a b}),
        y ≠ r1 → G.Adj z y →
        (z = p1 ∧ y ∈ Nc b1 \ {r1}) ∨
        (z = p2 ∧ y ∈ {t : V | t ∈ Rline} \ {r1})) )
    -- REPAIRED STATEMENT (see `REPORT.md`): the printed proof runs the whole 5.8 argument
    -- again for every choice of rungs, so the ambient hypotheses of 8.5 that make that
    -- argument available are needed here as well.
    (hG : Berge G)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
        K = ⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ R a b} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H)) :
    attachments G F (stripSystemVertices J S) \ S u v = N v \ S u v := by
  classical
  -- Two vertices of different strips at `v`, one of which is outside `N_v`, are not local.
  have hstripsep : ∀ c d : U, J.Adj v c → J.Adj v d → c ≠ d → ∀ y : V,
      y ∈ S v c → y ∉ S v d := by
    intro c d hvc hvd hcd y hyc hyd
    rcases Sym2.eq_iff.mp
      (StripSystemBasics.edge_eq_of_mem_strips hSN hvc hvd hyc hyd) with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hcd h2
    · exact hvd.ne h1
  have hnonlocal : ∀ (a : U) (z : V), J.Adj v a → a ≠ u → z ∈ S v a →
      ¬ LocalForStripSystem J S N ({x, z} : Set V) := by
    intro a z hva hau hzS
    have hxS' : x ∈ S v u := by rw [← StripSystemBasics.strip_symm hSN huv]; exact hxS
    rintro (⟨w, hw⟩ | ⟨c, d, hcd, hsub⟩)
    · have hxw : x ∈ N w := hw (by simp)
      have hzw : z ∈ N w := hw (by simp)
      have hwu : w = u := by
        by_contra hc
        have hwv : w ≠ v := by rintro rfl; exact hxNv hxw
        have h0 : x ∈ S u v ∩ N w := ⟨hxS, hxw⟩
        rw [StripSystemBasics.strip_inter_N_eq_empty hSN huv hc hwv] at h0
        exact h0
      have hwv : w ≠ v := by rw [hwu]; exact huv.ne
      have hwa : w ≠ a := by rw [hwu]; exact Ne.symm hau
      have h0 : z ∈ S v a ∩ N w := ⟨hzS, hzw⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN hva hwv hwa] at h0
      exact h0
    · have h1 : s(c, d) = s(v, u) :=
        StripSystemBasics.edge_eq_of_mem_strips hSN hcd huv.symm (hsub (by simp)) hxS'
      have h2 : s(c, d) = s(v, a) :=
        StripSystemBasics.edge_eq_of_mem_strips hSN hcd hva (hsub (by simp)) hzS
      rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨-, h4⟩ | ⟨h3, -⟩
      · exact hau h4.symm
      · exact hva.ne h3
  -- What the given choice of rungs yields.
  obtain ⟨u0, hu0adj, hu0prop⟩ :=
    Workspace.ProofLemmas.Thm85Claim2PerChoice.per_choice_attachments_at_v
      G J hJ S N hSN F hFmin v hXv H Rchoice hForms phi Nc hNc P p1 p2 hP hPF
      b1 b2 q Rline r1 r2 hb1 hb2 hq hqfrom hRimage hr1 hr2 hfirst
  have hu0u : u0 = u := by
    by_contra hne
    exact hxNv ((hu0prop u huv.symm (Ne.symm hne) x hxR).mp hxX)
  subst hu0u
  -- The same conclusion for the strip of every neighbour of `v` other than `u`.
  have hkey : ∀ (a : U) (z : V), J.Adj v a → a ≠ u0 → z ∈ S v a →
      (z ∈ attachments G F (stripSystemVertices J S) ↔ z ∈ N v) := by
    intro a z hva hau hzS
    obtain ⟨b, hbmem, hbu, hba⟩ : ∃ b ∈ J.neighborSet v, b ≠ u0 ∧ b ≠ a := by
      by_contra hcon
      push_neg at hcon
      have hsub : J.neighborSet v ⊆ ({u0, a} : Set U) := by
        intro y hy
        by_cases hyu : y = u0
        · exact Or.inl hyu
        · exact Or.inr (hcon y hy hyu)
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 : ({u0, a} : Set U).ncard ≤ 2 := by
        have := Set.ncard_insert_le u0 ({a} : Set U)
        simpa using this
      have h3 := SubdivisionCounting.three_le_degree_of_three_connected J hJ v
      omega
    have hvb : J.Adj v b := hbmem
    -- the end of the `vb`-rung of the given choice is an attachment lying in `N_v`
    obtain ⟨-, sb, tb, hpathb, hsubb, hsb, -⟩ := hForms.1 v b hvb
    have hsbR : sb ∈ Rchoice v b := List.mem_of_mem_head? hpathb.2.1
    have hsbN : sb ∈ N v := (hsb sb hsbR).mpr rfl
    have hsbS : sb ∈ S v b := hsubb sb hsbR
    have hsbX : sb ∈ attachments G F (stripSystemVertices J S) :=
      (hu0prop b hvb hbu sb hsbR).mpr hsbN
    -- a choice of rungs carrying `x`, `sb` and `z`
    obtain ⟨R', hR', hR'symm, hmeet⟩ :=
      Workspace.ProofLemmas.Thm85RungChoice.exists_rung_family_meeting hSN
        ({x, sb, z} : Set V)
    have hxS' : x ∈ S v u0 := by rw [← StripSystemBasics.strip_symm hSN huv]; exact hxS
    have hgetin : ∀ (c : U) (y : V), J.Adj v c → y ∈ ({x, sb, z} : Set V) → y ∈ S v c →
        (∀ y' ∈ ({x, sb, z} : Set V), y' ∈ S v c → y' = y) → y ∈ R' v c := by
      intro c y hvc hyD hyS huniq
      obtain ⟨w, hwD, hwR⟩ := hmeet v c hvc ⟨y, hyD, hyS⟩
      have hwS : w ∈ S v c := StripSystemBasics.rung_subset_strip (hR' v c hvc) w hwR
      rwa [huniq w hwD hwS] at hwR
    have hxR' : x ∈ R' v u0 := by
      refine hgetin u0 x huv.symm (by simp) hxS' ?_
      rintro y' (rfl | rfl | rfl) hy'
      · rfl
      · exact absurd hy' (hstripsep b u0 hvb huv.symm hbu y' hsbS)
      · exact absurd hy' (hstripsep a u0 hva huv.symm hau y' hzS)
    have hsbR' : sb ∈ R' v b := by
      refine hgetin b sb hvb (by simp) hsbS ?_
      rintro y' (rfl | rfl | rfl) hy'
      · exact absurd hy' (hstripsep u0 b huv.symm hvb (Ne.symm hbu) y' hxS')
      · rfl
      · exact absurd hy' (hstripsep a b hva hvb (Ne.symm hba) y' hzS)
    have hzR' : z ∈ R' v a := by
      refine hgetin a z hva (by simp) hzS ?_
      rintro y' (rfl | rfl | rfl) hy'
      · exact absurd hy' (hstripsep u0 a huv.symm hva (Ne.symm hau) y' hxS')
      · exact absurd hy' (hstripsep b a hvb hva hba y' hsbS)
      · rfl
    obtain ⟨u1, hu1adj, hu1prop⟩ :=
      Workspace.ProofLemmas.Thm85Claim2AllChoices.allChoices
        G hG J hJ S N hSN hnoenl F hFcompl hFconn hFmin hclaim1 v hXv R' hR' hR'symm
        x sb u0 b huv.symm hvb hxX hsbX hxR' hsbR' (hnonlocal b sb hvb hbu hsbS)
    have hu1u : u1 = u0 := by
      by_contra hne
      exact hxNv ((hu1prop u0 huv.symm (Ne.symm hne) x hxR').mp hxX)
    subst hu1u
    exact hu1prop a hva hau z hzR'
  -- Assembling the two inclusions.
  ext z
  simp only [Set.mem_diff]
  constructor
  · rintro ⟨hzX, hzS⟩
    refine ⟨?_, hzS⟩
    have hzu := hXv hzX
    simp only [Set.mem_iUnion] at hzu
    obtain ⟨a, hav, hzSa⟩ := hzu
    have hzSa' : z ∈ S v a := by rw [← StripSystemBasics.strip_symm hSN hav]; exact hzSa
    have hau : a ≠ u0 := by
      rintro rfl
      exact hzS (by rw [StripSystemBasics.strip_symm hSN huv]; exact hzSa')
    exact (hkey a z hav.symm hau hzSa').mp hzX
  · rintro ⟨hzN, hzS⟩
    refine ⟨?_, hzS⟩
    have hzu := StripSystemBasics.N_subset_iUnion hSN v hzN
    simp only [Set.mem_iUnion] at hzu
    obtain ⟨a, hva, hzSa⟩ := hzu
    have hau : a ≠ u0 := by
      rintro rfl
      exact hzS (by rw [StripSystemBasics.strip_symm hSN huv]; exact hzSa)
    exact (hkey a z hva hau hzSa).mpr hzN

/-- PAPER (proof of 8.5, claim (2), printed p. 42):

*"The minimality of `F` implies that there is a path `P` with `V(P)=F`, with ends `p1,p2`
such that `p1` is complete to `N_v \ N_vu`, and no other vertex of `P` has any neighbours in
`N_v \ N_vu`, and `p2` is adjacent to `x`, and no other vertex of `P` has any neighbours in
`S_uv \ N_v`. But then we can add `p1` to `N_v` and `F` to `S_uv`, contradicting the
maximality of `(S,N)`."* -/
theorem attachment_identity_contradicts_maximality
    {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmin : ∀ F1 : Set V, F1 ⊆ F → ConnectedSet G F1 →
      ¬ LocalForStripSystem J S N (attachments G F1 (stripSystemVertices J S)) → F1 = F)
    (u v : U) (huv : J.Adj u v) (x : V)
    (hxX : x ∈ attachments G F (stripSystemVertices J S))
    (hxS : x ∈ S u v) (hxNv : x ∉ N v)
    (hidentity : attachments G F (stripSystemVertices J S) \ S u v = N v \ S u v)
    -- REPAIRED STATEMENT (see `REPORT.md`): without `J` being 3-connected the vertex `v`
    -- may have no neighbour other than `u`, and then `N_v \ S_uv = ∅`, so the enlargement of
    -- the printed proof does not exist.
    (hJ : IsKConnected J 3) :
    False :=
  Workspace.ProofLemmas.Thm85Claim2Maximality.contradiction_of_identity
    G J hJ S N hSN hmax F hFcompl hFne hFconn hFmin u v huv x hxX hxS hxNv hidentity

end Workspace.ProofLemmas.Thm85Claim2Closing
