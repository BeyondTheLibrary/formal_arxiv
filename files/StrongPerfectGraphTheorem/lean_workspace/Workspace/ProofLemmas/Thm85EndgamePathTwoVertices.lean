import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgamePathEnds
import Workspace.ProofLemmas.Thm85EndgameOptimalChoice
import Workspace.ProofLemmas.Thm85EnlargeStripBySet
import Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesClaim4
import Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesBroad
import Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGap

/-!
# 8.5: the minimal `F` has at least two vertices

PAPER (printed p. 44, inside claim (6) of 8.5):

*"Hence `n ≥ 2`, for if `n = 1` then we can add `f₁` to `N_i`, `N_j` and `S_ij`, contrary to the
maximality of the strip system."*

The printed proof establishes `n ≥ 2` inside claim (6), after claims (4) and (5).  In this
formalization the ordered pair `(i,j)` of claim (4) is only determined once `f₁ ≠ f_n` is known
— exchanging `f₁` and `f_n` exchanges `(i,j)` with `(j,i)` in
`Thm85EndgameNotions.IsTraversal` — so the sentence above has to be available *before* claim
(4) is applied.

## How the proof goes

Suppose `f₁ = f_n`.  The path `f₁ … f_n` then has one vertex, so `F = {f₁}`.

Claim (4) and claim (5) are still available in the weaker, unordered form: a broad choice of
rungs has *some* traversal (`Thm85EndgamePathTwoVerticesClaim4.claim4_exists`), and every
choice of rungs is broad (`Thm85EndgamePathTwoVerticesBroad.every_choice_broad`).  Fix a broad
choice with traversal `(i,j)`, and split on whether every choice of rungs has `ij` as its
traversal edge.

* If it does, then for every edge `uv` and every `uv`-rung `L` there is a choice of rungs that
  takes `L` on `uv` and still has traversal `(i,j)`.  The three bullets of claim (4), read on
  those choices, say exactly that no strip of an edge disjoint from `ij` meets `X`, that every
  attachment of `f₁` outside `S_ij` lies in `N_i ∪ N_j`, and that `f₁` is complete to
  `N_i \ S_ij` and to `N_j \ S_ij`.  That is precisely what
  `Thm85EnlargeStripBySet.thm85EnlargeStripBySet` needs in order to add `f₁` to `N_i`, `N_j`
  and `S_ij`, contradicting the maximality of `(S,N)`.  This is the printed sentence.
* If it does not, two choices of rungs have different traversals, and the closing paragraph of
  the printed proof applies; for `f₁ = f_n` that paragraph is the odd hole
  `f₁-r_hj-R_hj-r_jh-r_ji-f₁`, isolated as the single remaining gap
  `Thm85EndgamePathTwoVerticesGap.n1_different_traversals_absurd`.

## Repaired statement

The theorem as written by the earlier agent had only the hypotheses of `Thm85Endgame` up to
claim (3).  Claim (4) cannot be applied without claim (1) and without the hypothesis that no
enlargement of `J` appears in `G`, and the second branch above needs the `K₄` hypothesis of
8.5, so `hnoenl`, `hK₄` and `hclaim1` have been added; all three are available verbatim at the
only call site, `Thm85Endgame.thm85Endgame`.  See `lean_workspace/REPORT.md`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgamePathTwoVertices

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

/-- **"Hence `n ≥ 2`, for if `n = 1` then we can add `f₁` to `N_i`, `N_j` and `S_ij`, contrary
to the maximality of the strip system"** (printed p. 44).

`F` is the vertex set of the path `f₁ … f_n` of the proof of 8.5, so `n = 1` is exactly
`f₁ = f_n`.  In that case `F = {f₁}`, the attachments of `F` are the neighbours of `f₁` in
`V(S,N)`, and the printed sentence adds `f₁` to `N_i`, `N_j` and `S_ij` for the traversal edge
`ij`, producing a strictly larger `J`-strip system and contradicting `hmax`. -/
theorem path_ends_distinct {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
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
    (hclaim3 : ∃ u v u' v' : U, J.Adj u v ∧ J.Adj u' v' ∧ [u, v, u', v'].Nodup ∧
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty ∧
      (attachments G F (stripSystemVertices J S) ∩ S u' v').Nonempty)
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P}) :
    f₁ ≠ fn := by
  classical
  intro hfeq
  -- ## `n = 1`: the path is the single vertex `f₁`
  have hf₁F : f₁ ∈ F := by
    rw [hPF]; exact List.mem_of_mem_head? hP.2.1
  have hFsingle : F = ({f₁} : Set V) := by
    rw [hPF]
    ext z
    constructor
    · intro hz
      exact Workspace.ProofLemmas.Thm85EndgamePathEnds.eq_of_ends_eq hP hfeq z hz
    · rintro rfl
      rw [← hPF]; exact hf₁F
  have hfnF : fn ∈ F := by rw [← hfeq]; exact hf₁F
  -- ## Claims (4) and (5), in the unordered form
  have hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      ∃ p q : U, IsTraversal G J N F f₁ fn R p q := by
    intro R hBroad
    exact Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesClaim4.claim4_exists
      G hG J hJ S N hSN hnoenl F hFcompl hFconn hFmin hclaim1 P f₁ fn hP hPF R hBroad
  obtain ⟨R₀, hR₀broad⟩ :=
    Workspace.ProofLemmas.Thm85EndgameNotions.exists_broad_choice hSN
      (attachments G F (stripSystemVertices J S)) hclaim3
  have hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R :=
    Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesBroad.every_choice_broad
      G J hJ S N hSN F f₁ fn hf₁F hfnF ⟨R₀, hR₀broad⟩ hclaim4
  obtain ⟨i, j, htrav₀⟩ := hclaim4 R₀ hR₀broad
  have hij : J.Adj i j := htrav₀.1
  -- with `f₁ = f_n` a traversal may be read in either direction
  have hswap : ∀ (R : U → U → List V) (p q : U),
      IsTraversal G J N F f₁ fn R p q → IsTraversal G J N F f₁ fn R q p := by
    intro R p q h
    refine ⟨h.1.symm, ?_, ?_, ?_⟩
    · intro w hw hqw
      rw [hfeq]
      exact h.2.2.1 w hw hqw
    · intro w hw hpw
      rw [← hfeq]
      exact h.2.1 w hw hpw
    · intro u v huv hnd2
      refine h.2.2.2 u v huv ?_
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or] at hnd2 ⊢
      tauto
  by_cases hsame : ∀ R : U → U → List V, RungChoice G J S N R →
      ∀ p q : U, IsTraversal G J N F f₁ fn R p q → s(p, q) = s(i, j)
  · -- ## Every choice has traversal edge `ij`: enlarge the strip system
    -- a choice of rungs taking a prescribed rung on one edge, with traversal `(i,j)`
    have hkey : ∀ (u v : U), J.Adj u v → ∀ L : List V, IsUVRung G J S N u v L →
        ∃ R₂ : U → U → List V, R₂ u v = L ∧ IsTraversal G J N F f₁ fn R₂ i j := by
      intro u v huv L hL
      obtain ⟨R₂, hR₂, hR₂uv, -⟩ :=
        Workspace.ProofLemmas.Thm85EndgameOptimalChoice.exists_rung_choice_replacing
          hSN R₀ hR₀broad.1 huv hL
      obtain ⟨p, q, htrav₂⟩ := hclaim4 R₂ (hclaim5 R₂ hR₂)
      have hpq := hsame R₂ hR₂ p q htrav₂
      rcases Sym2.eq_iff.mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨R₂, hR₂uv, htrav₂⟩
      · exact ⟨R₂, hR₂uv, hswap R₂ _ _ htrav₂⟩
    -- (A) no strip of an edge disjoint from `ij` has a neighbour of `f₁`
    have hA : ∀ (u v : U), J.Adj u v → [u, v, i, j].Nodup → ∀ y ∈ S u v, ¬ G.Adj y f₁ := by
      intro u v huv hnd y hy hadj
      obtain ⟨L, hL, hyL⟩ := StripSystemBasics.exists_rung hSN huv hy
      obtain ⟨R₂, hR₂uv, htrav₂⟩ := hkey u v huv L hL
      refine htrav₂.2.2.2 u v huv hnd y ?_ f₁ hf₁F hadj
      show y ∈ R₂ u v
      rw [hR₂uv]; exact hyL
    -- (B) an attachment on a strip at `i` other than `S_ij` lies in `N_i`
    have hB : ∀ w : U, w ≠ j → J.Adj i w → ∀ y ∈ S i w, G.Adj y f₁ → y ∈ N i := by
      intro w hw hiw y hy hadj
      obtain ⟨L, hL, hyL⟩ := StripSystemBasics.exists_rung hSN hiw hy
      obtain ⟨R₂, hR₂uv, htrav₂⟩ := hkey i w hiw L hL
      obtain ⟨r, -, hrN, hu⟩ := htrav₂.2.1 w hw hiw
      have hyR : y ∈ {x : V | x ∈ R₂ i w} := by
        show y ∈ R₂ i w
        rw [hR₂uv]; exact hyL
      have hyr : y = r := (hu.2.2.2 y hyR f₁ hf₁F hadj).1
      rw [hyr]; exact hrN
    -- (C) the same at `j`
    have hC : ∀ w : U, w ≠ i → J.Adj j w → ∀ y ∈ S j w, G.Adj y f₁ → y ∈ N j := by
      intro w hw hjw y hy hadj
      obtain ⟨L, hL, hyL⟩ := StripSystemBasics.exists_rung hSN hjw hy
      obtain ⟨R₂, hR₂uv, htrav₂⟩ := hkey j w hjw L hL
      obtain ⟨r, -, hrN, hu⟩ := htrav₂.2.2.1 w hw hjw
      have hyR : y ∈ {x : V | x ∈ R₂ j w} := by
        show y ∈ R₂ j w
        rw [hR₂uv]; exact hyL
      have hyr : y = r := (hu.2.2.2 y hyR fn hfnF (by rw [← hfeq]; exact hadj)).1
      rw [hyr]; exact hrN
    -- (D) `f₁` is complete to `N_i \ S_ij`
    have hD : ∀ w : U, w ≠ j → J.Adj i w → ∀ y ∈ N i ∩ S i w, G.Adj f₁ y := by
      intro w hw hiw y hy
      obtain ⟨L, hL, hyL⟩ := StripSystemBasics.exists_rung hSN hiw hy.2
      obtain ⟨R₂, hR₂uv, htrav₂⟩ := hkey i w hiw L hL
      obtain ⟨r, hrR, hrN, hu⟩ := htrav₂.2.1 w hw hiw
      have hrL : r ∈ L := by rw [← hR₂uv]; exact hrR
      obtain ⟨-, s, t, -, -, hsN, -⟩ := hL
      have h1 : y = s := (hsN y hyL).mp hy.1
      have h2 : r = s := (hsN r hrL).mp hrN
      have hyr : y = r := by rw [h1, h2]
      rw [hyr]
      exact hu.2.2.1.symm
    -- (E) the same at `j`
    have hE : ∀ w : U, w ≠ i → J.Adj j w → ∀ y ∈ N j ∩ S j w, G.Adj f₁ y := by
      intro w hw hjw y hy
      obtain ⟨L, hL, hyL⟩ := StripSystemBasics.exists_rung hSN hjw hy.2
      obtain ⟨R₂, hR₂uv, htrav₂⟩ := hkey j w hjw L hL
      obtain ⟨r, hrR, hrN, hu⟩ := htrav₂.2.2.1 w hw hjw
      have hrL : r ∈ L := by rw [← hR₂uv]; exact hrR
      obtain ⟨-, s, t, -, -, hsN, -⟩ := hL
      have h1 : y = s := (hsN y hyL).mp hy.1
      have h2 : r = s := (hsN r hrL).mp hrN
      have hyr : y = r := by rw [h1, h2]
      rw [hyr, hfeq]
      exact hu.2.2.1.symm
    -- ## The enlarged strip system
    have hFdisj : Disjoint F (stripSystemVertices J S) :=
      Set.disjoint_left.mpr fun z hz hz' => (hFcompl hz) hz'
    have hfmem : ∀ f : V, f ∈ F → f = f₁ := by
      intro f hf; rw [hFsingle] at hf; exact hf
    refine Workspace.ProofLemmas.Thm85EnlargeStripBySet.thm85EnlargeStripBySet
      G J S N hSN hmax i j hij F hFne hFdisj F F subset_rfl subset_rfl
      (fun a b => {z : V | z ∈ S a b ∨ (s(a, b) = s(i, j) ∧ z ∈ F)})
      (fun a => {z : V | z ∈ N a ∨ ((a = i ∨ a = j) ∧ z ∈ F)})
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · -- `S'_ij = S_ij ∪ F`
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union, true_and]
    · -- `S'_ji = S_ij ∪ F`
      have hs : S j i = S i j := (StripSystemBasics.strip_symm hSN hij).symm
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union, Sym2.eq_swap, true_and, hs]
    · -- every other strip is unchanged
      intro x y hxy hne
      ext z
      simp only [Set.mem_setOf_eq, hne, false_and, or_false]
    · -- `N'_i = N_i ∪ F`
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union, true_or, true_and]
    · -- `N'_j = N_j ∪ F`
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union, or_true, true_and]
    · -- every other neighbourhood is unchanged
      intro w hwi hwj
      ext z
      simp only [Set.mem_setOf_eq, hwi, hwj, or_self, false_and, or_false]
    · -- the attachments of `f₁` outside `S_ij` lie in `N_i ∪ N_j`
      intro f hfF w x hwx hne y hyS hadj
      have hfe : f = f₁ := hfmem f hfF
      subst hfe
      have hadj' : G.Adj y f := hadj.symm
      by_cases hwi : w = i
      · subst hwi
        have hxj : x ≠ j := by rintro rfl; exact hne rfl
        exact Or.inl ⟨hfF, hB x hxj hwx y hyS hadj'⟩
      by_cases hwj : w = j
      · subst hwj
        have hxi : x ≠ i := by rintro rfl; exact hne Sym2.eq_swap
        exact Or.inr ⟨hfF, hC x hxi hwx y hyS hadj'⟩
      by_cases hxi : x = i
      · subst hxi
        rw [StripSystemBasics.strip_symm hSN hwx] at hyS
        exact Or.inl ⟨hfF, hB w hwj hwx.symm y hyS hadj'⟩
      by_cases hxj : x = j
      · subst hxj
        rw [StripSystemBasics.strip_symm hSN hwx] at hyS
        exact Or.inr ⟨hfF, hC w hwi hwx.symm y hyS hadj'⟩
      · exfalso
        have hnd : [w, x, i, j].Nodup := by
          have hwx' : w ≠ x := hwx.ne
          have hijne : i ≠ j := hij.ne
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or]
          tauto
        exact hA w x hwx hnd y hyS hadj'
    · -- `f₁` is complete to `N_i ∩ S_iw` for `w ≠ j`
      intro w hiw hwj p hp y hy
      have hpe : p = f₁ := hfmem p hp
      subst hpe
      exact hD w hwj hiw y hy
    · -- `f₁` is complete to `N_j ∩ S_jw` for `w ≠ i`
      intro w hjw hwi p hp y hy
      have hpe : p = f₁ := hfmem p hp
      subst hpe
      exact hE w hwi hjw y hy
    · -- every vertex of `S_ij ∪ F` is on a rung of the enlarged system
      -- old rungs stay rungs
      have hlift : ∀ L : List V, IsUVRung G J S N i j L →
          IsUVRung G J
            (fun a b => {z : V | z ∈ S a b ∨ (s(a, b) = s(i, j) ∧ z ∈ F)})
            (fun a => {z : V | z ∈ N a ∨ ((a = i ∨ a = j) ∧ z ∈ F)}) i j L := by
        rintro L ⟨-, s, t, hpath, hsub, hsN, htN⟩
        have hnotF : ∀ z ∈ L, z ∉ F := by
          intro z hz hzF
          exact (hFcompl hzF) (StripSystemBasics.strip_subset_vertices hij (hsub z hz))
        refine ⟨hij, s, t, hpath, ?_, ?_, ?_⟩
        · intro z hz
          exact Or.inl (hsub z hz)
        · intro z hz
          constructor
          · rintro (h | ⟨-, h⟩)
            · exact (hsN z hz).mp h
            · exact absurd h (hnotF z hz)
          · intro h
            exact Or.inl ((hsN z hz).mpr h)
        · intro z hz
          constructor
          · rintro (h | ⟨-, h⟩)
            · exact (htN z hz).mp h
            · exact absurd h (hnotF z hz)
          · intro h
            exact Or.inl ((htN z hz).mpr h)
      rintro x (hx | hx)
      · obtain ⟨L, hL, hxL⟩ := StripSystemBasics.exists_rung hSN hij hx
        exact ⟨L, hlift L hL, hxL⟩
      · have hxe : x = f₁ := hfmem x hx
        subst hxe
        refine ⟨[x], ⟨hij, x, x, ⟨PathBasics.isPathList_singleton G x, rfl, rfl⟩, ?_, ?_, ?_⟩,
          List.mem_singleton_self x⟩
        · intro z hz
          rw [List.mem_singleton] at hz
          subst hz
          exact Or.inr ⟨rfl, hx⟩
        · intro z hz
          rw [List.mem_singleton] at hz
          subst hz
          exact ⟨fun _ => rfl, fun _ => Or.inr ⟨Or.inl rfl, hx⟩⟩
        · intro z hz
          rw [List.mem_singleton] at hz
          subst hz
          exact ⟨fun _ => rfl, fun _ => Or.inr ⟨Or.inr rfl, hx⟩⟩
  · -- ## Two choices with different traversals: the closing paragraph of 8.5
    push_neg at hsame
    obtain ⟨R, hR, p, q, htrav, hne⟩ := hsame
    exact Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGap.n1_different_traversals_absurd
      G hG J hJ S N hSN hK₄ F hFcompl hFmin hclaim1 P f₁ fn hP hPF hfeq hclaim4 hclaim5
      ⟨R₀, R, i, j, p, q, hR₀broad.1, hR, htrav₀, htrav, Ne.symm hne⟩

end Workspace.ProofLemmas.Thm85EndgamePathTwoVertices
