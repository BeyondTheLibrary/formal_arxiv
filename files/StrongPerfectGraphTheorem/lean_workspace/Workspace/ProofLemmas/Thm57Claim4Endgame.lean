import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.TrackGlueAtCommonEndpoint
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.Thm57EndgameEdgeDeletion
import Workspace.ProofLemmas.Thm57Claim4Basics
import Workspace.ProofLemmas.Thm57Claim4Config
import Workspace.ProofLemmas.Thm57Claim4Component
import Workspace.ProofLemmas.Thm57Claim4EndgameBasics
import Workspace.ProofLemmas.Thm57Claim4EndgameInside
import Workspace.ProofLemmas.Thm57Claim4EndgameOutside

/-!
# 5.7 (4): the last paragraph of the printed proof

PAPER (printed pp. 24–25), continuing from the configuration `a₁b₃, b₂a₃, a₃b₃ ∈ E(K)` with no
further edge of `K` at `a₃` or `b₃`:

> *"Let the tracks in `A` corresponding to `a₁b₃, b₂a₃, a₃b₃ ∈ E(K)` be `P₁, P₂, P₃`
> respectively.  Since `P₃` joins the adjacent vertices `a₃, b₃` and does not use the edge
> `x₃`, it follows that `P₃` has nonempty interior.  Choose a maximal connected subgraph `S`
> of `A` including the interior of `P₃` and not containing either of `a₃, b₃`.  Since there
> are no more edges of `K` incident with `a₃` or `b₃`, it follows that none of `a₁, b₁, a₂,
> b₂` is in `V(S)`, and therefore `S` is vertex-disjoint from `P₁` and `P₂` as well.
> Consequently the only edges of `A` between `V(S) ∪ {a₃, b₃}` and the remainder of `H` are
> incident with `a₃` or `b₃`.  Since `H` is cyclically 3-connected and `a₃, b₃` are adjacent,
> it follows that `H \ {a₃, b₃}` is connected, and therefore there is an edge `sv` of `H` such
> that `s ∈ V(S)` and `v ∈ V(H) \ (V(S) ∪ {a₃, b₃})`.  Since `S` is maximal it follows that
> `sv ∉ E(A)`; and since `A` is maximal, it follows that `sv ∈ X`; and from the symmetry we may
> assume `v ∉ {a₁, b₁}`.  Choose a minimal track in `S` between `s` and the interior of `P₃`;
> then it can be extended via a subpath of `P₃` and via `sv` to become a track `P₄` in `H`, of
> length `≥ 2`, from `v` to `b₃`, using none of `a₁, b₁, a₃`, and with only its first edge in
> `X`.  But then the tracks `b₁-a₁-P₁-b₃`, `P₄`, and the one-edge track made by `x₃`, violate
> (3)."*

Everything before this paragraph is proved: `Thm57Claim4Core.endpointCleanConnection_different_color`
is the colour step, `Thm57Claim4NoDoubleForeign.no_double_foreign` is *"`a₃` is not adjacent in
`K` to both `b₁` and `b₂`, and five similar statements"*, and
`Thm57Claim4Component.exists_config` is *"we may assume that `a₁b₃, b₂a₃, a₃b₃ ∈ E(K)`"*
together with the two hypotheses `hak`, `hbk` below, which say *"there are no more edges of `K`
incident with `a₃` or `b₃`"*.  The statement below is exactly the quoted paragraph, and it is
the only remaining gap of 5.7 (4).

Here `k` plays the role of the index `3`, `i` the role of `1` and `j` the role of `2`; the
paper's symmetry *"from the symmetry we may assume `v ∉ {a₁, b₁}`"* is the symmetry that
exchanges `a` with `b` and `i` with `j`, under which every hypothesis below is preserved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm57Claim4Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Config
open Workspace.ProofLemmas.Thm57Claim4Component
open Workspace.ProofLemmas.Thm57Claim4Basics
open Workspace.ProofLemmas.Thm57Claim4EndgameBasics
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **GAP LEMMA.**  The final paragraph of the printed proof of 5.7 (4), quoted in full in the
module docstring above.  `A` is a *maximal* connected subgraph of `H \ X` (`hmaximal`), the
three marked edges `x i, x j, x k` are pairwise disjoint edges of `H` in `X`, with ends `a`
and `b` as in `hs`, and `K` has the edges `a k b k`, `a k b j`, `a i b k` and no other edge at
`a k` or at `b k`.  The conclusion is the contradiction with claim (3) that the paragraph
constructs. -/
theorem endgame
    (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W))
    (A : Set W) (x : Fin 3 → Sym2 W) (a b : Fin 3 → W)
    (hconn : ConnectedSet (H.deleteEdges X) A)
    (hmaximal : ∀ D : Set W, A ⊆ D → ConnectedSet (H.deleteEdges X) D → D = A)
    (hxX : ∀ i, x i ∈ X) (hxE : ∀ i, x i ∈ H.edgeSet)
    (hs : Setup H X A x a b)
    (hclaim3 :
      ¬ ∃ (c a₁ a₂ a₃ : W) (P₁ P₂ P₃ : List W)
          (_h₁ : 2 ≤ P₁.length) (_h₂ : 2 ≤ P₂.length) (_h₃ : 2 ≤ P₃.length),
        IsTrackFrom H P₁ c a₁ ∧ IsTrackFrom H P₂ c a₂ ∧ IsTrackFrom H P₃ c a₃ ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₂ → v = c) ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₃ → v = c) ∧
        (∀ v : W, v ∈ P₂ → v ∈ P₃ → v = c) ∧
        (∃ e ∈ trackEdges P₁, e ∈ X) ∧
        (∃ e ∈ trackEdges P₂, e ∈ X) ∧
        (∃ e ∈ trackEdges P₃, e ∈ X) ∧
        ((s(P₁[0], P₁[1]) ∉ X ∧ s(P₂[0], P₂[1]) ∉ X) ∨
         (s(P₁[0], P₁[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X) ∨
         (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X)))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hP₃ : KAdj H X A x (a k) (b k))
    (hP₂ : KAdj H X A x (a k) (b j))
    (hP₁ : KAdj H X A x (a i) (b k))
    (hak : ∀ m : Fin 3, KAdj H X A x (a k) (b m) → m = k ∨ m = j)
    (hbk : ∀ m : Fin 3, KAdj H X A x (b k) (a m) → m = k ∨ m = i) :
    False := by
  classical
  -- ### the marked edge `x k`
  have hxk : x k = s(a k, b k) := hs.hab k
  have hadjk : H.Adj (a k) (b k) := by have h := hxE k; rw [hxk] at h; exact h
  have hXk : s(a k, b k) ∈ X := by rw [← hxk]; exact hxX k
  have hXk' : s(b k, a k) ∈ X := by rw [Sym2.eq_swap]; exact hXk
  have hne : ∀ m n : Fin 3, m ≠ n → a m ≠ a n ∧ a m ≠ b n ∧ b m ≠ a n ∧ b m ≠ b n := hs.hdist
  -- ### the three tracks `P₁, P₂, P₃`
  obtain ⟨P3, hP3t, hP3A, hP3T⟩ := hP₃
  obtain ⟨P2, hP2t, hP2A, hP2T⟩ := hP₂
  obtain ⟨P1, hP1t, hP1A, hP1T⟩ := hP₁
  have hP3ne : 0 < P3.length := List.length_pos_of_ne_nil hP3t.1.1
  have hP30 : P3[0]'hP3ne = a k := getElem_zero_of_head? hP3t.2.1 hP3ne
  have hP3l : P3[P3.length - 1]'(by omega) = b k := getElem_last_of_getLast? hP3t.2.2 hP3ne
  have hP3nd := hP3t.1.2.1
  -- *"Since `P₃` joins the adjacent vertices `a₃, b₃` and does not use the edge `x₃`, it
  -- follows that `P₃` has nonempty interior."*
  have hlen3 : 3 ≤ P3.length := by
    by_contra hc
    rcases Nat.lt_or_ge P3.length 2 with h1 | h1
    · refine hs.hab_ne k ?_
      rw [← hP30, ← hP3l]
      exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3
        (by omega) hP3ne (by omega)
    · refine edge_not_mem_of_delete hP3t.1 (n := 0) (by omega) ?_
      have e1 : P3[0 + 1]'(by omega) = b k := by
        rw [← hP3l]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3
          (by omega) (by omega) (by omega)
      rw [show P3[0]'(by omega) = a k from hP30, e1]
      exact hXk
  -- ### the set `B = V(A) \ {a₃, b₃}` and the interior of `P₃`
  have hindexB : ∀ (r : ℕ) (h : r < P3.length), 1 ≤ r → r ≤ P3.length - 2 →
      (P3[r]'h ∈ A ∧ P3[r]'h ≠ a k ∧ P3[r]'h ≠ b k) := by
    intro r h h1 h2
    refine ⟨hP3A _ (List.getElem_mem h), ?_, ?_⟩
    · rw [← hP30]
      intro hcon
      have := (List.Nodup.getElem_inj_iff hP3nd).mp hcon
      omega
    · rw [← hP3l]
      intro hcon
      have := (List.Nodup.getElem_inj_iff hP3nd).mp hcon
      omega
  set B : Set W := {z | z ∈ A ∧ z ≠ a k ∧ z ≠ b k} with hBdef
  have hs0B : P3[1]'(by omega) ∈ B := hindexB 1 (by omega) le_rfl (by omega)
  -- *"Choose a maximal connected subgraph `S` of `A` including the interior of `P₃` and not
  -- containing either of `a₃, b₃`."*
  obtain ⟨S, hScomp, hs0S⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem
      (H.deleteEdges X) B hs0B
  have hSB : S ⊆ B := hScomp.1
  have hSconn : ConnectedSet (H.deleteEdges X) S := hScomp.2.1
  have hSA : ∀ z ∈ S, z ∈ A := fun z hz => (hSB hz).1
  have hSak : ∀ z ∈ S, z ≠ a k := fun z hz => (hSB hz).2.1
  have hSbk : ∀ z ∈ S, z ≠ b k := fun z hz => (hSB hz).2.2
  have hakS : a k ∉ S := fun h => (hSak _ h) rfl
  have hbkS : b k ∉ S := fun h => (hSbk _ h) rfl
  have hSclose : ∀ p, p ∈ S → ∀ q, q ∈ B → (H.deleteEdges X).Adj p q → q ∈ S := by
    intro p hp q hq hadj
    have hD : ConnectedSet (H.deleteEdges X) (S ∪ {q}) :=
      Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
        hSconn ⟨p, hp, hadj.symm⟩
    have heq := hScomp.2.2 (S ∪ {q}) Set.subset_union_left
      (Set.union_subset hSB (Set.singleton_subset_iff.mpr hq)) hD
    rw [← heq]
    exact Or.inr rfl
  -- the interior of `P₃` lies in `S`
  have hP3int : ∀ (r : ℕ) (h : r < P3.length), 1 ≤ r → r ≤ P3.length - 2 → P3[r]'h ∈ S := by
    intro r h h1 h2
    have htr : IsTrackFrom (H.deleteEdges X) (slice P3 1 r) (P3[1]'(by omega)) (P3[r]'h) :=
      isTrackFrom_slice hP3t.1 h h1
    have hall : ∀ z ∈ slice P3 1 r, z ∈ B := by
      intro z hz
      obtain ⟨t, ht, h1t, htr', rfl⟩ := (mem_slice_iff h h1).mp hz
      exact hindexB t ht h1t (by omega)
    exact mem_of_track hSclose htr hall hs0S _
      ((mem_slice_iff h h1).mpr ⟨r, h, h1, le_rfl, rfl⟩)
  have hP3S : ∀ z ∈ P3, z = a k ∨ z = b k ∨ z ∈ S := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hz
    by_cases h0 : r = 0
    · exact Or.inl (by rw [← hP30]; exact
        Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3 h0 hr hP3ne)
    by_cases hl : r = P3.length - 1
    · exact Or.inr (Or.inl (by rw [← hP3l]; exact
        Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3 hl hr (by omega)))
    · exact Or.inr (Or.inr (hP3int r hr (by omega) (by omega)))
  -- ### *"none of `a₁, b₁, a₂, b₂` is in `V(S)`"*
  have hnoterm : ∀ z ∈ S, z ∉ Terminals x := by
    intro t0 ht0S ht0T
    obtain ⟨p, hp, t, ht, R, hRt, hRS, hRcleanA, hRcleanB⟩ :=
      Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack (H.deleteEdges X) S
        {z | z ∈ P3 ∧ z ∈ S} {z | z ∈ S ∧ z ∈ Terminals x} hSconn
        ⟨P3[1]'(by omega), List.getElem_mem (by omega), hs0S⟩ ⟨t0, ht0S, ht0T⟩
        (fun z hz => hz.2) (fun z hz => hz.1)
    obtain ⟨hpP3, hpS⟩ := hp
    obtain ⟨htS, htT⟩ := ht
    obtain ⟨n, hn, hpn⟩ := List.mem_iff_getElem.mp hpP3
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        have hpa : p = a k := by
          rw [← hpn, ← hP30]
          exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3 h hn hP3ne
        exact hakS (hpa ▸ hpS)
      · exact h
    have hnl : n < P3.length - 1 := by
      rcases lt_or_eq_of_le (show n ≤ P3.length - 1 by omega) with h | h
      · exact h
      · exfalso
        have : p = b k := by
          rw [← hpn, ← hP3l]
          exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P3 h hn (by omega)
        exact hbkS (this ▸ hpS)
    -- the two halves of `P₃`, each glued to `R`
    have hPre : IsTrackFrom (H.deleteEdges X) (slice P3 0 n) (a k) p := by
      have h := isTrackFrom_slice (i := 0) (j := n) hP3t.1 hn (Nat.zero_le _)
      rw [hP30, hpn] at h
      exact h
    have hSuf : IsTrackFrom (H.deleteEdges X) (slice P3 n (P3.length - 1)) p (b k) := by
      have h := isTrackFrom_slice (i := n) (j := P3.length - 1) hP3t.1
        (show P3.length - 1 < P3.length by omega) (by omega)
      rw [hP3l, hpn] at h
      exact h
    have hcommon1 : ∀ z : W, z ∈ slice P3 0 n → z ∈ R → z = p := fun z h1 h2 =>
      hRcleanA z h2 ⟨mem_of_mem_slice h1, hRS z h2⟩
    have hcommon2 : ∀ z : W, z ∈ R.reverse → z ∈ slice P3 n (P3.length - 1) → z = p := by
      intro z h1 h2
      exact hRcleanA z (List.mem_reverse.mp h1)
        ⟨mem_of_mem_slice h2, hRS z (List.mem_reverse.mp h1)⟩
    obtain ⟨hQ1, hQ1mem⟩ :=
      Workspace.ProofLemmas.TrackGlueAtCommonEndpoint (H.deleteEdges X)
        (slice P3 0 n) R (a k) p t hPre hRt hcommon1
    obtain ⟨hQ2, hQ2mem⟩ :=
      Workspace.ProofLemmas.TrackGlueAtCommonEndpoint (H.deleteEdges X)
        R.reverse (slice P3 n (P3.length - 1)) t p (b k)
        (isTrackFrom_reverse hRt) hSuf hcommon2
    -- `b k` is not on the first half, `a k` is not on the second
    have hbkPre : b k ∉ slice P3 0 n := by
      intro h
      obtain ⟨r, hr, -, hrn, hrb⟩ := (mem_slice_iff hn (Nat.zero_le n)).mp h
      have hrr : r = P3.length - 1 := by
        have heq : P3[r]'hr = P3[P3.length - 1]'(by omega) := by rw [hrb, hP3l]
        exact (List.Nodup.getElem_inj_iff hP3nd).mp heq
      omega
    have hakSuf : a k ∉ slice P3 n (P3.length - 1) := by
      intro h
      obtain ⟨r, hr, hnr, -, hra⟩ :=
        (mem_slice_iff (show P3.length - 1 < P3.length by omega) (by omega)).mp h
      have hrr : r = 0 := by
        have heq : P3[r]'hr = P3[0]'hP3ne := by rw [hra, hP30]
        exact (List.Nodup.getElem_inj_iff hP3nd).mp heq
      omega
    have hKleft : KAdj H X A x (a k) t := by
      refine ⟨slice P3 0 n ++ R.tail, hQ1, ?_, ?_⟩
      · intro z hz
        rcases hQ1mem z hz with h | h
        · exact hP3A z (mem_of_mem_slice h)
        · exact hSA z (hRS z h)
      · intro z hz hzT
        rcases hQ1mem z hz with h | h
        · rcases hP3T z (mem_of_mem_slice h) hzT with h' | h'
          · exact Or.inl h'
          · exact absurd (h' ▸ h) hbkPre
        · exact Or.inr (hRcleanB z h ⟨hRS z h, hzT⟩)
    have hKright : KAdj H X A x t (b k) := by
      refine ⟨R.reverse ++ (slice P3 n (P3.length - 1)).tail, hQ2, ?_, ?_⟩
      · intro z hz
        rcases hQ2mem z hz with h | h
        · exact hSA z (hRS z (List.mem_reverse.mp h))
        · exact hP3A z (mem_of_mem_slice h)
      · intro z hz hzT
        rcases hQ2mem z hz with h | h
        · exact Or.inl (hRcleanB z (List.mem_reverse.mp h)
            ⟨hRS z (List.mem_reverse.mp h), hzT⟩)
        · rcases hP3T z (mem_of_mem_slice h) hzT with h' | h'
          · exact absurd (h' ▸ h) hakSuf
          · exact Or.inr h'
    obtain ⟨m, hm⟩ := terminal_cases hs htT
    rcases hm with rfl | rfl
    · have hmk : m ≠ k := fun h => hakS (h ▸ htS)
      exact hs.hnoaa k m (Ne.symm hmk) hKleft
    · have hmk : m ≠ k := fun h => hbkS (h ▸ htS)
      exact hs.hnobb m k hmk hKright
  -- ### endpoints and terminal-cleanness of `P₁` and `P₂`
  have hP1ne : 0 < P1.length := List.length_pos_of_ne_nil hP1t.1.1
  have hP10 : P1[0]'hP1ne = a i := getElem_zero_of_head? hP1t.2.1 hP1ne
  have hP1l : P1[P1.length - 1]'(by omega) = b k := getElem_last_of_getLast? hP1t.2.2 hP1ne
  have hP1nd := hP1t.1.2.1
  have hP2ne : 0 < P2.length := List.length_pos_of_ne_nil hP2t.1.1
  have hP20 : P2[0]'hP2ne = a k := getElem_zero_of_head? hP2t.2.1 hP2ne
  have hP2l : P2[P2.length - 1]'(by omega) = b j := getElem_last_of_getLast? hP2t.2.2 hP2ne
  have hP2nd := hP2t.1.2.1
  have hnotP1 : ∀ z : W, z ∈ Terminals x → z ≠ a i → z ≠ b k → z ∉ P1 := by
    intro z hzT h1 h2 hzP
    rcases hP1T z hzP hzT with h | h
    · exact h1 h
    · exact h2 h
  have hnotP2 : ∀ z : W, z ∈ Terminals x → z ≠ a k → z ≠ b j → z ∉ P2 := by
    intro z hzT h1 h2 hzP
    rcases hP2T z hzP hzT with h | h
    · exact h1 h
    · exact h2 h
  have hakP1 : a k ∉ P1 :=
    hnotP1 (a k) (term_a hs k) ((hne k i (Ne.symm hik)).1) (hs.hab_ne k)
  have hbiP1 : b i ∉ P1 :=
    hnotP1 (b i) (term_b hs i) (Ne.symm (hs.hab_ne i)) ((hne i k hik).2.2.2)
  have hbkP2 : b k ∉ P2 :=
    hnotP2 (b k) (term_b hs k) (Ne.symm (hs.hab_ne k)) ((hne k j (Ne.symm hjk)).2.2.2)
  have hajP2 : a j ∉ P2 :=
    hnotP2 (a j) (term_a hs j) ((hne j k hjk).1) (hs.hab_ne j)
  -- ### `S` is vertex-disjoint from `P₁` and `P₂`
  have hP1S : ∀ z ∈ P1, z ∉ S := by
    intro z hz hzS
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hz
    have hm0 : m ≠ 0 := by
      intro h
      refine hnoterm _ hzS ?_
      rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P1 h hm hP1ne, hP10]
      exact term_a hs i
    have hml : m ≠ P1.length - 1 := by
      intro h
      refine hnoterm _ hzS ?_
      rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P1 h hm (by omega),
        hP1l]
      exact term_b hs k
    have hall : ∀ w : W, w ∈ (slice P1 0 m).reverse → w ∈ B := by
      intro w hw
      obtain ⟨r, hr, -, hrm, rfl⟩ :=
        (mem_slice_iff hm (Nat.zero_le m)).mp (List.mem_reverse.mp hw)
      refine ⟨hP1A _ (List.getElem_mem hr), ?_, ?_⟩
      · intro hcon
        exact hakP1 (hcon ▸ List.getElem_mem hr)
      · intro hcon
        have hrr : r = P1.length - 1 := by
          have heq : P1[r]'hr = P1[P1.length - 1]'(by omega) := by rw [hcon, hP1l]
          exact (List.Nodup.getElem_inj_iff hP1nd).mp heq
        omega
    have htr : IsTrackFrom (H.deleteEdges X) (slice P1 0 m).reverse (P1[m]'hm) (a i) := by
      have h := isTrackFrom_slice (i := 0) (j := m) hP1t.1 hm (Nat.zero_le _)
      rw [hP10] at h
      exact isTrackFrom_reverse h
    have haiS : a i ∈ S :=
      mem_of_track hSclose htr hall hzS (a i)
        (by rw [List.mem_reverse]
            exact (mem_slice_iff hm (Nat.zero_le m)).mpr ⟨0, hP1ne, le_rfl, Nat.zero_le m, hP10⟩)
    exact hnoterm _ haiS (term_a hs i)
  have hP2S : ∀ z ∈ P2, z ∉ S := by
    intro z hz hzS
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hz
    have hm0 : m ≠ 0 := by
      intro h
      refine hakS ?_
      rw [← hP20, ← Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P2 h hm hP2ne]
      exact hzS
    have hml : m ≠ P2.length - 1 := by
      intro h
      refine hnoterm _ hzS ?_
      rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P2 h hm (by omega),
        hP2l]
      exact term_b hs j
    have hall : ∀ w : W, w ∈ slice P2 m (P2.length - 1) → w ∈ B := by
      intro w hw
      obtain ⟨r, hr, hmr, -, rfl⟩ :=
        (mem_slice_iff (show P2.length - 1 < P2.length by omega) (by omega)).mp hw
      refine ⟨hP2A _ (List.getElem_mem hr), ?_, ?_⟩
      · intro hcon
        have hrr : r = 0 := by
          have heq : P2[r]'hr = P2[0]'hP2ne := by rw [hcon, hP20]
          exact (List.Nodup.getElem_inj_iff hP2nd).mp heq
        omega
      · intro hcon
        exact hbkP2 (hcon ▸ List.getElem_mem hr)
    have htr : IsTrackFrom (H.deleteEdges X) (slice P2 m (P2.length - 1)) (P2[m]'hm) (b j) := by
      have h := isTrackFrom_slice (i := m) (j := P2.length - 1) hP2t.1
        (show P2.length - 1 < P2.length by omega) (by omega)
      rw [hP2l] at h
      exact h
    have hbjS : b j ∈ S :=
      mem_of_track hSclose htr hall hzS (b j)
        ((mem_slice_iff (show P2.length - 1 < P2.length by omega) (by omega)).mpr
          ⟨P2.length - 1, by omega, by omega, le_rfl, hP2l⟩)
    exact hnoterm _ hbjS (term_b hs j)
  -- ### *"there is an edge `sv` of `H` with `s ∈ V(S)` and `v ∉ V(S) ∪ {a₃, b₃}`"*
  have hUmem : ∀ z : W, z ≠ a k → z ≠ b k → z ∈ (({a k, b k} : Set W)ᶜ) := by
    intro z h1 h2
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨h1, h2⟩
  have hUmem' : ∀ z : W, z ∈ (({a k, b k} : Set W)ᶜ) → z ≠ a k ∧ z ≠ b k := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz
    exact hz
  have hUconn : ConnectedSet H (({a k, b k} : Set W)ᶜ) :=
    Workspace.ProofLemmas.Thm57EndgameEdgeDeletion.connected_compl_edge H hc3 hadjk
  have hSU : S ⊆ (({a k, b k} : Set W)ᶜ) := fun z hz => hUmem z (hSak z hz) (hSbk z hz)
  have hbiS : b i ∉ S := fun h => hnoterm _ h (term_b hs i)
  obtain ⟨sw, hswS, v, hvU, hvS, hadjsv⟩ :=
    exists_crossing_edge H (({a k, b k} : Set W)ᶜ) S hUconn hSU hs0S
      (hUmem (b i) ((hne i k hik).2.2.1) ((hne i k hik).2.2.2)) hbiS
  obtain ⟨hvak, hvbk⟩ := hUmem' v hvU
  -- *"since `S` is maximal `sv ∉ E(A)`; and since `A` is maximal, `sv ∈ X`"*
  have hswA : sw ∈ A := hSA sw hswS
  have hXsv : s(sw, v) ∈ X := by
    by_contra hnx
    have hGadj : (H.deleteEdges X).Adj sw v := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hadjsv, hnx⟩
    by_cases hvA : v ∈ A
    · exact hvS (hSclose sw hswS v ⟨hvA, hvak, hvbk⟩ hGadj)
    · have hD : ConnectedSet (H.deleteEdges X) (A ∪ {v}) :=
        Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton hconn
          ⟨sw, hswA, hGadj.symm⟩
      have heq := hmaximal (A ∪ {v}) Set.subset_union_left hD
      exact hvA (by rw [← heq]; exact Or.inr rfl)
  -- the marked edges at `x i` and `x j`
  have hxi : x i = s(a i, b i) := hs.hab i
  have hxj : x j = s(a j, b j) := hs.hab j
  have hXi : s(a i, b i) ∈ X := by rw [← hxi]; exact hxX i
  have hXj : s(b j, a j) ∈ X := by rw [Sym2.eq_swap, ← hxj]; exact hxX j
  have hadji : H.Adj (a i) (b i) := by have h := hxE i; rw [hxi] at h; exact h
  have hadjj : H.Adj (b j) (a j) := by
    have h := hxE j; rw [hxj] at h; exact h.symm
  -- ### *"from the symmetry we may assume `v ∉ {a₁, b₁}`"*
  by_cases hvi : v = a i ∨ v = b i
  · -- the symmetric side: play the same game with `a ↔ b` and `i ↔ j`
    have hvaj : v ≠ a j := by
      rcases hvi with h | h
      · exact fun hc => (hne i j hij).1 (h.symm.trans hc)
      · exact fun hc => (hne i j hij).2.2.1 (h.symm.trans hc)
    have hvT : v ∈ Terminals x := by
      rcases hvi with h | h
      · exact h ▸ term_a hs i
      · exact h ▸ term_b hs i
    have hvP2 : v ∉ P2 := by
      refine hnotP2 v hvT hvak ?_
      rcases hvi with h | h
      · exact fun hc => (hne i j hij).2.1 (h.symm.trans hc)
      · exact fun hc => (hne i j hij).2.2.2 (h.symm.trans hc)
    exact Workspace.ProofLemmas.Thm57Claim4EndgameOutside.caseVOutP H X hclaim3
      (isTrackFrom_reverse hP2t) (isTrackFrom_reverse hP3t) hSconn hswS
      (fun z hz => hP2S z (List.mem_reverse.mp hz))
      (fun z hz => by
        rcases hP3S z (List.mem_reverse.mp hz) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h))
      ⟨P3[1]'(by omega), by rw [List.mem_reverse]; exact List.getElem_mem (by omega), hs0S⟩
      hakS hbkS
      (fun h => hajP2 (List.mem_reverse.mp h)) (fun h => hnoterm _ h (term_a hs j))
      ((hne j k hjk).1) ((hne j k hjk).2.1)
      (fun h => hvP2 (List.mem_reverse.mp h)) hvS hvak hvbk hvaj
      (fun h => hbkP2 (List.mem_reverse.mp h)) ((hne j k hjk).2.2.1)
      hXj hXk hXsv hadjj hadjk hadjsv
  · push_neg at hvi
    obtain ⟨hvai, hvbi⟩ := hvi
    by_cases hvinP1 : v ∈ P1
    · -- `v` is an internal vertex of `P₁`
      obtain ⟨m, hm, hvm⟩ := List.mem_iff_getElem.mp hvinP1
      have hm0 : m ≠ 0 := by
        intro h
        refine hvai ?_
        rw [← hvm, ← hP10]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P1 h hm hP1ne
      have hml : m ≠ P1.length - 1 := by
        intro h
        refine hvbk ?_
        rw [← hvm, ← hP1l]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P1 h hm (by omega)
      exact Workspace.ProofLemmas.Thm57Claim4EndgameInside.caseVInP H X hclaim3
        hP1t (show 1 ≤ m by omega) (show m + 1 < P1.length by omega) hbiP1 hakP1
        ((hne i k hik).2.2.1)
        (fun h => hP1S sw h hswS) (fun hc => hbiS (hc ▸ hswS)) (fun hc => hakS (hc ▸ hswS))
        hXi hXk' (by rw [hvm, Sym2.eq_swap]; exact hXsv) hadji hadjk.symm (by rw [hvm]; exact hadjsv.symm)
    · -- the main case of the paper
      exact Workspace.ProofLemmas.Thm57Claim4EndgameOutside.caseVOutP H X hclaim3
        hP1t hP3t hSconn hswS hP1S
        (fun z hz => by
          rcases hP3S z hz with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h))
        ⟨P3[1]'(by omega), List.getElem_mem (by omega), hs0S⟩
        hbkS hakS
        hbiP1 hbiS ((hne i k hik).2.2.2) ((hne i k hik).2.2.1)
        hvinP1 hvS hvbk hvak hvbi
        hakP1 ((hne i k hik).2.1)
        hXi hXk' hXsv hadji hadjk.symm hadjsv


end Workspace.ProofLemmas.Thm57Claim4Endgame
