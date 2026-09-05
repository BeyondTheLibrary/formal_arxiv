import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
import Workspace.ProofLemmas.Thm57Claim4Config
import Workspace.ProofLemmas.Thm57Claim4Reach
import Workspace.ProofLemmas.Thm57Claim4NoDoubleForeign
import Workspace.ProofLemmas.Thm57Claim4Component
import Workspace.ProofLemmas.Thm57Claim4Endgame

/-!
# 5.7 (4): the six-terminal reduction

The proved lemma in this file is the first parity step in printed claim (4).  It says that an
endpoint-clean track in `H \ X` between two disjoint edges of `X` cannot join equally coloured
ends.  Otherwise, adding the two edges produces the even track forbidden by the hypothesis of
5.7.

The remaining labelled lemma records the graph-theoretic heart of the printed proof, beginning
with its auxiliary graph on the six ends of the three edges.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm57Claim4Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A track in `H \ X` between an end of `e` and an end of `f`, with no other end of either
edge on the track.  This is the kind of track represented by an edge of the auxiliary graph
`K` in the printed proof of 5.7 (4). -/
def EndpointCleanConnection (H : SimpleGraph W) (X : Set (Sym2 W))
    (e f : Sym2 W) (u v : W) (P : List W) : Prop :=
  IsTrackFrom (H.deleteEdges X) P u v ∧
    (∀ z ∈ P, z ∈ e → z = u) ∧
    (∀ z ∈ P, z ∈ f → z = v)

/-- If an auxiliary-graph edge joined two equally coloured ends, the two marked edges and its
track would be the forbidden even track from the hypothesis of 5.7. -/
theorem endpointCleanConnection_different_color
    (H : SimpleGraph W) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : NoEvenTrack57 H X) (col : H.Coloring Bool)
    {e f : Sym2 W} (heX : e ∈ X) (hfX : f ∈ X) (hef : DisjointEdges e f)
    {u v : W} (hu : u ∈ e) (hv : v ∈ f) {P : List W}
    (hP : EndpointCleanConnection H X e f u v P) : col u ≠ col v := by
  classical
  intro hcol
  obtain ⟨u', he⟩ := Sym2.mem_iff_exists.mp hu
  obtain ⟨v', hf⟩ := Sym2.mem_iff_exists.mp hv
  subst e
  subst f
  have heAdj : H.Adj u u' := hXE heX
  have hfAdj : H.Adj v v' := hXE hfX
  have huu' : u ≠ u' := heAdj.ne
  have hvv' : v ≠ v' := hfAdj.ne
  have huv : u ≠ v := by
    intro h
    subst v
    exact hef u ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  have hu'v : u' ≠ v := by
    intro h
    subst v
    exact hef u' ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
  have huv' : u ≠ v' := by
    intro h
    subst v'
    exact hef u ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩
  have hu'v' : u' ≠ v' := by
    intro h
    subst v'
    exact hef u' ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩
  have hPH : IsTrackFrom H P u v := by
    refine ⟨⟨hP.1.1.1, hP.1.1.2.1, ?_⟩, hP.1.2.1, hP.1.2.2⟩
    intro i hi
    exact (SimpleGraph.deleteEdges_adj.mp (hP.1.1.2.2 i hi)).1
  have hPtwo : 2 ≤ P.length := by
    by_contra hbad
    have hone : P.length = 1 := by
      have hpos := List.length_pos_of_ne_nil hP.1.1.1
      omega
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hone
    have hzu : z = u := by simpa using hPH.2.1
    have hzv : z = v := by simpa using hPH.2.2
    exact huv (hzu.symm.trans hzv)
  have hP0 : P[0]'(by omega) = u := by
    have hh := hPH.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hPlast : P[P.length - 1]'(by omega) = v := by
    have hh := hPH.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hu'P : u' ∉ P := by
    intro hu'P
    have := hP.2.1 u' hu'P (Sym2.mem_mk_right u u')
    exact huu' this.symm
  have hv'P : v' ∉ P := by
    intro hv'P
    have := hP.2.2 v' hv'P (Sym2.mem_mk_right v v')
    exact hvv' this.symm
  let T : List W := u' :: (P ++ [v'])
  have hTlen : T.length = P.length + 2 := by simp [T]
  have hTtrack : IsTrackList H T := by
    refine ⟨by simp [T], ?_, ?_⟩
    · simp only [T, List.nodup_cons, List.nodup_append, List.nodup_singleton]
      refine ⟨?_, ⟨hPH.1.2.1, by simp, ?_⟩⟩
      · intro hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hu'P hmem
        · exact hu'v' (by simpa using hmem)
      · intro z hz w hw hzw
        have hwv' : w = v' := by simpa using hw
        have hzv' : z = v' := hzw.trans hwv'
        exact hv'P (hzv' ▸ hz)
    · refine List.isChain_iff_getElem.mp ?_
      apply List.isChain_cons.mpr
      constructor
      · intro z hz
        rw [Option.mem_def, List.head?_append, hP.1.2.1] at hz
        rw [← Option.some_injective _ hz]
        exact heAdj.symm
      · apply List.isChain_append.mpr
        refine ⟨List.isChain_iff_getElem.mpr hPH.1.2.2, List.isChain_singleton _, ?_⟩
        intro z hz w hw
        rw [Option.mem_def, hP.1.2.2] at hz
        simp only [Option.mem_def, List.head?_singleton, Option.some.injEq] at hw
        rw [← Option.some_injective _ hz, ← hw]
        exact hfAdj
  have hTgetP : ∀ (k : ℕ) (hkT : k < T.length) (hk1 : 1 ≤ k) (hkP : k ≤ P.length),
      T[k]'hkT = P[k - 1]'(by omega) := by
    intro k hkT hk1 hkP
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [T, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega)]
    congr 1
  have hfirst : s(T[0]'(by omega), T[1]'(by omega)) = s(u, u') := by
    simp only [T, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega), hP0, Sym2.eq_swap]
  have hlast :
      s(T[T.length - 2]'(by omega), T[T.length - 1]'(by omega)) = s(v, v') := by
    rw [hTgetP (T.length - 2) (by omega) (by rw [hTlen]; omega) (by rw [hTlen]; omega)]
    have hi : T.length - 2 - 1 = P.length - 1 := by omega
    simp only [hi, hPlast]
    have hlastOpt : T.getLast? = some v' := by
      simp only [T, List.getLast?_cons, List.getLast?_append]
      simp
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlastOpt
    exact congrArg (s(v, ·)) (Option.some_injective _ hlastOpt)
  have hevenP : Even (trackLength P) :=
    (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hPH).mpr hcol
  have hevenT : Even (trackLength T) := by
    have hlen : trackLength T = trackLength P + 2 := by
      rw [trackLength, hTlen, trackLength]
      omega
    rw [hlen]
    exact hevenP.add (by decide)
  have hTlarge : 5 ≤ T.length := by
    rw [hTlen]
    obtain ⟨k, hk⟩ := hevenP
    rw [trackLength] at hk
    omega
  apply hnotrack
  refine ⟨T, hTlarge, hTtrack, hevenT, ?_, ?_, ?_⟩
  · rw [hfirst]
    exact heX
  · rw [hlast]
    exact hfX
  · intro g hgT hgne hgnf
    obtain ⟨k, hk, rfl⟩ := hgT
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      subst k
      exact hgne rfl
    have hkbefore : k < T.length - 2 := by
      have hkle : k ≤ T.length - 2 := by omega
      rcases hkle.eq_or_lt with h | h
      · exfalso
        have helem0 : T[k]'(by omega) = T[T.length - 2]'(by omega) :=
          hTtrack.2.1.getElem_inj_iff.mpr h
        have helem : T[k + 1]'(by omega) = T[T.length - 1]'(by omega) :=
          hTtrack.2.1.getElem_inj_iff.mpr (by omega)
        apply hgnf
        rw [helem0, helem]
      · exact h
    rw [hTgetP k (by omega) (by omega) (by omega),
      hTgetP (k + 1) (by omega) (by omega) (by omega)]
    have hdel := hP.1.1.2.2 (k - 1) (by rw [hTlen] at hkbefore; omega)
    simpa only [show k + 1 - 1 = k - 1 + 1 by omega] using
      (SimpleGraph.deleteEdges_adj.mp hdel).2

/-- If three pairwise disjoint marked edges meet one connected set and every clean connection
between different marked edges has opposite-coloured ends, then at least one marked edge has
both ends in the connected set.  This is the first consequence of the auxiliary graph `K`: if
each edge had only one end in the component, two of the three ends would have the same colour. -/
theorem some_marked_edge_internal
    (H : SimpleGraph W) (X : Set (Sym2 W)) (col : H.Coloring Bool)
    (x : Fin 3 → Sym2 W) (A : Set W)
    (hconn : ConnectedSet (H.deleteEdges X) A)
    (hxE : ∀ i, x i ∈ H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → DisjointEdges (x i) (x j))
    (hmeet : ∀ i, ∃ v ∈ A, v ∈ x i)
    (hpair : ∀ i j, i ≠ j → ∀ u v P, u ∈ x i → v ∈ x j →
      EndpointCleanConnection H X (x i) (x j) u v P → col u ≠ col v) :
    ∃ i, ∀ v ∈ x i, v ∈ A := by
  classical
  by_contra hnone
  push Not at hnone
  let u : Fin 3 → W := fun i => (hmeet i).choose
  have huA : ∀ i, u i ∈ A := fun i => (hmeet i).choose_spec.1
  have hux : ∀ i, u i ∈ x i := fun i => (hmeet i).choose_spec.2
  have huniq : ∀ i v, v ∈ A → v ∈ x i → v = u i := by
    intro i v hvA hvx
    obtain ⟨w, hiw⟩ := Sym2.mem_iff_exists.mp (hux i)
    have huw : u i ≠ w := by
      have hedge := hxE i
      rw [hiw] at hedge
      exact hedge.ne
    have hwA : w ∉ A := by
      obtain ⟨wbad, hwbadx, hwbadA⟩ := hnone i
      rw [hiw] at hwbadx
      rcases Sym2.mem_iff.mp hwbadx with h | h
      · exact absurd (h ▸ huA i) hwbadA
      · rw [h] at hwbadA
        exact hwbadA
    rw [hiw] at hvx
    rcases Sym2.mem_iff.mp hvx with h | h
    · exact h
    · exact absurd (h ▸ hvA) hwA
  have same_absurd : ∀ i j, i ≠ j → col (u i) = col (u j) → False := by
    intro i j hij hsame
    obtain ⟨a, ha, b, hb, P, hP, hPA, -, -⟩ :=
      Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
        (H.deleteEdges X) A {u i} {u j} hconn
        ⟨u i, rfl⟩ ⟨u j, rfl⟩ (Set.singleton_subset_iff.mpr (huA i))
          (Set.singleton_subset_iff.mpr (huA j))
    have hai : a = u i := by simpa using ha
    have hbj : b = u j := by simpa using hb
    subst a
    subst b
    exact (hpair i j hij (u i) (u j) P (hux i) (hux j)
      ⟨hP, fun z hz hzx => huniq i z (hPA z hz) hzx,
        fun z hz hzx => huniq j z (hPA z hz) hzx⟩) hsame
  by_cases h01 : col (u 0) = col (u 1)
  · exact same_absurd 0 1 (by decide) h01
  by_cases h02 : col (u 0) = col (u 2)
  · exact same_absurd 0 2 (by decide) h02
  have h12 : col (u 1) = col (u 2) := by
    cases h0 : col (u 0) <;> cases h1 : col (u 1) <;> cases h2 : col (u 2) <;>
      simp_all
  exact same_absurd 1 2 (by decide) h12

/--
PAPER (5.7 (4), printed p. 24), after the equal-colour parity step:

> *"Also, by (3) it follows that `a₃` is not adjacent in `K` to both `b₁` and `b₂`, and
> five similar statements. Since there is a component of `K` containing an end of each of
> `x₁,x₂,x₃`, we may assume that `a₁b₃,b₂a₃,a₃b₃ ∈ E(K)` ... But then the tracks
> `b₁-a₁-P₁-b₃`, `P₄`, and the one-edge track made by `x₃`, violate (3)."*

This lemma isolates the remaining six-terminal graph argument.  `hpair` is the preceding
sentence already proved by `endpointCleanConnection_different_color`: every endpoint-clean
connection between two marked edges has differently coloured ends.  `hclaim3` is printed claim
(3).  The conclusion is precisely the contradiction constructed in the quoted passage.
-/
theorem sixTerminalCore
    (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W))
    (col : H.Coloring Bool) (x : Fin 3 → Sym2 W) (A : Set W)
    (hconn : ConnectedSet (H.deleteEdges X) A)
    (hxX : ∀ i, x i ∈ X)
    (hxE : ∀ i, x i ∈ H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → DisjointEdges (x i) (x j))
    (hmeet : ∀ i, ∃ v ∈ A, v ∈ x i)
    (hinternal : ∃ i, ∀ v ∈ x i, v ∈ A)
    (hpair : ∀ i j, i ≠ j → ∀ u v P, u ∈ x i → v ∈ x j →
      EndpointCleanConnection H X (x i) (x j) u v P → col u ≠ col v)
    (hclaim3 :
      ¬ ∃ (b a₁ a₂ a₃ : W) (P₁ P₂ P₃ : List W)
          (_h₁ : 2 ≤ P₁.length) (_h₂ : 2 ≤ P₂.length) (_h₃ : 2 ≤ P₃.length),
        IsTrackFrom H P₁ b a₁ ∧ IsTrackFrom H P₂ b a₂ ∧ IsTrackFrom H P₃ b a₃ ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₂ → v = b) ∧
        (∀ v : W, v ∈ P₁ → v ∈ P₃ → v = b) ∧
        (∀ v : W, v ∈ P₂ → v ∈ P₃ → v = b) ∧
        (∃ e ∈ trackEdges P₁, e ∈ X) ∧
        (∃ e ∈ trackEdges P₂, e ∈ X) ∧
        (∃ e ∈ trackEdges P₃, e ∈ X) ∧
        ((s(P₁[0], P₁[1]) ∉ X ∧ s(P₂[0], P₂[1]) ∉ X) ∨
         (s(P₁[0], P₁[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X) ∨
         (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X))) : False := by
  classical
  -- *"We may assume `A` is a maximal connected subgraph of `H \ X`."*
  obtain ⟨A', hAA', hmaxA⟩ := Set.Finite.exists_le_maximal
    (Set.toFinite {C : Set W | ConnectedSet (H.deleteEdges X) C})
    (show A ∈ {C : Set W | ConnectedSet (H.deleteEdges X) C} from hconn)
  have hconn' : ConnectedSet (H.deleteEdges X) A' := hmaxA.1
  have hmaximal : ∀ D : Set W, A' ⊆ D → ConnectedSet (H.deleteEdges X) D → D = A' :=
    fun D hD hDc => Set.Subset.antisymm (hmaxA.2 hDc hD) hD
  -- *"let `xᵢ` have ends `aᵢ, bᵢ`, where `a₁, a₂, a₃` have the same biparity"*
  have hends : ∀ i, ∃ p q : W, x i = s(p, q) ∧ col p = true ∧ col q = false := by
    intro i
    have key : ∀ e : Sym2 W, e ∈ H.edgeSet →
        ∃ p q : W, e = s(p, q) ∧ col p = true ∧ col q = false := by
      refine Sym2.ind ?_
      intro p q hpq
      have hadj : H.Adj p q := hpq
      have hcne := col.valid hadj
      rcases Bool.eq_false_or_eq_true (col p) with hcp | hcp
      · refine ⟨p, q, rfl, hcp, ?_⟩
        rcases Bool.eq_false_or_eq_true (col q) with hcq | hcq
        · exact absurd (hcp.trans hcq.symm) hcne
        · exact hcq
      · refine ⟨q, p, Sym2.eq_swap, ?_, hcp⟩
        rcases Bool.eq_false_or_eq_true (col q) with hcq | hcq
        · exact hcq
        · exact absurd (hcp.trans hcq.symm) hcne
    exact key (x i) (hxE i)
  choose aa bb hab hcolA hcolB using hends
  have hax : ∀ i, aa i ∈ x i := fun i => by rw [hab i]; exact Sym2.mem_mk_left _ _
  have hbx : ∀ i, bb i ∈ x i := fun i => by rw [hab i]; exact Sym2.mem_mk_right _ _
  -- the auxiliary graph `K` and its two structural facts
  have hpair' : ∀ i j, i ≠ j → ∀ u v P, u ∈ x i → v ∈ x j →
      (IsTrackFrom (H.deleteEdges X) P u v ∧ (∀ z ∈ P, z ∈ x i → z = u) ∧
        (∀ z ∈ P, z ∈ x j → z = v)) → col u ≠ col v := hpair
  have hsetup : Workspace.ProofLemmas.Thm57Claim4Component.Setup H X A' x aa bb := by
    refine ⟨hab, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact ⟨fun h => hdisj i j hij (aa i) ⟨hax i, h ▸ hax j⟩,
        fun h => hdisj i j hij (aa i) ⟨hax i, h ▸ hbx j⟩,
        fun h => hdisj i j hij (bb i) ⟨hbx i, h ▸ hax j⟩,
        fun h => hdisj i j hij (bb i) ⟨hbx i, h ▸ hbx j⟩⟩
    · intro i h
      have := hcolA i
      rw [h, hcolB i] at this
      exact Bool.noConfusion this
    · intro i j hij hadj
      have := Workspace.ProofLemmas.Thm57Claim4Config.kAdj_col_ne hdisj hpair' hij
        (hax i) (hax j) hadj
      exact this ((hcolA i).trans (hcolA j).symm)
    · intro i j hij hadj
      have := Workspace.ProofLemmas.Thm57Claim4Config.kAdj_col_ne hdisj hpair' hij
        (hbx i) (hbx j) hadj
      exact this ((hcolB i).trans (hcolB j).symm)
    · intro i j k hij hik hjk u v w hu hv hw h1 h2
      exact Workspace.ProofLemmas.Thm57Claim4NoDoubleForeign.no_double_foreign
        H X A' x hxX hxE hdisj hclaim3 hij hik hjk hu hv hw h1 h2
    · intro i
      obtain ⟨v, hvA, hvx⟩ := hmeet i
      rw [hab i] at hvx
      rcases Sym2.mem_iff.mp hvx with h | h
      · exact Or.inl (h ▸ hAA' hvA)
      · exact Or.inr (h ▸ hAA' hvA)
    · intro u v hu hv huT hvT
      exact Workspace.ProofLemmas.Thm57Claim4Reach.reach_of_mem_A H X A' x hconn' hu hv huT hvT
  obtain ⟨i, j, k, hij, hik, hjk, hown, hkj, hik'⟩ :=
    Workspace.ProofLemmas.Thm57Claim4Component.exists_config hsetup
  -- *"there are no more edges of `K` incident with `a₃` or `b₃`"*
  have hakn : ∀ m : Fin 3,
      Workspace.ProofLemmas.Thm57Claim4Config.KAdj H X A' x (aa k) (bb m) → m = k ∨ m = j := by
    intro m hm
    by_contra hcon
    push_neg at hcon
    exact hsetup.hnd j m k (Ne.symm hcon.2) hjk hcon.1 (aa k) (bb j) (bb m)
      (hax k) (hbx j) (hbx m) hkj hm
  have hbkn : ∀ m : Fin 3,
      Workspace.ProofLemmas.Thm57Claim4Config.KAdj H X A' x (bb k) (aa m) → m = k ∨ m = i := by
    intro m hm
    by_contra hcon
    push_neg at hcon
    exact hsetup.hnd i m k (Ne.symm hcon.2) hik hcon.1 (bb k) (aa i) (aa m)
      (hbx k) (hax i) (hax m)
      (Workspace.ProofLemmas.Thm57Claim4Config.kAdj_symm hik') hm
  exact Workspace.ProofLemmas.Thm57Claim4Endgame.endgame H hc3 X A' x aa bb hconn' hmaximal
    hxX hxE hsetup hclaim3 hij hik hjk hown hkj hik' hakn hbkn


end Workspace.ProofLemmas.Thm57Claim4Core
