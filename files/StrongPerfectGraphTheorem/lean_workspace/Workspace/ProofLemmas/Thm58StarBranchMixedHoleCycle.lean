import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Connectivity58CycleBuild
import Workspace.ProofLemmas.Thm58StarBranchMixedHoleMirror
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# From the cycle `C₂` of `H` to the hole `L` of `G` (proof of 5.8 (6))

PAPER (proof of 5.8 (6), printed p. 28): *"In `H` there is a cycle `C₂` using the branch
between `v₁` and `v₂`, and using an edge in `A` and an edge in `B`. … Hence in `G`, there is a
path between `N_{v₁}` and `N_{v₂}` using a unique edge of `N(u)`, and that edge is between a
vertex `a ∈ A` and some vertex in `B`."*

This file does the *"hence in `G`"* half.  The cycle `C₂` is presented as a branch-track `Q`
and a second track `D` with the same ends which passes through the star vertex `c` at position
`j`, entering along the `A`-edge and leaving along the `B`-edge.  Rotating the cycle so that
`c` comes first makes the `A`-edge the first edge and the `B`-edge the last one, so the rung of
the cycle (`Thm58BranchBranchCycleRung.cycleRung`) is a hole of `G` starting at the `A`-vertex,
with no other vertex adjacent to `p₁`, and with the edges of the branch occupying a block of
consecutive positions.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm58StarBranchMixedHoleCycle

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58BranchBranchCycleRung Connectivity58CycleBuild
open Thm58StarBranchMixedHoleMirror

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-! ### Two edges of a track meet exactly when they are consecutive -/

private theorem consecutive_of_meet {W : Type*} [DecidableEq W] {Q : List W} (hnd : Q.Nodup)
    {i₁ i₂ : ℕ} (h₁ : i₁ + 1 < Q.length) (h₂ : i₂ + 1 < Q.length)
    (hne : i₁ ≠ i₂)
    (hmeet : ∃ v : W, v ∈ s(Q[i₁]'(by omega), Q[i₁ + 1]'h₁) ∧
      v ∈ s(Q[i₂]'(by omega), Q[i₂ + 1]'h₂)) :
    i₂ = i₁ + 1 ∨ i₁ = i₂ + 1 := by
  obtain ⟨v, hv1, hv2⟩ := hmeet
  rcases Sym2.mem_iff.mp hv1 with rfl | rfl <;> rcases Sym2.mem_iff.mp hv2 with hh | hh
  · exact absurd (hnd.getElem_inj_iff.mp hh) hne
  · exact Or.inr (hnd.getElem_inj_iff.mp hh)
  · exact Or.inl (hnd.getElem_inj_iff.mp hh).symm
  · have hh2 := hnd.getElem_inj_iff.mp hh
    exact absurd (by omega : i₁ = i₂) hne

/-! ### Normalising the order of the two marked vertices -/

/-- Reading the hole backwards from its first vertex exchanges the two marked consecutive
vertices. -/
theorem mirror_swaps {L : List V} {y₁ y₂ : V} {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ L.length)
    (h1 : L[k]? = some y₂) (h2 : L[k + 1]? = some y₁) :
    ∃ k', 1 ≤ k' ∧ k' + 2 ≤ (mirror L).length ∧
      (mirror L)[k']? = some y₁ ∧ (mirror L)[k' + 1]? = some y₂ := by
  have hlen : (mirror L).length = L.length := mirror_length L
  refine ⟨L.length - k - 1, by omega, by omega, ?_, ?_⟩
  · rw [List.getElem?_eq_getElem (by omega : L.length - k - 1 < (mirror L).length),
      mirror_getElem_pos L _ (by omega) (by omega) (by omega)]
    rw [List.getElem?_eq_getElem (by omega : k + 1 < L.length)] at h2
    rw [← h2]
    exact congrArg some (SubdivisionCounting.getElem_eq_of_index_eq L (by omega) _ _)
  · rw [List.getElem?_eq_getElem (by omega : L.length - k - 1 + 1 < (mirror L).length),
      mirror_getElem_pos L _ (by omega) (by omega) (by omega)]
    rw [List.getElem?_eq_getElem (by omega : k < L.length)] at h1
    rw [← h1]
    exact congrArg some (SubdivisionCounting.getElem_eq_of_index_eq L (by omega) _ _)

/-! ### The assembly -/

/-- **The rung of `C₂`.**  A branch-track `Q` and a second track `D` with the same ends,
meeting only there, with `D` passing through the star vertex `c` at position `j` between the
`A`-neighbour `xA` and the `B`-neighbour `xB`, produce the hole of 5.8 (6) — except that the
two marked vertices may come out in either order. -/
theorem exists_hole_unordered
    (h : Context G m J n H K φ N F P p₁ p₂ c q)
    {Q D : List (Fin n)} {w₁ w₂ : Fin n} {j : ℕ} {xA xB : Fin n} {y₁ y₂ : V}
    (hQ : IsTrackFrom H Q w₁ w₂) (hQ2 : 2 ≤ Q.length)
    (hD : IsTrackFrom H D w₁ w₂) (hD3 : 3 ≤ D.length)
    (hdisj : ∀ z ∈ trackInterior D, z ∉ Q)
    (hj1 : 1 ≤ j) (hj2 : j + 1 < D.length)
    (hcj : D[j]? = some c) (hxA : D[j - 1]? = some xA) (hxB : D[j + 1]? = some xB)
    (hAedge : s(c, xA) ∈ H.edgeSet)
    (hAadj : ∀ he : s(c, xA) ∈ H.edgeSet, G.Adj p₁ (↑(φ ⟨s(c, xA), he⟩) : V))
    (hBadj : ∀ he : s(c, xB) ∈ H.edgeSet, ¬ G.Adj p₁ (↑(φ ⟨s(c, xB), he⟩) : V))
    (hy₁ : y₁ ∈ edgeImage φ (trackEdges Q)) (hy₂ : y₂ ∈ edgeImage φ (trackEdges Q))
    (hy : G.Adj y₁ y₂) :
    ∃ (L : List V) (a : V) (k : ℕ),
      IsHoleList G L ∧ (∀ x ∈ L, x ∈ K) ∧ L.head? = some a ∧
      a ∈ N c ∧ G.Adj p₁ a ∧ (∀ x ∈ L, x ≠ a → ¬ G.Adj p₁ x) ∧
      1 ≤ k ∧ k + 2 ≤ L.length ∧
      ((L[k]? = some y₁ ∧ L[k + 1]? = some y₂) ∨
        (L[k]? = some y₂ ∧ L[k + 1]? = some y₁)) := by
  classical
  have hDj : D[j]'(by omega) = c := by
    have hh := hcj
    rw [List.getElem?_eq_getElem (by omega : j < D.length)] at hh
    exact Option.some_injective _ hh
  have hDjA : D[j - 1]'(by omega : j - 1 < D.length) = xA := by
    have hh := hxA
    rw [List.getElem?_eq_getElem (by omega : j - 1 < D.length)] at hh
    exact Option.some_injective _ hh
  have hDjB : D[j + 1]'(by omega) = xB := by
    have hh := hxB
    rw [List.getElem?_eq_getElem (by omega : j + 1 < D.length)] at hh
    exact Option.some_injective _ hh
  have hQ0 : Q[0]'(by omega) = w₁ := track_first hQ (by omega)
  have hQl : Q[Q.length - 1]'(by omega) = w₂ := track_last hQ (by omega)
  have hD0 : D[0]'(by omega) = w₁ := track_first hD (by omega)
  have hDl : D[D.length - 1]'(by omega) = w₂ := track_last hD (by omega)
  set NN : ℕ := Q.length + D.length - 2 with hNN
  have hjNN : j < NN := by omega
  have hNN3 : 3 ≤ NN := by omega
  set cy : List (Fin n) := cycleFrom Q D (NN - j) with hcydef
  have hcyc : IsCycleList H cy := isCycleList_cycleFrom hQ hD hQ2 hD3 hdisj _
  have hcylen : cy.length = NN := by rw [hcydef, cycleFrom_length]; omega
  have hBlen : (baseCycle Q D).length = NN := by rw [baseCycle_length]; omega
  have hrot : ∀ (mm : ℕ) (hm : mm < cy.length) (t : ℕ) (ht : t < NN),
      (mm + (NN - j)) % NN = t →
      cy[mm]'hm = (baseCycle Q D)[t]'(by rw [hBlen]; exact ht) := by
    intro mm hm t ht hmt
    have hrw : cy[mm]'hm
        = (baseCycle Q D)[(mm + (NN - j)) % (baseCycle Q D).length]'
            (Nat.mod_lt _ (by omega)) := by
      simp only [hcydef, cycleFrom]
      exact List.getElem_rotate _ _ _ _
    rw [hrw]
    refine SubdivisionCounting.getElem_eq_of_index_eq _ ?_ _ _
    rw [hBlen]; exact hmt
  have hleft : ∀ (mm : ℕ) (hm : mm < cy.length), mm ≤ j →
      cy[mm]'hm = D[j - mm]'(by omega) := by
    intro mm hm hmj
    rcases Nat.lt_or_ge mm j with hlt | hge
    · have hidx : (mm + (NN - j)) % NN = mm + (NN - j) := Nat.mod_eq_of_lt (by omega)
      rw [hrot mm hm (mm + (NN - j)) (by omega) hidx,
        baseCycle_getElem_right Q D _ (by omega) (by omega)]
      exact SubdivisionCounting.getElem_eq_of_index_eq D (by omega) _ _
    · have hmj' : mm = j := by omega
      subst hmj'
      have hidx : (mm + (NN - mm)) % NN = 0 := by
        rw [show mm + (NN - mm) = NN by omega, Nat.mod_self]
      rw [hrot mm hm 0 (by omega) hidx, baseCycle_getElem_left Q D 0 (by omega) (by omega),
        SubdivisionCounting.getElem_eq_of_index_eq D (show mm - mm = 0 by omega)
          (by omega) (by omega), hD0, hQ0]
  have hbranch : ∀ (i : ℕ) (hi : i < Q.length) (hm : j + i < cy.length),
      cy[j + i]'hm = Q[i]'hi := by
    intro i hi hm
    have hidx : (j + i + (NN - j)) % NN = i := by
      rw [show j + i + (NN - j) = i + 1 * NN by omega, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (by omega)]
    rw [hrot (j + i) hm i (by omega) hidx,
      baseCycle_getElem_left Q D i (by omega) (by omega)]
  have hlast : ∀ (hm : NN - 1 < cy.length), cy[NN - 1]'hm = D[j + 1]'(by omega) := by
    intro hm
    rcases Nat.lt_or_ge j (D.length - 2) with hlt | hge
    · have hidx : (NN - 1 + (NN - j)) % NN = NN - 1 - j := by
        rw [show NN - 1 + (NN - j) = (NN - 1 - j) + 1 * NN by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hrot (NN - 1) hm (NN - 1 - j) (by omega) hidx,
        baseCycle_getElem_right Q D _ (by omega) (by omega)]
      exact SubdivisionCounting.getElem_eq_of_index_eq D (by omega) _ _
    · have hjeq : j = D.length - 2 := by omega
      have hm2 : j + (Q.length - 1) < cy.length := by omega
      have hb := hbranch (Q.length - 1) (by omega) hm2
      rw [hQl] at hb
      rw [SubdivisionCounting.getElem_eq_of_index_eq cy
          (show NN - 1 = j + (Q.length - 1) by omega) hm hm2, hb,
        SubdivisionCounting.getElem_eq_of_index_eq D
          (show j + 1 = D.length - 1 by omega) (by omega) (by omega), hDl]
  -- the cycle has at least four vertices, because `H` is bipartite
  obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite h.ready.2.2.1.2
  have hNN4 : 4 ≤ NN := by
    by_contra hcon
    have h3 : NN = 3 := by omega
    have e0 : nxt cy 0 = 1 := by rw [nxt, hcylen, h3]
    have e1 : nxt cy 1 = 2 := by rw [nxt, hcylen, h3]
    have e2 : nxt cy 2 = 0 := by rw [nxt, hcylen, h3]
    have a01 : H.Adj (cy[0]'(by omega)) (cy[1]'(by omega)) := by
      have hh := hcyc.2.2 0 (by omega) (by omega)
      rwa [SubdivisionCounting.getElem_eq_of_index_eq cy e0 _ (by omega)] at hh
    have a12 : H.Adj (cy[1]'(by omega)) (cy[2]'(by omega)) := by
      have hh := hcyc.2.2 1 (by omega) (by omega)
      rwa [SubdivisionCounting.getElem_eq_of_index_eq cy e1 _ (by omega)] at hh
    have a20 : H.Adj (cy[2]'(by omega)) (cy[0]'(by omega)) := by
      have hh := hcyc.2.2 2 (by omega) (by omega)
      rwa [SubdivisionCounting.getElem_eq_of_index_eq cy e2 _ (by omega)] at hh
    have n01 := col.valid a01
    have n12 := col.valid a12
    have n20 := col.valid a20
    revert n01 n12 n20
    generalize col (cy[0]'(by omega : 0 < cy.length)) = b0
    generalize col (cy[1]'(by omega : 1 < cy.length)) = b1
    generalize col (cy[2]'(by omega : 2 < cy.length)) = b2
    revert b0 b1 b2
    decide
  have hcyc4 : 4 ≤ cy.length := by omega
  have hLlen : (cycleRung φ hcyc).length = NN := by rw [cycleRung_length, hcylen]
  have hLhole : IsHoleList G (cycleRung φ hcyc) := isHoleList_cycleRung φ hcyc hcyc4
  have hLK : ∀ x ∈ cycleRung φ hcyc, x ∈ K := cycleRung_subset_K φ hcyc
  -- reading the successor index
  have hnxt : ∀ i : ℕ, i + 1 < NN → nxt cy i = i + 1 := by
    intro i hi; rw [nxt, hcylen]; exact Nat.mod_eq_of_lt (by omega)
  have hnxtlast : nxt cy (NN - 1) = 0 := by
    rw [nxt, hcylen, show NN - 1 + 1 = NN by omega, Nat.mod_self]
  -- the three kinds of edge of the cycle
  have hedge0 : cycleEdge cy 0 (by omega) = s(c, xA) := by
    rw [cycleEdge_eq cy 0 (by omega) (nxt_lt (by omega)),
      SubdivisionCounting.getElem_eq_of_index_eq cy (hnxt 0 (by omega)) _ (by omega),
      hleft 0 (by omega) (by omega), hleft 1 (by omega) (by omega),
      SubdivisionCounting.getElem_eq_of_index_eq D (show j - 0 = j by omega) _ (by omega),
      hDj, hDjA]
  have hedgeL : cycleEdge cy (NN - 1) (by omega) = s(c, xB) := by
    rw [cycleEdge_eq cy (NN - 1) (by omega) (nxt_lt (by omega)),
      SubdivisionCounting.getElem_eq_of_index_eq cy hnxtlast _ (by omega),
      hlast (by omega), hleft 0 (by omega) (by omega),
      SubdivisionCounting.getElem_eq_of_index_eq D (show j - 0 = j by omega) _ (by omega),
      hDj, hDjB, Sym2.eq_swap]
  have hedgeQ : ∀ (i : ℕ) (hi : i + 1 < Q.length) (hm : j + i < cy.length),
      cycleEdge cy (j + i) hm = s(Q[i]'(by omega), Q[i + 1]'hi) := by
    intro i hi hm
    rw [cycleEdge_eq cy (j + i) hm (nxt_lt hm),
      SubdivisionCounting.getElem_eq_of_index_eq cy (hnxt (j + i) (by omega)) _ (by omega),
      hbranch i (by omega) hm,
      SubdivisionCounting.getElem_eq_of_index_eq cy (show j + i + 1 = j + (i + 1) by omega)
        (by omega) (by omega : j + (i + 1) < cy.length),
      hbranch (i + 1) hi (by omega)]
  -- reading the hole through the appearance
  have hphi : ∀ (i : ℕ) (hi' : i < cy.length) (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      cycleEdge cy i hi' = e → (cycleRung φ hcyc)[i]? = some (↑(φ ⟨e, he⟩) : V) := by
    intro i hi' e he heq
    have hi : i < (cycleRung φ hcyc).length := by rw [hLlen]; omega
    rw [List.getElem?_eq_getElem hi, cycleRung_getElem φ hcyc i hi hi']
    exact congrArg (fun t : ↥H.edgeSet => some (↑(φ t) : V)) (Subtype.ext heq)
  have hBedge : s(c, xB) ∈ H.edgeSet := hedgeL ▸ cycleEdge_mem hcyc (NN - 1) (by omega)
  have hL0 : (cycleRung φ hcyc)[0]? = some (↑(φ ⟨s(c, xA), hAedge⟩) : V) :=
    hphi 0 (by omega) _ hAedge hedge0
  have hLlast : (cycleRung φ hcyc)[NN - 1]? = some (↑(φ ⟨s(c, xB), hBedge⟩) : V) :=
    hphi (NN - 1) (by omega) _ hBedge hedgeL
  have hcy0 : cy[0]'(by omega) = c := by
    rw [hleft 0 (by omega) (by omega),
      SubdivisionCounting.getElem_eq_of_index_eq D (show j - 0 = j by omega) _ (by omega), hDj]
  -- the paper's *"a unique edge of `N(u)`"*
  have hother : ∀ x ∈ cycleRung φ hcyc, x ≠ (↑(φ ⟨s(c, xA), hAedge⟩) : V) → ¬ G.Adj p₁ x := by
    intro x hx hxa hadj
    obtain ⟨mm, hmm, rfl⟩ := List.mem_iff_getElem.mp hx
    have hmm' : mm < cy.length := by rw [hcylen]; rw [hLlen] at hmm; omega
    have hxK : ((cycleRung φ hcyc)[mm]'hmm) ∈ K := hLK _ (List.getElem_mem _)
    have hxN := first_adj_mem h hxK hadj
    rw [star_eq h c] at hxN
    obtain ⟨e₀, he₀, he₀c, heq⟩ := hxN
    have hval : ((cycleRung φ hcyc)[mm]'hmm)
        = (↑(φ ⟨cycleEdge cy mm hmm', cycleEdge_mem hcyc mm hmm'⟩) : V) :=
      cycleRung_getElem φ hcyc mm hmm hmm'
    have heq2 : cycleEdge cy mm hmm' = e₀ :=
      congrArg Subtype.val (φ.injective (Subtype.ext (hval.symm.trans heq)))
    have hcmem : c ∈ cycleEdge cy mm hmm' := by rw [heq2]; exact he₀c.2
    rw [cycleEdge_eq cy mm hmm' (nxt_lt hmm')] at hcmem
    have hnd := hcyc.2.1
    have hcase : mm = 0 ∨ nxt cy mm = 0 := by
      rcases Sym2.mem_iff.mp hcmem with hh | hh
      · exact Or.inl (hnd.getElem_inj_iff.mp (by rw [← hh, hcy0]))
      · exact Or.inr (hnd.getElem_inj_iff.mp (by rw [← hh, hcy0]))
    rcases hcase with hh | hh
    · subst hh
      rw [List.getElem?_eq_getElem hmm] at hL0
      exact hxa (Option.some_injective _ hL0)
    · have hmmlast : mm = NN - 1 := by
        rw [nxt, hcylen] at hh
        rcases Nat.lt_or_ge (mm + 1) NN with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at hh; omega
        · omega
      subst hmmlast
      rw [List.getElem?_eq_getElem hmm] at hLlast
      exact hBadj hBedge (Option.some_injective _ hLlast ▸ hadj)
  -- the first vertex lies in the star at `c`
  have haN : (↑(φ ⟨s(c, xA), hAedge⟩) : V) ∈ N c := by
    rw [star_eq h c]
    exact (image_mem_iff hAedge).mpr ⟨hAedge, Sym2.mem_mk_left c xA⟩
  have hhead : (cycleRung φ hcyc).head? = some (↑(φ ⟨s(c, xA), hAedge⟩) : V) := by
    rw [List.head?_eq_getElem?]; exact hL0
  -- locating the two marked vertices on the branch
  obtain ⟨e₁, he₁, he₁Q, hy₁eq⟩ := hy₁
  obtain ⟨e₂, he₂, he₂Q, hy₂eq⟩ := hy₂
  obtain ⟨i₁, hi₁, rfl⟩ := he₁Q
  obtain ⟨i₂, hi₂, rfl⟩ := he₂Q
  have hne12 : i₁ ≠ i₂ := by
    rintro rfl
    exact hy.ne (hy₁eq.trans hy₂eq.symm)
  have hadjline : H.lineGraph.Adj ⟨_, he₁⟩ ⟨_, he₂⟩ := by
    refine φ.map_rel_iff.mp ?_
    show G.Adj _ _
    simp only [Function.Embedding.coe_subtype]
    rw [← hy₁eq, ← hy₂eq]
    exact hy
  obtain ⟨-, v, hv1, hv2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hadjline
  have hcons := consecutive_of_meet hQ.1.2.1 hi₁ hi₂ hne12 ⟨v, hv1, hv2⟩
  have hb₁ : j + i₁ < cy.length := by omega
  have hb₂ : j + i₂ < cy.length := by omega
  have hval₁ : (cycleRung φ hcyc)[j + i₁]? = some y₁ := by
    rw [hy₁eq]; exact hphi (j + i₁) hb₁ _ he₁ (hedgeQ i₁ hi₁ hb₁)
  have hval₂ : (cycleRung φ hcyc)[j + i₂]? = some y₂ := by
    rw [hy₂eq]; exact hphi (j + i₂) hb₂ _ he₂ (hedgeQ i₂ hi₂ hb₂)
  rcases hcons with hcc | hcc
  · refine ⟨cycleRung φ hcyc, _, j + i₁, hLhole, hLK, hhead, haN, hAadj hAedge, hother,
      by omega, by omega, Or.inl ⟨hval₁, ?_⟩⟩
    rw [show j + i₁ + 1 = j + i₂ by omega]
    exact hval₂
  · refine ⟨cycleRung φ hcyc, _, j + i₂, hLhole, hLK, hhead, haN, hAadj hAedge, hother,
      by omega, by omega, Or.inr ⟨hval₂, ?_⟩⟩
    rw [show j + i₂ + 1 = j + i₁ by omega]
    exact hval₁

/-- **The hole of 5.8 (6).**  Same data as `exists_hole_unordered`, with the two marked
vertices now in the prescribed order. -/
theorem exists_hole
    (h : Context G m J n H K φ N F P p₁ p₂ c q)
    {Q D : List (Fin n)} {w₁ w₂ : Fin n} {j : ℕ} {xA xB : Fin n} {y₁ y₂ : V}
    (hQ : IsTrackFrom H Q w₁ w₂) (hQ2 : 2 ≤ Q.length)
    (hD : IsTrackFrom H D w₁ w₂) (hD3 : 3 ≤ D.length)
    (hdisj : ∀ z ∈ trackInterior D, z ∉ Q)
    (hj1 : 1 ≤ j) (hj2 : j + 1 < D.length)
    (hcj : D[j]? = some c) (hxA : D[j - 1]? = some xA) (hxB : D[j + 1]? = some xB)
    (hAedge : s(c, xA) ∈ H.edgeSet)
    (hAadj : ∀ he : s(c, xA) ∈ H.edgeSet, G.Adj p₁ (↑(φ ⟨s(c, xA), he⟩) : V))
    (hBadj : ∀ he : s(c, xB) ∈ H.edgeSet, ¬ G.Adj p₁ (↑(φ ⟨s(c, xB), he⟩) : V))
    (hy₁ : y₁ ∈ edgeImage φ (trackEdges Q)) (hy₂ : y₂ ∈ edgeImage φ (trackEdges Q))
    (hy : G.Adj y₁ y₂) :
    ∃ (L : List V) (a : V) (k : ℕ),
      IsHoleList G L ∧ (∀ x ∈ L, x ∈ K) ∧ L.head? = some a ∧
      a ∈ N c ∧ G.Adj p₁ a ∧ (∀ x ∈ L, x ≠ a → ¬ G.Adj p₁ x) ∧
      1 ≤ k ∧ k + 2 ≤ L.length ∧ L[k]? = some y₁ ∧ L[k + 1]? = some y₂ := by
  obtain ⟨L, a, k, h1, h2, h3, h4, h5, h6, h7, h8, hor⟩ :=
    exists_hole_unordered h hQ hQ2 hD hD3 hdisj hj1 hj2 hcj hxA hxB hAedge hAadj hBadj
      hy₁ hy₂ hy
  rcases hor with ⟨u1, u2⟩ | ⟨u1, u2⟩
  · exact ⟨L, a, k, h1, h2, h3, h4, h5, h6, h7, h8, u1, u2⟩
  · obtain ⟨k', hk1', hk2', hv1, hv2⟩ := mirror_swaps h7 h8 u1 u2
    have hL0 : L[0]? = some a := by rw [← List.head?_eq_getElem?]; exact h3
    refine ⟨mirror L, a, k', isHoleList_mirror h1, fun x hx => h2 x (mem_mirror.mp hx), ?_,
      h4, h5, fun x hx => h6 x (mem_mirror.mp hx), hk1', hk2', hv1, hv2⟩
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (by rw [mirror_length]; omega : 0 < (mirror L).length),
      mirror_getElem_zero L (by rw [mirror_length]; omega) (by omega)]
    rw [List.getElem?_eq_getElem (by omega : 0 < L.length)] at hL0
    exact hL0

end Workspace.ProofLemmas.Thm58StarBranchMixedHoleCycle
