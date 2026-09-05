import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.NoMajorVerticesGraphShape
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm84K4CaseDegenerate
import Workspace.ProofLemmas.Thm85EndgameNotions

/-!
# 8.5: two disjoint traversal edges force a degenerate `L(H)`

PAPER (printed pp. 43–44, in the proof of claim (4) of 8.5):

*"Suppose there is another, say `i'j'`.  Since `i'j'` meets all edges of `J` that share exactly
one end with `ij`, and `J` is 3-connected, it follows that `J = K₄` and the two edges `ij`,
`i'j'` are disjoint.  Moreover, the unique vertex of `R_{ii'}` in `X` is both `r_{ii'}` and
`r_{i'i}`, so `R_{ii'}` has length 0.  Similarly `R_{ij'}`, `R_{ji'}`, `R_{jj'}` all have length
0, and so `L(H)` is degenerate, contrary to (1)."*

The main theorem of this file, `disjoint_traversals_absurd`, is that sentence: if the two
bullets of claim (4) that place the ends of the rungs at `i` and at `j` next to `f₁` and `f_n`
hold for one edge `ij`, and a *full* traversal `ab` is disjoint from `ij`, then the four rungs
`R_ia`, `R_ib`, `R_ja`, `R_jb` have length `0`, `J = K₄` on `{i,j,a,b}`, and the line graph
formed by the choice is degenerate, contradicting claim (1).

The same sentence is what closes the uniqueness half of claim (4) and the "for any choice of
rungs there is an optimal choice with the same traversal" step of the closing paragraph, which
is why it is isolated here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgameK4Shape

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-! ## Two small graph facts -/

/-- A set closed under taking neighbours contains everything reachable from it. -/
theorem mem_of_walk {W : Type*} {Γ : SimpleGraph W} {T : Set W}
    (hT : ∀ x ∈ T, ∀ y : W, Γ.Adj x y → y ∈ T) :
    ∀ {x y : W}, Γ.Walk x y → x ∈ T → y ∈ T := by
  intro x y w
  induction w with
  | nil => exact id
  | cons hadj _ ih => exact fun hx => ih (hT _ hx _ hadj)

/-- A vertex of a 3-connected graph has more than two neighbours. -/
theorem not_two_neighbours [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3)
    (u p q : U) (hsub : ∀ w : U, J.Adj u w → w = p ∨ w = q) : False := by
  have hle : (J.neighborSet u).ncard ≤ ({p, q} : Set U).ncard :=
    Set.ncard_le_ncard (fun w hw => by rcases hsub w hw with h | h
                                       · exact Or.inl h
                                       · exact Or.inr h) (Set.toFinite _)
  have hpq : ({p, q} : Set U).ncard ≤ 2 := by
    refine le_trans (Set.ncard_insert_le _ _) ?_
    simp [Set.ncard_singleton]
  have := SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  omega

/-- In a 3-connected graph every vertex has a neighbour outside any prescribed pair. -/
theorem exists_adj_ne_two [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3) (a b c : U) :
    ∃ w : U, J.Adj a w ∧ w ≠ b ∧ w ≠ c := by
  classical
  by_contra hcon
  push_neg at hcon
  refine not_two_neighbours hJ a b c ?_
  intro w hw
  by_cases hb : w = b
  · exact Or.inl hb
  · exact Or.inr (hcon w hw hb)

/-- **"Hence `V(J) = {h,i,j,k}`"**: if the two ends of an edge of a 3-connected graph have all
their neighbours inside a fixed four-element set, then that set is all of `V(J)`.  Deleting the
other two vertices leaves a connected graph in which `i` and `j` see only each other. -/
theorem cover_of_hub_neighbourhoods [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {i j a b : U} (hia : i ≠ a) (hib : i ≠ b) (hja : j ≠ a) (hjb : j ≠ b)
    (hNi : ∀ w : U, J.Adj i w → w = j ∨ w = a ∨ w = b)
    (hNj : ∀ w : U, J.Adj j w → w = i ∨ w = a ∨ w = b) :
    ∀ c : U, c = i ∨ c = j ∨ c = a ∨ c = b := by
  classical
  intro c
  by_cases hca : c = a
  · exact Or.inr (Or.inr (Or.inl hca))
  by_cases hcb : c = b
  · exact Or.inr (Or.inr (Or.inr hcb))
  -- delete `a` and `b`
  have hpair : ({a, b} : Set U).ncard < 3 := by
    have := Set.ncard_insert_le a ({b} : Set U)
    rw [Set.ncard_singleton] at this
    omega
  have hconn := hJ.2 ({a, b} : Set U) hpair
  have hiT : i ∈ ({a, b} : Set U)ᶜ := by
    rintro (h | h)
    · exact hia h
    · exact hib h
  have hcT : c ∈ ({a, b} : Set U)ᶜ := by
    rintro (h | h)
    · exact hca h
    · exact hcb h
  set T : Set U := ({a, b} : Set U)ᶜ with hTdef
  set D : Set (↥T) := {x : ↥T | (x : U) = i ∨ (x : U) = j} with hDdef
  have hclosed : ∀ x ∈ D, ∀ y : ↥T, (J.induce T).Adj x y → y ∈ D := by
    intro x hx y hxy
    have hadj : J.Adj (x : U) (y : U) := hxy
    have hyT : (y : U) ∉ ({a, b} : Set U) := y.2
    rcases hx with hx | hx
    · rw [hx] at hadj
      rcases hNi _ hadj with h | h | h
      · exact Or.inr h
      · exact absurd (h ▸ Set.mem_insert _ _) hyT
      · exact absurd (h ▸ Set.mem_insert_of_mem _ rfl) hyT
    · rw [hx] at hadj
      rcases hNj _ hadj with h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ Set.mem_insert _ _) hyT
      · exact absurd (h ▸ Set.mem_insert_of_mem _ rfl) hyT
  obtain ⟨w⟩ := hconn.preconnected ⟨i, hiT⟩ ⟨c, hcT⟩
  have hmem : c = i ∨ c = j := mem_of_walk hclosed w (Or.inl rfl)
  rcases hmem with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- In `K₄` on `{h,i,j,k}`, an edge meeting each of `hj`, `hk`, `ij`, `ik` is `hi` or `jk`. -/
theorem edge_meeting_four {h i j k p q : U} (hnd : [h, i, j, k].Nodup)
    (hcover : ∀ c : U, c = h ∨ c = i ∨ c = j ∨ c = k) (hpq : p ≠ q)
    (d1 : h = p ∨ h = q ∨ j = p ∨ j = q) (d2 : h = p ∨ h = q ∨ k = p ∨ k = q)
    (d3 : i = p ∨ i = q ∨ j = p ∨ j = q) (d4 : i = p ∨ i = q ∨ k = p ∨ k = q) :
    (p = h ∧ q = i) ∨ (p = i ∧ q = h) ∨ (p = j ∧ q = k) ∨ (p = k ∧ q = j) := by
  have hd : h ≠ i ∧ h ≠ j ∧ h ≠ k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd
    tauto
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hd
  have e1' := e1.symm
  have e2' := e2.symm
  have e3' := e3.symm
  have e4' := e4.symm
  have e5' := e5.symm
  have e6' := e6.symm
  rcases hcover p with rfl | rfl | rfl | rfl <;> rcases hcover q with rfl | rfl | rfl | rfl <;>
    simp_all

/-! ## Rungs of length zero -/

/-- A rung with a vertex in `N_u ∩ N_v` has length `0`. -/
theorem zero_rung_of_common_end {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V}
    {N : U → Set V} {u v : U} {L : List V} (hL : IsUVRung G J S N u v L)
    {x : V} (hxL : x ∈ L) (hxu : x ∈ N u) (hxv : x ∈ N v) : pathLength L = 0 := by
  obtain ⟨-, s, t, hpath, -, hsN, htN⟩ := hL
  have hxs : x = s := (hsN x hxL).mp hxu
  have hxt : x = t := (htN x hxL).mp hxv
  have hst : s = t := hxs ▸ hxt
  have hpos : 0 < L.length := PathBasics.path_length_pos hpath.1
  have hfirst := PathBasics.getElem_zero_of_head? hpath.2.1 hpos
  have hlast := PathBasics.getElem_last_of_getLast? hpath.2.2 hpos
  have helem : L[0]'hpos = L[L.length - 1]'(by omega) := hfirst.trans (hst.trans hlast.symm)
  have hind : 0 = L.length - 1 := hpath.1.2.1.getElem_inj_iff.mp helem
  simp only [pathLength]
  omega

/-! ## The degenerate four-cycle -/

/-- **"Since `i'j'` meets all edges of `J` that share exactly one end with `ij`, and `J` is
3-connected, it follows that `J = K₄` … and so `L(H)` is degenerate, contrary to (1)"**
(printed pp. 43–44).

The pair `(i,j)` is only assumed to satisfy the first two bullets of claim (4) — that is enough
to make every rung at `i` or at `j` other than `R_ij` have a neighbour in `F` — while `(a,b)` is
a full traversal.  The third bullet of `(a,b)` then confines the neighbours of `i` and of `j` to
`{j,a,b}` and `{i,a,b}`, and the uniqueness clauses identify the two ends of each of the four
rungs `R_ia, R_ib, R_ja, R_jb`, so all four have length `0`. -/
theorem disjoint_traversals_absurd [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ Rc u v} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (R : U → U → List V) (hR : RungChoice G J S N R)
    (i j a b : U) (hnd : [i, j, a, b].Nodup) (hij : J.Adj i j)
    (hb1 : ∀ w : U, w ≠ j → J.Adj i w →
        ∃ r : V, r ∈ R i w ∧ r ∈ N i ∧ UniqueEdgeBetween G {x : V | x ∈ R i w} F r f₁)
    (hb2 : ∀ w : U, w ≠ i → J.Adj j w →
        ∃ r : V, r ∈ R j w ∧ r ∈ N j ∧ UniqueEdgeBetween G {x : V | x ∈ R j w} F r fn)
    (htrav : IsTraversal G J N F f₁ fn R a b) :
    False := by
  classical
  obtain ⟨hRfam, hRsym⟩ := hR
  have hab : J.Adj a b := htrav.1
  have hd : i ≠ j ∧ i ≠ a ∧ i ≠ b ∧ j ≠ a ∧ j ≠ b ∧ a ≠ b := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd
    tauto
  obtain ⟨hijne, hia, hib, hja, hjb, habne⟩ := hd
  -- the neighbours of `i` and of `j`
  have hNi : ∀ w : U, J.Adj i w → w = j ∨ w = a ∨ w = b := by
    intro w hiw
    by_cases hwj : w = j
    · exact Or.inl hwj
    by_cases hwa : w = a
    · exact Or.inr (Or.inl hwa)
    by_cases hwb : w = b
    · exact Or.inr (Or.inr hwb)
    exfalso
    obtain ⟨r, -, -, hu⟩ := hb1 w hwj hiw
    have hiwne : i ≠ w := hiw.ne
    have hnd2 : [i, w, a, b].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or]
      tauto
    exact htrav.2.2.2 i w hiw hnd2 r hu.1 f₁ hu.2.1 hu.2.2.1
  have hNj : ∀ w : U, J.Adj j w → w = i ∨ w = a ∨ w = b := by
    intro w hjw
    by_cases hwi : w = i
    · exact Or.inl hwi
    by_cases hwa : w = a
    · exact Or.inr (Or.inl hwa)
    by_cases hwb : w = b
    · exact Or.inr (Or.inr hwb)
    exfalso
    obtain ⟨r, -, -, hu⟩ := hb2 w hwi hjw
    have hjwne : j ≠ w := hjw.ne
    have hnd2 : [j, w, a, b].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        and_true, not_or]
      tauto
    exact htrav.2.2.2 j w hjw hnd2 r hu.1 fn hu.2.1 hu.2.2.1
  -- degrees force all four cross edges to be present
  have hiaAdj : J.Adj i a := by
    by_contra hcon
    refine not_two_neighbours hJ i j b ?_
    intro w hw
    rcases hNi w hw with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hw) hcon
    · exact Or.inr h
  have hibAdj : J.Adj i b := by
    by_contra hcon
    refine not_two_neighbours hJ i j a ?_
    intro w hw
    rcases hNi w hw with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h ▸ hw) hcon
  have hjaAdj : J.Adj j a := by
    by_contra hcon
    refine not_two_neighbours hJ j i b ?_
    intro w hw
    rcases hNj w hw with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hw) hcon
    · exact Or.inr h
  have hjbAdj : J.Adj j b := by
    by_contra hcon
    refine not_two_neighbours hJ j i a ?_
    intro w hw
    rcases hNj w hw with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h ▸ hw) hcon
  have hcover : ∀ c : U, c = i ∨ c = j ∨ c = a ∨ c = b :=
    cover_of_hub_neighbourhoods hJ hia hib hja hjb hNi hNj
  -- the four cross rungs have length zero
  have hz_ia : pathLength (R i a) = 0 := by
    obtain ⟨r, hrR, hrN, hu⟩ := hb1 a hja.symm hiaAdj
    obtain ⟨r', hr'R, hr'N, hu'⟩ := htrav.2.1 i hib hiaAdj.symm
    have hr'mem : r' ∈ R i a := by
      rw [hRsym i a hiaAdj, List.mem_reverse] at hr'R
      exact hr'R
    have hrr : r' = r := (hu.2.2.2 r' hr'mem f₁ hu'.2.1 hu'.2.2.1).1
    exact zero_rung_of_common_end (hRfam i a hiaAdj) hrR hrN (hrr ▸ hr'N)
  have hz_ib : pathLength (R i b) = 0 := by
    obtain ⟨r, hrR, hrN, hu⟩ := hb1 b hjb.symm hibAdj
    obtain ⟨r', hr'R, hr'N, hu'⟩ := htrav.2.2.1 i hia hibAdj.symm
    have hr'mem : r' ∈ R i b := by
      rw [hRsym i b hibAdj, List.mem_reverse] at hr'R
      exact hr'R
    have hrr : r' = r := (hu.2.2.2 r' hr'mem fn hu'.2.1 hu'.2.2.1).1
    exact zero_rung_of_common_end (hRfam i b hibAdj) hrR hrN (hrr ▸ hr'N)
  have hz_ja : pathLength (R j a) = 0 := by
    obtain ⟨r, hrR, hrN, hu⟩ := hb2 a hia.symm hjaAdj
    obtain ⟨r', hr'R, hr'N, hu'⟩ := htrav.2.1 j hjb hjaAdj.symm
    have hr'mem : r' ∈ R j a := by
      rw [hRsym j a hjaAdj, List.mem_reverse] at hr'R
      exact hr'R
    have hrr : r' = r := (hu.2.2.2 r' hr'mem f₁ hu'.2.1 hu'.2.2.1).1
    exact zero_rung_of_common_end (hRfam j a hjaAdj) hrR hrN (hrr ▸ hr'N)
  have hz_jb : pathLength (R j b) = 0 := by
    obtain ⟨r, hrR, hrN, hu⟩ := hb2 b hib.symm hjbAdj
    obtain ⟨r', hr'R, hr'N, hu'⟩ := htrav.2.2.1 j hja hjbAdj.symm
    have hr'mem : r' ∈ R j b := by
      rw [hRsym j b hjbAdj, List.mem_reverse] at hr'R
      exact hr'R
    have hrr : r' = r := (hu.2.2.2 r' hr'mem fn hu'.2.1 hu'.2.2.1).1
    exact zero_rung_of_common_end (hRfam j b hjbAdj) hrR hrN (hrr ▸ hr'N)
  have hz_aj : pathLength (R a j) = 0 := by
    rw [hRsym j a hjaAdj]
    simpa [pathLength] using hz_ja
  have hz_bi : pathLength (R b i) = 0 := by
    rw [hRsym i b hibAdj]
    simpa [pathLength] using hz_ib
  -- the choice forms a line graph, and that line graph is degenerate
  obtain ⟨n, H, hForms⟩ :=
    Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph G hG J hJ S N hSN R hRfam hRsym
  have hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := by
    refine NoMajorVerticesGraphShape.k4_of_two_hubs J hJ i j hij ?_ ?_
    · intro w hwi hwj
      rcases hcover w with h | h | h | h
      · exact absurd h hwi
      · exact absurd h hwj
      · subst h; exact ⟨hiaAdj.symm, hjaAdj.symm⟩
      · subst h; exact ⟨hibAdj.symm, hjbAdj.symm⟩
    · intro w hwi hwj x hx y hy
      have hx' : x = b ∨ x = a := by
        rcases hcover x with h | h | h | h
        · exact absurd h hx.2.1
        · exact absurd h hx.2.2
        · exact Or.inr h
        · exact Or.inl h
      have hy' : y = b ∨ y = a := by
        rcases hcover y with h | h | h | h
        · exact absurd h hy.2.1
        · exact absurd h hy.2.2
        · exact Or.inr h
        · exact Or.inl h
      rcases hcover w with h | h | h | h
      · exact absurd h hwi
      · exact absurd h hwj
      · subst h
        rcases hx' with hx1 | hx1
        · rcases hy' with hy1 | hy1
          · rw [hx1, hy1]
          · exact absurd (hy1 ▸ hy.1) (SimpleGraph.irrefl J)
        · exact absurd (hx1 ▸ hx.1) (SimpleGraph.irrefl J)
      · subst h
        rcases hx' with hx1 | hx1
        · exact absurd (hx1 ▸ hx.1) (SimpleGraph.irrefl J)
        · rcases hy' with hy1 | hy1
          · exact absurd (hy1 ▸ hy.1) (SimpleGraph.irrefl J)
          · rw [hx1, hy1]
  have hnd4 : [i, a, j, b].Nodup := by
    have haj : a ≠ j := hja.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or]
    tauto
  have hdegen : DegenerateAppearance J H :=
    Thm84K4CaseDegenerate.degenerate_of_zero_four_cycle hJ hSN hForms hK4 hnd4
      (fun u => by rcases hcover u with h | h | h | h
                   · exact Or.inl h
                   · exact Or.inr (Or.inr (Or.inl h))
                   · exact Or.inr (Or.inl h)
                   · exact Or.inr (Or.inr (Or.inr h)))
      hiaAdj hjaAdj.symm hjbAdj hibAdj.symm hz_ia hz_aj hz_jb hz_bi
  obtain ⟨-, hiso⟩ := hForms.2
  obtain ⟨phi⟩ := hiso
  exact (hclaim1 n H R _ phi rfl hForms).2 hK4 hdegen

end Workspace.ProofLemmas.Thm85EndgameK4Shape
