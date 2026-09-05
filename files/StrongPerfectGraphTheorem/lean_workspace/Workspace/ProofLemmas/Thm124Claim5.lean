import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.Thm124Setup
import Workspace.ProofLemmas.Thm124Claims
import Workspace.ProofLemmas.Thm124Claim4Finish
import Workspace.ProofLemmas.StaircaseStepBanisterOddPrism
import Workspace.ProofLemmas.StrongStaircaseCrossPair
import Workspace.ProofLemmas.Thm132Infrastructure
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S12.Thm_12_1
import Workspace.Statements.S12.Thm_12_3

/-!
# 12.4, claim (5)

PAPER (printed p. 75):

*"Every path in `G` from an `A`-complete vertex to a vertex with a neighbour
in `B ∪ C` contains either a vertex in `Q` or a `Q`-complete vertex."*

We choose a shortest counterexample.  Its first vertex is a left-star, and no
vertex of it lies in the strip.  Theorem 12.3 then gives a banister inside the
counterexample.  Claim (4) makes that banister long.  Roussel--Rubio applied to
the odd path obtained by closing it through a step supplies a crossed pair.
Adjoining that pair to the strip gives a larger staircase, against maximality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm124Claim5

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A counterexample to the assertion of claim (5), with its two ends named. -/
structure BadPath (G : SimpleGraph V) (A C B Q : Set V) (p : List V)
    (start finish : V) : Prop where
  path : IsPathFrom G p start finish
  startComplete : VertexComplete G start A
  finishAttached : ∃ z ∈ B ∪ C, G.Adj finish z
  avoids : ∀ w ∈ p, w ∉ Q ∧ ¬ VertexComplete G w Q

private theorem getElem_idx_eq {W : Type*} {l : List W} {i j : ℕ} (hij : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst hij
  rfl

private theorem two_le_length_of_ne_ends {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (huv : u ≠ v) : 2 ≤ p.length := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  by_contra hcon
  have hlen : p.length = 1 := by omega
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hn : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  apply huv
  rw [← h0, ← hn]
  apply hp.1.2.1.getElem_inj_iff.mpr
  omega

/-- A banister and a rung have only the two expected crossing edges. -/
private theorem banister_rung_edges {G : SimpleGraph V} {A C B : Set V}
    {u v a b : V} {p R : List V} (hp : IsBanister G A C B u p v)
    (hR : IsRungOfStrip G A C B a R b) :
    ∀ x ∈ p, ∀ y ∈ R,
      (G.Adj x y ↔ (x = u ∧ y = a) ∨ (x = v ∧ y = b)) := by
  intro x hx y hy
  have hyS := ProofAttempts.Thm124Claim4.rung_subset hR y hy
  constructor
  · intro hxy
    by_cases hxu : x = u
    · subst x
      refine Or.inl ⟨rfl, ?_⟩
      rcases hyS with (hyA | hyB) | hyC
      · exact hR.2.2.2.1 y hy hyA
      · exact absurd hxy (hp.2.2.1.2.2 y (Or.inl hyB))
      · exact absurd hxy (hp.2.2.1.2.2 y (Or.inr hyC))
    by_cases hxv : x = v
    · subst x
      refine Or.inr ⟨rfl, ?_⟩
      rcases hyS with (hyA | hyB) | hyC
      · exact absurd hxy (hp.2.2.2.1.2.2 y (Or.inl hyA))
      · exact hR.2.2.2.2.1 y hy hyB
      · exact absurd hxy (hp.2.2.2.1.2.2 y (Or.inr hyC))
    exact absurd hxy (hp.2.2.2.2 x
      ((PathBasics.mem_interior_iff_of_pathFrom hp.1).mpr ⟨hx, hxu, hxv⟩) y hyS)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hp.2.2.1.2.1 _ hR.2.1
    · exact hp.2.2.2.1.2.1 _ hR.2.2.1

/-- Closing a banister through an odd rung gives an even hole, so the
banister itself has odd length. -/
private theorem banister_odd {G : SimpleGraph V} (hG : Berge G) {A C B : Set V}
    {u v a b : V} {p R : List V} (hp : IsBanister G A C B u p v)
    (hS : StepConnected G A C B) (hR : IsRungOfStrip G A C B a R b)
    (hRodd : Odd (pathLength R)) :
    Odd (pathLength p) := by
  have hAB : Disjoint A B := hS.1.1
  have huv : u ≠ v := by
    obtain ⟨aA, haA⟩ : A.Nonempty := ⟨a, hR.2.1⟩
    intro he
    exact hp.2.2.2.1.2.2 aA (Or.inl haA) (he ▸ hp.2.2.1.2.1 aA haA)
  have hab : a ≠ b := by
    intro he
    exact Set.disjoint_left.mp hAB hR.2.1 (he ▸ hR.2.2.1)
  have hp2 : 2 ≤ p.length := two_le_length_of_ne_ends hp.1 huv
  have hR2 : 2 ≤ R.length := two_le_length_of_ne_ends hR.1 hab
  have hdisj : ∀ x ∈ p, x ∉ R := by
    intro x hxp hxR
    exact hp.2.1 x hxp (ProofAttempts.Thm124Claim4.rung_subset hR x hxR)
  have hcross : ∀ x ∈ p, ∀ y ∈ R.reverse,
      (G.Adj x y ↔ (x = v ∧ y = b) ∨ (x = u ∧ y = a)) := by
    intro x hx y hy
    rw [banister_rung_edges hp hR x hx y (List.mem_reverse.mp hy)]
    tauto
  have hhole : IsHoleList G (p ++ R.reverse) :=
    PathGlue.glue_hole hp.1 (PathBasics.isPathFrom_reverse hR.1)
      (fun x hx hxR => hdisj x hx (List.mem_reverse.mp hxR)) hcross (by simp; omega)
  have heven := hG.1 _ hhole
  have hpEq := PathBasics.pathLength_eq p
  have hREq := PathBasics.pathLength_eq R
  have hlen : holeLength (p ++ R.reverse) = p.length + R.length := by
    simp [holeLength]
  rw [hlen] at heven
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff] at hRodd ⊢
  omega

/-- An `A`-complete vertex of a bad path is the left-star from which 12.3
starts. -/
private theorem start_is_leftStar {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q)
    {x : V} (hxA : VertexComplete G x A) (hxQ : x ∉ Q)
    (hxnc : ¬ VertexComplete G x Q) : IsLeftStar G A C B x := by
  have hxswap : x ∉ B ∪ A ∪ C :=
    Thm132Infrastructure.bComplete_not_mem_strip
      (Thm124Setup.Setup.swap h).stepConnected hxA
  have hxS : x ∉ A ∪ B ∪ C := by
    simpa [Set.union_comm A B] using hxswap
  by_cases hxa₀ : x = a₀
  · simpa [hxa₀] using h.leftStar
  have hxR : x ∉ R₀ := by
    intro hxR
    by_cases hxb₀ : x = b₀
    · obtain ⟨a, ha⟩ := h.stepConnected.2.1.1
      exact h.rightStar.2.2 a (Or.inl ha) (hxb₀ ▸ hxA a ha)
    · have hxint : x ∈ SPGT.interior R₀ :=
        (PathBasics.mem_interior_iff_of_pathFrom h.pathFrom).mpr ⟨hxR, hxa₀, hxb₀⟩
      obtain ⟨a, ha⟩ := h.stepConnected.2.1.1
      exact h.interiorAnti x hxint a (Or.inl (Or.inl ha)) (hxA a ha)
  have hxK : x ∉ staircaseVertices A C B R₀ := fun hx => hx.elim hxR hxS
  have hnmaj : ¬ MajorForStaircase G A C B a₀ R₀ b₀ x := by
    intro hmaj
    exact (Thm124Claims.claim3 h x hmaj).elim hxQ hxnc
  obtain ⟨i, hi, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1
    G h.berge h.noK4 h.noPrism h.noBreaker A C B a₀ b₀ R₀ h.maximal x hxK
  fin_cases i
  · exact hi.2.1.resolve_right (not_not_intro hxA)
  · exact (hnmaj hi.1).elim
  · rcases hi with hl | hr
    · exact hl.1
    · obtain ⟨a, ha⟩ := h.stepConnected.2.1.1
      exact (hr.1.2.2 a (Or.inl ha) (hxA a ha)).elim

/-- **12.4(5).** Every path from an `A`-complete vertex to a vertex attached
to `B ∪ C` meets `Q` or a `Q`-complete vertex. -/
theorem claim5 {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) :
    ∀ (p : List V) (u v : V), IsPathFrom G p u v → VertexComplete G u A →
      (∃ z ∈ B ∪ C, G.Adj v z) →
      ∃ w ∈ p, w ∈ Q ∨ VertexComplete G w Q := by
  classical
  intro p₀ u₀ v₀ hp₀ hu₀ hv₀
  by_contra hgoal
  have hav₀ : ∀ w ∈ p₀, w ∉ Q ∧ ¬ VertexComplete G w Q := by
    intro w hw
    constructor
    · intro hwQ
      exact hgoal ⟨w, hw, Or.inl hwQ⟩
    · intro hwQ
      exact hgoal ⟨w, hw, Or.inr hwQ⟩
  have hbad₀ : BadPath G A C B Q p₀ u₀ v₀ := ⟨hp₀, hu₀, hv₀, hav₀⟩

  -- PAPER: choose a counterexample with the fewest vertices.
  have hex : ∃ n : ℕ, ∃ (p : List V) (u v : V),
      p.length = n ∧ BadPath G A C B Q p u v :=
    ⟨p₀.length, p₀, u₀, v₀, rfl, hbad₀⟩
  set n : ℕ := Nat.find hex with hn
  obtain ⟨p, u, v, hplen, hp⟩ := Nat.find_spec hex
  have hmin : ∀ (p' : List V) (u' v' : V), BadPath G A C B Q p' u' v' →
      p.length ≤ p'.length := by
    intro p' u' v' hp'
    by_contra hlt
    exact Nat.find_min hex (m := p'.length) (by omega) ⟨p', u', v', rfl, hp'⟩
  have hpPos : 0 < p.length := PathBasics.path_length_pos hp.path.1
  have hp0 : p[0]'hpPos = u :=
    PathBasics.getElem_zero_of_head? hp.path.2.1 hpPos

  -- No term lies in `A ∪ B`, since claim (2) makes those vertices
  -- `Q`-complete.
  have hpNoAB : ∀ w ∈ p, w ∉ A ∪ B := by
    intro w hw hwAB
    exact (hp.avoids w hw).2 (Thm124Claims.claim2 h w hwAB)

  -- No term lies in `C`.  Otherwise the prefix ending just before its first
  -- displayed occurrence is a shorter bad path, because that endpoint sees
  -- the `C`-vertex.
  have hpNoC : ∀ w ∈ p, w ∉ C := by
    intro w hw hwC
    obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.mp hw
    have hi0 : 0 < i := by
      by_contra hzero
      have hiEq : i = 0 := by omega
      have hwstart : w = u := by
        rw [← hiw, getElem_idx_eq hiEq hi hpPos, hp0]
      have hstartOut := Thm132Infrastructure.bComplete_not_mem_strip
        (Thm124Setup.Setup.swap h).stepConnected hp.startComplete
      exact hstartOut (by
        rw [← hwstart]
        exact Or.inr hwC)
    let j : ℕ := i - 1
    have hj : j < p.length := by dsimp [j]; omega
    have hj1 : j + 1 = i := by dsimp [j]; omega
    set r : List V := (p.drop 0).take (j - 0 + 1) with hrdef
    have hrlen : r.length = j + 1 := by
      rw [hrdef, PathBasics.length_slice p (by omega) hj]
      omega
    have hrfrom : IsPathFrom G r u (p[j]'hj) := by
      by_cases hj0 : j = 0
      ·
        have hrone : r = [p[0]'hpPos] := by
          rw [hrdef]
          simp [hj0]
          rw [List.take_one, hp.path.2.1]
          simp [← hp0]
        rw [hrone, hp0]
        refine ⟨PathBasics.isPathList_singleton G u, rfl, ?_⟩
        · simp only [List.getLast?_singleton, Option.some.injEq]
          rw [getElem_idx_eq hj0 hj hpPos, hp0]
      · have hs := PathBasics.isPathFrom_slice hp.path.1 (show 0 < j by omega) hj
        rw [getElem_idx_eq (show (0 : ℕ) = 0 by rfl) (by omega) hpPos, hp0] at hs
        simpa [hrdef] using hs
    have hadj' : G.Adj (p[j]'hj) w := by
      have hs := PathBasics.path_adj_succ hp.path.1 (i := j) (by omega)
      rw [getElem_idx_eq hj1 (by omega) hi] at hs
      rwa [hiw] at hs
    have hrsub : ∀ z ∈ r, z ∈ p := by
      intro z hz
      obtain ⟨k, hk, -, -, rfl⟩ := (PathBasics.mem_slice_iff p (by omega) hj).mp hz
      exact List.getElem_mem hk
    have hrbad : BadPath G A C B Q r u (p[j]'hj) := by
      refine ⟨hrfrom, hp.startComplete,
        ⟨w, Or.inr hwC, hadj'⟩, ?_⟩
      intro z hz
      exact hp.avoids z (hrsub z hz)
    have := hmin r u (p[j]'hj) hrbad
    omega

  have hpOutside : ∀ w ∈ p, w ∉ A ∪ B ∪ C := by
    intro w hw hwS
    rcases hwS with hwAB | hwC
    · exact hpNoAB w hw hwAB
    · exact hpNoC w hw hwC
  have hpNoMajor : ∀ w ∈ p, ¬ MajorForStaircase G A C B a₀ R₀ b₀ w := by
    intro w hw hmaj
    exact (Thm124Claims.claim3 h w hmaj).elim (hp.avoids w hw).1 (hp.avoids w hw).2
  have hstartStar : IsLeftStar G A C B u :=
    start_is_leftStar h hp.startComplete (hp.avoids u
      (PathBasics.head_mem hp.path.2.1)).1 (hp.avoids u
        (PathBasics.head_mem hp.path.2.1)).2

  -- Apply 12.3 to the vertex set of the shortest path.
  set F : Set V := {w : V | w ∈ p} with hFdef
  have hFsub : F ⊆ (A ∪ B ∪ C)ᶜ := by
    intro w hw
    exact hpOutside w hw
  have hFconn : ConnectedSet G F := by
    simpa [hFdef] using
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp.path.1)
  have hFstar : ∃ w ∈ F, IsLeftStar G A C B w :=
    ⟨u, PathBasics.head_mem hp.path.2.1, hstartStar⟩
  have hFatt : (attachments G F (B ∪ C)).Nonempty := by
    obtain ⟨z, hz, hvz⟩ := hp.finishAttached
    exact ⟨z, hz, v, PathBasics.getLast_mem hp.path.2.2, hvz.symm⟩
  rcases Workspace.Statements.S12.SPGT.thm_12_3 G h.berge h.noK4 h.noPrism h.noBreaker
      A C B a₀ b₀ R₀ h.maximal F hFsub hFconn hFstar hFatt with
    ⟨w, hwF, hwmaj⟩ | ⟨u, v, R, hRF, hban⟩
  · exact hpNoMajor w hwF hwmaj

  have hRavoid : ∀ w ∈ R, w ∉ Q ∧ ¬ VertexComplete G w Q := by
    intro w hw
    exact hp.avoids w (hRF w hw)
  have huvne : u ≠ v := by
    obtain ⟨a, ha⟩ := h.stepConnected.2.1.1
    intro he
    exact hban.2.2.2.1.2.2 a (Or.inl ha) (he ▸ hban.2.2.1.2.1 a ha)
  have hRlen2 : 2 ≤ R.length := two_le_length_of_ne_ends hban.1 huvne
  have hRnotone : pathLength R ≠ 1 := by
    intro hlen
    have huv : G.Adj u v := PathBasics.isPathFrom_ends_adj_of_length_one hban.1 hlen
    rcases Thm124Claim4Finish.claim4 h huv hban.2.2.1 hban.2.2.2.1 with huQ | hvQ
    · exact (hRavoid u (PathBasics.head_mem hban.1.2.1)).2 huQ
    · exact (hRavoid v (PathBasics.getLast_mem hban.1.2.2)).2 hvQ
  have hRlen : 2 ≤ pathLength R := by
    rw [PathBasics.pathLength_eq] at hRnotone ⊢
    omega

  -- Fix a step.  Its first rung has odd length by the prism parity lemma.
  obtain ⟨a, haA⟩ := h.stepConnected.2.1.1
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, -⟩ :=
    h.stepConnected.2.2.2.1 a (Or.inl (Or.inl haA))
  obtain ⟨-, -, hR₁odd, -⟩ :=
    StaircaseStepBanisterOddPrism.staircaseStepBanisterOddPrism
      G A C B a₀ b₀ a₁ b₁ a₂ b₂ R₀ R₁ R₂ h.staircase hstep h.berge h.noPrism
  have hRodd : Odd (pathLength R) :=
    banister_odd h.berge hban h.stepConnected hstep.1 hR₁odd
  have hRlen3 : 3 ≤ pathLength R := by
    obtain ⟨k, hk⟩ := hRodd
    omega

  have ha₁A : a₁ ∈ A := hstep.1.2.1
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have ha₂A : a₂ ∈ A := hstep.2.1.2.1
  have hb₂B : b₂ ∈ B := hstep.2.1.2.2.1
  have ha₁R₁ : a₁ ∈ R₁ := PathBasics.head_mem hstep.1.1.2.1
  have hb₂R₂ : b₂ ∈ R₂ := PathBasics.getLast_mem hstep.2.1.1.2.2
  have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
    intro hadj
    rcases (hstep.2.2.2 a₁ ha₁R₁ b₂ hb₂R₂).mp hadj with hcase | hcase
    · exact (Set.disjoint_left.mp h.stepConnected.1.1 ha₂A) (hcase.2 ▸ hb₂B)
    · exact (Set.disjoint_left.mp h.stepConnected.1.1 (hcase.1 ▸ ha₁A)) hb₁B
  have ha₁b₂ne : a₁ ≠ b₂ := fun he =>
    Set.disjoint_left.mp h.stepConnected.1.1 ha₁A (he ▸ hb₂B)
  have ha₁R : a₁ ∉ R := fun hm => hban.2.1 a₁ hm (Or.inl (Or.inl ha₁A))
  have hb₂R : b₂ ∉ R := fun hm => hban.2.1 b₂ hm (Or.inl (Or.inr hb₂B))
  have hlong : IsPathFrom G (a₁ :: (R ++ [b₂])) a₁ b₂ := by
    refine PathAttach.isPathFrom_cons_concat hban.1
      (hban.2.2.1.2.1 a₁ ha₁A).symm
      (hban.2.2.2.1.2.1 b₂ hb₂B).symm ha₁b₂ ha₁b₂ne
      ha₁R hb₂R ?_ ?_
    · intro z hz hzu hadj
      by_cases hzv : z = v
      · exact hban.2.2.2.1.2.2 a₁ (Or.inl ha₁A) (hzv ▸ hadj.symm)
      · exact hban.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr ⟨hz, hzu, hzv⟩)
          a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
    · intro z hz hzv hadj
      by_cases hzu : z = u
      · exact hban.2.2.1.2.2 b₂ (Or.inl hb₂B) (hzu ▸ hadj.symm)
      · exact hban.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr ⟨hz, hzu, hzv⟩)
          b₂ (Or.inl (Or.inr hb₂B)) hadj.symm
  have hlongLen : (a₁ :: (R ++ [b₂])).length = R.length + 2 := by simp
  have hlongPL : pathLength (a₁ :: (R ++ [b₂])) = pathLength R + 2 := by
    rw [PathAttach.pathLength_cons_append_singleton, PathBasics.pathLength_eq]
    omega
  have hlongOdd : Odd (pathLength (a₁ :: (R ++ [b₂]))) := by
    rw [hlongPL]
    exact hRodd.add_even (by simp)
  have hlong5 : 5 ≤ pathLength (a₁ :: (R ++ [b₂])) := by omega
  have hlongQ : ∀ w ∈ a₁ :: (R ++ [b₂]), w ∉ Q := by
    intro w hw
    rw [PathAttach.mem_cons_append_singleton] at hw
    rcases hw with hwa | hw | hwb
    · exact h.notMemQ_of_memStrip w (Or.inl (Or.inl (hwa ▸ ha₁A)))
    · exact (hRavoid w hw).1
    · exact h.notMemQ_of_memStrip w (Or.inl (Or.inr (hwb ▸ hb₂B)))
  have ha₁Q : VertexComplete G a₁ Q := Thm124Claims.claim2 h a₁ (Or.inl ha₁A)
  have hb₂Q : VertexComplete G b₂ Q := Thm124Claims.claim2 h b₂ (Or.inr hb₂B)
  have honly : ∀ w ∈ a₁ :: (R ++ [b₂]), VertexComplete G w Q →
      w = a₁ ∨ w = b₂ := by
    intro w hw hwQ
    rw [PathAttach.mem_cons_append_singleton] at hw
    rcases hw with rfl | hw | rfl
    · exact Or.inl rfl
    · exact absurd hwQ (hRavoid w hw).2
    · exact Or.inr rfl
  have hnoedge : ¬ ∃ x ∈ a₁ :: (R ++ [b₂]), ∃ y ∈ a₁ :: (R ++ [b₂]),
      EdgeComplete G Q x y := by
    rintro ⟨x, hx, y, hy, hxy, hxQ, hyQ⟩
    rcases honly x hx hxQ with rfl | rfl <;> rcases honly y hy hyQ with rfl | rfl
    · exact G.irrefl hxy
    · exact ha₁b₂ hxy
    · exact ha₁b₂ hxy.symm
    · exact G.irrefl hxy

  rcases Workspace.Statements.S02.SPGT.thm_2_1 G h.berge Q h.anticonnQ
      (a₁ :: (R ++ [b₂])) a₁ b₂ hlong hlongQ hlongOdd ha₁Q hb₂Q with
    hedge | hleapcase | hshort
  · exact hnoedge hedge
  · obtain ⟨-, aa, haaQ, bb, hbbQ, hleap⟩ := hleapcase
    have hP1lt : (1 : ℕ) < (a₁ :: (R ++ [b₂])).length := by omega
    have hPRlt : R.length < (a₁ :: (R ++ [b₂])).length := by omega
    have hRpos : 0 < R.length := by omega
    have hRu : R[0]'hRpos = u := PathBasics.getElem_zero_of_head? hban.1.2.1 hRpos
    have hRv : R[R.length - 1]'(by omega) = v :=
      PathBasics.getElem_last_of_getLast? hban.1.2.2 hRpos
    have hP1 : (a₁ :: (R ++ [b₂]))[1]'hP1lt = u := by
      rw [getElem_idx_eq (show (1 : ℕ) = 0 + 1 by omega) hP1lt (by omega),
        List.getElem_cons_succ, List.getElem_append_left hRpos, hRu]
    have hPv : (a₁ :: (R ++ [b₂]))[R.length]'hPRlt = v := by
      rw [getElem_idx_eq (show R.length = (R.length - 1) + 1 by omega) hPRlt (by omega),
        List.getElem_cons_succ, List.getElem_append_left (show R.length - 1 < R.length by omega),
        hRv]
    have haau : G.Adj aa u := by
      have := (hleap.2.2.2.2.1 1 hP1lt).mpr (Or.inr (Or.inl rfl))
      rwa [hP1] at this
    have haav : ¬ G.Adj aa v := by
      intro hadj
      rw [← hPv] at hadj
      rcases (hleap.2.2.2.2.1 R.length hPRlt).mp hadj with hcase | hcase | hcase <;>
        omega
    have hbbu : ¬ G.Adj bb u := by
      intro hadj
      rw [← hP1] at hadj
      rcases (hleap.2.2.2.2.2 1 hP1lt).mp hadj with hcase | hcase | hcase <;>
        omega
    have hbbv : G.Adj bb v := by
      have := (hleap.2.2.2.2.2 R.length hPRlt).mpr (Or.inr (Or.inl (by omega)))
      rwa [hPv] at this
    have haaInt : ∀ z ∈ SPGT.interior R, ¬ G.Adj aa z := by
      intro z hz hadj
      obtain ⟨k, hk, hk1, hk2, hkz⟩ :=
        PathBasics.exists_getElem_of_mem_interior hban.1.1 hz
      have hPk : k + 1 < (a₁ :: (R ++ [b₂])).length := by omega
      have hEq : (a₁ :: (R ++ [b₂]))[k + 1]'hPk = z := by
        rw [List.getElem_cons_succ, List.getElem_append_left hk, hkz]
      rw [← hEq] at hadj
      rcases (hleap.2.2.2.2.1 (k + 1) hPk).mp hadj with hcase | hcase | hcase <;>
        omega
    have hbbInt : ∀ z ∈ SPGT.interior R, ¬ G.Adj bb z := by
      intro z hz hadj
      obtain ⟨k, hk, hk1, hk2, hkz⟩ :=
        PathBasics.exists_getElem_of_mem_interior hban.1.1 hz
      have hPk : k + 1 < (a₁ :: (R ++ [b₂])).length := by omega
      have hEq : (a₁ :: (R ++ [b₂]))[k + 1]'hPk = z := by
        rw [List.getElem_cons_succ, List.getElem_append_left hk, hkz]
      rw [← hEq] at hadj
      rcases (hleap.2.2.2.2.2 (k + 1) hPk).mp hadj with hcase | hcase | hcase <;>
        omega
    have haaComp : VertexComplete G aa (A ∪ B) := by
      intro z hz
      rcases hz with hzA | hzB
      · exact (Thm124Claims.claim2 h z (Or.inl hzA) aa haaQ).symm
      · exact (Thm124Claims.claim2 h z (Or.inr hzB) aa haaQ).symm
    have hbbComp : VertexComplete G bb (A ∪ B) := by
      intro z hz
      rcases hz with hzA | hzB
      · exact (Thm124Claims.claim2 h z (Or.inl hzA) bb hbbQ).symm
      · exact (Thm124Claims.claim2 h z (Or.inr hzB) bb hbbQ).symm
    have hstairR : IsStaircase G A C B u R v := ⟨h.stepConnected, hban, hRlen3⟩
    have haaK : aa ∉ staircaseVertices A C B R := by
      rintro (haaR | haaS)
      · exact (hRavoid aa haaR).1 haaQ
      · exact h.outsideQ aa haaQ (Or.inr haaS)
    have hbbK : bb ∉ staircaseVertices A C B R := by
      rintro (hbbR | hbbS)
      · exact (hRavoid bb hbbR).1 hbbQ
      · exact h.outsideQ bb hbbQ (Or.inr hbbS)
    have hnew := StrongStaircaseCrossPair.staircase_adjoin_cross_pair
      G A C B u v R aa bb hstairR haaK hbbK hleap.2.2.1 hleap.2.2.2.1
      haaComp hbbComp haau haav hbbu hbbv haaInt hbbInt
    apply h.maximal.2
    refine ⟨A ∪ {aa}, C, B ∪ {bb}, u, R, v, hnew,
      Set.subset_union_left, Set.subset_union_left, Set.Subset.rfl, ?_⟩
    have hsub : A ∪ B ∪ C ⊆ (A ∪ {aa}) ∪ (B ∪ {bb}) ∪ C := by
      intro z hz
      rcases hz with (hzA | hzB) | hzC
      · exact Or.inl (Or.inl (Or.inl hzA))
      · exact Or.inl (Or.inr (Or.inl hzB))
      · exact Or.inr hzC
    apply (Set.ssubset_iff_of_subset hsub).2
    refine ⟨aa, Or.inl (Or.inl (Or.inr rfl)), ?_⟩
    exact fun haaS => h.outsideQ aa haaQ (Or.inr haaS)
  · exact (by obtain ⟨h3, -⟩ := hshort; omega)

end Workspace.ProofLemmas.Thm124Claim5
