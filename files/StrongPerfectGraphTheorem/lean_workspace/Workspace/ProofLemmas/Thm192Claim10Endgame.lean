import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.Thm192Claim4
import Workspace.ProofLemmas.Thm192Claim9
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm232ClosingCompletePair
import Workspace.Statements.S02.Thm_2_10

/-!
# The wheel/path/leap endgame of claim (10) of 19.2

PAPER (printed p. 122), the tail of the proof of claim (10):

> *"So `x₀` is adjacent to `f`, and therefore `x₁` is nonadjacent to both `x₂,f`.  By (8)
> `x₂` is adjacent to `y`, and therefore not `Y₀`-complete.  By (2) `z` is `Y₀`-complete and
> `(C,Y₀)` is a wheel.  Let `x₂-q₁-⋯-q_k-x₁` be a path between `x₁,x₂` with interior in `A`
> (so `f = q₁`) and let `C₁` be the hole `z-x₂-q₁-⋯-q_k-x₁-z`.  From (9),
> `A = {q₁,…,q_k}`.  Since `q_k = pₙ` and `z` is `Y`-complete, it follows from (4) that
> `q_k` is not `Y`-complete.  Since `(C₁,Y)` is not an odd wheel, it follows that `(C₁,Y)`
> is not a wheel, and so `z,x₁` are the only `Y`-complete vertices in `C₁`, by 2.3.  By
> 2.10, `Y` contains a leap or hat for `C₁`.  But `y` is adjacent to `x₂`, and all other
> vertices of `Y` have at least two neighbours in `{p₁,…,pₙ}`, which is a subset of
> `{q₁,…,q_k}`, a contradiction."*

Encoding notes.

* The hole `C₁` is written here with the `Y`-complete edge `x₁z` at its front, i.e. as the
  list `x₁ :: z :: S` where `S = x₂-q₁-⋯-q_k`.  That is the shape in which
  `Thm232ClosingCompletePair.pair_segment` recognises `{x₁,z}` as a `Y`-segment and
  `Thm232ClosingCompletePair.only_pair` turns *"`(C₁,Y)` is not an odd wheel"* into
  *"`z,x₁` are the only `Y`-complete vertices"* through 2.3.
* *"`q_k = pₙ`"* is justified here rather than assumed: claim (9), applied to the vertex set
  of `S` minus `x₂`, shows that this set is all of `A`, and then `q_k` is the **unique**
  neighbour of `x₁` in `A` because `S` is an induced path ending at `x₁`'s only rim
  neighbour.  Hence `pₙ ∈ A`, being a neighbour of `x₁`, equals `q_k`.
* *"all other vertices of `Y` have at least two neighbours in `{p₁,…,pₙ}`"* is the second
  conjunct of `hchoice`'s right disjunct: two distinct `Y₀`-complete vertices `c ≠ d` in
  `interior P ⊆ A`.  A hub vertex of a leap has at most **one** neighbour in the rim
  interior, which is what kills both leap orientations; `y` itself is excluded because it
  is adjacent to `x₂`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim10Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Unpacking a leap for a hole

Copied from the (private) helper of `Thm192Claim11`: `IsLeapForHole G c u v a b` is stated
through an unnamed rotation of `c`, and all the printed argument uses is *"`a`'s hole
neighbours are `u`, `v` and the neighbour `s` of `v` other than `u`; `b`'s are `u`, `v` and
the neighbour `t` of `u` other than `v`"*. -/
theorem leap_pair {G : SimpleGraph V} {C : List V} {u v a b : V}
    (hleap : IsLeapForHole G C u v a b) (ha : a ∉ C) (hb : b ∉ C) :
    ∃ s t : V,
      s ∈ C ∧ G.Adj v s ∧ s ≠ u ∧ s ≠ v ∧
      t ∈ C ∧ G.Adj u t ∧ t ≠ u ∧ t ≠ v ∧
      (∀ w ∈ C, G.Adj a w → w = u ∨ w = v ∨ w = s) ∧
      (∀ w ∈ C, G.Adj b w → w = u ∨ w = v ∨ w = t) ∧
      a ≠ b ∧ ¬ G.Adj a b := by
  obtain ⟨hC, i, hhd, hlst, hlp⟩ := hleap
  obtain ⟨hpath, hlen2, hab, hnadj, hA, hB⟩ := hlp
  have hrlen : (C.rotate i).length = C.length := List.length_rotate ..
  have hn4 : 4 ≤ (C.rotate i).length := by rw [hrlen]; exact hC.1
  have hpos : 0 < (C.rotate i).length := by omega
  have hr0 : (C.rotate i)[0]'(by omega) = v :=
    PathBasics.getElem_zero_of_head? hhd hpos
  have hrn : (C.rotate i)[(C.rotate i).length - 1]'(by omega) = u :=
    PathBasics.getElem_last_of_getLast? hlst hpos
  have hmemr : ∀ w : V, w ∈ C.rotate i ↔ w ∈ C := fun w => List.mem_rotate
  have huC : u ∈ C := (hmemr u).mp (by rw [← hrn]; exact List.getElem_mem _)
  have hvC : v ∈ C := (hmemr v).mp (by rw [← hr0]; exact List.getElem_mem _)
  have hau : a ≠ u := fun h => ha (h ▸ huC)
  have hav : a ≠ v := fun h => ha (h ▸ hvC)
  have hbu : b ≠ u := fun h => hb (h ▸ huC)
  have hbv : b ≠ v := fun h => hb (h ▸ hvC)
  have hdelA : ∀ w : V, ((G.deleteEdges {s(u, v)}).Adj a w ↔ G.Adj a w) := by
    intro w
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · exact fun h => h.1
    · refine fun h => ⟨h, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hau h1
      · exact hav h1
  have hdelB : ∀ w : V, ((G.deleteEdges {s(u, v)}).Adj b w ↔ G.Adj b w) := by
    intro w
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · exact fun h => h.1
    · refine fun h => ⟨h, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hbu h1
      · exact hbv h1
  refine ⟨(C.rotate i)[1]'(by omega), (C.rotate i)[(C.rotate i).length - 2]'(by omega),
    (hmemr _).mp (List.getElem_mem _), ?_, ?_, ?_,
    (hmemr _).mp (List.getElem_mem _), ?_, ?_, ?_, ?_, ?_, hab, ?_⟩
  · have h := PathBasics.path_adj_succ hpath (i := 0) (by omega)
    have h' := (SimpleGraph.deleteEdges_adj.mp h).1
    rw [← hr0]
    exact h'
  · intro hcon
    rw [← hrn] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · intro hcon
    rw [← hr0] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · have h := PathBasics.path_adj_succ hpath (i := (C.rotate i).length - 2) (by omega)
    have h' := (SimpleGraph.deleteEdges_adj.mp h).1
    have hidx : (C.rotate i)[(C.rotate i).length - 2 + 1]'(by omega)
        = (C.rotate i)[(C.rotate i).length - 1]'(by omega) :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rw [hidx, hrn] at h'
    exact h'.symm
  · intro hcon
    rw [← hrn] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · intro hcon
    rw [← hr0] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · intro w hw hadj
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem ((hmemr w).mpr hw)
    have hiff := hA j hj
    rw [hjw] at hiff
    have := hiff.mp ((hdelA w).mpr hadj)
    rcases this with h | h | h
    · subst h
      refine Or.inr (Or.inl ?_)
      rw [← hjw, ← hr0]
    · subst h
      refine Or.inr (Or.inr ?_)
      rw [← hjw]
    · subst h
      refine Or.inl ?_
      rw [← hjw, ← hrn]
  · intro w hw hadj
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem ((hmemr w).mpr hw)
    have hiff := hB j hj
    rw [hjw] at hiff
    have := hiff.mp ((hdelB w).mpr hadj)
    rcases this with h | h | h
    · subst h
      refine Or.inr (Or.inl ?_)
      rw [← hjw, ← hr0]
    · subst h
      refine Or.inr (Or.inr ?_)
      rw [← hjw]
    · subst h
      refine Or.inl ?_
      rw [← hjw, ← hrn]
  · intro hcon
    exact hnadj ((hdelA b).mpr hcon)


/-- PAPER (19.2, claim (10), printed p. 122), everything after the first application
of 17.1.  See the module header for the sentence-by-sentence map. -/
theorem endgame (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (f : V) (hfA : f ∈ A) (hfconn : ConnectedSet G (A \ {f})) (hfC : f ∉ P)
    (hfadj : G.Adj (x 2) f) (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f)
    (hx20 : G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (h0f : G.Adj (x 0) f) (h1f : ¬ G.Adj (x 1) f)
    (h2y : G.Adj (x 2) y) (h2Y0 : ¬ VertexComplete G (x 2) (Y \ {y})) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) := fun j hj => hws.2.2.2.2.2.2 j hj
  have hzAdjA : ∀ w ∈ A, ¬ G.Adj z w := fun w hw =>
    Thm192Setup.wheelSystemA_no_z _ (hAsub hw)
  have hxjA : ∀ j : ℕ, j ≤ 2 → x j ∉ A := fun j hj hm => hzAdjA _ hm (hzx j hj)
  have hzAmem : z ∉ A := by
    intro hz
    refine Thm192Setup.wheelSystemA_no_complete _ (hAsub hz) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hzx 0 (by omega)
    · exact hzx 1 (by omega)
  have hYA : ∀ w ∈ Y, w ∉ A := by
    intro w hw hmem
    refine Thm192Setup.wheelSystemA_no_complete _ (hAsub hmem) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact (hHyp.2.2.1 w hw).symm
    · exact (hHyp.2.2.2.1 w hw).symm
  have hx2nex1 : x 2 ≠ x 1 := by
    intro h; have := hws.2.1 2 (by omega) 1 (by omega) h; omega
  have hx2nez : x 2 ≠ z := (hws.2.2.1 2 (by omega)).2
  have hx1nez : x 1 ≠ z := (hws.2.2.1 1 (by omega)).2
  -- *"By (2) `z` is `Y₀`-complete"*: since `x₂` is adjacent to `y`, claim (2) returns its
  -- right disjunct, whose first conjunct is that `z` is `Y`-complete.
  have hzY : VertexComplete G z Y := by
    rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
      with hl | ⟨hz, -⟩
    · exact absurd h2y hl.2
    · exact hz
  -- *"all other vertices of `Y` have at least two neighbours in `{p₁,…,pₙ}`"*
  obtain ⟨-, c, hcI, d, hdI, hcd, hcY0, hdY0⟩ := hchoice.resolve_left h2Y0
  have hcA : c ∈ A := hPint c hcI
  have hdA : d ∈ A := hPint d hdI
  have hcP : c ∈ P := PathBasics.interior_subset hcI
  have hdP : d ∈ P := PathBasics.interior_subset hdI
  have hfc : f ≠ c := fun h => hfC (h ▸ hcP)
  have hfd : f ≠ d := fun h => hfC (h ▸ hdP)
  -- *"Let `x₂-q₁-⋯-q_k-x₁` be a path between `x₁,x₂` with interior in `A`."*
  obtain ⟨Q, hQ, hQint⟩ := MinimalConnectedIsPath.exists_path_interior_in hA.2.1
    (hxjA 2 (by omega)) (hxjA 1 (by omega)) ⟨f, hfA, hfadj⟩ hA.2.2.2.1
  have hQlen : 3 ≤ Q.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hQ hx2nex1 hx21
  have hQpos : 0 < Q.length := by omega
  have hQ0 : Q[0]'hQpos = x 2 := PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQL : Q[Q.length - 1]'(by omega) = x 1 :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  -- the vertices of `Q` are `x₂`, `x₁` and members of `A`
  have hQmem : ∀ w ∈ Q, w = x 2 ∨ w = x 1 ∨ w ∈ A := by
    intro w hw
    by_cases h2 : w = x 2
    · exact Or.inl h2
    by_cases h1 : w = x 1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (hQint w
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hw, h2, h1⟩)))
  have hzQ : z ∉ Q := by
    intro hz
    rcases hQmem z hz with h | h | h
    · exact hx2nez h.symm
    · exact hx1nez h.symm
    · exact hzAmem h
  -- `q₁ = f`
  have hq1int : (Q[1]'(by omega)) ∈ SPGT.interior Q :=
    PathBasics.getElem_mem_interior hQ.1 (by omega) (by omega) (by omega)
  have hq1f : (Q[1]'(by omega)) = f := by
    refine hfuniq _ (hQint _ hq1int) ?_
    have h := PathBasics.path_adj_succ hQ.1 (i := 0) (by omega)
    rw [hQ0] at h
    exact h
  -- `q_k`
  have hqkint : (Q[Q.length - 2]'(by omega)) ∈ SPGT.interior Q :=
    PathBasics.getElem_mem_interior hQ.1 (by omega) (by omega) (by omega)
  have hqkA : (Q[Q.length - 2]'(by omega)) ∈ A := hQint _ hqkint
  have hqkadj : G.Adj (x 1) (Q[Q.length - 2]'(by omega)) := by
    have h := PathBasics.path_adj_succ hQ.1 (i := Q.length - 2) (by omega)
    have hidx : Q[Q.length - 2 + 1]'(by omega) = Q[Q.length - 1]'(by omega) :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rw [hidx, hQL] at h
    exact h.symm
  -- *"From (9), `A = {q₁,…,q_k}`."*
  have hIQsub : {w : V | w ∈ SPGT.interior Q} ⊆ A := fun w hw => hQint w hw
  have hAeq : {w : V | w ∈ SPGT.interior Q} = A :=
    Thm192Claim9.claim9 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin hcex
      {w : V | w ∈ SPGT.interior Q} hIQsub
      (MinimalConnectedIsPath.connectedSet_interior hQ)
      ⟨f, by rw [Set.mem_setOf_eq, ← hq1f]; exact hq1int, h0f⟩
      ⟨_, hqkint, hqkadj⟩
      ⟨f, by rw [Set.mem_setOf_eq, ← hq1f]; exact hq1int, hfadj⟩
  -- `q_k` is the **unique** neighbour of `x₁` in `A`
  have hqkuniq : ∀ a ∈ A, G.Adj (x 1) a → a = Q[Q.length - 2]'(by omega) := by
    intro a haA h1a
    have haI : a ∈ SPGT.interior Q := by rw [← hAeq] at haA; exact haA
    obtain ⟨j, hj, hj1, hj2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hQ.1 haI
    have hadj : G.Adj (Q[Q.length - 1]'(by omega)) (Q[j]'hj) := by
      rw [hQL]; exact h1a
    have := (PathBasics.path_adj_iff hQ.1 (by omega : Q.length - 1 < Q.length) hj).mp hadj
    exact HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
  -- name `q_k`
  obtain ⟨qk, hqk⟩ : ∃ w : V, Q[Q.length - 2]'(by omega) = w := ⟨_, rfl⟩
  rw [hqk] at hqkint hqkA hqkadj hqkuniq
  -- *"Since `q_k = pₙ` and `z` is `Y`-complete, it follows from (4) that `q_k` is not
  -- `Y`-complete."*
  have hPn1 : P.length - 1 < P.length := by omega
  have hPn2 : P.length - 2 < P.length := by omega
  have hP0 : P[0]'(by omega) = x 0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hPL : P[P.length - 1]'hPn1 = x 1 :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hpnint : (P[P.length - 2]'hPn2) ∈ SPGT.interior P :=
    PathBasics.getElem_mem_interior hP.1 hPn2 (by omega) (by omega)
  have hpnadj : G.Adj (P[P.length - 2]'hPn2) (P[P.length - 1]'hPn1) := by
    have h := PathBasics.path_adj_succ hP.1 (i := P.length - 2) (by omega)
    have hidx : P[P.length - 2 + 1]'(by omega) = P[P.length - 1]'hPn1 :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rwa [hidx] at h
  have hpnqk : (P[P.length - 2]'hPn2) = qk :=
    hqkuniq _ (hPint _ hpnint) (by rw [← hPL]; exact hpnadj.symm)
  have h4 := Thm192Claim4.claim4 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
    hAmin hcex P hP hPint hPlen
  have hqkNotY : ¬ VertexComplete G qk Y := by
    intro hc
    refine h4.2.1 hzY (P.length - 2) (by omega) ⟨PathBasics.path_adj_succ hP.1 (by omega),
      by rw [hpnqk]; exact hc, ?_⟩
    have hidx : P[P.length - 2 + 1]'(by omega) = P[P.length - 1]'hPn1 :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rw [hidx, hPL]
    exact hHyp.2.2.2.1
  -- the sub-path `S = x₂-q₁-⋯-q_k` of `Q`
  have hSpath : IsPathFrom G ((Q.drop 0).take (Q.length - 2 - 0 + 1))
      (Q[0]'(by omega)) (Q[Q.length - 2]'(by omega)) :=
    PathBasics.isPathFrom_slice hQ.1 (by omega) (by omega)
  rw [hQ0, hqk] at hSpath
  obtain ⟨S, hSdef⟩ : ∃ l : List V, (Q.drop 0).take (Q.length - 2 - 0 + 1) = l := ⟨_, rfl⟩
  rw [hSdef] at hSpath
  have hSlen : S.length = Q.length - 1 := by
    rw [← hSdef, PathBasics.length_slice Q (by omega) (show Q.length - 2 < Q.length by omega)]
    omega
  have hmemS : ∀ w : V, w ∈ S ↔ ∃ (k : ℕ) (hk : k < Q.length), k ≤ Q.length - 2 ∧
      Q[k]'hk = w := by
    intro w
    rw [← hSdef, PathBasics.mem_slice_iff Q (by omega) (show Q.length - 2 < Q.length by omega)]
    constructor
    · rintro ⟨k, hk, -, h2, h3⟩; exact ⟨k, hk, h2, h3⟩
    · rintro ⟨k, hk, h2, h3⟩; exact ⟨k, hk, Nat.zero_le _, h2, h3⟩
  have hintS : ∀ w : V, w ∈ SPGT.interior S ↔ ∃ (k : ℕ) (hk : k < Q.length), 0 < k ∧
      k < Q.length - 2 ∧ Q[k]'hk = w := by
    intro w
    rw [← hSdef,
      PathBasics.mem_interior_slice_iff hQ.1 (by omega)
        (show Q.length - 2 < Q.length by omega)]
  have hSsubQ : ∀ w ∈ S, w ∈ Q := by
    intro w hw
    obtain ⟨k, hk, -, rfl⟩ := (hmemS w).mp hw
    exact List.getElem_mem hk
  have hAsubS : ∀ a ∈ A, a ∈ S := by
    intro a haA
    have haI : a ∈ SPGT.interior Q := by rw [← hAeq] at haA; exact haA
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hQ.1 haI
    exact (hmemS _).mpr ⟨k, hk, by omega, rfl⟩
  have hx2S : x 2 ∈ S := (hmemS _).mpr ⟨0, by omega, by omega, hQ0⟩
  have hSmem : ∀ w ∈ S, w = x 2 ∨ w ∈ A := by
    intro w hw
    obtain ⟨k, hk, hk2, rfl⟩ := (hmemS w).mp hw
    by_cases hk0 : k = 0
    · subst hk0; exact Or.inl hQ0
    · exact Or.inr (hQint _ (PathBasics.getElem_mem_interior hQ.1 hk (by omega) (by omega)))
  have hintSA : ∀ w ∈ SPGT.interior S, w ∈ A := by
    intro w hw
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hintS w).mp hw
    exact hQint _ (PathBasics.getElem_mem_interior hQ.1 hk (by omega) (by omega))
  -- the hole `C₁ = x₁-z-x₂-q₁-⋯-q_k-x₁`
  have hzS : z ∉ S := fun h => hzQ (hSsubQ z h)
  have hx1S : x 1 ∉ S := by
    intro h
    obtain ⟨k, hk, hk2, hkeq⟩ := (hmemS _).mp h
    refine PathBasics.path_ne_of_ne_index hQ.1 hk (show Q.length - 1 < Q.length by omega)
      (by omega) ?_
    rw [hkeq, hQL]
  have hintSx1 : ∀ w ∈ SPGT.interior S, ¬ G.Adj (x 1) w := by
    intro w hw hadj
    obtain ⟨k, hk, hk1, hk2, hkeq⟩ := (hintS w).mp hw
    have := hqkuniq w (hintSA w hw) hadj
    rw [← hkeq] at this
    refine PathBasics.path_ne_of_ne_index hQ.1 hk (show Q.length - 2 < Q.length by omega)
      (by omega) ?_
    rw [this, hqk]
  have hD : IsHoleList G (x 1 :: z :: S) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hSpath ?_
      (hzx 2 (by omega)) hqkadj (hzx 1 (by omega)) hzS hx1S
      (fun hc => hzAdjA qk hqkA hc) (fun hc => hx21 hc.symm) ?_ hintSx1
    · rw [PathBasics.pathLength_eq, hSlen]; omega
    · intro w hw
      exact hzAdjA w (hintSA w hw)
  -- the hole has length at least `6`
  have hQne3 : Q.length ≠ 3 := by
    intro h3
    have hcA' : c ∈ A := hcA
    have hcI' : c ∈ SPGT.interior Q := by rw [← hAeq] at hcA'; exact hcA'
    obtain ⟨k, hk, hk1, hk2, hkeq⟩ := PathBasics.exists_getElem_of_mem_interior hQ.1 hcI'
    have hk1' : k = 1 := by omega
    subst hk1'
    exact hfc (hq1f ▸ hkeq)
  have hD6 : 6 ≤ (x 1 :: z :: S).length := by
    have heven := hBerge.1 _ hD
    simp only [holeLength, List.length_cons] at heven
    have h4 := hD.1
    simp only [List.length_cons] at h4 ⊢
    rw [hSlen] at heven h4 ⊢
    rcases heven with ⟨m, hm⟩
    omega
  -- membership decoder for the rim
  have hDmem : ∀ w ∈ (x 1 :: z :: S), w = x 1 ∨ w = z ∨ w = x 2 ∨ w ∈ A := by
    intro w hw
    rcases List.mem_cons.mp hw with h | hw
    · exact Or.inl h
    rcases List.mem_cons.mp hw with h | hw
    · exact Or.inr (Or.inl h)
    · rcases hSmem w hw with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have hx1D : x 1 ∈ (x 1 :: z :: S) := List.mem_cons_self
  have hzD : z ∈ (x 1 :: z :: S) := List.mem_cons_of_mem _ List.mem_cons_self
  have hx2D : x 2 ∈ (x 1 :: z :: S) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx2S)
  have hAD : ∀ a ∈ A, a ∈ (x 1 :: z :: S) := fun a ha =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hAsubS a ha))
  have hDY : ∀ w ∈ (x 1 :: z :: S), w ∉ Y := by
    intro w hw hwY
    rcases hDmem w hw with h | h | h | h
    · exact (hHyp.1 w hwY).2.2.1 h
    · exact (hHyp.1 w hwY).1 h
    · exact (hHyp.1 w hwY).2.2.2 h
    · exact hYA w hwY h
  -- *"all other vertices of `Y` have at least two neighbours in `{q₁,…,q_k}`"*
  have hcx1 : c ≠ x 1 := fun h => hxjA 1 (by omega) (h ▸ hcA)
  have hcz : c ≠ z := fun h => hzAmem (h ▸ hcA)
  have hdx1 : d ≠ x 1 := fun h => hxjA 1 (by omega) (h ▸ hdA)
  have hdz : d ≠ z := fun h => hzAmem (h ▸ hdA)
  have key : ∀ v' ∈ Y, ∀ e : V,
      (∀ w ∈ (x 1 :: z :: S), G.Adj v' w → w = x 1 ∨ w = z ∨ w = e) → v' = y := by
    intro v' hv'Y e hnbr
    by_contra hne
    have hv'0 : v' ∈ Y \ {y} := ⟨hv'Y, by simpa using hne⟩
    have hce : c = e := by
      rcases hnbr c (hAD c hcA) (hcY0 v' hv'0).symm with h | h | h
      · exact absurd h hcx1
      · exact absurd h hcz
      · exact h
    have hde : d = e := by
      rcases hnbr d (hAD d hdA) (hdY0 v' hv'0).symm with h | h | h
      · exact absurd h hdx1
      · exact absurd h hdz
      · exact h
    exact hcd (hce.trans hde.symm)
  -- *"`z, x₁` are the only `Y`-complete vertices in `C₁`, by 2.3"*
  have hedge : EdgeComplete G Y (x 1) z :=
    ⟨(hzx 1 (by omega)).symm, hHyp.2.2.2.1, hzY⟩
  have hseg : IsSegment G (x 1 :: z :: S) Y [x 1, z] :=
    Thm232ClosingCompletePair.pair_segment hD hD6 hSpath hHyp.2.2.2.1 hzY
      hHyp.2.2.2.2.1 hqkNotY
  have honly : ∀ w ∈ (x 1 :: z :: S), VertexComplete G w Y → w = x 1 ∨ w = z := by
    refine Thm232ClosingCompletePair.only_pair hBerge hD hD6 ⟨y, hyY⟩ hHyp.2.1 hDY
      (fun hw => hG.2.1 ⟨_, _, hw⟩) hx1D hzD hedge hseg ?_ ?_
    · intro w hw hadj hwc
      rcases hDmem w hw with h | h | h | h
      · exact absurd (h ▸ hadj) G.irrefl
      · exact h
      · exact absurd (h ▸ hadj) (fun hc => hx21 hc.symm)
      · exact absurd (hqkuniq w h hadj ▸ hwc) hqkNotY
    · intro w hw hadj hwc
      rcases hDmem w hw with h | h | h | h
      · exact h
      · exact absurd (h ▸ hadj) G.irrefl
      · exact absurd (h ▸ hwc) hHyp.2.2.2.2.1
      · exact absurd hadj (hzAdjA w h)
  -- *"By 2.10, `Y` contains a leap or hat for `C₁`."*
  have hDlen : 4 < holeLength (x 1 :: z :: S) := by
    simp only [holeLength]
    omega
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge Y hHyp.2.1
      (x 1 :: z :: S) hD hDY hDlen (x 1) z hx1D hzD ((hzx 1 (by omega)).symm)
      hHyp.2.2.2.1 hzY honly with ⟨h, hhY, hhat⟩ | ⟨a, haY, b, hbY, hleap⟩
  · -- *"`y` is adjacent to `x₂`"*: no hat.
    have hhy : h = y := by
      refine key h hhY (x 1) ?_
      intro w hw hadj
      by_cases h1 : w = x 1
      · exact Or.inl h1
      by_cases h2 : w = z
      · exact Or.inr (Or.inl h2)
      · exact absurd hadj (hhat.2.2.2.2.2.2 w hw h1 h2)
    exact hhat.2.2.2.2.2.2 (x 2) hx2D hx2nex1 hx2nez (by rw [hhy]; exact h2y.symm)
  · -- a leap: both ends would have to be `y`
    have haD : a ∉ (x 1 :: z :: S) := fun hc => hDY a hc haY
    have hbD : b ∉ (x 1 :: z :: S) := fun hc => hDY b hc hbY
    rcases hleap with hl | hl
    · obtain ⟨s₀, t₀, -, -, -, -, -, -, -, -, hAn, hBn, hab, -⟩ := leap_pair hl haD hbD
      exact hab ((key a haY s₀ hAn).trans (key b hbY t₀ hBn).symm)
    · obtain ⟨s₀, t₀, -, -, -, -, -, -, -, -, hAn, hBn, hab, -⟩ := leap_pair hl haD hbD
      have hAn' : ∀ w ∈ (x 1 :: z :: S), G.Adj a w → w = x 1 ∨ w = z ∨ w = s₀ := by
        intro w hw hadj
        rcases hAn w hw hadj with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      have hBn' : ∀ w ∈ (x 1 :: z :: S), G.Adj b w → w = x 1 ∨ w = z ∨ w = t₀ := by
        intro w hw hadj
        rcases hBn w hw hadj with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      exact hab ((key a haY s₀ hAn').trans (key b hbY t₀ hBn').symm)

end Workspace.ProofLemmas.Thm192Claim10Endgame
