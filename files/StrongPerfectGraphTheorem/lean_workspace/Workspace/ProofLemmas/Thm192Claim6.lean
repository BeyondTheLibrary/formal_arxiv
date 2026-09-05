import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim4
import Workspace.ProofLemmas.Thm192Claim5
import Workspace.ProofLemmas.Thm192Claim6Basics
import Workspace.ProofLemmas.Thm192Claim6HatLeap
import Workspace.ProofLemmas.Thm192Claim6FirstNeighbour
import Workspace.ProofLemmas.Thm192Claim6Antihole

/-!
# Claim (6) of the printed proof of 19.2

PAPER (printed p. 119):

> *Let us choose `p₁,…,pₙ` and `C` such that either `x₂` is `Y₀`-complete or `(C, Y₀)` is a
> wheel (this is possible by (2)).*
>
> **(6)** *If `x₀` is adjacent to `x₂`, then not both `x₂, y` have neighbours in
> `{p₁,…,pₙ}`.*
>
> *For if they do, then by (5) `p₁` is the only neighbour of `x₂` in `{p₁,…,pₙ}`.  Suppose
> first that `x₂` is adjacent to `y`.  By (2), `z` is `Y`-complete, and `(C, Y₀)` is a
> wheel, and so every vertex in `Y₀` has a neighbour in `{p₂,…,pₙ}`.  By (4) `p₁` is not
> `Y`-complete.  Therefore `z, x₀` are the only `Y ∪ {x₂}`-complete vertices in `C`, and by
> 2.10 there is a hat or a leap.  Since all vertices in `Y₀` have a neighbour in
> `{p₂,…,pₙ}`, and `y` is adjacent to `x₁`, it follows that there is no hat, and so `y, x₂`
> form a leap, a contradiction since they are adjacent.  So `x₂` is nonadjacent to `y`.
> Choose `j` with `1 ≤ j ≤ n` minimum such that `y` is adjacent to `pⱼ`.  From the hole
> `z-x₂-p₁-⋯-pⱼ-y-z` we deduce that `j` is odd, and therefore `x₀-p₁-⋯-pⱼ-y-x₀` is not a
> hole, that is, `j = 1`, and hence `p₁` is adjacent to `y`.  By (4) `p₁` is not
> `Y₀`-complete.  If `x₂` is `Y₀`-complete, then an antipath between `p₁` and `y` with
> interior in `Y₀` can be extended to an antihole via `y-x₂-x₁-p₁`, and this antihole shares
> the vertices `p₁, x₁, x₂` with the hole `z-x₂-p₁-⋯-pₙ-x₁-z`, contrary to 15.7.  So `x₂`
> is not `Y₀`-complete.  By (2), `z` is `Y`-complete, and `(C, Y₀)` is a wheel.  By 16.1
> applied to the wheel `(C, Y₀)` and vertex `x₂`, it follows that `p₁` is `Y₀`-complete and
> therefore `Y ∪ {x₂}`-complete, contrary to (4).  This proves (6).*

Encoding notes.

* The extra choice made just before (6) — *"either `x₂` is `Y₀`-complete or `(C, Y₀)` is a
  wheel"* — is the hypothesis `hchoice`.  The hole `C = z-x₀-p₁-⋯-pₙ-x₁-z` is the list
  `z :: P`.
* **The right disjunct of `hchoice` carries a second conjunct**, namely that `{p₁,…,pₙ}`
  contains *two distinct* `Y₀`-complete vertices.  The word *"wheel"* alone does **not**
  supply this: `IsWheel` has no clause giving a hub vertex a rim neighbour, and its
  two-disjoint-edges clause can be mined for at most **one** `Y₀`-complete interior vertex,
  because `z` absorbs one of the two edges.  The fact is nevertheless available — it is the
  *other* conjunct of claim (2), the count `2 ≤ #{Y₀-complete edges of P}` — and the paper
  itself cites it in exactly this form at claim (3) (*"since `A` contains two `Y₀`-complete
  vertices"*) and at claim (9) (*"by (2) there are two `Y₀`-complete vertices in `A`"*).
  Claims (6) and (10) shorthand it as *"is a wheel"*; that is a citation slip in the
  exposition, not a gap in the mathematics.  `interludeChoice` in
  `Workspace/Statements/S19/Thm_19_2.lean` supplies the conjunct via
  `Thm192Infra.two_complete_in_interior`.  It is what kills 2.10's leap alternative here:
  a leap needs a hub vertex with a *unique* neighbour in the rim interior.
* *"`x₂` has a neighbour in `{p₁,…,pₙ}`"* is `∃ w ∈ SPGT.interior P, G.Adj (x 2) w`.
* **`hcex`, the minimum-counterexample hypothesis.**  The printed proof of (6) cites claim
  (4) twice, and both citations are of `hcex`-dependent conjuncts of (4):
  * *"By (4) `p₁` is not `Y`-complete"* (and later *"By (4) `p₁` is not `Y₀`-complete"*) —
    claim (4)'s **third** conjunct, whose printed justification (*"if say `pₙ` is
    `Y ∪ {x₂}`-complete, then `pₙx₁` is a `Y`-complete edge, a contradiction"*) runs through
    (4)'s **second** conjunct;
  * *"it follows that `p₁` is `Y₀`-complete and therefore `Y ∪ {x₂}`-complete, contrary to
    (4)"* — again claim (4)'s **third** conjunct.

  Only claim (4)'s **first** conjunct is free of `hcex`, and (6) does not use it.  Claim
  (4)'s second/third/fourth conjuncts are reductios against the choice of `Y` as a *minimum
  counterexample* (*"The second is immediate, for otherwise `(C,Y)` satisfies the
  theorem"*), i.e. against the standing assumption `¬ Concl192 G z A₀ x Y` set up by the
  first line of the proof of 19.2 (*"If possible, choose `Y` not satisfying the theorem,
  with `|Y|` minimum"*).  Since `Concl192` is 19.2's actual conclusion it cannot be refuted
  from (6)'s own hypotheses, so that standing assumption is carried explicitly as `hcex`, in
  the same binder slot as in claims (4), (10), (11) and (12).  On the assembly side
  (`Workspace/Statements/S19/Thm_19_2.lean`) `hcex` is produced by `by_contra` on the goal
  `Concl192 G z A₀ x Y` at the top of `core`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim6

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim **(6)** of the printed proof: *"If `x₀` is adjacent to `x₂`, then not both
`x₂, y` have neighbours in `{p₁,…,pₙ}`."* -/
theorem claim6 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (h02 : G.Adj (x 0) (x 2)) :
    ¬ ((∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧ (∃ w ∈ SPGT.interior P, G.Adj y w)) := by
  classical
  intro hboth
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hzP, hx2P, hC, hP5⟩ :=
    Thm192Claim6Basics.path_facts hBerge hws hA.1 hP hPint hPlen
  have hYdisj := Thm192Claim6Basics.Y_disjoint_path hHyp hA.1 hP hPint
  have hzI : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w :=
    fun w hw => wheelSystemA_no_z w (hA.1 (hPint w hw))
  have h5 := Thm192Claim5.claim5 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0
    A hA hAmin hcex P hP hPint hPlen h02
  have h4 := Thm192Claim4.claim4 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0
    A hA hAmin hcex P hP hPint hPlen
  have hx21 : ¬ G.Adj (x 2) (x 1) := by
    intro h21
    apply hws.2.2.2.2.2.1 2 (by omega) le_rfl
    rw [show (2 : ℕ) - 1 = 1 by omega, wheelSystemX_one]
    intro v hv
    rcases hv with rfl | rfl
    · exact h02.symm
    · exact h21
  have hxonly : ∀ i (hi : i < P.length), 1 ≤ i → i + 1 < P.length →
      G.Adj (x 2) (P[i]'hi) → i = 1 := by
    intro i hi hi1 hin hadj
    by_contra h
    exact h5 i (by omega) hin hadj
  have hx1 : G.Adj (x 2) (P[1]'(by omega)) := by
    obtain ⟨w, hw, hadj⟩ := hboth.1
    obtain ⟨i, hi, hi1, hin, hwi⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hw
    have he := hxonly i hi hi1 (by omega) (by rwa [hwi])
    subst i
    rwa [hwi]
  have hp1nc : ¬ VertexComplete G (P[1]'(by omega)) Y := by
    intro hc
    apply h4.2.2.1
    intro w hw
    rcases hw with hw | rfl
    · exact hc w hw
    · exact hx1.symm
  by_cases hx2c : VertexComplete G (x 2) (Y \ {y})
  · have hx2y : ¬ G.Adj (x 2) y := by
      intro hxy
      apply hHyp.2.2.2.2.1
      intro w hw
      by_cases hwy : w = y
      · simpa only [hwy] using hxy
      · exact hx2c w ⟨hw, hwy⟩
    have hyp1 : G.Adj y (P[1]'(by omega)) :=
      Thm192Claim6FirstNeighbour.first_neighbour hBerge hP hPlen hzP hx2P
        (fun h => hYdisj y h hyY) hzI (hws.2.2.2.2.2.2 2 le_rfl) hyz.symm
        (hHyp.2.2.1 y hyY).symm hx2y hx1 hxonly hboth.2
    have hp1nc0 : ¬ VertexComplete G (P[1]'(by omega)) (Y \ {y}) := by
      intro hc
      apply hp1nc
      intro w hw
      by_cases hwy : w = y
      · simpa only [hwy] using hyp1.symm
      · exact hc w ⟨hw, hwy⟩
    obtain ⟨Q, hQ, hQI⟩ := Thm192Claim6Basics.antipath_to_y hHyp.2.1 hyY
      (hYdisj _ (List.getElem_mem (by omega))) hp1nc0
    have hxcut : ∀ k (hk : k < P.length), 1 ≤ k →
        (G.Adj (x 2) (P[k]'hk) ↔ k = 1) := by
      intro k hk hk1
      constructor
      · intro h
        by_cases hklast : k = P.length - 1
        · have hlast := PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
          subst k
          rw [hlast] at h
          exact (hx21 h).elim
        · exact hxonly k hk hk1 (by omega) h
      · rintro rfl
        exact hx1
    have hC1 : IsHoleList G (z :: x 2 :: P.drop 1) :=
      Thm192Infra.holeFromCut hP hPint (fun w hw => wheelSystemA_no_z w (hA.1 hw))
        (hws.2.2.2.2.2.2 0 (by omega)) (hws.2.2.2.2.2.2 1 (by omega))
        (hws.2.2.2.2.2.2 2 le_rfl) hzP hx2P (by omega) (by omega) hxcut
    have hp1b : ¬ G.Adj (P[1]'(by omega)) (x 1) := by
      rw [← PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
      exact PathBasics.path_not_adj_of_gap hP.1 (by omega) (by omega) (by omega) (by omega)
    have hp1I := PathBasics.getElem_mem_interior hP.1 (by omega : 1 < P.length)
      (by omega) (by omega)
    apply Thm192Claim6Antihole.antihole_absurd hG.1 hQ hQI hyp1.symm hx1.symm
      (hHyp.2.2.2.1 y hyY).symm (fun h => hx2y h.symm) hx21 hp1b
      (hHyp.1 y hyY).2.2.2
      (fun h => by have := hws.2.1 2 le_rfl 1 (by omega) h; omega)
      ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hp1I).2.2 hx2c
      (fun w hw => hHyp.2.2.2.1 w hw.1) hC1
      (by simp only [holeLength, List.length_cons, List.length_drop]; omega)
    · simp only [List.mem_cons]
      exact Or.inr (Or.inr (by
        rw [List.mem_iff_getElem]
        refine ⟨0, by simp; omega, ?_⟩
        simp))
    · simp
    · simp only [List.mem_cons]
      right; right
      rw [List.mem_iff_getElem]
      refine ⟨P.length - 2, by simp; omega, ?_⟩
      rw [List.getElem_drop]
      have he : 1 + (P.length - 2) = P.length - 1 := by omega
      simpa only [he] using PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  · obtain ⟨hwheel, c, hcI, d, hdI, hcd, hc0, hd0⟩ := hchoice.resolve_left hx2c
    have hzY : VertexComplete G z Y :=
      Thm192Claim6Basics.z_complete_of_noncomplete hHyp ih hyY hyz hY0 hx2c
    -- The paper's 2.10 argument also closes its later wheel case: every member
    -- of the enlarged hub has a neighbour in the interior, whereas a hat or
    -- one vertex of a leap has none.
    apply Thm192Claim6HatLeap.hat_leap_absurd hBerge
      (KiteTailBasics.anticonnectedSet_union_singleton hHyp.2.1 hHyp.2.2.2.2.1)
      hP hC hP5
    · intro w hw hwS
      rcases hwS with hwY | rfl
      · rcases List.mem_cons.mp hw with he | hwP
        · exact (hHyp.1 w hwY).1 he
        · exact hYdisj w hwP hwY
      · rcases List.mem_cons.mp hw with he | hmem
        · exact (hws.2.2.1 2 le_rfl).2 he
        · exact hx2P hmem
    · exact hws.2.2.2.2.2.2 0 (by omega)
    · intro w hw
      rcases hw with hw | rfl
      · exact hzY w hw
      · exact hws.2.2.2.2.2.2 2 le_rfl
    · intro w hw
      rcases hw with hw | rfl
      · exact hHyp.2.2.1 w hw
      · exact h02
    · intro w hw hwS
      rcases List.mem_cons.mp hw with rfl | hwP
      · exact Or.inl rfl
      by_cases hw0 : w = x 0
      · exact Or.inr hw0
      by_cases hw1 : w = x 1
      · exact (hx21 (hw1 ▸ (hwS (x 2) (Or.inr rfl)).symm)).elim
      have hwI := (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hwP, hw0, hw1⟩
      obtain ⟨i, hi, hi1, hin, hiw⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hwI
      have he := hxonly i hi hi1 (by omega) (by rw [hiw]; exact (hwS _ (Or.inr rfl)).symm)
      subst i
      exact (hp1nc (by rw [hiw]; exact fun v hv => hwS v (Or.inl hv))).elim
    · intro w hw
      rcases hw with hw | rfl
      · by_cases hwy : w = y
        · simpa only [hwy] using hboth.2
        · exact ⟨c, hcI, (hc0 w ⟨hw, hwy⟩).symm⟩
      · exact hboth.1

end Workspace.ProofLemmas.Thm192Claim6
