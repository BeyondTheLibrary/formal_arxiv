import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.Thm224Claim1
import Workspace.ProofLemmas.Thm224OddQForcesKite
import Workspace.ProofLemmas.Thm224Claim4
import Workspace.ProofLemmas.Thm224Claim5LengthTwoExclusion
import Workspace.ProofLemmas.Thm224Claim5
import Workspace.ProofLemmas.Thm224Claim6
import Workspace.ProofLemmas.Thm224Claim7Reduction
import Workspace.ProofLemmas.Thm224Claim7WheelTrichotomy
import Workspace.ProofLemmas.Thm224MinimalNeighborHole
import Workspace.ProofLemmas.Thm224LeapExclusion
import Workspace.ProofLemmas.Thm224HatCatchContradiction
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S02.Thm_2_2
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.TwoPathsHole
import Workspace.ProofLemmas.PathGlue

/-!
# The printed proof of 22.4, cut along the paper's own numbered claims

The proof of 22.4 (perfect.pdf, printed pages 136–137) is a proof by contradiction that opens

> *We assume for a contradiction that `y` has no neighbour in `A_t ∪ {x_{t+1}}`.  Let
> `y-u₁-⋯-uₙ` be a minimal subpath of `T \ z` such that `uₙ` has a neighbour in `A_t`; so `n > 0`.
> From the maximality of `A_t` it follows that `uₙ` is `X_t`-complete and therefore
> `X₁`-complete since `t ≥ 1`; and since `T` is a tail it follows that none of `u₁,…,uₙ` are
> `Y`-complete.*

and then proves seven numbered claims, of which

* **(2)** *"We may assume that `Q` has even length `≥ 4`, and so `n` is even."*
* **(3)** *"`x_{t+1}` is adjacent to one of `u₁,…,u_{n−1}`."*
* **(7)** *"None of `u₁,…,u_{n−1}` is `X_t`-complete."*

are the ones the final paragraph uses; claims (1), (4), (5) and (6) are auxiliary to them and
are used only inside their proofs.  The final paragraph then chooses `i` minimal with
`x_{t+1}` adjacent to `uᵢ`, applies 2.10 to the hole `z-y-u₁-⋯-uᵢ-x_{t+1}-z` to get a leap or a
hat, rules out the leap by 13.6, and turns the hat into a violation of 17.1.

This module fixes the vocabulary for the `u`-path and states the four steps.  The `u`-path is
carried as a list `u` with `z :: y :: u` a prefix of the tail `T`, so that `uₙ` is `u.getLast`
and `u₁,…,u_{n−1}` is `u.dropLast`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm224Claims

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The opening sentence of the proof: the minimal subpath exists.  `uₙ` has a neighbour in `A_t`
because the tail `T` ends in `V(C) \ {z, x₀, x₁} ⊆ A₀ ⊆ A_t`, and a *minimal* such initial segment
exists by well-ordering; `uₙ` is then `X_t`-complete by the maximality of `A_t` (otherwise `A_t`
could be enlarged by `uₙ`), and no `uᵢ` is `Y`-complete because they are internal vertices of the
tail `T`. -/
theorem exists_uPath {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)})) :
    ∃ u : List V, IsUPath G z A₀ x t Y T y u := by
  classical
  subst hTshape
  -- ## Data carried by the tail
  have hw := KiteTailBasics.tail_isWheel hT
  have hC : IsHoleList G C := KiteTailBasics.wheel_isHoleList hw
  have hlen5 : 5 ≤ C.length := by have := KiteTailBasics.wheel_six_le_length hw; omega
  have hzC : z ∈ C := KiteTailBasics.tail_mem_rim hT
  have hnb := KiteTailBasics.tail_rimNeighbours hT
  obtain ⟨hc0, hcz, hc1⟩ := KiteTailBasics.tail_complete_triple hT
  obtain ⟨y', R', hTeq0, hRne', -, -, hy1', -, -, -, -, -, -, -⟩ :=
    KiteTailBasics.tail_snd_spec hT
  obtain ⟨hyy, hRR⟩ : y = y' ∧ R = R' := by
    simpa only [List.cons.injEq, true_and] using hTeq0
  have hy1 : G.Adj y (x 1) := by rw [hyy]; exact hy1'
  have hRne : R ≠ [] := by rw [hRR]; exact hRne'
  -- ## `t ≥ 1`: otherwise `x₁` would be `(Y ∪ {y})`-complete, contradicting the hub condition
  have hnotcomp : ¬ VertexComplete G (x (t + 1)) (Y ∪ {y}) := hhub.2.2.2.2.2.2
  have ht1 : 1 ≤ t := by
    by_contra hlt
    have ht0 : t = 0 := by omega
    subst ht0
    exact hnotcomp (KiteTailBasics.vertexComplete_union_singleton hc1 hy1.symm)
  -- ## `(z, A₀)` is a frame and `A₀ ⊆ A_t`
  have hframe : IsFrame G z A₀ := by
    rw [hA₀]; exact KiteTailBasics.isFrame_rim_minus hC hzC hnb
  have hnoXt : ∀ v ∈ A₀, ¬ VertexComplete G v (wheelSystemX x t) := by
    intro v hv hvc
    rw [hA₀] at hv
    refine KiteTailBasics.no_pair_complete_rim_minus hC hlen5 hzC hnb v hv ?_
    intro a ha
    refine hvc a (WheelSystemBasics.wheelSystemX_mono x ht1 ?_)
    rw [WheelSystemBasics.wheelSystemX_one]
    exact ha
  have hA₀sub : A₀ ⊆ wheelSystemA G z A₀ x t :=
    WheelSystemBasics.A₀_subset_wheelSystemA hframe hnoXt
  -- ## The far end `w` of the tail lies in `A₀`, hence in `A_t`
  obtain ⟨w, hpath, hwC, hwz, hw0, hw1⟩ := KiteTailBasics.tail_exists_end hT
  have hwA : w ∈ wheelSystemA G z A₀ x t := by
    refine hA₀sub ?_
    rw [hA₀]
    exact KiteTailBasics.mem_rim_minus.mpr ⟨hwC, hwz, hw0, hw1⟩
  have hPlist : IsPathList G (z :: y :: R) := hpath.1
  have hPnodup : (z :: y :: R).Nodup := hPlist.2.1
  have hzR : z ∉ R := by
    have h := (List.nodup_cons.mp hPnodup).1
    intro hmem
    exact h (List.mem_cons_of_mem _ hmem)
  have hRnodup : R.Nodup := (List.nodup_cons.mp (List.nodup_cons.mp hPnodup).2).2
  -- ## Index dictionary for the path `z :: y :: R`
  have hadjR : ∀ (i : ℕ) (hi : i + 1 < R.length),
      G.Adj (R[i]'(by omega)) (R[i + 1]'hi) := fun i hi =>
    PathBasics.path_adj_succ (p := z :: y :: R) hPlist (i := i + 1 + 1)
      (hi := by simp only [List.length_cons]; omega)
  have hadjy0 : ∀ hi : 0 < R.length, G.Adj y (R[0]'hi) := fun hi =>
    PathBasics.path_adj_succ (p := z :: y :: R) hPlist (i := 1)
      (hi := by simp only [List.length_cons]; omega)
  have hznadj : ∀ (i : ℕ) (hi : i < R.length), ¬ G.Adj z (R[i]'hi) := fun i hi =>
    PathBasics.path_not_adj_of_gap (p := z :: y :: R) hPlist (i := 0) (j := i + 1 + 1)
      (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
      (by omega) (by omega)
  have hL1 : 0 < R.length := by
    rcases R with _ | ⟨a, l⟩
    · exact absurd rfl hRne
    · simp
  have hRlastq : R[R.length - 1]? = some w := by
    have h1 : (z :: y :: R).getLast? = some w := hpath.2.2
    rw [List.getLast?_eq_getElem?] at h1
    rw [show (z :: y :: R).length - 1 = (R.length - 1) + 1 + 1 by
      simp only [List.length_cons]; omega] at h1
    simpa only [List.getElem?_cons_succ] using h1
  -- ## `n ≥ 2`: if `R` were a single vertex, `y` would be adjacent to `w ∈ A_t`
  have hR2 : 2 ≤ R.length := by
    by_contra hlt
    have hLen1 : R.length = 1 := by omega
    have hw0' : R[0]'(by omega) = w := by
      have h := hRlastq
      rw [hLen1] at h
      norm_num at h
      rw [List.getElem?_eq_getElem (by omega)] at h
      exact Option.some_injective _ h
    refine hcon w (Or.inl hwA) ?_
    rw [← hw0']
    exact hadjy0 (by omega)
  -- ## Some vertex of `R` has a neighbour in `A_t`: the one before the far end
  have hwit : ∃ v, R[R.length - 2]? = some v ∧
      ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj v a := by
    refine ⟨R[R.length - 2]'(by omega), List.getElem?_eq_getElem (by omega), w, hwA, ?_⟩
    have he : R[(R.length - 2) + 1]'(by omega) = w := by
      have h : R[(R.length - 2) + 1]? = some w := by
        rw [show (R.length - 2) + 1 = R.length - 1 by omega]; exact hRlastq
      rw [List.getElem?_eq_getElem (by omega)] at h
      exact Option.some_injective _ h
    rw [← he]
    exact hadjR (R.length - 2) (by omega)
  have hQex : ∃ k, ∃ v, R[k]? = some v ∧
      ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj v a := ⟨R.length - 2, hwit⟩
  -- ## Choose the minimal such index — the paper's *minimal* subpath
  obtain ⟨k, hk, hkmin⟩ :
      ∃ k, (∃ v, R[k]? = some v ∧ ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj v a) ∧
        ∀ m < k, ¬ (∃ v, R[m]? = some v ∧ ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj v a) :=
    ⟨Nat.find hQex, Nat.find_spec hQex, fun m hm => Nat.find_min hQex hm⟩
  have hkle : k ≤ R.length - 2 := by
    by_contra hgt
    push_neg at hgt
    exact hkmin (R.length - 2) hgt hwit
  have hklt : k < R.length := by omega
  obtain ⟨vk, hvkq, hvknbr⟩ := hk
  have hvk : R[k]'hklt = vk := by
    rw [List.getElem?_eq_getElem hklt] at hvkq
    exact Option.some_injective _ hvkq
  -- ## The `u`-path is `R.take (k+1)`
  refine ⟨R.take (k + 1), ⟨R.drop (k + 1), by simp⟩, ?_, ?_, ?_, ?_⟩
  · -- non-null
    intro hnil
    have h := congrArg List.length hnil
    rw [List.length_take] at h
    simp only [List.length_nil] at h
    omega
  · -- `uₙ` has a neighbour in `A_t` and is `X_t`-complete
    intro un hun
    have hlast : (R.take (k + 1)).getLast? = R[k]? := by
      rw [List.getLast?_eq_getElem?, List.length_take,
        show min (k + 1) R.length = k + 1 by omega]
      simp only [Nat.add_sub_cancel]
      rw [List.getElem?_take, if_pos (Nat.lt_succ_self k)]
    rw [hlast, hvkq] at hun
    have hune : un = vk := by
      simpa only [Option.mem_def, Option.some.injEq] using hun.symm
    subst hune
    refine ⟨hvknbr, ?_⟩
    by_contra hnc
    -- *"From the maximality of `A_t` it follows that `uₙ` is `X_t`-complete"*
    obtain ⟨a, haA, hadja⟩ := hvknbr
    have hunA : un ∈ wheelSystemA G z A₀ x t := by
      refine WheelSystemBasics.mem_wheelSystemA_of_witness
        (B := wheelSystemA G z A₀ x t ∪ {un}) (hA₀sub.trans Set.subset_union_left)
        (ConnectedSetUnionAttach.connectedSet_union_singleton
          (WheelSystemBasics.connectedSet_wheelSystemA hframe.1) ⟨a, haA, hadja⟩)
        ?_ ?_ (Or.inr rfl)
      · rintro v (hv | hv)
        · exact WheelSystemBasics.wheelSystemA_no_nbr hv
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          rw [← hvk]
          exact hznadj k hklt
      · rintro v (hv | hv)
        · exact WheelSystemBasics.wheelSystemA_no_complete hv
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          exact hnc
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · -- `n = 1`: then `y` itself would have a neighbour in `A_t`
      refine hcon un (Or.inl hunA) ?_
      rw [← hvk]
      exact hadjy0 (by omega)
    · -- `n ≥ 2`: then `u_{n-1}` has a neighbour in `A_t`, contradicting minimality
      refine hkmin (k - 1) (by omega) ⟨R[k - 1]'(by omega),
        List.getElem?_eq_getElem (by omega), un, hunA, ?_⟩
      have he : R[(k - 1) + 1]'(by omega) = un := by
        have h : R[(k - 1) + 1]? = some un := by
          rw [show (k - 1) + 1 = k by omega]; exact hvkq
        rw [List.getElem?_eq_getElem (by omega)] at h
        exact Option.some_injective _ h
      rw [← he]
      exact hadjR (k - 1) (by omega)
  · -- minimality: `u₁,…,u_{n−1}` have no neighbours in `A_t`
    have hdl : (R.take (k + 1)).dropLast = R.take k := by
      rw [List.dropLast_eq_take, List.length_take, List.take_take,
        show min (k + 1) R.length = k + 1 by omega]
      simp only [Nat.add_sub_cancel]
      congr 1
      omega
    rw [hdl]
    intro v hv a haA hadj
    obtain ⟨j, hjlt, hjeq⟩ := List.getElem_of_mem hv
    rw [List.length_take] at hjlt
    have hjk : j < k := by omega
    have hjR : j < R.length := by omega
    have hvj : R[j]'hjR = v := by
      rw [← hjeq]
      exact List.getElem_take.symm
    exact hkmin j hjk ⟨v, by rw [List.getElem?_eq_getElem hjR, hvj], a, haA, hadj⟩
  · -- *"since `T` is a tail it follows that none of `u₁,…,uₙ` are `Y`-complete"*
    intro v hv
    obtain ⟨j, hjlt, hjeq⟩ := List.getElem_of_mem hv
    rw [List.length_take] at hjlt
    have hjR : j < R.length := by omega
    have hjlt' : j < R.length - 1 := by omega
    have hvj : R[j]'hjR = v := by
      rw [← hjeq]
      exact List.getElem_take.symm
    have hvT : v ∈ (z :: y :: R) := by
      rw [← hvj]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.getElem_mem hjR))
    have hvz : v ≠ z := by
      rw [← hvj]
      intro hcontra
      exact hzR (hcontra ▸ List.getElem_mem hjR)
    have hvw : v ≠ w := by
      rw [← hvj]
      intro hcontra
      have hwj : R[R.length - 1]'(by omega) = w := by
        rw [List.getElem?_eq_getElem (show R.length - 1 < R.length by omega)] at hRlastq
        exact Option.some_injective _ hRlastq
      have : R[j]'hjR = R[R.length - 1]'(show R.length - 1 < R.length by omega) := by
        rw [hcontra, hwj]
      have := (List.Nodup.getElem_inj_iff hRnodup).mp this
      omega
    exact (KiteTailBasics.tail_notYComplete_of_mem hT hpath hvT hvz hvw).2

/-- **(2)** PAPER: *"We may assume that `Q` has even length `≥ 4`, and so `n` is even."*

`Q` is the path `z-y-u₁-⋯-uₙ-P-p`, whose ends are `Y`-complete and none of whose internal
vertices is; by (1) `P` is odd, so the parity of `Q` determines the parity of `n`.  The length-3
case is excluded because it makes `u₁` a kite for `(C, Y)`, and 13.6 excludes every other odd
length. -/
theorem uPath_length_even {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) (hnokite : ¬ ∃ v : V, IsKite G C Y v)
    {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) :
    Even u.length := by
  classical
  let A := wheelSystemA G z A₀ x t
  let B : Set V := {w | VertexComplete G w Y}
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  let un := u.getLast hu.2.1
  have hun : u.getLast? = some un := List.getLast?_eq_some_getLast hu.2.1
  have hunmem : un ∈ u := PathBasics.getLast_mem hun
  have hunopt : un ∈ u.getLast? := by simp [hun]
  have hundata := hu.2.2.1 un hunopt
  have hunY : un ∉ B := hu.2.2.2.2 un hunmem
  have hAB : (A ∩ B).Nonempty := ⟨a, hA₀sub ha, haY⟩
  obtain ⟨p, ⟨hpA, hpY⟩, P, hP, hPpos, hPsub, hPunique⟩ :=
    Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet
      G A B un hAconn hundata.1 hAB hunY
  have hPunion : ∀ w ∈ P, w ∈ (A ∪ {un} : Set V) := by
    intro w hw
    by_cases hwu : w = un
    · exact Or.inr (by simpa [hwu])
    · exact Or.inl (hPsub w hw hwu)
  have hPnc : ∀ w ∈ P, w ≠ p → ¬ VertexComplete G w Y := by
    intro w hw hwp hwY
    exact hwp ((hPunique w hw).mp hwY)
  have hPodd : Odd (pathLength P) :=
    Workspace.ProofLemmas.Thm224Claim1.claim1
      hG hopt hT hTshape hA₀ hhub hcon hu hun hP hPunion hpY hPnc
  let Q := [z, y] ++ u ++ P.tail
  have hQnotOdd : ¬ Odd (pathLength Q) := by
    simpa [Q] using
      (Workspace.ProofLemmas.Thm224OddQForcesKite
        hG hopt hnokite hT hTshape hA₀ hhub hcon hu hun hP hPsub hpY hPnc hPpos)
  have hQeven : Even (pathLength Q) := Nat.not_odd_iff_even.mp hQnotOdd
  have hPlen : 0 < P.length := PathBasics.path_length_pos hP.1
  have hQlen : pathLength Q = 1 + u.length + pathLength P := by
    simp only [Q, List.length_append, List.length_cons, List.length_nil,
      List.length_tail, pathLength]
    omega
  rw [Nat.even_iff]
  have hQmod := Nat.even_iff.mp hQeven
  have hPmod := Nat.odd_iff.mp hPodd
  omega
/-- **(3)** PAPER: *"`x_{t+1}` is adjacent to one of `u₁,…,u_{n−1}`."*

Otherwise a path `N` from `x_{t+1}` to `uₙ` with interior in `A_t` closes the hole
`z-y-u₁-⋯-uₙ-N-x_{t+1}-z`; since `n` is even, `N` is even, so `z-x_{t+1}-N-uₙ` is an odd path whose
ends are `X_t`-complete and whose internal vertices are not, while the `X_t`-complete vertex `y`
has no neighbour in its interior — contrary to 2.2. -/
theorem xt1_adj_dropLast {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) (hnokite : ¬ ∃ v : V, IsKite G C Y v)
    {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) (hlen : Even u.length) :
    ∃ v ∈ u.dropLast, G.Adj (x (t + 1)) v := by
  classical
  by_contra hno
  push Not at hno
  let A := wheelSystemA G z A₀ x t
  let X := wheelSystemX x t
  let q := x (t + 1)
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  let un := u.getLast hu.2.1
  have hun : u.getLast? = some un := List.getLast?_eq_some_getLast hu.2.1
  have hunmem : un ∈ u := PathBasics.getLast_mem hun
  have hunopt : un ∈ u.getLast? := by simp [hun]
  have hundata := hu.2.2.1 un hunopt
  have hunX : VertexComplete G un X := hundata.2
  have hzq : G.Adj z q := hzXq q (Or.inr rfl)
  have hqu : q ≠ un := by
    intro heq
    exact hzu un hunmem (by rw [← heq]; exact hzq)
  have hqz_ne : q ≠ z := (hhub.1.2.2.1 (t + 1) (by omega)).2
  have no_isolated_mem :
      ∀ w : V, VertexAnticomplete G w A → (∃ c ∈ A, c ≠ w) → w ∉ A := by
    intro w hwanti hex hwA
    obtain ⟨c, hcA, hcw⟩ := hex
    obtain ⟨P, hP, hPmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hAconn hwA hcA
    have hPpos : 0 < P.length := PathBasics.path_length_pos hP.1
    have hP2 : 2 ≤ P.length := by
      by_contra hlt
      have hP1 : P.length = 1 := by omega
      obtain ⟨d, rfl⟩ : ∃ d, P = [d] := by
        cases P with
        | nil => simp at hP1
        | cons d l =>
          cases l with
          | nil => exact ⟨d, rfl⟩
          | cons e l => simp at hP1
      have hdw : d = w := Option.some_injective _ hP.2.1
      have hdc : d = c := Option.some_injective _ hP.2.2
      exact hcw (hdc.symm.trans hdw)
    have hadj :=
      PathBasics.path_adj_succ hP.1 (i := 0) (hi := by omega)
    have hw0 : P[0]'hPpos = w :=
      PathBasics.getElem_zero_of_head? hP.2.1 hPpos
    rw [hw0] at hadj
    exact hwanti _ (hPmem _ (List.getElem_mem (show 1 < P.length by omega))) hadj
  have hzNotA : z ∉ A := by
    obtain ⟨c, hc⟩ := hframe.1
    refine no_isolated_mem z hzA ⟨c, hA₀sub hc, ?_⟩
    intro hcz
    apply hframe.2.2.1
    rw [← hcz]
    exact hc
  have hdropNotA : ∀ w ∈ u.dropLast, w ∉ A := by
    intro w hw
    refine no_isolated_mem w (hu.2.2.2.1 w hw) ?_
    obtain ⟨c, hcA, hqc⟩ := hxNbr (t + 1) le_rfl
    refine ⟨c, hcA, ?_⟩
    intro hcw
    subst c
    exact hno w hw hqc
  have hqNotA : q ∉ A := by
    intro hqA
    exact hzA q hqA hzq
  have hunNotA : un ∉ A := by
    intro hunA
    exact hAnoX un hunA hunX
  obtain ⟨N, hN, hNmem⟩ :=
    Workspace.ProofLemmas.PathInteriorIn.exists_path_mem_of_interior_in
      hAconn hqNotA hunNotA (hxNbr (t + 1) le_rfl) hundata.1
  have hNne : N ≠ [] := PathBasics.path_ne_nil hN.1
  have hNpos : 0 < N.length := PathBasics.path_length_pos hN.1
  have hN2 : 2 ≤ N.length := by
    by_contra hlt
    have hN1 : N.length = 1 := by omega
    obtain ⟨d, rfl⟩ : ∃ d, N = [d] := by
      cases N with
      | nil => simp at hN1
      | cons d l =>
        cases l with
        | nil => exact ⟨d, rfl⟩
        | cons e l => simp at hN1
    have hdq : d = q := Option.some_injective _ hN.2.1
    have hdu : d = un := Option.some_injective _ hN.2.2
    exact hqu (hdq.symm.trans hdu)
  have hzpath : IsPathFrom G [z] z z := by
    simp [IsPathFrom, IsPathList]
  have hzNotN : z ∉ N := by
    intro hzN
    rcases hNmem z hzN with hzq' | hzu' | hzA'
    · exact hqz_ne hzq'.symm
    · have hzmemu : z ∈ u := by rw [hzu']; exact hunmem
      exact (List.nodup_cons.mp hpath.2.1).1
        (List.mem_cons_of_mem y hzmemu)
    · exact hzNotA hzA'
  have hzcross : ∀ zz ∈ [z], ∀ w ∈ N,
      (G.Adj zz w ↔ (zz = z ∧ w = q)) := by
    intro zz hzz w hw
    simp only [List.mem_singleton] at hzz
    subst zz
    constructor
    · intro hzw
      rcases hNmem w hw with rfl | rfl | hwA
      · exact ⟨rfl, rfl⟩
      · exact absurd hzw (hzu un hunmem)
      · exact absurd hzw (hzA w hwA)
    · rintro ⟨-, rfl⟩
      exact hzq
  have hZN : IsPathFrom G (z :: N) z un := by
    simpa using PathGlue.glue_path hzpath hN
      (by simpa using hzNotN) hzcross
  have htail : IsPathFrom G (z :: y :: u) z un := by
    refine ⟨hpath, by simp, ?_⟩
    rw [List.getLast?_cons_of_ne_nil (by simp),
      List.getLast?_cons_of_ne_nil hu.2.1, hun]
  have hunLast : u.getLast hu.2.1 = un := by
    apply Option.some_injective
    rw [← List.getLast?_eq_some_getLast hu.2.1, hun]
  have hUnodup : u.Nodup :=
    (List.nodup_cons.mp (List.nodup_cons.mp hpath.2.1).2).2
  have htailInt : ∀ w ∈ SPGT.interior (z :: y :: u), w = y ∨ w ∈ u.dropLast := by
    intro w hw
    have hwi := (PathBasics.mem_interior_iff_of_pathFrom htail).mp hw
    simp only [List.mem_cons] at hwi
    rcases hwi.1 with hwz | hwy | hwu
    · exact absurd hwz hwi.2.1
    · exact Or.inl hwy
    · refine Or.inr ((PathBasics.mem_dropLast_iff hUnodup hu.2.1).2 ⟨hwu, ?_⟩)
      rw [hunLast]
      exact hwi.2.2
  have hNlast : N.getLast hNne = un := by
    apply Option.some_injective
    rw [← List.getLast?_eq_some_getLast hNne, hN.2.2]
  have hZNInt : ∀ w ∈ SPGT.interior (z :: N), w = q ∨ w ∈ A := by
    intro w hw
    have hwDrop : w ∈ N.dropLast := by simpa [SPGT.interior] using hw
    have hwd := (PathBasics.mem_dropLast_iff hN.1.2.1 hNne).mp hwDrop
    rw [hNlast] at hwd
    rcases hNmem w hwd.1 with h | h | h
    · exact Or.inl h
    · exact absurd h hwd.2
    · exact Or.inr h
  have hdisj : ∀ w ∈ SPGT.interior (z :: y :: u), w ∉ SPGT.interior (z :: N) := by
    intro w hwT hwZ
    rcases htailInt w hwT with hwy | hwU
    · subst w
      rcases hZNInt y hwZ with hyq | hyA
      · exact hqYy (Or.inr hyq.symm)
      · exact hzA y hyA
          (PathBasics.path_adj_succ hpath (i := 0) (hi := by simp))
    · rcases hZNInt w hwZ with hwq | hwA
      · subst w
        exact hzu q (List.mem_of_mem_dropLast hwU) hzq
      · exact hdropNotA w hwU hwA
  have hanti : ∀ w ∈ SPGT.interior (z :: y :: u), ∀ c ∈ SPGT.interior (z :: N), ¬ G.Adj w c := by
    intro w hwT c hcZ
    rcases htailInt w hwT with hwy | hwU
    · subst w
      rcases hZNInt c hcZ with hcq | hcA
      · subst c
        exact hcon q (Or.inr rfl)
      · exact hcon c (Or.inl hcA)
    · rcases hZNInt c hcZ with rfl | hcA
      · intro hwq
        exact hno w hwU hwq.symm
      · exact hu.2.2.2.1 w hwU c hcA
  have htail3 : 3 ≤ (z :: y :: u).length := by
    have : 0 < u.length := List.length_pos_of_ne_nil hu.2.1
    simp only [List.length_cons]
    omega
  have hZN3 : 3 ≤ (z :: N).length := by simp; omega
  obtain ⟨hhole, hholeLen⟩ :=
    TwoPathsHole.odd_hole_of_two_paths htail hZN htail3 hZN3 hdisj hanti
  have hBerge : Berge G := hG.1.1.1.1.1
  have hholeEven := hBerge.1 _ hhole
  rw [hholeLen] at hholeEven
  have htailLen : pathLength (z :: y :: u) = u.length + 1 := by
    simp [pathLength]
  have hZNLen : pathLength (z :: N) = pathLength N + 1 := by
    simp only [pathLength, List.length_cons]
    omega
  have hNeven : Even (pathLength N) := by
    rw [Nat.even_iff]
    have hhmod := Nat.even_iff.mp hholeEven
    have humod := Nat.even_iff.mp hlen
    rw [htailLen, hZNLen] at hhmod
    omega
  have hZNodd : Odd (pathLength (z :: N)) := by
    rw [hZNLen, Nat.odd_iff]
    have hmod := Nat.even_iff.mp hNeven
    omega
  have hzX : VertexComplete G z X := fun w hw => hzXq w (Or.inl hw)
  have hzNotX : z ∉ X := by
    intro hzmem
    exact G.irrefl (hzX z hzmem)
  have hunNotX : un ∉ X := by
    intro humem
    exact G.irrefl (hunX un humem)
  have hANotX : ∀ w ∈ A, w ∉ X := by
    intro w hwA hwX
    exact hzA w hwA (hzX w hwX)
  have hZNoutside : ∀ w ∈ z :: N, w ∉ X := by
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with hwz | hwN
    · subst w
      exact hzNotX
    · rcases hNmem w hwN with hwq | hwu | hwA
      · subst w
        exact hqX
      · subst w
        exact hunNotX
      · exact hANotX w hwA
  have hcompleteEnds : ∀ w ∈ z :: N, VertexComplete G w X → w = z ∨ w = un := by
    intro w hw hwc
    simp only [List.mem_cons] at hw
    rcases hw with hwz | hwN
    · exact Or.inl hwz
    · rcases hNmem w hwN with hwq | hwu | hwA
      · subst w
        exact absurd hwc hqXnc
      · exact Or.inr hwu
      · exact absurd hwc (hAnoX w hwA)
  have hnoedge : ¬ ∃ a ∈ z :: N, ∃ b ∈ z :: N, EdgeComplete G X a b := by
    rintro ⟨a, haP, b, hbP, habE⟩
    rcases hcompleteEnds a haP habE.2.1 with rfl | rfl <;>
      rcases hcompleteEnds b hbP habE.2.2 with rfl | rfl
    · exact G.irrefl habE.1
    · exact hzu un hunmem habE.1
    · exact hzu un hunmem habE.1.symm
    · exact G.irrefl habE.1
  obtain ⟨w, hwint, hyw⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hBerge X hXanti (z :: N) z un
      hZN hZNoutside hZNodd hzX hunX hnoedge y hyX
  rcases hZNInt w hwint with rfl | hwA
  · exact hcon q (Or.inr rfl) hyw
  · exact hcon w (Or.inl hwA) hyw
/-- **(7)** PAPER: *"None of `u₁,…,u_{n−1}` is `X_t`-complete."*

Otherwise a path `S` from `x_{t+1}` to the first such vertex `s`, together with the path `R` of
(5) from `x_{t+1}` to a `Y`-complete vertex `r ∈ A_t`, is pushed through 2.2 and 13.7 to force
both `R` and `S` to have length 1; then every `Y`-complete vertex is adjacent to one of
`x_{t+1}, s`, which makes `x_{t+1}` have two adjacent neighbours in `C` of opposite wheel-parity
and at least one other neighbour in `C` — contrary to 16.1, since `x_{t+1}` is not a kite and the
wheel is optimal. -/
theorem no_dropLast_Xt_complete {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) (hnokite : ¬ ∃ v : V, IsKite G C Y v)
    {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) (hlen : Even u.length) :
    ∀ v ∈ u.dropLast, ¬ VertexComplete G v (wheelSystemX x t) := by
  classical
  intro v hv hvc
  obtain ⟨s, hs, r, hr, a, ha, b, hb, hab, haC, hbC, habAdj, haY, hbY,
      S, Rp, LY, hS, hSlen, hRp, hRplen, hLY, hLYint, hLYodd,
      hqnc, hsX, hrY, hcover, hqa, hqb, hqz⟩ :=
    Workspace.ProofLemmas.Thm224Claim7Reduction.thm224Claim7Reduction
      hG hopt hT hTshape hA₀ hhub hcon hu hlen
      (xt1_adj_dropLast hG hopt hnokite hT hTshape hA₀ hhub hcon hu hlen)
      ⟨v, hv, hvc⟩
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, aa, haa, bb, hbb,
      haabb, haaC, hbbC, haaAdj, haaY, hbbY⟩ := hcons
  have hws := hhub.1
  have hqA₀ : x (t + 1) ∉ A₀ := (hws.2.2.1 (t + 1) (by omega)).1
  have hqz_ne : x (t + 1) ≠ z := (hws.2.2.1 (t + 1) (by omega)).2
  have hq0 : x (t + 1) ≠ x 0 := by
    intro heq
    have he := hws.2.1 (t + 1) (by omega) 0 (by omega) heq
    omega
  have hq1 : x (t + 1) ≠ x 1 := by
    intro heq
    have he := hws.2.1 (t + 1) (by omega) 1 (by omega) heq
    omega
  have hqC : x (t + 1) ∉ C := by
    intro hmem
    apply hqA₀
    rw [hA₀]
    exact ⟨hmem, by simp [hq0, hqz_ne, hq1]⟩
  have hqY : x (t + 1) ∉ Y := by
    intro hmem
    exact hqYy (Or.inl hmem)
  have haOutside : a ∉ ({x 0, z, x 1} : Set V) := by
    have h := ha
    rw [hA₀] at h
    intro hmem
    apply h.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm,
      or_comm] using hmem
  have hbOutside : b ∉ ({x 0, z, x 1} : Set V) := by
    have h := hb
    rw [hA₀] at h
    intro hmem
    apply h.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc, or_left_comm,
      or_comm] using hmem
  have hw := KiteTailBasics.tail_isWheel hT
  have hhole := KiteTailBasics.wheel_isHoleList hw
  have hBerge : Berge G := hG.1.1.1.1.1
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  have hopp : OppositeWheelParity G C Y a b :=
    ⟨hab, haC, hbC,
      OddWheelParityFacts.not_sameWheelParity_of_edgeComplete
        hhole heven haC hbC ⟨habAdj, haY, hbY⟩⟩
  exact
    Workspace.ProofLemmas.Thm224Claim7WheelTrichotomy.thm224Claim7WheelTrichotomy
      hG.1.1 hopt hnokite hqC hqY hqnc hab haC hbC habAdj haY hbY hopp
      (KiteTailBasics.tail_mem_rim hT) hqa hqb hqz haOutside hbOutside
      (KiteTailBasics.tail_rimNeighbours hT)


/-- The final paragraph.  PAPER: *"By (3) we may choose `i` with `1 ≤ i ≤ n−1` minimum such that
`x_{t+1}` is adjacent to `uᵢ`.  By (7), the only `X_t`-complete vertices in the hole
`z-y-u₁-⋯-uᵢ-x_{t+1}-z` are `z, y`, and therefore by (6) this hole has length `≥ 6`.  By 2.10 `X_t`
contains a leap or a hat.  If it contains a leap, … this contradicts 13.6.  So there is a hat,
that is, there exists `x ∈ X_t` with no neighbours in `{u₁,…,uᵢ,x_{t+1}}`.  Then
`A_t ∪ {u₁,…,uₙ,x_{t+1}}` (`= F` say) catches the triangle `{z, y, x}`; … and so `F` contains no
reflection of the triangle.  This contradicts 17.1, and therefore proves 22.4."* -/
theorem endgame {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hopt : OptimalWheel G C Y) (hnokite : ¬ ∃ v : V, IsKite G C Y v)
    {z : V} {x : ℕ → V} {T : List V}
    (hT : IsTail G C Y z (x 0) (x 1) T) {y : V} {R : List V} (hTshape : T = z :: y :: R)
    {A₀ : Set V} (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1}) {t : ℕ}
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    {u : List V} (hu : IsUPath G z A₀ x t Y T y u) (hlen : Even u.length)
    (hadj : ∃ v ∈ u.dropLast, G.Adj (x (t + 1)) v)
    (hXt : ∀ v ∈ u.dropLast, ¬ VertexComplete G v (wheelSystemX x t)) :
    False := by
  classical
  obtain ⟨k, hk, hkadj, hkmin, hH⟩ :=
    Workspace.ProofLemmas.Thm224MinimalNeighborHole.thm224MinimalNeighborHole
      hG hopt hT hTshape hA₀ hhub hcon hu hlen hadj hXt
  let H := [z, y] ++ u.take (k + 1) ++ [x (t + 1)]
  change IsHoleList G H ∧
      6 ≤ holeLength H ∧
      (∀ w ∈ H, w ∉ wheelSystemX x t) ∧
      (∀ w ∈ H, VertexComplete G w (wheelSystemX x t) ↔ w = z ∨ w = y) at hH
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpath, hzu, hyu, a, ha, b, hb,
      hab, haC, hbC, habAdj, haY, hbY⟩ := hcons
  have hzmem : z ∈ H := by simp [H]
  have hymem : y ∈ H := by simp [H]
  have hzy : G.Adj z y :=
    PathBasics.path_adj_succ hpath (i := 0) (hi := by simp)
  have hzcomp : VertexComplete G z (wheelSystemX x t) :=
    (hH.2.2.2 z hzmem).2 (Or.inl rfl)
  have hycomp : VertexComplete G y (wheelSystemX x t) :=
    (hH.2.2.2 y hymem).2 (Or.inr rfl)
  have hBerge : Berge G := hG.1.1.1.1.1
  have h210 :=
    Workspace.Statements.S02.SPGT.thm_2_10 G hBerge (wheelSystemX x t)
      hXanti H hH.1 hH.2.2.1 (by omega) z y hzmem hymem hzy hzcomp hycomp
      (fun w hw hwc => (hH.2.2.2 w hw).mp hwc)
  rcases h210 with hhat | hleap
  · obtain ⟨h, hhX, hhat⟩ := hhat
    have hcontra :=
      Workspace.ProofLemmas.Thm224HatCatchContradiction.thm224HatCatchContradiction
        hG hopt hT hTshape hA₀ hhub hcon hu hlen hadj hXt hk hkadj hkmin hH
    exact hcontra h hhX hhat
  · exact
      (Workspace.ProofLemmas.Thm224LeapExclusion.thm224LeapExclusion
        hG hopt hT hTshape hA₀ hhub hcon hu hlen hadj hXt hk hkadj hkmin hH) hleap

end Workspace.ProofLemmas.Thm224Claims
