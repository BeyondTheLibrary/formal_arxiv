/-  Proof attempt 1 for statement 20.4 (printed p. 127, proof printed pp. 127-128).

    Reproduces the printed proof step for step: the two numbered claims (1) and
    (2), then the endgame.  Assume no such `Y'` exists.

    * standing facts: `q` is `X_{t-2}`-complete (maximality of `A_{t-2}`) and
      nonadjacent to `x_{t-1}` (because `q \in A_{t-1}`);
    * (1) `x_{t-1}` has neighbours in `A_{t-3}`: the path `R` from `q` with
      interior in `A_{t-2}`, the hole `q-R-x_{t-1}-x_t-q` (so `R` even), 13.6 on
      the odd path `q-R-x_{t-1}-z` (so `R` has length 2, middle vertex `r`), the
      antihole `r-Q-x_{t-1}-q-z-r` (so `Q` odd), 2.2 in the complement (so `r`
      has a neighbour in `A_{t-3}`), the 5-hole `z-x_{t-1}-r-q-x_{t-2}-z`, and
      finally the `{q}`-square `x_0,...,x_{t-1}`;
    * (2) `q` has neighbours in `A_{t-3}`: the antipath `S` inside `X_t`, 2.2 in
      the complement forcing `S` odd, and 13.6 in the complement applied to
      `x_t-S-x_{t-1}-q-z`;
    * endgame: `x_{t-1}` is not `X_{t-3}`-complete (else a `{q}`-diamond), and
      then the two reindexings `x_0,...,x_{t-3},x_{t-1},x_{t-2},x_t` (polished
      `Y`-diamond of height `t`) and `x_0,...,x_{t-3},x_{t-1},x_t` (`Y`-square of
      height `t-1`).                                                          -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.Thm203Prelim
import Workspace.ProofLemmas.Thm203AntipathTools
import Workspace.ProofLemmas.Thm203Step3Aux
import Workspace.ProofLemmas.YDiamondTruncation
import Workspace.ProofLemmas.Thm134RegionAux

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S20

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.ProofLemmas

/-! ### tiny path helpers -/

private theorem one_le_pathLength_of_ne {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (huv : u ≠ v) : 1 ≤ pathLength p := by
  by_contra h
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have hlen1 : p.length = 1 := by
    have := PathBasics.pathLength_eq p; omega
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen1
  have e1 : a = u := by simpa using hp.2.1
  have e2 : a = v := by simpa using hp.2.2
  exact huv (e1 ▸ e2)

private theorem two_le_pathLength_of_nonadj {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (huv : u ≠ v) (hnadj : ¬ G.Adj u v) : 2 ≤ pathLength p := by
  have h1 := one_le_pathLength_of_ne hp huv
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · exact absurd (PathBasics.isPathFrom_ends_adj_of_length_one hp h.symm) hnadj
  · omega

private theorem not_adj_of_compl_adj {G : SimpleGraph V} {u v : V} (h : Gᶜ.Adj u v) :
    ¬ G.Adj u v := by
  rw [SimpleGraph.compl_adj] at h; exact h.2

private theorem isPathFrom_triple {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : ¬ G.Adj a c) (hne : a ≠ c) :
    IsPathFrom G [a, b, c] a c := by
  have hca : ¬ G.Adj c a := fun h => hac h.symm
  refine ⟨⟨by simp, ?_, ?_⟩, rfl, rfl⟩
  · simp [hab.ne, hne, hbc.ne]
  · intro i j hi hj
    have hi' : i < 3 := by simpa using hi
    have hj' : j < 3 := by simpa using hj
    interval_cases i <;> interval_cases j <;>
      simp_all [SimpleGraph.irrefl, hab.symm, hbc.symm]

/-! ### the reindexed square `x₀,…,x_{t−3},x_{t−1},x_t` -/

private theorem square_reindex {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hsq : IsYSquare G z A₀ x t Y) (ht : 4 ≤ t)
    {q : V} (hzq : ¬ G.Adj z q) (hqxt : G.Adj q (x t))
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    (hqA3 : ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b)
    (hx1A3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)
    (hx1X3 : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)))
    (hxtX3 : ¬ VertexComplete G (x t) (wheelSystemX x (t - 3))) :
    ∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y := by
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hadjt, hnoA2, -⟩ := id hsq
  obtain ⟨-, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := id hws
  obtain ⟨x', hx'⟩ : ∃ x' : ℕ → V,
      ∀ i, x' i = x (if i ≤ t - 3 then i else if i = t - 2 then t - 1 else t) :=
    ⟨_, fun _ => rfl⟩
  have hlo : ∀ i, i ≤ t - 3 → x' i = x i := by
    intro i hi; rw [hx' i, if_pos hi]
  have hmid : x' (t - 2) = x (t - 1) := by
    rw [hx' (t - 2), if_neg (by omega), if_pos rfl]
  have hhi : x' (t - 1) = x t := by
    rw [hx' (t - 1), if_neg (by omega), if_neg (by omega)]
  have hbd : ∀ i, i ≤ t - 1 →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1 else t) ≤ t := by
    intro i hi; split_ifs <;> omega
  have hbd' : ∀ i, i < t - 1 →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1 else t) < t := by
    intro i hi; split_ifs <;> omega
  have hinj' : ∀ j ≤ t - 1, ∀ k ≤ t - 1, x' j = x' k → j = k := by
    intro j hj k hk h
    rw [hx' j, hx' k] at h
    have h2 := hinj _ (hbd j hj) _ (hbd k hk) h
    split_ifs at h2 <;> omega
  have hXeq : ∀ j, j ≤ t - 3 → wheelSystemX x' j = wheelSystemX x j := by
    intro j hj
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, hlo k (by omega)⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, (hlo k (by omega)).symm⟩
  have hAeq : ∀ j, j ≤ t - 3 →
      wheelSystemA G z A₀ x' j = wheelSystemA G z A₀ x j := by
    intro j hj; unfold wheelSystemA; rw [hXeq j hj]
  have hX'2 : wheelSystemX x' (t - 2) = wheelSystemX x (t - 3) ∪ {x (t - 1)} := by
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k (t - 2) with h | h
      · exact Or.inl ⟨k, by omega, hlo k (by omega)⟩
      · have hk2 : k = t - 2 := by omega
        exact Or.inr (by rw [hk2, hmid])
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, by omega, (hlo k hk).symm⟩
      · exact ⟨t - 2, le_rfl, hmid.symm⟩
  -- `A₀ ⊆ A_{t−3}` and `A_{t−3}` is connected
  have hA₀sub : A₀ ⊆ wheelSystemA G z A₀ x (t - 3) :=
    Thm203Prelim.A₀_subset_wheelSystemA' hframe hws (by omega)
  have hAconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  -- the witness set `A_{t−3} ∪ {q}`
  have hBA₀ : A₀ ⊆ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V) :=
    hA₀sub.trans Set.subset_union_left
  have hBconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V)) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hAconn hqA3
  have hBz : ∀ v ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V), ¬ G.Adj z v := by
    rintro v (hv | hv)
    · exact WheelSystemBasics.wheelSystemA_no_nbr hv
    · rw [Set.mem_singleton_iff] at hv; subst hv; exact hzq
  have hBX : ∀ v ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V),
      ¬ VertexComplete G v (wheelSystemX x' (t - 2)) := by
    rintro v (hv | hv) hcon
    · exact WheelSystemBasics.wheelSystemA_no_complete hv
        (fun w hw => hcon w (by rw [hX'2]; exact Or.inl hw))
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact hqx1 (hcon (x (t - 1)) (by rw [hX'2]; exact Or.inr rfl))
  have hBmem : ∀ b ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V),
      b ∈ wheelSystemA G z A₀ x' (t - 2) := fun b hb =>
    WheelSystemBasics.mem_wheelSystemA_of_witness hBA₀ hBconn hBz hBX hb
  have hqA'2 : q ∈ wheelSystemA G z A₀ x' (t - 2) := hBmem q (Or.inr rfl)
  -- ### `x'` is a wheel system of height `t − 1`
  have hws' : IsWheelSystem G z A₀ x' (t - 1) := by
    refine ⟨by omega, hinj', ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro j hj; rw [hx' j]; exact hout _ (hbd j hj)
    · rw [hlo 0 (by omega)]; exact hnb0
    · rw [hlo 1 (by omega)]; exact hnb1
    · rw [hlo 0 (by omega), hlo 1 (by omega)]; exact hA₀nc
    · intro i hi2 hit
      rcases Nat.lt_or_ge i (t - 2) with hsmall | hbig
      · obtain ⟨B, hB0, hBc, hBn, hBzz, hBnc⟩ := hcond2 i hi2 (by omega)
        refine ⟨B, hB0, hBc, ?_, hBzz, ?_⟩
        · rw [hlo i (by omega)]; exact hBn
        · intro v hv; rw [hXeq (i - 1) (by omega)]; exact hBnc v hv
      · rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
        · refine ⟨wheelSystemA G z A₀ x (t - 3), hA₀sub, hAconn, ?_,
            fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
          · rw [← hEq, hmid]; exact hx1A3
          · intro v hv
            have hi3 : i - 1 = t - 3 := by omega
            rw [hi3, hXeq (t - 3) le_rfl]
            exact WheelSystemBasics.wheelSystemA_no_complete hv
        · have hii : i = t - 1 := by omega
          refine ⟨wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V), hBA₀, hBconn, ?_, hBz, ?_⟩
          · exact ⟨q, Or.inr rfl, by rw [hii, hhi]; exact hqxt.symm⟩
          · intro v hv
            have hi2' : i - 1 = t - 2 := by omega
            rw [hi2']
            exact hBX v hv
    · intro i hi1 hit
      rcases Nat.lt_or_ge i (t - 2) with hsmall | hbig
      · rw [hlo i (by omega), hXeq (i - 1) (by omega)]
        exact hcond3 i hi1 (by omega)
      · rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
        · have hj3 : t - 2 - 1 = t - 3 := by omega
          rw [← hEq, hmid, hj3, hXeq (t - 3) le_rfl]
          exact hx1X3
        · have hii : i = t - 1 := by omega
          have hj2 : t - 1 - 1 = t - 2 := by omega
          rw [hii, hhi, hj2]
          intro hcon
          exact hxtX3 (fun w hw => hcon w (by rw [hX'2]; exact Or.inl hw))
    · intro j hj; rw [hx' j]; exact hzadj _ (hbd j hj)
  -- ### `x'` is a `Y`-square of height `t − 1`
  have e1 : t - 1 - 1 = t - 2 := by omega
  have e2 : t - 1 - 2 = t - 3 := by omega
  refine ⟨x', hws', hYne, hYanti, ⟨hzY, ?_⟩, ?_, ?_, by omega, ?_, ?_, ?_⟩
  · intro i hi; rw [hx' i]; exact hxY _ (hbd i hi)
  · intro i hi; rw [hx' i]; exact hVC _ (hbd' i hi)
  · rw [hhi]; exact hnVC
  · rw [e1, hhi, hmid]; exact hadjt
  · rw [e2, hAeq (t - 3) le_rfl, hhi]
    intro a ha
    exact hnoA2 a (WheelSystemBasics.wheelSystemA_mono (by omega) ha)
  · rw [e1, e2, hAeq (t - 3) le_rfl, hhi]
    exact ⟨q, hqA'2, hqxt, hqA3⟩

/-! ### the reindexed polished diamond `x₀,…,x_{t−3},x_{t−1},x_{t−2},x_t` -/

private theorem polished_reindex {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hsq : IsYSquare G z A₀ x t Y) (ht : 4 ≤ t)
    {q : V} (hzq : ¬ G.Adj z q) (hqxt : G.Adj q (x t))
    (hqA1 : q ∈ wheelSystemA G z A₀ x (t - 1))
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    (hqA3 : ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b)
    (hx1A3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)
    (hx1X3 : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)))
    (hxtX3 : VertexComplete G (x t) (wheelSystemX x (t - 3))) :
    ∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y := by
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hadjt, hnoA2, -⟩ := id hsq
  obtain ⟨-, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := id hws
  obtain ⟨x', hx'⟩ : ∃ x' : ℕ → V,
      ∀ i, x' i = x (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t - 2 else t) :=
    ⟨_, fun _ => rfl⟩
  have hlo : ∀ i, i ≤ t - 3 → x' i = x i := by
    intro i hi; rw [hx' i, if_pos hi]
  have hmid : x' (t - 2) = x (t - 1) := by
    rw [hx' (t - 2), if_neg (by omega), if_pos rfl]
  have hmid2 : x' (t - 1) = x (t - 2) := by
    rw [hx' (t - 1), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hhi : x' t = x t := by
    rw [hx' t, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hbd : ∀ i, i ≤ t →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t - 2 else t) ≤ t := by
    intro i hi; split_ifs <;> omega
  have hbd' : ∀ i, i < t →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t - 2 else t) < t := by
    intro i hi; split_ifs <;> omega
  have hbd1 : ∀ i, i ≤ t - 1 →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t - 2 else t) ≤ t - 1 := by
    intro i hi; split_ifs <;> omega
  have hinj' : ∀ j ≤ t, ∀ k ≤ t, x' j = x' k → j = k := by
    intro j hj k hk h
    rw [hx' j, hx' k] at h
    have h2 := hinj _ (hbd j hj) _ (hbd k hk) h
    split_ifs at h2 <;> omega
  have hXeq : ∀ j, j ≤ t - 3 → wheelSystemX x' j = wheelSystemX x j := by
    intro j hj
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, hlo k (by omega)⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, (hlo k (by omega)).symm⟩
  have hAeq : ∀ j, j ≤ t - 3 →
      wheelSystemA G z A₀ x' j = wheelSystemA G z A₀ x j := by
    intro j hj; unfold wheelSystemA; rw [hXeq j hj]
  have hX'2 : wheelSystemX x' (t - 2) = wheelSystemX x (t - 3) ∪ {x (t - 1)} := by
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k (t - 2) with h | h
      · exact Or.inl ⟨k, by omega, hlo k (by omega)⟩
      · have hk2 : k = t - 2 := by omega
        exact Or.inr (by rw [hk2, hmid])
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, by omega, (hlo k hk).symm⟩
      · exact ⟨t - 2, le_rfl, hmid.symm⟩
  have hX'1 : wheelSystemX x' (t - 1) = wheelSystemX x (t - 1) := by
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [hx' k]
      exact ⟨_, hbd1 k (by omega), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k (t - 2) with h | h
      · exact ⟨k, by omega, (hlo k (by omega)).symm⟩
      · rcases Nat.eq_or_lt_of_le h with hEq | hGt
        · exact ⟨t - 1, le_rfl, by rw [hmid2, hEq]⟩
        · have : k = t - 1 := by omega
          exact ⟨t - 2, by omega, by rw [hmid, this]⟩
  have hA'1 : wheelSystemA G z A₀ x' (t - 1) = wheelSystemA G z A₀ x (t - 1) := by
    unfold wheelSystemA; rw [hX'1]
  -- `A₀ ⊆ A_{t−3}` and `A_{t−3}` is connected
  have hA₀sub : A₀ ⊆ wheelSystemA G z A₀ x (t - 3) :=
    Thm203Prelim.A₀_subset_wheelSystemA' hframe hws (by omega)
  have hAconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA1conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 1)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA₀sub1 : A₀ ⊆ wheelSystemA G z A₀ x (t - 1) :=
    Thm203Prelim.A₀_subset_wheelSystemA' hframe hws (by omega)
  -- the witness set `A_{t−3} ∪ {q}`
  have hBA₀ : A₀ ⊆ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V) :=
    hA₀sub.trans Set.subset_union_left
  have hBconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V)) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hAconn hqA3
  have hBz : ∀ v ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V), ¬ G.Adj z v := by
    rintro v (hv | hv)
    · exact WheelSystemBasics.wheelSystemA_no_nbr hv
    · rw [Set.mem_singleton_iff] at hv; subst hv; exact hzq
  have hBX : ∀ v ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V),
      ¬ VertexComplete G v (wheelSystemX x' (t - 2)) := by
    rintro v (hv | hv) hcon
    · exact WheelSystemBasics.wheelSystemA_no_complete hv
        (fun w hw => hcon w (by rw [hX'2]; exact Or.inl hw))
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact hqx1 (hcon (x (t - 1)) (by rw [hX'2]; exact Or.inr rfl))
  have hqA'2 : q ∈ wheelSystemA G z A₀ x' (t - 2) :=
    WheelSystemBasics.mem_wheelSystemA_of_witness hBA₀ hBconn hBz hBX (Or.inr rfl)
  -- `x_{t−2}` has a neighbour in `A_{t−3}`
  have hx2A3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 2)) a :=
    Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
  -- ### `x'` is a wheel system of height `t`
  have hws' : IsWheelSystem G z A₀ x' t := by
    refine ⟨by omega, hinj', ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro j hj; rw [hx' j]; exact hout _ (hbd j hj)
    · rw [hlo 0 (by omega)]; exact hnb0
    · rw [hlo 1 (by omega)]; exact hnb1
    · rw [hlo 0 (by omega), hlo 1 (by omega)]; exact hA₀nc
    · intro i hi2 hit
      rcases Nat.lt_or_ge i (t - 2) with hsmall | hbig
      · obtain ⟨B, hB0, hBc, hBn, hBzz, hBnc⟩ := hcond2 i hi2 (by omega)
        refine ⟨B, hB0, hBc, ?_, hBzz, ?_⟩
        · rw [hlo i (by omega)]; exact hBn
        · intro v hv; rw [hXeq (i - 1) (by omega)]; exact hBnc v hv
      · rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
        · -- `i = t − 2`
          refine ⟨wheelSystemA G z A₀ x (t - 3), hA₀sub, hAconn, ?_,
            fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
          · rw [← hEq, hmid]; exact hx1A3
          · intro v hv
            have hi3 : i - 1 = t - 3 := by omega
            rw [hi3, hXeq (t - 3) le_rfl]
            exact WheelSystemBasics.wheelSystemA_no_complete hv
        · rcases Nat.lt_or_ge i t with hlt | hge
          · -- `i = t − 1`
            have hii : i = t - 1 := by omega
            refine ⟨wheelSystemA G z A₀ x (t - 3), hA₀sub, hAconn, ?_,
              fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
            · rw [hii, hmid2]; exact hx2A3
            · intro v hv
              have hi2' : i - 1 = t - 2 := by omega
              rw [hi2']
              exact hBX v (Or.inl hv)
          · -- `i = t`
            have hii : i = t := by omega
            refine ⟨wheelSystemA G z A₀ x (t - 1), hA₀sub1, hA1conn, ?_,
              fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
            · exact ⟨q, hqA1, by rw [hii, hhi]; exact hqxt.symm⟩
            · intro v hv
              have hi1' : i - 1 = t - 1 := by omega
              rw [hi1', hX'1]
              exact WheelSystemBasics.wheelSystemA_no_complete hv
    · intro i hi1 hit
      rcases Nat.lt_or_ge i (t - 2) with hsmall | hbig
      · rw [hlo i (by omega), hXeq (i - 1) (by omega)]
        exact hcond3 i hi1 (by omega)
      · rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
        · have hj3 : t - 2 - 1 = t - 3 := by omega
          rw [← hEq, hmid, hj3, hXeq (t - 3) le_rfl]
          exact hx1X3
        · rcases Nat.lt_or_ge i t with hlt | hge
          · have hii : i = t - 1 := by omega
            have hj2 : t - 1 - 1 = t - 2 := by omega
            rw [hii, hmid2, hj2]
            intro hcon
            refine hcond3 (t - 2) (by omega) (by omega) ?_
            have hj3 : t - 2 - 1 = t - 3 := by omega
            rw [hj3]
            exact fun w hw => hcon w (by rw [hX'2]; exact Or.inl hw)
          · have hii : i = t := by omega
            rw [hii, hhi, hX'1]
            exact hcond3 t (by omega) le_rfl
    · intro j hj; rw [hx' j]; exact hzadj _ (hbd j hj)
  -- ### `x'` is a polished `Y`-diamond of height `t`
  refine ⟨x', ⟨hws', hYne, hYanti, ⟨hzY, ?_⟩, ?_, ?_, by omega, ?_, ?_⟩,
    by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi; rw [hx' i]; exact hxY _ (hbd i hi)
  · intro i hi; rw [hx' i]; exact hVC _ (hbd' i hi)
  · rw [hhi]; exact hnVC
  · rw [hX'2, hhi]
    intro w hw
    rcases hw with hw | hw
    · exact hxtX3 w hw
    · rw [Set.mem_singleton_iff] at hw; subst hw; exact hadjt
  · exact ⟨q, hqA'2, by rw [hhi]; exact hqxt.symm⟩
  · rw [hmid2, hXeq (t - 3) le_rfl]
    have hj3 : t - 2 - 1 = t - 3 := by omega
    have := hcond3 (t - 2) (by omega) (by omega)
    rwa [hj3] at this
  · rw [hAeq (t - 3) le_rfl, hhi]
    intro a ha
    exact hnoA2 a (WheelSystemBasics.wheelSystemA_mono (by omega) ha)
  · rw [hAeq (t - 3) le_rfl, hmid2]; exact hx2A3
  · refine ⟨q, hqA'2, by rw [hhi]; exact hqxt, ?_, ?_⟩
    · rw [hmid2]
      exact hqX2 (x (t - 2)) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    · rw [hAeq (t - 3) le_rfl]; exact hqA3

theorem thm_20_4 (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (Y : Set V) (hYsub : ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (x : ℕ → V) (t : ℕ) (hsq : IsYSquare G z A₀ x t Y) (ht : 4 ≤ t) :
    ∃ Y' : Set V, Y'.Nonempty ∧ AnticonnectedSet G Y' ∧
      (∀ y ∈ Y', y ∉ A₀ ∧ y ≠ z) ∧
      (Y = Y' ∨ ¬ VertexComplete G z Y') ∧
      ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y')) := by
  by_contra hcon
  have key : ∀ Y' : Set V, Y'.Nonempty → AnticonnectedSet G Y' →
      (∀ y ∈ Y', y ∉ A₀ ∧ y ≠ z) → (Y = Y' ∨ ¬ VertexComplete G z Y') →
      ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y')) → False :=
    fun Y' h1 h2 h3 h4 h5 => hcon ⟨Y', h1, h2, h3, h4, h5⟩
  obtain ⟨hws, hYne', hYanti', ⟨hzY, hxY⟩, hVC, hnVC, ht3, hadjt, hnoA2,
    q, hqA1, hqxt, bq, hbqA2, hqbq⟩ := id hsq
  obtain ⟨-, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := id hws
  have hBerge : Berge G := hG.1.1.1.1
  have hF5 : InF5 G := hG.1.1
  -- ###  standing facts about `q`
  have hzq : ¬ G.Adj z q := WheelSystemBasics.wheelSystemA_no_nbr hqA1
  have hqnotA2 : q ∉ wheelSystemA G z A₀ x (t - 2) := fun h => hnoA2 q h hqxt.symm
  -- "From the maximality of `A_{t−2}` it follows that `q` is `X_{t−2}`-complete."
  have hqX2 : VertexComplete G q (wheelSystemX x (t - 2)) :=
    Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (by omega) hzq hqnotA2
      ⟨bq, hbqA2, hqbq⟩
  -- "Since `q ∈ A_{t−1}`, it is not `X_{t−1}`-complete, and so `q` is nonadjacent to `x_{t−1}`."
  have hqx1 : ¬ G.Adj q (x (t - 1)) := by
    intro hadj
    refine WheelSystemBasics.wheelSystemA_no_complete hqA1 ?_
    rintro w ⟨j, hj, rfl⟩
    rcases Nat.lt_or_ge j (t - 1) with h | h
    · exact hqX2 (x j) ⟨j, by omega, rfl⟩
    · have hj1 : j = t - 1 := by omega
      rw [hj1]; exact hadj
  have hqne_z : q ≠ z := fun h =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 1 ≤ t by omega) (h ▸ hqA1)
  have hqA₀ : q ∉ A₀ := by
    intro h
    refine hA₀nc q h ?_
    intro w hw
    rcases hw with rfl | hw
    · exact hqX2 (x 0) ⟨0, by omega, rfl⟩
    · rw [Set.mem_singleton_iff] at hw; subst hw
      exact hqX2 (x 1) ⟨1, by omega, rfl⟩
  have hQanti : AnticonnectedSet G ({q} : Set V) :=
    Thm134RegionAux.connectedSet_singleton Gᶜ q
  have hQsub : ∀ y ∈ ({q} : Set V), y ∉ A₀ ∧ y ≠ z := by
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact ⟨hqA₀, hqne_z⟩
  have hQzn : ¬ VertexComplete G z ({q} : Set V) := fun h => hzq (h q rfl)
  have hQne : ({q} : Set V).Nonempty := ⟨q, rfl⟩
  -- shared bookkeeping
  have hA3conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA2conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 2)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hznotA3 : z ∉ wheelSystemA G z A₀ x (t - 3) :=
    Thm203Prelim.z_notMem_wheelSystemA hws (by omega)
  have hzA3nadj : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj z a :=
    fun a ha => WheelSystemBasics.wheelSystemA_no_nbr ha
  have hzA2nadj : ∀ a ∈ wheelSystemA G z A₀ x (t - 2), ¬ G.Adj z a :=
    fun a ha => WheelSystemBasics.wheelSystemA_no_nbr ha
  have hx1nc : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 2)) := by
    have h := hcond3 (t - 1) (by omega) (by omega)
    rwa [show t - 1 - 1 = t - 2 from by omega] at h
  have hzX2 : VertexComplete G z (wheelSystemX x (t - 2)) := by
    rintro w ⟨j, hj, rfl⟩; exact hzadj j (by omega)
  have hX2anti : AnticonnectedSet G (wheelSystemX x (t - 2)) :=
    Thm203Prelim.anticonnected_wheelSystemX hws (t - 2) (by omega)
  -- =====================================================================
  -- ###  (1)  `x_{t−1}` has neighbours in `A_{t−3}`.
  -- =====================================================================
  have step1 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a := by
    by_contra hno3'
    push Not at hno3'
    have hno3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a := hno3'
    have hx1notA2 : x (t - 1) ∉ wheelSystemA G z A₀ x (t - 2) :=
      Thm203Prelim.x_notMem_wheelSystemA hws (by omega)
    have hx1A2 : ∃ a ∈ wheelSystemA G z A₀ x (t - 2), G.Adj (x (t - 1)) a :=
      Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
    -- "Let `R` be a path between `q` and `x_{t−1}` with interior in `A_{t−2}`."
    obtain ⟨R, hR, hRmem⟩ :=
      PathInteriorIn.exists_path_mem_of_interior_in hA2conn hqnotA2 hx1notA2
        ⟨bq, hbqA2, hqbq⟩ hx1A2
    have hRint : ∀ y ∈ SPGT.interior R, y ∈ wheelSystemA G z A₀ x (t - 2) := by
      intro y hy
      obtain ⟨hyR, hy1, hy2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hy
      rcases hRmem y hyR with h | h | h
      · exact absurd h hy1
      · exact absurd h hy2
      · exact h
    have hqnex1 : q ≠ x (t - 1) := fun h =>
      Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t by omega)
        (show x (t - 1) ∈ wheelSystemA G z A₀ x (t - 1) by rw [← h]; exact hqA1)
    -- "Then `R` has length ≥ 2"
    have hRlen : 2 ≤ pathLength R := two_le_pathLength_of_nonadj hR hqnex1 hqx1
    have hxtnotR : x t ∉ R := by
      intro hm
      rcases hRmem _ hm with h | h | h
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t ≤ t from le_rfl)
          (show x t ∈ wheelSystemA G z A₀ x (t - 1) by rw [h]; exact hqA1)
      · have := hinj t le_rfl (t - 1) (by omega) h; omega
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t ≤ t from le_rfl) h
    -- "and from the hole `q-R-x_{t−1}-x_t-q` it follows that `R` has even length."
    have hhole : IsHoleList G (x t :: R) :=
      PrismBasics.isHoleList_of_path_add_vertex hR hRlen hqxt.symm hadjt hxtnotR
        (fun y hy => hnoA2 y (hRint y hy))
    have hReven : Even (pathLength R) := by
      have hev := hBerge.1 _ hhole
      rw [PrismBasics.holeLength_cons _ (PathBasics.path_ne_nil hR.1)] at hev
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 1, by omega⟩
    -- "So the path `q-R-x_{t−1}-z` is odd"
    have hznotR : z ∉ R := by
      intro hm
      rcases hRmem _ hm with h | h | h
      · exact hqne_z h.symm
      · exact (hout (t - 1) (by omega)).2 h.symm
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega) h
    have hPz : IsPathFrom G (R ++ [z]) q z := by
      refine PathAttach.isPathFrom_concat hR (hzadj (t - 1) (by omega)) hznotR ?_
      intro y hy hyne
      rcases hRmem y hy with h | h | h
      · rw [h]; exact hzq
      · exact absurd h hyne
      · exact WheelSystemBasics.wheelSystemA_no_nbr h
    have hPzlen : pathLength (R ++ [z]) = pathLength R + 1 := by
      have hpos : 0 < R.length := PathBasics.path_length_pos hR.1
      simp only [pathLength, List.length_append, List.length_singleton]
      omega
    have hPzodd : Odd (pathLength (R ++ [z])) := by
      rw [hPzlen]; exact Even.add_one hReven
    -- "and its ends are `X_{t−2}`-complete, and its interior vertices are not,
    --  so by 13.6 it has length 3, that is, `R` has length 2."
    have hXsub : wheelSystemX x (t - 2) ⊆ {v : V | v ∈ R ++ [z]}ᶜ := by
      rintro y ⟨j, hj, rfl⟩ hmem
      rcases List.mem_append.mp hmem with h | h
      · rcases hRmem _ h with e | e | e
        · have hadj := hqX2 (x j) ⟨j, hj, rfl⟩
          rw [e] at hadj
          exact G.irrefl hadj
        · have := hinj j (by omega) (t - 1) (by omega) e; omega
        · exact Thm203Prelim.x_notMem_wheelSystemA hws (show j ≤ t by omega) e
      · rw [List.mem_singleton] at h
        exact (hout j (by omega)).2 h
    have hclass : ∀ y ∈ R ++ [z], VertexComplete G y (wheelSystemX x (t - 2)) →
        y = q ∨ y = z := by
      intro y hy hyc
      rcases List.mem_append.mp hy with h | h
      · rcases hRmem y h with e | e | e
        · exact Or.inl e
        · exact absurd (e ▸ hyc) hx1nc
        · exact absurd hyc (WheelSystemBasics.wheelSystemA_no_complete e)
      · rw [List.mem_singleton] at h; exact Or.inr h
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hF5 (R ++ [z]) q z hPz hPzodd
        (wheelSystemX x (t - 2)) hXsub hX2anti hqX2 hzX2 with halt1 | halt2
    · obtain ⟨u, hu, v, hv, hadj, huc, hvc⟩ := halt1
      rcases hclass u hu huc with rfl | rfl <;> rcases hclass v hv hvc with hv' | hv'
      · exact G.irrefl (hv' ▸ hadj)
      · exact hzq (hv' ▸ hadj).symm
      · exact hzq (hv' ▸ hadj)
      · exact G.irrefl (hv' ▸ hadj)
    obtain ⟨hlen3, -, -, -, -⟩ := halt2
    have hRlen3 : R.length = 3 := by
      rw [hPzlen] at hlen3
      have := PathBasics.pathLength_eq R
      have hpos : 0 < R.length := PathBasics.path_length_pos hR.1
      omega
    obtain ⟨a0, r, a2, hReq0⟩ := PrismBasics.length_eq_three hRlen3
    have ha0 : a0 = q := by rw [hReq0] at hR; simpa using hR.2.1
    have ha2 : a2 = x (t - 1) := by rw [hReq0] at hR; simpa using hR.2.2
    have hReq : R = [q, r, x (t - 1)] := by rw [hReq0, ha0, ha2]
    have hR' : IsPathFrom G [q, r, x (t - 1)] q (x (t - 1)) := by rw [← hReq]; exact hR
    have hqr : G.Adj q r := by
      have h := PathBasics.path_adj_succ hR'.1 (i := 0) (by simp); simpa using h
    have hrx1 : G.Adj r (x (t - 1)) := by
      have h := PathBasics.path_adj_succ hR'.1 (i := 1) (by simp); simpa using h
    have hintR : SPGT.interior R = [r] := by rw [hReq]; rfl
    have hrA2 : r ∈ wheelSystemA G z A₀ x (t - 2) := hRint r (by rw [hintR]; simp)
    -- "Since `x_{t−1}` has no neighbour in `A_{t−3}`, it follows that `r ∈ A_{t−2} \ A_{t−3}`."
    have hrnotA3 : r ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hno3 r h hrx1.symm
    -- "Let `Q` be an antipath between `r` and `x_{t−1}` with interior in `X_{t−2}`."
    obtain ⟨Q, hQ, hQint⟩ := Thm203Step3Aux.exists_antipath_to_A2 hws ht hrA2
    have hQmem : ∀ y ∈ Q, y = x (t - 1) ∨ y = r ∨ y ∈ wheelSystemX x (t - 2) := by
      intro y hy
      by_cases h1 : y = x (t - 1)
      · exact Or.inl h1
      by_cases h2 : y = r
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (hQint y
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hy, h1, h2⟩)))
    have hqnotQ : q ∉ Q := by
      intro hy
      rcases hQmem q hy with h | h | h
      · exact hqnex1 h
      · exact hqnotA2 (by rw [h]; exact hrA2)
      · exact G.irrefl (hqX2 q h)
    have hznotQ : z ∉ Q := by
      intro hy
      rcases hQmem z hy with h | h | h
      · exact (hout (t - 1) (by omega)).2 h.symm
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega)
          (h.symm ▸ hrA2)
      · exact G.irrefl (hzX2 z h)
    have hx1ner : x (t - 1) ≠ r := fun h => hx1notA2 (by rw [h]; exact hrA2)
    have hQlen1 : 1 ≤ pathLength Q := one_le_pathLength_of_ne (G := Gᶜ) hQ hx1ner
    have hznotr : z ≠ r := fun h =>
      Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega) (h.symm ▸ hrA2)
    -- "Since `r-Q-x_{t−1}-q-z-r` is an antihole, it follows that `Q` is odd."
    have hantihole : IsAntiholeList G (z :: q :: Q) := by
      refine PrismBasics.isHoleList_of_path_add_two_vertices (G := Gᶜ) hQ hQlen1 ?_ ?_ ?_
        hqnotQ hznotQ ?_ ?_ ?_ ?_
      · rw [SimpleGraph.compl_adj]; exact ⟨fun h => hqnex1 h, hqx1⟩
      · rw [SimpleGraph.compl_adj]
        exact ⟨hznotr, WheelSystemBasics.wheelSystemA_no_nbr hrA2⟩
      · rw [SimpleGraph.compl_adj]; exact ⟨hqne_z, fun h => hzq h.symm⟩
      · intro h; exact not_adj_of_compl_adj h hqr
      · intro h; exact not_adj_of_compl_adj h (hzadj (t - 1) (by omega))
      · intro y hy h
        exact not_adj_of_compl_adj h (hqX2 y (hQint y hy))
      · intro y hy h
        exact not_adj_of_compl_adj h (hzX2 y (hQint y hy))
    have hQodd : Odd (pathLength Q) := by
      have hev := hBerge.2 _ hantihole
      rw [PrismBasics.holeLength_cons_cons q z (PathBasics.path_ne_nil hQ.1)] at hev
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 2, by omega⟩
    -- "By 2.2 applied in `Ḡ`, it follows that `r` has neighbours in `A_{t−3}`."
    have hQnotA3 : ∀ w ∈ Q, w ∉ wheelSystemA G z A₀ x (t - 3) := by
      intro w hw
      rcases hQmem w hw with h | h | h
      · rw [h]; exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t by omega)
      · rw [h]; exact hrnotA3
      · obtain ⟨j, hj, rfl⟩ := h
        exact Thm203Prelim.x_notMem_wheelSystemA hws (show j ≤ t by omega)
    have hQintA3 : ∀ w ∈ SPGT.interior Q,
        ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj w a := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := hQint w hw
      exact Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
    have hQintz : ∀ w ∈ SPGT.interior Q, G.Adj z w := by
      intro w hw
      obtain ⟨j, hj, rfl⟩ := hQint w hw
      exact hzadj j (by omega)
    have hrA3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj r a := by
      rcases Thm203AntipathTools.exists_end_nbr_of_odd_antipath hBerge hA3conn hznotA3
          hzA3nadj hQ hQodd hrx1.symm hQnotA3 hQintA3 hQintz with hc | hc
      · obtain ⟨a, ha, hadj⟩ := hc; exact absurd hadj (hno3 a ha)
      · exact hc
    -- "Hence `r` is `X_{t−3}`-complete, and nonadjacent to `x_{t−2}`."
    have hrX3 : VertexComplete G r (wheelSystemX x (t - 3)) :=
      Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (by omega)
        (WheelSystemBasics.wheelSystemA_no_nbr hrA2) hrnotA3 hrA3
    have hrx2 : ¬ G.Adj r (x (t - 2)) := by
      intro hadj
      refine WheelSystemBasics.wheelSystemA_no_complete hrA2 ?_
      rintro w ⟨j, hj, rfl⟩
      rcases Nat.lt_or_ge j (t - 2) with h | h
      · exact hrX3 (x j) ⟨j, by omega, rfl⟩
      · have hj2 : j = t - 2 := by omega
        rw [hj2]; exact hadj
    -- "Since `z-x_{t−1}-r-q-x_{t−2}-z` is not an odd hole it follows that
    --  `x_{t−2}` is adjacent to `x_{t−1}`."
    have hqx2adj : G.Adj q (x (t - 2)) :=
      hqX2 (x (t - 2)) (WheelSystemBasics.self_mem_wheelSystemX x le_rfl)
    have hx2x1 : G.Adj (x (t - 2)) (x (t - 1)) := by
      by_contra hnadj
      have hpath : IsPathFrom G [x (t - 1), r, q] (x (t - 1)) q :=
        isPathFrom_triple hrx1.symm hqr.symm (fun h => hqx1 h.symm) (fun h => hqnex1 h.symm)
      have hznotp : z ∉ [x (t - 1), r, q] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        exact ⟨fun h => (hout (t - 1) (by omega)).2 h.symm, hznotr, hqne_z.symm⟩
      have hx2notp : x (t - 2) ∉ [x (t - 1), r, q] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
        · have := hinj (t - 2) (by omega) (t - 1) (by omega) h; omega
        · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 2 ≤ t by omega)
            (by rw [h]; exact hrA2)
        · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 2 ≤ t by omega)
            (by rw [h]; exact hqA1)
      have hhole5 : IsHoleList G (x (t - 2) :: z :: [x (t - 1), r, q]) := by
        refine PrismBasics.isHoleList_of_path_add_two_vertices hpath (by norm_num [pathLength])
          (hzadj (t - 1) (by omega)) hqx2adj.symm (hzadj (t - 2) (by omega))
          hznotp hx2notp hzq hnadj ?_ ?_
        · intro y hy
          have hyr : y = r := by
            rw [show SPGT.interior [x (t - 1), r, q] = [r] from rfl] at hy
            simpa using hy
          rw [hyr]; exact WheelSystemBasics.wheelSystemA_no_nbr hrA2
        · intro y hy
          have hyr : y = r := by
            rw [show SPGT.interior [x (t - 1), r, q] = [r] from rfl] at hy
            simpa using hy
          rw [hyr]; exact fun h => hrx2 h.symm
      have hev := hBerge.1 _ hhole5
      rw [PrismBasics.holeLength_cons_cons z (x (t - 2)) (by simp)] at hev
      rw [show pathLength [x (t - 1), r, q] = 2 from rfl] at hev
      obtain ⟨k, hk⟩ := hev
      omega
    -- "But then `x₀,…,x_{t−1}` is a `{q}`-square of height `t − 1`,
    --  and yet `z` is not `{q}`-complete, a contradiction."
    refine key ({q} : Set V) hQne hQanti hQsub (Or.inr hQzn) (Or.inr (Or.inl ⟨x, ?_⟩))
    refine ⟨YDiamondTruncation.wheelSystem_truncate hws (by omega) (by omega),
      hQne, hQanti, ⟨?_, ?_⟩, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · intro h; rw [Set.mem_singleton_iff] at h; exact hqne_z h.symm
    · intro i hi h
      rw [Set.mem_singleton_iff] at h
      exact Thm203Prelim.x_notMem_wheelSystemA hws (show i ≤ t by omega)
        (show x i ∈ wheelSystemA G z A₀ x (t - 1) by rw [h]; exact hqA1)
    · intro i hi y hy
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact (hqX2 (x i) ⟨i, by omega, rfl⟩).symm
    · intro hcc; exact hqx1 (hcc q rfl).symm
    · rw [show t - 1 - 1 = t - 2 from by omega]; exact hx2x1.symm
    · rw [show t - 1 - 2 = t - 3 from by omega]; exact hno3
    · rw [show t - 1 - 1 = t - 2 from by omega, show t - 1 - 2 = t - 3 from by omega]
      exact ⟨r, hrA2, hrx1, hrA3⟩
  -- =====================================================================
  -- ###  (2)  `q` has neighbours in `A_{t−3}`.
  -- =====================================================================
  have step2 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q a := by
    by_contra hnoq'
    push Not at hnoq'
    have hnoq : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj q a := hnoq'
    have hXtanti : AnticonnectedSet G (wheelSystemX x t) :=
      Thm203Prelim.anticonnected_wheelSystemX hws t le_rfl
    -- "Let `S` be an antipath between `x_t` and `x_{t−1}` with `V(S) ⊆ X_t`."
    obtain ⟨S, hS, hSmem⟩ :=
      InducedPathExtraction.exists_isAntipathFrom_of_anticonnected hXtanti
        (WheelSystemBasics.self_mem_wheelSystemX x (le_refl t))
        (WheelSystemBasics.self_mem_wheelSystemX x (show t - 1 ≤ t by omega))
    have hxtnex1 : x t ≠ x (t - 1) := by
      intro h; have := hinj t le_rfl (t - 1) (by omega) h; omega
    have hSlen : 2 ≤ pathLength S := by
      refine two_le_pathLength_of_nonadj (G := Gᶜ) hS hxtnex1 ?_
      intro h; exact not_adj_of_compl_adj h hadjt
    have hSint : ∀ y ∈ SPGT.interior S, y ∈ wheelSystemX x (t - 2) := by
      intro y hy
      obtain ⟨hyS, hy1, hy2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hS).mp hy
      obtain ⟨j, hj, rfl⟩ := hSmem y hyS
      refine ⟨j, ?_, rfl⟩
      by_contra hjc
      have hj' : j = t - 1 ∨ j = t := by omega
      rcases hj' with rfl | rfl
      · exact hy2 rfl
      · exact hy1 rfl
    have hqnotXt : q ∉ wheelSystemX x t := by
      rintro ⟨j, hj, hq⟩
      exact Thm203Prelim.x_notMem_wheelSystemA hws (show j ≤ t by omega)
        (show x j ∈ wheelSystemA G z A₀ x (t - 1) by rw [← hq]; exact hqA1)
    have hqnotS : q ∉ S := fun h => hqnotXt (hSmem q h)
    have hqnex1 : q ≠ x (t - 1) := fun h =>
      Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t by omega)
        (show x (t - 1) ∈ wheelSystemA G z A₀ x (t - 1) by rw [← h]; exact hqA1)
    -- "Then `x_t-S-x_{t−1}-q` is an antipath with length ≥ 3."
    have hP : IsAntipathFrom G (S ++ [q]) (x t) q := by
      refine PathAttach.isPathFrom_concat (G := Gᶜ) hS ?_ hqnotS ?_
      · rw [SimpleGraph.compl_adj]; exact ⟨hqnex1, hqx1⟩
      · intro y hy hyne hc
        obtain ⟨j, hj, rfl⟩ := hSmem y hy
        refine not_adj_of_compl_adj hc ?_
        rcases Nat.lt_or_ge j (t - 1) with h | h
        · exact hqX2 (x j) ⟨j, by omega, rfl⟩
        · rcases Nat.eq_or_lt_of_le h with hEq | hGt
          · exact absurd (congrArg x hEq).symm hyne
          · have hjt : j = t := by omega
            rw [hjt]; exact hqxt
    have hPlen : pathLength (S ++ [q]) = pathLength S + 1 := by
      have hpos : 0 < S.length := PathBasics.path_length_pos hS.1
      simp only [pathLength, List.length_append, List.length_singleton]
      omega
    -- "by 2.2 applied in `Ḡ` it follows that `S` has odd length."
    have hSodd : Odd (pathLength S) := by
      by_contra hnotodd
      have hSeven : Even (pathLength S) := Nat.not_odd_iff_even.mp hnotodd
      have hPodd : Odd (pathLength (S ++ [q])) := by
        rw [hPlen]; exact Even.add_one hSeven
      have hPnotA3 : ∀ w ∈ S ++ [q], w ∉ wheelSystemA G z A₀ x (t - 3) := by
        intro w hw
        rcases List.mem_append.mp hw with h | h
        · obtain ⟨j, hj, rfl⟩ := hSmem w h
          exact Thm203Prelim.x_notMem_wheelSystemA hws (show j ≤ t by omega)
        · rw [List.mem_singleton] at h; subst h
          exact fun hc => hqnotA2 (WheelSystemBasics.wheelSystemA_mono (by omega) hc)
      have hPintA3 : ∀ w ∈ SPGT.interior (S ++ [q]),
          ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj w a := by
        intro w hw
        obtain ⟨hwP, hw1, hw2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
        rcases List.mem_append.mp hwP with h | h
        · obtain ⟨j, hj, rfl⟩ := hSmem w h
          rcases Nat.lt_or_ge j (t - 1) with hlt | hge
          · exact Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega)
              (by omega)
          · rcases Nat.eq_or_lt_of_le hge with hEq | hGt
            · rw [← hEq]; exact step1
            · exact absurd (congrArg x (show j = t by omega)) hw1
        · rw [List.mem_singleton] at h; exact absurd h hw2
      have hPintz : ∀ w ∈ SPGT.interior (S ++ [q]), G.Adj z w := by
        intro w hw
        obtain ⟨hwP, hw1, hw2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
        rcases List.mem_append.mp hwP with h | h
        · obtain ⟨j, hj, rfl⟩ := hSmem w h
          exact hzadj j hj
        · rw [List.mem_singleton] at h; exact absurd h hw2
      rcases Thm203AntipathTools.exists_end_nbr_of_odd_antipath hBerge hA3conn hznotA3
          hzA3nadj hP hPodd hqxt.symm hPnotA3 hPintA3 hPintz with hc | hc
      · obtain ⟨a, ha, hadj⟩ := hc
        exact hnoA2 a (WheelSystemBasics.wheelSystemA_mono (by omega) ha) hadj
      · obtain ⟨a, ha, hadj⟩ := hc
        exact hnoq a ha hadj
    -- "But then `x_t-S-x_{t−1}-q-z` has odd length ≥ 5 … contrary to 13.6 applied in `Ḡ`."
    have hznotP : z ∉ S ++ [q] := by
      intro hm
      rcases List.mem_append.mp hm with h | h
      · obtain ⟨j, hj, he⟩ := hSmem z h
        have hzz := hzadj j hj
        rw [← he] at hzz
        exact G.irrefl hzz
      · rw [List.mem_singleton] at h; exact hqne_z h.symm
    have hP' : IsAntipathFrom G ((S ++ [q]) ++ [z]) (x t) z := by
      refine PathAttach.isPathFrom_concat (G := Gᶜ) hP ?_ hznotP ?_
      · rw [SimpleGraph.compl_adj]; exact ⟨fun h => hqne_z h.symm, hzq⟩
      · intro y hy hyne hc
        refine not_adj_of_compl_adj hc ?_
        rcases List.mem_append.mp hy with h | h
        · obtain ⟨j, hj, rfl⟩ := hSmem y h
          exact hzadj j hj
        · rw [List.mem_singleton] at h; exact absurd h hyne
    have hP'len : pathLength ((S ++ [q]) ++ [z]) = pathLength S + 2 := by
      have hpos : 0 < S.length := PathBasics.path_length_pos hS.1
      simp only [pathLength, List.length_append, List.length_singleton]
      omega
    have hP'odd : Odd (pathLength ((S ++ [q]) ++ [z])) := by
      rw [hP'len]; obtain ⟨k, hk⟩ := hSodd; exact ⟨k + 1, by omega⟩
    have hP'notA2 : ∀ w ∈ (S ++ [q]) ++ [z], w ∉ wheelSystemA G z A₀ x (t - 2) := by
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · rcases List.mem_append.mp h with h' | h'
        · obtain ⟨j, hj, rfl⟩ := hSmem w h'
          exact Thm203Prelim.x_notMem_wheelSystemA hws (show j ≤ t by omega)
        · rw [List.mem_singleton] at h'; subst h'; exact hqnotA2
      · rw [List.mem_singleton] at h; subst h
        exact Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega)
    have hP'intA2 : ∀ w ∈ SPGT.interior ((S ++ [q]) ++ [z]),
        ∃ a ∈ wheelSystemA G z A₀ x (t - 2), G.Adj w a := by
      intro w hw
      obtain ⟨hwP, hw1, hw2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP').mp hw
      rcases List.mem_append.mp hwP with h | h
      · rcases List.mem_append.mp h with h' | h'
        · obtain ⟨j, hj, rfl⟩ := hSmem w h'
          rcases Nat.lt_or_ge j t with hlt | hge
          · exact Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega)
              (by omega)
          · exact absurd (congrArg x (show j = t by omega)) hw1
        · rw [List.mem_singleton] at h'; subst h'
          exact ⟨bq, hbqA2, hqbq⟩
      · rw [List.mem_singleton] at h; exact absurd h hw2
    have hlen3 := Thm203AntipathTools.antipath_length_three_of_odd hF5 hA2conn hP' hP'odd
      (hzadj t le_rfl).symm hP'notA2 hnoA2 hzA2nadj hP'intA2
    rw [hP'len] at hlen3
    obtain ⟨k, hk⟩ := hSodd
    omega
  -- =====================================================================
  -- ###  the endgame
  -- =====================================================================
  -- "If `x_{t−1}` is `X_{t−3}`-complete, then `x₀,…,x_{t−1}` is a `{q}`-diamond of
  --  height `t − 1`, and yet `z` is not `{q}`-complete, a contradiction."
  have hx1X3 : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)) := by
    intro hcomp
    refine key ({q} : Set V) hQne hQanti hQsub (Or.inr hQzn) (Or.inl ⟨x, ?_⟩)
    refine ⟨YDiamondTruncation.wheelSystem_truncate hws (by omega) (by omega),
      hQne, hQanti, ⟨?_, ?_⟩, ?_, ?_, by omega, ?_, ?_⟩
    · intro h; rw [Set.mem_singleton_iff] at h; exact hqne_z h.symm
    · intro i hi h
      rw [Set.mem_singleton_iff] at h
      exact Thm203Prelim.x_notMem_wheelSystemA hws (show i ≤ t by omega)
        (show x i ∈ wheelSystemA G z A₀ x (t - 1) by rw [h]; exact hqA1)
    · intro i hi y hy
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact (hqX2 (x i) ⟨i, by omega, rfl⟩).symm
    · intro hcc; exact hqx1 (hcc q rfl).symm
    · rw [show t - 1 - 2 = t - 3 from by omega]; exact hcomp
    · rw [show t - 1 - 2 = t - 3 from by omega]; exact step1
  -- "It follows from (2) that if `x_t` is `X_{t−3}`-complete then
  --  `x₀,…,x_{t−3},x_{t−1},x_{t−2},x_t` is a polished `Y`-diamond of height `t`,
  --  while if `x_t` is not `X_{t−3}`-complete then `x₀,…,x_{t−3},x_{t−1},x_t`
  --  is a `Y`-square of height `t − 1`, in either case a contradiction."
  by_cases hxtX3 : VertexComplete G (x t) (wheelSystemX x (t - 3))
  · obtain ⟨x', hx'⟩ :=
      polished_reindex hframe hsq ht hzq hqxt hqA1 hqX2 hqx1 step2 step1 hx1X3 hxtX3
    exact key Y hYne hYanti hYsub (Or.inl rfl) (Or.inr (Or.inr ⟨x', hx'⟩))
  · obtain ⟨x', hx'⟩ :=
      square_reindex hframe hsq ht hzq hqxt hqX2 hqx1 step2 step1 hx1X3 hxtX3
    exact key Y hYne hYanti hYsub (Or.inl rfl) (Or.inr (Or.inl ⟨x', hx'⟩))


end SPGT

end Workspace.Statements.S20
