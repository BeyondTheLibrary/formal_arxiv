/-  Proof attempt 1 for statement 20.5 (printed p. 128, proof printed pp. 128-129).

    Reproduces the printed proof step for step.  Assume no such `Y'` exists; write
    `q` for the vertex of `A_{t-1}` adjacent to both `x_{t+1}` and `x_t` with a
    neighbour in `A_{t-2}`.

    * standing facts: from the maximality of `A_{t-2}`, `q` is `X_{t-2}`-complete,
      and therefore nonadjacent to `x_{t-1}`;
    * `middle_vertex` is *"Let `R` be a path between `q` and `x_{t-1}` with interior
      in ... .  Then `R` has length >= 2, and from the hole `q-R-x_{t-1}-x_{t+1}-q`
      it follows that `R` has even length.  So the path `q-R-x_{t-1}-z` is odd ...
      so by 13.6 it has length 3 ... Let its middle vertex be `r`."*  It is
      parameterised by the set the interior lives in, because the proof runs it
      three times;
    * (1) `x_{t-1}` has neighbours in `A_{t-3}` -- `step_one_square` packages the
      antihole `r-Q-x_{t-1}-q-z-r`, 2.2 in the complement, the 5-hole
      `z-x_{t-1}-r-q-x_{t-2}-z`, and the resulting `{q}`-square of height `t-1`;
    * the chain `v_1-...-v_s` (`exists_attach_chain`) and the re-chosen `R` with
      interior in `A_{t-3} u {v_1,...,v_s}`;
    * (2) `q` has neighbours in `A_{t-3}`: `s >= 2` and `r = v_1`, the antihole
      forcing `Q` odd, and 13.6 in the complement applied to the odd antipath
      `q-x_{t-1}-Q-r-x_{t+1}` of length >= 5 with `T = A_{t-3} u {v_2,...,v_s}`.
      "and therefore `r` in `A_{t-3}`" is realised by re-running `middle_vertex`
      with the interior confined to `A_{t-3}` (the paper's `s = 1` case);
    * (3) `x_{t-1}` is not `X_{t-3}`-complete, else a `{q}`-diamond of height `t-1`;
    * (4) `x_t` has no neighbour in `A_{t-3}`, via `diamond_reindex_drop`
      (`x_0,...,x_{t-2},x_t`) and `polished_reindex_shift`
      (`x_0,...,x_{t-3},x_{t-1},x_t,x_{t+1}`);
    * endgame: `x_t` is not adjacent to `r`, the 5-hole `z-x_t-q-r-x_{t-1}-z` forces
      the edge `x_t x_{t-1}`, and then `polished_reindex'`
      (`x_0,...,x_{t-3},x_{t-1},x_{t-2},x_t`) resp. `square_reindex'`
      (`x_0,...,x_{t-3},x_{t-1},x_t`) with hub `Y u {x_{t+1}}`.               -/
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

private theorem square_reindex' {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hws : IsWheelSystem G z A₀ x t) (ht : 4 ≤ t)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hzY : z ∉ Y) (hxY : ∀ i ≤ t, x i ∉ Y)
    (hVC : ∀ i < t, VertexComplete G (x i) Y) (hnVC : ¬ VertexComplete G (x t) Y)
    (hadjt : G.Adj (x t) (x (t - 1)))
    (hnoA3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x t) a)
    {q : V} (hzq : ¬ G.Adj z q) (hqxt : G.Adj q (x t))
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    (hqA3 : ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b)
    (hx1A3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)
    (hx1X3 : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)))
    (hxtX3 : ¬ VertexComplete G (x t) (wheelSystemX x (t - 3))) :
    ∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y := by
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
    exact hnoA3
  · rw [e1, e2, hAeq (t - 3) le_rfl, hhi]
    exact ⟨q, hqA'2, hqxt, hqA3⟩

/-! ### the reindexed polished diamond `x₀,…,x_{t−3},x_{t−1},x_{t−2},x_t` -/

private theorem polished_reindex' {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hws : IsWheelSystem G z A₀ x t) (ht : 4 ≤ t)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hzY : z ∉ Y) (hxY : ∀ i ≤ t, x i ∉ Y)
    (hVC : ∀ i < t, VertexComplete G (x i) Y) (hnVC : ¬ VertexComplete G (x t) Y)
    (hadjt : G.Adj (x t) (x (t - 1)))
    (hnoA3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x t) a)
    {q : V} (hzq : ¬ G.Adj z q) (hqxt : G.Adj q (x t))
    (hqA1 : q ∈ wheelSystemA G z A₀ x (t - 1))
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    (hqA3 : ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b)
    (hx1A3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)
    (hx1X3 : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)))
    (hxtX3 : VertexComplete G (x t) (wheelSystemX x (t - 3))) :
    ∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y := by
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
    exact hnoA3
  · rw [hAeq (t - 3) le_rfl, hmid2]; exact hx2A3
  · refine ⟨q, hqA'2, by rw [hhi]; exact hqxt, ?_, ?_⟩
    · rw [hmid2]
      exact hqX2 (x (t - 2)) (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    · rw [hAeq (t - 3) le_rfl]; exact hqA3


/-! ### the reindexed diamond `x₀,…,x_{t−2},x_t` -/

private theorem diamond_reindex_drop {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y' : Set V}
    (hws : IsWheelSystem G z A₀ x t) (ht : 4 ≤ t)
    (hYne : Y'.Nonempty) (hYanti : AnticonnectedSet G Y')
    (hzY : z ∉ Y') (hxY : ∀ i ≤ t, x i ∉ Y')
    (hVC : ∀ i, i ≤ t - 2 → VertexComplete G (x i) Y')
    (hnVC : ¬ VertexComplete G (x t) Y')
    (hxtX2 : ¬ VertexComplete G (x t) (wheelSystemX x (t - 2)))
    (hxtA2 : ∃ a ∈ wheelSystemA G z A₀ x (t - 2), G.Adj (x t) a)
    (hxtX3 : VertexComplete G (x t) (wheelSystemX x (t - 3)))
    (hxtA3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x t) a) :
    ∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y' := by
  obtain ⟨-, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := id hws
  obtain ⟨x', hx'⟩ : ∃ x' : ℕ → V, ∀ i, x' i = x (if i ≤ t - 2 then i else t) :=
    ⟨_, fun _ => rfl⟩
  have hlo : ∀ i, i ≤ t - 2 → x' i = x i := by
    intro i hi; rw [hx' i, if_pos hi]
  have hhi : x' (t - 1) = x t := by
    rw [hx' (t - 1), if_neg (by omega)]
  have hbd : ∀ i, i ≤ t - 1 → (if i ≤ t - 2 then i else t) ≤ t := by
    intro i hi; split_ifs <;> omega
  have hbd' : ∀ i, i < t - 1 → (if i ≤ t - 2 then i else t) ≤ t - 2 := by
    intro i hi; split_ifs <;> omega
  have hinj' : ∀ j ≤ t - 1, ∀ k ≤ t - 1, x' j = x' k → j = k := by
    intro j hj k hk h
    rw [hx' j, hx' k] at h
    have h2 := hinj _ (hbd j hj) _ (hbd k hk) h
    split_ifs at h2 <;> omega
  have hXeq : ∀ j, j ≤ t - 2 → wheelSystemX x' j = wheelSystemX x j := by
    intro j hj
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, hlo k (by omega)⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, (hlo k (by omega)).symm⟩
  have hAeq : ∀ j, j ≤ t - 2 → wheelSystemA G z A₀ x' j = wheelSystemA G z A₀ x j := by
    intro j hj; unfold wheelSystemA; rw [hXeq j hj]
  have hws' : IsWheelSystem G z A₀ x' (t - 1) := by
    refine ⟨by omega, hinj', ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro j hj; rw [hx' j]; exact hout _ (hbd j hj)
    · rw [hlo 0 (by omega)]; exact hnb0
    · rw [hlo 1 (by omega)]; exact hnb1
    · rw [hlo 0 (by omega), hlo 1 (by omega)]; exact hA₀nc
    · intro i hi2 hit
      rcases Nat.lt_or_ge i (t - 1) with hsmall | hbig
      · obtain ⟨B, hB0, hBc, hBn, hBzz, hBnc⟩ := hcond2 i hi2 (by omega)
        refine ⟨B, hB0, hBc, ?_, hBzz, ?_⟩
        · rw [hlo i (by omega)]; exact hBn
        · intro v hv; rw [hXeq (i - 1) (by omega)]; exact hBnc v hv
      · have hii : i = t - 1 := by omega
        refine ⟨wheelSystemA G z A₀ x (t - 2),
          Thm203Prelim.A₀_subset_wheelSystemA' hframe hws (by omega),
          WheelSystemBasics.connectedSet_wheelSystemA hframe.1, ?_,
          fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
        · rw [hii, hhi]; exact hxtA2
        · intro v hv
          rw [show i - 1 = t - 2 from by omega, hXeq (t - 2) le_rfl]
          exact WheelSystemBasics.wheelSystemA_no_complete hv
    · intro i hi1 hit
      rcases Nat.lt_or_ge i (t - 1) with hsmall | hbig
      · rw [hlo i (by omega), hXeq (i - 1) (by omega)]
        exact hcond3 i hi1 (by omega)
      · have hii : i = t - 1 := by omega
        rw [hii, hhi, show t - 1 - 1 = t - 2 from by omega, hXeq (t - 2) le_rfl]
        exact hxtX2
    · intro j hj; rw [hx' j]; exact hzadj _ (hbd j hj)
  refine ⟨x', hws', hYne, hYanti, ⟨hzY, ?_⟩, ?_, ?_, by omega, ?_, ?_⟩
  · intro i hi; rw [hx' i]; exact hxY _ (hbd i hi)
  · intro i hi; rw [hx' i]; exact hVC _ (hbd' i hi)
  · rw [hhi]; exact hnVC
  · rw [hhi, show t - 1 - 2 = t - 3 from by omega, hXeq (t - 3) (by omega)]
    exact hxtX3
  · rw [hhi, show t - 1 - 2 = t - 3 from by omega, hAeq (t - 3) (by omega)]
    exact hxtA3

/-! ### the reindexed polished diamond `x₀,…,x_{t−3},x_{t−1},x_t,x_{t+1}` -/

private theorem polished_reindex_shift {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hws : IsWheelSystem G z A₀ x (t + 1)) (ht : 4 ≤ t)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hzY : z ∉ Y) (hxY : ∀ i ≤ t + 1, x i ∉ Y)
    (hVC : ∀ i < t + 1, VertexComplete G (x i) Y)
    (hnVC : ¬ VertexComplete G (x (t + 1)) Y)
    (hxt1X1 : VertexComplete G (x (t + 1)) (wheelSystemX x (t - 1)))
    (hnadj : ¬ G.Adj (x (t + 1)) (x t))
    (hxt1noA3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t + 1)) a)
    (hx1A3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)
    (hx1X3 : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)))
    (hxtA3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x t) a)
    (hxtX3 : ¬ VertexComplete G (x t) (wheelSystemX x (t - 3)))
    {q : V} (hzq : ¬ G.Adj z q) (hqxt1 : G.Adj q (x (t + 1))) (hqxt : G.Adj q (x t))
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    (hqA3 : ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b) :
    ∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y := by
  obtain ⟨-, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := id hws
  obtain ⟨x', hx'⟩ : ∃ x' : ℕ → V,
      ∀ i, x' i = x (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t else t + 1) :=
    ⟨_, fun _ => rfl⟩
  have hlo : ∀ i, i ≤ t - 3 → x' i = x i := by
    intro i hi; rw [hx' i, if_pos hi]
  have hm1 : x' (t - 2) = x (t - 1) := by
    rw [hx' (t - 2), if_neg (by omega), if_pos rfl]
  have hm2 : x' (t - 1) = x t := by
    rw [hx' (t - 1), if_neg (by omega), if_neg (by omega), if_pos rfl]
  have hhi : x' t = x (t + 1) := by
    rw [hx' t, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hbd : ∀ i, i ≤ t →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t else t + 1) ≤ t + 1 := by
    intro i hi; split_ifs <;> omega
  have hbd' : ∀ i, i < t →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t else t + 1) < t + 1 := by
    intro i hi; split_ifs <;> omega
  have hbd1 : ∀ i, i ≤ t - 1 →
      (if i ≤ t - 3 then i else if i = t - 2 then t - 1
        else if i = t - 1 then t else t + 1) ≤ t := by
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
  have hAeq : ∀ j, j ≤ t - 3 → wheelSystemA G z A₀ x' j = wheelSystemA G z A₀ x j := by
    intro j hj; unfold wheelSystemA; rw [hXeq j hj]
  have hX'2 : wheelSystemX x' (t - 2) = wheelSystemX x (t - 3) ∪ {x (t - 1)} := by
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k (t - 2) with h | h
      · exact Or.inl ⟨k, by omega, hlo k (by omega)⟩
      · exact Or.inr (by rw [show k = t - 2 from by omega, hm1])
    · rintro (⟨k, hk, rfl⟩ | rfl)
      · exact ⟨k, by omega, (hlo k hk).symm⟩
      · exact ⟨t - 2, le_rfl, hm1.symm⟩
  have hX'1 : wheelSystemX x' (t - 1) = wheelSystemX x (t - 3) ∪ {x (t - 1), x t} := by
    ext v
    simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k (t - 2) with h | h
      · exact Or.inl ⟨k, by omega, hlo k (by omega)⟩
      · rcases Nat.eq_or_lt_of_le h with hEq | hGt
        · exact Or.inr (Or.inl (by rw [← hEq, hm1]))
        · exact Or.inr (Or.inr (by rw [show k = t - 1 from by omega, hm2]))
    · rintro (⟨k, hk, rfl⟩ | rfl | rfl)
      · exact ⟨k, by omega, (hlo k hk).symm⟩
      · exact ⟨t - 2, by omega, hm1.symm⟩
      · exact ⟨t - 1, le_rfl, hm2.symm⟩
  -- `A₀ ⊆ A_{t−3}` and the witness set `A_{t−3} ∪ {q}`
  have hA₀sub : A₀ ⊆ wheelSystemA G z A₀ x (t - 3) :=
    Thm203Prelim.A₀_subset_wheelSystemA' hframe hws (by omega)
  have hAconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hBA₀ : A₀ ⊆ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V) :=
    hA₀sub.trans Set.subset_union_left
  have hBconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V)) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hAconn hqA3
  have hBz : ∀ v ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V), ¬ G.Adj z v := by
    rintro v (hv | hv)
    · exact WheelSystemBasics.wheelSystemA_no_nbr hv
    · rw [Set.mem_singleton_iff] at hv; subst hv; exact hzq
  have hBX2 : ∀ v ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V),
      ¬ VertexComplete G v (wheelSystemX x' (t - 2)) := by
    rintro v (hv | hv) hcon
    · exact WheelSystemBasics.wheelSystemA_no_complete hv
        (fun w hw => hcon w (by rw [hX'2]; exact Or.inl hw))
    · rw [Set.mem_singleton_iff] at hv; subst hv
      exact hqx1 (hcon (x (t - 1)) (by rw [hX'2]; exact Or.inr rfl))
  have hBX1 : ∀ v ∈ wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V),
      ¬ VertexComplete G v (wheelSystemX x' (t - 1)) := by
    rintro v (hv | hv) hcon
    · exact WheelSystemBasics.wheelSystemA_no_complete hv
        (fun w hw => hcon w (by rw [hX'1]; exact Or.inl hw))
    · rw [Set.mem_singleton_iff] at hv; subst hv
      exact hqx1 (hcon (x (t - 1)) (by rw [hX'1]; exact Or.inr (Or.inl rfl)))
  have hqA'2 : q ∈ wheelSystemA G z A₀ x' (t - 2) :=
    WheelSystemBasics.mem_wheelSystemA_of_witness hBA₀ hBconn hBz hBX2 (Or.inr rfl)
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
        · refine ⟨wheelSystemA G z A₀ x (t - 3), hA₀sub, hAconn, ?_,
            fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
          · rw [← hEq, hm1]; exact hx1A3
          · intro v hv
            rw [show i - 1 = t - 3 from by omega, hXeq (t - 3) le_rfl]
            exact WheelSystemBasics.wheelSystemA_no_complete hv
        · rcases Nat.lt_or_ge i t with hlt | hge
          · refine ⟨wheelSystemA G z A₀ x (t - 3), hA₀sub, hAconn, ?_,
              fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
            · rw [show i = t - 1 from by omega, hm2]; exact hxtA3
            · intro v hv
              rw [show i - 1 = t - 2 from by omega]
              exact hBX2 v (Or.inl hv)
          · refine ⟨wheelSystemA G z A₀ x (t - 3) ∪ ({q} : Set V), hBA₀, hBconn, ?_, hBz, ?_⟩
            · exact ⟨q, Or.inr rfl, by rw [show i = t from by omega, hhi]; exact hqxt1.symm⟩
            · intro v hv
              rw [show i - 1 = t - 1 from by omega]
              exact hBX1 v hv
    · intro i hi1 hit
      rcases Nat.lt_or_ge i (t - 2) with hsmall | hbig
      · rw [hlo i (by omega), hXeq (i - 1) (by omega)]
        exact hcond3 i hi1 (by omega)
      · rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
        · rw [← hEq, hm1, show t - 2 - 1 = t - 3 from by omega, hXeq (t - 3) le_rfl]
          exact hx1X3
        · rcases Nat.lt_or_ge i t with hlt | hge
          · rw [show i = t - 1 from by omega, hm2, show t - 1 - 1 = t - 2 from by omega]
            intro hcon
            exact hxtX3 (fun w hw => hcon w (by rw [hX'2]; exact Or.inl hw))
          · rw [show i = t from by omega, hhi, show t - 1 = t - 1 from rfl]
            intro hcon
            exact hnadj (hcon (x t) (by rw [hX'1]; exact Or.inr (Or.inr rfl)))
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
    · exact hxt1X1 w (WheelSystemBasics.wheelSystemX_mono x (by omega) hw)
    · rw [Set.mem_singleton_iff] at hw; subst hw
      exact hxt1X1 (x (t - 1)) (WheelSystemBasics.self_mem_wheelSystemX x le_rfl)
  · exact ⟨q, hqA'2, by rw [hhi]; exact hqxt1.symm⟩
  · rw [hm2, hXeq (t - 3) le_rfl]; exact hxtX3
  · rw [hAeq (t - 3) le_rfl, hhi]; exact hxt1noA3
  · rw [hAeq (t - 3) le_rfl, hm2]; exact hxtA3
  · refine ⟨q, hqA'2, by rw [hhi]; exact hqxt1, ?_, ?_⟩
    · rw [hm2]; exact hqxt
    · rw [hAeq (t - 3) le_rfl]; exact hqA3

/-! ### the paper's `v₁-⋯-v_s` -/

/-- *"Choose a path `v₁-⋯-v_s` with `s` minimum such that `v₁,…,v_s ∈ A₂`, and `v₁` is
adjacent to `q`, and `v_s ∈ A₃`."*  The only consequence of the minimality that the proof
uses is that `q` has **no** neighbour among `v₂,…,v_s`; that is exactly what an *induced*
path out of `q` delivers, so the chain is produced as the tail of an induced `q`-to-`A₃`
path inside `A₂ ∪ {q}`. -/
private theorem exists_attach_chain {G : SimpleGraph V} {A2 A3 : Set V} {q : V}
    (hA2conn : ConnectedSet G A2) (hqA2 : q ∉ A2)
    (hA3sub : A3 ⊆ A2) {a : V} (ha : a ∈ A3)
    (hqb : ∃ b ∈ A2, G.Adj q b) :
    ∃ (v : V) (L : List V) (w : V), (v :: L).getLast? = some w ∧
      (∀ y ∈ v :: L, y ∈ A2) ∧ List.IsChain G.Adj (v :: L) ∧
      G.Adj q v ∧ w ∈ A3 ∧ (∀ y ∈ L, ¬ G.Adj q y) := by
  have hconn : ConnectedSet G (A2 ∪ ({q} : Set V)) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hA2conn hqb
  obtain ⟨P, hP, hPmem⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hconn
    (show q ∈ A2 ∪ ({q} : Set V) from Or.inr rfl)
    (show a ∈ A2 ∪ ({q} : Set V) from Or.inl (hA3sub ha))
  have hnodup : P.Nodup := PathBasics.path_nodup hP.1
  have hpos : 0 < P.length := PathBasics.path_length_pos hP.1
  obtain ⟨L, hPeq⟩ : ∃ L, P = q :: L := by
    cases P with
    | nil => simp at hpos
    | cons b c =>
      have hb : b = q := by simpa using hP.2.1
      exact ⟨c, by rw [hb]⟩
  subst hPeq
  have hnd := List.nodup_cons.mp hnodup
  have hLne : L ≠ [] := by
    intro hnil
    subst hnil
    have hqa : q = a := by simpa using hP.2.2
    exact hqA2 (hA3sub (hqa ▸ ha))
  obtain ⟨v, L', rfl⟩ : ∃ v L', L = v :: L' := by
    cases L with
    | nil => exact absurd rfl hLne
    | cons b c => exact ⟨b, c, rfl⟩
  have hne2 : (v :: L') ≠ [] := by simp
  have hlastP : (q :: v :: L').getLast (by simp) = (v :: L').getLast hne2 :=
    List.getLast_cons hne2
  have hlast : (q :: v :: L').getLast? = some a := hP.2.2
  rw [List.getLast?_eq_some_getLast (by simp), hlastP] at hlast
  have hwa : (v :: L').getLast hne2 = a := by simpa using hlast
  refine ⟨v, L', (v :: L').getLast hne2, List.getLast?_eq_some_getLast hne2, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro y hy
    have hyP : y ∈ q :: v :: L' := List.mem_cons_of_mem _ hy
    have hyq : y ≠ q := by
      intro h; subst h; exact hnd.1 hy
    rcases hPmem y hyP with h | h
    · exact h
    · exact absurd h hyq
  · exact (InducedPathExtraction.isChain_of_isPathList hP.1).of_cons
  · have h := PathBasics.path_adj_succ hP.1 (i := 0) (by simp)
    simpa using h
  · rw [hwa]; exact ha
  · intro y hy
    have hyP : y ∈ q :: v :: L' := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy)
    obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hyP
    have hj0 : j ≠ 0 := by
      intro h
      subst h
      simp only [List.getElem_cons_zero] at hjy
      exact hnd.1 (hjy ▸ List.mem_cons_of_mem _ hy)
    have hj1 : j ≠ 1 := by
      intro h
      subst h
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hjy
      exact (List.nodup_cons.mp hnd.2).1 (hjy ▸ hy)
    intro hadj
    have h0 : (0 : ℕ) < (q :: v :: L').length := by simp
    have hq0 : (q :: v :: L')[0]'h0 = q := rfl
    have hcon := (PathBasics.path_adj_iff hP.1 h0 hj).mp (by rw [hq0, hjy]; exact hadj)
    omega

/-! ### *"Let `R` be a path between `q` and `x_{t−1}` with interior in `S`. … so by 13.6 it
has length 3, that is, `R` has length 2.  Let its middle vertex be `r`."* -/

private theorem middle_vertex {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x (t + 1)) (ht : 4 ≤ t)
    (hxt1X1 : VertexComplete G (x (t + 1)) (wheelSystemX x (t - 1)))
    (hxt1noA2 : ∀ a ∈ wheelSystemA G z A₀ x (t - 2), ¬ G.Adj (x (t + 1)) a)
    {q : V} (hzq : ¬ G.Adj z q) (hqxt1 : G.Adj q (x (t + 1)))
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    {S : Set V} (hScon : ConnectedSet G S)
    (hSsub : S ⊆ wheelSystemA G z A₀ x (t - 2))
    (hqS : ∃ b ∈ S, G.Adj q b) (hx1S : ∃ a ∈ S, G.Adj (x (t - 1)) a) :
    ∃ r ∈ S, G.Adj q r ∧ G.Adj r (x (t - 1)) := by
  obtain ⟨-, hinj, hout, -, hcond2, hcond3, hzadj⟩ := id hws
  have hBerge : Berge G := hG.1.1.1.1
  have hF5 : InF5 G := hG.1.1
  have hx1nc : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 2)) := by
    have h := hcond3 (t - 1) (by omega) (by omega)
    rwa [show t - 1 - 1 = t - 2 from by omega] at h
  have hqnotA2 : q ∉ wheelSystemA G z A₀ x (t - 2) := fun h => hxt1noA2 q h hqxt1.symm
  have hqne_z : q ≠ z := fun h => hqx1 (by rw [h]; exact hzadj (t - 1) (by omega))
  have hx1notA2 : x (t - 1) ∉ wheelSystemA G z A₀ x (t - 2) :=
    Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t + 1 by omega)
  have hqnotS : q ∉ S := fun h => hqnotA2 (hSsub h)
  have hx1notS : x (t - 1) ∉ S := fun h => hx1notA2 (hSsub h)
  obtain ⟨R, hR, hRmem⟩ :=
    PathInteriorIn.exists_path_mem_of_interior_in hScon hqnotS hx1notS hqS hx1S
  have hRint : ∀ y ∈ SPGT.interior R, y ∈ S := by
    intro y hy
    obtain ⟨hyR, hy1, hy2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hy
    rcases hRmem y hyR with h | h | h
    · exact absurd h hy1
    · exact absurd h hy2
    · exact h
  have hqnex1 : q ≠ x (t - 1) := fun h => hx1nc (h ▸ hqX2)
  have hRlen : 2 ≤ pathLength R := two_le_pathLength_of_nonadj hR hqnex1 hqx1
  have hxt1x1 : G.Adj (x (t + 1)) (x (t - 1)) :=
    hxt1X1 (x (t - 1)) (WheelSystemBasics.self_mem_wheelSystemX x le_rfl)
  have hxt1notR : x (t + 1) ∉ R := by
    intro hm
    rcases hRmem _ hm with h | h | h
    · exact G.irrefl (h ▸ hqxt1)
    · have := hinj (t + 1) le_rfl (t - 1) (by omega) h; omega
    · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t + 1 ≤ t + 1 from le_rfl)
        (hSsub h)
  have hhole : IsHoleList G (x (t + 1) :: R) :=
    PrismBasics.isHoleList_of_path_add_vertex hR hRlen hqxt1.symm hxt1x1 hxt1notR
      (fun y hy => hxt1noA2 y (hSsub (hRint y hy)))
  have hReven : Even (pathLength R) := by
    have hev := hBerge.1 _ hhole
    rw [PrismBasics.holeLength_cons _ (PathBasics.path_ne_nil hR.1)] at hev
    obtain ⟨k, hk⟩ := hev
    exact ⟨k - 1, by omega⟩
  have hznotR : z ∉ R := by
    intro hm
    rcases hRmem _ hm with h | h | h
    · exact hqne_z h.symm
    · exact (hout (t - 1) (by omega)).2 h.symm
    · exact Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t + 1 by omega) (hSsub h)
  have hPz : IsPathFrom G (R ++ [z]) q z := by
    refine PathAttach.isPathFrom_concat hR (hzadj (t - 1) (by omega)) hznotR ?_
    intro y hy hyne
    rcases hRmem y hy with h | h | h
    · rw [h]; exact hzq
    · exact absurd h hyne
    · exact WheelSystemBasics.wheelSystemA_no_nbr (hSsub h)
  have hPzlen : pathLength (R ++ [z]) = pathLength R + 1 := by
    have hpos : 0 < R.length := PathBasics.path_length_pos hR.1
    simp only [pathLength, List.length_append, List.length_singleton]
    omega
  have hPzodd : Odd (pathLength (R ++ [z])) := by
    rw [hPzlen]; exact Even.add_one hReven
  have hzX2 : VertexComplete G z (wheelSystemX x (t - 2)) := by
    rintro w ⟨j, hj, rfl⟩; exact hzadj j (by omega)
  have hX2anti : AnticonnectedSet G (wheelSystemX x (t - 2)) :=
    Thm203Prelim.anticonnected_wheelSystemX hws (t - 2) (by omega)
  have hXsub : wheelSystemX x (t - 2) ⊆ {v : V | v ∈ R ++ [z]}ᶜ := by
    rintro y ⟨j, hj, rfl⟩ hmem
    rcases List.mem_append.mp hmem with h | h
    · rcases hRmem _ h with e | e | e
      · have hadj := hqX2 (x j) ⟨j, hj, rfl⟩
        rw [e] at hadj
        exact G.irrefl hadj
      · have := hinj j (by omega) (t - 1) (by omega) e; omega
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show j ≤ t + 1 by omega) (hSsub e)
    · rw [List.mem_singleton] at h
      exact (hout j (by omega)).2 h
  have hclass : ∀ y ∈ R ++ [z], VertexComplete G y (wheelSystemX x (t - 2)) →
      y = q ∨ y = z := by
    intro y hy hyc
    rcases List.mem_append.mp hy with h | h
    · rcases hRmem y h with e | e | e
      · exact Or.inl e
      · exact absurd (e ▸ hyc) hx1nc
      · exact absurd hyc (WheelSystemBasics.wheelSystemA_no_complete (hSsub e))
    · rw [List.mem_singleton] at h; exact Or.inr h
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hF5 (R ++ [z]) q z hPz hPzodd
      (wheelSystemX x (t - 2)) hXsub hX2anti hqX2 hzX2 with halt1 | halt2
  · exfalso
    obtain ⟨u, hu, v, hv, hadj, huc, hvc⟩ := halt1
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
  exact ⟨r, hRint r (by rw [hintR]; simp), hqr, hrx1⟩

/-! ### the tail of claim (1): the antihole, 2.2 in `Ḡ`, the 5-hole, and the `{q}`-square -/

private theorem step_one_square {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x (t + 1)) (ht : 4 ≤ t)
    {q : V} (hzq : ¬ G.Adj z q) (hqA1 : q ∈ wheelSystemA G z A₀ x (t - 1))
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    (hno3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a)
    {r : V} (hrA2 : r ∈ wheelSystemA G z A₀ x (t - 2))
    (hqr : G.Adj q r) (hrx1 : G.Adj r (x (t - 1))) :
    IsYSquare G z A₀ x (t - 1) ({q} : Set V) := by
  obtain ⟨-, hinj, hout, -, hcond2, hcond3, hzadj⟩ := id hws
  have hBerge : Berge G := hG.1.1.1.1
  have hws_t : IsWheelSystem G z A₀ x t :=
    YDiamondTruncation.wheelSystem_truncate hws (by omega) (by omega)
  have hx1nc : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 2)) := by
    have h := hcond3 (t - 1) (by omega) (by omega)
    rwa [show t - 1 - 1 = t - 2 from by omega] at h
  have hqnotA2 : q ∉ wheelSystemA G z A₀ x (t - 2) := fun h =>
    WheelSystemBasics.wheelSystemA_no_complete h hqX2
  have hqne_z : q ≠ z := fun h => hqx1 (by rw [h]; exact hzadj (t - 1) (by omega))
  have hqnex1 : q ≠ x (t - 1) := fun h => hx1nc (h ▸ hqX2)
  have hx1notA2 : x (t - 1) ∉ wheelSystemA G z A₀ x (t - 2) :=
    Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t + 1 by omega)
  have hzX2 : VertexComplete G z (wheelSystemX x (t - 2)) := by
    rintro w ⟨j, hj, rfl⟩; exact hzadj j (by omega)
  have hA3conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hznotA3 : z ∉ wheelSystemA G z A₀ x (t - 3) :=
    Thm203Prelim.z_notMem_wheelSystemA hws (by omega)
  have hzA3nadj : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj z a :=
    fun a ha => WheelSystemBasics.wheelSystemA_no_nbr ha
  have hrnotA3 : r ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hno3 r h hrx1.symm
  -- "Let `Q` be an antipath between `r` and `x_{t−1}` with interior in `X_{t−2}`."
  obtain ⟨Q, hQ, hQint⟩ := Thm203Step3Aux.exists_antipath_to_A2 hws_t ht hrA2
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
    · exact Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t + 1 by omega)
        (h.symm ▸ hrA2)
    · exact G.irrefl (hzX2 z h)
  have hx1ner : x (t - 1) ≠ r := fun h => hx1notA2 (by rw [h]; exact hrA2)
  have hQlen1 : 1 ≤ pathLength Q := one_le_pathLength_of_ne (G := Gᶜ) hQ hx1ner
  have hznotr : z ≠ r := fun h =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t + 1 by omega) (h.symm ▸ hrA2)
  -- "Since `r-Q-x_{t−1}-q-z-r` is an antihole, it follows that `Q` is odd."
  have hantihole : IsAntiholeList G (z :: q :: Q) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices (G := Gᶜ) hQ hQlen1 ?_ ?_ ?_
      hqnotQ hznotQ ?_ ?_ ?_ ?_
    · rw [SimpleGraph.compl_adj]; exact ⟨hqnex1, hqx1⟩
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
    · rw [h]; exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t + 1 by omega)
    · rw [h]; exact hrnotA3
    · obtain ⟨j, hj, rfl⟩ := h
      exact Thm203Prelim.x_notMem_wheelSystemA hws (show j ≤ t + 1 by omega)
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
    · rw [show j = t - 2 from by omega]; exact hadj
  -- "Since `z-x_{t−1}-r-q-x_{t−2}-z` is not an odd hole it follows that `x_{t−2}` is
  --  adjacent to `x_{t−1}`."
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
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 2 ≤ t + 1 by omega)
          (by rw [h]; exact hrA2)
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 2 ≤ t + 1 by omega)
          (show x (t - 2) ∈ wheelSystemA G z A₀ x (t - 1) by rw [h]; exact hqA1)
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
  -- "But then `x₀,…,x_{t−1}` is a `{q}`-square of height `t − 1`."
  refine ⟨YDiamondTruncation.wheelSystem_truncate hws (by omega) (by omega),
    ⟨q, rfl⟩, Thm134RegionAux.connectedSet_singleton Gᶜ q, ⟨?_, ?_⟩, ?_, ?_,
    by omega, ?_, ?_, ?_⟩
  · intro h; rw [Set.mem_singleton_iff] at h; exact hqne_z h.symm
  · intro i hi h
    rw [Set.mem_singleton_iff] at h
    exact Thm203Prelim.x_notMem_wheelSystemA hws (show i ≤ t + 1 by omega)
      (show x i ∈ wheelSystemA G z A₀ x (t - 1) by rw [h]; exact hqA1)
  · intro i hi y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact (hqX2 (x i) ⟨i, by omega, rfl⟩).symm
  · intro hcc; exact hqx1 (hcc q rfl).symm
  · rw [show t - 1 - 1 = t - 2 from by omega]; exact hx2x1.symm
  · rw [show t - 1 - 2 = t - 3 from by omega]; exact hno3
  · rw [show t - 1 - 1 = t - 2 from by omega, show t - 1 - 2 = t - 3 from by omega]
    exact ⟨r, hrA2, hrx1, hrA3⟩

/-! ### *"From the antihole `x_{t−1}-Q-r-z-q-x_{t−1}` it follows that `Q` is odd."* -/

private theorem antipath_odd {G : SimpleGraph V} (hBerge : Berge G)
    {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x (t + 1)) (ht : 4 ≤ t)
    {q : V} (hzq : ¬ G.Adj z q)
    (hqX2 : VertexComplete G q (wheelSystemX x (t - 2)))
    (hqx1 : ¬ G.Adj q (x (t - 1)))
    {r : V} (hrA2 : r ∈ wheelSystemA G z A₀ x (t - 2))
    (hqr : G.Adj q r) (hrx1 : G.Adj r (x (t - 1)))
    {Q : List V} (hQ : IsAntipathFrom G Q (x (t - 1)) r)
    (hQint : ∀ y ∈ SPGT.interior Q, y ∈ wheelSystemX x (t - 2)) :
    Odd (pathLength Q) ∧
      (∀ y ∈ Q, y = x (t - 1) ∨ y = r ∨ y ∈ wheelSystemX x (t - 2)) := by
  obtain ⟨-, hinj, hout, -, hcond2, hcond3, hzadj⟩ := id hws
  have hx1nc : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 2)) := by
    have h := hcond3 (t - 1) (by omega) (by omega)
    rwa [show t - 1 - 1 = t - 2 from by omega] at h
  have hqnotA2 : q ∉ wheelSystemA G z A₀ x (t - 2) := fun h =>
    WheelSystemBasics.wheelSystemA_no_complete h hqX2
  have hqne_z : q ≠ z := fun h => hqx1 (by rw [h]; exact hzadj (t - 1) (by omega))
  have hqnex1 : q ≠ x (t - 1) := fun h => hx1nc (h ▸ hqX2)
  have hx1notA2 : x (t - 1) ∉ wheelSystemA G z A₀ x (t - 2) :=
    Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t + 1 by omega)
  have hzX2 : VertexComplete G z (wheelSystemX x (t - 2)) := by
    rintro w ⟨j, hj, rfl⟩; exact hzadj j (by omega)
  have hQmem : ∀ y ∈ Q, y = x (t - 1) ∨ y = r ∨ y ∈ wheelSystemX x (t - 2) := by
    intro y hy
    by_cases h1 : y = x (t - 1)
    · exact Or.inl h1
    by_cases h2 : y = r
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hQint y
      ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hy, h1, h2⟩)))
  refine ⟨?_, hQmem⟩
  have hqnotQ : q ∉ Q := by
    intro hy
    rcases hQmem q hy with h | h | h
    · exact hqnex1 h
    · exact hqnotA2 (by rw [h]; exact hrA2)
    · exact G.irrefl (hqX2 q h)
  have hznotr : z ≠ r := fun h =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t + 1 by omega) (h.symm ▸ hrA2)
  have hznotQ : z ∉ Q := by
    intro hy
    rcases hQmem z hy with h | h | h
    · exact (hout (t - 1) (by omega)).2 h.symm
    · exact hznotr h
    · exact G.irrefl (hzX2 z h)
  have hx1ner : x (t - 1) ≠ r := fun h => hx1notA2 (by rw [h]; exact hrA2)
  have hQlen1 : 1 ≤ pathLength Q := one_le_pathLength_of_ne (G := Gᶜ) hQ hx1ner
  have hantihole : IsAntiholeList G (z :: q :: Q) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices (G := Gᶜ) hQ hQlen1 ?_ ?_ ?_
      hqnotQ hznotQ ?_ ?_ ?_ ?_
    · rw [SimpleGraph.compl_adj]; exact ⟨hqnex1, hqx1⟩
    · rw [SimpleGraph.compl_adj]
      exact ⟨hznotr, WheelSystemBasics.wheelSystemA_no_nbr hrA2⟩
    · rw [SimpleGraph.compl_adj]; exact ⟨hqne_z, fun h => hzq h.symm⟩
    · intro h; exact not_adj_of_compl_adj h hqr
    · intro h; exact not_adj_of_compl_adj h (hzadj (t - 1) (by omega))
    · intro y hy h
      exact not_adj_of_compl_adj h (hqX2 y (hQint y hy))
    · intro y hy h
      exact not_adj_of_compl_adj h (hzX2 y (hQint y hy))
  have hev := hBerge.2 _ hantihole
  rw [PrismBasics.holeLength_cons_cons q z (PathBasics.path_ne_nil hQ.1)] at hev
  obtain ⟨k, hk⟩ := hev
  exact ⟨k - 2, by omega⟩

theorem thm_20_5 (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (Y : Set V) (hYsub : ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (x : ℕ → V) (t : ℕ) (hpol : IsPolishedYDiamond G z A₀ x (t + 1) Y)
    (ht : 5 ≤ t + 1) :
    ∃ Y' : Set V, Y'.Nonempty ∧ AnticonnectedSet G Y' ∧
      (∀ y ∈ Y', y ∉ A₀ ∧ y ≠ z) ∧
      (Y ⊆ Y' ∨ ¬ VertexComplete G z Y') ∧
      ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y')) := by
  by_contra hcon
  have key : ∀ Y' : Set V, Y'.Nonempty → AnticonnectedSet G Y' →
      (∀ y ∈ Y', y ∉ A₀ ∧ y ≠ z) → (Y ⊆ Y' ∨ ¬ VertexComplete G z Y') →
      ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y')) → False :=
    fun Y' h1 h2 h3 h4 h5 => hcon ⟨Y', h1, h2, h3, h4, h5⟩
  have ht4 : 4 ≤ t := by omega
  obtain ⟨hws, hYne', hYanti', ⟨hzY, hxY⟩, hVC, hnVC, -, hxt1X1', -⟩ := id hpol.1
  have hxt1X1 : VertexComplete G (x (t + 1)) (wheelSystemX x (t - 1)) := hxt1X1'
  have hxtXn : ¬ VertexComplete G (x t) (wheelSystemX x (t - 2)) := hpol.2.2.1
  have hxt1noA : ∀ a ∈ wheelSystemA G z A₀ x (t - 2), ¬ G.Adj (x (t + 1)) a := hpol.2.2.2.1
  have hxtA2 : ∃ a ∈ wheelSystemA G z A₀ x (t - 2), G.Adj (x t) a := hpol.2.2.2.2.1
  obtain ⟨q, hqA1, hqxt1, hqxt, bq, hbqA2, hqbq⟩ :
      ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj a (x (t + 1)) ∧ G.Adj a (x t) ∧
        ∃ b ∈ wheelSystemA G z A₀ x (t - 2), G.Adj a b := hpol.2.2.2.2.2
  have hnadj1t : ¬ G.Adj (x (t + 1)) (x t) := YDiamondTruncation.ydiamond_top_nonadj hpol.1
  obtain ⟨-, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := id hws
  have hBerge : Berge G := hG.1.1.1.1
  have hws_t : IsWheelSystem G z A₀ x t :=
    YDiamondTruncation.wheelSystem_truncate hws (by omega) (by omega)
  -- ###  standing facts about `q`
  have hzq : ¬ G.Adj z q := WheelSystemBasics.wheelSystemA_no_nbr hqA1
  have hqnotA2 : q ∉ wheelSystemA G z A₀ x (t - 2) := fun h => hxt1noA q h hqxt1.symm
  -- "From the maximality of `A_{t−2}` it follows that `q` is `X_{t−2}`-complete."
  have hqX2 : VertexComplete G q (wheelSystemX x (t - 2)) :=
    Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (by omega) hzq hqnotA2
      ⟨bq, hbqA2, hqbq⟩
  -- "and therefore nonadjacent to `x_{t−1}`"
  have hqx1 : ¬ G.Adj q (x (t - 1)) := by
    intro hadj
    refine WheelSystemBasics.wheelSystemA_no_complete hqA1 ?_
    rintro w ⟨j, hj, rfl⟩
    rcases Nat.lt_or_ge j (t - 1) with h | h
    · exact hqX2 (x j) ⟨j, by omega, rfl⟩
    · rw [show j = t - 1 from by omega]; exact hadj
  have hqne_z : q ≠ z := fun h =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 1 ≤ t + 1 by omega) (h ▸ hqA1)
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
  have hA2conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 2)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA3conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA3subA2 : wheelSystemA G z A₀ x (t - 3) ⊆ wheelSystemA G z A₀ x (t - 2) :=
    WheelSystemBasics.wheelSystemA_mono (by omega)
  -- =====================================================================
  -- ###  (1)  `x_{t−1}` has neighbours in `A_{t−3}`.
  -- =====================================================================
  have step1 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a := by
    by_contra hno3'
    push Not at hno3'
    have hno3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a := hno3'
    have hx1A2 : ∃ a ∈ wheelSystemA G z A₀ x (t - 2), G.Adj (x (t - 1)) a :=
      Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
    obtain ⟨r, hrA2, hqr, hrx1⟩ := middle_vertex hG hframe hws ht4 hxt1X1 hxt1noA hzq
      hqxt1 hqX2 hqx1 hA2conn subset_rfl ⟨bq, hbqA2, hqbq⟩ hx1A2
    exact key ({q} : Set V) hQne hQanti hQsub (Or.inr hQzn)
      (Or.inr (Or.inl ⟨x, step_one_square hG hframe hws ht4 hzq hqA1 hqX2 hqx1 hno3
        hrA2 hqr hrx1⟩))
  -- =====================================================================
  -- ###  the chain `v₁-⋯-v_s` and the re-chosen `R`
  -- =====================================================================
  obtain ⟨a3, ha3⟩ : (wheelSystemA G z A₀ x (t - 3)).Nonempty := by
    obtain ⟨a0, ha0⟩ := hframe.1
    exact ⟨a0, Thm203Prelim.A₀_subset_wheelSystemA' hframe hws (by omega) ha0⟩
  obtain ⟨v, L, w, hLlast, hLA2, hLchain, hqv, hwA3, hLnoq⟩ :=
    exists_attach_chain hA2conn hqnotA2 hA3subA2 ha3 ⟨bq, hbqA2, hqbq⟩
  have hwmem : w ∈ v :: L := List.mem_of_mem_getLast? hLlast
  have hWconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ v :: L}) :=
    ConnectedSetUnionAttach.connectedSet_union hA3conn
      (InducedPathExtraction.connectedSet_setOf_mem_of_isChain hLchain)
      (Or.inl ⟨w, hwA3, hwmem⟩)
  have hWsub : wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ v :: L} ⊆
      wheelSystemA G z A₀ x (t - 2) := by
    rintro y (hy | hy)
    · exact hA3subA2 hy
    · exact hLA2 y hy
  obtain ⟨r, hrW, hqr, hrx1⟩ := middle_vertex hG hframe hws ht4 hxt1X1 hxt1noA hzq
    hqxt1 hqX2 hqx1 hWconn hWsub ⟨v, Or.inr (by simp), hqv⟩
    (by obtain ⟨a, ha, hadj⟩ := step1; exact ⟨a, Or.inl ha, hadj⟩)
  have hrA2 : r ∈ wheelSystemA G z A₀ x (t - 2) := hWsub hrW
  -- =====================================================================
  -- ###  (2)  `q` has neighbours in `A_{t−3}`.
  -- =====================================================================
  have step2 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q a := by
    by_contra hnoq'
    push Not at hnoq'
    have hnoq : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj q a := hnoq'
    -- "Then `s ≥ 2` and `r = v₁`."
    have hrnotA3 : r ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hnoq r h hqr
    have hrL : r ∈ v :: L := by
      rcases hrW with h | h
      · exact absurd h hrnotA3
      · exact h
    have hrv : r = v := by
      rcases List.mem_cons.mp hrL with h | h
      · exact h
      · exact absurd hqr (hLnoq r h)
    have hvnotA3 : v ∉ wheelSystemA G z A₀ x (t - 3) := by rw [← hrv]; exact hrnotA3
    have hwL : w ∈ L := by
      rcases List.mem_cons.mp hwmem with h | h
      · exact absurd hwA3 (h.symm ▸ hvnotA3)
      · exact h
    have hLchain' : List.IsChain G.Adj L := hLchain.of_cons
    obtain ⟨v2, L2, hL⟩ : ∃ v2 L2, L = v2 :: L2 := by
      cases L with
      | nil => simp at hwL
      | cons b c => exact ⟨b, c, rfl⟩
    have hvv2 : G.Adj v v2 := by
      have h := hLchain
      rw [hL] at h
      exact h.rel
    have hv2L : v2 ∈ L := by rw [hL]; simp
    have hTconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ L}) :=
      ConnectedSetUnionAttach.connectedSet_union hA3conn
        (InducedPathExtraction.connectedSet_setOf_mem_of_isChain hLchain')
        (Or.inl ⟨w, hwA3, hwL⟩)
    have hTsub : wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ L} ⊆
        wheelSystemA G z A₀ x (t - 2) := by
      rintro y (hy | hy)
      · exact hA3subA2 hy
      · exact hLA2 y (List.mem_cons_of_mem _ hy)
    have hvnotL : v ∉ L := fun h => hLnoq v h hqv
    -- "Let `Q` be an antipath between `x_{t−1}` and `r` with interior in `X_{t−2}`."
    obtain ⟨Q, hQ, hQint⟩ := Thm203Step3Aux.exists_antipath_to_A2 hws_t ht4 hrA2
    obtain ⟨hQodd, hQmem⟩ :=
      antipath_odd hBerge hws ht4 hzq hqX2 hqx1 hrA2 hqr hrx1 hQ hQint
    have hqnex1 : q ≠ x (t - 1) := by
      intro h
      have hx1nc := hcond3 (t - 1) (by omega) (by omega)
      rw [show t - 1 - 1 = t - 2 from by omega] at hx1nc
      exact hx1nc (h ▸ hqX2)
    have hqnotQ : q ∉ Q := by
      intro hy
      rcases hQmem q hy with h | h | h
      · exact hqnex1 h
      · exact hqnotA2 (by rw [h]; exact hrA2)
      · exact G.irrefl (hqX2 q h)
    have hxt1notQ : x (t + 1) ∉ Q := by
      intro hy
      rcases hQmem _ hy with h | h | h
      · have := hinj (t + 1) le_rfl (t - 1) (by omega) h; omega
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t + 1 ≤ t + 1 from le_rfl)
          (show x (t + 1) ∈ wheelSystemA G z A₀ x (t - 2) by rw [h]; exact hrA2)
      · obtain ⟨j, hj, he⟩ := h
        have := hinj (t + 1) le_rfl j (by omega) he; omega
    -- "Hence the antipath `q-x_{t−1}-Q-r-x_{t+1}` is odd with length ≥ 5."
    have hP : IsAntipathFrom G (q :: (Q ++ [x (t + 1)])) q (x (t + 1)) := by
      refine PathAttach.isPathFrom_cons_concat (G := Gᶜ) hQ ?_ ?_ ?_ ?_ hqnotQ hxt1notQ ?_ ?_
      · rw [SimpleGraph.compl_adj]; exact ⟨hqnex1, hqx1⟩
      · rw [SimpleGraph.compl_adj]
        refine ⟨fun h => ?_, fun h => hxt1noA r hrA2 h⟩
        exact Thm203Prelim.x_notMem_wheelSystemA hws (show t + 1 ≤ t + 1 from le_rfl)
          (show x (t + 1) ∈ wheelSystemA G z A₀ x (t - 2) by rw [h]; exact hrA2)
      · intro h; exact not_adj_of_compl_adj h hqxt1
      · intro h
        exact Thm203Prelim.x_notMem_wheelSystemA hws (show t + 1 ≤ t + 1 from le_rfl)
          (show x (t + 1) ∈ wheelSystemA G z A₀ x (t - 1) by rw [← h]; exact hqA1)
      · intro y hy hyne hc
        refine not_adj_of_compl_adj hc ?_
        rcases hQmem y hy with h | h | h
        · exact absurd h hyne
        · rw [h]; exact hqr
        · exact hqX2 y h
      · intro y hy hyne hc
        refine not_adj_of_compl_adj hc ?_
        rcases hQmem y hy with h | h | h
        · rw [h]
          exact hxt1X1 (x (t - 1)) (WheelSystemBasics.self_mem_wheelSystemX x le_rfl)
        · exact absurd h hyne
        · obtain ⟨j, hj, rfl⟩ := h
          exact hxt1X1 (x j) ⟨j, by omega, rfl⟩
    have hPlen : pathLength (q :: (Q ++ [x (t + 1)])) = pathLength Q + 2 := by
      rw [PathAttach.pathLength_cons_append_singleton]
      have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
      simp only [pathLength]; omega
    have hPodd : Odd (pathLength (q :: (Q ++ [x (t + 1)]))) := by
      rw [hPlen]; obtain ⟨k, hk⟩ := hQodd; exact ⟨k + 1, by omega⟩
    have hQlen3 : 3 ≤ pathLength Q := by
      obtain ⟨k, hk⟩ := hQodd
      by_contra hlt
      have h1 : pathLength Q = 1 := by omega
      exact not_adj_of_compl_adj
        (PathBasics.isPathFrom_ends_adj_of_length_one (G := Gᶜ) hQ h1) hrx1.symm
    -- "contrary to 13.6 applied in `Ḡ`"
    have hPT : ∀ y ∈ q :: (Q ++ [x (t + 1)]),
        y ∉ wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ L} := by
      intro y hy
      rcases PathAttach.mem_cons_append_singleton.mp hy with h | h | h
      · subst h; exact fun hc => hqnotA2 (hTsub hc)
      · rcases hQmem y h with e | e | e
        · rw [e]
          exact fun hc => Thm203Prelim.x_notMem_wheelSystemA hws
            (show t - 1 ≤ t + 1 by omega) (hTsub hc)
        · rw [e]
          rintro (hc | hc)
          · exact hrnotA3 hc
          · exact hvnotL (hrv ▸ hc)
        · obtain ⟨j, hj, rfl⟩ := e
          exact fun hc => Thm203Prelim.x_notMem_wheelSystemA hws
            (show j ≤ t + 1 by omega) (hTsub hc)
      · subst h
        exact fun hc => Thm203Prelim.x_notMem_wheelSystemA hws
          (show t + 1 ≤ t + 1 from le_rfl) (hTsub hc)
    have huT : ∀ a ∈ wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ L}, ¬ G.Adj q a := by
      rintro a (ha | ha)
      · exact hnoq a ha
      · exact hLnoq a ha
    have hvT : ∀ a ∈ wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ L},
        ¬ G.Adj (x (t + 1)) a := fun a ha => hxt1noA a (hTsub ha)
    have hintT : ∀ y ∈ SPGT.interior (q :: (Q ++ [x (t + 1)])),
        ∃ a ∈ wheelSystemA G z A₀ x (t - 3) ∪ {y : V | y ∈ L}, G.Adj y a := by
      intro y hy
      obtain ⟨hyP, hy1, hy2⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hy
      rcases PathAttach.mem_cons_append_singleton.mp hyP with h | h | h
      · exact absurd h hy1
      · rcases hQmem y h with e | e | e
        · obtain ⟨a, ha, hadj⟩ := step1
          exact ⟨a, Or.inl ha, by rw [e]; exact hadj⟩
        · exact ⟨v2, Or.inr hv2L, by rw [e, hrv]; exact hvv2⟩
        · obtain ⟨j, hj, rfl⟩ := e
          obtain ⟨a, ha, hadj⟩ :=
            Thm203Prelim.exists_nbr_wheelSystemA hframe hws (show j ≤ t + 1 by omega)
              (show 1 ≤ t - 3 by omega) (show j ≤ t - 3 + 1 by omega)
          exact ⟨a, Or.inl ha, hadj⟩
      · exact absurd h hy2
    have hlen3 := Thm203AntipathTools.antipath_length_three_of_odd hG.1.1 hTconn hP hPodd
      hqxt1 hPT huT hvT hintT
    rw [hPlen] at hlen3
    omega
  -- "and therefore `r ∈ A_{t−3}`": with `q` having a neighbour in `A_{t−3}`, the path `R`
  -- may be chosen with interior inside `A_{t−3}` itself.
  obtain ⟨r₂, hr₂A3, hqr₂, hr₂x1⟩ := middle_vertex hG hframe hws ht4 hxt1X1 hxt1noA hzq
    hqxt1 hqX2 hqx1 hA3conn hA3subA2 step2 step1
  -- =====================================================================
  -- ###  (3)  `x_{t−1}` is not `X_{t−3}`-complete.
  -- =====================================================================
  have step3 : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)) := by
    intro hcomp
    refine key ({q} : Set V) hQne hQanti hQsub (Or.inr hQzn) (Or.inl ⟨x, ?_⟩)
    refine ⟨YDiamondTruncation.wheelSystem_truncate hws (by omega) (by omega),
      hQne, hQanti, ⟨?_, ?_⟩, ?_, ?_, by omega, ?_, ?_⟩
    · intro h; rw [Set.mem_singleton_iff] at h; exact hqne_z h.symm
    · intro i hi h
      rw [Set.mem_singleton_iff] at h
      exact Thm203Prelim.x_notMem_wheelSystemA hws (show i ≤ t + 1 by omega)
        (show x i ∈ wheelSystemA G z A₀ x (t - 1) by rw [h]; exact hqA1)
    · intro i hi y hy
      rw [Set.mem_singleton_iff] at hy; subst hy
      exact (hqX2 (x i) ⟨i, by omega, rfl⟩).symm
    · intro hcc; exact hqx1 (hcc q rfl).symm
    · rw [show t - 1 - 2 = t - 3 from by omega]; exact hcomp
    · rw [show t - 1 - 2 = t - 3 from by omega]; exact step1
  -- ###  the hub `Y ∪ {x_{t+1}}`
  have hxt1notY : x (t + 1) ∉ Y := hxY (t + 1) le_rfl
  have hY2anti : AnticonnectedSet G (Y ∪ {x (t + 1)}) :=
    YDiamondTruncation.anticonnected_union_singleton hYanti' hxt1notY hnVC
  have hY2ne : (Y ∪ {x (t + 1)}).Nonempty := hYne.mono Set.subset_union_left
  have hY2sub : ∀ y ∈ Y ∪ {x (t + 1)}, y ∉ A₀ ∧ y ≠ z := by
    rintro y (hy | hy)
    · exact hYsub y hy
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact hout (t + 1) le_rfl
  have hzY2 : z ∉ Y ∪ {x (t + 1)} := by
    rintro (h | h)
    · exact hzY h
    · rw [Set.mem_singleton_iff] at h; exact (hout (t + 1) le_rfl).2 h.symm
  have hxY2 : ∀ i ≤ t, x i ∉ Y ∪ {x (t + 1)} := by
    rintro i hi (h | h)
    · exact hxY i (by omega) h
    · rw [Set.mem_singleton_iff] at h
      have := hinj i (by omega) (t + 1) le_rfl h; omega
  have hVC2 : ∀ i < t, VertexComplete G (x i) (Y ∪ {x (t + 1)}) := by
    rintro i hi y (hy | hy)
    · exact hVC i (by omega) y hy
    · rw [Set.mem_singleton_iff] at hy; subst hy
      exact (hxt1X1 (x i) ⟨i, by omega, rfl⟩).symm
  have hnVC2 : ¬ VertexComplete G (x t) (Y ∪ {x (t + 1)}) := fun h =>
    hnadj1t (h (x (t + 1)) (Or.inr rfl)).symm
  -- =====================================================================
  -- ###  (4)  `x_t` has no neighbour in `A_{t−3}`.
  -- =====================================================================
  have step4 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x t) a := by
    intro a ha hadj
    by_cases hxtX3 : VertexComplete G (x t) (wheelSystemX x (t - 3))
    · obtain ⟨x', hx'⟩ := diamond_reindex_drop hframe hws_t ht4 hY2ne hY2anti hzY2 hxY2
        (fun i hi => hVC2 i (by omega)) hnVC2 hxtXn hxtA2 hxtX3 ⟨a, ha, hadj⟩
      exact key (Y ∪ {x (t + 1)}) hY2ne hY2anti hY2sub (Or.inl Set.subset_union_left)
        (Or.inl ⟨x', hx'⟩)
    · obtain ⟨x', hx'⟩ := polished_reindex_shift hframe hws ht4 hYne hYanti hzY hxY hVC
        hnVC hxt1X1 hnadj1t (fun a' ha' => hxt1noA a' (hA3subA2 ha')) step1 step3
        ⟨a, ha, hadj⟩ hxtX3 hzq hqxt1 hqxt hqX2 hqx1 step2
      exact key Y hYne hYanti hYsub (Or.inl subset_rfl) (Or.inr (Or.inr ⟨x', hx'⟩))
  -- =====================================================================
  -- ###  the endgame
  -- =====================================================================
  -- "In particular, `x_t` is not adjacent to `r`.  Since `z-x_t-q-r-x_{t−1}-z` is not an
  --  odd hole it follows that `x_t` is adjacent to `x_{t−1}`."
  have hxtr : ¬ G.Adj (x t) r₂ := fun h => step4 r₂ hr₂A3 h
  have hxtx1 : G.Adj (x t) (x (t - 1)) := by
    by_contra hnadj
    have hxtner : x t ≠ r₂ := fun h =>
      Thm203Prelim.x_notMem_wheelSystemA hws (show t ≤ t + 1 by omega)
        (show x t ∈ wheelSystemA G z A₀ x (t - 3) by rw [h]; exact hr₂A3)
    have hpath : IsPathFrom G [x t, q, r₂] (x t) r₂ :=
      isPathFrom_triple hqxt.symm hqr₂ hxtr hxtner
    have hznotp : z ∉ [x t, q, r₂] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      push Not
      refine ⟨fun h => (hout t (by omega)).2 h.symm, hqne_z.symm, fun h => ?_⟩
      exact Thm203Prelim.z_notMem_wheelSystemA hws (show t - 3 ≤ t + 1 by omega)
        (h.symm ▸ hr₂A3)
    have hx1notp : x (t - 1) ∉ [x t, q, r₂] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      push Not
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := hinj (t - 1) (by omega) t (by omega) h; omega
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t + 1 by omega)
          (show x (t - 1) ∈ wheelSystemA G z A₀ x (t - 1) by rw [h]; exact hqA1)
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (show t - 1 ≤ t + 1 by omega)
          (show x (t - 1) ∈ wheelSystemA G z A₀ x (t - 3) by rw [h]; exact hr₂A3)
    have hhole5 : IsHoleList G (x (t - 1) :: z :: [x t, q, r₂]) := by
      refine PrismBasics.isHoleList_of_path_add_two_vertices hpath (by norm_num [pathLength])
        (hzadj t (by omega)) hr₂x1.symm (hzadj (t - 1) (by omega))
        hznotp hx1notp ?_ (fun h => hnadj h.symm) ?_ ?_
      · exact fun h => WheelSystemBasics.wheelSystemA_no_nbr hr₂A3 h
      · intro y hy
        have hyq : y = q := by
          rw [show SPGT.interior [x t, q, r₂] = [q] from rfl] at hy
          simpa using hy
        rw [hyq]; exact hzq
      · intro y hy
        have hyq : y = q := by
          rw [show SPGT.interior [x t, q, r₂] = [q] from rfl] at hy
          simpa using hy
        rw [hyq]; exact fun h => hqx1 h.symm
    have hev := hBerge.1 _ hhole5
    rw [PrismBasics.holeLength_cons_cons z (x (t - 1)) (by simp)] at hev
    rw [show pathLength [x t, q, r₂] = 2 from rfl] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  -- "If `x_t` is `X_{t−3}`-complete, then `x₀,…,x_{t−3},x_{t−1},x_{t−2},x_t` is a polished
  --  `Y ∪ {x_{t+1}}`-diamond of height `t`; while if `x_t` is not `X_{t−3}`-complete, then
  --  `x₀,…,x_{t−3},x_{t−1},x_t` is a `Y ∪ {x_{t+1}}`-square of height `t − 1`."
  by_cases hxtX3 : VertexComplete G (x t) (wheelSystemX x (t - 3))
  · obtain ⟨x', hx'⟩ := polished_reindex' hframe hws_t ht4 hY2ne hY2anti hzY2 hxY2 hVC2
      hnVC2 hxtx1 step4 hzq hqxt hqA1 hqX2 hqx1 step2 step1 step3 hxtX3
    exact key (Y ∪ {x (t + 1)}) hY2ne hY2anti hY2sub (Or.inl Set.subset_union_left)
      (Or.inr (Or.inr ⟨x', hx'⟩))
  · obtain ⟨x', hx'⟩ := square_reindex' hframe hws_t ht4 hY2ne hY2anti hzY2 hxY2 hVC2
      hnVC2 hxtx1 step4 hzq hqxt hqX2 hqx1 step2 step1 step3 hxtX3
    exact key (Y ∪ {x (t + 1)}) hY2ne hY2anti hY2sub (Or.inl Set.subset_union_left)
      (Or.inr (Or.inl ⟨x', hx'⟩))


end SPGT

end Workspace.Statements.S20
