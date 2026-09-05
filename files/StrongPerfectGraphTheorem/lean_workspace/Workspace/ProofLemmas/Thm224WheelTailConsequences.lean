import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.KiteTailBasics

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm224WheelTailConsequences

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

private theorem wheelSystemX_succ {V : Type*} (x : ℕ → V) (k : ℕ) :
    wheelSystemX x (k + 1) = wheelSystemX x k ∪ {x (k + 1)} := by
  ext v
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases lt_or_eq_of_le hj with hjlt | rfl
    · exact Or.inl ⟨j, by omega, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨j, hj, rfl⟩ | rfl)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨k + 1, le_rfl, rfl⟩

private theorem anticonnected_wheelSystemX_prefix
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {n k : ℕ}
    (hws : IsWheelSystem G z A₀ x n) (hk : k ≤ n) :
    AnticonnectedSet G (wheelSystemX x k) := by
  revert hk
  induction k with
  | zero =>
      intro _
      rw [WheelSystemBasics.wheelSystemX_zero]
      intro a b
      exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)
  | succ k ih =>
      intro hk
      have hanti : AnticonnectedSet G (wheelSystemX x k) := ih (by omega)
      have hnc : ¬ VertexComplete G (x (k + 1)) (wheelSystemX x k) := by
        simpa using hws.2.2.2.2.2.1 (k + 1) (by omega) hk
      rw [wheelSystemX_succ]
      exact KiteTailBasics.anticonnectedSet_union_singleton hanti hnc

theorem thm224WheelTailConsequences
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u : List V} {Y A₀ : Set V} {z y : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u) :
    let A := wheelSystemA G z A₀ x t
    let X := wheelSystemX x t
    let q := x (t + 1)
    1 ≤ t ∧
    IsFrame G z A₀ ∧
    A₀ ⊆ A ∧
    A.Nonempty ∧
    ConnectedSet G A ∧
    VertexAnticomplete G z A ∧
    (∀ a ∈ A, ¬ VertexComplete G a X) ∧
    (∀ j ≤ t + 1, ∃ a ∈ A, G.Adj (x j) a) ∧
    X.Nonempty ∧
    AnticonnectedSet G X ∧
    (X ∪ {q}).Nonempty ∧
    AnticonnectedSet G (X ∪ {q}) ∧
    q ∉ X ∧
    q ∉ Y ∪ {y} ∧
    ¬ VertexComplete G q X ∧
    VertexComplete G z (X ∪ {q}) ∧
    VertexComplete G z (Y ∪ {y}) ∧
    Complete G X Y ∧
    VertexComplete G y X ∧
    Disjoint A Y ∧
    IsPathList G (z :: y :: u) ∧
    VertexAnticomplete G z {v : V | v ∈ u} ∧
    (∀ v ∈ u, G.Adj y v ↔ u.head? = some v) ∧
    ∃ a ∈ A₀, ∃ b ∈ A₀,
      a ≠ b ∧ a ∈ C ∧ b ∈ C ∧ G.Adj a b ∧
      VertexComplete G a Y ∧ VertexComplete G b Y := by
  classical
  subst hTshape
  rcases u with _ | ⟨u₁, us⟩
  · exact (hu.2.1 rfl).elim
  · have hw : IsWheel G C Y := KiteTailBasics.tail_isWheel hT
    have hC : IsHoleList G C := KiteTailBasics.wheel_isHoleList hw
    have hlen5 : 5 ≤ C.length := by
      have hlen6 := KiteTailBasics.wheel_six_le_length hw
      omega
    have hzC : z ∈ C := KiteTailBasics.tail_mem_rim hT
    have hnb := KiteTailBasics.tail_rimNeighbours hT
    obtain ⟨hc0, hcz, hc1⟩ := KiteTailBasics.tail_complete_triple hT
    obtain ⟨y', R', hTeq0, hRne', -, -, hy1', -, -, -, -, -, -, -⟩ :=
      KiteTailBasics.tail_snd_spec hT
    obtain ⟨hyy, hRR⟩ : y = y' ∧ R = R' := by
      simpa only [List.cons.injEq, true_and] using hTeq0
    have hy1 : G.Adj y (x 1) := by
      rw [hyy]
      exact hy1'
    have hnotcomp : ¬ VertexComplete G (x (t + 1)) (Y ∪ {y}) :=
      hhub.2.2.2.2.2.2
    have ht1 : 1 ≤ t := by
      by_contra hlt
      have ht0 : t = 0 := by omega
      subst ht0
      exact hnotcomp (KiteTailBasics.vertexComplete_union_singleton hc1 hy1.symm)
    have hframe : IsFrame G z A₀ := by
      rw [hA₀]
      exact KiteTailBasics.isFrame_rim_minus hC hzC hnb
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
    have hAne : (wheelSystemA G z A₀ x t).Nonempty := by
      obtain ⟨a, ha⟩ := hframe.1
      exact ⟨a, hA₀sub ha⟩
    have hAconn : ConnectedSet G (wheelSystemA G z A₀ x t) :=
      WheelSystemBasics.connectedSet_wheelSystemA hframe.1
    have hzA : VertexAnticomplete G z (wheelSystemA G z A₀ x t) := by
      intro a ha
      exact WheelSystemBasics.wheelSystemA_no_nbr ha
    have hAnoX : ∀ a ∈ wheelSystemA G z A₀ x t,
        ¬ VertexComplete G a (wheelSystemX x t) := by
      intro a ha
      exact WheelSystemBasics.wheelSystemA_no_complete ha
    have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
    have hxNbr : ∀ j ≤ t + 1, ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj (x j) a := by
      intro j hj
      by_cases hj0 : j = 0
      · subst j
        obtain ⟨a, ha, hadj⟩ := hws.2.2.2.1.1
        exact ⟨a, hA₀sub ha, hadj⟩
      by_cases hj1 : j = 1
      · subst j
        obtain ⟨a, ha, hadj⟩ := hws.2.2.2.1.2.1
        exact ⟨a, hA₀sub ha, hadj⟩
      obtain ⟨B, hA₀B, hBconn, hBadj, hBz, hBX⟩ :=
        hws.2.2.2.2.1 j (by omega) hj
      obtain ⟨a, ha, hadj⟩ :=
        WheelSystemBasics.exists_adj_wheelSystemA_of_witness hA₀B hBconn hBz hBX hBadj
      exact ⟨a, WheelSystemBasics.wheelSystemA_mono (by omega) ha, hadj⟩
    have hXne : (wheelSystemX x t).Nonempty :=
      ⟨x 0, WheelSystemBasics.self_mem_wheelSystemX x (by omega)⟩
    have hXanti : AnticonnectedSet G (wheelSystemX x t) :=
      anticonnected_wheelSystemX_prefix hws (by omega)
    have hXqne : (wheelSystemX x t ∪ {x (t + 1)}).Nonempty :=
      ⟨x (t + 1), Or.inr rfl⟩
    have hXqanti : AnticonnectedSet G (wheelSystemX x t ∪ {x (t + 1)}) := by
      rw [← wheelSystemX_succ x t]
      exact anticonnected_wheelSystemX_prefix hws (le_refl _)
    have hqX : x (t + 1) ∉ wheelSystemX x t := by
      intro hqX
      obtain ⟨j, hj, hqeq⟩ := hqX
      exact (KiteTailBasics.hub_last_ne hhub hj) hqeq
    have hqYy : x (t + 1) ∉ Y ∪ {y} := KiteTailBasics.hub_last_notMem hhub
    have hqXnc : ¬ VertexComplete G (x (t + 1)) (wheelSystemX x t) := by
      simpa using hws.2.2.2.2.2.1 (t + 1) (by omega) (le_refl _)
    have hzXq : VertexComplete G z (wheelSystemX x t ∪ {x (t + 1)}) := by
      intro v hv
      rcases hv with hv | hv
      · obtain ⟨j, hj, rfl⟩ := hv
        exact hws.2.2.2.2.2.2 j (by omega)
      · rw [Set.mem_singleton_iff] at hv
        subst v
        exact hws.2.2.2.2.2.2 (t + 1) (le_refl _)
    have hzYy : VertexComplete G z (Y ∪ {y}) := hhub.2.2.2.2.1
    have hXY : Complete G (wheelSystemX x t) Y := by
      intro v hv w hw
      obtain ⟨j, hj, rfl⟩ := hv
      exact hhub.2.2.2.2.2.1 j (by omega) w (Or.inl hw)
    have hyX : VertexComplete G y (wheelSystemX x t) := by
      intro v hv
      obtain ⟨j, hj, rfl⟩ := hv
      exact (hhub.2.2.2.2.2.1 j (by omega) y (Or.inr rfl)).symm
    have hAY : Disjoint (wheelSystemA G z A₀ x t) Y := by
      rw [Set.disjoint_left]
      intro a haA haY
      exact WheelSystemBasics.wheelSystemA_no_nbr haA (hzYy a (Or.inl haY))
    have hTpath : IsPathList G (z :: y :: R) := KiteTailBasics.tail_isPathList hT
    obtain ⟨S, hpre⟩ := hu.1
    have htake : z :: y :: u₁ :: us = (z :: y :: R).take (z :: y :: u₁ :: us).length := by
      rw [← hpre]
      simp
    have hpath : IsPathList G (z :: y :: u₁ :: us) := by
      rw [htake]
      exact PathBasics.isPathList_take hTpath (by simp)
    have hzu : VertexAnticomplete G z {v : V | v ∈ u₁ :: us} := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · have hnot := PathBasics.path_not_adj_of_gap hpath (i := 0) (j := 2)
          (by simp) (by simp) (by omega) (by omega)
        simpa using hnot
      · obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
        have hnot := PathBasics.path_not_adj_of_gap hpath (i := 0) (j := j + 3)
          (by simp) (by simp; omega) (by omega) (by omega)
        rw [← hjv]
        simpa only [List.getElem_cons_zero, List.getElem_cons_succ] using hnot
    have hanotus : u₁ ∉ us := by
      have hnd1 : (y :: u₁ :: us).Nodup := (List.nodup_cons.mp hpath.2.1).2
      have hnd2 : (u₁ :: us).Nodup := (List.nodup_cons.mp hnd1).2
      exact (List.nodup_cons.mp hnd2).1
    have hyu : ∀ v ∈ u₁ :: us, G.Adj y v ↔ (u₁ :: us).head? = some v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · have hadj := PathBasics.path_adj_succ hpath (i := 1) (by simp)
        simpa using hadj
      · obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
        have hnot := PathBasics.path_not_adj_of_gap hpath (i := 1) (j := j + 3)
          (by simp) (by simp; omega) (by omega) (by omega)
        have hnot' : ¬ G.Adj y v := by
          rw [← hjv]
          simpa only [List.getElem_cons_succ] using hnot
        have hvne : v ≠ u₁ := by
          intro hEq
          exact hanotus (hEq ▸ hv)
        simpa only [List.head?_cons, Option.some.injEq] using
          (iff_of_false hnot' (Ne.symm hvne))
    obtain ⟨a, b, haC, hbC, haout, hbout, hab, haY, hbY⟩ :=
      KiteTailBasics.tail_exists_yEdge hT
    have haA₀ : a ∈ A₀ := by
      rw [hA₀]
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or]
      exact ⟨haC, haout.2.1, haout.1, haout.2.2⟩
    have hbA₀ : b ∈ A₀ := by
      rw [hA₀]
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or]
      exact ⟨hbC, hbout.2.1, hbout.1, hbout.2.2⟩
    exact ⟨ht1, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq, hzYy,
      hXY, hyX, hAY, hpath, hzu, hyu,
      a, haA₀, b, hbA₀, hab.ne, haC, hbC, hab, haY, hbY⟩

end Workspace.ProofLemmas.Thm224WheelTailConsequences
