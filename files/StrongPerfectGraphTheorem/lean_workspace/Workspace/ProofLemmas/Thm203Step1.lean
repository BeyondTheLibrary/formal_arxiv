import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.YDiamondTruncation

/-!
# 20.3, step (1)

PAPER (printed p. 125):

> **(1) Not both `x_t` and `x_{t−1}` have neighbours in `A_{t−3}`.**
>
> *For suppose they do.  If `x_{t−1}` is `X_{t−3}`-complete, then `x₀,…,x_{t−1}`
> is a `Y ∪ {x_t}`-diamond of height `t − 1`, while if `x_{t−1}` is not
> `X_{t−3}`-complete, then `x₀,…,x_{t−3},x_{t−1},x_t` is a `Y`-diamond of height
> `t − 1`, in both cases a contradiction.  This proves (1).*

The contradiction is against 20.3's hypothesis `hnone`, so the mathematical
content of the step is the *positive* statement proved here: if both `x_t` and
`x_{t−1}` have neighbours in `A_{t−3}`, then there is an anticonnected `Y' ⊇ Y`
carrying a `Y'`-diamond of height `t − 1`.  Feeding that to `hnone` is step (1).

The first case is `YDiamondTruncation.ydiamond_truncate_union`.  The second case
is the reindexed sequence `x₀,…,x_{t−3},x_{t−1},x_t`, written here as `x ∘ σ`
with `σ i = i` for `i ≤ t−3`, `σ (t−2) = t−1` and `σ (t−1) = t`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm203Step1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **20.3 step (1)**, in positive form. -/
theorem exists_diamond_of_both_nbrs {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hxt : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x t) a)
    (hxt1 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a) :
    ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y' := by
  by_cases hcomp : VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3))
  · -- first case: `x₀,…,x_{t−1}` is a `Y ∪ {x_t}`-diamond of height `t − 1`
    refine ⟨Y ∪ {x t}, ?_, Set.subset_union_left, x,
      YDiamondTruncation.ydiamond_truncate_union hd ht hcomp hxt1⟩
    exact YDiamondTruncation.anticonnected_union_singleton hd.2.2.1
      (hd.2.2.2.1.2 t le_rfl) hd.2.2.2.2.2.1
  · -- second case: `x₀,…,x_{t−3},x_{t−1},x_t` is a `Y`-diamond of height `t − 1`
    have hnonadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
    obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hA⟩ := hd
    obtain ⟨-, hinj, hout, ⟨hnb0, hnb1, hA₀nc⟩, hcond2, hcond3, hzadj⟩ := id hws
    have he : t - 1 - 2 = t - 3 := by omega
    -- the reindexed sequence
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
    have hsubX : wheelSystemX x (t - 3) ⊆ wheelSystemX x' (t - 2) := by
      intro v hv
      rw [WheelSystemBasics.mem_wheelSystemX] at hv ⊢
      obtain ⟨k, hk, rfl⟩ := hv
      exact ⟨k, by omega, (hlo k hk).symm⟩
    -- `A₀` contains no `X_{t−3}`-complete vertex
    have hA₀nc' : ∀ v ∈ A₀, ¬ VertexComplete G v (wheelSystemX x (t - 3)) := by
      intro v hv hcon
      refine hA₀nc v hv ?_
      rintro w (rfl | rfl)
      · exact hcon _ (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
      · exact hcon _ (WheelSystemBasics.self_mem_wheelSystemX x (by omega))
    have hA₀sub : A₀ ⊆ wheelSystemA G z A₀ x (t - 3) :=
      WheelSystemBasics.A₀_subset_wheelSystemA hframe hA₀nc'
    have hAconn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
      WheelSystemBasics.connectedSet_wheelSystemA hframe.1
    -- ### `x'` is a wheel system of height `t − 1`
    have hws' : IsWheelSystem G z A₀ x' (t - 1) := by
      refine ⟨by omega, hinj', ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · intro j hj; rw [hx' j]; exact hout _ (hbd j hj)
      · rw [hlo 0 (by omega)]; exact hnb0
      · rw [hlo 1 (by omega)]; exact hnb1
      · rw [hlo 0 (by omega), hlo 1 (by omega)]; exact hA₀nc
      · intro i hi2 hit
        rcases Nat.lt_or_ge i (t - 2) with hsmall | hbig
        · obtain ⟨B, hB0, hBc, hBn, hBz, hBnc⟩ := hcond2 i hi2 (by omega)
          refine ⟨B, hB0, hBc, ?_, hBz, ?_⟩
          · rw [hlo i (by omega)]; exact hBn
          · intro v hv; rw [hXeq (i - 1) (by omega)]; exact hBnc v hv
        · refine ⟨wheelSystemA G z A₀ x (t - 3), hA₀sub, hAconn, ?_,
            fun v hv => WheelSystemBasics.wheelSystemA_no_nbr hv, ?_⟩
          · rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
            · rw [← hEq, hmid]; exact hxt1
            · have : i = t - 1 := by omega
              rw [this, hhi]; exact hxt
          · intro v hv hcon
            refine WheelSystemBasics.wheelSystemA_no_complete hv ?_
            rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
            · have hi3 : i - 1 = t - 3 := by omega
              rw [← hXeq (t - 3) le_rfl, ← hi3]; exact hcon
            · have hi2' : i - 1 = t - 2 := by omega
              rw [hi2'] at hcon
              exact fun w hw => hcon w (hsubX hw)
      · intro i hi1 hit
        rcases Nat.lt_or_ge i (t - 2) with hsmall | hbig
        · rw [hlo i (by omega), hXeq (i - 1) (by omega)]
          exact hcond3 i hi1 (by omega)
        · rcases Nat.eq_or_lt_of_le hbig with hEq | hGt
          · have hj3 : t - 2 - 1 = t - 3 := by omega
            rw [← hEq, hmid, hj3, hXeq (t - 3) le_rfl]
            exact hcomp
          · have hii : i = t - 1 := by omega
            have hj2 : t - 1 - 1 = t - 2 := by omega
            rw [hii, hhi, hj2]
            intro hcon
            exact hnonadj (hmid ▸ hcon (x' (t - 2))
              (WheelSystemBasics.self_mem_wheelSystemX x' (le_refl (t - 2))))
      · intro j hj; rw [hx' j]; exact hzadj _ (hbd j hj)
    -- ### `x'` is a `Y`-diamond of height `t − 1`
    refine ⟨Y, hYanti, subset_rfl, x', hws', hYne, hYanti, ⟨hzY, ?_⟩, ?_, ?_,
      by omega, ?_, ?_⟩
    · intro i hi; rw [hx' i]; exact hxY _ (hbd i hi)
    · intro i hi; rw [hx' i]; exact hVC _ (hbd' i hi)
    · rw [hhi]; exact hnVC
    · rw [hhi, he, hXeq (t - 3) le_rfl]
      exact WheelSystemBasics.vertexComplete_wheelSystemX_mono (by omega) hXc
    · rw [hhi, he, hAeq (t - 3) le_rfl]; exact hxt

/-- **The last sentence of the proof of 20.3** (printed p. 127).

> *"If `x_{t−1}` is not `X_{t−3}`-complete, then `x₀,…,x_t` is a polished
> `Y`-diamond of height `t`; while if `x_{t−1}` is `X_{t−3}`-complete, then
> `x₀,…,x_{t−1}` is a `Y ∪ {x_t}`-diamond of height `t − 1`, in both cases a
> contradiction.  This proves 20.3."*

The three data the earlier steps supply are the hypotheses `hno` (`x_t` has no
neighbour in `A_{t−3}`, from (3) and the choice of `R`), `hnbr1` (`x_{t−1}` has
one, which is (3)) and `hq` (the vertex `q ∈ A_{t−2}` of (2), adjacent to both
`x_t, x_{t−1}` and with a neighbour in `A_{t−3}`). -/
theorem exists_diamond_endgame {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} {Y : Set V} (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hno : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x t) a)
    (hnbr1 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)
    (hq : ∃ a ∈ wheelSystemA G z A₀ x (t - 2),
      G.Adj a (x t) ∧ G.Adj a (x (t - 1)) ∧
        ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj a b) :
    ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y')) := by
  by_cases hcomp : VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3))
  · refine ⟨Y ∪ {x t}, ?_, Set.subset_union_left,
      Or.inl ⟨x, YDiamondTruncation.ydiamond_truncate_union hd ht hcomp hnbr1⟩⟩
    exact YDiamondTruncation.anticonnected_union_singleton hd.2.2.1
      (hd.2.2.2.1.2 t le_rfl) hd.2.2.2.2.2.1
  · exact ⟨Y, hd.2.2.1, subset_rfl, Or.inr ⟨x, hd, ht, hcomp, hno, hnbr1, hq⟩⟩

end Workspace.ProofLemmas.Thm203Step1
