import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaLatticeDiscrete
import Workspace.ProofLemmas.SublemmaEcountDecomp

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Pointwise

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaEcountEqSumTsum (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) (R : ℝ)
    (U : Finset (Fin f → ℂ)) (hU_lat : ∀ u ∈ U, u ∈ lattice sel DD)
    (a : Fin f → ℂ) :
    (Ecount sel DD R U a : ℝ) = ∑ u ∈ U, ∑' l : ↥(lattice sel DD),
      (window R ∩ (window R - {u})).indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) := by
  classical
  have hfin : (Xset sel DD R a).Finite := (SublemmaLatticeDiscrete hcm sel DD hDD R).1 a
  have he_inj : Function.Injective (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) :=
    fun l1 l2 h => Subtype.ext (add_left_cancel h)
  -- General periodization bridge (same as Ncount, for an arbitrary window set `S`).
  have hgen : ∀ S : Set (Fin f → ℂ),
      (({z | z - a ∈ lattice sel DD} ∩ S).ncard : ℝ)
        = ∑' l : ↥(lattice sel DD), S.indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) := by
    intro S
    set T : Set (↥(lattice sel DD)) := {l | a + (l : Fin f → ℂ) ∈ S} with hTdef
    have hT : ∀ l : ↥(lattice sel DD),
        S.indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) = T.indicator (fun _ => (1 : ℝ)) l := by
      intro l; simp only [Set.indicator_apply, hTdef, Set.mem_setOf_eq]
    rw [tsum_congr hT, ← tsum_subtype]
    simp only [tsum_const, nsmul_eq_mul, mul_one, Nat.card_coe_set_eq]
    have himg : (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) '' T
        = {z | z - a ∈ lattice sel DD} ∩ S := by
      ext z
      constructor
      · rintro ⟨l, hl, rfl⟩
        refine ⟨?_, hl⟩
        show (a + (l : Fin f → ℂ)) - a ∈ lattice sel DD
        rw [add_sub_cancel_left]; exact l.2
      · rintro ⟨hz1, hz2⟩
        refine ⟨⟨z - a, hz1⟩, ?_, ?_⟩
        · show a + (z - a) ∈ S
          rw [show a + (z - a) = z from by abel]; exact hz2
        · show a + (z - a) = z
          abel
    have hncard : ({z | z - a ∈ lattice sel DD} ∩ S).ncard = T.ncard := by
      rw [← himg]; exact Set.ncard_image_of_injective T he_inj
    exact_mod_cast hncard
  -- Expand `Ecount` via the finite fiber decomposition, then bridge each fiber.
  rw [SublemmaEcountDecomp sel DD R U a hfin]
  push_cast
  apply Finset.sum_congr rfl
  intro u hu
  -- For this `u ∈ U` (so `u ∈ Λ`), rewrite the fiber set and apply the periodization bridge.
  have hu_lat := hU_lat u hu
  have hsub_iff : ∀ y : Fin f → ℂ, y ∈ window R - {u} ↔ y + u ∈ window R := by
    intro y
    rw [Set.mem_sub]
    constructor
    · rintro ⟨p, hp, q, hq, hpq⟩
      rw [Set.mem_singleton_iff] at hq; subst hq
      rw [← hpq]; simpa using hp
    · intro hy
      exact ⟨y + u, hy, u, Set.mem_singleton u, by abel⟩
  have hset : {x | x ∈ Xset sel DD R a ∧ x + u ∈ Xset sel DD R a}
      = {z | z - a ∈ lattice sel DD} ∩ (window R ∩ (window R - {u})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Xset]
    constructor
    · rintro ⟨⟨hxΛ, hxw⟩, _, hxuw⟩
      exact ⟨hxΛ, hxw, (hsub_iff x).mpr hxuw⟩
    · rintro ⟨hxΛ, hxw, hxsub⟩
      have hxuw : x + u ∈ window R := (hsub_iff x).mp hxsub
      refine ⟨⟨hxΛ, hxw⟩, ?_, hxuw⟩
      rw [show x + u - a = (x - a) + u from by abel]
      exact AddSubgroup.add_mem _ hxΛ hu_lat
  rw [hset, hgen]

end MinkowskiLemmas
