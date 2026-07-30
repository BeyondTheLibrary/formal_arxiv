import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaEcountDecomp (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (U : Finset (Fin f → ℂ)) (a : Fin f → ℂ) (hfin : (Xset sel DD R a).Finite) :
    Ecount sel DD R U a =
      ∑ u ∈ U, {x | x ∈ Xset sel DD R a ∧ x + u ∈ Xset sel DD R a}.ncard := by
  classical
  set X := Xset sel DD R a with hXdef
  set XF := hfin.toFinset with hXFdef
  have hmem : ∀ x, x ∈ XF ↔ x ∈ X := fun x => Set.Finite.mem_toFinset hfin
  -- The `Ecount` index set as a `Finset`.
  set IF : Finset ((Fin f → ℂ) × (Fin f → ℂ)) :=
    (XF ×ˢ XF).filter (fun p => p.2 - p.1 ∈ U) with hIFdef
  have hIFmem : ∀ p, p ∈ IF ↔ (p.1 ∈ X ∧ p.2 ∈ X ∧ p.2 - p.1 ∈ U) := by
    intro p
    rw [hIFdef, Finset.mem_filter, Finset.mem_product, hmem, hmem]
    tauto
  -- `Ecount = IF.card`.
  have hEcard : Ecount sel DD R U a = IF.card := by
    have hE : Ecount sel DD R U a =
        {p : (Fin f → ℂ) × (Fin f → ℂ) | p.1 ∈ X ∧ p.2 ∈ X ∧ p.2 - p.1 ∈ U}.ncard := rfl
    rw [hE, ← Set.ncard_coe_finset IF]
    congr 1
    ext p
    rw [Set.mem_setOf_eq, Finset.mem_coe, hIFmem]
  rw [hEcard]
  -- Fiber the pairs over their difference `u = p.2 - p.1`.
  have hmaps : Set.MapsTo (fun p : (Fin f → ℂ) × (Fin f → ℂ) => p.2 - p.1) ↑IF ↑U := by
    intro p hp
    rw [Finset.mem_coe] at hp
    rw [Finset.mem_coe]
    exact ((hIFmem p).1 hp).2.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro u hu
  -- The `u`-fiber count equals the shift-count `#{x ∈ X | x + u ∈ X}`.
  set AF : Finset (Fin f → ℂ) := XF.filter (fun x => x + u ∈ X) with hAFdef
  have hAFmem : ∀ x, x ∈ AF ↔ (x ∈ X ∧ x + u ∈ X) := by
    intro x; rw [hAFdef, Finset.mem_filter, hmem]
  have hAcard : {x | x ∈ X ∧ x + u ∈ X}.ncard = AF.card := by
    rw [← Set.ncard_coe_finset AF]
    congr 1
    ext x
    rw [Set.mem_setOf_eq, Finset.mem_coe, hAFmem]
  rw [hAcard]
  -- Bijection `p ↦ p.1` between the `u`-fiber and `AF`, inverse `x ↦ (x, x + u)`.
  apply Finset.card_nbij' (fun p => p.1) (fun x => (x, x + u))
  · -- maps the fiber into `AF`
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨hpIF, hpu⟩ := hp
    rw [Finset.mem_coe, hAFmem]
    have hx : p.1 ∈ X := ((hIFmem p).1 hpIF).1
    have hp2 : p.2 ∈ X := ((hIFmem p).1 hpIF).2.1
    have hsum : p.1 + u = p.2 := by rw [← hpu]; ring
    exact ⟨hx, by rw [hsum]; exact hp2⟩
  · -- maps `AF` into the fiber
    intro x hx
    rw [Finset.mem_coe, hAFmem] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(hIFmem (x, x + u)).2 ⟨hx.1, ?_, ?_⟩, ?_⟩
    · exact hx.2
    · simpa using hu
    · simp
  · -- left inverse on the fiber
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨_, hpu⟩ := hp
    have hsum : p.1 + u = p.2 := by rw [← hpu]; ring
    apply Prod.ext
    · rfl
    · simpa using hsum
  · -- right inverse on `AF`
    intro x _
    rfl

end MinkowskiLemmas
