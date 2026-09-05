import Workspace.ProofLemmas.Thm192Claim4

/-! The last-neighbour case in claim (5) of 19.2 (printed p. 119). -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim5Last

open Workspace.Types.Core.SPGT Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup
open Workspace.ProofLemmas.Thm192Claim4Rim

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "Suppose first that `i = n`. ... it can be completed via
`x₂-x₁-x₀-pₙ` to an antihole of length ≥ 5 containing `x₀,x₁,pₙ`, a contradiction." -/
theorem last_not_adj {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2) {Y : Set V}
    (hHyp : Hyp192 G z A₀ x Y) {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ interior P, w ∈ wheelSystemA G z A₀ x 1) (hPlen : 3 ≤ P.length)
    (h02 : G.Adj (x 0) (x 2))
    (hpn : ¬ VertexComplete G (P[P.length - 2]'(by omega)) (Y ∪ {x 2})) :
    ¬ G.Adj (x 2) (P[P.length - 2]'(by omega)) := by
  classical
  intro h2p
  have hrim := rim hG.1.1.1.1 hws hP hPint hPlen
  have hlen : 5 ≤ P.length := by
    have := hrim.2
    simpa only [holeLength, List.length_cons, Nat.succ_le_succ_iff] using this
  let p := P[P.length - 2]'(by omega)
  have hpint : p ∈ interior P :=
    PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)
  have hpmem := PathBasics.interior_subset hpint
  have hpends := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hpint
  have hpY : p ∉ Y := hub_outside hHyp (hPint p hpint)
  have h2Y : x 2 ∉ Y := fun h => (hHyp.1 (x 2) h).2.2.2 rfl
  have hpc : ¬ VertexComplete G p Y := by
    intro hc
    apply hpn
    rintro a (ha | rfl)
    · exact hc a ha
    · exact h2p.symm
  have hpnon : ∃ a ∈ Y, ¬ G.Adj p a := by
    simpa only [VertexComplete, not_forall, exists_prop] using hpc
  have h2non : ∃ a ∈ Y, ¬ G.Adj (x 2) a := by
    simpa only [VertexComplete, not_forall, exists_prop] using hHyp.2.2.2.2.1
  obtain ⟨Q, hQ, hQint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hHyp.2.1 hpY h2Y hpnon h2non
  have h01 := x0_not_adj_x1 hws
  have hxne : ∀ i ≤ 2, ∀ j ≤ 2, i ≠ j → x i ≠ x j := by
    intro i hi j hj hne he
    exact hne (hws.2.1 i hi j hj he)
  have h21 : ¬ G.Adj (x 2) (x 1) := by
    intro he
    apply hws.2.2.2.2.2.1 2 (by omega) (by omega)
    rw [show (2 : ℕ) - 1 = 1 from rfl, wheelSystemX_one]
    rintro a (rfl | rfl)
    · exact h02.symm
    · exact he
  have hp1 : G.Adj p (x 1) := by
    rw [← PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
    exact (PathBasics.path_adj_iff hP.1 (by omega) (by omega)).mpr (Or.inl (by omega))
  have hp0 : ¬ G.Adj p (x 0) := by
    rw [← PathBasics.getElem_zero_of_head? hP.2.1 (by omega)]
    exact PathBasics.path_not_adj_of_gap hP.1 (by omega) (by omega) (by omega) (by omega)
  have hpair : IsPathFrom Gᶜ [x 1, x 0] (x 1) (x 0) :=
    ⟨PathBasics.isPathList_pair ⟨hxne 1 (by omega) 0 (by omega) (by omega),
      fun h => h01 h.symm⟩, rfl, rfl⟩
  have hR : IsAntipathFrom G [x 2, x 1, x 0, p] (x 2) p := by
    apply PathAttach.isPathFrom_cons_concat hpair
    · exact ⟨hxne 2 (by omega) 1 (by omega) (by omega), h21⟩
    · exact ⟨hpends.2.1, hp0⟩
    · exact fun h => h.2 h2p
    · exact h2p.ne
    · simp [hxne 2 (by omega) 1 (by omega) (by omega),
        hxne 2 (by omega) 0 (by omega) (by omega)]
    · simp [hpends.2.1, hpends.2.2]
    · intro a ha hne hcon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with he | he
      · exact hne he
      · exact hcon.2 (by rw [he]; exact h02.symm)
    · intro a ha hne hcon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with he | he
      · exact hcon.2 (by rw [he]; exact hp1)
      · exact hne he
  have hRi : interior [x 2, x 1, x 0, p] = [x 1, x 0] := rfl
  have hRc : ∀ a ∈ interior [x 2, x 1, x 0, p], VertexComplete G a Y := by
    rw [hRi]
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with he | he
    · rw [he]; exact hHyp.2.2.2.1
    · rw [he]; exact hHyp.2.2.1
  apply Thm192Infra.antipathExtendToAntihole hG.1 h2p.symm hQ hQint hR (by simp)
    hRc hrim.1 (by have := hrim.2; omega)
    (c₀ := x 0) (c₁ := x 1) (c₂ := p)
    (hxne 0 (by omega) 1 (by omega) (by omega)) hpends.2.1.symm hpends.2.2.symm
    (List.mem_cons_of_mem _ (PathBasics.head_mem hP.2.1))
    (List.mem_cons_of_mem _ (PathBasics.getLast_mem hP.2.2))
    (List.mem_cons_of_mem _ hpmem)
  · rw [hRi]; exact List.mem_append_right _ (by simp)
  · rw [hRi]; exact List.mem_append_right _ (by simp)
  · exact List.mem_append_left _ (PathBasics.head_mem hQ.2.1)

end Workspace.ProofLemmas.Thm192Claim5Last
