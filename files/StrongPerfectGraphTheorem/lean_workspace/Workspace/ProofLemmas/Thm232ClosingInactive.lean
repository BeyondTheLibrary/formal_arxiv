import Workspace.ProofLemmas.Thm232ClosingRegion
import Workspace.ProofLemmas.Thm232ClosingHat
import Workspace.ProofLemmas.Thm232ClosingLeap
import Workspace.ProofLemmas.Thm232ClosingCompletePair
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S02.Thm_2_10

/-! The other rim neighbour of an inactive end is complete to the hub. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingInactive

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2, printed p. 141): “We claim that `x₀ = c₃`.”  If the other rim
neighbour of the inactive end is not complete, the auxiliary hole has just two
complete vertices. The hat and leap alternatives of 2.10 both give contradictions. -/
theorem next_complete {G : SimpleGraph V} (hG : InF8 G) {C : List V} {Y : Set V}
    (hw : IsWheel G C Y) {z p u y : V} (hzC : z ∈ C)
    (hnb : IsRimNeighbours G C z p u)
    (hpY : VertexComplete G p Y) (hzY : VertexComplete G z Y)
    (huY : VertexComplete G u Y)
    (r : Thm232ClosingRegion.Region G C Y z p u y) : VertexComplete G r.s Y := by
  by_contra hsY
  obtain ⟨S, hS, hSB⟩ := InducedPathExtraction.exists_isPathFrom_of_connected
    r.connected r.ymem r.smem
  have hSpos := PathBasics.path_length_pos hS.1
  have hS2 : 2 ≤ S.length := by
    by_contra hh
    have hfirst := PathBasics.getElem_zero_of_head? hS.2.1 hSpos
    have hlast := PathBasics.getElem_last_of_getLast? hS.2.2 hSpos
    exact r.ys (hfirst.symm.trans ((hS.1.2.1.getElem_inj_iff.mpr (by omega)).trans hlast))
  have hS3 : 3 ≤ S.length := by
    by_contra hh
    exact r.not_adj_ys
      (PathBasics.isPathFrom_ends_adj_of_length_one hS (by change S.length - 1 = 1; omega))
  have hD : IsHoleList G (p :: z :: S) :=
    PrismBasics.isHoleList_of_path_add_two_vertices hS (by change 1 ≤ S.length - 1; omega)
      r.zy r.pnb.2.2.2.2.1 hnb.2.2.2.1
      (fun h => (r.avoid z (hSB z h)).1 rfl)
      (fun h => (r.avoid p (hSB p h)).2.1 rfl)
      (fun h => r.ys (r.zunique r.s r.smem h).symm)
      (fun h => r.ys (r.punique y r.ymem h))
      (by
        intro a ha hza
        exact ((PathBasics.mem_interior_iff_of_pathFrom hS).mp ha).2.1
          (r.zunique a (hSB a (PathBasics.interior_subset ha)) hza))
      (by
        intro a ha hpa
        exact ((PathBasics.mem_interior_iff_of_pathFrom hS).mp ha).2.2
          (r.punique a (hSB a (PathBasics.interior_subset ha)) hpa))
  have hD6 : 6 ≤ (p :: z :: S).length := by
    have he := hG.1.1.1.1.1.1 _ hD
    change Even (S.length + 2) at he
    rw [Nat.even_iff] at he
    simp only [List.length_cons]
    omega
  have hDY : ∀ a ∈ p :: z :: S, a ∉ Y := by
    intro a ha
    rcases List.mem_cons.mp ha with he | ha
    · exact he ▸ hw.2.1.2.2 p hnb.2.1
    rcases List.mem_cons.mp ha with he | ha
    · exact he ▸ hw.2.1.2.2 z hzC
    · exact (r.avoid a (hSB a ha)).2.2.2
  have hpD : p ∈ p :: z :: S := by simp
  have hzD : z ∈ p :: z :: S := by simp
  have hyD : y ∈ p :: z :: S := by simp [PathBasics.head_mem hS.2.1]
  have hsD : r.s ∈ p :: z :: S := by simp [PathBasics.getLast_mem hS.2.2]
  have hDB : ∀ a ∈ p :: z :: S, a ≠ z → a ≠ p → a ∈ r.B := by
    intro a ha haz hap
    exact hSB a (by simpa only [List.mem_cons, hap, haz, false_or] using ha)
  have hseg := Thm232ClosingCompletePair.pair_segment hD hD6 hS hpY hzY r.y_incomplete hsY
  have honly := Thm232ClosingCompletePair.only_pair hG.1.1.1.1.1 hD hD6
    hw.2.1.1 hw.2.1.2.1 hDY (fun h => hG.1.2.1 ⟨_,Y,h⟩) hpD hzD
    ⟨hnb.2.2.2.1.symm, hpY, hzY⟩ hseg
    (by
      intro a ha hpa haY
      by_cases haz : a = z
      · exact haz
      have hap : a ≠ p := hpa.ne'
      exact (hsY (r.punique a (hDB a ha haz hap) hpa ▸ haY)).elim)
    (by
      intro a ha hza haY
      by_cases hap : a = p
      · exact hap
      have haz : a ≠ z := hza.ne'
      exact (r.y_incomplete (r.zunique a (hDB a ha haz hap) hza ▸ haY)).elim)
  rcases Workspace.Statements.S02.SPGT.thm_2_10 G hG.1.1.1.1.1 Y hw.2.1.2.1
      _ hD hDY (by change 4 < (p :: z :: S).length; omega)
      z p hzD hpD hnb.2.2.2.1 hzY hpY (fun a ha hc => (honly a ha hc).symm) with
      ⟨h, hh, hhat⟩ | ⟨a, ha, b, hb, hleap⟩
  · exact Thm232ClosingHat.hat_absurd hG.1 hw.1.1 hw.1.2 hzC hnb.2.1 r.sC
      r.connected (fun a ha => ⟨(r.avoid a ha).1, (r.avoid a ha).2.1, (r.avoid a ha).2.2.2⟩)
      r.ymem r.smem hyD hsD r.zy r.pnb.2.2.2.2.1 r.ys r.zunique r.punique r.hub_attach hh hhat
  · have hsingle : AnticonnectedSet G ({p} : Set V) := by
      intro a b
      exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)
    have hpair : AnticonnectedSet G ({p,u} : Set V) := by
      rw [show ({p,u} : Set V) = {p} ∪ {u} by ext a; simp [or_comm]]
      exact ConnectedSetUnionAttach.connectedSet_union_singleton hsingle
        ⟨p, rfl, by
          rw [SimpleGraph.compl_adj]
          exact ⟨hnb.1.symm, fun h => rimNeighbours_not_adj hw.1.1 hzC hnb h.symm⟩⟩
    have hYX : ∀ a ∈ Y, VertexComplete G a ({p,u} : Set V) := by
      intro a ha t ht
      rcases ht with rfl | rfl
      · exact (hpY a ha).symm
      · exact (huY a ha).symm
    have hYout : ∀ a ∈ Y, a ∉ ({p,u} : Set V) := by
      intro a ha ht
      rcases ht with he | he
      · exact hw.2.1.2.2 p hnb.2.1 (he ▸ ha)
      · exact hw.2.1.2.2 u hnb.2.2.1 (he ▸ ha)
    have hBout : ∀ a ∈ r.B, a ∉ ({p,u} : Set V) := by
      intro a ha ht
      exact ht.elim (r.avoid a ha).2.1 (r.avoid a ha).2.2.1
    rcases hleap with h | h
    · exact Thm232ClosingLeap.leap_absurd hG.1.1.1 hD hD6 hpair hDY hDB
        hYX hYout hBout r.pair_incomplete ha hb h
    · exact Thm232ClosingLeap.leap_absurd hG.1.1.1 hD hD6 hpair hDY
        (fun a ha hap haz => hDB a ha haz hap) hYX hYout hBout r.pair_incomplete ha hb h

end Workspace.ProofLemmas.Thm232ClosingInactive
