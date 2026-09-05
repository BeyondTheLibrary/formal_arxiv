import Workspace.ProofLemmas.Thm232ClosingAttachment
import Workspace.ProofLemmas.Thm232ClosingGeometry
import Workspace.ProofLemmas.Thm232Claim3

/-! The isolated attachment path in the last paragraph of 23.2. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingAttachmentPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2, printed p. 141): “there is a path `R` between `z,c₂` with interior
in `F`, and no vertex of `C` has neighbours in the interior of `R` except `z,c₂`.”
The two cases exchange the ends of the complete triples. -/
theorem attachment_path (G : SimpleGraph V) (hG : InF8 G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : IsRimNeighbours G C z x₀ x₁)
    (hnbc : IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ a b : V, a ∈ C → b ∈ C → EdgeComplete G Y a b →
      ({a,b} : Set V) = {x₀,z} ∨ ({a,b} : Set V) = {z,x₁} ∨
      ({a,b} : Set V) = {c₁,c₂} ∨ ({a,b} : Set V) = {c₂,c₃})
    (T : List V) (w : V) (hT : IsPathFrom G T z w) (hwC : w ∈ C) (hwz : w ≠ z)
    (havoid : ∀ a ∈ T, a ≠ x₀ ∧ a ≠ x₁)
    (hint : ∀ a ∈ SPGT.interior T, a ∉ Y ∧ ¬ VertexComplete G a Y)
    (horient :
      (VertexAnticomplete G x₀ {a : V | a ∈ SPGT.interior T} ∧ x₀ = c₃) ∨
      (VertexAnticomplete G x₁ {a : V | a ∈ SPGT.interior T} ∧ x₁ = c₁)) :
    ∃ Q : List V, IsPathFrom G Q z c₂ ∧
      (∀ a ∈ SPGT.interior Q, a ∈ SPGT.interior T) ∧
      (∀ c ∈ C, ∀ a ∈ SPGT.interior Q, G.Adj c a → c = z ∨ c = c₂) := by
  have hC := hopt.1.1.1
  have hn6 : 6 ≤ C.length := hopt.1.1.2
  have hzC := (hole_triple hC ⟨k, hpre1⟩).2.1
  have hcC := (hole_triple hC ⟨k + d, hpre2⟩).2.1
  have hzc := Thm232ClosingGeometry.middles_ne hC hd2 hdn hpre1 hpre2
  have heven := WheelBasics.even_cycCount_of_wheel hG.1.1.1.1.1 hopt.1
  have hpar : ∀ c ∈ C, c ≠ z → c ≠ c₂ → OppositeWheelParity G C Y c z := by
    intro c hc hcz hcc
    by_cases h0 : c = x₀
    · subst c
      exact ⟨hnb.2.2.2.1.ne', hnb.2.1, hzC,
        OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hC heven hnb.2.1 hzC
          ⟨hnb.2.2.2.1.symm, h0Y, hzY⟩⟩
    by_cases h1 : c = x₁
    · subst c
      exact ⟨hnb.2.2.2.2.1.ne', hnb.2.2.1, hzC,
        OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hC heven hnb.2.2.1 hzC
          ⟨hnb.2.2.2.2.1.symm, h1Y, hzY⟩⟩
    exact Thm232Claim3.layout_opposite G C Y hC heven x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn
      hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hexh c hc hcz h0 h1 hcc
  rcases horient with ⟨hanti, he⟩ | ⟨hanti, he⟩
  · have hnbc' : IsRimNeighbours G C c₂ c₁ x₀ := by rwa [he]
    have hnd := Thm232ClosingTriples.five_distinct hC hn6 hzC hcC hzc hnb hnbc'
    apply Thm232ClosingAttachment.path_from_initial_path hG.1.1 hopt hnd hzC hnb
      ?_ hpar hT hwC hwz havoid hint hanti
    intro a b ha hb hab
    simpa only [← he] using hexh a b ha hb hab
  · have hnb' := isRimNeighbours_symm hnb
    have hnbc' : IsRimNeighbours G C c₂ c₃ x₁ := by
      rw [he]
      exact isRimNeighbours_symm hnbc
    have hnd := Thm232ClosingTriples.five_distinct hC hn6 hzC hcC hzc hnb' hnbc'
    apply Thm232ClosingAttachment.path_from_initial_path hG.1.1 hopt hnd hzC hnb'
      ?_ hpar hT hwC hwz (fun a ha => (havoid a ha).symm) hint hanti
    intro a b ha hb hab
    rcases hexh a b ha hb hab with hh | hh | hh | hh
    · exact Or.inr (Or.inl (hh.trans (Set.pair_comm _ _)))
    · exact Or.inl (hh.trans (Set.pair_comm _ _))
    · right; right; right
      rw [← he] at hh
      exact hh.trans (Set.pair_comm _ _)
    · exact Or.inr (Or.inr (Or.inl (hh.trans (Set.pair_comm _ _))))

end Workspace.ProofLemmas.Thm232ClosingAttachmentPath
