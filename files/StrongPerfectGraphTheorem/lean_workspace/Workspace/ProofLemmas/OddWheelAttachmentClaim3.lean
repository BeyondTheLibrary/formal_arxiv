import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentMain
import Workspace.ProofLemmas.OddWheelAttachmentClaim2
import Workspace.ProofLemmas.OddWheelAttachmentYCount

/-!
# 16.2, claim (3)

PAPER (16.2, printed pp. 98–99):

> **(3) If `X₁` has members of opposite wheel-parity then the theorem holds.**

Its printed proof derives a contradiction (it ends *"…a contradiction.  This proves (3)"*), so
the Lean form — `Workspace.ProofLemmas.OddWheelAttachmentMain.Claim3` — is the negation
`¬ HasOpp G C Y X₁`.

The rim toolkit this claim shares with claims (2), (4) and the endgame now lives in
`Workspace.ProofLemmas.OddWheelAttachmentArcs`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.OddWheelAttachmentClaim3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs
open Workspace.ProofLemmas.OddWheelAttachmentMain

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-! ### The first paragraph of claim (3)

PAPER: *"For assume `X₁` has members of opposite wheel-parity.  Then we may assume its only
members are `p₁, p₂`, and they are both `Y`-complete.  From (2) we may assume that all members
of `X₂` have the same wheel-parity as `p₂`.  In particular, `p₁` has no neighbour in
`F \ {f₁}`."*

`Setup3` records exactly that configuration.  `π` is the two-valued wheel-parity function of
`OddWheelParityFacts.exists_parity'`; the printed *"we may assume"* is the choice of which of
the two members of `X₁` is called `p₂` — namely the one whose wheel-parity `X₂` shares. -/
structure Setup3 (G : SimpleGraph V) (C : List V) (Y F : Set V) (P : List V)
    (x₁ x₂ f₁ fk p₁ p₂ : V) (π : V → ℕ) : Prop where
  /-- The ambient configuration of the `|F| ≥ 2` line. -/
  cfg : Config G C Y F P x₁ x₂ f₁ fk
  /-- Wheel-parity is two-valued. -/
  pi2 : ∀ z : V, π z < 2
  /-- `π` *is* wheel-parity. -/
  piSpec : ∀ a b : V, a ∈ C → b ∈ C → a ≠ b → (SameWheelParity G C Y a b ↔ π a = π b)
  /-- *"we may assume its only members are `p₁, p₂`"*. -/
  X₁eq : Att G C (F \ {fk}) = {p₁, p₂}
  /-- `p₁p₂` is an edge of the rim. -/
  adj12 : G.Adj p₁ p₂
  /-- *"and they are both `Y`-complete"*. -/
  yc1 : VertexComplete G p₁ Y
  yc2 : VertexComplete G p₂ Y
  /-- They have opposite wheel-parity — that is the hypothesis of claim (3). -/
  piNe : π p₁ ≠ π p₂
  /-- *"all members of `X₂` have the same wheel-parity as `p₂`"*. -/
  X₂par : ∀ z ∈ Att G C (F \ {f₁}), π z = π p₂
  /-- *"In particular, `p₁` has no neighbour in `F \ {f₁}`"*. -/
  p₁notX₂ : p₁ ∉ Att G C (F \ {f₁})
  /-- Consequently `f₁` is the unique neighbour of `p₁` in `F`. -/
  adjp₁f₁ : G.Adj p₁ f₁
  p₁C : p₁ ∈ C
  p₂C : p₂ ∈ C

/-- **The first paragraph of claim (3).** -/
theorem exists_setup3 [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y F : Set V}
    {P : List V} {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk) (hc2 : Claim2 G)
    (hopp1 : HasOpp G C Y (Att G C (F \ {fk}))) :
    ∃ (p₁ p₂ : V) (π : V → ℕ), Setup3 G C Y F P x₁ x₂ f₁ fk p₁ p₂ π := by
  classical
  have hC : IsHoleList G C := h.wheel.1.1
  have hBerge : Berge G := h.inF6.1.1.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge h.wheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC heven
  -- *"we may assume its only members are `p₁, p₂`"*
  obtain ⟨u, v, hu, hv, huv, hopuv, hall⟩ :=
    OddWheelAttachmentClaim2.two_adjacent hC (fun z hz => hz.1) h.dich₁ hopp1
  have huC : u ∈ C := hu.1
  have hvC : v ∈ C := hv.1
  have hπuv : π u ≠ π v := fun he => hopuv.2.2.2 ((hπ u v huC hvC hopuv.1).mpr he)
  have hX₁eq : Att G C (F \ {fk}) = {u, v} := by
    ext z
    constructor
    · intro hz
      rcases hall z hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact hu
      · exact hv
  -- *"and they are both `Y`-complete"*
  obtain ⟨-, hyu, hyv⟩ :=
    (OddWheelAttachmentYCount.parity_step hC heven hπ huC hvC huv).mp hπuv
  -- *"From (2) we may assume that all members of `X₂` have the same wheel-parity as `p₂`"*
  have hno2 : ¬ HasOpp G C Y (Att G C (F \ {f₁})) :=
    fun hopp2 => hc2 C Y F P x₁ x₂ f₁ fk h ⟨hopp1, hopp2⟩
  have hmono2 : ∀ a ∈ Att G C (F \ {f₁}), ∀ b ∈ Att G C (F \ {f₁}), π a = π b := by
    intro a ha b hb
    by_cases hab : a = b
    · rw [hab]
    · have hnopp : ¬ OppositeWheelParity G C Y a b := fun hcon => hno2 ⟨a, ha, b, hb, hcon⟩
      have hsame : SameWheelParity G C Y a b := by
        by_contra hcon
        exact hnopp ⟨hab, ha.1, hb.1, hcon⟩
      exact (hπ a b ha.1 hb.1 hab).mp hsame
  -- `X₂` is nonempty: otherwise `X = X₁ = {u, v}` is a single edge, and the nonadjacent pair
  -- `x₁, x₂` of `X` would have to be `u, v`.
  obtain ⟨z₀, hz₀⟩ : ∃ z : V, z ∈ Att G C (F \ {f₁}) := by
    by_contra hcon
    push_neg at hcon
    have hx₁ : x₁ ∈ Att G C (F \ {fk}) := by
      rcases (h.union ▸ h.att₁ : x₁ ∈ Att G C (F \ {fk}) ∪ Att G C (F \ {f₁})) with hm | hm
      · exact hm
      · exact absurd hm (hcon x₁)
    have hx₂ : x₂ ∈ Att G C (F \ {fk}) := by
      rcases (h.union ▸ h.att₂ : x₂ ∈ Att G C (F \ {fk}) ∪ Att G C (F \ {f₁})) with hm | hm
      · exact hm
      · exact absurd hm (hcon x₂)
    refine h.nadj ?_
    rcases hall x₁ hx₁ with rfl | rfl <;> rcases hall x₂ hx₂ with rfl | rfl
    · exact absurd rfl h.opp.1
    · exact huv
    · exact huv.symm
    · exact absurd rfl h.opp.1
  -- the labelling: `p₂` is the member of `X₁` whose wheel-parity `X₂` shares
  by_cases hcase : π z₀ = π u
  · refine ⟨v, u, π, ?_⟩
    have hp₁notX₂ : v ∉ Att G C (F \ {f₁}) := by
      intro hmem
      exact hπuv ((hmono2 z₀ hz₀ v hmem).symm.trans hcase).symm
    obtain ⟨g, hg, hgadj⟩ : ∃ g ∈ F \ {fk}, G.Adj v g := hv.2
    have hgf₁ : g = f₁ := by
      by_contra hgne
      exact hp₁notX₂ ⟨hvC, g, ⟨hg.1, hgne⟩, hgadj⟩
    exact
      { cfg := h
        pi2 := hπ2
        piSpec := hπ
        X₁eq := by rw [hX₁eq, Set.pair_comm]
        adj12 := huv.symm
        yc1 := hyv
        yc2 := hyu
        piNe := fun he => hπuv he.symm
        X₂par := fun z hz => (hmono2 z hz z₀ hz₀).trans hcase
        p₁notX₂ := hp₁notX₂
        adjp₁f₁ := by rw [← hgf₁]; exact hgadj
        p₁C := hvC
        p₂C := huC }
  · refine ⟨u, v, π, ?_⟩
    have hzv : π z₀ = π v := by
      have h1 := hπ2 z₀; have h2 := hπ2 u; have h3 := hπ2 v; omega
    have hp₁notX₂ : u ∉ Att G C (F \ {f₁}) := by
      intro hmem
      exact hπuv ((hmono2 u hmem z₀ hz₀).trans hzv)
    obtain ⟨g, hg, hgadj⟩ : ∃ g ∈ F \ {fk}, G.Adj u g := hu.2
    have hgf₁ : g = f₁ := by
      by_contra hgne
      exact hp₁notX₂ ⟨huC, g, ⟨hg.1, hgne⟩, hgadj⟩
    exact
      { cfg := h
        pi2 := hπ2
        piSpec := hπ
        X₁eq := hX₁eq
        adj12 := huv
        yc1 := hyu
        yc2 := hyv
        piNe := hπuv
        X₂par := fun z hz => (hmono2 z hz z₀ hz₀).trans hzv
        p₁notX₂ := hp₁notX₂
        adjp₁f₁ := by rw [← hgf₁]; exact hgadj
        p₁C := huC
        p₂C := hvC }

end Workspace.ProofLemmas.OddWheelAttachmentClaim3
