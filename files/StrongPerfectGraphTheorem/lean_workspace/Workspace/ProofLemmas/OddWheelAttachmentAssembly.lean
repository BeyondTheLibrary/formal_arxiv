import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.OddWheelAttachmentMain
import Workspace.ProofLemmas.OddWheelAttachmentSetup

/-!
# 16.2: joining the `|F| ≥ 2` line to the minimality reduction

`OddWheelAttachmentSetup.thm_16_2_of_bigCase` reduces 16.2 to `BigCaseFalse G C Y` — the whole
`|F| ≥ 2` line of the printed proof.  `OddWheelAttachmentMain.contradiction_of_claims` proves
exactly that line, but phrased against `AttachmentHyp` (the minimality form the paragraph after
claim (1) uses) rather than against `GoodF`.

This module is the two-line reconciliation: `AttachmentHyp` is `GoodF` with its conjuncts
permuted, and *"`F` has minimum cardinality among the `GoodF` subsets of `F`"* implies *"no
proper subset of `F` satisfies `AttachmentHyp`"* because a proper subset of a finite set has
strictly smaller cardinality.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAttachmentAssembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `AttachmentHyp` is `GoodF` with its conjuncts permuted. -/
theorem attachmentHyp_iff_goodF {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V} :
    OddWheelAttachmentMain.AttachmentHyp G C Y F ↔ OddWheelAttachmentSetup.GoodF G C Y F := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h3, h1, h2, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h2, h3, h1, h4, h5, h6⟩

/-- **Piece D of 16.2, in the shape `thm_16_2_of_bigCase` consumes it.** -/
theorem bigCaseFalse_of_claims {G : SimpleGraph V} (hG : InF6 G) {C : List V} {Y : Set V}
    (hw : IsWheel G C Y)
    (hc2 : OddWheelAttachmentMain.Claim2 G) (hc3 : OddWheelAttachmentMain.Claim3 G)
    (hc4 : OddWheelAttachmentMain.Claim4 G) (hend : OddWheelAttachmentMain.Endgame G) :
    OddWheelAttachmentSetup.BigCaseFalse G C Y := by
  classical
  rintro F hF hmin hcard ⟨x₁, hx₁, x₂, hx₂, hne, hnadj, hopp⟩
  obtain ⟨hconn, hFC, hFY, hFnc, -, -⟩ := hF
  -- *"We may assume that `F` is minimal"*, in the form the paragraph after claim (1) uses.
  have hmin' : ∀ F' : Set V, F' ⊆ F → F' ≠ F →
      ¬ OddWheelAttachmentMain.AttachmentHyp G C Y F' := by
    intro F' hsub hne' hAH
    have hgood : OddWheelAttachmentSetup.GoodF G C Y F' := attachmentHyp_iff_goodF.mp hAH
    have hlt : F'.ncard < F.ncard :=
      Set.ncard_lt_ncard (HasSubset.Subset.ssubset_of_ne hsub hne') (Set.toFinite _)
    have := hmin F' hsub hgood
    omega
  exact OddWheelAttachmentMain.contradiction_of_claims hG hc2 hc3 hc4 hend hw hFC hFY hconn
    hFnc hcard hmin' hx₁ hx₂ hopp hnadj

/-- **16.2, modulo the four printed claims.**  Claim (1) and the minimality reduction are
already discharged in `OddWheelAttachmentSetup`; what is left is exactly claims (2), (3), (4)
and the endgame. -/
theorem concl_of_claims {G : SimpleGraph V} (hG : InF6 G) {C : List V} {Y : Set V}
    (hw : IsWheel G C Y)
    (hc2 : OddWheelAttachmentMain.Claim2 G) (hc3 : OddWheelAttachmentMain.Claim3 G)
    (hc4 : OddWheelAttachmentMain.Claim4 G) (hend : OddWheelAttachmentMain.Endgame G)
    {F : Set V} (hF : OddWheelAttachmentSetup.GoodF G C Y F) :
    OddWheelAttachmentSetup.Concl G C Y F :=
  OddWheelAttachmentSetup.thm_16_2_of_bigCase hG hw
    (bigCaseFalse_of_claims hG hw hc2 hc3 hc4 hend) hF

end Workspace.ProofLemmas.OddWheelAttachmentAssembly
