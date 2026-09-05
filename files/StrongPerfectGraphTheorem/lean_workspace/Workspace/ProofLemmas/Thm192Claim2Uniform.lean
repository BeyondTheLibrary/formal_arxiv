import Workspace.ProofLemmas.Thm192Setup

/-!
# *"Choose `Y` not satisfying the theorem, with `|Y|` minimum"* — the induction

PAPER (printed p. 118, opening of the proof of 19.2): *"If possible, choose `Y` not
satisfying the theorem, with `|Y|` minimum."*

The counterexample being chosen is a whole tuple: a graph, a frame in it, a wheel
system, and a hub `Y`.  Only `|Y|` is minimised, and nothing ties the graph down, so
the proof may use the theorem in any graph whatsoever as long as the hub is smaller.
Claim (2) does exactly that, in an induced subgraph of the graph at hand (see
`Thm192Claim2Localization.inductive_wheel_with_rim_in_A`).

Since an induced subgraph of an induced subgraph is again one, it is enough to run the
induction over all graphs at once, and to carry, along with the usual induction
hypothesis inside the fixed graph, the hypothesis `Thm192Setup.IHInduced` for its
induced subgraphs.  That is what `uniform_induction` below does; it replaces
`Thm192Setup.aux`, which fixed the graph and therefore could not feed claim (2).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim2Uniform

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

universe u

/-- Strong induction on `|Y|`, uniformly over all graphs on types in one universe.

The `step` is the whole printed argument for one counterexample: it receives the
hypotheses of 19.2 together with both halves of the induction hypothesis — the theorem
for smaller hubs in the same graph, and `IHInduced`, the theorem for smaller hubs in
every induced subgraph. -/
theorem uniform_induction
    (step : ∀ (W : Type u) (instF : Fintype W) (instD : DecidableEq W) (G : SimpleGraph W)
      (z : W) (A₀ : Set W) (x : ℕ → W) (Y : Set W), InF7 G → IsFrame G z A₀ →
      IsWheelSystem G z A₀ x 2 → Hyp192 G z A₀ x Y →
      ((∀ Y' : Set W, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
        IHInduced G Y.ncard) → Concl192 G z A₀ x Y) :
    ∀ (n : ℕ) (W : Type u) (instF : Fintype W) (instD : DecidableEq W) (G : SimpleGraph W)
      (z : W) (A₀ : Set W) (x : ℕ → W) (Y : Set W), InF7 G → IsFrame G z A₀ →
      IsWheelSystem G z A₀ x 2 → Y.ncard ≤ n → Hyp192 G z A₀ x Y →
      Concl192 G z A₀ x Y := by
  intro n
  induction n with
  | zero =>
      intro W iF iD G z A₀ x Y hG hfr hws hcard hHyp
      exfalso
      haveI := iF
      have hpos : 0 < Y.ncard := (Set.ncard_pos (Set.toFinite Y)).mpr (Y_nonempty hHyp)
      omega
  | succ n ihn =>
      intro W iF iD G z A₀ x Y hG hfr hws hcard hHyp
      haveI := iF
      refine step W iF iD G z A₀ x Y hG hfr hws hHyp ⟨?_, ?_⟩
      · intro Y' hlt hHyp'
        exact ihn W iF iD G z A₀ x Y' hG hfr hws (by omega) hHyp'
      · intro S z' A' x' Y' hG' hfr' hws' hlt hHyp'
        exact ihn ↥S (Fintype.ofFinite ↥S) (Classical.decEq ↥S) (G.induce S) z' A' x' Y'
          hG' hfr' hws' (by omega) hHyp'

end Workspace.ProofLemmas.Thm192Claim2Uniform
