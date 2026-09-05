import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Classes
import Workspace.Statements.S18.Thm_18_5
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm186Setup

/-!
# 18.6, opening sentence — *"From 18.5 `|F| ≥ 2`."*

PAPER (`paper/proofs/18_6.md`, published page 114): *"Proof.  Suppose the theorem is false, and
choose a minimal counterexample `F`.  From 18.5 `|F| ≥ 2`."*

18.5 is the one-vertex case of 18.6: for a single vertex `v ∈ V(G) \ (X ∪ Y ∪ V(P))` that is
not `Y`-complete, the required subpath exists — and *"the attachments of `{v}` in `P`"* is
exactly *"the neighbours of `v` in `P`"*, so 18.5's conclusion **is** `Good … {v}`.  Hence a
counterexample cannot be a singleton; and it cannot be empty either, since the empty set has no
attachments and no `X`-complete vertex, so `P' = p₁` serves.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm186FSizeTwo

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm186Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"From 18.5 `|F| ≥ 2`."* -/
theorem two_le_ncard_of_counterexample (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hF : Adm G X Y P F) (hne : ¬ Good G X Y P p₁ pₙ F) :
    2 ≤ F.ncard := by
  classical
  by_contra hlt
  have hp₁P : p₁ ∈ P := PathBasics.head_mem hhead
  obtain ⟨s, t, hst⟩ := List.append_of_mem hp₁P
  have hinfix : [p₁] <:+: P := ⟨s, t, by rw [hst]; simp⟩
  have hint : ∀ w ∈ SPGT.interior [p₁], ¬ VertexComplete G w Y := by
    intro w hw
    simp [SPGT.interior] at hw
  refine hne ?_
  rcases (by omega : F.ncard = 0 ∨ F.ncard = 1) with h0 | h1
  · -- the empty set has no attachment and no `X`-complete vertex, so `P' = p₁` serves
    have hFe : F = ∅ := (Set.ncard_eq_zero (Set.toFinite F)).mp h0
    subst hFe
    refine ⟨[p₁], PathBasics.isPathList_singleton G p₁, hinfix, ?_, hint, ?_⟩
    · intro w hw
      obtain ⟨-, f, hf, -⟩ := hw
      exact absurd hf (Set.notMem_empty f)
    · rintro ⟨f, hf, -⟩
      exact absurd hf (Set.notMem_empty f)
  · -- a singleton is exactly the case 18.5 settles
    obtain ⟨v, rfl⟩ := Set.ncard_eq_one.mp h1
    have hv : v ∈ ({v} : Set V) := rfl
    obtain ⟨hvXY, hvP⟩ := hF.1 v hv
    have hvY := hF.2.2 v hv
    obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ :=
      _root_.Workspace.Statements.S18.SPGT.thm_18_5 G hG X Y P p₁ pₙ hopt hhead hlast v
        hvXY hvP hvY
    refine ⟨q, hq1, hq2, ?_, hq4, ?_⟩
    · intro w hw
      obtain ⟨hwP, f, hf, hadj⟩ := hw
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact hq3 w hwP hadj.symm
    · rintro ⟨f, hf, hfX⟩
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact hq5 hfX

end Workspace.ProofLemmas.Thm186FSizeTwo
