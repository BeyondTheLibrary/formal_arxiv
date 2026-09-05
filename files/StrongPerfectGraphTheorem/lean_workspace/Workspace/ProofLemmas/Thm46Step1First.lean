import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.BalancedRestrictNonComplete
import Workspace.Statements.S04.Thm_4_2
import Workspace.Statements.S04.Thm_4_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm46Step1First

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-  Statement (1) of the proof of **4.6**, first half: the distinguished component `A₁`
    of `A` is balanced with respect to the kernel `W`.  -/
theorem balanced_first {G : SimpleGraph V} (hG : Berge G) {A B W A₁ : Set V}
    (hAB : IsSkewPartition G A B) (hWB : W ⊆ B) (hA₁ : IsComponent G A A₁)
    (hpath : ∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v →
      (∃ x ∈ A₁, G.Adj u x) → (∃ x ∈ A₁, G.Adj v x) →
      ∃ p : List V, IsPathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ A) ∧
        Even (pathLength p))
    (hantipath : ∀ u ∈ A₁, ∀ v ∈ A₁, G.Adj u v →
      (∃ w ∈ W, ¬ G.Adj u w) → (∃ w ∈ W, ¬ G.Adj v w) →
      ∃ p : List V, IsAntipathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ B) ∧
        Even (pathLength p))
    (hcon : ¬ AdmitsBalancedSkewPartition G) :
    SPGT.Balanced G A₁ W := by
  classical
  have hnl : ¬ IsLooseSkewPartition G A B := by
    intro hloose
    exact hcon (Workspace.Statements.S04.SPGT.thm_4_2 G hG ⟨A, B, hloose⟩)
  apply Workspace.ProofLemmas.BalancedRestrictNonComplete.balanced_of_notComplete
  constructor
  · intro u v p hu hv huv hp hint hodd
    have hunbr : ∃ x ∈ A₁, G.Adj u x := by
      by_contra hn
      push_neg at hn
      exact hnl ⟨hAB, Or.inl ⟨u, hWB hu, A₁, hA₁, hn⟩⟩
    have hvnbr : ∃ x ∈ A₁, G.Adj v x := by
      by_contra hn
      push_neg at hn
      exact hnl ⟨hAB, Or.inl ⟨v, hWB hv, A₁, hA₁, hn⟩⟩
    obtain ⟨p', hp', hp'int, hp'even⟩ := hpath u hu v hv huv hunbr hvnbr
    exact hcon (Workspace.Statements.S04.SPGT.thm_4_3 G hG A B hAB
      (Or.inl ⟨u, v, p, p', hWB hu, hWB hv, hp,
        (fun x hx => hA₁.1 (hint x hx).1), hodd, hp', hp'int, hp'even⟩)).2
  · intro u v p hu hv huv hp hint hodd
    have hunon : ∃ w ∈ W, ¬ G.Adj u w := by
      simp only [VertexComplete, not_forall] at hu
      obtain ⟨w, hw, hn⟩ := hu.2
      exact ⟨w, hw, hn⟩
    have hvnon : ∃ w ∈ W, ¬ G.Adj v w := by
      simp only [VertexComplete, not_forall] at hv
      obtain ⟨w, hw, hn⟩ := hv.2
      exact ⟨w, hw, hn⟩
    obtain ⟨p', hp', hp'int, hp'even⟩ :=
      hantipath u hu.1 v hv.1 huv hunon hvnon
    exact hcon (Workspace.Statements.S04.SPGT.thm_4_3 G hG A B hAB
      (Or.inr ⟨u, v, p, p', hA₁.1 hu.1, hA₁.1 hv.1, hp,
        (fun x hx => hWB (hint x hx)), hodd, hp', hp'int, hp'even⟩)).2

end Workspace.ProofLemmas.Thm46Step1First
