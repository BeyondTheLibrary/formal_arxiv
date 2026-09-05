import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.NonlocalStaircaseSelectedStep
import Workspace.ProofLemmas.NonlocalStaircasePrismSetup
import Workspace.ProofLemmas.NonlocalStaircasePrismJumpEndgame
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.Statements.S10.Thm_10_1

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.NonlocalStaircaseAttachmentPrismJumpForcesOutcome

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT

/-- The non-A-complete minimal attachment path forces one of the outcomes of 12.2
after the selected-step prism analysis. -/
theorem nonlocalStaircaseAttachmentPrismJumpForcesOutcome
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (F_orig F : Set V) (f : List V) (f₁ fk : V)
    (hBerge : Berge G)
    (hNoK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hNoEvenPrism :
      ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G alpha beta P₁ P₂ P₃)
    (hMaximalStaircase : MaximalStaircase G A C B a₀ R₀ b₀)
    (hFsub : F ⊆ F_orig)
    (hFoutside : F ⊆ (staircaseVertices A C B R₀)ᶜ)
    (hFconnected : ConnectedSet G F)
    (hFnonlocal : ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G F (staircaseVertices A C B R₀)))
    (hMinimal : ∀ D : Set V, D ⊂ F → ConnectedSet G D →
      LocalForStaircase A C B a₀ R₀ b₀
        (attachments G D (staircaseVertices A C B R₀)))
    (hFvertices : F = {v : V | v ∈ f})
    (hPath : IsPathFrom G f f₁ fk)
    (hLength : 2 ≤ f.length)
    (hf₁LeftAttachment : ∃ u ∈ A ∪ C, G.Adj f₁ u)
    (hf₁Unique : ∀ x ∈ F, (∃ u ∈ A ∪ C, G.Adj x u) → x = f₁)
    (hfkR₀Attachment : ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj fk r)
    (hfkUnique : ∀ x ∈ F, (∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r) → x = fk)
    (hf₁NotComplete : ¬ VertexComplete G f₁ A) :
    (∃ w ∈ F_orig, MajorForStaircase G A C B a₀ R₀ b₀ w) ∨
    (∃ (u v : V) (R : List V),
      (∀ w ∈ R, w ∈ F_orig) ∧
      IsBanister G A C B u R v ∧
      Anticomplete G {w : V | w ∈ R} {w : V | w ∈ R₀}) ∨
    (∃ (u v : V) (R : List V),
      (∀ w ∈ R, w ∈ F_orig) ∧
      IsPathFrom G R u v ∧
      ((IsLeftStar G A C B u ∧
          (∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∧
          Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)) ∨
        (IsRightStar G A C B u ∧
          (∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x) ∧
          Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)))) := by
  classical
  have hK : IsStaircase G A C B a₀ R₀ b₀ := hMaximalStaircase.1
  obtain ⟨a₁, b₁, a₂, b₂, R₁, R₂, hstep, hy, hfa₂⟩ :=
    Workspace.ProofLemmas.NonlocalStaircaseSelectedStep.exists_selected_step
      G A C B f₁ hK.1 hf₁LeftAttachment hf₁NotComplete
  have hf₁F : f₁ ∈ F := by
    rw [hFvertices]
    exact Workspace.ProofLemmas.PathBasics.head_mem hPath.2.1
  have hfkF : fk ∈ F := by
    rw [hFvertices]
    exact Workspace.ProofLemmas.PathBasics.getLast_mem hPath.2.2
  let Kp : Set V :=
    {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}
  have hform : FormPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ :=
    Workspace.ProofLemmas.PrismFromBanisterAndStep.formPrism_of_banister_and_step
      hK.2.1 hstep
  have hprismSetup :=
    Workspace.ProofLemmas.NonlocalStaircasePrismSetup.prism_nonlocal
      G A C B a₀ b₀ R₀ F f₁ fk hK hFoutside
        a₁ b₁ a₂ b₂ R₁ R₂ hstep hy hf₁F hfkR₀Attachment hfkF
  dsimp only at hprismSetup
  have hFKp : F ⊆ Kpᶜ := by
    simpa [Kp] using hprismSetup.1
  have hnonlocalPrism :
      ¬ LocalForPrism ![a₁, a₂, a₀] ![b₁, b₂, b₀]
        R₁ R₂ R₀ (attachments G F Kp) := by
    simpa [Kp] using hprismSetup.2
  by_cases hmajor : ∃ v ∈ F, MajorForPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] v
  · left
    obtain ⟨v, hvF, hvmaj⟩ := hmajor
    exact ⟨v, hFsub hvF,
      Workspace.ProofLemmas.NonlocalStaircasePrismSetup.major_for_prism_is_major_for_staircase
        G hBerge hNoEvenPrism A C B a₀ b₀ R₀ hK
          a₁ b₁ a₂ b₂ R₁ R₂ hstep v (hFoutside hvF) hvmaj⟩
  · have hnomajor : ∀ v ∈ F,
        ¬ MajorForPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] v := by
      push Not at hmajor
      exact hmajor
    have hnoa₂ : ∀ x ∈ F, ¬ G.Adj x a₂ := by
      intro x hxF hxa₂
      have hxf₁ := hf₁Unique x hxF ⟨a₂, Or.inl hstep.2.1.2.1, hxa₂⟩
      subst x
      exact hfa₂ hxa₂
    obtain ⟨q, p₁, p₂, hq, hqF, -, a', b', R', σ, hR', hab, hcase⟩ :=
      Workspace.Statements.S10.SPGT.thm_10_1 G hBerge
        ![a₁, a₂, a₀] ![b₁, b₂, b₀] ![R₁, R₂, R₀]
        Kp F hform (by simp [Kp]) hFKp hFconnected hnonlocalPrism hnomajor
    have hp₁F : p₁ ∈ F := hqF p₁
      (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1)
    have hp₂F : p₂ ∈ F := hqF p₂
      (Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2)
    rcases hcase with hcase1 | hcase2 | hcase3 | hcase4
    · obtain ⟨u, u', hu, hu', huu', hp₁u, hp₁u', w, w', hw, hw', hww',
          hp₂w, hp₂w', honly, happ⟩ := hcase1
      exact (hNoK4 happ).elim
    · rcases hab with hab | hab
      · have hadj := hcase2.2.1 (σ.symm 1)
        rw [hab.1] at hadj
        have : G.Adj p₁ a₂ := by simpa using hadj
        exact (hnoa₂ p₁ hp₁F this).elim
      · have hadj := hcase2.2.2.1 (σ.symm 1)
        rw [hab.2] at hadj
        have : G.Adj p₂ a₂ := by simpa using hadj
        exact (hnoa₂ p₂ hp₂F this).elim
    · exact (Workspace.ProofLemmas.NonlocalStaircasePrismJumpEndgame.third_case_contradicts_maximality
          G A C B a₀ b₀ R₀ hMaximalStaircase
          F hFoutside a₁ b₁ a₂ b₂ R₁ R₂ hstep hnoa₂
          q p₁ p₂ hq hqF a' b' R' σ hR' hab
          (by simpa [Kp] using hcase3)).elim
    · exact (Workspace.ProofLemmas.NonlocalStaircasePrismJumpEndgame.fourth_case_contradiction
          G A C B a₀ b₀ R₀ hMaximalStaircase
          F hFoutside hMinimal f₁ hf₁F a₁ b₁ a₂ b₂ R₁ R₂ hstep hy hnoa₂
          q p₁ p₂ hq hqF a' b' R' σ hR' hab
          (by simpa [Kp] using hcase4)).elim

end Workspace.ProofLemmas.NonlocalStaircaseAttachmentPrismJumpForcesOutcome
