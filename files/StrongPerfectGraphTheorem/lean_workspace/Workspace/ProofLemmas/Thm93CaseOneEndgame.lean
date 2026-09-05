import Workspace.ProofLemmas.Thm93CaseOneBranches
import Workspace.ProofLemmas.Thm93OutcomeFourWitness

/-! Read the two kinds of branch from 5.8, then apply their attachment proofs. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm93CaseOneEndgame
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure
open Workspace.ProofLemmas.Thm93CaseOneBranches
open Workspace.ProofLemmas
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Case (1) of 9.3 after applying 5.8, with the remaining structural constructions named. -/
theorem endgame
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hQ₁len : pathLength Q₁ = 1) (hQ₂len : pathLength Q₂ = 1)
    (hoddP₁ : Odd (pathLength P₁)) (hoddP₂ : Odd (pathLength P₂))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi)
    (F : Set V)
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary G H K phi P₁ P₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
      c₁ c₂ c₃ c₄ N)
    (h58 : FiveEightOutcome G H K phi N F) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  have hdict' := hdict
  obtain ⟨hN, hnd, h12, h23, h34, h41, hbv, _⟩ := hdict'
  have hdeg : DegenerateK4Appearance H :=
    ⟨c₁, c₂, c₃, c₄, hnd, h12, h23, h34, h41, by rw [hbv]⟩
  obtain ⟨T, p₁, p₂, hT, hTF, hnonlocal | hbranch⟩ := h58
  · obtain ⟨d₁, d₂, hnb, h₁, h₂, hno⟩ := hnonlocal
    obtain ⟨m, J', henl, happ'⟩ := nonlocal_enlargement_gap G hG H K phi happ hdeg N hN
      T p₁ p₂ hT d₁ d₂ hnb h₁ h₂ hno
    exact (hnoenl ⟨m, J', henl, Or.inl happ'⟩).elim
  · obtain ⟨d₁, d₂, q, R, r₁, r₂, hd₁, hd₂, hq, hqt, hR, hRset, hR₁, hR₂, halt⟩ := hbranch
    rcases classify_branch_gap G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
      hknot hP₁ hP₂ hQ₁ hQ₂ hQ₁len hQ₂len hoddP₁ hoddP₂ K hK H phi happ
      c₁ c₂ c₃ c₄ N hdict d₁ d₂ q R r₁ r₂ hd₁ hd₂ hq hqt hR hRset hR₁ hR₂ with hlong | hshort
    · obtain ⟨a, b, P, P', hsym, hs, hset, he₁, he₂⟩ := hlong
      subst r₁
      subst r₂
      rcases Thm93CaseOneLong.long_branch hs hR hset hT hTF halt with htwo | hthree
      · have hsym₂ :
            (a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
            (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁) := by
          rcases hsym with h | h | h | h <;> cases h <;> simp
        exact Or.inr (Or.inl ⟨a, P, P', hsym₂, T, p₁, p₂, hT, hTF, htwo⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨a, b, P, P', hsym, T, p₁, p₂, hT, hTF, hthree⟩))
    · obtain ⟨x, y, Q', hsym, hs, hset, he₁, he₂⟩ := hshort
      subst r₁
      subst r₂
      by_cases heq : p₁ = p₂
      · subst p₂
        obtain ⟨hneigh, hnonadj⟩ := Thm93CaseOneShort.singleton_endgame hs hset hT halt
        exact Or.inr (Or.inr (Or.inr ⟨x, y, Q', hsym, p₁,
          hTF p₁ (PathBasics.isPathFrom_ends_mem hT).1, hneigh,
          Thm93OutcomeFourWitness.witness_of_nonadj hknot hP₁ hP₂ hQ₁ hQ₂ hsym hnonadj⟩))
      · exact (hnoover (positive_short_branch_overshadowed_gap G hG H K phi happ hdeg N hN
          d₁ d₂ q R x hd₁ hd₂ hq hqt hR hRset hR₁ hR₂ hset T p₁ p₂ hT heq halt)).elim

end Workspace.ProofLemmas.Thm93CaseOneEndgame
