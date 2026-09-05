import Workspace.ProofLemmas.Thm93CaseTwoLeaps
import Workspace.ProofLemmas.Thm93CaseTwoSixOne
import Workspace.Types.Overshadowed

/-! The two branches of the all-major paragraph in 9.3. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoAllMajor

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure Workspace.ProofLemmas.Thm93CaseTwoCommon
open Workspace.ProofLemmas.Thm93CaseTwoSaturated Workspace.ProofLemmas.Thm93CaseTwoPairs
open Workspace.ProofLemmas.Thm93CaseTwoLeaps

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The saturation branch of the all-major paragraph of 9.3. -/
theorem saturated_case
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (hQlong : ¬ (pathLength Q₁ = 1 ∧ pathLength Q₂ = 1))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K))
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary Gᶜ H K phi Q₁ Q₂ x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂
      c₁ c₂ c₃ c₄ N)
    (hsat : SaturatesLineGraph H {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F}) :
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  obtain ⟨hPcommon, hmiss1, hmiss2⟩ := saturated_common_sets G hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len K hK
    F hFsub hFconn hFattach H phi happ c₁ c₂ c₃ c₄ N hdict hsat
  obtain ⟨_, d1q1, d1q2, _, _, dq, _, _, _, _, _, hcomp, _, _, _, _, n11, n12, _, _⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have ha1 := (PathBasics.isPathFrom_ends_mem hP₁).1
  have hb1 := (PathBasics.isPathFrom_ends_mem hP₁).2
  have hab := PathBasics.isPathFrom_ends_adj_of_length_one hP₁ hP₁len
  have hp1 := extend_antipath hQ₁ hab (d1q1 _ ha1) (d1q1 _ hb1) n11
  have hp2 := extend_antipath hQ₂ hab (d1q2 _ ha1) (d1q2 _ hb1) n12
  have haX := hPcommon (Or.inl ha1)
  have hbX := hPcommon (Or.inl hb1)
  have hQ1K : ∀ w ∈ Q₁, w ∈ K := by rw [hK]; exact fun _ hw => Or.inl (Or.inr hw)
  have hQ2K : ∀ w ∈ Q₂, w ∈ K := by rw [hK]; exact fun _ hw => Or.inr hw
  obtain ⟨⟨_, _, ho1, ho2⟩, _⟩ := Workspace.Statements.S09.SPGT.thm_9_1 G hG _ _ _ _ hknot
  have hleap : (∃ f ∈ F, ∃ g ∈ F, IsLeapForPath Gᶜ (b₁ :: (Q₁ ++ [a₁])) f g) ∨
      (∃ f ∈ F, ∃ g ∈ F, IsLeapForPath Gᶜ (b₁ :: (Q₂ ++ [a₁])) f g) := by
    by_cases hl1 : 3 ≤ pathLength Q₁
    · exact Or.inl (leap_on_long_antipath hG hFsub hFconn hp1 ho1 hl1 hQ1K haX hbX hmiss1)
    · have hl2 : 3 ≤ pathLength Q₂ := by
        obtain ⟨i, hi⟩ := ho1
        obtain ⟨j, hj⟩ := ho2
        omega
      exact Or.inr (leap_on_long_antipath hG hFsub hFconn hp2 ho2 hl2 hQ2K haX hbX hmiss2)
  have hpairs := pairs_from_long_leap hG hFsub hQ₁ hQ₂ ho1 ho2 hp1 hp2
    hQ1K hQ2K haX hbX dq hcomp hleap
  exact pair_of_complement_pairs hknot hP₁ hP₂ hQ₁ hQ₂ hK hFsub hPcommon hpairs

/-- **The nonsaturating use of 6.1 and its four-cycle dictionary.**

PAPER (proof of 9.3, printed p. 49): "If `X` does not saturate `L(H)` in `G̅`, then by (2)
we may apply 6.1. Since `Q₁` has length > 1 it follows that the last outcome of 6.1 holds,
and hence statement 3 of the theorem holds."

The conclusion records the edge between the two vertices in the last outcome of 6.1,
their neighbours on the other three paths, and their possible edges to the replaced path.
`conclusion_of_pair` supplies the odd path.  The saturating branch, including both leaps,
is proved in `saturated_case`.
-/
theorem nonsaturating_pair_gap
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (hQlong : ¬ (pathLength Q₁ = 1 ∧ pathLength Q₂ = 1))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi)
    (hnoovercompl : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' psi)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K))
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary Gᶜ H K phi Q₁ Q₂ x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂
      c₁ c₂ c₃ c₄ N)
    (hallmajor : ∀ f ∈ F, MajorForLineGraph Gᶜ H K phi f) :
    (¬ SaturatesLineGraph H {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F}) →
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  intro hnotsat
  exact Workspace.ProofLemmas.Thm93CaseTwoSixOne.nonsaturating_pair G hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len hQlong K hK
    hnoover hnoovercompl F hFsub hFconn H phi happ c₁ c₂ c₃ c₄ N hdict hallmajor hnotsat

/-- The final paragraph of 9.3, split according to saturation of the common neighbours. -/
theorem all_major
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (hQlong : ¬ (pathLength Q₁ = 1 ∧ pathLength Q₂ = 1))
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi)
    (hnoovercompl : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' psi)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K))
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary Gᶜ H K phi Q₁ Q₂ x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂
      c₁ c₂ c₃ c₄ N)
    (hallmajor : ∀ f ∈ F, MajorForLineGraph Gᶜ H K phi f) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  by_cases hsat : SaturatesLineGraph H {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      VertexComplete Gᶜ (↑(phi ⟨e, he⟩) : V) F}
  · apply conclusion_of_pair
    exact saturated_case G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
      hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len hQlong K hK F hFsub hFconn hFattach
      H phi happ c₁ c₂ c₃ c₄ N hdict hsat
  · apply conclusion_of_pair
    exact nonsaturating_pair_gap G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂
      hP₁len hP₂len hQlong K hK hnoenl hnoover hnoovercompl F hFsub hFconn hFattach
      H phi happ c₁ c₂ c₃ c₄ N hdict hallmajor hsat
end Workspace.ProofLemmas.Thm93CaseTwoAllMajor
