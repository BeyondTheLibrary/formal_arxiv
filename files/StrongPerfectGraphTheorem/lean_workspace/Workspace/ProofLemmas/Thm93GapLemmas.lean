import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.ProofLemmas.Thm93Infrastructure
import Workspace.ProofLemmas.Thm93KnotCanonical
import Workspace.ProofLemmas.Thm93CaseOneEndgame
import Workspace.ProofLemmas.Thm93CaseTwoAllMajor
import Workspace.ProofLemmas.Thm93CaseTwoNonmajor

/-!
# Explicit remaining gaps in the proof of 9.3

Each theorem in this file is one printed sentence or one printed paragraph.  They are kept
separate from the assembly so the unfinished mathematical steps are visible in the audit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93GapLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Gap: the degenerate appearance carried by a knot with two short antipaths.**

PAPER (proof of 9.3, printed p. 48): *"For assume `Q₁,Q₂` have length 1. Then `K` is a
degenerate appearance of `K₄` in `G`, say `K=L(H)`."*

The result also names the four branch vertices and the two long branches.  This is the
dictionary used by the very next sentences about the sets `N(b₁)` and `N(b₂)`. -/
theorem appearance_data_of_knot_gap
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hlen₁ : pathLength Q₁ = 1) (hlen₂ : pathLength Q₂ = 1) :
    KnotAppearanceData G P₁ P₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K := by
  exact Thm93KnotCanonical.appearance_data G hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ K hK hlen₁ hlen₂

/-- **Gap: the case-(1) analysis of outcome 5.8.**

PAPER (proof of 9.3, printed pp. 48--49): *"If 5.8.1 holds then there is an appearance in
`G` of some `K₄`-enlargement, a contradiction. So 5.8.2 holds. ... In the first case ...
statement 4 holds or there is an overshadowed appearance. In the second case ... statements
2,3 hold, respectively, and the last case is impossible since `P₁` is odd."* -/
theorem case_one_five_eight_endgame_gap
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
  exact Thm93CaseOneEndgame.endgame G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
    hknot hP₁ hP₂ hQ₁ hQ₂ hQ₁len hQ₂len hoddP₁ hoddP₂ K hK hnoenl hnoover F
    H phi happ c₁ c₂ c₃ c₄ N hdict h58

/-- **Gap: the last sentence of claim (2), after applying 5.8 in the complement.**

PAPER (proof of 9.3, printed p. 49): *"We can apply 5.8 (or, indeed, 5.7) in `G̅`, and
deduce, as before, that either there is a `K₄`-enlargement that appears in `G̅` (a
contradiction), or ... statement 2 holds, or ... either statement 1 or statement 4 holds."* -/
theorem case_two_nonmajor_five_eight_endgame_gap
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi)
    (hnoovercompl : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' psi)
    (F : Set V) (f : V) (hfF : f ∈ F) (hfK : f ∉ K)
    (hnotres : ¬ ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K))
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary Gᶜ H K phi Q₁ Q₂ x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂
      c₁ c₂ c₃ c₄ N)
    (h58 : FiveEightOutcome Gᶜ H K phi N ({f} : Set V)) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  exact Thm93CaseTwoNonmajor.endgame G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
    hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len K hK hnoenl hnoover hnoovercompl F f hfF hfK
    H phi happ c₁ c₂ c₃ c₄ N hdict h58

/-- **Gap: the all-major final paragraph of 9.3.**

PAPER (proof of 9.3, printed p. 49): *"We may therefore assume that every `f ∈ F` is major
with respect to `L(H)` in `G̅`. ... If `X` does not saturate `L(H)` in `G̅`, ... apply 6.1
... statement 3 holds. ... We may therefore assume that `X` saturates ... By 2.1, `F`
contains a leap ... Therefore, back in `G`, ... statement 3 of the theorem holds."* -/
theorem case_two_all_major_gap
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
  exact Workspace.ProofLemmas.Thm93CaseTwoAllMajor.all_major G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂
    hP₁len hP₂len hQlong K hK hnoenl hnoover hnoovercompl F hFsub hFconn hFattach
    H phi happ c₁ c₂ c₃ c₄ N hdict hallmajor

end Workspace.ProofLemmas.Thm93GapLemmas
