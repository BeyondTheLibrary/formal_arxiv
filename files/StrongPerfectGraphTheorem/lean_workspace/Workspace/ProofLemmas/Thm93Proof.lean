import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.KnotCompl
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm93Assembly
import Workspace.ProofLemmas.Thm93Case1FiveEight
import Workspace.ProofLemmas.Thm93GapLemmas
import Workspace.ProofLemmas.Thm93Infrastructure
import Workspace.Statements.S05.Thm_5_8
import Workspace.Statements.S09.Thm_9_1
import Workspace.Statements.S09.Thm_9_2

/-!
# Proof assembly for 9.3

This file implements all reductions surrounding the four explicit gaps in
`Thm93GapLemmas`.  In particular, both appearances are constructed through the same knot
dictionary, both calls to 5.8 are made here, and the second call uses the one-vertex set from
claim (2) of the printed proof.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93Proof

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Case (1) of the printed proof, reduced to the two matching gap lemmas. -/
theorem case_one_lane
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hQ₁len : pathLength Q₁ = 1) (hQ₂len : pathLength Q₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (phi : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' phi)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K))
    (hnomajor : ∀ f ∈ F, ¬ ((({x₁, x₂, a₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({x₁, y₂, a₂} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, y₂, b₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, x₂, b₂} : Set V) \ G.neighborSet f).Subsingleton)) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  obtain ⟨⟨hoddP₁, hoddP₂, -, -⟩, -⟩ :=
    _root_.Workspace.Statements.S09.SPGT.thm_9_1 G hG P₁ P₂ Q₁ Q₂ hknot
  obtain ⟨n, H, phi, happ, hdeg, c₁, c₂, c₃, c₄, N, hdict⟩ :=
    Thm93GapLemmas.appearance_data_of_knot_gap G hG P₁ P₂ Q₁ Q₂
      a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ K hK hQ₁len hQ₂len
  have hdict' := hdict
  rcases hdict' with
    ⟨hN, hnd, hc₁c₂, hc₂c₃, hc₃c₄, hc₄c₁, hbv,
      hex₁, hey₂, hey₁, hex₂, hNc₁, hNc₂, hNc₃, hNc₄, hbranch₁, hbranch₂⟩
  have h58 : FiveEightOutcome G H K phi N F :=
    Thm93Case1FiveEight.five_eight_in_case_one G hG P₁ P₂ Q₁ Q₂
      a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hQ₁len hQ₂len K hK n H phi happ N hN
      c₁ c₂ c₃ c₄ hbv hNc₁ hNc₂ hNc₃ hNc₄ F hFsub hFconn hFattach hnomajor
  exact Thm93GapLemmas.case_one_five_eight_endgame_gap G hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hQ₁len hQ₂len
    hoddP₁ hoddP₂ K hK hnoenl hnoover F H phi happ c₁ c₂ c₃ c₄ N hdict h58

/-- The attachments of the singleton `{f}` in the complement are the vertices of `K` missed
by the `G`-neighbour set of `f`. -/
theorem attachments_compl_singleton (G : SimpleGraph V) (K : Set V) (f : V) (hfK : f ∉ K) :
    attachments Gᶜ ({f} : Set V) K = K \ (G.neighborSet f ∩ K) := by
  ext v
  constructor
  · rintro ⟨hvK, w, hw, hadj⟩
    have hwf : w = f := by simpa using hw
    subst w
    refine ⟨hvK, ?_⟩
    rintro ⟨hvN, -⟩
    exact hadj.2 hvN.symm
  · rintro ⟨hvK, hvnot⟩
    refine ⟨hvK, f, by simp, ?_⟩
    have hvf : v ≠ f := by
      intro hvf
      exact hfK (hvf ▸ hvK)
    refine (SimpleGraph.compl_adj G v f).mpr ⟨hvf, ?_⟩
    intro hadj
    exact hvnot ⟨hadj.symm, hvK⟩

/-- A singleton is connected in every graph. -/
theorem connectedSet_singleton (G : SimpleGraph V) (f : V) :
    ConnectedSet G ({f} : Set V) := by
  intro a b
  exact Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a

/-- Claim (2) and the final all-major paragraph in the complement lane. -/
theorem case_two_lane
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
    (hnoover : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (phi : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' phi)
    (hnoovercompl : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (phi : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' phi)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K)) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  have hGc : Berge Gᶜ := Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG
  have hknotc : IsKnot Gᶜ Q₁ Q₂ P₁.reverse P₂.reverse :=
    Workspace.ProofLemmas.KnotCompl.isKnot_compl hknot
  have hP₁c : IsPathFrom Gᶜ Q₁ x₁ y₁ := hQ₁
  have hP₂c : IsPathFrom Gᶜ Q₂ x₂ y₂ := hQ₂
  have hQ₁c : IsAntipathFrom Gᶜ P₁.reverse b₁ a₁ := by
    show IsPathFrom (Gᶜ)ᶜ P₁.reverse b₁ a₁
    rw [compl_compl]
    exact Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hP₁
  have hQ₂c : IsAntipathFrom Gᶜ P₂.reverse b₂ a₂ := by
    show IsPathFrom (Gᶜ)ᶜ P₂.reverse b₂ a₂
    rw [compl_compl]
    exact Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hP₂
  have hQ₁clen : pathLength P₁.reverse = 1 := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_reverse]
    exact hP₁len
  have hQ₂clen : pathLength P₂.reverse = 1 := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_reverse]
    exact hP₂len
  have hKc : KnotInduces Q₁ Q₂ P₁.reverse P₂.reverse K :=
    Workspace.ProofLemmas.KnotCompl.knotInduces_compl hK
  obtain ⟨n, H, phi, happ, hdeg, c₁, c₂, c₃, c₄, N, hdict⟩ :=
    Thm93GapLemmas.appearance_data_of_knot_gap Gᶜ hGc Q₁ Q₂ P₁.reverse P₂.reverse
      x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂ hknotc hP₁c hP₂c hQ₁c hQ₂c K hKc hQ₁clen hQ₂clen
  have hdict' := hdict
  rcases hdict' with
    ⟨hN, hnd, hc₁c₂, hc₂c₃, hc₃c₄, hc₄c₁, hbv,
      heb₁, hea₂, hea₁, heb₂, hNc₁, hNc₂, hNc₃, hNc₄, hbranch₁, hbranch₂⟩
  by_cases hnonmajor : ∃ f ∈ F, ¬ MajorForLineGraph Gᶜ H K phi f
  · obtain ⟨f, hfF, hfnotmajor⟩ := hnonmajor
    by_cases hres : ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K)
    · exact Or.inl ⟨f, hfF, hres⟩
    · have hfK : f ∉ K := hFsub hfF
      have hatteq : attachments Gᶜ ({f} : Set V) K = K \ (G.neighborSet f ∩ K) :=
        attachments_compl_singleton G K f hfK
      have hnotlocalKnot :
          ¬ LocalForKnot Gᶜ Q₁ Q₂ P₁.reverse P₂.reverse (attachments Gᶜ ({f} : Set V) K) := by
        intro hlocal
        apply hres
        apply (Workspace.ProofLemmas.KnotCompl.resolvesKnot_iff_localForKnot_compl hknot hK).mpr
        rwa [hatteq] at hlocal
      have hnotlocalLine : ¬ LocalForLineGraph H
          {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
            (↑(phi ⟨e, he⟩) : V) ∈ attachments Gᶜ ({f} : Set V) K} := by
        intro hlocal
        apply hnotlocalKnot
        exact ((_root_.Workspace.Statements.S09.SPGT.thm_9_2 Gᶜ Q₁ Q₂ P₁.reverse P₂.reverse
          hknotc K hKc hQ₁clen hQ₂clen n H phi happ (attachments Gᶜ ({f} : Set V) K)
          (Thm93Case1FiveEight.attachments_subset Gᶜ ({f} : Set V) K)).1).mpr hlocal
      have h58 : FiveEightOutcome Gᶜ H K phi N ({f} : Set V) := by
        refine _root_.Workspace.Statements.S05.SPGT.thm_5_8 Gᶜ hGc 4
          (⊤ : SimpleGraph (Fin 4)) SubdivisionCounting.k4_three_connected n H K happ.1 phi N hN
          ({f} : Set V) ?_ (connectedSet_singleton Gᶜ f) hnotlocalLine ?_
        · intro z hz
          have hzf : z = f := by simpa using hz
          subst z
          exact hfK
        · intro z hz hmajor
          have hzf : z = f := by simpa using hz
          subst z
          exact hfnotmajor hmajor
      exact Thm93GapLemmas.case_two_nonmajor_five_eight_endgame_gap G hG P₁ P₂ Q₁ Q₂
        a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len K hK hnoenl hnoover
        hnoovercompl F f hfF hfK hres H phi happ c₁ c₂ c₃ c₄ N hdict h58
  · have hallmajor : ∀ f ∈ F, MajorForLineGraph Gᶜ H K phi f := by
      intro f hfF
      by_contra hnot
      exact hnonmajor ⟨f, hfF, hnot⟩
    exact Thm93GapLemmas.case_two_all_major_gap G hG P₁ P₂ Q₁ Q₂
      a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len hQlong
      K hK hnoenl hnoover hnoovercompl F hFsub hFconn hFattach H phi happ c₁ c₂ c₃ c₄ N hdict hallmajor

/-- The frozen statement 9.3, after unfolding its named conclusion. -/
theorem thm_9_3_core
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (phi : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' phi)
    (hnoovercompl : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (phi : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' phi)
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K)) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  refine Thm93Assembly.thm_9_3_of_cases G hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ K hK F hFsub ?_ ?_
  · intro hQ₁len hQ₂len hnomajor
    exact case_one_lane G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
      hknot hP₁ hP₂ hQ₁ hQ₂ hQ₁len hQ₂len K hK hnoenl hnoover F hFsub hFconn hFattach hnomajor
  · intro hP₁len hP₂len hQlong
    exact case_two_lane G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
      hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len hQlong K hK hnoenl hnoover hnoovercompl
      F hFsub hFconn hFattach

end Workspace.ProofLemmas.Thm93Proof
