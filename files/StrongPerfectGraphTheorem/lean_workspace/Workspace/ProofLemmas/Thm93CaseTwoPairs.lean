import Workspace.ProofLemmas.Thm93CaseTwoCommon

/-! Reading the two vertices produced in case (2) of 9.3 as an odd path. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoPairs

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure Workspace.ProofLemmas.Thm93CaseTwoCommon

variable {V : Type*}

/-- The two-vertex form of statement 3. The order of the ends records the paper's
"up to symmetry". -/
def PairData (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ : V) (F : Set V) : Prop :=
  ∃ (a b : V) (P P' : List V),
    ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
      (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
    ∃ f₁ ∈ F, ∃ f₂ ∈ F, G.Adj f₁ f₂ ∧
      (∀ w ∈ ({v | v ∈ P'} ∪ {v | v ∈ Q₁} ∪ {v | v ∈ Q₂} : Set V),
        (G.Adj f₁ w ↔ G.Adj a w)) ∧
      (∀ w ∈ ({v | v ∈ P'} ∪ {v | v ∈ Q₁} ∪ {v | v ∈ Q₂} : Set V),
        (G.Adj f₂ w ↔ G.Adj b w)) ∧
      (∀ w ∈ P, G.Adj f₁ w → w = a) ∧ (∀ w ∈ P, G.Adj f₂ w → w = b)

/-- The two leaps have one end-neighbour each on both antipaths. Their order on the second
antipath determines which of `P₁,P₂` is replaced. -/
def ComplementPairs (G : SimpleGraph V) (Q₁ Q₂ : List V)
    (x₁ y₁ x₂ y₂ : V) (F : Set V) : Prop :=
  ∃ f₁ ∈ F, ∃ f₂ ∈ F, G.Adj f₁ f₂ ∧
    (∀ w ∈ Q₁, Gᶜ.Adj f₁ w ↔ w = x₁) ∧
    (∀ w ∈ Q₁, Gᶜ.Adj f₂ w ↔ w = y₁) ∧
    (((∀ w ∈ Q₂, Gᶜ.Adj f₁ w ↔ w = x₂) ∧
      (∀ w ∈ Q₂, Gᶜ.Adj f₂ w ↔ w = y₂)) ∨
     ((∀ w ∈ Q₂, Gᶜ.Adj f₁ w ↔ w = y₂) ∧
      (∀ w ∈ Q₂, Gᶜ.Adj f₂ w ↔ w = x₂)))

/-- PAPER (9.3, p. 49): "and hence statement 3 ... holds."
The edge between the two vertices is an odd path with empty interior. -/
theorem conclusion_of_pair {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K F : Set V}
    (h : PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  obtain ⟨a, b, P, P', hchoice, f₁, hf₁, f₂, hf₂, hadj, hsame₁, hsame₂, hP₁, hP₂⟩ := h
  refine Or.inr (Or.inr (Or.inl ⟨a, b, P, P', hchoice, [f₁, f₂], f₁, f₂,
    ⟨PathBasics.isPathList_pair hadj, rfl, rfl⟩, ?_, ?_, hsame₁, hsame₂, ?_, ?_⟩))
  · intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    exacts [hf₁, hf₂]
  · exact ⟨0, rfl⟩
  · intro v hv
    simp [SPGT.interior] at hv
  · intro v hv w hw h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact Or.inl ⟨rfl, hP₁ w hw h⟩
    · exact Or.inr ⟨rfl, hP₂ w hw h⟩

/-- A private neighbour in the complement is the unique non-neighbour in the graph. -/
theorem adj_iff_ne {G : SimpleGraph V} {K F : Set V} (hF : F ⊆ Kᶜ)
    {f x : V} (hf : f ∈ F) {Q : List V} (hQ : ∀ w ∈ Q, w ∈ K)
    (h : ∀ w ∈ Q, Gᶜ.Adj f w ↔ w = x) :
    ∀ w ∈ Q, G.Adj f w ↔ w ≠ x := by
  intro w hw
  have hne : f ≠ w := fun he => hF hf (he ▸ hQ w hw)
  have hh := h w hw
  rw [G.compl_adj, and_iff_right hne] at hh
  exact not_iff_not.mp (by simpa only [not_not] using hh)

/-- PAPER (9.3, p. 49): "Therefore, back in `G`, ... statement 3 ... holds."
The choice of order on `Q₂` gives respectively the `P₁` or `P₂` instance. -/
theorem pair_of_complement_pairs {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    {K F : Set V} (hK : KnotInduces P₁ P₂ Q₁ Q₂ K) (hF : F ⊆ Kᶜ)
    (hPcommon : ({v | v ∈ P₁} ∪ {v | v ∈ P₂} : Set V) ⊆ common G K F)
    (hpairs : ComplementPairs G Q₁ Q₂ x₁ y₁ x₂ y₂ F) :
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  obtain ⟨_, _, _, _, _, _, l1, l2, _, _, hanti, _, _, _, _, _, n11, n12, n21, n22⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have ha1 := (PathBasics.isPathFrom_ends_mem hP₁).1
  have hb1 := (PathBasics.isPathFrom_ends_mem hP₁).2
  have ha2 := (PathBasics.isPathFrom_ends_mem hP₂).1
  have hb2 := (PathBasics.isPathFrom_ends_mem hP₂).2
  have hab1 := PathBasics.isPathFrom_ends_ne hP₁ l1
  have hab2 := PathBasics.isPathFrom_ends_ne hP₂ l2
  have hQ1K : ∀ w ∈ Q₁, w ∈ K := by rw [hK]; exact fun _ hw => Or.inl (Or.inr hw)
  have hQ2K : ∀ w ∈ Q₂, w ∈ K := by rw [hK]; exact fun _ hw => Or.inr hw
  have hfP : ∀ f ∈ F, ∀ w ∈ ({v | v ∈ P₁} ∪ {v | v ∈ P₂} : Set V), ¬ G.Adj f w := by
    intro f hf w hw h
    exact ((hPcommon hw).2 f hf).2 h.symm
  have hn11a : ∀ w ∈ Q₁, G.Adj a₁ w ↔ w ≠ y₁ := by
    intro w hw
    have h := n11 w hw a₁ (by simp)
    simp only [true_and, hab1, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hn11b : ∀ w ∈ Q₁, G.Adj b₁ w ↔ w ≠ x₁ := by
    intro w hw
    have h := n11 w hw b₁ (by simp)
    simp only [hab1.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hn12a : ∀ w ∈ Q₂, G.Adj a₁ w ↔ w ≠ y₂ := by
    intro w hw
    have h := n12 w hw a₁ (by simp)
    simp only [true_and, hab1, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hn12b : ∀ w ∈ Q₂, G.Adj b₁ w ↔ w ≠ x₂ := by
    intro w hw
    have h := n12 w hw b₁ (by simp)
    simp only [hab1.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hn21a : ∀ w ∈ Q₁, G.Adj a₂ w ↔ w ≠ y₁ := by
    intro w hw
    have h := n21 w hw a₂ (by simp)
    simp only [true_and, hab2, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hn21b : ∀ w ∈ Q₁, G.Adj b₂ w ↔ w ≠ x₁ := by
    intro w hw
    have h := n21 w hw b₂ (by simp)
    simp only [hab2.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hn22a : ∀ w ∈ Q₂, G.Adj a₂ w ↔ w ≠ x₂ := by
    intro w hw
    have h := n22 w hw a₂ (by simp)
    simp only [true_and, hab2, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hn22b : ∀ w ∈ Q₂, G.Adj b₂ w ↔ w ≠ y₂ := by
    intro w hw
    have h := n22 w hw b₂ (by simp)
    simp only [hab2.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  obtain ⟨f₁, hf₁, f₂, hf₂, hadj, hq11, hq12, hq2⟩ := hpairs
  have hq11' := adj_iff_ne hF hf₁ hQ1K hq11
  have hq12' := adj_iff_ne hF hf₂ hQ1K hq12
  rcases hq2 with ⟨hq21, hq22⟩ | ⟨hq21, hq22⟩
  · have hq21' := adj_iff_ne hF hf₁ hQ2K hq21
    have hq22' := adj_iff_ne hF hf₂ hQ2K hq22
    refine ⟨b₁, a₁, P₁, P₂, Or.inr (Or.inl rfl), f₁, hf₁, f₂, hf₂, hadj, ?_, ?_, ?_, ?_⟩
    · rintro w ((hw | hw) | hw)
      · exact iff_of_false (hfP f₁ hf₁ w (Or.inr hw)) (hanti b₁ hb1 w hw)
      · exact (hq11' w hw).trans (hn11b w hw).symm
      · exact (hq21' w hw).trans (hn12b w hw).symm
    · rintro w ((hw | hw) | hw)
      · exact iff_of_false (hfP f₂ hf₂ w (Or.inr hw)) (hanti a₁ ha1 w hw)
      · exact (hq12' w hw).trans (hn11a w hw).symm
      · exact (hq22' w hw).trans (hn12a w hw).symm
    · exact fun w hw h => (hfP f₁ hf₁ w (Or.inl hw) h).elim
    · exact fun w hw h => (hfP f₂ hf₂ w (Or.inl hw) h).elim
  · have hq21' := adj_iff_ne hF hf₁ hQ2K hq21
    have hq22' := adj_iff_ne hF hf₂ hQ2K hq22
    refine ⟨b₂, a₂, P₂, P₁, Or.inr (Or.inr (Or.inr rfl)),
      f₁, hf₁, f₂, hf₂, hadj, ?_, ?_, ?_, ?_⟩
    · rintro w ((hw | hw) | hw)
      · exact iff_of_false (hfP f₁ hf₁ w (Or.inl hw)) (fun h => hanti w hw b₂ hb2 h.symm)
      · exact (hq11' w hw).trans (hn21b w hw).symm
      · exact (hq21' w hw).trans (hn22b w hw).symm
    · rintro w ((hw | hw) | hw)
      · exact iff_of_false (hfP f₂ hf₂ w (Or.inl hw)) (fun h => hanti w hw a₂ ha2 h.symm)
      · exact (hq12' w hw).trans (hn21a w hw).symm
      · exact (hq22' w hw).trans (hn22a w hw).symm
    · exact fun w hw h => (hfP f₁ hf₁ w (Or.inr hw) h).elim
    · exact fun w hw h => (hfP f₂ hf₂ w (Or.inr hw) h).elim

end Workspace.ProofLemmas.Thm93CaseTwoPairs
