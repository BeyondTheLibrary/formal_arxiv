import Workspace.ProofLemmas.Thm93CaseTwoPairs

/-!
# Reading the last outcome of 6.1 as statement 3 of 9.3

PAPER (proof of 9.3, printed p. 49): *"If `X` does not saturate `L(H)` in `G̅`, then by (2)
we may apply 6.1.  Since `Q₁` has length `> 1` it follows that the last outcome of 6.1 holds,
and hence statement 3 of the theorem holds."*

The last outcome of 6.1 supplies two nonadjacent vertices of `G̅` — that is, two adjacent
vertices of `G` — whose neighbours in `K` are prescribed.  This module turns that
neighbour pattern into the two-vertex form `PairData` of statement 3.  There are two
patterns, according to which of the two paths of the knot is the one that gets replaced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoSixOnePairs

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93CaseTwoPairs

variable {V : Type*}

/-- The neighbour pattern that replaces `P₁`: `f₁` behaves like `b₁` and `f₂` like `a₁`. -/
theorem pair_first (G : SimpleGraph V) {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {F : Set V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    {f₁ f₂ : V} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) (hadj : G.Adj f₁ f₂)
    (h₁P₂ : ∀ w ∈ P₂, ¬ G.Adj f₁ w) (h₂P₂ : ∀ w ∈ P₂, ¬ G.Adj f₂ w)
    (h₁P₁ : ∀ w ∈ P₁, G.Adj f₁ w → w = b₁) (h₂P₁ : ∀ w ∈ P₁, G.Adj f₂ w → w = a₁)
    (h₁Q₁ : ∀ w ∈ Q₁, G.Adj f₁ w ↔ w ≠ x₁) (h₂Q₁ : ∀ w ∈ Q₁, G.Adj f₂ w ↔ w ≠ y₁)
    (h₁Q₂ : ∀ w ∈ Q₂, G.Adj f₁ w ↔ w ≠ x₂) (h₂Q₂ : ∀ w ∈ Q₂, G.Adj f₂ w ↔ w ≠ y₂) :
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hanti, -, -, -, -, -, n11, n12, -, -⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have ha1 := (PathBasics.isPathFrom_ends_mem hP₁).1
  have hb1 := (PathBasics.isPathFrom_ends_mem hP₁).2
  have hab1 : a₁ ≠ b₁ := PathBasics.isPathFrom_ends_ne hP₁
    (by
      obtain ⟨-, -, -, -, -, -, h, -⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
      exact h)
  have hbQ₁ : ∀ w ∈ Q₁, G.Adj b₁ w ↔ w ≠ x₁ := by
    intro w hw
    have h := n11 w hw b₁ (by simp)
    simp only [hab1.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have haQ₁ : ∀ w ∈ Q₁, G.Adj a₁ w ↔ w ≠ y₁ := by
    intro w hw
    have h := n11 w hw a₁ (by simp)
    simp only [true_and, hab1, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hbQ₂ : ∀ w ∈ Q₂, G.Adj b₁ w ↔ w ≠ x₂ := by
    intro w hw
    have h := n12 w hw b₁ (by simp)
    simp only [hab1.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have haQ₂ : ∀ w ∈ Q₂, G.Adj a₁ w ↔ w ≠ y₂ := by
    intro w hw
    have h := n12 w hw a₁ (by simp)
    simp only [true_and, hab1, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  refine ⟨b₁, a₁, P₁, P₂, Or.inr (Or.inl rfl), f₁, hf₁, f₂, hf₂, hadj, ?_, ?_, ?_, ?_⟩
  · rintro w ((hw | hw) | hw)
    · exact iff_of_false (h₁P₂ w hw) (hanti b₁ hb1 w hw)
    · exact (h₁Q₁ w hw).trans (hbQ₁ w hw).symm
    · exact (h₁Q₂ w hw).trans (hbQ₂ w hw).symm
  · rintro w ((hw | hw) | hw)
    · exact iff_of_false (h₂P₂ w hw) (hanti a₁ ha1 w hw)
    · exact (h₂Q₁ w hw).trans (haQ₁ w hw).symm
    · exact (h₂Q₂ w hw).trans (haQ₂ w hw).symm
  · exact h₁P₁
  · exact h₂P₁

/-- The neighbour pattern that replaces `P₂`: `f₁` behaves like `b₂` and `f₂` like `a₂`. -/
theorem pair_second (G : SimpleGraph V) {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {F : Set V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    {f₁ f₂ : V} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) (hadj : G.Adj f₁ f₂)
    (h₁P₁ : ∀ w ∈ P₁, ¬ G.Adj f₁ w) (h₂P₁ : ∀ w ∈ P₁, ¬ G.Adj f₂ w)
    (h₁P₂ : ∀ w ∈ P₂, G.Adj f₁ w → w = b₂) (h₂P₂ : ∀ w ∈ P₂, G.Adj f₂ w → w = a₂)
    (h₁Q₁ : ∀ w ∈ Q₁, G.Adj f₁ w ↔ w ≠ x₁) (h₂Q₁ : ∀ w ∈ Q₁, G.Adj f₂ w ↔ w ≠ y₁)
    (h₁Q₂ : ∀ w ∈ Q₂, G.Adj f₁ w ↔ w ≠ y₂) (h₂Q₂ : ∀ w ∈ Q₂, G.Adj f₂ w ↔ w ≠ x₂) :
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hanti, -, -, -, -, -, -, -, n21, n22⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have ha2 := (PathBasics.isPathFrom_ends_mem hP₂).1
  have hb2 := (PathBasics.isPathFrom_ends_mem hP₂).2
  have hab2 : a₂ ≠ b₂ := PathBasics.isPathFrom_ends_ne hP₂
    (by
      obtain ⟨-, -, -, -, -, -, -, h, -⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
      exact h)
  have hbQ₁ : ∀ w ∈ Q₁, G.Adj b₂ w ↔ w ≠ x₁ := by
    intro w hw
    have h := n21 w hw b₂ (by simp)
    simp only [hab2.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have haQ₁ : ∀ w ∈ Q₁, G.Adj a₂ w ↔ w ≠ y₁ := by
    intro w hw
    have h := n21 w hw a₂ (by simp)
    simp only [true_and, hab2, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have hbQ₂ : ∀ w ∈ Q₂, G.Adj b₂ w ↔ w ≠ y₂ := by
    intro w hw
    have h := n22 w hw b₂ (by simp)
    simp only [hab2.symm, false_and, false_or, true_and] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  have haQ₂ : ∀ w ∈ Q₂, G.Adj a₂ w ↔ w ≠ x₂ := by
    intro w hw
    have h := n22 w hw a₂ (by simp)
    simp only [true_and, hab2, false_and, or_false] at h
    rw [G.adj_comm]
    exact not_iff_not.mp (by simpa only [not_not] using h)
  refine ⟨b₂, a₂, P₂, P₁, Or.inr (Or.inr (Or.inr rfl)),
    f₁, hf₁, f₂, hf₂, hadj, ?_, ?_, ?_, ?_⟩
  · rintro w ((hw | hw) | hw)
    · exact iff_of_false (h₁P₁ w hw) (fun h => hanti w hw b₂ hb2 h.symm)
    · exact (h₁Q₁ w hw).trans (hbQ₁ w hw).symm
    · exact (h₁Q₂ w hw).trans (hbQ₂ w hw).symm
  · rintro w ((hw | hw) | hw)
    · exact iff_of_false (h₂P₁ w hw) (fun h => hanti w hw a₂ ha2 h.symm)
    · exact (h₂Q₁ w hw).trans (haQ₁ w hw).symm
    · exact (h₂Q₂ w hw).trans (haQ₂ w hw).symm
  · exact h₁P₂
  · exact h₂P₂

/-- The two halves of an "exact neighbour set" statement, in the form the knot needs.
A vertex outside `K` is nonadjacent in `G` to everything it is adjacent to in `G̅`. -/
theorem adj_iff_of_sets {G : SimpleGraph V} {K : Set V} {f : V} (hfK : f ∉ K) {S T : Set V}
    (hsup : ∀ w ∈ S, Gᶜ.Adj f w) (hsub : ∀ w ∈ K, Gᶜ.Adj f w → w ∈ T) :
    (∀ w ∈ S, ¬ G.Adj f w) ∧ (∀ w ∈ K, w ∉ T → G.Adj f w) := by
  refine ⟨fun w hw => ?_, fun w hw hwT => ?_⟩
  · exact ((G.compl_adj f w).mp (hsup w hw)).2
  · by_contra hadj
    exact hwT (hsub w hw ((G.compl_adj f w).mpr ⟨fun h => hfK (h ▸ hw), hadj⟩))

/-- The membership facts about the eight labels that both patterns use. -/
structure Labels (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V) (K : Set V) : Prop where
  P₁_eq : P₁ = [a₁, b₁]
  P₂_eq : P₂ = [a₂, b₂]
  x₁_mem : x₁ ∈ Q₁
  y₁_mem : y₁ ∈ Q₁
  x₂_mem : x₂ ∈ Q₂
  y₂_mem : y₂ ∈ Q₂
  Q₁_sub : ∀ w ∈ Q₁, w ∈ K
  Q₂_sub : ∀ w ∈ Q₂, w ∈ K
  Q₁_ne : ∀ w ∈ Q₁, w ≠ a₁ ∧ w ≠ b₁ ∧ w ≠ a₂ ∧ w ≠ b₂ ∧ w ≠ x₂ ∧ w ≠ y₂
  Q₂_ne : ∀ w ∈ Q₂, w ≠ a₁ ∧ w ≠ b₁ ∧ w ≠ a₂ ∧ w ≠ b₂ ∧ w ≠ x₁ ∧ w ≠ y₁
  x₁_ne_y₁ : x₁ ≠ y₁
  x₂_ne_y₂ : x₂ ≠ y₂
  a₁_ne_b₁ : a₁ ≠ b₁
  a₂_ne_b₂ : a₂ ≠ b₂
  P_disj : ∀ w ∈ P₁, w ∉ P₂

/-- Reading the labels of a knot whose two paths have length `1`. -/
theorem labels_of_knot {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K : Set V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (hK : KnotInduces P₁ P₂ Q₁ Q₂ K) :
    Labels P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K := by
  obtain ⟨d12, d1q1, d1q2, d2q1, d2q2, dq, -⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  have hP1 : P₁ = [a₁, b₁] := KnotLabels.eq_pair_of_length_one hP₁ hP₁len
  have hP2 : P₂ = [a₂, b₂] := KnotLabels.eq_pair_of_length_one hP₂ hP₂len
  have ha1 : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).1
  have hb1 : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).2
  have ha2 : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).1
  have hb2 : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).2
  have hx1 : x₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ₁).1
  have hy1 : y₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ₁).2
  have hx2 : x₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ₂).1
  have hy2 : y₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ₂).2
  have hq1len : 1 ≤ pathLength Q₁ := by
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
    exact h
  have hq2len : 1 ≤ pathLength Q₂ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
    exact h
  have hp1len : 1 ≤ pathLength P₁ := by omega
  have hp2len : 1 ≤ pathLength P₂ := by omega
  refine ⟨hP1, hP2, hx1, hy1, hx2, hy2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, d12⟩
  · rw [hK]; exact fun w hw => Or.inl (Or.inr hw)
  · rw [hK]; exact fun w hw => Or.inr hw
  · exact fun w hw => ⟨fun h => d1q1 a₁ ha1 (h ▸ hw), fun h => d1q1 b₁ hb1 (h ▸ hw),
      fun h => d2q1 a₂ ha2 (h ▸ hw), fun h => d2q1 b₂ hb2 (h ▸ hw),
      fun h => dq w hw (h ▸ hx2), fun h => dq w hw (h ▸ hy2)⟩
  · exact fun w hw => ⟨fun h => d1q2 a₁ ha1 (h ▸ hw), fun h => d1q2 b₁ hb1 (h ▸ hw),
      fun h => d2q2 a₂ ha2 (h ▸ hw), fun h => d2q2 b₂ hb2 (h ▸ hw),
      fun h => dq x₁ hx1 (h ▸ hw), fun h => dq y₁ hy1 (h ▸ hw)⟩
  · exact PathBasics.isPathFrom_ends_ne hQ₁ hq1len
  · exact PathBasics.isPathFrom_ends_ne hQ₂ hq2len
  · exact PathBasics.isPathFrom_ends_ne hP₁ hp1len
  · exact PathBasics.isPathFrom_ends_ne hP₂ hp2len

/-- **The last outcome of 6.1, first pattern.**  `f₁` sees in `G̅` all of `a₁,a₂,b₂,x₁,x₂` and
in `K` nothing else but possibly `b₁`, and `f₂` sees `b₁,a₂,b₂,y₁,y₂` and nothing else but
possibly `a₁`.  Then `f₁` plays the role of `b₁` and `f₂` that of `a₁`. -/
theorem pair_first_of_sets (G : SimpleGraph V) {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K F : Set V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hL : Labels P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K)
    {f₁ f₂ : V} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) (h₁K : f₁ ∉ K) (h₂K : f₂ ∉ K)
    (hnadj : ¬ Gᶜ.Adj f₁ f₂)
    (hsup₁ : ∀ w ∈ ({a₁, a₂, b₂, x₁, x₂} : Set V), Gᶜ.Adj f₁ w)
    (hsub₁ : ∀ w ∈ K, Gᶜ.Adj f₁ w → w ∈ ({a₁, a₂, b₂, x₁, x₂, b₁} : Set V))
    (hsup₂ : ∀ w ∈ ({b₁, a₂, b₂, y₁, y₂} : Set V), Gᶜ.Adj f₂ w)
    (hsub₂ : ∀ w ∈ K, Gᶜ.Adj f₂ w → w ∈ ({b₁, a₂, b₂, y₁, y₂, a₁} : Set V)) :
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  obtain ⟨hno₁, hyes₁⟩ := adj_iff_of_sets h₁K hsup₁ hsub₁
  obtain ⟨hno₂, hyes₂⟩ := adj_iff_of_sets h₂K hsup₂ hsub₂
  have hne : f₁ ≠ f₂ := by
    rintro rfl
    have h := hsub₂ x₁ (hL.Q₁_sub x₁ hL.x₁_mem) (hsup₁ x₁ (by simp))
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₁_ne x₁ hL.x₁_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h | h
    exacts [h2 h, h3 h, h4 h, hL.x₁_ne_y₁ h, h6 h, h1 h]
  have hadj : G.Adj f₁ f₂ := by
    by_contra h
    exact hnadj ((G.compl_adj f₁ f₂).mpr ⟨hne, h⟩)
  refine pair_first G hknot hP₁ hP₂ hQ₁ hQ₂ hf₁ hf₂ hadj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hL.P₂_eq]; intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hno₁ w (by simp), hno₁ w (by simp)]
  · rw [hL.P₂_eq]; intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hno₂ w (by simp), hno₂ w (by simp)]
  · rw [hL.P₁_eq]; intro w hw hadjw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact absurd hadjw (hno₁ w (by simp))
    · rfl
  · rw [hL.P₁_eq]; intro w hw hadjw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rfl
    · exact absurd hadjw (hno₂ w (by simp))
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₁_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₁ w (by simp) hadjw
    · intro hwx
      refine hyes₁ w (hL.Q₁_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h1, h3, h4, hwx, h5, h2⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₁_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₂ w (by simp) hadjw
    · intro hwy
      refine hyes₂ w (hL.Q₁_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h2, h3, h4, hwy, h6, h1⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₂_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₁ w (by simp) hadjw
    · intro hwx
      refine hyes₁ w (hL.Q₂_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h1, h3, h4, h5, hwx, h2⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₂_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₂ w (by simp) hadjw
    · intro hwy
      refine hyes₂ w (hL.Q₂_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h2, h3, h4, h6, hwy, h1⟩

/-- **The last outcome of 6.1, second pattern.**  Here `f₁` plays the role of `b₂` and `f₂`
that of `a₂`. -/
theorem pair_second_of_sets (G : SimpleGraph V) {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K F : Set V}
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hL : Labels P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K)
    {f₁ f₂ : V} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F) (h₁K : f₁ ∉ K) (h₂K : f₂ ∉ K)
    (hnadj : ¬ Gᶜ.Adj f₁ f₂)
    (hsup₁ : ∀ w ∈ ({a₁, b₁, a₂, x₁, y₂} : Set V), Gᶜ.Adj f₁ w)
    (hsub₁ : ∀ w ∈ K, Gᶜ.Adj f₁ w → w ∈ ({a₁, b₁, a₂, x₁, y₂, b₂} : Set V))
    (hsup₂ : ∀ w ∈ ({a₁, b₁, b₂, y₁, x₂} : Set V), Gᶜ.Adj f₂ w)
    (hsub₂ : ∀ w ∈ K, Gᶜ.Adj f₂ w → w ∈ ({a₁, b₁, b₂, y₁, x₂, a₂} : Set V)) :
    PairData G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ F := by
  obtain ⟨hno₁, hyes₁⟩ := adj_iff_of_sets h₁K hsup₁ hsub₁
  obtain ⟨hno₂, hyes₂⟩ := adj_iff_of_sets h₂K hsup₂ hsub₂
  have hne : f₁ ≠ f₂ := by
    rintro rfl
    have h := hsub₂ x₁ (hL.Q₁_sub x₁ hL.x₁_mem) (hsup₁ x₁ (by simp))
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₁_ne x₁ hL.x₁_mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h | h
    exacts [h1 h, h2 h, h4 h, hL.x₁_ne_y₁ h, h5 h, h3 h]
  have hadj : G.Adj f₁ f₂ := by
    by_contra h
    exact hnadj ((G.compl_adj f₁ f₂).mpr ⟨hne, h⟩)
  refine pair_second G hknot hP₁ hP₂ hQ₁ hQ₂ hf₁ hf₂ hadj ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hL.P₁_eq]; intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hno₁ w (by simp), hno₁ w (by simp)]
  · rw [hL.P₁_eq]; intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hno₂ w (by simp), hno₂ w (by simp)]
  · rw [hL.P₂_eq]; intro w hw hadjw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact absurd hadjw (hno₁ w (by simp))
    · rfl
  · rw [hL.P₂_eq]; intro w hw hadjw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · rfl
    · exact absurd hadjw (hno₂ w (by simp))
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₁_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₁ w (by simp) hadjw
    · intro hwx
      refine hyes₁ w (hL.Q₁_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h1, h2, h3, hwx, h6, h4⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₁_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₂ w (by simp) hadjw
    · intro hwy
      refine hyes₂ w (hL.Q₁_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h1, h2, h4, hwy, h5, h3⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₂_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₁ w (by simp) hadjw
    · intro hwy
      refine hyes₁ w (hL.Q₂_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h1, h2, h3, h5, hwy, h4⟩
  · intro w hw
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hL.Q₂_ne w hw
    constructor
    · rintro hadjw rfl; exact hno₂ w (by simp) hadjw
    · intro hwx
      refine hyes₂ w (hL.Q₂_sub w hw) ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨h1, h2, h4, h6, hwx, h3⟩

/-- The twenty-eight disequalities among the eight labels of a knot. -/
theorem all_ne {P₁ P₂ Q₁ Q₂ : List V} {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K : Set V}
    (hL : Labels P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K) :
    (a₁ ≠ b₁ ∧ a₁ ≠ a₂ ∧ a₁ ≠ b₂ ∧ a₁ ≠ x₁ ∧ a₁ ≠ y₁ ∧ a₁ ≠ x₂ ∧ a₁ ≠ y₂) ∧
    (b₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ b₁ ≠ x₁ ∧ b₁ ≠ y₁ ∧ b₁ ≠ x₂ ∧ b₁ ≠ y₂) ∧
    (a₂ ≠ b₂ ∧ a₂ ≠ x₁ ∧ a₂ ≠ y₁ ∧ a₂ ≠ x₂ ∧ a₂ ≠ y₂) ∧
    (b₂ ≠ x₁ ∧ b₂ ≠ y₁ ∧ b₂ ≠ x₂ ∧ b₂ ≠ y₂) ∧
    (x₁ ≠ y₁ ∧ x₁ ≠ x₂ ∧ x₁ ≠ y₂ ∧ y₁ ≠ x₂ ∧ y₁ ≠ y₂ ∧ x₂ ≠ y₂) := by
  have hP1a : a₁ ∈ P₁ := by rw [hL.P₁_eq]; simp
  have hP1b : b₁ ∈ P₁ := by rw [hL.P₁_eq]; simp
  have hP2a : a₂ ∈ P₂ := by rw [hL.P₂_eq]; simp
  have hP2b : b₂ ∈ P₂ := by rw [hL.P₂_eq]; simp
  have c1 : a₁ ≠ a₂ := fun h => hL.P_disj a₁ hP1a (h ▸ hP2a)
  have c2 : a₁ ≠ b₂ := fun h => hL.P_disj a₁ hP1a (h ▸ hP2b)
  have c3 : b₁ ≠ a₂ := fun h => hL.P_disj b₁ hP1b (h ▸ hP2a)
  have c4 : b₁ ≠ b₂ := fun h => hL.P_disj b₁ hP1b (h ▸ hP2b)
  obtain ⟨qa1, qa2, qa3, qa4, qa5, qa6⟩ := hL.Q₁_ne x₁ hL.x₁_mem
  obtain ⟨qb1, qb2, qb3, qb4, qb5, qb6⟩ := hL.Q₁_ne y₁ hL.y₁_mem
  obtain ⟨qc1, qc2, qc3, qc4, qc5, qc6⟩ := hL.Q₂_ne x₂ hL.x₂_mem
  obtain ⟨qd1, qd2, qd3, qd4, qd5, qd6⟩ := hL.Q₂_ne y₂ hL.y₂_mem
  exact ⟨⟨hL.a₁_ne_b₁, c1, c2, qa1.symm, qb1.symm, qc1.symm, qd1.symm⟩,
    ⟨c3, c4, qa2.symm, qb2.symm, qc2.symm, qd2.symm⟩,
    ⟨hL.a₂_ne_b₂, qa3.symm, qb3.symm, qc3.symm, qd3.symm⟩,
    ⟨qa4.symm, qb4.symm, qc4.symm, qd4.symm⟩,
    ⟨hL.x₁_ne_y₁, qa5, qa6, qb5, qb6, hL.x₂_ne_y₂⟩⟩

end Workspace.ProofLemmas.Thm93CaseTwoSixOnePairs
