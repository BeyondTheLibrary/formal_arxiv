import Workspace.ProofLemmas.KnotLabels
import Workspace.ProofLemmas.PathBasics
import Workspace.Types.Knots

/-!
# The corrected form of 9.3.4, for the non-major lane of case (2) of 9.3

PAPER (proof of 9.3, printed p. 49): *"... or (up to symmetry) `f, x₁` have the same neighbours
in `V(P₁) ∪ V(P₂) ∪ V(Q₂)` (but then either statement 1 or statement 4 of the theorem
holds)."*

The dichotomy the proof of 9.3 really establishes at this point is the one proved below:
either the neighbour set of `f` in `K` resolves the knot (statement 1), or `f` has a
**non-neighbour in `V(Q₁) \ {x₁}`**.  When `Q₁` has length `1` — which is case (1) of 9.3 —
that non-neighbour can only be `y₁`, and the second outcome is exactly statement 4 of 9.3.
In case (2), where `Q₁` may be long, the two are no longer the same, and 9.3.4 as printed is
strictly stronger than what the argument gives.  See the section
"9.3, case 2: 9.3.4 is too strong" of `REPORT.md` for an explicit counterexample.

Nothing in this module is used by the rest of the development; it records the statement that
the case-(2) argument does prove, so that the gap left in
`Thm93CaseTwoNonmajor.statement_one_or_four_gap` is pinned down exactly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseTwoNonmajorRepair

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **If `f` copies `x` on the two paths and on the far antipath, and in addition is complete
to the near antipath except at `x`, then the neighbour set of `f` in `K` resolves the knot.**

`Qx` is the antipath containing `x` and `Q'` is the other one; `xa` (in `P₁`) and `xb` (in
`P₂`) are the unique neighbours of `x` on the two paths. -/
theorem resolves_of_complete {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ Qx Q' : List V} {K : Set V}
    (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    {f x xa xb : V}
    (hQ'eq : Q' = Q₁ ∨ Q' = Q₂)
    (hcover : ∀ w : V, (w ∈ Q₁ ∨ w ∈ Q₂) → (w ∈ Qx ∨ w ∈ Q'))
    (hxaP : xa ∈ P₁) (hxbP : xb ∈ P₂)
    (hxP₁ : ∀ u ∈ P₁, (G.Adj u x ↔ u = xa))
    (hxP₂ : ∀ u ∈ P₂, (G.Adj u x ↔ u = xb))
    (hxQ' : ∀ w ∈ Q', G.Adj x w)
    (hsame : ∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
      (G.Adj f w ↔ G.Adj x w))
    (hcompl : ∀ w ∈ Qx, w ≠ x → G.Adj f w)
    (hQxK : ∀ w ∈ Qx, w ∈ K) :
    ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K) := by
  have hP₁K : ∀ w ∈ P₁, w ∈ K := by rw [hK]; exact fun w hw => Or.inl (Or.inl (Or.inl hw))
  have hP₂K : ∀ w ∈ P₂, w ∈ K := by rw [hK]; exact fun w hw => Or.inl (Or.inl (Or.inr hw))
  have hQ₁K : ∀ w ∈ Q₁, w ∈ K := by rw [hK]; exact fun w hw => Or.inl (Or.inr hw)
  have hQ₂K : ∀ w ∈ Q₂, w ∈ K := by rw [hK]; exact fun w hw => Or.inr hw
  have hQ'K : ∀ w ∈ Q', w ∈ K := by
    rcases hQ'eq with rfl | rfl
    exacts [hQ₁K, hQ₂K]
  -- every vertex of the far antipath is a neighbour of `f` inside `K`
  have hQ'X : ∀ w ∈ Q', w ∈ (G.neighborSet f ∩ K) := by
    intro w hw
    exact ⟨(hsame w (Or.inr hw)).mpr (hxQ' w hw), hQ'K w hw⟩
  -- the two path-neighbours of `x` are neighbours of `f` inside `K`
  have hxaX : xa ∈ (G.neighborSet f ∩ K) := by
    refine ⟨(hsame xa (Or.inl (Or.inl hxaP))).mpr ?_, hP₁K xa hxaP⟩
    exact ((hxP₁ xa hxaP).mpr rfl).symm
  have hxbX : xb ∈ (G.neighborSet f ∩ K) := by
    refine ⟨(hsame xb (Or.inl (Or.inr hxbP))).mpr ?_, hP₂K xb hxbP⟩
    exact ((hxP₂ xb hxbP).mpr rfl).symm
  refine ⟨?_, ⟨xa, hxaX, hxaP⟩, ⟨xb, hxbX, hxbP⟩, ?_⟩
  · rcases hQ'eq with h | h
    · exact Or.inl (fun w hw => hQ'X w (h ▸ hw))
    · exact Or.inr (fun w hw => hQ'X w (h ▸ hw))
  · intro u hu w hw hadj
    rcases hcover w hw with hwx | hwQ'
    · by_cases hwe : w = x
      · subst hwe
        rcases hu with hu | hu
        · exact Or.inl ((hxP₁ u hu).mp hadj ▸ hxaX)
        · exact Or.inl ((hxP₂ u hu).mp hadj ▸ hxbX)
      · exact Or.inr ⟨hcompl w hwx hwe, hQxK w hwx⟩
    · exact Or.inr (hQ'X w hwQ')

/-- **The dichotomy that the case-(2) argument of 9.3 really proves.**

PAPER (proof of 9.3, printed p. 49): *"... or (up to symmetry) `f, x₁` have the same neighbours
in `V(P₁) ∪ V(P₂) ∪ V(Q₂)` (but then either statement 1 or statement 4 of the theorem
holds)."*

Either the neighbour set of `f` in `K` resolves the knot — statement 1 of 9.3 — or `f` has a
non-neighbour in `V(Qx) \ {x}`, where `Qx` is the antipath one of whose ends is `x`.
Statement 4 of 9.3 asks for the non-neighbour to be the *other end* `y` of `Qx`; that is the
same thing exactly when `Qx` has length `1`. -/
theorem resolves_or_nonneighbour
    (G : SimpleGraph V)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (F : Set V) (f : V) (hfF : f ∈ F)
    (x y : V) (Q' Qx : List V)
    (hchoice : ((x, y, Q', Qx) = (x₁, y₁, Q₂, Q₁) ∨ (x, y, Q', Qx) = (y₁, x₁, Q₂, Q₁) ∨
      (x, y, Q', Qx) = (x₂, y₂, Q₁, Q₂) ∨ (x, y, Q', Qx) = (y₂, x₂, Q₁, Q₂)))
    (hsame : ∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
      (G.Adj f w ↔ G.Adj x w)) :
    (∃ g ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet g ∩ K)) ∨
      (∃ w ∈ Qx, w ≠ x ∧ ¬ G.Adj f w) := by
  classical
  by_cases hc : ∀ w ∈ Qx, w ≠ x → G.Adj f w
  · refine Or.inl ⟨f, hfF, ?_⟩
    obtain ⟨-, -, -, -, -, -, -, -, hq₁len, hq₂len, -, hcomp,
      hE11, hE12, hE21, hE22, -⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
    have hxy₁ : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hQ₁ hq₁len
    have hxy₂ : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hQ₂ hq₂len
    have ha₁P : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).1
    have hb₁P : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem hP₁).2
    have ha₂P : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).1
    have hb₂P : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem hP₂).2
    have hx₁Q : x₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ₁).1
    have hy₁Q : y₁ ∈ Q₁ := (PathBasics.isPathFrom_ends_mem hQ₁).2
    have hx₂Q : x₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ₂).1
    have hy₂Q : y₂ ∈ Q₂ := (PathBasics.isPathFrom_ends_mem hQ₂).2
    have hQ₁K : ∀ w ∈ Q₁, w ∈ K := by rw [hK]; exact fun w hw => Or.inl (Or.inr hw)
    have hQ₂K : ∀ w ∈ Q₂, w ∈ K := by rw [hK]; exact fun w hw => Or.inr hw
    have hcov1 : ∀ w : V, (w ∈ Q₁ ∨ w ∈ Q₂) → (w ∈ Q₁ ∨ w ∈ Q₂) := fun _ h => h
    have hcov2 : ∀ w : V, (w ∈ Q₁ ∨ w ∈ Q₂) → (w ∈ Q₂ ∨ w ∈ Q₁) := fun _ h => h.symm
    rcases hchoice with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨e1, -, e3, e4⟩ := h <;> rw [e1] at hsame hc <;> rw [e3] at hsame <;>
      rw [e4] at hc
    · refine resolves_of_complete hK (Or.inr rfl) hcov1 ha₁P ha₂P ?_ ?_
        (fun w hw => hcomp x₁ hx₁Q w hw) hsame hc hQ₁K
      · intro u hu
        rw [hE11 u hu x₁ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => t.1) (fun t => absurd t.2 hxy₁),
          fun hh => Or.inl ⟨hh, rfl⟩⟩
      · intro u hu
        rw [hE21 u hu x₁ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => t.1) (fun t => absurd t.2 hxy₁),
          fun hh => Or.inl ⟨hh, rfl⟩⟩
    · refine resolves_of_complete hK (Or.inr rfl) hcov1 hb₁P hb₂P ?_ ?_
        (fun w hw => hcomp y₁ hy₁Q w hw) hsame hc hQ₁K
      · intro u hu
        rw [hE11 u hu y₁ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => absurd t.2.symm hxy₁) (fun t => t.1),
          fun hh => Or.inr ⟨hh, rfl⟩⟩
      · intro u hu
        rw [hE21 u hu y₁ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => absurd t.2.symm hxy₁) (fun t => t.1),
          fun hh => Or.inr ⟨hh, rfl⟩⟩
    · refine resolves_of_complete hK (Or.inl rfl) hcov2 ha₁P hb₂P ?_ ?_
        (fun w hw => (hcomp w hw x₂ hx₂Q).symm) hsame hc hQ₂K
      · intro u hu
        rw [hE12 u hu x₂ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => t.1) (fun t => absurd t.2 hxy₂),
          fun hh => Or.inl ⟨hh, rfl⟩⟩
      · intro u hu
        rw [hE22 u hu x₂ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => absurd t.2 hxy₂) (fun t => t.1),
          fun hh => Or.inr ⟨hh, rfl⟩⟩
    · refine resolves_of_complete hK (Or.inl rfl) hcov2 hb₁P ha₂P ?_ ?_
        (fun w hw => (hcomp w hw y₂ hy₂Q).symm) hsame hc hQ₂K
      · intro u hu
        rw [hE12 u hu y₂ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => absurd t.2.symm hxy₂) (fun t => t.1),
          fun hh => Or.inr ⟨hh, rfl⟩⟩
      · intro u hu
        rw [hE22 u hu y₂ (by simp)]
        exact ⟨fun hh => hh.elim (fun t => t.1) (fun t => absurd t.2.symm hxy₂),
          fun hh => Or.inl ⟨hh, rfl⟩⟩
  · push_neg at hc
    obtain ⟨w, hw, hwx, hwadj⟩ := hc
    exact Or.inr ⟨w, hw, hwx, hwadj⟩

end Workspace.ProofLemmas.Thm93CaseTwoNonmajorRepair
