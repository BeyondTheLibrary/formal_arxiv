/-  Proof attempt 1 for statement 11.3 (`Workspace.Statements.S11.SPGT.thm_11_3`).

    THE PAPER'S PROOF (perfect.pdf, printed p. 67; `paper/proofs/11_3.md`), verbatim:

        "Proof.  Let a1-R1-b1, a2-R2-b2 be a step.  Then these three paths form a prism,
         and it is not an even prism by hypothesis.  In particular R0 has odd length, by
         7.2.  For any rung a-R-b, the hole a0-R0-b0-b-R-a-a0 has even length, and so R
         is odd.  This proves 11.3."

    The Lean proof follows those four sentences in order:

    * `banister_odd` is sentences 1-3.  A step exists because the strip is step-connected
      and `A` is nonempty (every vertex of `A ∪ B ∪ C` lies in a step).  The three paths
      `R₀, R₁, R₂` form a prism with triangles `{a₀,a₁,a₂}`, `{b₀,b₁,b₂}`: `a₀` is a
      left-star so it is complete to `A` (hence adjacent to `a₁, a₂`) and anticomplete to
      `B ∪ C`, `b₀` is a right-star, `a₁a₂` and `b₁b₂` are the two edges of the step, and
      the interior of the banister is anticomplete to `V(S)`, so the only edges between
      `V(R₀)` and `V(Rᵢ)` are `a₀aᵢ` and `b₀bᵢ`.  If `R₀` were even then by 7.2 all three
      would be even, i.e. an even prism, contrary to hypothesis; so `R₀` is odd.
    * `rung_odd_of_banister_odd` is the fourth sentence.  For a rung `a-R-b` the list
      `R₀ ++ R.reverse` is exactly the printed cycle `a₀-R₀-b₀-b-R-a-a₀`; it is a hole by
      the same "only edges are `a₀a` and `b₀b`" computation, so `G` being Berge makes
      `|R₀| + |R|` even, and since `R₀` is odd so is `R`.

    Nothing here departs from the printed argument; the helper lemmas only spell out the
    edge bookkeeping the authors leave implicit.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S07.Thm_7_2

set_option autoImplicit false

-- The frozen statement's `variable` line carries `[Fintype V] [DecidableEq V]`, which the
-- rung half of this proof does not use.  The linter's suggested `omit ... in` would change
-- the elaborated signature (and be rejected by `rollback_check`), so it is switched off.
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S11

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

/-! ### Helper lemmas

Edge bookkeeping around a banister and the rungs of its strip.  These have no counterpart
in the paper: the authors simply say "these three paths form a prism" and "the hole
`a₀-R₀-b₀-b-R-a-a₀`", leaving the verification to the reader. -/

section Helpers

variable {V : Type*}

/-- A path with two distinct ends has at least two vertices. -/
private theorem len_ge_two {G : SimpleGraph V} {P : List V} {x y : V}
    (hP : IsPathFrom G P x y) (hxy : x ≠ y) : 2 ≤ P.length := by
  have h0 : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
  by_contra hcon
  have hone : P.length = 1 := by omega
  obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hone
  have h1 : c = x := by simpa using hP.2.1
  have h2 : c = y := by simpa using hP.2.2
  exact hxy (h1.symm.trans h2)

/-- Every vertex of a rung lies in `V(S) = A ∪ B ∪ C`. -/
private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V} {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) : ∀ w ∈ p, w ∈ A ∪ B ∪ C := by
  intro w hw
  by_cases hwa : w = a
  · exact Or.inl (Or.inl (by rw [hwa]; exact h.2.1))
  by_cases hwb : w = b
  · exact Or.inl (Or.inr (by rw [hwb]; exact h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 w
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).mpr
        ⟨hw, hwa, hwb⟩))

/-- The only edges between a banister `a₀-R₀-b₀` and a rung `a-R-b` are `a₀a` and `b₀b`. -/
private theorem banister_rung_edges {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ a b : V}
    {R₀ R : List V} (hban : IsBanister G A C B a₀ R₀ b₀)
    (hr : IsRungOfStrip G A C B a R b) :
    ∀ u ∈ R₀, ∀ w ∈ R, (G.Adj u w ↔ (u = a₀ ∧ w = a) ∨ (u = b₀ ∧ w = b)) := by
  obtain ⟨hR₀path, _, hLS, hRS, hR₀int⟩ := hban
  intro u hu w hw
  constructor
  · intro hadj
    have hwS : w ∈ A ∪ B ∪ C := rung_mem_strip hr w hw
    by_cases hua : u = a₀
    · subst u
      refine Or.inl ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact hr.2.2.2.1 w hw hwA
      · exact absurd hadj (hLS.2.2 w (Or.inl hwB))
      · exact absurd hadj (hLS.2.2 w (Or.inr hwC))
    by_cases hub : u = b₀
    · subst u
      refine Or.inr ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact absurd hadj (hRS.2.2 w (Or.inl hwA))
      · exact hr.2.2.2.2.1 w hw hwB
      · exact absurd hadj (hRS.2.2 w (Or.inr hwC))
    · exact absurd hadj (hR₀int u
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR₀path).mpr
          ⟨hu, hua, hub⟩) w hwS)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hLS.2.1 w hr.2.1
    · exact hRS.2.1 w hr.2.2.1

/-- **The paper's fourth sentence**: *"For any rung `a`-`R`-`b`, the hole
`a₀`-`R₀`-`b₀`-`b`-`R`-`a`-`a₀` has even length, and so `R` is odd."*

The printed cycle is the list `R₀ ++ R.reverse`. -/
private theorem rung_odd_of_banister_odd {G : SimpleGraph V} {A C B : Set V}
    {a₀ b₀ a b : V} {R₀ R : List V}
    (hdAB : Disjoint A B) (hBerge : Berge G)
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (hr : IsRungOfStrip G A C B a R b)
    (hodd0 : Odd (pathLength R₀)) :
    Odd (pathLength R) := by
  have hban' := hban
  obtain ⟨hR₀path, hR₀out, hLS, hRS, _⟩ := hban'
  have haA : a ∈ A := hr.2.1
  have hbB : b ∈ B := hr.2.2.1
  -- `a₀ ≠ b₀`: `a₀` is adjacent to `a ∈ A` and `b₀` is anticomplete to `A ∪ C`.
  have hne : a₀ ≠ b₀ := by
    intro hc
    exact hRS.2.2 a (Or.inl haA) (by rw [← hc]; exact hLS.2.1 a haA)
  have hab : a ≠ b := by
    intro hc
    exact Set.disjoint_left.mp hdAB haA (by rw [hc]; exact hbB)
  have hlen0 : 2 ≤ R₀.length := len_ge_two hR₀path hne
  have hlenR : 2 ≤ R.length := len_ge_two hr.1 hab
  have hRrev : IsPathFrom G R.reverse b a :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hr.1
  have hcross := banister_rung_edges hban hr
  have hhole : IsHoleList G (R₀ ++ R.reverse) := by
    refine Workspace.ProofLemmas.PathGlue.glue_hole hR₀path hRrev ?_ ?_ ?_
    · intro x hx hx'
      exact hR₀out x hx (rung_mem_strip hr x (List.mem_reverse.mp hx'))
    · intro x hx y hy
      rw [hcross x hx y (List.mem_reverse.mp hy)]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl h
    · simp only [List.length_reverse]; omega
  have hev : Even ((R₀ ++ R.reverse).length) := hBerge.1 _ hhole
  simp only [List.length_append, List.length_reverse] at hev
  rw [Nat.even_iff] at hev
  rw [Nat.odd_iff] at hodd0 ⊢
  simp only [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hodd0 ⊢
  omega

end Helpers

section BanisterOdd

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The paper's first three sentences**: *"Let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step.
Then these three paths form a prism, and it is not an even prism by hypothesis.  In
particular `R₀` has odd length, by 7.2."* -/
private theorem banister_odd {G : SimpleGraph V} {A C B : Set V}
    {a₀ b₀ a₁ b₁ a₂ b₂ : V} {R₀ R₁ R₂ : List V}
    (hdAB : Disjoint A B)
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (hStep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hBerge : Berge G)
    (hNoEven : ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
      IsEvenPrism G alpha beta P₁ P₂ P₃) :
    Odd (pathLength R₀) := by
  have hban' := hban
  obtain ⟨hR₀path, _, hLS, hRS, _⟩ := hban'
  obtain ⟨hr₁, hr₂, _, hcross12⟩ := hStep
  have ha₁A : a₁ ∈ A := hr₁.2.1
  have hb₁B : b₁ ∈ B := hr₁.2.2.1
  have ha₂A : a₂ ∈ A := hr₂.2.1
  have hb₂B : b₂ ∈ B := hr₂.2.2.1
  have ha₁R₁ : a₁ ∈ R₁ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).1
  have hb₁R₁ : b₁ ∈ R₁ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).2
  have ha₂R₂ : a₂ ∈ R₂ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).1
  have hb₂R₂ : b₂ ∈ R₂ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).2
  have hAdj_a0a1 : G.Adj a₀ a₁ := hLS.2.1 a₁ ha₁A
  have hAdj_a0a2 : G.Adj a₀ a₂ := hLS.2.1 a₂ ha₂A
  have hAdj_a1a2 : G.Adj a₁ a₂ :=
    (hcross12 a₁ ha₁R₁ a₂ ha₂R₂).mpr (Or.inl ⟨rfl, rfl⟩)
  have hAdj_b0b1 : G.Adj b₀ b₁ := hRS.2.1 b₁ hb₁B
  have hAdj_b0b2 : G.Adj b₀ b₂ := hRS.2.1 b₂ hb₂B
  have hAdj_b1b2 : G.Adj b₁ b₂ :=
    (hcross12 b₁ hb₁R₁ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩)
  have hne_a0b0 : a₀ ≠ b₀ := by
    intro hc
    exact hRS.2.2 a₁ (Or.inl ha₁A) (by rw [← hc]; exact hAdj_a0a1)
  have hne_a0b1 : a₀ ≠ b₁ := by
    intro hc
    exact hLS.1 (by rw [hc]; exact Or.inl (Or.inr hb₁B))
  have hne_a0b2 : a₀ ≠ b₂ := by
    intro hc
    exact hLS.1 (by rw [hc]; exact Or.inl (Or.inr hb₂B))
  have hne_a1b0 : a₁ ≠ b₀ := by
    intro hc
    exact hRS.1 (by rw [← hc]; exact Or.inl (Or.inl ha₁A))
  have hne_a2b0 : a₂ ≠ b₀ := by
    intro hc
    exact hRS.1 (by rw [← hc]; exact Or.inl (Or.inl ha₂A))
  have hne_a1b1 : a₁ ≠ b₁ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₁A (by rw [← hc] at hb₁B; exact hb₁B)
  have hne_a1b2 : a₁ ≠ b₂ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₁A (by rw [← hc] at hb₂B; exact hb₂B)
  have hne_a2b1 : a₂ ≠ b₁ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₂A (by rw [← hc] at hb₁B; exact hb₁B)
  have hne_a2b2 : a₂ ≠ b₂ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₂A (by rw [← hc] at hb₂B; exact hb₂B)
  have hcross01 : ∀ u ∈ R₀, ∀ w ∈ R₁,
      (G.Adj u w ↔ (u = a₀ ∧ w = a₁) ∨ (u = b₀ ∧ w = b₁)) :=
    banister_rung_edges hban hr₁
  have hcross02 : ∀ u ∈ R₀, ∀ w ∈ R₂,
      (G.Adj u w ↔ (u = a₀ ∧ w = a₂) ∨ (u = b₀ ∧ w = b₂)) :=
    banister_rung_edges hban hr₂
  have hprism : FormPrism G ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂ :=
    Workspace.ProofLemmas.PrismBasics.formPrism_of_data
      hAdj_a0a1 hAdj_a0a2 hAdj_a1a2 hAdj_b0b1 hAdj_b0b2 hAdj_b1b2
      hne_a0b0 hne_a0b1 hne_a0b2 hne_a1b0 hne_a1b1 hne_a1b2
      hne_a2b0 hne_a2b1 hne_a2b2 hR₀path hr₁.1 hr₂.1 hcross01 hcross02 hcross12
  -- 7.2: the three paths of a prism in a Berge graph have the same parity.
  have hpar := Workspace.Statements.S07.SPGT.thm_7_2 G hBerge
    ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂ hprism
  have hnotEven0 : ¬ Even (pathLength R₀) := by
    intro he0
    exact hNoEven ⟨![a₀, a₁, a₂], ![b₀, b₁, b₂], R₀, R₁, R₂,
      hprism, he0, hpar.1.mp he0, hpar.2.mp he0⟩
  exact Nat.not_even_iff_odd.mp hnotEven0

end BanisterOdd

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **11.3** (printed p. 65), introduced by *"We remark:"*

PAPER: *"Let `G` be Berge, containing no even prism, let `S = (A, C, B)` be a step-connected
strip in `G`, and let `a₀`-`R₀`-`b₀` be a banister.  Then every rung of the strip has odd
length, and so does `R₀`."*

This is the **published** form of 11.3.  The arXiv v1 draft stops at *"every rung of the strip
has odd length"*, which is strictly weaker than the form its own 11.4 cites (*"By 11.3 `R₀`
and every rung has odd length"*); both proofs in fact derive the assertion about `R₀`. -/
theorem thm_11_3 (G : SimpleGraph V) (hG : Berge G)
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (A C B : Set V) (hS : StepConnected G A C B)
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀) :
    (∀ (a : V) (p : List V) (b : V), IsRungOfStrip G A C B a p b → Odd (pathLength p)) ∧
      Odd (pathLength R₀) := by
  obtain ⟨⟨hdAB, _, _⟩, ⟨hAne, _⟩, _, hinstep, _⟩ := hS
  -- "Let a₁-R₁-b₁, a₂-R₂-b₂ be a step."  One exists: the strip is step-connected, so every
  -- vertex of A ∪ B ∪ C lies in a step, and A is nonempty.
  obtain ⟨x, hx⟩ := hAne
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hStep, -⟩ := hinstep x (Or.inl (Or.inl hx))
  -- "Then these three paths form a prism ... In particular R₀ has odd length, by 7.2."
  have hodd0 : Odd (pathLength R₀) := banister_odd hdAB hban hStep hG hprism
  refine ⟨?_, hodd0⟩
  -- "For any rung a-R-b, the hole a₀-R₀-b₀-b-R-a-a₀ has even length, and so R is odd."
  intro a p b hr
  exact rung_odd_of_banister_odd hdAB hG hban hr hodd0


end SPGT

end Workspace.Statements.S11
