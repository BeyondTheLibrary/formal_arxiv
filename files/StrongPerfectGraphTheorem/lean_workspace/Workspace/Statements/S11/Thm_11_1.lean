/-  Proof attempt 1 for statement 11.1.

    The printed proof (paper/proofs/11_1.md) is:

      "Let F be a connected subset of V(P), containing v and disjoint from V(R₀), and with an
      attachment in R₀ \ a₀.

      (1) For every step a₁-R₁-b₁, a₂-R₂-b₂, if v has a neighbour in R₁ ∪ R₂ then v is adjacent
      to a₁, a₂ and to no other vertices of R₁ ∪ R₂.

      [proof of (1)]

      From (1) it follows that v has no neighbour in C (since every vertex is in a step), and
      therefore v has at least one neighbour in A; and from (1) again, v has no nonneighbour in
      A (for otherwise we could choose the step in (1) with v adjacent to a₁ and not to a₂,
      since the strip is step-connected.)  This proves 11.1."

    Statement (1), together with the choice of F, is the commissioned carve-out
    `Workspace.ProofLemmas.Thm111Claim1.thm111Claim1`; it is cited here rather than re-derived.
    The three sentences after (1) are the three `have`s below, in the printed order.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm111Claim1

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S11

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **11.1** (printed p. 64)

PAPER: *"Let `G` be a Berge graph, such that there is no nondegenerate appearance of `K₄` in
`G`.  Let `S = (A, C, B)` be a step-connected strip in `G`, and let `a₀`-`R₀`-`b₀` be a
banister.  Suppose that `v ∈ V(G) \ V(S)` has a neighbour in `A ∪ C`, and has no neighbour in
`B`; and that `P` is a path in `G \ (V(S) ∪ {a₀})` from `v` to `b₀`, such that there are no
edges between `P*` and `V(S)`.  Then `v` is a left-star."*

Notes on the transcription.

* `V(S) = A ∪ B ∪ C`, so `v ∈ V(G) \ V(S)` is `v ∉ A ∪ B ∪ C`.
* *"`P` is a path in `G \ (V(S) ∪ {a₀})` from `v` to `b₀`"* is: `P` is a path of `G` with ends
  `v` and `b₀`, none of whose vertices lies in `V(S) ∪ {a₀}`.
* *"has no neighbour in `B`"* is `VertexAnticomplete G v B`. -/
theorem thm_11_1 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (A C B : Set V) (hS : StepConnected G A C B)
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ A ∪ B ∪ C)
    (hvAC : ∃ x ∈ A ∪ C, G.Adj v x)
    (hvB : SPGT.VertexAnticomplete G v B)
    (P : List V) (hP : IsPathFrom G P v b₀)
    (hPavoid : ∀ w ∈ P, w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V))
    (hPint : SPGT.Anticomplete G {w : V | w ∈ SPGT.interior P} (A ∪ B ∪ C)) :
    IsLeftStar G A C B v := by
  -- Statement (1) of the printed proof, cited from the carve-out.
  have claim1 : ∀ (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ →
      (∃ x : V, (x ∈ R₁ ∨ x ∈ R₂) ∧ G.Adj v x) →
      G.Adj v a₁ ∧ G.Adj v a₂ ∧
        ∀ x : V, (x ∈ R₁ ∨ x ∈ R₂) → G.Adj v x → (x = a₁ ∨ x = a₂) := by
    intro a₁ R₁ b₁ a₂ R₂ b₂ hstep hnb
    exact _root_.Workspace.ProofLemmas.Thm111Claim1.thm111Claim1 G hG hK4 A C B hS a₀ b₀ R₀
      hban v hv hvB P hP hPavoid hPint a₁ R₁ b₁ a₂ R₂ b₂ hstep hnb
  -- "From (1) it follows that v has no neighbour in C (since every vertex is in a step)".
  have hvC : SPGT.VertexAnticomplete G v C := by
    intro c hc hadj
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hcmem⟩ :=
      hS.2.2.2.1 c (Set.mem_union_right _ hc)
    obtain ⟨-, -, h3⟩ := claim1 a₁ R₁ b₁ a₂ R₂ b₂ hstep ⟨c, hcmem, hadj⟩
    rcases h3 c hcmem hadj with rfl | rfl
    · exact Set.disjoint_left.mp hS.1.2.1 hstep.1.2.1 hc
    · exact Set.disjoint_left.mp hS.1.2.1 hstep.2.1.2.1 hc
  -- v is anticomplete to B ∪ C: to B by hypothesis, to C by the previous step.
  have hvBC : SPGT.VertexAnticomplete G v (B ∪ C) := by
    rintro x (hx | hx)
    · exact hvB x hx
    · exact hvC x hx
  -- "and therefore v has at least one neighbour in A"
  obtain ⟨x₀, hx₀mem, hx₀adj⟩ := hvAC
  have hx₀A : x₀ ∈ A := by
    rcases hx₀mem with h | h
    · exact h
    · exact absurd hx₀adj (hvC x₀ h)
  -- "and from (1) again, v has no nonneighbour in A (for otherwise we could choose the step in
  -- (1) with v adjacent to a₁ and not to a₂, since the strip is step-connected.)"
  have hcomplete : SPGT.VertexComplete G v A := by
    by_contra hcon
    have hcon' : ¬ ∀ x ∈ A, G.Adj v x := hcon
    push Not at hcon'
    obtain ⟨a, haA, hna⟩ := hcon'
    -- the partition of A into the neighbours and the nonneighbours of v
    have hXY : {y : V | y ∈ A ∧ G.Adj v y} ∪ {y : V | y ∈ A ∧ ¬ G.Adj v y} = A := by
      ext y
      constructor
      · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
      · intro hy
        by_cases hadj : G.Adj v y
        · exact Or.inl ⟨hy, hadj⟩
        · exact Or.inr ⟨hy, hadj⟩
    have hdisj : Disjoint {y : V | y ∈ A ∧ G.Adj v y} {y : V | y ∈ A ∧ ¬ G.Adj v y} := by
      rw [Set.disjoint_left]
      rintro y ⟨-, h1⟩ ⟨-, h2⟩
      exact h2 h1
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hend₁, hend₂⟩ :=
      hS.2.2.2.2 {y : V | y ∈ A ∧ G.Adj v y} {y : V | y ∈ A ∧ ¬ G.Adj v y}
        (Or.inl hXY) hdisj ⟨x₀, hx₀A, hx₀adj⟩ ⟨a, haA, hna⟩
    -- the end of R₁ lying in the neighbour class is a₁ (b₁ ∈ B is disjoint from A)
    have hadj₁ : G.Adj v a₁ := by
      rcases hend₁ with h | h
      · exact h.2
      · exact absurd h.1 (Set.disjoint_right.mp hS.1.1 hstep.1.2.2.1)
    -- likewise the end of R₂ lying in the nonneighbour class is a₂
    have hnadj₂ : ¬ G.Adj v a₂ := by
      rcases hend₂ with h | h
      · exact h.2
      · exact absurd h.1 (Set.disjoint_right.mp hS.1.1 hstep.2.1.2.2.1)
    -- v has a neighbour in R₁, so (1) forces v to be adjacent to a₂ as well
    have ha₁mem : a₁ ∈ R₁ :=
      (_root_.Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hstep.1.1).1
    exact hnadj₂ (claim1 a₁ R₁ b₁ a₂ R₂ b₂ hstep ⟨a₁, Or.inl ha₁mem, hadj₁⟩).2.1
  exact ⟨hv, hcomplete, hvBC⟩


end SPGT

end Workspace.Statements.S11
