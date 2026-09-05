import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PrismSymmetry

/-!
# The four-way conclusion of 10.1, packaged, and its two symmetries

PAPER (10.1, printed p. 56): *"Then there is a path `f₁-⋯-fₙ` in `F` with `n ≥ 1`, such that
**(up to symmetry)** either: 1. … 2. … 3. … 4. …"*

`Concl G a b R K f f₁ fn` is *exactly* the inner existential of the frozen Lean statement
`Workspace.Statements.S10.SPGT.thm_10_1` — the `∃ a' b' R' σ, …` block carrying the four
alternatives 10.1.1–10.1.4.  Packaging it as a `def` is what lets the printed proof's repeated
*"from the symmetry we may assume"* / *"by exchanging `A` and `B` if necessary"* be discharged
by the two transport lemmas below instead of by re-running the case analysis six or twelve
times:

* `concl_perm` — it suffices to prove the conclusion for the prism relabelled by any
  permutation `τ` of the three indices;
* `concl_swap` — it suffices to prove it with the two triangles `A = {a₁,a₂,a₃}` and
  `B = {b₁,b₂,b₃}` interchanged.

Both are pure bookkeeping on the existential: `Concl` already quantifies over the relabelling
`σ` and over the choice of which triangle plays the role of `A`, so a permuted instance is
recovered by composing permutations, and a swapped instance by flipping the disjunct.

The hypotheses of 10.1 are invariant under the same two symmetries; that half lives in
`Workspace.ProofLemmas.PrismSymmetry` (`formPrism_perm`, `formPrism_swap`,
`localForPrism_perm`, `localForPrism_swap`, `majorForPrism_perm`, `majorForPrism_swap`,
`prismVertices_perm`, `prismVertices_reverse`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm101Assembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*}

/-- The conclusion of 10.1, for a fixed path `f` with ends `f₁`, `fn`: the `∃ a' b' R' σ, …`
block of the frozen statement, listing the four alternatives 10.1.1–10.1.4. -/
def Concl (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V) (K : Set V)
    (f : List V) (f₁ fn : V) : Prop :=
  ∃ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (σ : Equiv.Perm (Fin 3)),
    (R' = fun i => R (σ i)) ∧
    (((a' = fun i => a (σ i)) ∧ (b' = fun i => b (σ i))) ∨
      ((a' = fun i => b (σ i)) ∧ (b' = fun i => a (σ i)))) ∧
    -- 10.1.1
    ((∃ u u' : V, u ∈ R' 0 ∧ u' ∈ R' 0 ∧ G.Adj u u' ∧ G.Adj f₁ u ∧ G.Adj f₁ u' ∧
        ∃ w w' : V, w ∈ R' 1 ∧ w' ∈ R' 1 ∧ G.Adj w w' ∧ G.Adj fn w ∧ G.Adj fn w' ∧
          (∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
            (x = f₁ ∧ (k = u ∨ k = u')) ∨ (x = fn ∧ (k = w ∨ k = w'))) ∧
          Appears G (⊤ : SimpleGraph (Fin 4))) ∨
    -- 10.1.2
      (2 ≤ f.length ∧ (∀ i : Fin 3, G.Adj f₁ (a' i)) ∧ (∀ i : Fin 3, G.Adj fn (b' i)) ∧
        (∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
          (x = f₁ ∧ ∃ i : Fin 3, k = a' i) ∨ (x = fn ∧ ∃ i : Fin 3, k = b' i))) ∨
    -- 10.1.3
      (2 ≤ f.length ∧ G.Adj f₁ (a' 0) ∧ G.Adj f₁ (a' 1) ∧
        G.Adj fn (b' 0) ∧ G.Adj fn (b' 1) ∧
        (∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
          (x = f₁ ∧ (k = a' 0 ∨ k = a' 1)) ∨ (x = fn ∧ (k = b' 0 ∨ k = b' 1)))) ∨
    -- 10.1.4
      (G.Adj f₁ (a' 0) ∧ G.Adj f₁ (a' 1) ∧ (∃ y ∈ R' 2, y ≠ a' 2 ∧ G.Adj fn y) ∧
        (∀ x ∈ f, ∀ k ∈ K, k ≠ a' 2 → G.Adj x k →
          (x = f₁ ∧ (k = a' 0 ∨ k = a' 1)) ∨ (x = fn ∧ k ∈ R' 2))))

/-- **"From the symmetry we may assume …" (permuting the three indices).**  Proving 10.1's
conclusion for the prism relabelled by `τ` proves it for the original labelling. -/
theorem concl_perm {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V} {K : Set V}
    {f : List V} {f₁ fn : V} (τ : Equiv.Perm (Fin 3))
    (h : Concl G (fun i => a (τ i)) (fun i => b (τ i)) (fun i => R (τ i)) K f f₁ fn) :
    Concl G a b R K f f₁ fn := by
  obtain ⟨a', b', R', σ, hR', hab, hcase⟩ := h
  refine ⟨a', b', R', τ * σ, ?_, ?_, hcase⟩
  · rw [hR']; funext i; simp [Equiv.Perm.mul_apply]
  · rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1]; funext i; simp [Equiv.Perm.mul_apply],
        by rw [h2]; funext i; simp [Equiv.Perm.mul_apply]⟩
    · exact Or.inr ⟨by rw [h1]; funext i; simp [Equiv.Perm.mul_apply],
        by rw [h2]; funext i; simp [Equiv.Perm.mul_apply]⟩

/-- **"By exchanging `A` and `B` if necessary".**  Proving 10.1's conclusion with the two
triangles interchanged proves it for the original labelling.  (The paths themselves are not
relabelled: the four alternatives refer to `R'` only through vertex membership.) -/
theorem concl_swap {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V} {K : Set V}
    {f : List V} {f₁ fn : V} (h : Concl G b a R K f f₁ fn) :
    Concl G a b R K f f₁ fn := by
  obtain ⟨a', b', R', σ, hR', hab, hcase⟩ := h
  exact ⟨a', b', R', σ, hR', hab.symm, hcase⟩

end Workspace.ProofLemmas.Thm101Assembly
