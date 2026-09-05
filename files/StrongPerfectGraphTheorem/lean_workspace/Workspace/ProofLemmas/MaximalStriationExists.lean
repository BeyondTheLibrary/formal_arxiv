import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots

/-!
# Existence of a maximal striation

The proof of 9.6 (printed p. 54) says

> *"… and hence there is a striation in `G`; **choose a maximal striation `L`**."*

Nothing in the paper is cited for the second half of that sentence, and nothing in the
development supplies it: both `thm_9_4` and `thm_9_5` **take** `MaximalStriation G S T` as a
hypothesis, so somebody has to produce one.  This module does.

`Workspace.Types.Knots.SPGT.MaximalStriation` unfolds to *"`(S, T)` is a striation and there is
no striation `(S', T')` whatsoever with `V(L) ⊂ V(L')`"* — the quantifier ranges over **all**
striations of `G`, not merely over those extending `(S, T)`.  That is nevertheless exactly a
maximal element of the up-set of `(S, T)`: any rival `(S', T')` with `V(L) ⊂ V(L')` already
satisfies `V(L₀) ⊆ V(L')` for the starting striation `L₀`, so it lies in the family we
maximise over.

Since a striation is a pair of *families* indexed by `Fin m`, `Fin n` with `m`, `n` varying,
the family of striations is not indexed by a `Fintype`.  The fix is to maximise not over
striations but over their **vertex sets** `striationVertices S T : Set V`, which live in
`Set V` — a finite type as soon as `V` is (`Finite (Set V)` comes from `Pi.finite`), so
`Set.toFinite` applies and `Set.Finite.exists_le_maximal` does the rest.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.MaximalStriationExists

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Finite V]

/-- **Every striation extends to a maximal one.**

This is the *"choose a maximal striation `L`"* of 9.6 (printed p. 54), and the only way to
discharge the `MaximalStriation` hypothesis of `thm_9_4` and `thm_9_5`.

The conclusion also records that the maximal striation found contains the one we started
from, which is what a caller needs when the starting striation was built from a specific
degenerate `K₄` appearance. -/
theorem exists_maximalStriation (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (hstr : IsStriation G S T) :
    ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
      (T' : Fin n' → Set V × Set V × Set V),
      MaximalStriation G S' T' ∧ striationVertices S T ⊆ striationVertices S' T' := by
  classical
  -- Maximise the *vertex set* of a striation extending `(S, T)`, over the finite type `Set V`.
  obtain ⟨W, -, hmax⟩ :=
    Set.Finite.exists_le_maximal
      (s := {W : Set V | ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
          (T' : Fin n' → Set V × Set V × Set V),
          IsStriation G S' T' ∧ striationVertices S' T' = W ∧
            striationVertices S T ⊆ W})
      (Set.toFinite _)
      (a := striationVertices S T)
      ⟨m, n, S, T, hstr, rfl, subset_rfl⟩
  obtain ⟨m', n', S', T', hstr', hWeq, hsub'⟩ := hmax.1
  subst hWeq
  refine ⟨m', n', S', T', ⟨hstr', ?_⟩, hsub'⟩
  -- A rival striation strictly containing this one would itself lie in the family.
  rintro ⟨m'', n'', S'', T'', hstr'', hlt⟩
  have hback : striationVertices S'' T'' ≤ striationVertices S' T' :=
    hmax.2 ⟨m'', n'', S'', T'', hstr'', rfl, hsub'.trans hlt.subset⟩ hlt.subset
  exact absurd (subset_antisymm hlt.subset hback) hlt.ne

end Workspace.ProofLemmas.MaximalStriationExists
