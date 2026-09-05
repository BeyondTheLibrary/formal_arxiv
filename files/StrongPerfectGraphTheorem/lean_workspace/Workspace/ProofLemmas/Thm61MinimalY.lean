import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# 6.1, opening sentence: we may assume `Y` is minimal

PAPER (proof of 6.1, printed p. 29):

> *"We may assume that `Y` is minimal such that it is anticonnected and its common neighbours
> do not saturate `L(H)`."*

The reduction is legitimate because the conclusion of 6.1 is monotone in `Y`
(`Workspace.ProofLemmas.Thm61Conclusion.Thm61Concl_mono`), so it suffices to prove the theorem
for a minimal `Y₀ ⊆ Y`.  This module supplies the existence of that minimal `Y₀`.

The argument is the usual finite-minimality one: the collection of subsets `Z ⊆ Y` that are
anticonnected and whose set of common neighbours in `L(H)` does not saturate `L(H)` is nonempty
(it contains `Y`), and `V` is finite, so one may take a member of least cardinality.  Note that
minimality is only ever used against *proper subsets*, and every proper subset of `Y₀` is a
subset of `Y`, so no separate `⊆ Y` clause is needed in the minimality statement.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61MinimalY

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- **6.1, first sentence.**  *"We may assume that `Y` is minimal such that it is anticonnected
and its common neighbours do not saturate `L(H)`."*

Given one anticonnected `Y` whose set of `Y`-complete vertices of `L(H)` fails to saturate
`L(H)`, there is a subset `Y₀ ⊆ Y` with the same two properties which is minimal: every proper
subset of `Y₀` that is anticonnected *does* have a saturating set of common neighbours. -/
theorem exists_minimal_anticonnected_nonsaturating
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hnotsat : ¬ SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, VertexComplete G (↑(φ ⟨e, he⟩) : V) Y}) :
    ∃ Y₀ : Set V, Y₀ ⊆ Y ∧ AnticonnectedSet G Y₀ ∧
      (¬ SaturatesLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, VertexComplete G (↑(φ ⟨e, he⟩) : V) Y₀}) ∧
      ∀ Y₁ : Set V, Y₁ ⊂ Y₀ → AnticonnectedSet G Y₁ →
        SaturatesLineGraph H
          {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
            VertexComplete G (↑(φ ⟨e, he⟩) : V) Y₁} := by
  classical
  -- The property "`Z` is a subset of `Y`, anticonnected, and its common neighbours in `L(H)`
  -- do not saturate `L(H)`".
  set P : Set V → Prop := fun Z => Z ⊆ Y ∧ AnticonnectedSet G Z ∧
    ¬ SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, VertexComplete G (↑(φ ⟨e, he⟩) : V) Z} with hP
  have hex : ∃ k : ℕ, ∃ Z : Set V, P Z ∧ Z.ncard = k :=
    ⟨Y.ncard, Y, ⟨subset_rfl, hYanti, hnotsat⟩, rfl⟩
  obtain ⟨Z, hZ, hZcard⟩ := Nat.find_spec hex
  refine ⟨Z, hZ.1, hZ.2.1, hZ.2.2, ?_⟩
  intro Y₁ hlt hanti
  by_contra hns
  have hPY₁ : P Y₁ := ⟨hlt.subset.trans hZ.1, hanti, hns⟩
  have hle : Nat.find hex ≤ Y₁.ncard := Nat.find_le ⟨Y₁, hPY₁, rfl⟩
  have hlt' : Y₁.ncard < Z.ncard := Set.ncard_lt_ncard hlt (Set.toFinite Z)
  omega

end Workspace.ProofLemmas.Thm61MinimalY
