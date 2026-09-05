import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# The `X`-complete edges of `P` all lie before the last `X`-complete vertex

An `X`-complete edge has *both* ends `X`-complete, so if `pₘ` is the last
`X`-complete vertex of `P` then every `X`-complete edge of `P` is already an
`X`-complete edge of the initial segment `p₁-⋯-pₘ`.  This is the silent step in
the printed proof of 18.2 that lets *"an even number of **its** edges are
`X`-complete"* be read off the whole path `P`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm182EdgeSetTake

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- Membership of `p[i]` in the prefix `p.take (m + 1)` when `i ≤ m`. -/
theorem getElem_mem_take (p : List V) {i m : ℕ} (hi : i < p.length) (him : i ≤ m) :
    (p[i]'hi) ∈ p.take (m + 1) := by
  have hlt : i < (p.take (m + 1)).length := by
    rw [List.length_take]; omega
  have heq : (p.take (m + 1))[i]'hlt = p[i]'hi := by
    simp only [List.getElem_take]
  exact heq ▸ List.getElem_mem hlt

/-- Truncating `p` at its last `X`-complete vertex does not change the set of
`X`-complete edges. -/
theorem xed_eq_take (G : SimpleGraph V) (X : Set V) (p : List V)
    (m : ℕ) (hm : m < p.length)
    (hmax : ∀ (k : ℕ) (hk : k < p.length), VertexComplete G (p[k]'hk) X → k ≤ m) :
    {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G X u v}
      = {e : Sym2 V | ∃ u ∈ p.take (m + 1), ∃ v ∈ p.take (m + 1),
          e = s(u, v) ∧ EdgeComplete G X u v} := by
  ext e
  constructor
  · rintro ⟨u, hu, v, hv, rfl, hE⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    exact ⟨_, getElem_mem_take p hi (hmax i hi hE.2.1),
      _, getElem_mem_take p hj (hmax j hj hE.2.2), rfl, hE⟩
  · rintro ⟨u, hu, v, hv, rfl, hE⟩
    exact ⟨u, List.take_subset _ _ hu, v, List.take_subset _ _ hv, rfl, hE⟩

end Workspace.ProofLemmas.Thm182EdgeSetTake
