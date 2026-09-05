import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# *"Choose an `X`-complete vertex `pᵢ` in `P` with `i` maximum"*

The opening move of the printed proof of 18.2 (published page 110).  Since `p₁` is
`X`-complete the set of indices of `X`-complete vertices of `P` is non-empty, and it
is a set of indices into a finite list, so it has a maximum.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm182MaxIndex

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- **"Choose an `X`-complete vertex `pᵢ` in `P` with `i` maximum."**  Stated with
0-based indices, so the paper's `i` is `m + 1`. -/
theorem exists_max_complete_index (G : SimpleGraph V) (X : Set V) (p : List V)
    (hpos : 0 < p.length) (h0 : VertexComplete G (p[0]'hpos) X) :
    ∃ m : ℕ, ∃ hm : m < p.length,
      VertexComplete G (p[m]'hm) X ∧
      ∀ (k : ℕ) (hk : k < p.length), VertexComplete G (p[k]'hk) X → k ≤ m := by
  classical
  set P : ℕ → Prop := fun k => ∃ h : k < p.length, VertexComplete G (p[k]'h) X with hPdef
  set s : Finset ℕ := (Finset.range p.length).filter P with hsdef
  have hmem_iff : ∀ k : ℕ, k ∈ s ↔ (k < p.length ∧ P k) := by
    intro k
    rw [hsdef, Finset.mem_filter, Finset.mem_range]
  have h0s : (0 : ℕ) ∈ s := (hmem_iff 0).mpr ⟨hpos, ⟨hpos, h0⟩⟩
  have hne : s.Nonempty := ⟨0, h0s⟩
  have hmax := s.max'_mem hne
  obtain ⟨hlt, hlt', hc⟩ := (hmem_iff _).mp hmax
  refine ⟨s.max' hne, hlt, hc, ?_⟩
  intro k hk hck
  exact Finset.le_max' s k ((hmem_iff k).mpr ⟨hk, ⟨hk, hck⟩⟩)

end Workspace.ProofLemmas.Thm182MaxIndex
