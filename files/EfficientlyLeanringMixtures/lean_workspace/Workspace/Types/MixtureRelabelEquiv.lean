import Mathlib
import Workspace.Types.GaussianMixture2
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 400000

namespace Workspace.Types.MixtureRelabelEquiv

open Workspace.Types.GaussianMixture2
open Workspace.Types.GaussianPDF

/--
Equivalence-up-to-relabeling for two-component Gaussian mixtures.

`MixtureRelabelEquiv F F'` holds iff there exists a permutation `π ∈ Sym{1,2}`
such that for every `i ∈ {1,2}`, `w_i = w'_{π(i)}` and the `i`-th component has
the same parameter tuple `(μ, σ²)` as the `π(i)`-th component of `F'`.

Only the two permutations of `{1,2}` are possible, so we unfold this to a
straight disjunction of the *identity case* and the *swap case*.

We compare Gaussian components by the projections `mean` and `varSq` (NOT
by full structure equality or by density equality) — this matches the paper's
phrasing "parameters are the same" and avoids spurious dependence on the
positivity proof term `varSq_pos`.
-/
def MixtureRelabelEquiv (F F' : GaussianMixture2) : Prop :=
  (F.weight1 = F'.weight1 ∧ F.weight2 = F'.weight2 ∧
    F.comp1.mean = F'.comp1.mean ∧ F.comp1.varSq = F'.comp1.varSq ∧
    F.comp2.mean = F'.comp2.mean ∧ F.comp2.varSq = F'.comp2.varSq)
  ∨
  (F.weight1 = F'.weight2 ∧ F.weight2 = F'.weight1 ∧
    F.comp1.mean = F'.comp2.mean ∧ F.comp1.varSq = F'.comp2.varSq ∧
    F.comp2.mean = F'.comp1.mean ∧ F.comp2.varSq = F'.comp1.varSq)

namespace MixtureRelabelEquiv

/-- Constructor for the identity case (no relabeling): the parameter tuples of
`F` and `F'` agree componentwise. -/
theorem identity {F F' : GaussianMixture2}
    (hw1 : F.weight1 = F'.weight1) (hw2 : F.weight2 = F'.weight2)
    (hμ1 : F.comp1.mean = F'.comp1.mean) (hσ1 : F.comp1.varSq = F'.comp1.varSq)
    (hμ2 : F.comp2.mean = F'.comp2.mean) (hσ2 : F.comp2.varSq = F'.comp2.varSq) :
    MixtureRelabelEquiv F F' :=
  Or.inl ⟨hw1, hw2, hμ1, hσ1, hμ2, hσ2⟩

/-- Constructor for the swap case: the parameter tuple of `F` agrees with that
of `F'` after swapping the two components of `F'`. -/
theorem swap {F F' : GaussianMixture2}
    (hw1 : F.weight1 = F'.weight2) (hw2 : F.weight2 = F'.weight1)
    (hμ1 : F.comp1.mean = F'.comp2.mean) (hσ1 : F.comp1.varSq = F'.comp2.varSq)
    (hμ2 : F.comp2.mean = F'.comp1.mean) (hσ2 : F.comp2.varSq = F'.comp1.varSq) :
    MixtureRelabelEquiv F F' :=
  Or.inr ⟨hw1, hw2, hμ1, hσ1, hμ2, hσ2⟩

/-- Alias for `identity`: introducing the left (no-relabeling) disjunct. -/
theorem inl {F F' : GaussianMixture2}
    (h : F.weight1 = F'.weight1 ∧ F.weight2 = F'.weight2 ∧
        F.comp1.mean = F'.comp1.mean ∧ F.comp1.varSq = F'.comp1.varSq ∧
        F.comp2.mean = F'.comp2.mean ∧ F.comp2.varSq = F'.comp2.varSq) :
    MixtureRelabelEquiv F F' :=
  Or.inl h

/-- Alias for `swap`: introducing the right (swap) disjunct. -/
theorem inr {F F' : GaussianMixture2}
    (h : F.weight1 = F'.weight2 ∧ F.weight2 = F'.weight1 ∧
        F.comp1.mean = F'.comp2.mean ∧ F.comp1.varSq = F'.comp2.varSq ∧
        F.comp2.mean = F'.comp1.mean ∧ F.comp2.varSq = F'.comp1.varSq) :
    MixtureRelabelEquiv F F' :=
  Or.inr h

/-- Reflexivity: every mixture is relabel-equivalent to itself (via the
identity permutation). -/
theorem refl (F : GaussianMixture2) : MixtureRelabelEquiv F F :=
  identity rfl rfl rfl rfl rfl rfl

end MixtureRelabelEquiv

end Workspace.Types.MixtureRelabelEquiv
