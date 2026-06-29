import Mathlib
import Workspace.Types.GaussianMixture2
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 400000

namespace Workspace.Types.EpsilonStandardPair

open Workspace.Types.GaussianMixture2
open Workspace.Types.GaussianPDF

/--
Definition 1 of Moitra--Valiant ("ε-standard pair"):
two `GaussianMixture2` distributions `F, F'` are an `ε`-standard pair iff
the following four conditions all hold.

(i)  **Weights bounded below by ε.** Each of the four mixing weights is `≥ ε`.

(ii) **Variances bounded above by 1, means bounded by `1/ε` in absolute value.**
     Every variance is `≤ 1`, and every mean lies in `[-1/ε, 1/ε]`.

(iii) **Intra-mixture separation.** Within each of `F` and `F'`, the two
     components are separated by at least `ε` in the `|μ₁-μ₂| + |σ₁²-σ₂²|`
     pseudo-distance.

(iv) **Inter-mixture separation under both permutations.** The two mixtures
     are at distance ≥ `ε` from each other in the per-component
     `|w-w'| + |μ-μ'| + |σ²-σ'²|` metric, where the inter-mixture distance
     is taken as the minimum over the two permutations of `{1,2}` (so the
     definition is symmetric under relabelling).

The positivity hypothesis `ε > 0` is intentionally **not** included in the
predicate: downstream lemmas that need it may take it separately as a
hypothesis (as in the paper's surrounding context).
-/
structure EpsilonStandardPair
    (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ) : Prop where
  /-- Condition (i): each of the four mixing weights is at least `ε`. -/
  weights_bounded :
    ε ≤ F.weight1 ∧ ε ≤ F.weight2 ∧ ε ≤ F'.weight1 ∧ ε ≤ F'.weight2
  /-- Condition (ii): each variance is at most `1`, and each mean is bounded
  by `1/ε` in absolute value. -/
  means_and_vars_bounded :
    (F.comp1.varSq ≤ 1 ∧ F.comp2.varSq ≤ 1
      ∧ F'.comp1.varSq ≤ 1 ∧ F'.comp2.varSq ≤ 1)
    ∧ (|F.comp1.mean| ≤ 1 / ε ∧ |F.comp2.mean| ≤ 1 / ε
        ∧ |F'.comp1.mean| ≤ 1 / ε ∧ |F'.comp2.mean| ≤ 1 / ε)
  /-- Condition (iii): within `F` and within `F'`, the two components are
  separated by at least `ε` in the `|μ₁-μ₂| + |σ₁²-σ₂²|` pseudo-distance. -/
  intra_separation :
    (|F.comp1.mean - F.comp2.mean| + |F.comp1.varSq - F.comp2.varSq| ≥ ε)
    ∧ (|F'.comp1.mean - F'.comp2.mean| + |F'.comp1.varSq - F'.comp2.varSq| ≥ ε)
  /-- Condition (iv): the two mixtures are at distance ≥ `ε` from each other,
  where the inter-mixture distance is the minimum over the two ways of
  pairing up components (identity permutation vs. swap). -/
  inter_separation :
    ε ≤ min
          (((|F.weight1 - F'.weight1| + |F.comp1.mean - F'.comp1.mean|
              + |F.comp1.varSq - F'.comp1.varSq|)
            + (|F.weight2 - F'.weight2| + |F.comp2.mean - F'.comp2.mean|
                + |F.comp2.varSq - F'.comp2.varSq|)))
          (((|F.weight1 - F'.weight2| + |F.comp1.mean - F'.comp2.mean|
              + |F.comp1.varSq - F'.comp2.varSq|)
            + (|F.weight2 - F'.weight1| + |F.comp2.mean - F'.comp1.mean|
                + |F.comp2.varSq - F'.comp1.varSq|)))

namespace EpsilonStandardPair

variable {F F' : Workspace.Types.GaussianMixture2.GaussianMixture2} {ε : ℝ}

/-! ### Destructor helpers — extract individual sub-conditions

These one-line projections make it easy for downstream proofs to extract any
of the four conditions (or their atomic sub-parts) without manually
destructuring the conjunctions inside each field. -/

/-- `ε ≤ F.weight1`. -/
theorem eps_le_weight1_F (h : EpsilonStandardPair F F' ε) : ε ≤ F.weight1 :=
  h.weights_bounded.1

/-- `ε ≤ F.weight2`. -/
theorem eps_le_weight2_F (h : EpsilonStandardPair F F' ε) : ε ≤ F.weight2 :=
  h.weights_bounded.2.1

/-- `ε ≤ F'.weight1`. -/
theorem eps_le_weight1_F' (h : EpsilonStandardPair F F' ε) : ε ≤ F'.weight1 :=
  h.weights_bounded.2.2.1

/-- `ε ≤ F'.weight2`. -/
theorem eps_le_weight2_F' (h : EpsilonStandardPair F F' ε) : ε ≤ F'.weight2 :=
  h.weights_bounded.2.2.2

/-- `F.comp1.varSq ≤ 1`. -/
theorem varSq_le_one_F_comp1 (h : EpsilonStandardPair F F' ε) : F.comp1.varSq ≤ 1 :=
  h.means_and_vars_bounded.1.1

/-- `F.comp2.varSq ≤ 1`. -/
theorem varSq_le_one_F_comp2 (h : EpsilonStandardPair F F' ε) : F.comp2.varSq ≤ 1 :=
  h.means_and_vars_bounded.1.2.1

/-- `F'.comp1.varSq ≤ 1`. -/
theorem varSq_le_one_F'_comp1 (h : EpsilonStandardPair F F' ε) : F'.comp1.varSq ≤ 1 :=
  h.means_and_vars_bounded.1.2.2.1

/-- `F'.comp2.varSq ≤ 1`. -/
theorem varSq_le_one_F'_comp2 (h : EpsilonStandardPair F F' ε) : F'.comp2.varSq ≤ 1 :=
  h.means_and_vars_bounded.1.2.2.2

/-- `|F.comp1.mean| ≤ 1/ε`. -/
theorem abs_mean_le_F_comp1 (h : EpsilonStandardPair F F' ε) : |F.comp1.mean| ≤ 1 / ε :=
  h.means_and_vars_bounded.2.1

/-- `|F.comp2.mean| ≤ 1/ε`. -/
theorem abs_mean_le_F_comp2 (h : EpsilonStandardPair F F' ε) : |F.comp2.mean| ≤ 1 / ε :=
  h.means_and_vars_bounded.2.2.1

/-- `|F'.comp1.mean| ≤ 1/ε`. -/
theorem abs_mean_le_F'_comp1 (h : EpsilonStandardPair F F' ε) : |F'.comp1.mean| ≤ 1 / ε :=
  h.means_and_vars_bounded.2.2.2.1

/-- `|F'.comp2.mean| ≤ 1/ε`. -/
theorem abs_mean_le_F'_comp2 (h : EpsilonStandardPair F F' ε) : |F'.comp2.mean| ≤ 1 / ε :=
  h.means_and_vars_bounded.2.2.2.2

/-- Intra-mixture separation for `F`. -/
theorem intra_sep_F (h : EpsilonStandardPair F F' ε) :
    |F.comp1.mean - F.comp2.mean| + |F.comp1.varSq - F.comp2.varSq| ≥ ε :=
  h.intra_separation.1

/-- Intra-mixture separation for `F'`. -/
theorem intra_sep_F' (h : EpsilonStandardPair F F' ε) :
    |F'.comp1.mean - F'.comp2.mean| + |F'.comp1.varSq - F'.comp2.varSq| ≥ ε :=
  h.intra_separation.2

/-- Inter-mixture separation under the identity permutation
(component 1 ↔ component 1, component 2 ↔ component 2). -/
theorem inter_sep_id (h : EpsilonStandardPair F F' ε) :
    ε ≤ ((|F.weight1 - F'.weight1| + |F.comp1.mean - F'.comp1.mean|
            + |F.comp1.varSq - F'.comp1.varSq|)
          + (|F.weight2 - F'.weight2| + |F.comp2.mean - F'.comp2.mean|
              + |F.comp2.varSq - F'.comp2.varSq|)) :=
  le_trans h.inter_separation (min_le_left _ _)

/-- Inter-mixture separation under the swap permutation
(component 1 ↔ component 2, component 2 ↔ component 1). -/
theorem inter_sep_swap (h : EpsilonStandardPair F F' ε) :
    ε ≤ ((|F.weight1 - F'.weight2| + |F.comp1.mean - F'.comp2.mean|
            + |F.comp1.varSq - F'.comp2.varSq|)
          + (|F.weight2 - F'.weight1| + |F.comp2.mean - F'.comp1.mean|
              + |F.comp2.varSq - F'.comp1.varSq|)) :=
  le_trans h.inter_separation (min_le_right _ _)

/-! ### Constructor helper

A convenient way to build an `EpsilonStandardPair` from the four named
conditions (mirroring the structure's `mk`, but with a public name that
documents intent). -/

/-- Bundle the four conditions of Definition 1 into an `EpsilonStandardPair`. -/
theorem mk'
    (hW : ε ≤ F.weight1 ∧ ε ≤ F.weight2 ∧ ε ≤ F'.weight1 ∧ ε ≤ F'.weight2)
    (hMV :
      (F.comp1.varSq ≤ 1 ∧ F.comp2.varSq ≤ 1
        ∧ F'.comp1.varSq ≤ 1 ∧ F'.comp2.varSq ≤ 1)
      ∧ (|F.comp1.mean| ≤ 1 / ε ∧ |F.comp2.mean| ≤ 1 / ε
          ∧ |F'.comp1.mean| ≤ 1 / ε ∧ |F'.comp2.mean| ≤ 1 / ε))
    (hIntra :
      (|F.comp1.mean - F.comp2.mean| + |F.comp1.varSq - F.comp2.varSq| ≥ ε)
      ∧ (|F'.comp1.mean - F'.comp2.mean|
          + |F'.comp1.varSq - F'.comp2.varSq| ≥ ε))
    (hInter :
      ε ≤ min
            (((|F.weight1 - F'.weight1| + |F.comp1.mean - F'.comp1.mean|
                + |F.comp1.varSq - F'.comp1.varSq|)
              + (|F.weight2 - F'.weight2| + |F.comp2.mean - F'.comp2.mean|
                  + |F.comp2.varSq - F'.comp2.varSq|)))
            (((|F.weight1 - F'.weight2| + |F.comp1.mean - F'.comp2.mean|
                + |F.comp1.varSq - F'.comp2.varSq|)
              + (|F.weight2 - F'.weight1| + |F.comp2.mean - F'.comp1.mean|
                  + |F.comp2.varSq - F'.comp1.varSq|)))) :
    EpsilonStandardPair F F' ε :=
  { weights_bounded := hW
    means_and_vars_bounded := hMV
    intra_separation := hIntra
    inter_separation := hInter }

end EpsilonStandardPair

end Workspace.Types.EpsilonStandardPair
