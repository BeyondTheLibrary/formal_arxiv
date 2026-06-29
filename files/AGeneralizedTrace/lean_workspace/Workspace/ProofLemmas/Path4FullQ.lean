import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.QFactorBounds
import Workspace.ProofLemmas.CentralBinomialUpperTailWide

/-!
# Path4FullQ — fixed-range residual product `Q_full`

The paper's fixed-range residual product over a full range of binomial indices.
We define the even-index and odd-index versions `fullQeven` / `fullQodd`,
prove they lie in `[0, 1]` (each factor `1 - α·binPMF n (1/2) j ∈ [0,1]` since
`α·binPMF n (1/2) j ≤ 1`), and prove that for odd `n` the even and odd versions
are equal (binomial symmetry `j ↦ n - j` flips parity and preserves the factor).
-/

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression

namespace Workspace.ProofLemmas.Path4FullQ

/-- Fixed-range residual product over even indices in `{0, …, n}`. -/
noncomputable def fullQeven (n : ℕ) (α : ℝ) : ℝ :=
  ∏ j ∈ (Finset.range (n+1)).filter (fun j => j % 2 = 0),
    (1 - α * Workspace.Types.AlternatingSumExpression.binPMF n (1/2) j)

/-- Fixed-range residual product over odd indices in `{0, …, n}`. -/
noncomputable def fullQodd (n : ℕ) (α : ℝ) : ℝ :=
  ∏ j ∈ (Finset.range (n+1)).filter (fun j => j % 2 = 1),
    (1 - α * Workspace.Types.AlternatingSumExpression.binPMF n (1/2) j)

/-- For `j ≤ n`, `binPMF n (1/2) j = C(n,j) · (2^n)⁻¹`. -/
lemma binPMF_half_eq_choose (n j : ℕ) (hj : j ≤ n) :
    binPMF n (1/2 : ℝ) j = (Nat.choose n j : ℝ) * (2 ^ n : ℝ)⁻¹ := by
  rw [CentralBinomialLowerTailWideProof.binPMF_half_eq n j hj]
  congr 1
  rw [one_div, inv_pow]

/-- Each factor of `fullQeven`/`fullQodd` rewrites to the `Q_mem_unitInterval` shape
on `Finset.range (n+1)`. -/
lemma factor_eq_on_range (n : ℕ) (α : ℝ) (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
    (1 - α * binPMF n (1/2 : ℝ) j)
      = (1 - α * ((Nat.choose n j : ℝ) * (2 ^ n : ℝ)⁻¹)) := by
  have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [binPMF_half_eq_choose n j hjle]

/-- **`Q_full ∈ [0,1]`** for the even-index product. -/
lemma full_Q_le_one_even (n : ℕ) (hn1 : 1 ≤ n)
    (α : ℝ)
    (hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) :
    0 ≤ fullQeven n α ∧ fullQeven n α ≤ 1 := by
  unfold fullQeven
  have hrw : (∏ j ∈ (Finset.range (n+1)).filter (fun j => j % 2 = 0),
        (1 - α * binPMF n (1/2 : ℝ) j))
      = ∏ j ∈ (Finset.range (n+1)).filter (fun j => j % 2 = 0),
        (1 - α * ((Nat.choose n j : ℝ) * (2 ^ n : ℝ)⁻¹)) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact factor_eq_on_range n α j (Finset.mem_of_mem_filter j hj)
  rw [hrw]
  exact Workspace.ProofLemmas.QFactorBounds.Q_mem_unitInterval hn1 α hα
    ((Finset.range (n+1)).filter (fun j => j % 2 = 0)) id

/-- **`Q_full ∈ [0,1]`** for the odd-index product. -/
lemma full_Q_le_one_odd (n : ℕ) (hn1 : 1 ≤ n)
    (α : ℝ)
    (hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) :
    0 ≤ fullQodd n α ∧ fullQodd n α ≤ 1 := by
  unfold fullQodd
  have hrw : (∏ j ∈ (Finset.range (n+1)).filter (fun j => j % 2 = 1),
        (1 - α * binPMF n (1/2 : ℝ) j))
      = ∏ j ∈ (Finset.range (n+1)).filter (fun j => j % 2 = 1),
        (1 - α * ((Nat.choose n j : ℝ) * (2 ^ n : ℝ)⁻¹)) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact factor_eq_on_range n α j (Finset.mem_of_mem_filter j hj)
  rw [hrw]
  exact Workspace.ProofLemmas.QFactorBounds.Q_mem_unitInterval hn1 α hα
    ((Finset.range (n+1)).filter (fun j => j % 2 = 1)) id

/-- Combined `[0,1]` membership for both versions. -/
lemma full_Q_le_one (n : ℕ) (hn1 : 1 ≤ n)
    (α : ℝ)
    (hα : α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) :
    (0 ≤ fullQeven n α ∧ fullQeven n α ≤ 1) ∧
      (0 ≤ fullQodd n α ∧ fullQodd n α ≤ 1) :=
  ⟨full_Q_le_one_even n hn1 α hα, full_Q_le_one_odd n hn1 α hα⟩

/-- `binPMF n (1/2) j = binPMF n (1/2) (n - j)` for `j ≤ n` (binomial symmetry). -/
lemma binPMF_half_symm (n j : ℕ) (hj : j ≤ n) :
    binPMF n (1/2 : ℝ) j = binPMF n (1/2 : ℝ) (n - j) :=
  CentralBinomialUpperTailWideProof.binPMF_half_symm n j hj

/-- **Even = Odd for odd `n`.** The reflection `j ↦ n - j` bijects the even-index
set onto the odd-index set (parity flips since `n` is odd) and preserves each
factor (binomial symmetry). -/
lemma full_Q_even_eq_odd (n : ℕ) (hn : n % 2 = 1) (α : ℝ) :
    fullQeven n α = fullQodd n α := by
  unfold fullQeven fullQodd
  apply Finset.prod_nbij' (fun j => n - j) (fun j => n - j)
  · -- maps even set into odd set
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hjr, hje⟩ := hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjr
    refine ⟨by omega, ?_⟩
    omega
  · -- maps odd set into even set
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hjr, hjo⟩ := hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjr
    refine ⟨by omega, ?_⟩
    omega
  · -- left inverse
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjr, _⟩ := hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjr
    omega
  · -- right inverse
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjr, _⟩ := hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjr
    omega
  · -- factor preserved
    intro j hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjr, _⟩ := hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp hjr
    rw [binPMF_half_symm n j hjle]

end Workspace.ProofLemmas.Path4FullQ
