import Mathlib
import Workspace.Types.ProbVec

theorem PrefixSuffixMarginalsToOne :
    ∀ {n k : ℕ} (S : Workspace.Types.ProbVec.ProbVec n)
      (offset : Fin k → Fin n),
      (∑ μ : Fin k → Bool,
        ∏ i : Fin k,
          (if μ i then S.p (offset i) else 1 - S.p (offset i))) = 1 := by
  intro n k S offset
  -- Define f i b explicitly so the unifier can spot the pattern
  set f : Fin k → Bool → ℝ := fun i b => if b then S.p (offset i) else 1 - S.p (offset i) with hf
  show (∑ μ : Fin k → Bool, ∏ i : Fin k, f i (μ i)) = 1
  -- Convert sum over functions to sum over piFinset (defeq)
  have h1 : (∑ μ : Fin k → Bool, ∏ i : Fin k, f i (μ i))
      = ∑ x ∈ Fintype.piFinset (fun (_ : Fin k) => (Finset.univ : Finset Bool)),
          ∏ i : Fin k, f i (x i) := rfl
  rw [h1, ← Finset.prod_univ_sum]
  simp [hf]
