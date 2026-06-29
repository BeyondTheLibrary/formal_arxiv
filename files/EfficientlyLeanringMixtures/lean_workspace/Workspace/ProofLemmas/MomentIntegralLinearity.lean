import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.MixtureRawMoments
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian

set_option maxHeartbeats 800000

open MeasureTheory

/-- Helper: For a signed Gaussian combination and any `i : ℕ`, the function
`x ↦ x^i * S.density x` is integrable. Proof is by induction on `S.components`. -/
private lemma integrable_xpow_signed_density
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination) (i : ℕ) :
    Integrable (fun x : ℝ => x ^ i * S.density x) volume := by
  -- Rewrite using density_eq: S.density x = (S.components.map (fun p => p.1 * p.2.density x)).sum
  have h_rewrite : (fun x : ℝ => x ^ i * S.density x)
      = (fun x : ℝ => (S.components.map (fun p => x ^ i * (p.1 * p.2.density x))).sum) := by
    funext x
    rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq]
    -- Goal: x^i * (L.map (fun p => p.1 * p.2.density x)).sum = (L.map (fun p => x^i * (p.1 * p.2.density x))).sum
    induction S.components with
    | nil => simp
    | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih]
  rw [h_rewrite]
  -- Now show integrability by induction on the list.
  induction S.components with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons]
    apply Integrable.add
    · -- Integrable x ↦ x^i * (p.1 * p.2.density x) = p.1 * (x^i * p.2.density x)
      have h_eq : (fun x : ℝ => x ^ i * (p.1 * p.2.density x))
          = (fun x : ℝ => p.1 * (x ^ i * p.2.density x)) := by
        funext x; ring
      rw [h_eq]
      exact (Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian p.2 i).const_mul p.1
    · exact ih

theorem MomentIntegralLinearity
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (ε : ℝ)
    (hε_pos : 0 < ε)
    (hε_le : ε ≤ 2 ^ ((1 : ℝ) / 12))
    (hS_len : S.components.length ≤ 4)
    (hS_bounds : ∀ p ∈ S.components,
        |p.fst| ≤ 1 ∧ |p.snd.mean| ≤ 1 / ε
        ∧ ε ^ 12 ≤ p.snd.varSq ∧ p.snd.varSq ≤ 2)
    (cs : Fin 7 → ℝ) :
    (∫ x : ℝ, (Finset.univ : Finset (Fin 7)).sum (fun i => cs i * x ^ (i : ℕ))
                * S.density x ∂MeasureTheory.volume)
      = (Finset.univ : Finset (Fin 7)).sum (fun i =>
          cs i * Workspace.Types.MixtureRawMoments.rawMoment_ofSigned S (i : ℕ)) := by
  -- Step 1: Distribute the sum
  have h_pointwise : ∀ x : ℝ,
      (Finset.univ : Finset (Fin 7)).sum (fun i => cs i * x ^ (i : ℕ)) * S.density x
        = (Finset.univ : Finset (Fin 7)).sum
            (fun i => cs i * (x ^ (i : ℕ) * S.density x)) := by
    intro x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h_eq : (fun x : ℝ =>
        (Finset.univ : Finset (Fin 7)).sum (fun i => cs i * x ^ (i : ℕ)) * S.density x)
      = (fun x : ℝ =>
          (Finset.univ : Finset (Fin 7)).sum
            (fun i => cs i * (x ^ (i : ℕ) * S.density x))) := by
    funext x
    exact h_pointwise x
  rw [show (∫ x : ℝ,
        (Finset.univ : Finset (Fin 7)).sum (fun i => cs i * x ^ (i : ℕ)) * S.density x
          ∂MeasureTheory.volume)
      = ∫ x : ℝ,
          (Finset.univ : Finset (Fin 7)).sum
            (fun i => cs i * (x ^ (i : ℕ) * S.density x)) ∂MeasureTheory.volume from by
    rw [h_eq]]
  -- Step 2: Integrability of each summand
  have h_int : ∀ i ∈ (Finset.univ : Finset (Fin 7)),
      Integrable (fun x : ℝ => cs i * (x ^ (i : ℕ) * S.density x)) volume := by
    intro i _
    exact (integrable_xpow_signed_density S (i : ℕ)).const_mul (cs i)
  -- Step 3: Pull out the sum
  rw [MeasureTheory.integral_finset_sum _ h_int]
  -- Step 4: Pull out cs i from each integral
  apply Finset.sum_congr rfl
  intro i _
  rw [MeasureTheory.integral_const_mul]
  -- Step 5: Recognize rawMoment_ofSigned
  rfl
