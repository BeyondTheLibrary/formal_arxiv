import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.SublemmaSGCDensityIsAnalytic

namespace Workspace.ProofLemmas

theorem SublemmaSignedGaussianDensityZerosFinite
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (h_nonzero_fn : ∃ x : ℝ, S.density x ≠ 0)
    (a b : ℝ) :
    Set.Finite ({x ∈ Set.Icc a b | S.density x = 0}) := by
  -- Step 1: S.density is analytic on ℝ
  have hAn : AnalyticOnNhd ℝ S.density Set.univ := SublemmaSGCDensityIsAnalytic S
  -- Step 2: from non-triviality, get codiscrete-ness of non-zero set
  obtain ⟨x₀, hx₀⟩ := h_nonzero_fn
  have hCodisc : S.density ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℝ :=
    hAn.preimage_zero_mem_codiscrete hx₀
  -- Step 3: the zero set is closed and has discrete topology
  have hPre : (S.density ⁻¹' {0})ᶜ = S.density ⁻¹' {0}ᶜ := by
    ext x; simp
  have hCodisc' : (S.density ⁻¹' {0})ᶜ ∈ Filter.codiscrete ℝ := by
    rw [hPre]; exact hCodisc
  have hClosedDiscrete : IsClosed (S.density ⁻¹' {0}) ∧
      DiscreteTopology (S.density ⁻¹' {0} : Set ℝ) := by
    rw [← compl_mem_codiscrete_iff]; exact hCodisc'
  obtain ⟨hClosed, hDisc⟩ := hClosedDiscrete
  -- Step 4: rewrite our set as Icc a b ∩ S.density ⁻¹' {0}
  have hSetEq : {x ∈ Set.Icc a b | S.density x = 0} =
      Set.Icc a b ∩ S.density ⁻¹' {0} := by
    ext x; simp [Set.mem_preimage]
  rw [hSetEq]
  -- Step 5: this set is closed (intersection of two closed sets)
  have hIntClosed : IsClosed (Set.Icc a b ∩ S.density ⁻¹' {0}) :=
    isClosed_Icc.inter hClosed
  -- Step 6: this set is compact (closed subset of a compact set Icc a b)
  have hIccCompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have hCompact : IsCompact (Set.Icc a b ∩ S.density ⁻¹' {0}) :=
    hIccCompact.of_isClosed_subset hIntClosed Set.inter_subset_left
  -- Step 7: this set has discrete topology (subset of discrete-topology set)
  have hSubsetDisc : DiscreteTopology
      (↥(Set.Icc a b ∩ S.density ⁻¹' {0}) : Type) := by
    have hSubset : Set.Icc a b ∩ S.density ⁻¹' {0} ⊆ S.density ⁻¹' {0} :=
      Set.inter_subset_right
    exact DiscreteTopology.of_subset hDisc hSubset
  -- Step 8: compact + discrete → finite
  have hIsDisc : IsDiscrete (Set.Icc a b ∩ S.density ⁻¹' {0}) :=
    isDiscrete_iff_discreteTopology.mpr hSubsetDisc
  exact hCompact.finite hIsDisc

end Workspace.ProofLemmas
