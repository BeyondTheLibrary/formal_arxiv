import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

theorem SublemmaSGCDensityIsAnalytic
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination) :
    AnalyticOnNhd ℝ S.density Set.univ := by
  rw [SignedGaussianCombination.density_def]
  induction S.components with
  | nil =>
    simp
    exact analyticOnNhd_const
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    refine AnalyticOnNhd.add ?_ ih
    refine analyticOnNhd_const.mul ?_
    rw [GaussianPDF.density_def]
    refine analyticOnNhd_const.mul ?_
    refine analyticOnNhd_rexp.comp ?_ (fun _ _ => Set.mem_univ _)
    apply AnalyticOnNhd.div_const
    apply AnalyticOnNhd.neg
    apply AnalyticOnNhd.pow
    exact analyticOnNhd_id.sub analyticOnNhd_const

end Workspace.ProofLemmas
