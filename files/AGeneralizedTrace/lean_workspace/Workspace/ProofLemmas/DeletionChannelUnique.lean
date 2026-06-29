import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.DelProb
import Workspace.Types.DeletionChannel

theorem DeletionChannelUnique :
    ∀ {n : ℕ} (b : Workspace.Types.BinVec.BinVec n) (δ : Workspace.Types.DelProb.DelProb)
      (dc dc' : Workspace.Types.DeletionChannel.DeletionChannel n b δ),
      dc.toPMF = dc'.toPMF := by
  intro n b δ dc dc'
  ext τ
  rw [dc.pmf_eq_keep_set_sum τ, dc'.pmf_eq_keep_set_sum τ]
