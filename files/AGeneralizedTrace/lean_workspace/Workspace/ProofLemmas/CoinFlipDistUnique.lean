import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist

theorem CoinFlipDistUnique :
    ∀ {n : ℕ} (S : Workspace.Types.ProbVec.ProbVec n)
      (cfd cfd' : Workspace.Types.CoinFlipDist.CoinFlipDist n S),
      cfd.toPMF = cfd'.toPMF := by
  intro n S cfd cfd'
  ext b
  rw [cfd.prod_factorisation b]
  rw [cfd'.prod_factorisation b]
