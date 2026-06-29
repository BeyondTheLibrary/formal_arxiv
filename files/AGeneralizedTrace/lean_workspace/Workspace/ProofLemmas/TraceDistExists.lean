import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.DeletionChannel
import Workspace.Types.TraceDist
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.CoinFlipDistUnique
import Workspace.ProofLemmas.DeletionChannelExists
import Workspace.ProofLemmas.DeletionChannelUnique

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.CoinFlipDist
open Workspace.Types.DeletionChannel
open Workspace.Types.TraceDist

theorem traceDist_exists :
    ∀ {n : ℕ} (S : Workspace.Types.ProbVec.ProbVec n) (δ : Workspace.Types.DelProb.DelProb),
      Nonempty (Workspace.Types.TraceDist.TraceDist n S δ) := by
  intro n S δ
  obtain ⟨cfd₀⟩ := CoinFlipDistExists S
  have dc₀ : ∀ b : BinVec n, DeletionChannel n b δ := fun b => (DeletionChannelExists b δ).some
  refine ⟨{
    toPMF := cfd₀.toPMF.bind (fun b => (dc₀ b).toPMF)
    composition_law := ?_
  }⟩
  intro cfd dc τ
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro b
  rw [CoinFlipDistUnique S cfd₀ cfd, DeletionChannelUnique b δ (dc₀ b) (dc b)]
