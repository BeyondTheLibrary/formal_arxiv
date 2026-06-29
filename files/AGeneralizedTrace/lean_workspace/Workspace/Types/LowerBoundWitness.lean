import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.TraceDist
import Workspace.Types.LInfDistance
import Workspace.Types.L1Distance
import Workspace.Types.TVDistance
import Workspace.Types.LowerBoundConstants
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.DeletionChannel

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.TraceDist
open Workspace.Types.LInfDistance
open Workspace.Types.L1Distance
open Workspace.Types.TVDistance
open Workspace.Types.LowerBoundConstants

namespace Workspace.Types.LowerBoundWitness

/--
A `LowerBoundWitness C n` is a pair of probability strings `S, S' : ProbVec n`
that together certify the lower-bound conclusion of the main theorem for a
fixed constant bundle `C : LowerBoundConstants` and a length `n : ℕ`
(with `n ≥ C.n0` provided as a field).

It bundles:

* `S`, `S'` — two length-`n` probability vectors.
* `n_ge_n0` — the threshold condition `C.n0 ≤ n`.
* `linf_sep` — a `c_inf` lower bound on the ℓ∞ separation of `S` and `S'`.
* `l1_lb`, `l1_ub` — the two-sided `[c_1 √n, C_1 √n]` bound on the ℓ¹
  distance of `S` and `S'`.
* `tv_decay` — for every deletion probability `δ` with
  `C.cDelta / √n ≤ δ.val`, and every pair of trace distributions
  `td1 : TraceDist n S δ`, `td2 : TraceDist n S' δ`, the total-variation
  distance between their underlying PMFs is at most `exp(-C.cTv · √n)`.
-/
structure LowerBoundWitness (C : Workspace.Types.LowerBoundConstants.LowerBoundConstants)
    (n : ℕ) where
  /-- The first probability string. -/
  S : Workspace.Types.ProbVec.ProbVec n
  /-- The second probability string. -/
  S' : Workspace.Types.ProbVec.ProbVec n
  /-- The length `n` is at least the threshold `C.n0`. -/
  n_ge_n0 : C.n0 ≤ n
  /-- ℓ∞ separation lower bound: `LInfDistance S S' ≥ C.cInf`. -/
  linf_sep :
    C.cInf ≤ Workspace.Types.LInfDistance.LInfDistance S S'
  /-- ℓ¹ lower bound: `c_1 · √n ≤ L1Distance S S'`. -/
  l1_lb :
    C.c1 * Real.sqrt (n : ℝ) ≤ Workspace.Types.L1Distance.L1Distance S S'
  /-- ℓ¹ upper bound: `L1Distance S S' ≤ C_1 · √n`. -/
  l1_ub :
    Workspace.Types.L1Distance.L1Distance S S' ≤ C.cC1 * Real.sqrt (n : ℝ)
  /-- For every `δ` with `C.cDelta / √n ≤ δ.val` and every pair of trace
  distributions on `S`, `S'` with parameter `δ`, the total-variation distance
  between the induced trace PMFs is at most `exp(-C.cTv · √n)`. -/
  tv_decay :
    ∀ (δ : Workspace.Types.DelProb.DelProb),
      C.cDelta / Real.sqrt (n : ℝ) ≤ δ.val →
      ∀ (td1 : Workspace.Types.TraceDist.TraceDist n S δ)
        (td2 : Workspace.Types.TraceDist.TraceDist n S' δ),
        Workspace.Types.TVDistance.TVDistance td1.toPMF td2.toPMF
          ≤ Real.exp (-C.cTv * Real.sqrt (n : ℝ))

end Workspace.Types.LowerBoundWitness
