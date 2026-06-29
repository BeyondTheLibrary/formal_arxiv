import Mathlib
import Workspace.Types.BoolMat
import Workspace.Types.Interlace
import Workspace.Types.Extract
import Workspace.Types.Equipartition

namespace Workspace.Types.Bracket

open Workspace.Types.BoolMat
open Workspace.Types.Interlace
open Workspace.Types.Extract
open Workspace.Types.Equipartition

/-- The bracket notation `[M]_{p,x,y}` (Definition 4.1).

Given an `m × n` matrix `M`, a positive integer `p`, and reals `0 < x, y ≤ 1`,
set `T = ⌈m · x⌉`.  Then `[M]_{p,x,y}` is the **set** of all matrices
`ε(⟨M⟩^p, R, C)` (i.e. `extract (interlace M p) R C`) where:

* `R ⊆ [0, m·p)` is `m, T, p`-equipartitioned — each of the `p` consecutive
  blocks `[m·γ, m·(γ+1))` contains exactly `⌈m·x⌉` elements of `R`; and
* `C ⊆ [0, n^p)` with `|C| = ⌈n^p · y⌉`, where `n^p` is the column count of
  the interlaced matrix `⟨M⟩^p`.

The real target `(M.m : ℝ) * x` is passed to `IsEquipartitioned`, which
ceilings it internally; since `⌈⌈M.m · x⌉⌉ = ⌈M.m · x⌉` this matches the
paper's integer `T = ⌈m · x⌉`.

The result is a `Set BoolMat`, so the bracket's communication complexity is
measured via the set-complexity `DSet`. -/
def bracket (M : BoolMat) (p : ℕ) (x y : ℝ) : Set BoolMat :=
  { g | ∃ (R C : Finset ℕ),
      R ⊆ Finset.range (M.m * p) ∧
      IsEquipartitioned R M.m ((M.m : ℝ) * x) p ∧
      C ⊆ Finset.range (M.n ^ p) ∧
      C.card = ⌈((M.n ^ p : ℕ) : ℝ) * y⌉₊ ∧
      g = extract (interlace M p) R C }

end Workspace.Types.Bracket
