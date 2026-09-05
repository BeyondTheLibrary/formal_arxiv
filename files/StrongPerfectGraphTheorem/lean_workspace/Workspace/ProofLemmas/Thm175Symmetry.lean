import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm175Optimal

/-!
# The `X,Y` symmetry after claim (1) of 17.5

Once claim (1) says that `p₁` is the unique `X`-complete path vertex, reversing
the path and exchanging `X` and `Y` gives another counterexample.  Its
`Y`-complete edge set is empty, since the original `pₙ` was the unique
`Y`-complete path vertex.  All three optimality measures are unchanged.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Symmetry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm175Minimal
open Workspace.ProofLemmas.Thm175Optimal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The reversed counterexample with the two anticonnected sides exchanged.
This is the paper's sentence *"In view of (1), there is symmetry between `X`
and `Y`."* -/
def swapCounterexample
    (G : SimpleGraph V) (z : V) (c : Counterexample G z)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁)) :
    Counterexample G z := by
  classical
  have hpₙmem : c.core.pₙ ∈ c.core.p :=
    PathBasics.getLast_mem c.core.hp.2.2
  have hpₙY : VertexComplete G c.core.pₙ c.Y :=
    (c.core.hYuniq c.core.pₙ hpₙmem).mpr rfl
  have hEmpty : {e : Sym2 V | ∃ u ∈ c.core.p.reverse,
      ∃ v ∈ c.core.p.reverse,
        e = s(u, v) ∧ EdgeComplete G c.Y u v} = ∅ := by
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hE⟩
      have huP : u ∈ c.core.p := List.mem_reverse.mp hu
      have hvP : v ∈ c.core.p := List.mem_reverse.mp hv
      have hueq : u = c.core.pₙ :=
        (c.core.hYuniq u huP).mp hE.2.1
      have hveq : v = c.core.pₙ :=
        (c.core.hYuniq v hvP).mp hE.2.2
      rw [hueq, hveq] at hE
      exact (G.irrefl hE.1).elim
    · simp
  have hEven : Even {e : Sym2 V | ∃ u ∈ c.core.p.reverse,
      ∃ v ∈ c.core.p.reverse,
        e = s(u, v) ∧ EdgeComplete G c.Y u v}.ncard := by
    rw [hEmpty]
    simp
  exact
    { X := c.Y
      Y := c.X
      core :=
        { p := c.core.p.reverse
          p₁ := c.core.pₙ
          pₙ := c.core.p₁
          hp := PathBasics.isPathFrom_reverse c.core.hp
          hodd := by
            rw [PathBasics.pathLength_reverse]
            exact c.core.hodd
          hlong := by
            rw [PathBasics.pathLength_reverse]
            exact c.core.hlong
          houtX := fun w hw => c.core.houtY w (List.mem_reverse.mp hw)
          houtY := fun w hw => c.core.houtX w (List.mem_reverse.mp hw)
          hp₁X := hpₙY
          hYuniq := fun w hw => hfirst w (List.mem_reverse.mp hw)
          hzP := fun hw => c.core.hzP (List.mem_reverse.mp hw)
          hzanti := fun w hw => c.core.hzanti w (List.mem_reverse.mp hw)
          heven := hEven }
      hXa := c.hYa
      hYa := c.hXa
      hXYa := by simpa [Set.union_comm] using c.hXYa
      hz := by simpa [Set.union_comm] using c.hz
      hzXY := by simpa [Set.union_comm] using c.hzXY }

/-- Reversal and exchanging the two sides preserve the three optimality
measures. -/
theorem swap_isOptimal
    (G : SimpleGraph V) (z : V) (c : Counterexample G z)
    (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p,
      (VertexComplete G w c.X ↔ w = c.core.p₁)) :
    IsOptimal (swapCounterexample G z c hfirst) := by
  classical
  have hlen : (swapCounterexample G z c hfirst).core.p.length =
      c.core.p.length := by
    simp [swapCounterexample]
  have hunion : ((swapCounterexample G z c hfirst).X ∪
      (swapCounterexample G z c hfirst).Y).ncard =
      (c.X ∪ c.Y).ncard := by
    simp [swapCounterexample, Set.union_comm]
  have htotal : (swapCounterexample G z c hfirst).X.ncard +
      (swapCounterexample G z c hfirst).Y.ncard =
      c.X.ncard + c.Y.ncard := by
    simp [swapCounterexample, Nat.add_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    apply hopt.1 d
    omega
  · intro d hd hdu
    apply hopt.2.1 d
    · omega
    · omega
  · intro d hd hdu hdt
    apply hopt.2.2 d
    · omega
    · omega
    · omega

end Workspace.ProofLemmas.Thm175Symmetry
