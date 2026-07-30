import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.SublemmaSplitDescendsEFOne
import Workspace.ProofLemmas.SublemmaSplitDescendsCount

open scoped NumberField
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

theorem SublemmaCompleteSplittingDescends
    (N Lp : Type*) [Field N] [NumberField N] [Field Lp] [NumberField Lp]
    [Algebra ℚ Lp] [Algebra Lp N] [Algebra ℚ N] [IsScalarTower ℚ Lp N]
    [FiniteDimensional Lp N] (q : ℕ) :
    SplitsCompletelyRat q N → SplitsCompletelyRat q Lp := by
  intro hsplitN
  have hqP : q.Prime := hsplitN.1
  have hef : ∀ 𝔭 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp),
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1 :=
    fun 𝔭 h𝔭 => SublemmaSplitDescendsEFOne N Lp q hsplitN 𝔭 h𝔭
  exact ⟨hqP, SublemmaSplitDescendsCount Lp q hqP hef, hef⟩
