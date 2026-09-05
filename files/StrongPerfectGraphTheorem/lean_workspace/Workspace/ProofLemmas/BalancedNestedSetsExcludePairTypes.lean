import Workspace.Types.Core
import Workspace.Types.SkewTools

set_option autoImplicit false

namespace Workspace.Types.BalancedNestedSetsExcludePairTypes

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.SkewTools.SPGT

theorem balancedNestedSetsExcludePairTypes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B L Y A₁ B₁ : Set V)
    (hbalanced : Balanced G L Y) (hA₁ : A₁ ⊆ L) (hB₁ : B₁ ⊆ Y) :
    ¬ IsPathPair G A B A₁ B₁ ∧ ¬ IsAntipathPair G A B A₁ B₁ := by
  constructor
  · intro hpair
    rcases hpair.2.2.2 with ⟨p, u, v, hu, hv, huv, hp, hint, hodd⟩
    exact hbalanced.1 u v p (hB₁ hu) (hB₁ hv) huv hp
      (fun x hx => hA₁ (hint x hx)) hodd
  · intro hpair
    rcases hpair.2.2.2 with ⟨p, u, v, hu, hv, huv, hp, hint, hodd⟩
    exact hbalanced.2 u v p (hA₁ hu) (hA₁ hv) huv hp
      (fun x hx => hB₁ (hint x hx)) hodd

end Workspace.Types.BalancedNestedSetsExcludePairTypes
