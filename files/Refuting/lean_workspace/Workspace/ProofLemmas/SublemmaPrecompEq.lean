import Mathlib
import Workspace.Types.Protocol
import Workspace.Types.CommComplexity
import Workspace.ProofLemmas.SublemmaPrecompNoIncrease
import Workspace.ProofLemmas.SublemmaSurjRestrictGE

namespace Workspace.ProofLemmas

open Workspace.Types.CommComplexity

theorem SublemmaPrecompEq {A B A' B' Z : Type*} [Fintype A] [Fintype B]
    [Fintype A'] [Fintype B'] (g : A → B → Z) (α : A' → A) (β : B' → B)
    (hα : Function.Surjective α) (hβ : Function.Surjective β) :
    D (fun u v => g (α u) (β v)) = D g := by
  exact le_antisymm (Workspace.ProofLemmas.SublemmaPrecompNoIncrease g α β)
    (Workspace.ProofLemmas.SublemmaSurjRestrictGE g α β hα hβ)

end Workspace.ProofLemmas
