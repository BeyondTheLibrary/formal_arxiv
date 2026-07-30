import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.ProofLemmas.FrobRepExistsMaxUnramified

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 800000

/-- **Existence of a Frobenius representative at a finite prime.** For every number field `F` and
every prime `v : Ideal (𝓞 F)` with `v ≠ ⊥` and `v.IsPrime`, there exists `σ : galUr 3 F` that is a
Frobenius representative at `v` (`IsFrobeniusRepAt 3 F σ v`): a compatible system of Frobenii
restricting to a Frobenius element on every finite Galois layer of `F^{ur,3}/F`. Unconditional in
`v` (every finite layer is everywhere unramified over `F`). -/
theorem SublemmaFrobRepExists
    (F : Type*) [Field F] [NumberField F]
    (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime) :
    ∃ σ : galUr 3 F, IsFrobeniusRepAt 3 F σ v :=
  FrobRepExistsMaxUnramified F v hv hvp
