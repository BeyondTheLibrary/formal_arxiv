import Mathlib

/-!
# The group `Γ = 𝔽₂³` and its dual `Γ*`

The group `Γ` of the paper: the `3`-dimensional vector space over the two-element field
`𝔽₂ = ZMod 2`, written additively, with `8` elements and characteristic two. `Γ*` is its dual
space of `𝔽₂`-linear maps `Γ → 𝔽₂`. Both are `abbrev`s over standard Mathlib objects
(`Γ := Fin 3 → ZMod 2`, `Γ* := Module.Dual (ZMod 2) Γ`), so Mathlib's linear-algebra API
applies directly; the basic numerical facts are recorded as lemmas.
-/

namespace Workspace.Types.Gamma

/-- The two-element field `𝔽₂`, realised as `ZMod 2`. -/
abbrev F2 : Type := ZMod 2

/-- The group `Γ = 𝔽₂³` of the paper: the `3`-dimensional vector space over the
two-element field, written additively.  It is a reducible abbreviation for
`Fin 3 → ZMod 2`, so all of Mathlib's linear-algebra API applies to it. -/
abbrev Gamma : Type := Fin 3 → F2

/-- The dual space `Γ*` of `Γ`: the `𝔽₂`-vector space of `𝔽₂`-linear maps
`Γ → 𝔽₂`. -/
abbrev GammaDual : Type := Module.Dual F2 Gamma

/-- `Γ*` is a finite type: a linear map is determined by its underlying
function, and there are only finitely many functions `Γ → 𝔽₂`. -/
instance : Finite GammaDual :=
  Finite.of_injective (fun f : GammaDual => (f : Gamma → F2)) DFunLike.coe_injective

namespace Gamma

/-- `Γ` has exactly `8` elements. -/
theorem card_eq : Fintype.card Gamma = 8 := by
  simp [Gamma, F2]

/-- `Γ` has characteristic two: every element is its own additive inverse. -/
theorem add_self (a : Gamma) : a + a = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (a i)

/-- `Γ` is `3`-dimensional over `𝔽₂`. -/
theorem finrank_eq : Module.finrank F2 Gamma = 3 := by
  simp [Gamma, F2]

/-- The dual `Γ*` is `3`-dimensional over `𝔽₂`. -/
theorem finrank_dual_eq : Module.finrank F2 GammaDual = 3 := by
  rw [Subspace.dual_finrank_eq, finrank_eq]

/-- `Γ*` has exactly `8` elements. -/
theorem card_dual_eq : Nat.card GammaDual = 8 := by
  have : Fintype GammaDual := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F2), finrank_dual_eq]
  simp

end Gamma

end Workspace.Types.Gamma
