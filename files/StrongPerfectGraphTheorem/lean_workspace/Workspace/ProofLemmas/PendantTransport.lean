import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.AddPendantVertexTransport
import Workspace.ProofLemmas.RestrictGraph

/-!
# Transporting anticonnectedness onto `G + y`

`AddPendantVertexTransport` already moves paths, holes and their lengths across
`addPendantVertex`, but not **anticonnectedness** — and that is what the auxiliary graph
`G₀ = (G \ Y) + y` of 2.9, 2.10 and 2.11 needs, because every one of those proofs cites 2.1,
2.2 or 2.10 *inside* `G₀`, and all three demand an anticonnected set there.

The point is `AddPendantVertexTransport.compl_adj_inl_inl`: on old vertices the complement of
`G +ᵥ S` is the complement of `G`, so `Sum.inl` is a surjective graph homomorphism
`Gᶜ|A → (G +ᵥ S)ᶜ|(inl '' A)` and `SimpleGraph.Preconnected.map` finishes.

`anticonnectedSet_pendant_restrict` is the composite the section proofs actually want: `X`
anticonnected in `G` and contained in the kept set `W` gives `Sum.inl '' X` anticonnected in
`(restrictTo G W) +ᵥ S`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.PendantTransport

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.AddPendantVertexTransport

variable {V : Type*}

/-- **Anticonnectedness survives adding the pendant vertex.**  On old vertices the complement of
`G +ᵥ S` agrees with the complement of `G`, so `Sum.inl` restricts to a surjective homomorphism
between the two induced complements. -/
theorem anticonnectedSet_image_inl {H : SimpleGraph V} {S A : Set V}
    (h : AnticonnectedSet H A) :
    AnticonnectedSet (addPendantVertex H S) (Sum.inl '' A) := by
  -- the homomorphism must be written inline: binding it with `have` makes it opaque, and the
  -- surjectivity goal then no longer reduces (see `lean_knowledge.md`).
  refine SimpleGraph.Preconnected.map
    (⟨fun a => ⟨Sum.inl a.1, ⟨a.1, a.2, rfl⟩⟩,
      fun {a b} hab => (compl_adj_inl_inl H S a.1 b.1).mpr hab⟩ :
      (Hᶜ.induce A) →g (((addPendantVertex H S)ᶜ).induce (Sum.inl '' A))) ?_ h
  rintro ⟨z, hz⟩
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The composite used by 2.9, 2.10 and 2.11: `X` is anticonnected in `G` and lives inside the
kept set `W`, so its image is anticonnected in the auxiliary graph
`G₀ = (restrictTo G W) +ᵥ S`. -/
theorem anticonnectedSet_pendant_restrict {G : SimpleGraph V} {W X S : Set V}
    (hXW : X ⊆ W) (hX : AnticonnectedSet G X) :
    AnticonnectedSet (addPendantVertex (RestrictGraph.restrictTo G W) S) (Sum.inl '' X) :=
  anticonnectedSet_image_inl ((RestrictGraph.anticonnectedSet_restrictTo hXW).mpr hX)

/-- Membership in the image, in the form the section proofs meet it. -/
theorem mem_image_inl {A : Set V} {a : V} (ha : a ∈ A) : (Sum.inl a : V ⊕ Unit) ∈ Sum.inl '' A :=
  ⟨a, ha, rfl⟩

/-- …and its converse: only old vertices lie in the image, and they lie in `A`. -/
theorem mem_image_inl_iff {A : Set V} {z : V ⊕ Unit} :
    z ∈ Sum.inl '' A ↔ ∃ a ∈ A, z = Sum.inl a := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

/-- The pendant vertex is never in the image of `Sum.inl`. -/
theorem inr_notMem_image_inl {A : Set V} : (Sum.inr () : V ⊕ Unit) ∉ Sum.inl '' A := by
  rintro ⟨a, -, h⟩
  simp at h

end Workspace.ProofLemmas.PendantTransport
