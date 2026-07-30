import Mathlib
import Workspace.Types.MinkowskiWindow

open scoped NumberField
open Workspace.Types.MinkowskiWindow

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- **Lemma 2.5, part 1 (projection injectivity).** The first-coordinate projection
`z ↦ z 0` is injective on every coset `a + Λ` of the lattice. -/
theorem Lemma25ProjectionInjective [NeZero f] (sel : EmbeddingSelection L K f) (DD : ℕ)
    (a : Fin f → ℂ) :
    Set.InjOn (fun z : Fin f → ℂ => z 0) {z : Fin f → ℂ | z - a ∈ lattice sel DD} := by
  intro z hz z' hz' h
  simp only [Set.mem_setOf_eq] at hz hz'
  have hzz : z 0 = z' 0 := h
  -- Step 1: z - z' lies in the lattice.
  have hdiff : z - z' ∈ lattice sel DD := by
    have hsub := (lattice sel DD).sub_mem hz hz'
    have heq : (z - a) - (z' - a) = z - z' := by ring
    rwa [heq] at hsub
  obtain ⟨β, hβ⟩ := hdiff
  -- Unfold latticeHom applied to β.
  have key : latticeHom sel DD β
      = minkowskiMap sel ((algebraMap (𝓞 K) K β) * (DD : K)⁻¹) := by
    simp [latticeHom]
  -- Step 2: the 0-th coordinate of the difference vanishes.
  have h0 : sel.sigma 0 ((algebraMap (𝓞 K) K β) * (DD : K)⁻¹) = 0 := by
    have hcoord : (minkowskiMap sel ((algebraMap (𝓞 K) K β) * (DD : K)⁻¹)) 0 = (z - z') 0 := by
      rw [← key, hβ]
    simp only [minkowskiMap, Pi.ringHom_apply] at hcoord
    rw [hcoord]
    simp [Pi.sub_apply, hzz]
  -- Step 3: injectivity of the field embedding forces the field element to be 0.
  have hx : (algebraMap (𝓞 K) K β) * (DD : K)⁻¹ = 0 := by
    have hinj := RingHom.injective (sel.sigma 0)
    apply hinj
    rw [h0, map_zero]
  -- Step 4: the whole difference vector vanishes, so z = z'.
  have hzero : z - z' = 0 := by
    rw [← hβ, key, hx, map_zero]
  exact sub_eq_zero.mp hzero

end MinkowskiLemmas
