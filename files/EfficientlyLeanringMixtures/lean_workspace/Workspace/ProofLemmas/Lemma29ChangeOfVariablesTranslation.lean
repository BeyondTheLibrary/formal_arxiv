import Mathlib

open MeasureTheory

namespace Workspace.ProofLemmas

/--
Change-of-variables for translation on the real line, specialised to the form needed
by Lemma 29. For every Lebesgue-measurable `f : ℝ → ℝ`, every shift `μ ∈ ℝ`, and every
Lebesgue-measurable set `S ⊆ ℝ`,

  `∫ x in S, f (x - μ) = ∫ u in {u : ℝ | u + μ ∈ S}, f u`,

i.e. substituting `u := x - μ` rewrites a set integral over `S` (with integrand
`f (x - μ)`) as a set integral over `S - μ = {u : ℝ | u + μ ∈ S}` (with integrand
`f u`). Uses translation-invariance of Lebesgue measure on `ℝ`.

Specialised to `S := {x : ℝ | 2/ε ≤ |x|}` and `f u := |u + μ|^i · (1 / √(2π σ²))
  · exp(-u² / (2 σ²))`, this rewrites the Gaussian tail integral so that the
Gaussian is centred at `0` and the moving piece `|x|^i` becomes `|u + μ|^i`.
-/
theorem Lemma29ChangeOfVariablesTranslation
    (f : ℝ → ℝ) (μ : ℝ) (S : Set ℝ) (_hf : Measurable f) (_hS : MeasurableSet S) :
    ∫ x in S, f (x - μ) ∂MeasureTheory.volume =
      ∫ u in {u : ℝ | u + μ ∈ S}, f u ∂MeasureTheory.volume := by
  -- Apply the measure-preserving change of variables x ↦ x + μ.
  -- For g(x) := f(x - μ), setIntegral_preimage_emb gives:
  --   ∫ u in (·+μ)⁻¹' S, g (u + μ) = ∫ x in S, g x
  -- i.e. ∫ u in {u | u+μ ∈ S}, f((u+μ) - μ) = ∫ x in S, f(x - μ),
  -- which simplifies to the goal (symmetrically).
  have hmp : MeasurePreserving (fun u : ℝ => u + μ) volume volume :=
    measurePreserving_add_right volume μ
  have hemb : MeasurableEmbedding (fun u : ℝ => u + μ) :=
    (Homeomorph.addRight μ).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb (fun x => f (x - μ)) S
  -- h : ∫ u in (·+μ)⁻¹' S, f((u+μ) - μ) ∂vol = ∫ x in S, f(x - μ) ∂vol
  -- The preimage `(·+μ)⁻¹' S` equals `{u | u + μ ∈ S}` by definition.
  -- Simplify `(u + μ) - μ = u`.
  simp only [add_sub_cancel_right] at h
  -- Now h : ∫ u in (·+μ)⁻¹' S, f u ∂vol = ∫ x in S, f(x - μ) ∂vol
  -- And `(fun u => u + μ) ⁻¹' S = {u | u + μ ∈ S}` definitionally.
  exact h.symm

end Workspace.ProofLemmas
