import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination

/-!
# Sound sub-pieces for tail-domination of a signed Gaussian combination

This file proves the two concrete sub-pieces that the SOUND tail-domination
argument (Moitra–Valiant §6.1 Step 1) needs but that the existing axiom-clean
building blocks do not provide:

1. `SublemmaEqualVarSmallerMeanLittleORight` /
   `SublemmaEqualVarLargerMeanLittleOLeft` — the missing *little-o* facts for the
   variance-tie case.  `SublemmaRestIsLittleODom` only handles the
   `μ_other = μ_dom` exact tie (and only exports `O`); here, for two Gaussian
   densities with the **same** variance but a strictly smaller mean
   (`μ_other < μ_dom`), the density ratio tends to `0` on the RIGHT tail
   (`x → +∞`).  By reflection, a strictly larger mean gives `o` on the LEFT tail.

2. `exists_lexMax_component_right` / `exists_lexMax_component_left` — per-tail
   *lexicographic*-max nonzero-component selection.  The workspace's
   `exists_max_variance_component` only maximises `varSq`; here we additionally
   break ties by `mean` (largest mean for the right tail; smallest mean for the
   left tail), which is exactly the selection the sound residual bound requires.

No new axioms are introduced; the file depends only on Mathlib and the project
type definitions.
-/

namespace Workspace.ProofLemmas

open Filter Asymptotics
open scoped Topology

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

/-! ## Part 1 — the missing variance-tie little-o lemma -/

/--
**Equal variance, strictly smaller mean ⇒ little-o on the right tail.**

For two Gaussian *exponent* factors with the SAME variance `v` but a strictly
smaller "other" mean (`μ_other < μ_dom`), the ratio of the smaller-mean factor
to the larger-mean factor tends to `0` as `x → +∞`.  Mechanism: the exponent
difference is *linear* in `x`,

  `-(x-μ_other)²/(2v) - (-(x-μ_dom)²/(2v)) = (μ_other-μ_dom)/v · x + const`,

with slope `(μ_other - μ_dom)/v < 0`, so the linear form tends to `-∞` and the
exponential of it tends to `0`.
-/
theorem SublemmaEqualVarSmallerMeanLittleORight
    (v μ_other μ_dom : ℝ) (hv : 0 < v) (hμ : μ_other < μ_dom) :
    (fun x : ℝ => Real.exp (-(x - μ_other)^2 / (2 * v))) =o[Filter.atTop]
      (fun x : ℝ => Real.exp (-(x - μ_dom)^2 / (2 * v))) := by
  -- Slope and intercept of the linear exponent difference.
  set m : ℝ := (μ_other - μ_dom) / v with hm_def
  set k : ℝ := (μ_dom^2 - μ_other^2) / (2 * v) with hk_def
  have hm_neg : m < 0 := by
    rw [hm_def]
    apply div_neg_of_neg_of_pos _ hv
    linarith
  have h2v : (2 * v) ≠ 0 := by positivity
  have hv_ne : v ≠ 0 := ne_of_gt hv
  -- Pointwise: ratio = exp(m·x + k).
  have ratio_eq : ∀ x : ℝ,
      Real.exp (-(x - μ_other)^2 / (2 * v)) / Real.exp (-(x - μ_dom)^2 / (2 * v))
        = Real.exp (m * x + k) := by
    intro x
    rw [← Real.exp_sub]
    congr 1
    rw [hm_def, hk_def]
    field_simp
    ring
  -- The linear form tends to -∞ at atTop (negative slope).
  have h_lin : Tendsto (fun x : ℝ => m * x + k) atTop atBot :=
    (Filter.tendsto_id.const_mul_atTop_of_neg hm_neg).atBot_add tendsto_const_nhds
  have h_exp : Tendsto (fun x : ℝ => Real.exp (m * x + k)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_lin
  have hne : ∀ x : ℝ, Real.exp (-(x - μ_dom)^2 / (2 * v)) = 0 →
      Real.exp (-(x - μ_other)^2 / (2 * v)) = 0 := fun x hx =>
    absurd hx (ne_of_gt (Real.exp_pos _))
  rw [Asymptotics.isLittleO_iff_tendsto hne]
  refine h_exp.congr ?_
  intro x
  exact (ratio_eq x).symm

/--
**Equal variance, strictly larger mean ⇒ little-o on the left tail.**

The reflection (`x ↦ -x`) of `SublemmaEqualVarSmallerMeanLittleORight`: for the
SAME variance `v` but a strictly larger "other" mean (`μ_dom < μ_other`), the
ratio tends to `0` as `x → -∞`.
-/
theorem SublemmaEqualVarLargerMeanLittleOLeft
    (v μ_other μ_dom : ℝ) (hv : 0 < v) (hμ : μ_dom < μ_other) :
    (fun x : ℝ => Real.exp (-(x - μ_other)^2 / (2 * v))) =o[Filter.atBot]
      (fun x : ℝ => Real.exp (-(x - μ_dom)^2 / (2 * v))) := by
  -- Apply the right-tail version with reflected means, then pull back via x ↦ -x.
  have hμ' : (-μ_other) < (-μ_dom) := by linarith
  have hright := SublemmaEqualVarSmallerMeanLittleORight v (-μ_other) (-μ_dom) hv hμ'
  -- hright : exp(-(x-(-μ_other))²/(2v)) =o[atTop] exp(-(x-(-μ_dom))²/(2v))
  -- Compose with negation: atBot → atTop.
  have hcomp := hright.comp_tendsto Filter.tendsto_neg_atBot_atTop
  -- Rewrite the composed functions to the target shape using (-x - (-μ))² = (x - μ)².
  refine (hcomp.congr' ?_ ?_)
  · filter_upwards with x
    simp only [Function.comp_apply]
    congr 2
    ring
  · filter_upwards with x
    simp only [Function.comp_apply]
    congr 2
    ring

/-! ## Part 2 — per-tail lexicographic-max nonzero-component selection -/

/--
**Right-tail lexicographic-max nonzero component.**

From a signed Gaussian combination with at least one nonzero coefficient, there
is a component `(c, G)` with `c ≠ 0` that is lexicographically maximal by
`(varSq, mean)`: every other nonzero component `p` has `p.2.varSq ≤ G.varSq`,
and in case of a variance tie (`p.2.varSq = G.varSq`) also `p.2.mean ≤ G.mean`.
-/
theorem exists_lexMax_component_right
    (S : SignedGaussianCombination)
    (hS : ∃ p ∈ S.components, p.1 ≠ 0) :
    ∃ (c : ℝ) (G : GaussianPDF), (c, G) ∈ S.components ∧ c ≠ 0 ∧
      ∀ p ∈ S.components, p.1 ≠ 0 →
        p.2.varSq < G.varSq ∨ (p.2.varSq = G.varSq ∧ p.2.mean ≤ G.mean) := by
  classical
  -- Encode the lex order by the lexicographic product key (varSq, mean).
  let key : ℝ × GaussianPDF → Lex (ℝ × ℝ) := fun p => toLex (p.2.varSq, p.2.mean)
  let ne_comps := S.components.filter (fun p => p.1 ≠ 0)
  have h_nonempty : ne_comps ≠ [] := by
    obtain ⟨p, hp_mem, hp_ne⟩ := hS
    intro h
    have hmem' : p ∈ ne_comps := by
      simp [ne_comps, List.mem_filter, hp_mem, hp_ne]
    rw [h] at hmem'
    exact List.not_mem_nil hmem'
  obtain ⟨q, hq_argmax⟩ :
      ∃ q, List.argmax key ne_comps = some q := by
    rcases h : List.argmax key ne_comps with _ | q
    · exact absurd (List.argmax_eq_none.mp h) h_nonempty
    · exact ⟨q, rfl⟩
  have hq_mem : q ∈ ne_comps := List.argmax_mem hq_argmax
  have hq_in : q ∈ S.components := (List.mem_filter.mp hq_mem).1
  have hq_ne : q.1 ≠ 0 := by
    have := (List.mem_filter.mp hq_mem).2
    simpa using this
  refine ⟨q.1, q.2, ?_, hq_ne, ?_⟩
  · simpa using hq_in
  · intro p hp hpne
    have hp_ne_comps : p ∈ ne_comps := by
      simp [ne_comps, List.mem_filter, hp, hpne]
    -- argmax gives key p ≤ key q in the lex order.
    have hkey : key p ≤ key q :=
      List.le_of_mem_argmax (f := key) hp_ne_comps hq_argmax
    -- Decode the lex ≤ into the desired varSq/mean disjunction.
    rw [Prod.Lex.le_iff] at hkey
    simp only [key, ofLex_toLex] at hkey
    rcases hkey with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2

/--
**Left-tail lexicographic-max nonzero component.**

Same as `exists_lexMax_component_right` but the tie-break maximises `-mean`
(equivalently, *minimises* `mean`): in case of a variance tie the selected
component has the smallest mean.
-/
theorem exists_lexMax_component_left
    (S : SignedGaussianCombination)
    (hS : ∃ p ∈ S.components, p.1 ≠ 0) :
    ∃ (c : ℝ) (G : GaussianPDF), (c, G) ∈ S.components ∧ c ≠ 0 ∧
      ∀ p ∈ S.components, p.1 ≠ 0 →
        p.2.varSq < G.varSq ∨ (p.2.varSq = G.varSq ∧ G.mean ≤ p.2.mean) := by
  classical
  let key : ℝ × GaussianPDF → Lex (ℝ × ℝ) := fun p => toLex (p.2.varSq, -p.2.mean)
  let ne_comps := S.components.filter (fun p => p.1 ≠ 0)
  have h_nonempty : ne_comps ≠ [] := by
    obtain ⟨p, hp_mem, hp_ne⟩ := hS
    intro h
    have hmem' : p ∈ ne_comps := by
      simp [ne_comps, List.mem_filter, hp_mem, hp_ne]
    rw [h] at hmem'
    exact List.not_mem_nil hmem'
  obtain ⟨q, hq_argmax⟩ :
      ∃ q, List.argmax key ne_comps = some q := by
    rcases h : List.argmax key ne_comps with _ | q
    · exact absurd (List.argmax_eq_none.mp h) h_nonempty
    · exact ⟨q, rfl⟩
  have hq_mem : q ∈ ne_comps := List.argmax_mem hq_argmax
  have hq_in : q ∈ S.components := (List.mem_filter.mp hq_mem).1
  have hq_ne : q.1 ≠ 0 := by
    have := (List.mem_filter.mp hq_mem).2
    simpa using this
  refine ⟨q.1, q.2, ?_, hq_ne, ?_⟩
  · simpa using hq_in
  · intro p hp hpne
    have hp_ne_comps : p ∈ ne_comps := by
      simp [ne_comps, List.mem_filter, hp, hpne]
    have hkey : key p ≤ key q :=
      List.le_of_mem_argmax (f := key) hp_ne_comps hq_argmax
    rw [Prod.Lex.le_iff] at hkey
    simp only [key, ofLex_toLex] at hkey
    rcases hkey with h1 | h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2.1, ?_⟩
      have := h2.2
      linarith

end Workspace.ProofLemmas
