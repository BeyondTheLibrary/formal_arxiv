import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.SublemmaEnvIsLittleODom
import Workspace.ProofLemmas.SublemmaTailDominanceSoundPieces

/-!
# Sound right-tail Gaussian-domination core

This file builds the SOUND right-tail core of `SublemmaTailDomination`, using only
Mathlib and the already-proven, axiom-clean building blocks
(`SublemmaEnvIsLittleODom`, `SublemmaRestIsLittleODom`,
`SublemmaTailDominanceSoundPieces`).  No new axioms, and in particular it does NOT
route through the FALSE-RISK `MaxVarianceGaussianTailEstimate` /
`MaxVarianceGaussianTailDominanceCoreMagnitude`.

The result `SublemmaTailDominationRightSound` returns, for a signed Gaussian
combination with a nonzero coefficient, a right-tail threshold `b'`, a nonzero
effective coefficient `a'`, and a positive variance `s'` such that for all
`x > b'` the density is sign-aligned with `a'` and strictly dominates the
`s'`-envelope `|a'| · (1/√(2π s')) · exp(-x²/(2 s'))`.
-/

namespace Workspace.ProofLemmas

open Filter Asymptotics
open scoped Topology
open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

-- COUNTEREXAMPLE CHECK (temporary): hypothesis `∃ nonzero coeff` does NOT imply
-- nonzero density. Here density ≡ 0 but a nonzero coefficient exists.
private example (G : GaussianPDF) (x : ℝ) :
    (⟨[(1, G), (-1, G)]⟩ : SignedGaussianCombination).density x = 0 := by
  simp [SignedGaussianCombination.density_eq]
private example (G : GaussianPDF) :
    ∃ p ∈ (⟨[(1, G), (-1, G)]⟩ : SignedGaussianCombination).components, p.1 ≠ 0 :=
  ⟨(1, G), by simp⟩

/-! ## Strict-smaller-variance little-o (arbitrary means), both tails -/

/--
Strictly smaller variance ⇒ little-o on the right tail, for arbitrary means.
The ratio's exponent is a quadratic in `x` with negative leading coefficient
`1/(2 v_dom) − 1/(2 v_other) < 0`, hence tends to `−∞`.
-/
private theorem strictVar_littleO_right
    (v_dom μ_dom v_other μ_other : ℝ)
    (h_dom : 0 < v_dom) (h_other : 0 < v_other) (h_lt : v_other < v_dom) :
    (fun x : ℝ => Real.exp (-(x - μ_other)^2 / (2 * v_other))) =o[Filter.atTop]
      (fun x : ℝ => Real.exp (-(x - μ_dom)^2 / (2 * v_dom))) := by
  set a : ℝ := 1 / (2 * v_dom) - 1 / (2 * v_other) with ha_def
  set b : ℝ := μ_other / v_other - μ_dom / v_dom with hb_def
  set c : ℝ := μ_dom^2 / (2 * v_dom) - μ_other^2 / (2 * v_other) with hc_def
  have h2other : (0 : ℝ) < 2 * v_other := by positivity
  have h2dom : (0 : ℝ) < 2 * v_dom := by positivity
  have ha_neg : a < 0 := by
    have h1 : 1 / (2 * v_dom) < 1 / (2 * v_other) :=
      one_div_lt_one_div_of_lt h2other (by linarith)
    rw [ha_def]; linarith
  have hvo : v_other ≠ 0 := ne_of_gt h_other
  have hvd : v_dom ≠ 0 := ne_of_gt h_dom
  have ratio_eq : ∀ x : ℝ,
      Real.exp (-(x - μ_other)^2 / (2 * v_other)) / Real.exp (-(x - μ_dom)^2 / (2 * v_dom))
        = Real.exp (a * x^2 + b * x + c) := by
    intro x
    rw [← Real.exp_sub]
    congr 1
    rw [ha_def, hb_def, hc_def]
    field_simp
    ring
  have h_lin : Tendsto (fun x : ℝ => a * x + b) atTop atBot :=
    (Filter.tendsto_id.const_mul_atTop_of_neg ha_neg).atBot_add tendsto_const_nhds
  have h_quad : Tendsto (fun x : ℝ => a * x^2 + b * x + c) atTop atBot := by
    have h2 : Tendsto (fun x : ℝ => x * (a * x + b)) atTop atBot :=
      Filter.tendsto_id.atTop_mul_atBot₀ h_lin
    have h3 : Tendsto (fun x : ℝ => x * (a * x + b) + c) atTop atBot :=
      h2.atBot_add tendsto_const_nhds
    apply h3.congr; intro x; ring
  have h_exp : Tendsto (fun x : ℝ => Real.exp (a * x^2 + b * x + c)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h_quad
  have hne : ∀ x : ℝ, Real.exp (-(x - μ_dom)^2 / (2 * v_dom)) = 0 →
      Real.exp (-(x - μ_other)^2 / (2 * v_other)) = 0 := fun x hx =>
    absurd hx (ne_of_gt (Real.exp_pos _))
  rw [Asymptotics.isLittleO_iff_tendsto hne]
  refine h_exp.congr ?_
  intro x; exact (ratio_eq x).symm

/-- Strictly smaller variance ⇒ little-o on the left tail, arbitrary means. -/
private theorem strictVar_littleO_left
    (v_dom μ_dom v_other μ_other : ℝ)
    (h_dom : 0 < v_dom) (h_other : 0 < v_other) (h_lt : v_other < v_dom) :
    (fun x : ℝ => Real.exp (-(x - μ_other)^2 / (2 * v_other))) =o[Filter.atBot]
      (fun x : ℝ => Real.exp (-(x - μ_dom)^2 / (2 * v_dom))) := by
  have hright := strictVar_littleO_right v_dom (-μ_dom) v_other (-μ_other) h_dom h_other h_lt
  have hcomp := hright.comp_tendsto Filter.tendsto_neg_atBot_atTop
  refine (hcomp.congr' ?_ ?_)
  · filter_upwards with x
    simp only [Function.comp_apply]; congr 2; ring
  · filter_upwards with x
    simp only [Function.comp_apply]; congr 2; ring

/-! ## Per-component little-o relative to the dominant Gaussian -/

/-- The exponential part of a Gaussian density. -/
private noncomputable def gexp (G : GaussianPDF) : ℝ → ℝ :=
  fun x => Real.exp (-(x - G.mean)^2 / (2 * G.varSq))

private theorem density_eq_const_mul_gexp (G : GaussianPDF) :
    G.density = fun x => (1 / Real.sqrt (2 * Real.pi * G.varSq)) * gexp G x := by
  funext x; rw [GaussianPDF.density_eq]; rfl

/-- For a component `(c, Gi)` whose key `(varSq, mean)` is lexicographically
strictly below the dominant `(V, M)` (strictly smaller variance, OR equal
variance and strictly smaller mean), the term `c · Gi.density` is little-o of
the dominant exponential `gexp Gdom` on the right tail. -/
private theorem component_littleO_right
    (Gdom Gi : GaussianPDF) (c : ℝ)
    (hkey : Gi.varSq < Gdom.varSq ∨ (Gi.varSq = Gdom.varSq ∧ Gi.mean < Gdom.mean)) :
    (fun x : ℝ => c * Gi.density x) =o[Filter.atTop] (gexp Gdom) := by
  have hi : 0 < Gi.varSq := Gi.varSq_pos
  have hd : 0 < Gdom.varSq := Gdom.varSq_pos
  -- exp-level little-o
  have hexp : (gexp Gi) =o[Filter.atTop] (gexp Gdom) := by
    rcases hkey with hlt | ⟨heq, hμ⟩
    · exact strictVar_littleO_right Gdom.varSq Gdom.mean Gi.varSq Gi.mean hd hi hlt
    · -- equal variance, strictly smaller mean
      have := SublemmaEqualVarSmallerMeanLittleORight Gdom.varSq Gi.mean Gdom.mean hd hμ
      -- `this` : exp(-(x-Gi.mean)²/(2 Gdom.varSq)) =o exp(-(x-Gdom.mean)²/(2 Gdom.varSq))
      -- rewrite Gi.varSq = Gdom.varSq in the LHS exponent
      rw [show gexp Gi = (fun x : ℝ => Real.exp (-(x - Gi.mean)^2 / (2 * Gdom.varSq))) by
            funext x; rw [gexp, heq]]
      exact this
  -- density = (positive const) * gexp, and we multiply by constant c
  have hdens : (fun x : ℝ => c * Gi.density x)
      = (fun x : ℝ => (c * (1 / Real.sqrt (2 * Real.pi * Gi.varSq))) * gexp Gi x) := by
    funext x; rw [density_eq_const_mul_gexp]; ring
  rw [hdens]
  exact (hexp.const_mul_left _)

/-- Left-tail analogue. -/
private theorem component_littleO_left
    (Gdom Gi : GaussianPDF) (c : ℝ)
    (hkey : Gi.varSq < Gdom.varSq ∨ (Gi.varSq = Gdom.varSq ∧ Gdom.mean < Gi.mean)) :
    (fun x : ℝ => c * Gi.density x) =o[Filter.atBot] (gexp Gdom) := by
  have hi : 0 < Gi.varSq := Gi.varSq_pos
  have hd : 0 < Gdom.varSq := Gdom.varSq_pos
  have hexp : (gexp Gi) =o[Filter.atBot] (gexp Gdom) := by
    rcases hkey with hlt | ⟨heq, hμ⟩
    · exact strictVar_littleO_left Gdom.varSq Gdom.mean Gi.varSq Gi.mean hd hi hlt
    · have := SublemmaEqualVarLargerMeanLittleOLeft Gdom.varSq Gi.mean Gdom.mean hd hμ
      rw [show gexp Gi = (fun x : ℝ => Real.exp (-(x - Gi.mean)^2 / (2 * Gdom.varSq))) by
            funext x; rw [gexp, heq]]
      exact this
  have hdens : (fun x : ℝ => c * Gi.density x)
      = (fun x : ℝ => (c * (1 / Real.sqrt (2 * Real.pi * Gi.varSq))) * gexp Gi x) := by
    funext x; rw [density_eq_const_mul_gexp]; ring
  rw [hdens]
  exact (hexp.const_mul_left _)

/-! ## Summing little-o over a list -/

/-- The key of a component is strictly below the dominant key `(V, M)` in the
right-tail lex order: strictly smaller variance, or equal variance & strictly
smaller mean. -/
private def belowKeyRight (Gdom : GaussianPDF) (p : ℝ × GaussianPDF) : Prop :=
  p.2.varSq < Gdom.varSq ∨ (p.2.varSq = Gdom.varSq ∧ p.2.mean < Gdom.mean)

private def belowKeyLeft (Gdom : GaussianPDF) (p : ℝ × GaussianPDF) : Prop :=
  p.2.varSq < Gdom.varSq ∨ (p.2.varSq = Gdom.varSq ∧ Gdom.mean < p.2.mean)

/-- A list-sum of components, each either zero-coefficient or strictly below the
dominant key, is little-o of the dominant exponential on the right tail. -/
private theorem listSum_littleO_right
    (Gdom : GaussianPDF) (L : List (ℝ × GaussianPDF))
    (hL : ∀ p ∈ L, p.1 = 0 ∨ belowKeyRight Gdom p) :
    (fun x : ℝ => (L.map (fun p => p.1 * p.2.density x)).sum) =o[Filter.atTop] (gexp Gdom) := by
  induction L with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact Asymptotics.isLittleO_zero _ _
  | cons hd tl ih =>
      have hhd := hL hd (List.mem_cons_self)
      have htl : ∀ p ∈ tl, p.1 = 0 ∨ belowKeyRight Gdom p := fun p hp =>
        hL p (List.mem_cons_of_mem _ hp)
      have ih' := ih htl
      have hhd_o : (fun x : ℝ => hd.1 * hd.2.density x) =o[Filter.atTop] (gexp Gdom) := by
        rcases hhd with h0 | hbelow
        · rw [h0]; simp only [zero_mul]; exact Asymptotics.isLittleO_zero _ _
        · exact component_littleO_right Gdom hd.2 hd.1 hbelow
      have hsum := hhd_o.add ih'
      refine hsum.congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
      filter_upwards with x
      simp only [List.map_cons, List.sum_cons]

private theorem listSum_littleO_left
    (Gdom : GaussianPDF) (L : List (ℝ × GaussianPDF))
    (hL : ∀ p ∈ L, p.1 = 0 ∨ belowKeyLeft Gdom p) :
    (fun x : ℝ => (L.map (fun p => p.1 * p.2.density x)).sum) =o[Filter.atBot] (gexp Gdom) := by
  induction L with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact Asymptotics.isLittleO_zero _ _
  | cons hd tl ih =>
      have hhd := hL hd (List.mem_cons_self)
      have htl : ∀ p ∈ tl, p.1 = 0 ∨ belowKeyLeft Gdom p := fun p hp =>
        hL p (List.mem_cons_of_mem _ hp)
      have ih' := ih htl
      have hhd_o : (fun x : ℝ => hd.1 * hd.2.density x) =o[Filter.atBot] (gexp Gdom) := by
        rcases hhd with h0 | hbelow
        · rw [h0]; simp only [zero_mul]; exact Asymptotics.isLittleO_zero _ _
        · exact component_littleO_left Gdom hd.2 hd.1 hbelow
      have hsum := hhd_o.add ih'
      refine hsum.congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
      filter_upwards with x
      simp only [List.map_cons, List.sum_cons]

/-! ## Density decomposition into a dominant Gaussian plus a residual -/

/-- Predicate: a component is exactly the dominant Gaussian (same variance AND mean). -/
private def isTop (Gdom : GaussianPDF) (p : ℝ × GaussianPDF) : Prop :=
  p.2.varSq = Gdom.varSq ∧ p.2.mean = Gdom.mean

private noncomputable instance (Gdom : GaussianPDF) : DecidablePred (isTop Gdom) := fun p =>
  Classical.propDecidable _

/-- A component that is exactly the dominant Gaussian has the same density. -/
private theorem density_of_isTop {Gdom : GaussianPDF} {p : ℝ × GaussianPDF}
    (h : isTop Gdom p) (x : ℝ) : p.2.density x = Gdom.density x := by
  obtain ⟨hv, hm⟩ := h
  rw [GaussianPDF.density_eq, GaussianPDF.density_eq, hv, hm]

/-- The group coefficient sum of the dominant Gaussian. -/
private noncomputable def topCoeffSum (Gdom : GaussianPDF)
    (S : SignedGaussianCombination) : ℝ :=
  ((S.components.filter (fun p => decide (isTop Gdom p))).map (fun p => p.1)).sum

/-- The signed combination obtained by deleting the `isTop Gdom` group from `S`. -/
private noncomputable def dropTop (Gdom : GaussianPDF) (S : SignedGaussianCombination) :
    SignedGaussianCombination :=
  ⟨S.components.filter (fun p => decide ¬ isTop Gdom p)⟩

/-- **Pointwise density split** (no cover hypothesis needed): the density of `S`
equals the dominant-group contribution `topCoeffSum · Gdom.density` plus the
density of the `Gdom`-group-deleted combination `dropTop Gdom S`. -/
private theorem density_split (S : SignedGaussianCombination) (Gdom : GaussianPDF) (x : ℝ) :
    S.density x = topCoeffSum Gdom S * Gdom.density x + (dropTop Gdom S).density x := by
  classical
  set top := S.components.filter (fun p => decide (isTop Gdom p)) with htop_def
  set rest := S.components.filter (fun p => decide ¬ isTop Gdom p) with hrest_def
  have hpart := List.sum_map_filter_add_sum_map_filter_not (isTop Gdom)
    (fun p => p.1 * p.2.density x) S.components
  have htop_sum : (top.map (fun p => p.1 * p.2.density x)).sum
      = topCoeffSum Gdom S * Gdom.density x := by
    have hmap_eq : top.map (fun p => p.1 * p.2.density x)
        = top.map (fun p => p.1 * Gdom.density x) := by
      apply List.map_congr_left
      intro p hp
      have hp_top : isTop Gdom p := by
        have := (List.mem_filter.mp hp).2
        simpa using this
      rw [density_of_isTop hp_top]
    rw [hmap_eq, List.sum_map_mul_right top (fun p => p.1) (Gdom.density x)]
    rfl
  rw [SignedGaussianCombination.density_eq, dropTop, SignedGaussianCombination.density_eq]
  rw [← hpart, htop_sum]

/-- If every coefficient of `S` is zero then the density is identically zero. -/
private theorem density_zero_of_all_coeff_zero (S : SignedGaussianCombination)
    (h : ∀ p ∈ S.components, p.1 = 0) (x : ℝ) : S.density x = 0 := by
  rw [SignedGaussianCombination.density_eq]
  apply List.sum_eq_zero
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨p, hp, rfl⟩ := hy
  rw [h p hp, zero_mul]

/-- A density that is somewhere nonzero has a nonzero coefficient. -/
private theorem exists_nonzero_coeff_of_density_ne (S : SignedGaussianCombination)
    (hS : ∃ x, S.density x ≠ 0) : ∃ p ∈ S.components, p.1 ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx⟩ := hS
  exact hx (density_zero_of_all_coeff_zero S h x)

/-- **Density decomposition (right tail).** Suppose the dominant `Gdom` is such
that every nonzero component is either exactly `Gdom` (same varSq & mean) or
strictly below it in the right-tail lex order.  Then
`S.density x = A · Gdom.density x + R x` with `A = topCoeffSum` and `R =o gexp Gdom`. -/
private theorem density_decomp_right
    (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    (hcov : ∀ p ∈ S.components, p.1 = 0 ∨ isTop Gdom p ∨ belowKeyRight Gdom p) :
    (fun x : ℝ => S.density x
        - topCoeffSum Gdom S * Gdom.density x) =o[Filter.atTop] (gexp Gdom) := by
  classical
  set top := S.components.filter (fun p => decide (isTop Gdom p)) with htop_def
  set rest := S.components.filter (fun p => decide ¬ isTop Gdom p) with hrest_def
  -- residual = rest-list sum
  have hsplit : ∀ x : ℝ,
      S.density x - topCoeffSum Gdom S * Gdom.density x
        = (rest.map (fun p => p.1 * p.2.density x)).sum := by
    intro x
    have hpart := List.sum_map_filter_add_sum_map_filter_not (isTop Gdom)
      (fun p => p.1 * p.2.density x) S.components
    -- top-sum = A * Gdom.density x
    have htop_sum : (top.map (fun p => p.1 * p.2.density x)).sum
        = topCoeffSum Gdom S * Gdom.density x := by
      have hmap_eq : top.map (fun p => p.1 * p.2.density x)
          = top.map (fun p => p.1 * Gdom.density x) := by
        apply List.map_congr_left
        intro p hp
        have hp_top : isTop Gdom p := by
          have := (List.mem_filter.mp hp).2
          simpa using this
        rw [density_of_isTop hp_top]
      rw [hmap_eq, List.sum_map_mul_right top (fun p => p.1) (Gdom.density x)]
      rfl
    rw [SignedGaussianCombination.density_eq]
    rw [← hpart]
    rw [htop_def, hrest_def] at *
    rw [htop_sum]
    ring
  -- residual is o(gexp Gdom)
  have hres_o : (fun x : ℝ => (rest.map (fun p => p.1 * p.2.density x)).sum)
      =o[Filter.atTop] (gexp Gdom) := by
    apply listSum_littleO_right
    intro p hp
    have hp_comp : p ∈ S.components := (List.mem_filter.mp hp).1
    have hp_not : ¬ isTop Gdom p := by
      have := (List.mem_filter.mp hp).2
      simpa using this
    rcases hcov p hp_comp with h0 | htopp | hbelow
    · exact Or.inl h0
    · exact absurd htopp hp_not
    · exact Or.inr hbelow
  exact hres_o.congr' (Filter.Eventually.of_forall (fun x => (hsplit x).symm))
    (Filter.Eventually.of_forall (fun _ => rfl))

/-- **Density decomposition (left tail).** Mirror of `density_decomp_right`
using the left-tail lex order (`belowKeyLeft`) and `atBot`. -/
private theorem density_decomp_left
    (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    (hcov : ∀ p ∈ S.components, p.1 = 0 ∨ isTop Gdom p ∨ belowKeyLeft Gdom p) :
    (fun x : ℝ => S.density x
        - topCoeffSum Gdom S * Gdom.density x) =o[Filter.atBot] (gexp Gdom) := by
  classical
  set top := S.components.filter (fun p => decide (isTop Gdom p)) with htop_def
  set rest := S.components.filter (fun p => decide ¬ isTop Gdom p) with hrest_def
  have hsplit : ∀ x : ℝ,
      S.density x - topCoeffSum Gdom S * Gdom.density x
        = (rest.map (fun p => p.1 * p.2.density x)).sum := by
    intro x
    have hpart := List.sum_map_filter_add_sum_map_filter_not (isTop Gdom)
      (fun p => p.1 * p.2.density x) S.components
    have htop_sum : (top.map (fun p => p.1 * p.2.density x)).sum
        = topCoeffSum Gdom S * Gdom.density x := by
      have hmap_eq : top.map (fun p => p.1 * p.2.density x)
          = top.map (fun p => p.1 * Gdom.density x) := by
        apply List.map_congr_left
        intro p hp
        have hp_top : isTop Gdom p := by
          have := (List.mem_filter.mp hp).2
          simpa using this
        rw [density_of_isTop hp_top]
      rw [hmap_eq, List.sum_map_mul_right top (fun p => p.1) (Gdom.density x)]
      rfl
    rw [SignedGaussianCombination.density_eq]
    rw [← hpart]
    rw [htop_def, hrest_def] at *
    rw [htop_sum]
    ring
  have hres_o : (fun x : ℝ => (rest.map (fun p => p.1 * p.2.density x)).sum)
      =o[Filter.atBot] (gexp Gdom) := by
    apply listSum_littleO_left
    intro p hp
    have hp_comp : p ∈ S.components := (List.mem_filter.mp hp).1
    have hp_not : ¬ isTop Gdom p := by
      have := (List.mem_filter.mp hp).2
      simpa using this
    rcases hcov p hp_comp with h0 | htopp | hbelow
    · exact Or.inl h0
    · exact absurd htopp hp_not
    · exact Or.inr hbelow
  exact hres_o.congr' (Filter.Eventually.of_forall (fun x => (hsplit x).symm))
    (Filter.Eventually.of_forall (fun _ => rfl))

/-! ## The glued right-tail domination core -/

/-- **Sound right-tail domination core.**

Given a dominant Gaussian `Gdom` such that
* every nonzero component of `S` is either exactly `Gdom` (same varSq & mean) or
  strictly below it in the right-tail lex order (smaller varSq, or equal varSq &
  smaller mean), and
* the dominant group coefficient sum `A := topCoeffSum Gdom S` is nonzero,

then on the right tail `S.density` is sign-aligned with `A` and strictly
dominates the `(Gdom.varSq/2)`-envelope with coefficient `A`.

No false axioms: built from `density_decomp_right` + `SublemmaEnvIsLittleODom`. -/
theorem SublemmaTailDominationRightCore
    (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    (hcov : ∀ p ∈ S.components, p.1 = 0 ∨ isTop Gdom p ∨ belowKeyRight Gdom p)
    (hA : topCoeffSum Gdom S ≠ 0) :
    ∃ b' : ℝ, ∀ x : ℝ, x > b' →
      (S.density x).sign = (topCoeffSum Gdom S).sign ∧
      |topCoeffSum Gdom S| * (1 / Real.sqrt (2 * Real.pi * (Gdom.varSq / 2))) *
        Real.exp (-x^2 / (2 * (Gdom.varSq / 2))) < |S.density x| := by
  classical
  set A := topCoeffSum Gdom S with hA_def
  set V := Gdom.varSq with hV_def
  have hV : 0 < V := Gdom.varSq_pos
  -- positive normalising constants
  set K : ℝ := 1 / Real.sqrt (2 * Real.pi * V) with hK_def
  have hK_pos : 0 < K := by
    rw [hK_def]; positivity
  set Kenv : ℝ := 1 / Real.sqrt (2 * Real.pi * (V / 2)) with hKenv_def
  have hKenv_pos : 0 < Kenv := by
    rw [hKenv_def]; positivity
  -- gexp is positive
  have hgexp_pos : ∀ x, 0 < gexp Gdom x := fun x => Real.exp_pos _
  -- Gdom.density x = K * gexp Gdom x
  have hGdens : ∀ x, Gdom.density x = K * gexp Gdom x := by
    intro x; rw [GaussianPDF.density_eq, hK_def, gexp]
  -- residual decomposition
  have hdecomp := density_decomp_right S Gdom hcov
  -- envelope-exp is o(gexp Gdom): exp(-x²/(2(V/2))) =o exp(-(x-M)²/(2V))
  have henv_o : (fun x : ℝ => Real.exp (-x^2 / (2 * (V / 2)))) =o[Filter.atTop] (gexp Gdom) := by
    have h := (SublemmaEnvIsLittleODom (V / 2) V Gdom.mean (by linarith) hV (by linarith)).1
    refine h.congr_right ?_
    intro x
    rw [gexp, hV_def]
  -- |A| K > 0
  have hAK : 0 < |A| * K := mul_pos (abs_pos.mpr hA) hK_pos
  -- eventually |R| ≤ (|A| K / 4) gexp
  have hR_bound : ∀ᶠ x in Filter.atTop,
      |S.density x - A * Gdom.density x| ≤ (|A| * K / 4) * gexp Gdom x := by
    have := hdecomp.def (c := |A| * K / 4) (by positivity)
    filter_upwards [this] with x hx
    have : ‖S.density x - A * Gdom.density x‖ ≤ (|A| * K / 4) * ‖gexp Gdom x‖ := hx
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hgexp_pos x)] at this
  -- eventually Kenv * envexp ≤ (K / 2) gexp
  have henv_bound : ∀ᶠ x in Filter.atTop,
      Kenv * Real.exp (-x^2 / (2 * (V / 2))) ≤ (K / 2) * gexp Gdom x := by
    have hc : (0 : ℝ) < K / (2 * Kenv) := by positivity
    have := henv_o.def (c := K / (2 * Kenv)) hc
    filter_upwards [this] with x hx
    have hx' : Real.exp (-x^2 / (2 * (V / 2))) ≤ (K / (2 * Kenv)) * gexp Gdom x := by
      have := hx
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_pos (hgexp_pos x)] at this
    calc Kenv * Real.exp (-x^2 / (2 * (V / 2)))
        ≤ Kenv * ((K / (2 * Kenv)) * gexp Gdom x) :=
          mul_le_mul_of_nonneg_left hx' (le_of_lt hKenv_pos)
      _ = (K / 2) * gexp Gdom x := by field_simp
  -- combine the eventual facts into the full pointwise conclusion
  have hfull : ∀ᶠ x in Filter.atTop,
      (S.density x).sign = A.sign ∧
      |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2))) < |S.density x| := by
    filter_upwards [hR_bound, henv_bound] with x hRb henv
    -- notation
    set g := gexp Gdom x with hg_def
    have hg_pos : 0 < g := hgexp_pos x
    -- D = A * K * g, with Gdom.density x = K g
    have hD : A * Gdom.density x = A * K * g := by rw [hGdens x, hg_def]; ring
    -- |S.density x| ≥ |A| K g - |R| ≥ (3/4)|A|K g
    have habs_split : |A| * K * g - |A| * K / 4 * g ≤ |S.density x| := by
      have h1 : |A * Gdom.density x| - |S.density x - A * Gdom.density x| ≤ |S.density x| := by
        have := abs_sub_abs_le_abs_sub (A * Gdom.density x) (A * Gdom.density x - S.density x)
        simp only [sub_sub_cancel] at this
        calc |A * Gdom.density x| - |S.density x - A * Gdom.density x|
            = |A * Gdom.density x| - |A * Gdom.density x - S.density x| := by
              rw [abs_sub_comm (S.density x)]
          _ ≤ |S.density x| := this
      have hDabs : |A * Gdom.density x| = |A| * K * g := by
        rw [hD, abs_mul, abs_mul, abs_of_pos hK_pos, abs_of_pos hg_pos]
      rw [hDabs] at h1
      linarith [hRb, h1]
    have hpos_lb : 0 < |A| * K * g - |A| * K / 4 * g := by
      have : |A| * K / 4 * g < |A| * K * g := by nlinarith [hAK, hg_pos]
      linarith
    refine ⟨?_, ?_⟩
    · -- sign: S.density x = A K g + R with |R| < |A K g|, K g > 0 ⇒ sign = sign A
      have hKg : 0 < K * g := mul_pos hK_pos hg_pos
      have hRlt : |S.density x - A * Gdom.density x| < |A| * (K * g) := by
        have : |A| * K / 4 * g < |A| * (K * g) := by nlinarith [hAK, hg_pos]
        linarith [hRb]
      -- S.density x = A * (K g) + (S.density x - A K g)
      have heq : S.density x = A * (K * g) + (S.density x - A * Gdom.density x) := by
        rw [hD]; ring
      rcases lt_trichotomy A 0 with hAneg | hAzero | hApos
      · have hsd_neg : S.density x < 0 := by
          have : A * (K * g) < 0 := mul_neg_of_neg_of_pos hAneg hKg
          have hR2 : |S.density x - A * Gdom.density x| < -(A * (K * g)) := by
            rw [abs_of_neg hAneg] at hRlt; linarith
          have := abs_lt.mp hR2
          rw [heq]; linarith [this.2]
        rw [Real.sign_of_neg hsd_neg, Real.sign_of_neg hAneg]
      · exact absurd hAzero hA
      · have hsd_pos : 0 < S.density x := by
          have hAKg : 0 < A * (K * g) := mul_pos hApos hKg
          have hR2 : |S.density x - A * Gdom.density x| < A * (K * g) := by
            rw [abs_of_pos hApos] at hRlt; linarith
          have := abs_lt.mp hR2
          rw [heq]; linarith [this.1]
        rw [Real.sign_of_pos hsd_pos, Real.sign_of_pos hApos]
    · -- magnitude: |A| Kenv envexp ≤ |A| (K/2) g < (3/4)|A|K g ≤ |S.density x|
      have henv2 : |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2)))
          ≤ |A| * ((K / 2) * g) := by
        have hAnn : 0 ≤ |A| := abs_nonneg A
        calc |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2)))
            = |A| * (Kenv * Real.exp (-x^2 / (2 * (V / 2)))) := by ring
          _ ≤ |A| * ((K / 2) * g) := by
              apply mul_le_mul_of_nonneg_left _ hAnn
              rw [hg_def]; exact henv
      have hstrict : |A| * ((K / 2) * g) < |A| * K * g - |A| * K / 4 * g := by
        nlinarith [hAK, hg_pos]
      linarith [henv2, hstrict, habs_split]
  -- extract a threshold b'
  obtain ⟨a₀, ha₀⟩ := hfull.exists_forall_of_atTop
  refine ⟨a₀, fun x hx => ?_⟩
  have hxa : x ≥ a₀ := le_of_lt hx
  obtain ⟨hsign, hmag⟩ := ha₀ x hxa
  refine ⟨by rw [hsign], ?_⟩
  -- rewrite the envelope into the file's normalised form: |A| * Kenv * envexp
  have : |A| * (1 / Real.sqrt (2 * Real.pi * (V / 2))) *
      Real.exp (-x^2 / (2 * (V / 2)))
        = |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2))) := by rw [hKenv_def]
  rw [hV_def] at this ⊢
  rw [this]
  exact hmag

/-- **Sound left-tail domination core.** Mirror of `SublemmaTailDominationRightCore`
on the left tail, using the left-tail lex order (`belowKeyLeft`). -/
theorem SublemmaTailDominationLeftCore
    (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    (hcov : ∀ p ∈ S.components, p.1 = 0 ∨ isTop Gdom p ∨ belowKeyLeft Gdom p)
    (hA : topCoeffSum Gdom S ≠ 0) :
    ∃ b : ℝ, ∀ x : ℝ, x < b →
      (S.density x).sign = (topCoeffSum Gdom S).sign ∧
      |topCoeffSum Gdom S| * (1 / Real.sqrt (2 * Real.pi * (Gdom.varSq / 2))) *
        Real.exp (-x^2 / (2 * (Gdom.varSq / 2))) < |S.density x| := by
  classical
  set A := topCoeffSum Gdom S with hA_def
  set V := Gdom.varSq with hV_def
  have hV : 0 < V := Gdom.varSq_pos
  set K : ℝ := 1 / Real.sqrt (2 * Real.pi * V) with hK_def
  have hK_pos : 0 < K := by rw [hK_def]; positivity
  set Kenv : ℝ := 1 / Real.sqrt (2 * Real.pi * (V / 2)) with hKenv_def
  have hKenv_pos : 0 < Kenv := by rw [hKenv_def]; positivity
  have hgexp_pos : ∀ x, 0 < gexp Gdom x := fun x => Real.exp_pos _
  have hGdens : ∀ x, Gdom.density x = K * gexp Gdom x := by
    intro x; rw [GaussianPDF.density_eq, hK_def, gexp]
  have hdecomp := density_decomp_left S Gdom hcov
  have henv_o : (fun x : ℝ => Real.exp (-x^2 / (2 * (V / 2)))) =o[Filter.atBot] (gexp Gdom) := by
    have h := (SublemmaEnvIsLittleODom (V / 2) V Gdom.mean (by linarith) hV (by linarith)).2
    refine h.congr_right ?_
    intro x
    rw [gexp, hV_def]
  have hAK : 0 < |A| * K := mul_pos (abs_pos.mpr hA) hK_pos
  have hR_bound : ∀ᶠ x in Filter.atBot,
      |S.density x - A * Gdom.density x| ≤ (|A| * K / 4) * gexp Gdom x := by
    have := hdecomp.def (c := |A| * K / 4) (by positivity)
    filter_upwards [this] with x hx
    have : ‖S.density x - A * Gdom.density x‖ ≤ (|A| * K / 4) * ‖gexp Gdom x‖ := hx
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hgexp_pos x)] at this
  have henv_bound : ∀ᶠ x in Filter.atBot,
      Kenv * Real.exp (-x^2 / (2 * (V / 2))) ≤ (K / 2) * gexp Gdom x := by
    have hc : (0 : ℝ) < K / (2 * Kenv) := by positivity
    have := henv_o.def (c := K / (2 * Kenv)) hc
    filter_upwards [this] with x hx
    have hx' : Real.exp (-x^2 / (2 * (V / 2))) ≤ (K / (2 * Kenv)) * gexp Gdom x := by
      have := hx
      rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_pos (hgexp_pos x)] at this
    calc Kenv * Real.exp (-x^2 / (2 * (V / 2)))
        ≤ Kenv * ((K / (2 * Kenv)) * gexp Gdom x) :=
          mul_le_mul_of_nonneg_left hx' (le_of_lt hKenv_pos)
      _ = (K / 2) * gexp Gdom x := by field_simp
  have hfull : ∀ᶠ x in Filter.atBot,
      (S.density x).sign = A.sign ∧
      |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2))) < |S.density x| := by
    filter_upwards [hR_bound, henv_bound] with x hRb henv
    set g := gexp Gdom x with hg_def
    have hg_pos : 0 < g := hgexp_pos x
    have hD : A * Gdom.density x = A * K * g := by rw [hGdens x, hg_def]; ring
    have habs_split : |A| * K * g - |A| * K / 4 * g ≤ |S.density x| := by
      have h1 : |A * Gdom.density x| - |S.density x - A * Gdom.density x| ≤ |S.density x| := by
        have := abs_sub_abs_le_abs_sub (A * Gdom.density x) (A * Gdom.density x - S.density x)
        simp only [sub_sub_cancel] at this
        calc |A * Gdom.density x| - |S.density x - A * Gdom.density x|
            = |A * Gdom.density x| - |A * Gdom.density x - S.density x| := by
              rw [abs_sub_comm (S.density x)]
          _ ≤ |S.density x| := this
      have hDabs : |A * Gdom.density x| = |A| * K * g := by
        rw [hD, abs_mul, abs_mul, abs_of_pos hK_pos, abs_of_pos hg_pos]
      rw [hDabs] at h1
      linarith [hRb, h1]
    refine ⟨?_, ?_⟩
    · have hKg : 0 < K * g := mul_pos hK_pos hg_pos
      have hRlt : |S.density x - A * Gdom.density x| < |A| * (K * g) := by
        have : |A| * K / 4 * g < |A| * (K * g) := by nlinarith [hAK, hg_pos]
        linarith [hRb]
      have heq : S.density x = A * (K * g) + (S.density x - A * Gdom.density x) := by
        rw [hD]; ring
      rcases lt_trichotomy A 0 with hAneg | hAzero | hApos
      · have hsd_neg : S.density x < 0 := by
          have : A * (K * g) < 0 := mul_neg_of_neg_of_pos hAneg hKg
          have hR2 : |S.density x - A * Gdom.density x| < -(A * (K * g)) := by
            rw [abs_of_neg hAneg] at hRlt; linarith
          have := abs_lt.mp hR2
          rw [heq]; linarith [this.2]
        rw [Real.sign_of_neg hsd_neg, Real.sign_of_neg hAneg]
      · exact absurd hAzero hA
      · have hsd_pos : 0 < S.density x := by
          have hAKg : 0 < A * (K * g) := mul_pos hApos hKg
          have hR2 : |S.density x - A * Gdom.density x| < A * (K * g) := by
            rw [abs_of_pos hApos] at hRlt; linarith
          have := abs_lt.mp hR2
          rw [heq]; linarith [this.1]
        rw [Real.sign_of_pos hsd_pos, Real.sign_of_pos hApos]
    · have henv2 : |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2)))
          ≤ |A| * ((K / 2) * g) := by
        have hAnn : 0 ≤ |A| := abs_nonneg A
        calc |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2)))
            = |A| * (Kenv * Real.exp (-x^2 / (2 * (V / 2)))) := by ring
          _ ≤ |A| * ((K / 2) * g) := by
              apply mul_le_mul_of_nonneg_left _ hAnn
              rw [hg_def]; exact henv
      have hstrict : |A| * ((K / 2) * g) < |A| * K * g - |A| * K / 4 * g := by
        nlinarith [hAK, hg_pos]
      linarith [henv2, hstrict, habs_split]
  obtain ⟨a₀, ha₀⟩ := hfull.exists_forall_of_atBot
  refine ⟨a₀, fun x hx => ?_⟩
  have hxa : x ≤ a₀ := le_of_lt hx
  obtain ⟨hsign, hmag⟩ := ha₀ x hxa
  refine ⟨by rw [hsign], ?_⟩
  have : |A| * (1 / Real.sqrt (2 * Real.pi * (V / 2))) *
      Real.exp (-x^2 / (2 * (V / 2)))
        = |A| * Kenv * Real.exp (-x^2 / (2 * (V / 2))) := by rw [hKenv_def]
  rw [hV_def] at this ⊢
  rw [this]
  exact hmag

/-! ## Bridges from lexicographic-max selection -/

/-- Bridge: a right-tail lex-max dominant `G` (every nonzero component below-or-
equal in `(varSq, mean)`) gives the cover hypothesis of the right core. -/
theorem cover_right_of_lexMax
    (S : SignedGaussianCombination) (G : GaussianPDF)
    (hmax : ∀ p ∈ S.components, p.1 ≠ 0 →
        p.2.varSq < G.varSq ∨ (p.2.varSq = G.varSq ∧ p.2.mean ≤ G.mean)) :
    ∀ p ∈ S.components, p.1 = 0 ∨ isTop G p ∨ belowKeyRight G p := by
  intro p hp
  by_cases h0 : p.1 = 0
  · exact Or.inl h0
  · rcases hmax p hp h0 with hlt | ⟨heq, hle⟩
    · exact Or.inr (Or.inr (Or.inl hlt))
    · rcases lt_or_eq_of_le hle with hmlt | hmeq
      · exact Or.inr (Or.inr (Or.inr ⟨heq, hmlt⟩))
      · exact Or.inr (Or.inl ⟨heq, hmeq⟩)

/-- Bridge: a left-tail lex-max dominant `G` (every nonzero component below-or-
equal, ties broken by SMALLEST mean) gives the cover hypothesis of the left core. -/
theorem cover_left_of_lexMax
    (S : SignedGaussianCombination) (G : GaussianPDF)
    (hmax : ∀ p ∈ S.components, p.1 ≠ 0 →
        p.2.varSq < G.varSq ∨ (p.2.varSq = G.varSq ∧ G.mean ≤ p.2.mean)) :
    ∀ p ∈ S.components, p.1 = 0 ∨ isTop G p ∨ belowKeyLeft G p := by
  intro p hp
  by_cases h0 : p.1 = 0
  · exact Or.inl h0
  · rcases hmax p hp h0 with hlt | ⟨heq, hle⟩
    · exact Or.inr (Or.inr (Or.inl hlt))
    · rcases lt_or_eq_of_le hle with hmlt | hmeq
      · exact Or.inr (Or.inr (Or.inr ⟨heq, hmlt⟩))
      · exact Or.inr (Or.inl ⟨heq, hmeq.symm⟩)

/-! ## Assembled sound tail-domination

This is now FULLY PROVEN (no `sorry`) under the correct hypothesis
`∃ x, S.density x ≠ 0` (the density is not identically zero).

The previous `topCoeffSum … ≠ 0` gaps are discharged by the finite reduction
`exists_reduced_right/left` above: the lexicographic-max nonzero *single*
component selected by `exists_lexMax_component_right/left` may belong to a group
of identical Gaussians (same `varSq` AND `mean`) whose coefficients SUM TO ZERO;
in that case the whole top group is deleted (which preserves the density exactly
and strictly shortens the component list), and the reduction recurses on the
shortened combination.  Because the density is not identically zero, the
recursion must terminate at a reduced combination whose lex-max group has a
nonzero coefficient sum — the empty combination has density `≡ 0`, contradicting
the hypothesis.  The original `S = [(1,G), (-1,G)]` counterexample to the OLD
hypothesis `∃ p ∈ S.components, p.1 ≠ 0` (density `≡ 0`) is correctly excluded by
`∃ x, S.density x ≠ 0`.

Everything in this file — the analytic little-o building blocks, the density
decomposition, the sign/magnitude domination glue, the finite reduction, and the
per-tail assembly — is fully proven and axiom-clean (no `sorry`, no use of the
FALSE-RISK `MaxVarianceGaussianTailEstimate` /
`MaxVarianceGaussianTailDominanceCoreMagnitude`).
-/

/-! ## Finite reduction: drop cancelling top groups until one survives

Under the correct hypothesis `∃ x, S.density x ≠ 0`, we can produce a reduced
combination `S'` (with the SAME density) and a dominant `G` such that the cover
hypothesis holds for `S'` AND the dominant group coefficient sum is nonzero.

The reduction repeatedly deletes the lexicographically-maximal Gaussian group
when its coefficient sum cancels to zero (which preserves the density and
strictly shortens the component list), terminating when the surviving lex-max
group has a nonzero coefficient sum.
-/

/-- Deleting a *cancelling* top group (coefficient sum zero) preserves density. -/
private theorem dropTop_density_eq_of_topCoeffSum_zero
    (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    (hzero : topCoeffSum Gdom S = 0) (x : ℝ) :
    (dropTop Gdom S).density x = S.density x := by
  rw [density_split S Gdom x, hzero, zero_mul, zero_add]

/-- Deleting a top group that contains a nonzero `isTop` component strictly
shortens the component list. -/
private theorem dropTop_length_lt
    (S : SignedGaussianCombination) (Gdom : GaussianPDF)
    {c : ℝ} (hmem : (c, Gdom) ∈ S.components) :
    (dropTop Gdom S).components.length < S.components.length := by
  classical
  -- the deleted predicate `¬ isTop Gdom` is FALSE on `(c, Gdom)`, so the filter
  -- strictly drops at least that element.
  have hp_top : isTop Gdom (c, Gdom) := ⟨rfl, rfl⟩
  have hp_false : ¬ (decide ¬ isTop Gdom (c, Gdom)) = true := by
    simp [hp_top]
  -- general fact: filtering a list that contains an element failing the predicate
  -- yields a strictly shorter list.
  have : (S.components.filter (fun p => decide ¬ isTop Gdom p)).length
      < S.components.length := by
    have hle := List.length_filter_le (fun p => decide ¬ isTop Gdom p) S.components
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      -- equal length forces the filter predicate to hold on every element
      have hall : ∀ p ∈ S.components, (fun p => decide ¬ isTop Gdom p) p = true := by
        have := (List.length_filter_eq_length_iff).mp h
        exact this
      exact hp_false (hall (c, Gdom) hmem)
  simpa [dropTop] using this

/-- **Core reduction (right tail).** From a density that is somewhere nonzero,
produce a reduced combination `S'` with the same density, together with a
dominant `G` whose group coefficient sum is nonzero and which covers `S'`. -/
private theorem exists_reduced_right :
    ∀ (n : ℕ) (S : SignedGaussianCombination),
      S.components.length ≤ n → (∃ x, S.density x ≠ 0) →
      ∃ (S' : SignedGaussianCombination) (G : GaussianPDF),
        (∀ x, S'.density x = S.density x) ∧
        (∀ p ∈ S'.components, p.1 = 0 ∨ isTop G p ∨ belowKeyRight G p) ∧
        topCoeffSum G S' ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro S hlen hS
      -- length ≤ 0 ⇒ empty ⇒ density ≡ 0, contradicting hS
      have hnil : S.components = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      exfalso
      obtain ⟨x, hx⟩ := hS
      apply hx
      apply density_zero_of_all_coeff_zero
      intro p hp; rw [hnil] at hp; exact absurd hp (List.not_mem_nil)
  | succ n ih =>
      intro S hlen hS
      obtain ⟨c, G, hmem, hc, hmax⟩ :=
        exists_lexMax_component_right S (exists_nonzero_coeff_of_density_ne S hS)
      have hcov := cover_right_of_lexMax S G hmax
      by_cases hA : topCoeffSum G S = 0
      · -- cancelling top group: drop it, density preserved, list shortens, recurse
        have hlt := dropTop_length_lt S G hmem
        have hlen' : (dropTop G S).components.length ≤ n := by omega
        have hS' : ∃ x, (dropTop G S).density x ≠ 0 := by
          obtain ⟨x, hx⟩ := hS
          exact ⟨x, by rw [dropTop_density_eq_of_topCoeffSum_zero S G hA x]; exact hx⟩
        obtain ⟨S', G', hdens', hcov', hA'⟩ := ih (dropTop G S) hlen' hS'
        refine ⟨S', G', ?_, hcov', hA'⟩
        intro x
        rw [hdens' x, dropTop_density_eq_of_topCoeffSum_zero S G hA x]
      · exact ⟨S, G, fun x => rfl, hcov, hA⟩

/-- **Core reduction (left tail).** Mirror of `exists_reduced_right` using the
left-tail lex order. -/
private theorem exists_reduced_left :
    ∀ (n : ℕ) (S : SignedGaussianCombination),
      S.components.length ≤ n → (∃ x, S.density x ≠ 0) →
      ∃ (S' : SignedGaussianCombination) (G : GaussianPDF),
        (∀ x, S'.density x = S.density x) ∧
        (∀ p ∈ S'.components, p.1 = 0 ∨ isTop G p ∨ belowKeyLeft G p) ∧
        topCoeffSum G S' ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro S hlen hS
      have hnil : S.components = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      exfalso
      obtain ⟨x, hx⟩ := hS
      apply hx
      apply density_zero_of_all_coeff_zero
      intro p hp; rw [hnil] at hp; exact absurd hp (List.not_mem_nil)
  | succ n ih =>
      intro S hlen hS
      obtain ⟨c, G, hmem, hc, hmax⟩ :=
        exists_lexMax_component_left S (exists_nonzero_coeff_of_density_ne S hS)
      have hcov := cover_left_of_lexMax S G hmax
      by_cases hA : topCoeffSum G S = 0
      · have hlt := dropTop_length_lt S G hmem
        have hlen' : (dropTop G S).components.length ≤ n := by omega
        have hS' : ∃ x, (dropTop G S).density x ≠ 0 := by
          obtain ⟨x, hx⟩ := hS
          exact ⟨x, by rw [dropTop_density_eq_of_topCoeffSum_zero S G hA x]; exact hx⟩
        obtain ⟨S', G', hdens', hcov', hA'⟩ := ih (dropTop G S) hlen' hS'
        refine ⟨S', G', ?_, hcov', hA'⟩
        intro x
        rw [hdens' x, dropTop_density_eq_of_topCoeffSum_zero S G hA x]
      · exact ⟨S, G, fun x => rfl, hcov, hA⟩

/-- The full sound right-tail existence (dominant chosen by lex-max). -/
theorem rightTail_sound (S : SignedGaussianCombination)
    (hS : ∃ x, S.density x ≠ 0) :
    ∃ (b' a' s' : ℝ), a' ≠ 0 ∧ 0 < s' ∧
      ∀ x : ℝ, x > b' →
        (S.density x).sign = a'.sign ∧
        |a'| * (1 / Real.sqrt (2 * Real.pi * s')) *
            Real.exp (-x ^ 2 / (2 * s')) < |S.density x| := by
  obtain ⟨S', G, hdens, hcov, hA⟩ :=
    exists_reduced_right S.components.length S le_rfl hS
  obtain ⟨b', hb'⟩ := SublemmaTailDominationRightCore S' G hcov hA
  refine ⟨b', topCoeffSum G S', G.varSq / 2, hA, by have := G.varSq_pos; linarith, ?_⟩
  intro x hx
  obtain ⟨hsign, hmag⟩ := hb' x hx
  rw [hdens x] at hsign hmag
  exact ⟨hsign, hmag⟩

/-- The full sound left-tail existence (dominant chosen by lex-max). -/
theorem leftTail_sound (S : SignedGaussianCombination)
    (hS : ∃ x, S.density x ≠ 0) :
    ∃ (b a s : ℝ), a ≠ 0 ∧ 0 < s ∧
      ∀ x : ℝ, x < b →
        (S.density x).sign = a.sign ∧
        |a| * (1 / Real.sqrt (2 * Real.pi * s)) *
            Real.exp (-x ^ 2 / (2 * s)) < |S.density x| := by
  obtain ⟨S', G, hdens, hcov, hA⟩ :=
    exists_reduced_left S.components.length S le_rfl hS
  obtain ⟨b, hb⟩ := SublemmaTailDominationLeftCore S' G hcov hA
  refine ⟨b, topCoeffSum G S', G.varSq / 2, hA, by have := G.varSq_pos; linarith, ?_⟩
  intro x hx
  obtain ⟨hsign, hmag⟩ := hb x hx
  rw [hdens x] at hsign hmag
  exact ⟨hsign, hmag⟩

/-- **Assembled sound tail-domination** (target shape of `SublemmaTailDomination`).
Both tails combined; thresholds `b < b'` produced by shifting the per-tail
thresholds apart.  Modulo the two `topCoeffSum ≠ 0` sorries documented above,
this is fully Mathlib- and proven-lemma-only and uses NO false axioms. -/
theorem SublemmaTailDominationSound
    (S : SignedGaussianCombination)
    (hS : ∃ x, S.density x ≠ 0) :
    ∃ (b b' a a' s s' : ℝ),
      b < b' ∧ a ≠ 0 ∧ a' ≠ 0 ∧ 0 < s ∧ 0 < s' ∧
      (∀ x : ℝ, x < b →
        (S.density x).sign = a.sign ∧
        |a| * (1 / Real.sqrt (2 * Real.pi * s)) *
            Real.exp (-x ^ 2 / (2 * s)) < |S.density x|) ∧
      (∀ x : ℝ, x > b' →
        (S.density x).sign = a'.sign ∧
        |a'| * (1 / Real.sqrt (2 * Real.pi * s')) *
            Real.exp (-x ^ 2 / (2 * s')) < |S.density x|) := by
  obtain ⟨bL, a, s, ha, hs, hL⟩ := leftTail_sound S hS
  obtain ⟨bR, a', s', ha', hs', hR⟩ := rightTail_sound S hS
  -- shift thresholds apart so the left threshold is strictly below the right one
  have hlt : min bL bR - 1 < max bL bR + 1 := by
    have h1 : min bL bR ≤ max bL bR := min_le_max
    linarith
  refine ⟨min bL bR - 1, max bL bR + 1, a, a', s, s', hlt, ha, ha', hs, hs', ?_, ?_⟩
  · intro x hx
    have hxbL : x < bL := by
      have : min bL bR ≤ bL := min_le_left _ _
      linarith
    exact hL x hxbL
  · intro x hx
    have hxbR : x > bR := by
      have : bR ≤ max bL bR := le_max_right _ _
      linarith
    exact hR x hxbR

end Workspace.ProofLemmas
