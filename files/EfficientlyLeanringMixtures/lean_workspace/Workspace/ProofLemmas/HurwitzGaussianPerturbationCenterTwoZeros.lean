import Mathlib
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianPDF

namespace Workspace.ProofLemmas

/-!
# Region (c) of Moitra–Valiant §6.1 — the "inner region" ≤2-zeros core

## Natural-language decomposition

We must show: for `h = g + a_k·N(μ_k, v)` with `g` analytic and a small,
near-delta Gaussian bump centred at `μ_k`, the number of zeros of `h` in the
*inner* interval `Ioo (μ_k − δ) (μ_k + δ)` is at most `2`.

The faithful structure is a THREE-region inner split with a **v-dependent** inner
radius `β(v) = √(v · log(1/v) / 2)`:

* central band `(μ_k − β(v), μ_k + β(v))` — here the bump VALUE dominates `max|g|`,
  so `h ≠ 0`.  The crucial scaling: at the band edge the bump value is
  `(1/√(2πv))·exp(−β(v)²/(2v)) = v^{−1/4}/√(2π) → ∞`, so for small `v` it exceeds
  the (fixed) bound `max|g|` on the window;
* left flank `[μ_k − δ, μ_k − β(v)]` and right flank `[μ_k + β(v), μ_k + δ]` —
  here the bump DERIVATIVE dominates `max|g'|` (at the inner edge the bump
  derivative is `v^{−3/4}·√(log(1/v)/2)/√(2π) → ∞`), so `deriv h` is sign-definite
  and `h` is strictly monotone ⇒ ≤1 zero per flank.

Total: ≤1 (left flank) + 0 (band) + ≤1 (right flank) = ≤2 zeros on
`Ioo (μ_k − δ) (μ_k + δ)`.

### Why `β` must depend on `v` (correction to a prior FALSE statement)

The earlier version of `centerWindowThreeRegion` fixed `β` OUTSIDE the `∀ v`
quantifier.  That statement is FALSE: at a fixed distance `β` from `μ_k` the
Gaussian value `(1/√(2πv))·exp(−β²/(2v)) → 0` as `v → 0⁺` (it is the tail, not
the peak — the peak `1/√(2πv)` lives within `O(√v)` of `μ_k`, which shrinks below
any fixed `β`).  Counterexample to the band clause: `g(x) = x − μ_k`, `a_k = 1`,
gives `h(μ_k − β) → −β < 0` while `h(μ_k) = 1/√(2πv) > 0`, so IVT forces a zero
in the band.  Making `β = β(v)` shrink (but more slowly than the peak width `√v`)
fixes this: `√v ≪ β(v) ≪ 1`, so the spike fills the band.

## Sub-lemmas

* **(C-core) `unimodalOn_encard_zeros_le_two`** — pure real analysis.
* **(C-mirror) `antiThenMonoOn_encard_zeros_le_two`** — the mirror image.
* **(C-split) `innerSplit_encard_zeros_le_two`** — the three-region assembler.
* **(C-shape) `centerWindowThreeRegion`** — the analytic content, with the
  v-dependent band radius.
* **(C-assemble) the main theorem** — combine.
-/

open Set

/--
**(C-core)** A real function that is strictly increasing on `[a, c]` and strictly
decreasing on `[c, b]` has at most two zeros in the open interval `(a, b)`.
-/
theorem unimodalOn_encard_zeros_le_two
    {f : ℝ → ℝ} {a c b : ℝ}
    (hmono : StrictMonoOn f (Set.Icc a c))
    (hanti : StrictAntiOn f (Set.Icc c b)) :
    {x ∈ Set.Ioo a b | f x = 0}.encard ≤ 2 := by
  -- The zero set inside (a,b) is covered by its intersections with [a,c] and [c,b].
  -- On each of those, f is injective, so at most one zero lives there.
  set Z : Set ℝ := {x ∈ Set.Ioo a b | f x = 0} with hZ
  set Z₁ : Set ℝ := {x ∈ Set.Icc a c | f x = 0} with hZ₁
  set Z₂ : Set ℝ := {x ∈ Set.Icc c b | f x = 0} with hZ₂
  -- Cover: Z ⊆ Z₁ ∪ Z₂.
  have hcover : Z ⊆ Z₁ ∪ Z₂ := by
    intro x hx
    obtain ⟨hxIoo, hxf⟩ := hx
    rcases le_total x c with hxc | hxc
    · exact Or.inl ⟨⟨le_of_lt hxIoo.1, hxc⟩, hxf⟩
    · exact Or.inr ⟨⟨hxc, le_of_lt hxIoo.2⟩, hxf⟩
  -- Each piece is a subsingleton (injectivity from strict monotonicity).
  have hZ₁_sub : Z₁.Subsingleton := by
    intro x hx y hy
    have hxmem : x ∈ Set.Icc a c := hx.1
    have hymem : y ∈ Set.Icc a c := hy.1
    have hfx : f x = f y := by rw [hx.2, hy.2]
    exact hmono.injOn hxmem hymem hfx
  have hZ₂_sub : Z₂.Subsingleton := by
    intro x hx y hy
    have hxmem : x ∈ Set.Icc c b := hx.1
    have hymem : y ∈ Set.Icc c b := hy.1
    have hfx : f x = f y := by rw [hx.2, hy.2]
    exact hanti.injOn hxmem hymem hfx
  have hZ₁_le : Z₁.encard ≤ 1 := Set.encard_le_one_iff_subsingleton.mpr hZ₁_sub
  have hZ₂_le : Z₂.encard ≤ 1 := Set.encard_le_one_iff_subsingleton.mpr hZ₂_sub
  calc Z.encard ≤ (Z₁ ∪ Z₂).encard := Set.encard_le_encard hcover
    _ ≤ Z₁.encard + Z₂.encard := Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add hZ₁_le hZ₂_le
    _ = 2 := by norm_num

/--
**(C-mirror)** The mirror image of `unimodalOn_encard_zeros_le_two`.
-/
theorem antiThenMonoOn_encard_zeros_le_two
    {f : ℝ → ℝ} {a c b : ℝ}
    (hanti : StrictAntiOn f (Set.Icc a c))
    (hmono : StrictMonoOn f (Set.Icc c b)) :
    {x ∈ Set.Ioo a b | f x = 0}.encard ≤ 2 := by
  -- `-f` is mono on [a,c] and anti on [c,b]; its zero set equals f's.
  have hmono' : StrictMonoOn (fun x => -f x) (Set.Icc a c) := by
    intro x hx y hy hxy
    simpa using neg_lt_neg (hanti hx hy hxy)
  have hanti' : StrictAntiOn (fun x => -f x) (Set.Icc c b) := by
    intro x hx y hy hxy
    simpa using neg_lt_neg (hmono hx hy hxy)
  have hzeros : {x ∈ Set.Ioo a b | (fun x => -f x) x = 0}
      = {x ∈ Set.Ioo a b | f x = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, neg_eq_zero]
  have := unimodalOn_encard_zeros_le_two hmono' hanti'
  rwa [hzeros] at this

/--
**(C-split)** The FAITHFUL inner-region ≤2-zeros assembler (Moitra–Valiant
§6.1).  The window `(a, b)` (with `a < l ≤ r < b`) is split into three pieces:

* a left flank `[a, l]` where `h` is strictly monotone (≤1 zero);
* a middle band `(l, r)` where `h` is sign-definite / nonzero — NO zeros;
* a right flank `[r, b]` where `h` is strictly monotone (≤1 zero).

Total: ≤ 2 zeros in `(a, b)`.  Mathlib-only.  Orientation of the two flanks is
irrelevant here (each is handled by injectivity from strict mono OR strict anti).
-/
theorem innerSplit_encard_zeros_le_two
    {f : ℝ → ℝ} {a l r b : ℝ}
    (_hlr : l ≤ r)
    (hleft : StrictMonoOn f (Set.Icc a l) ∨ StrictAntiOn f (Set.Icc a l))
    (hmid : ∀ x ∈ Set.Ioo l r, f x ≠ 0)
    (hright : StrictMonoOn f (Set.Icc r b) ∨ StrictAntiOn f (Set.Icc r b)) :
    {x ∈ Set.Ioo a b | f x = 0}.encard ≤ 2 := by
  set Z : Set ℝ := {x ∈ Set.Ioo a b | f x = 0} with hZ
  set Z₁ : Set ℝ := {x ∈ Set.Icc a l | f x = 0} with hZ₁
  set Z₂ : Set ℝ := {x ∈ Set.Icc r b | f x = 0} with hZ₂
  -- Cover: every zero in (a,b) lies in [a,l] or [r,b] (the open middle has no zeros).
  have hcover : Z ⊆ Z₁ ∪ Z₂ := by
    intro x hx
    obtain ⟨hxIoo, hxf⟩ := hx
    rcases le_or_gt x l with hxl | hxl
    · exact Or.inl ⟨⟨le_of_lt hxIoo.1, hxl⟩, hxf⟩
    · rcases le_or_gt r x with hxr | hxr
      · exact Or.inr ⟨⟨hxr, le_of_lt hxIoo.2⟩, hxf⟩
      · exact absurd hxf (hmid x ⟨hxl, hxr⟩)
  -- Each flank piece is a subsingleton (injectivity from strict monotonicity).
  have flank_sub : ∀ (s : Set ℝ), (StrictMonoOn f s ∨ StrictAntiOn f s) →
      {x ∈ s | f x = 0}.Subsingleton := by
    intro s hs x hx y hy
    have hfx : f x = f y := by rw [hx.2, hy.2]
    rcases hs with hmono | hanti
    · exact hmono.injOn hx.1 hy.1 hfx
    · exact hanti.injOn hx.1 hy.1 hfx
  have hZ₁_le : Z₁.encard ≤ 1 :=
    Set.encard_le_one_iff_subsingleton.mpr (flank_sub _ hleft)
  have hZ₂_le : Z₂.encard ≤ 1 :=
    Set.encard_le_one_iff_subsingleton.mpr (flank_sub _ hright)
  calc Z.encard ≤ (Z₁ ∪ Z₂).encard := Set.encard_le_encard hcover
    _ ≤ Z₁.encard + Z₂.encard := Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add hZ₁_le hZ₂_le
    _ = 2 := by norm_num

/--
Derivative of the (un-normalised) Gaussian exponential bump.
`d/dx exp(-(x-μ)²/(2v)) = exp(-(x-μ)²/(2v)) · (-(x-μ)/v)`.
-/
theorem bump_exp_hasDerivAt (μ v : ℝ) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun y => Real.exp (-(y - μ) ^ 2 / (2 * v)))
      (Real.exp (-(x - μ) ^ 2 / (2 * v)) * (-(x - μ) / v)) x := by
  have h1 : HasDerivAt (fun y => -(y - μ) ^ 2 / (2 * v)) (-(x - μ) / v) x := by
    have hpow : HasDerivAt (fun y => -(y - μ) ^ 2 / (2 * v))
        ((-(2 * (x - μ) ^ 1 * 1)) / (2 * v)) x := by
      apply HasDerivAt.div_const
      apply HasDerivAt.neg
      exact ((hasDerivAt_id x).sub_const μ).pow 2
    convert hpow using 1
    field_simp
  have := (Real.hasDerivAt_exp (-(x - μ) ^ 2 / (2 * v))).comp x h1
  simpa [Function.comp] using this

/-- The Gaussian density `GaussianPDF.density ⟨μ, v, hv⟩` has a derivative at every
point, equal to `density · (-(x-μ)/v)`.  This is `N'(μ,v,x) = -(x-μ)/v · N(μ,v,x)`. -/
theorem density_hasDerivAt (μ v : ℝ) (hv : 0 < v) (x : ℝ) :
    HasDerivAt (Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ, v, hv⟩)
      (Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ, v, hv⟩ x * (-(x - μ) / v)) x := by
  have hc := (bump_exp_hasDerivAt μ v (ne_of_gt hv) x).const_mul
    (1 / Real.sqrt (2 * Real.pi * v))
  have heq : (Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ, v, hv⟩)
      = fun y => (1 / Real.sqrt (2 * Real.pi * v))
          * Real.exp (-(y - μ) ^ 2 / (2 * v)) := by
    funext y
    simp only [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  rw [heq]
  convert hc using 1
  ring

/-- The perturbed function `h = g + a_k·N(μ_k, v, ·)` is differentiable everywhere. -/
theorem center_h_differentiable
    (g : ℝ → ℝ) (hg : AnalyticOnNhd ℝ g Set.univ)
    (a_k μ_k v : ℝ) (hv : 0 < v) :
    Differentiable ℝ
      (fun x => g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x) := by
  have hg_diff : Differentiable ℝ g := by
    intro x
    exact (hg x (Set.mem_univ x)).differentiableAt
  have hdens_diff : Differentiable ℝ
      (Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩) := by
    intro x
    exact (density_hasDerivAt μ_k v hv x).differentiableAt
  exact fun x => (hg_diff x).add ((hdens_diff x).const_mul a_k)

/-! ### The v-dependent band radius `β(v) = √(v · log(1/v) / 2)` and its bookkeeping -/

/-- The band radius. -/
noncomputable def bandRadius (v : ℝ) : ℝ := Real.sqrt (v * Real.log (1 / v) / 2)

/-- For `0 < v < 1`, the band radius is strictly positive. -/
theorem bandRadius_pos {v : ℝ} (hv : 0 < v) (hv1 : v < 1) : 0 < bandRadius v := by
  unfold bandRadius
  apply Real.sqrt_pos.mpr
  have hlog : 0 < Real.log (1 / v) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hv]; linarith
  positivity

/-- A clean upper bound on the band radius near `0`: for `0 < v < 1`,
`bandRadius v < v^{1/4}` (since `log(1/v) < 2/√v`, hence `β² = v·log(1/v)/2 < √v`). -/
theorem bandRadius_lt_rpow {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    bandRadius v < v ^ ((1:ℝ)/4) := by
  -- log(1/v) < 2/√v.
  have hsqrt_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  -- log(1/√v) ≤ 1/√v - 1 < 1/√v, and log(1/v) = 2·log(1/√v).
  have hlog_half : Real.log (1 / v) = 2 * Real.log (1 / Real.sqrt v) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_sqrt (le_of_lt hv)]
    ring
  have hlog_lt : Real.log (1 / Real.sqrt v) < 1 / Real.sqrt v := by
    have h1 : Real.log (1 / Real.sqrt v) ≤ 1 / Real.sqrt v - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hlogv_lt : Real.log (1 / v) < 2 / Real.sqrt v := by
    rw [hlog_half]
    have : 2 * Real.log (1 / Real.sqrt v) < 2 * (1 / Real.sqrt v) := by
      linarith [hlog_lt]
    rw [mul_one_div] at this
    linarith
  -- β² = v·log(1/v)/2 < v·(2/√v)/2 = v/√v = √v.
  have hlogpos : 0 < Real.log (1 / v) := by
    apply Real.log_pos; rw [lt_div_iff₀ hv]; linarith
  have hbsq_lt : v * Real.log (1 / v) / 2 < Real.sqrt v := by
    have hstep : v * Real.log (1 / v) < v * (2 / Real.sqrt v) :=
      mul_lt_mul_of_pos_left hlogv_lt hv
    have hvsv : v * (2 / Real.sqrt v) = 2 * Real.sqrt v := by
      have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt (le_of_lt hv)
      field_simp
      nlinarith [hsq, hsqrt_pos]
    rw [hvsv] at hstep
    linarith
  -- so β = √(β²) < √(√v) = v^{1/4}.
  have hnn : 0 ≤ v * Real.log (1 / v) / 2 := by positivity
  unfold bandRadius
  have hsv_lt : Real.sqrt (v * Real.log (1 / v) / 2) < Real.sqrt (Real.sqrt v) :=
    Real.sqrt_lt_sqrt hnn hbsq_lt
  have hrw : Real.sqrt (Real.sqrt v) = v ^ ((1:ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hv)]
    norm_num
  rwa [hrw] at hsv_lt

/-- For any `δ > 0` there is a `vδ > 0` so that `bandRadius v < δ` for all `v ∈ (0, vδ]`.
Use `bandRadius v < v^{1/4}` and pick `vδ = min (1/2) (δ⁴)`. -/
theorem bandRadius_lt_of_small {δ : ℝ} (hδ : 0 < δ) :
    ∃ vδ : ℝ, 0 < vδ ∧ ∀ (v : ℝ), 0 < v → v ≤ vδ → bandRadius v < δ := by
  refine ⟨min (1/2) (δ ^ 4), lt_min (by norm_num) (by positivity), ?_⟩
  intro v hv hvle
  have hv2 : v ≤ 1/2 := le_trans hvle (min_le_left _ _)
  have hvδ4 : v ≤ δ ^ 4 := le_trans hvle (min_le_right _ _)
  have hv1 : v < 1 := by linarith
  -- bandRadius v < v^{1/4} ≤ (δ⁴)^{1/4} = δ.
  have h1 := bandRadius_lt_rpow hv hv1
  have h2 : v ^ ((1:ℝ)/4) ≤ (δ ^ 4) ^ ((1:ℝ)/4) :=
    Real.rpow_le_rpow (le_of_lt hv) hvδ4 (by norm_num)
  have h3 : (δ ^ 4) ^ ((1:ℝ)/4) = δ := by
    rw [← Real.rpow_natCast δ 4, ← Real.rpow_mul (le_of_lt hδ)]
    norm_num
  rw [h3] at h2
  linarith

/-- **`v ≪ β(v)` comparison.**  For any `K ≥ 0` there is a threshold `v₀ ∈ (0,1)` so
that `K·v < bandRadius v` for all `v ∈ (0, v₀]`.  This encodes that the band radius
`β(v) = √(v·log(1/v)/2)` shrinks strictly slower than `v` (since
`β(v)/v = √(log(1/v)/(2v)) → ∞`).  Proof: it suffices that `2K²v < log(1/v)`, and
for `v ≤ min(e⁻¹, 1/(2K²+1))` we have `2K²v < 1 ≤ log(1/v)`. -/
theorem cmp_aux (K : ℝ) (hK : 0 ≤ K) :
    ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ < 1 ∧ ∀ v, 0 < v → v ≤ v₀ → K * v < bandRadius v := by
  refine ⟨min (Real.exp (-1)) (1 / (2 * K ^ 2 + 1)), by positivity, ?_, ?_⟩
  · calc min (Real.exp (-1)) (1 / (2 * K ^ 2 + 1)) ≤ Real.exp (-1) := min_le_left _ _
      _ < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  · intro v hv hvle
    have hve : v ≤ Real.exp (-1) := le_trans hvle (min_le_left _ _)
    have hvk : v ≤ 1 / (2 * K ^ 2 + 1) := le_trans hvle (min_le_right _ _)
    have hlog1 : (1 : ℝ) ≤ Real.log (1 / v) := by
      rw [one_div, Real.log_inv]
      have : Real.log v ≤ Real.log (Real.exp (-1)) := Real.log_le_log hv hve
      rw [Real.log_exp] at this; linarith
    have hden : 0 < 2 * K ^ 2 + 1 := by positivity
    have h2k : 2 * K ^ 2 * v < 1 := by
      rw [le_div_iff₀ hden] at hvk
      nlinarith [sq_nonneg K]
    have hbr : bandRadius v = Real.sqrt (v * Real.log (1 / v) / 2) := rfl
    rw [hbr, show K * v = Real.sqrt ((K * v) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith [hlog1, h2k, hv, sq_nonneg K]

/-- The defining identity at the band edge: `exp(−β(v)²/(2v)) = v^{1/4}` for `0 < v < 1`.
    Stated as `exp(−β²/(2v)) = √(√v)` (= `v^{1/4}`). -/
theorem exp_at_bandRadius {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    Real.exp (-(bandRadius v) ^ 2 / (2 * v)) = Real.sqrt (Real.sqrt v) := by
  unfold bandRadius
  have hlogpos : 0 < Real.log (1 / v) := by
    apply Real.log_pos; rw [lt_div_iff₀ hv]; linarith
  have hnn : 0 ≤ v * Real.log (1 / v) / 2 := by positivity
  rw [Real.sq_sqrt hnn]
  -- -(v·log(1/v)/2)/(2v) = -log(1/v)/4 = log v / 4
  have hlog_inv : Real.log (1 / v) = - Real.log v := by
    rw [one_div, Real.log_inv]
  have hexp_arg : -(v * Real.log (1 / v) / 2) / (2 * v) = Real.log v / 4 := by
    rw [hlog_inv]
    field_simp
    ring
  rw [hexp_arg]
  -- exp(log v / 4) = (exp(log v))^{1/4} ... use rpow
  have hvpos : (0:ℝ) < v := hv
  -- √(√v) = v^{1/4} = exp((1/4) log v)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hvpos)]
  rw [Real.rpow_def_of_pos hvpos]
  congr 1
  ring

/-- Inside the band `|x − μ_k| < β(v)`, the Gaussian density value exceeds its
band-edge value `v^{−1/4}/√(2π)`.  Stated as `density x ≥ (1/√(2πv))·√(√v)`
(= `v^{−1/4}/√(2π)`).  Uses that `exp` is decreasing in `(x−μ_k)²`. -/
theorem density_ge_on_band {μ_k v : ℝ} (hv : 0 < v) (hv1 : v < 1)
    {x : ℝ} (hx : x ∈ Set.Ioo (μ_k - bandRadius v) (μ_k + bandRadius v)) :
    (1 / Real.sqrt (2 * Real.pi * v)) * Real.sqrt (Real.sqrt v)
      ≤ Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x := by
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  simp only []
  have hcoef_pos : 0 < 1 / Real.sqrt (2 * Real.pi * v) := by
    apply div_pos one_pos
    apply Real.sqrt_pos.mpr
    have : 0 < 2 * Real.pi := by positivity
    positivity
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hcoef_pos)
  rw [← exp_at_bandRadius hv hv1]
  apply Real.exp_le_exp.mpr
  -- need: -(bandRadius v)²/(2v) ≤ -(x-μ_k)²/(2v), i.e. (x-μ_k)² ≤ (bandRadius v)²
  have hbr : 0 < bandRadius v := bandRadius_pos hv hv1
  have hdist : |x - μ_k| < bandRadius v := by
    rw [abs_lt]
    constructor
    · have := hx.1; linarith
    · have := hx.2; linarith
  have hsq : (x - μ_k) ^ 2 < (bandRadius v) ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_lt.mp hdist |>.1] : -(bandRadius v) < x - μ_k)
      (by linarith [abs_lt.mp hdist |>.2] : x - μ_k < bandRadius v)
    exact this
  have h2v : 0 < 2 * v := by linarith
  rw [neg_div, neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_right (le_of_lt hsq) (le_of_lt h2v)

/-- The band-edge bump value `(1/√(2πv))·√(√v) = v^{−1/4}/√(2π)` exceeds any fixed
threshold `M` for `v` small enough.  Explicit: it suffices that
`0 < v ≤ v₀` with `v₀ = min (1/2) ((1/(M·√(2π)+1))^4)` (and `M ≥ 0`). -/
theorem bandEdgeValue_gt {M : ℝ} (hM : 0 ≤ M) :
    ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ < 1 ∧ ∀ {v : ℝ}, 0 < v → v ≤ v₀ →
      M < (1 / Real.sqrt (2 * Real.pi * v)) * Real.sqrt (Real.sqrt v) := by
  set s : ℝ := Real.sqrt (2 * Real.pi) with hs
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  -- threshold on v^{1/4}: need v^{1/4} < 1/((M+1)·s)
  set c : ℝ := 1 / ((M + 1) * s) with hc
  have hc_pos : 0 < c := by
    apply div_pos one_pos
    have : 0 < M + 1 := by linarith
    positivity
  refine ⟨min (1/2) (c ^ 4), ?_, ?_, ?_⟩
  · apply lt_min
    · norm_num
    · positivity
  · calc min (1/2) (c ^ 4) ≤ (1:ℝ)/2 := min_le_left _ _
      _ < 1 := by norm_num
  · intro v hv hvle
    have hv2 : v ≤ 1/2 := le_trans hvle (min_le_left _ _)
    have hvc4 : v ≤ c ^ 4 := le_trans hvle (min_le_right _ _)
    have hv1 : v < 1 := by linarith
    -- rewrite the product as v^{-1/4}/s
    have hsqrt2piv : Real.sqrt (2 * Real.pi * v) = s * Real.sqrt v := by
      rw [hs, ← Real.sqrt_mul (by positivity)]
    rw [hsqrt2piv]
    have hsv_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
    have hssv_pos : 0 < Real.sqrt (Real.sqrt v) := Real.sqrt_pos.mpr hsv_pos
    -- v^{1/4} ≤ c  (from v ≤ c^4): use rpow algebra
    have hquarter : Real.sqrt (Real.sqrt v) ≤ c := by
      -- √(√v) = v^{1/4}, and v ≤ c^4 ⇒ v^{1/4} ≤ c
      have hrw : Real.sqrt (Real.sqrt v) = v ^ ((1:ℝ)/4) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hv)]
        norm_num
      rw [hrw]
      have : v ^ ((1:ℝ)/4) ≤ (c ^ 4) ^ ((1:ℝ)/4) := by
        apply Real.rpow_le_rpow (le_of_lt hv) hvc4 (by norm_num)
      rw [← Real.rpow_natCast c 4, ← Real.rpow_mul (le_of_lt hc_pos)] at this
      simpa using this
    -- Key: (1/(s√v))·√(√v) = 1/(s·√(√v)), and s·√(√v) ≤ s·c = 1/(M+1).
    have hsqv : Real.sqrt v = Real.sqrt (Real.sqrt v) * Real.sqrt (Real.sqrt v) := by
      rw [Real.mul_self_sqrt (le_of_lt hsv_pos)]
    have hprod_eq : 1 / (s * Real.sqrt v) * Real.sqrt (Real.sqrt v)
        = 1 / (s * Real.sqrt (Real.sqrt v)) := by
      set w : ℝ := Real.sqrt (Real.sqrt v) with hw
      have hww : Real.sqrt v = w * w := hsqv
      rw [hww]
      rw [one_div, one_div, mul_inv, mul_inv]
      field_simp
    rw [hprod_eq]
    -- s·√(√v) ≤ 1/(M+1)
    have hsc : s * Real.sqrt (Real.sqrt v) ≤ 1 / (M + 1) := by
      have : s * Real.sqrt (Real.sqrt v) ≤ s * c :=
        mul_le_mul_of_nonneg_left hquarter (le_of_lt hs_pos)
      have hsc_eq : s * c = 1 / (M + 1) := by
        rw [hc]; field_simp
      linarith [hsc_eq ▸ this]
    -- so 1/(s√(√v)) ≥ M+1 > M
    have hden_pos : 0 < s * Real.sqrt (Real.sqrt v) := by positivity
    have hMp1 : 0 < M + 1 := by linarith
    have : M + 1 ≤ 1 / (s * Real.sqrt (Real.sqrt v)) := by
      rw [le_div_iff₀ hden_pos]
      calc (M + 1) * (s * Real.sqrt (Real.sqrt v))
          ≤ (M + 1) * (1 / (M + 1)) :=
            mul_le_mul_of_nonneg_left hsc (le_of_lt hMp1)
        _ = 1 := by field_simp
    linarith

/-! ### Band non-vanishing on a fixed window (FULLY PROVED, Mathlib-only)

For ANY fixed window radius `δ > 0`, there is a `v₀ > 0` so that for `v ∈ (0, v₀]`
the v-dependent band `(μ_k − β(v), μ_k + β(v))` (with `β(v) = bandRadius v`) sits
inside the window and is ZERO-FREE for `h = g + a_k·N(μ_k,v,·)`: the bump VALUE
`≥ (1/√(2πv))·√(√v) = v^{−1/4}/√(2π)` dominates `max_{window} |g|/|a_k|`
(`density_ge_on_band` + `bandEdgeValue_gt`), so `|a_k·N| > |g|` ⇒ `h ≠ 0`.

This is the genuine fix over the prior (FALSE) fixed-`β` statement: making
`β = β(v)` shrink slower than the peak width `√v` lets the spike fill the band. -/
theorem bandZeroFree
    (g : ℝ → ℝ) (hg : AnalyticOnNhd ℝ g Set.univ)
    (a_k : ℝ) (ha_k : a_k ≠ 0) (μ_k : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v₀ : ℝ, 0 < v₀ ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
        bandRadius v < δ ∧
        (∀ x ∈ Set.Ioo (μ_k - bandRadius v) (μ_k + bandRadius v),
          g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x ≠ 0) := by
  -- `g` is continuous, hence bounded on the compact window `[μ_k−δ, μ_k+δ]`.
  have hg_cont : Continuous g := by
    have : Differentiable ℝ g := fun x => (hg x (Set.mem_univ x)).differentiableAt
    exact this.continuous
  obtain ⟨Mg, hMg⟩ :
      ∃ Mg : ℝ, ∀ x ∈ Set.Icc (μ_k - δ) (μ_k + δ), |g x| ≤ Mg := by
    have hne : (Set.Icc (μ_k - δ) (μ_k + δ)).Nonempty :=
      Set.nonempty_Icc.mpr (by linarith)
    obtain ⟨x₀, _hx₀mem, hx₀⟩ :=
      (isCompact_Icc (a := μ_k - δ) (b := μ_k + δ)).exists_isMaxOn hne
        (f := fun x => |g x|) (hg_cont.abs.continuousOn)
    exact ⟨|g x₀|, fun x hx => hx₀ hx⟩
  -- Threshold so the band-edge bump value beats `max|g| / |a_k|`.
  have hMpos : 0 ≤ Mg / |a_k| := by
    have h0 : 0 ≤ Mg := le_trans (abs_nonneg _) (hMg μ_k (by constructor <;> linarith))
    positivity
  obtain ⟨vB, hvB_pos, hvB_lt1, hvB⟩ := bandEdgeValue_gt hMpos
  -- Also need β(v) < δ; β(v) = √(v·log(1/v)/2) → 0, so a `v₀` clearing it exists.
  -- We pick `v₀ = min vB δ²` (crude bound `β(v) ≤ √(v/2)·√(log(1/v))`; for the
  -- statement we only need `β(v) < δ`, handled per-`v` below using `v ≤ δ²/2` when
  -- `δ ≤ 1` and the `β < 1` bound otherwise).  Simplest: shrink `v₀` so that
  -- `v·log(1/v)/2 < δ²`.  Use `log(1/v) ≤ 1/v - 1 < 1/v` ⇒ `v·log(1/v) < 1`; for
  -- `δ ≥ 1` that already gives `β < 1 ≤ δ`.  For `δ < 1` we additionally cap
  -- `v ≤ δ⁴` so that `v·log(1/v) ≤ v·(1/v) = 1`… that is too weak; instead cap
  -- `v` so `v·log(1/v) < δ²` directly via monotonicity near 0.  We avoid the
  -- delicate analysis by using `bandRadius_lt_of_small` below.
  obtain ⟨vδ, hvδ_pos, hvδ⟩ := bandRadius_lt_of_small (δ := δ) hδ
  refine ⟨min vB vδ, lt_min hvB_pos hvδ_pos, ?_⟩
  intro v hv hvle
  have hvleB : v ≤ vB := le_trans hvle (min_le_left _ _)
  have hvleδ : v ≤ vδ := le_trans hvle (min_le_right _ _)
  have hv1 : v < 1 := lt_of_le_of_lt hvleB hvB_lt1
  have hβlt : bandRadius v < δ := hvδ v hv hvleδ
  refine ⟨hβlt, ?_⟩
  -- BAND non-vanishing: |a_k·N| > |g| on (μ_k−β, μ_k+β).
  intro x hx
  show g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x ≠ 0
  have hxmem : x ∈ Set.Icc (μ_k - δ) (μ_k + δ) := by
    constructor <;> [linarith [hx.1, hβlt]; linarith [hx.2, hβlt]]
  have hgx : |g x| ≤ Mg := hMg x hxmem
  have hak_pos : 0 < |a_k| := abs_pos.mpr ha_k
  -- bump value ≥ band-edge value > Mg/|a_k|
  have hdens_ge := density_ge_on_band hv hv1 (μ_k := μ_k) (x := x) hx
  have hedge := hvB hv hvleB
  have hdens_gt : Mg / |a_k| <
      Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x :=
    lt_of_lt_of_le hedge hdens_ge
  have hdens_pos : 0 < Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x :=
    lt_of_le_of_lt hMpos hdens_gt
  have habsN : |a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x|
      = |a_k| * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x := by
    rw [abs_mul, abs_of_pos hdens_pos]
  have hgt : |g x| < |a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x| := by
    rw [habsN]
    have hMgN : Mg < Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x * |a_k| :=
      (div_lt_iff₀ hak_pos).mp hdens_gt
    have : Mg < |a_k| * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x := by
      rw [mul_comm]; exact hMgN
    linarith [hgx]
  intro hzero
  have heq : a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = - g x := by
    linarith [hzero]
  rw [heq, abs_neg] at hgt
  exact (lt_irrefl (|g x|)) hgt

/-! ### The per-flank ≤1-zero engine (φ = h/N monotonicity)

The zeros of `h = g + a_k·N(μ_k,v,·)` coincide (since `N>0`) with the zeros of
`H(x) = g(x)·exp((x−μ_k)²/(2v)) + a_k/√(2πv)`, because
`h(x)·exp((x−μ_k)²/(2v)) = H(x)`.  Its derivative is
`H'(x) = exp((x−μ_k)²/(2v)) · (deriv g x + g x·(x−μ_k)/v)
       = exp((x−μ_k)²/(2v))/v · ψ(x)`, where `ψ(x) = v·deriv g x + (x−μ_k)·g x`.
So whenever `ψ` is sign-definite on an interval, `H` is strictly monotone there,
hence injective, so `h` has at most one zero on it. -/

/-- `H(x) = g(x)·exp((x−μ_k)²/(2v)) + C` has derivative
`deriv g x · exp(..) + g x · (exp(..) · (x−μ_k)/v)` everywhere. -/
theorem flankH_hasDerivAt
    (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (μ_k v C : ℝ) (x : ℝ) :
    HasDerivAt (fun y => g y * Real.exp ((y - μ_k) ^ 2 / (2 * v)) + C)
      (deriv g x * Real.exp ((x - μ_k) ^ 2 / (2 * v))
        + g x * (Real.exp ((x - μ_k) ^ 2 / (2 * v)) * ((x - μ_k) / v))) x := by
  have h1 : HasDerivAt (fun y => (y - μ_k) ^ 2 / (2 * v)) ((x - μ_k) / v) x := by
    have h0 : HasDerivAt (fun y => (y - μ_k) ^ 2 / (2 * v))
        ((2 * (x - μ_k) ^ 1 * 1) / (2 * v)) x := by
      apply HasDerivAt.div_const
      exact ((hasDerivAt_id x).sub_const μ_k).pow 2
    convert h0 using 1; ring
  have hE : HasDerivAt (fun y => Real.exp ((y - μ_k) ^ 2 / (2 * v)))
      (Real.exp ((x - μ_k) ^ 2 / (2 * v)) * ((x - μ_k) / v)) x :=
    (Real.hasDerivAt_exp _).comp x h1
  exact ((hgd x).hasDerivAt.mul hE).add_const C

/-- **Per-flank ≤1-zero engine.**  On an interval `Icc p q` on which
`ψ(x) = v·deriv g x + (x−μ_k)·g x` is sign-definite (either everywhere positive or
everywhere negative), the perturbed function `h = g + a_k·N(μ_k,v,·)` has at most
one zero. -/
theorem flank_subsingleton
    (g : ℝ → ℝ) (hgd : Differentiable ℝ g) (a_k μ_k v : ℝ) (hv : 0 < v) (p q : ℝ)
    (hpsi : (∀ x ∈ Set.Icc p q, 0 < v * deriv g x + (x - μ_k) * g x)
          ∨ (∀ x ∈ Set.Icc p q, v * deriv g x + (x - μ_k) * g x < 0)) :
    {x ∈ Set.Icc p q |
        g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0}.Subsingleton := by
  set C : ℝ := a_k / Real.sqrt (2 * Real.pi * v) with hC
  set E : ℝ → ℝ := fun x => Real.exp ((x - μ_k) ^ 2 / (2 * v)) with hE
  set H : ℝ → ℝ := fun x => g x * E x + C with hH
  have hEpos : ∀ x, 0 < E x := fun x => Real.exp_pos _
  -- deriv H x = E x * ψ x / v
  have hHderiv : ∀ x, deriv H x = E x / v * (v * deriv g x + (x - μ_k) * g x) := by
    intro x
    have := (flankH_hasDerivAt g hgd μ_k v C x).deriv
    rw [hH]
    rw [this]
    field_simp
    ring
  have hHdiff : Differentiable ℝ H := fun x => (flankH_hasDerivAt g hgd μ_k v C x).differentiableAt
  -- zeros of h coincide with zeros of H (multiply by E > 0)
  have hzeros_eq : ∀ x,
      (g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0) ↔ H x = 0 := by
    intro x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
    simp only [hH, hE]
    have hsqrt_ne : Real.sqrt (2 * Real.pi * v) ≠ 0 := by
      apply ne_of_gt; apply Real.sqrt_pos.mpr; positivity
    have hee : Real.exp (-(x - μ_k) ^ 2 / (2 * v)) * Real.exp ((x - μ_k) ^ 2 / (2 * v)) = 1 := by
      rw [← Real.exp_add,
        show -(x - μ_k) ^ 2 / (2 * v) + (x - μ_k) ^ 2 / (2 * v) = 0 by ring, Real.exp_zero]
    constructor
    · intro hzero
      have hmul : (g x + a_k * ((1 / Real.sqrt (2 * Real.pi * v))
          * Real.exp (-(x - μ_k) ^ 2 / (2 * v)))) * Real.exp ((x - μ_k) ^ 2 / (2 * v)) = 0 := by
        rw [hzero]; ring
      rw [hC]
      have hexpand : (g x + a_k * ((1 / Real.sqrt (2 * Real.pi * v))
            * Real.exp (-(x - μ_k) ^ 2 / (2 * v)))) * Real.exp ((x - μ_k) ^ 2 / (2 * v))
          = g x * Real.exp ((x - μ_k) ^ 2 / (2 * v))
              + a_k / Real.sqrt (2 * Real.pi * v)
                * (Real.exp (-(x - μ_k) ^ 2 / (2 * v)) * Real.exp ((x - μ_k) ^ 2 / (2 * v))) := by
        field_simp
      rw [hexpand, hee, mul_one] at hmul
      exact hmul
    · intro hzero
      rw [hC] at hzero
      have key : g x + a_k * (1 / Real.sqrt (2 * Real.pi * v) * Real.exp (-(x - μ_k) ^ 2 / (2 * v)))
          = (g x * Real.exp ((x - μ_k) ^ 2 / (2 * v)) + a_k / Real.sqrt (2 * Real.pi * v))
              * Real.exp (-(x - μ_k) ^ 2 / (2 * v)) := by
        have hee2 : Real.exp ((x - μ_k) ^ 2 / (2 * v)) * Real.exp (-(x - μ_k) ^ 2 / (2 * v)) = 1 := by
          rw [← Real.exp_add,
            show (x - μ_k) ^ 2 / (2 * v) + -(x - μ_k) ^ 2 / (2 * v) = 0 by ring, Real.exp_zero]
        have hrw : (g x * Real.exp ((x - μ_k) ^ 2 / (2 * v)) + a_k / Real.sqrt (2 * Real.pi * v))
              * Real.exp (-(x - μ_k) ^ 2 / (2 * v))
            = g x * (Real.exp ((x - μ_k) ^ 2 / (2 * v)) * Real.exp (-(x - μ_k) ^ 2 / (2 * v)))
              + a_k / Real.sqrt (2 * Real.pi * v) * Real.exp (-(x - μ_k) ^ 2 / (2 * v)) := by ring
        rw [hrw, hee2, mul_one]
        field_simp
      rw [key, hzero, zero_mul]
  -- H strictly monotone (mono or anti) on Icc p q ⇒ injective there.
  have hHinj : Set.InjOn H (Set.Icc p q) := by
    rcases hpsi with hpos | hneg
    · have hmono : StrictMonoOn H (Set.Icc p q) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hHdiff.continuous.continuousOn
        intro x hx
        rw [hHderiv x]
        have hxIcc : x ∈ Set.Icc p q := interior_subset hx
        apply mul_pos (by positivity) (hpos x hxIcc)
      exact hmono.injOn
    · have hanti : StrictAntiOn H (Set.Icc p q) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hHdiff.continuous.continuousOn
        intro x hx
        rw [hHderiv x]
        have hxIcc : x ∈ Set.Icc p q := interior_subset hx
        have hEv : 0 < E x / v := by positivity
        exact mul_neg_of_pos_of_neg hEv (hneg x hxIcc)
      exact hanti.injOn
  intro x hx y hy
  obtain ⟨hxIcc, hxz⟩ := hx
  obtain ⟨hyIcc, hyz⟩ := hy
  have hHx : H x = 0 := (hzeros_eq x).mp hxz
  have hHy : H y = 0 := (hzeros_eq y).mp hyz
  exact hHinj hxIcc hyIcc (by rw [hHx, hHy])

/-- **Local sign-constancy with quantitative lower bound.**  If `g` is continuous
and `g μ_k ≠ 0`, there is `δ > 0` and `m₀ > 0` so that on `Icc (μ_k − δ) (μ_k + δ)`
the function `g` is sign-constant and bounded away from `0`: either `m₀ ≤ g x`
everywhere on the window, or `g x ≤ -m₀` everywhere on it. -/
theorem g_signConst_near
    (g : ℝ → ℝ) (hgc : Continuous g) (μ_k : ℝ) (hμ : g μ_k ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ m₀ : ℝ, 0 < m₀ ∧
      ((∀ x ∈ Set.Icc (μ_k - δ) (μ_k + δ), m₀ ≤ g x)
        ∨ (∀ x ∈ Set.Icc (μ_k - δ) (μ_k + δ), g x ≤ -m₀)) := by
  -- abs lower bound on a neighbourhood
  have hpos : 0 < |g μ_k| := abs_pos.mpr hμ
  have hcont : ContinuousAt (fun x => |g x|) μ_k := (hgc.abs).continuousAt
  have hlt : |g μ_k| / 2 < |g μ_k| := by linarith
  have hev : ∀ᶠ y in nhds μ_k, |g μ_k| / 2 ≤ |g y| :=
    ((continuousAt_const (y := |g μ_k| / 2)).eventually_lt hcont hlt).mono
      (fun y hy => le_of_lt hy)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by linarith, |g μ_k| / 2, by linarith, ?_⟩
  -- on this window, |g| ≥ m₀
  have habs : ∀ x ∈ Set.Icc (μ_k - ε / 2) (μ_k + ε / 2), |g μ_k| / 2 ≤ |g x| := by
    intro x hx
    apply hball
    rw [Real.dist_eq, abs_lt]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
  -- g sign constant: split on the sign of g μ_k
  rcases lt_or_gt_of_ne hμ with hneg | hpos'
  · -- g μ_k < 0 ⇒ g x ≤ -m₀ on the window
    right
    intro x hx
    -- g x < 0 (sign constancy via IVT)
    have hgxneg : g x < 0 := by
      by_contra hge
      rw [not_lt] at hge
      have hxj_mem : μ_k ∈ Set.Icc (μ_k - ε / 2) (μ_k + ε / 2) := by constructor <;> linarith
      have hseg : Set.uIcc μ_k x ⊆ Set.Icc (μ_k - ε / 2) (μ_k + ε / 2) := by
        intro y hy
        rcases le_total μ_k x with hle | hle
        · rw [Set.uIcc_of_le hle] at hy
          exact ⟨le_trans hxj_mem.1 hy.1, le_trans hy.2 hx.2⟩
        · rw [Set.uIcc_of_ge hle] at hy
          exact ⟨le_trans hx.1 hy.1, le_trans hy.2 hxj_mem.2⟩
      have h_ivt : Set.uIcc (g μ_k) (g x) ⊆ g '' Set.uIcc μ_k x :=
        intermediate_value_uIcc hgc.continuousOn
      have hzero_mem : (0 : ℝ) ∈ Set.uIcc (g μ_k) (g x) := by
        rw [Set.uIcc_of_le (le_trans (le_of_lt hneg) hge)]; exact ⟨le_of_lt hneg, hge⟩
      obtain ⟨y, hy_mem, hy_eq⟩ := h_ivt hzero_mem
      have hy_in : y ∈ Set.Icc (μ_k - ε / 2) (μ_k + ε / 2) := hseg hy_mem
      have := habs y hy_in
      rw [hy_eq] at this; simp at this; linarith
    have hax : |g x| = -g x := abs_of_neg hgxneg
    have := habs x hx
    rw [hax] at this; linarith
  · -- g μ_k > 0 ⇒ m₀ ≤ g x on the window
    left
    intro x hx
    have hgxpos : 0 < g x := by
      by_contra hle
      rw [not_lt] at hle
      have hxj_mem : μ_k ∈ Set.Icc (μ_k - ε / 2) (μ_k + ε / 2) := by constructor <;> linarith
      have hseg : Set.uIcc μ_k x ⊆ Set.Icc (μ_k - ε / 2) (μ_k + ε / 2) := by
        intro y hy
        rcases le_total μ_k x with hle' | hle'
        · rw [Set.uIcc_of_le hle'] at hy
          exact ⟨le_trans hxj_mem.1 hy.1, le_trans hy.2 hx.2⟩
        · rw [Set.uIcc_of_ge hle'] at hy
          exact ⟨le_trans hx.1 hy.1, le_trans hy.2 hxj_mem.2⟩
      have h_ivt : Set.uIcc (g μ_k) (g x) ⊆ g '' Set.uIcc μ_k x :=
        intermediate_value_uIcc hgc.continuousOn
      have hzero_mem : (0 : ℝ) ∈ Set.uIcc (g μ_k) (g x) := by
        rw [Set.uIcc_of_ge (le_trans hle (le_of_lt hpos'))]; exact ⟨hle, le_of_lt hpos'⟩
      obtain ⟨y, hy_mem, hy_eq⟩ := h_ivt hzero_mem
      have hy_in : y ∈ Set.Icc (μ_k - ε / 2) (μ_k + ε / 2) := hseg hy_mem
      have := habs y hy_in
      rw [hy_eq] at this; simp at this; linarith
    have hax : |g x| = g x := abs_of_pos hgxpos
    have := habs x hx
    rw [hax] at this; linarith

/-- **Local factorization facts at a vanishing centre.**  If `g` is analytic on
`univ`, `g μ_k = 0`, and `g` is NOT eventually `0` near `μ_k`, there are a small
radius `δ₁ > 0`, an order `n ≥ 1`, an analytic cofactor `G` with `G μ_k ≠ 0`, and
positive local bounds `m_G ≤ |G|`, `|G| ≤ M_G`, `|deriv G| ≤ M_{G'}` valid on the
window `Icc (μ_k − δ₁) (μ_k + δ₁)`, such that there `g x = (x − μ_k)^n · G x` and
`deriv g x = n·(x−μ_k)^{n-1}·G x + (x−μ_k)^n·deriv G x`, and `G` is sign-constant
on the window. -/
theorem centerVanishing_factor_facts
    (g : ℝ → ℝ) (hg : AnalyticOnNhd ℝ g Set.univ) (μ_k : ℝ)
    (hμ : g μ_k = 0) (hne : ¬ ∀ᶠ z in nhds μ_k, g z = 0) :
    ∃ (δ₁ : ℝ), 0 < δ₁ ∧ ∃ (n : ℕ), 1 ≤ n ∧ ∃ (G : ℝ → ℝ),
      (∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁),
          g x = (x - μ_k) ^ n * G x) ∧
      (∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁),
          deriv g x =
            (n : ℝ) * (x - μ_k) ^ (n - 1) * G x + (x - μ_k) ^ n * deriv G x) ∧
      ∃ (m_G M_G M_G' : ℝ), 0 < m_G ∧ 0 ≤ M_G ∧ 0 ≤ M_G' ∧
        ((∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), m_G ≤ G x)
          ∨ (∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), G x ≤ -m_G)) ∧
        (∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), |G x| ≤ M_G) ∧
        (∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), |deriv G x| ≤ M_G') := by
  -- Factor `g = (·-μ_k)^n • G` near μ_k with `G μ_k ≠ 0`.
  have hgat : AnalyticAt ℝ g μ_k := hg μ_k (Set.mem_univ _)
  obtain ⟨n, G, hGat, hGne, hfac⟩ :=
    (hgat.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hne
  -- `smul = mul` on ℝ; record the eventual product form.
  have hfac' : ∀ᶠ z in nhds μ_k, g z = (z - μ_k) ^ n * G z := by
    filter_upwards [hfac] with z hz
    simpa [smul_eq_mul] using hz
  -- `n ≥ 1`: otherwise `g μ_k = G μ_k ≠ 0`.
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hpos
    · exfalso
      have := hfac'.self_of_nhds
      rw [hn0] at this
      simp only [pow_zero, one_mul, sub_self] at this
      rw [hμ] at this
      exact hGne this.symm
    · exact hpos
  -- Local smoothness of `G`: continuous, and `deriv G` continuous, near μ_k.
  have hGcont_ev : ∀ᶠ z in nhds μ_k, ContinuousAt G z := by
    have h1 : ∀ᶠ z in nhds μ_k, AnalyticAt ℝ G z := hGat.eventually_analyticAt
    filter_upwards [h1] with z hz
    exact hz.continuousAt
  -- Continuity of `deriv G` near μ_k (from `ContDiffAt 2`).
  have hGderiv_cont_ev : ∀ᶠ z in nhds μ_k, ContinuousAt (deriv G) z := by
    have h1 : ∀ᶠ z in nhds μ_k, AnalyticAt ℝ G z := hGat.eventually_analyticAt
    filter_upwards [h1] with z hz
    exact ((hz.deriv).continuousAt)
  -- Eventual derivative formula for `g` via product rule on the factored form.
  have hderiv_ev : ∀ᶠ z in nhds μ_k,
      deriv g z = (n : ℝ) * (z - μ_k) ^ (n - 1) * G z + (z - μ_k) ^ n * deriv G z := by
    have hfac_ev2 : ∀ᶠ z in nhds μ_k, ∀ᶠ w in nhds z, g w = (w - μ_k) ^ n * G w :=
      eventually_eventually_nhds.mpr hfac'
    have hGan_ev : ∀ᶠ z in nhds μ_k, AnalyticAt ℝ G z := hGat.eventually_analyticAt
    filter_upwards [hfac_ev2, hGan_ev] with z hz_ev hGz
    -- `HasDerivAt` for the factored form at `z`.
    have hpow : HasDerivAt (fun y => (y - μ_k) ^ n)
        ((n : ℝ) * (z - μ_k) ^ (n - 1)) z := by
      have := ((hasDerivAt_id z).sub_const μ_k).pow n
      simpa using this
    have hGd : HasDerivAt G (deriv G z) z := hGz.differentiableAt.hasDerivAt
    have hmul : HasDerivAt (fun y => (y - μ_k) ^ n * G y)
        ((n : ℝ) * (z - μ_k) ^ (n - 1) * G z + (z - μ_k) ^ n * deriv G z) z := by
      have := hpow.mul hGd
      convert this using 1
    -- `g =ᶠ[nhds z] factored`, so `deriv g z = deriv factored z`.
    have heqg : g =ᶠ[nhds z] (fun y => (y - μ_k) ^ n * G y) := hz_ev
    rw [heqg.deriv_eq, hmul.deriv]
  -- Lower bound `|G μ_k|/2 ≤ |G|` near μ_k.
  have hGpos : 0 < |G μ_k| := abs_pos.mpr hGne
  have hGabs_cont : ContinuousAt (fun x => |G x|) μ_k := (hGcont_ev.self_of_nhds).abs
  have hGlb_ev : ∀ᶠ z in nhds μ_k, |G μ_k| / 2 ≤ |G z| :=
    ((continuousAt_const (y := |G μ_k| / 2)).eventually_lt hGabs_cont
      (by linarith : |G μ_k| / 2 < |G μ_k|)).mono (fun y hy => le_of_lt hy)
  -- Collect all eventual facts into one ball of radius `ε`.
  have hall : ∀ᶠ z in nhds μ_k,
      (deriv g z = (n : ℝ) * (z - μ_k) ^ (n - 1) * G z + (z - μ_k) ^ n * deriv G z)
      ∧ ContinuousAt G z ∧ ContinuousAt (deriv G) z
      ∧ (g z = (z - μ_k) ^ n * G z) ∧ |G μ_k| / 2 ≤ |G z| := by
    filter_upwards [hderiv_ev, hGcont_ev, hGderiv_cont_ev, hfac', hGlb_ev]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  rw [Metric.eventually_nhds_iff] at hall
  obtain ⟨ε, hε, hball⟩ := hall
  -- Window radius `δ₁ = ε/2`, so the CLOSED window `Icc (μ_k-δ₁) (μ_k+δ₁)` ⊆ ball ε.
  set δ₁ : ℝ := ε / 2 with hδ₁
  have hδ₁pos : 0 < δ₁ := by positivity
  have hwin_sub : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), dist x μ_k < ε := by
    intro x hx
    rw [Real.dist_eq, abs_lt]
    constructor <;> [linarith [hx.1, hδ₁]; linarith [hx.2, hδ₁]]
  -- Per-point facts on the window.
  have hfacx : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), g x = (x - μ_k) ^ n * G x :=
    fun x hx => (hball (hwin_sub x hx)).2.2.2.1
  have hderivx : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁),
      deriv g x = (n : ℝ) * (x - μ_k) ^ (n - 1) * G x + (x - μ_k) ^ n * deriv G x :=
    fun x hx => (hball (hwin_sub x hx)).1
  have hGcontx : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), ContinuousAt G x :=
    fun x hx => (hball (hwin_sub x hx)).2.1
  have hGdcontx : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), ContinuousAt (deriv G) x :=
    fun x hx => (hball (hwin_sub x hx)).2.2.1
  have hGlbx : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), |G μ_k| / 2 ≤ |G x| :=
    fun x hx => (hball (hwin_sub x hx)).2.2.2.2
  refine ⟨δ₁, hδ₁pos, n, hn1, G, hfacx, hderivx, ?_⟩
  -- `G` and `deriv G` are continuous on the (compact) window.
  have hGcontOn : ContinuousOn G (Set.Icc (μ_k - δ₁) (μ_k + δ₁)) :=
    fun x hx => (hGcontx x hx).continuousWithinAt
  have hGdcontOn : ContinuousOn (deriv G) (Set.Icc (μ_k - δ₁) (μ_k + δ₁)) :=
    fun x hx => (hGdcontx x hx).continuousWithinAt
  have hne_win : (Set.Icc (μ_k - δ₁) (μ_k + δ₁)).Nonempty :=
    Set.nonempty_Icc.mpr (by linarith)
  have hμmem : μ_k ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨by linarith, by linarith⟩
  -- Upper bound `M_G`.
  obtain ⟨xM, _hxM, hxMmax⟩ :=
    (isCompact_Icc (a := μ_k - δ₁) (b := μ_k + δ₁)).exists_isMaxOn hne_win
      (f := fun x => |G x|) hGcontOn.abs
  -- Upper bound `M_G'`.
  obtain ⟨xM', _hxM', hxM'max⟩ :=
    (isCompact_Icc (a := μ_k - δ₁) (b := μ_k + δ₁)).exists_isMaxOn hne_win
      (f := fun x => |deriv G x|) hGdcontOn.abs
  refine ⟨|G μ_k| / 2, |G xM|, |deriv G xM'|, by linarith, abs_nonneg _, abs_nonneg _,
    ?_, fun x hx => hxMmax hx, fun x hx => hxM'max hx⟩
  -- Sign-constancy of `G` on the window via IVT (|G| ≥ m_G > 0 ⇒ no zero ⇒ fixed sign).
  set m_G : ℝ := |G μ_k| / 2 with hm_G
  have hm_Gpos : 0 < m_G := by rw [hm_G]; linarith
  rcases lt_or_gt_of_ne hGne with hneg | hpos
  · -- `G μ_k < 0` ⇒ `G x ≤ -m_G` on the window.
    right
    intro x hx
    have hGxneg : G x < 0 := by
      by_contra hge
      rw [not_lt] at hge
      have hseg : Set.uIcc μ_k x ⊆ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := by
        intro y hy
        rcases le_total μ_k x with hle | hle
        · rw [Set.uIcc_of_le hle] at hy
          exact ⟨le_trans hμmem.1 hy.1, le_trans hy.2 hx.2⟩
        · rw [Set.uIcc_of_ge hle] at hy
          exact ⟨le_trans hx.1 hy.1, le_trans hy.2 hμmem.2⟩
      have h_ivt : Set.uIcc (G μ_k) (G x) ⊆ G '' Set.uIcc μ_k x :=
        intermediate_value_uIcc (hGcontOn.mono hseg)
      have hzero_mem : (0 : ℝ) ∈ Set.uIcc (G μ_k) (G x) := by
        rw [Set.uIcc_of_le (le_trans (le_of_lt hneg) hge)]; exact ⟨le_of_lt hneg, hge⟩
      obtain ⟨y, hy_mem, hy_eq⟩ := h_ivt hzero_mem
      have hy_in : y ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := hseg hy_mem
      have := hGlbx y hy_in
      rw [hy_eq] at this; simp at this; linarith
    have hax : |G x| = -G x := abs_of_neg hGxneg
    have := hGlbx x hx
    rw [hax] at this; linarith
  · -- `G μ_k > 0` ⇒ `m_G ≤ G x` on the window.
    left
    intro x hx
    have hGxpos : 0 < G x := by
      by_contra hle
      rw [not_lt] at hle
      have hseg : Set.uIcc μ_k x ⊆ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := by
        intro y hy
        rcases le_total μ_k x with hle' | hle'
        · rw [Set.uIcc_of_le hle'] at hy
          exact ⟨le_trans hμmem.1 hy.1, le_trans hy.2 hx.2⟩
        · rw [Set.uIcc_of_ge hle'] at hy
          exact ⟨le_trans hx.1 hy.1, le_trans hy.2 hμmem.2⟩
      have h_ivt : Set.uIcc (G μ_k) (G x) ⊆ G '' Set.uIcc μ_k x :=
        intermediate_value_uIcc (hGcontOn.mono hseg)
      have hzero_mem : (0 : ℝ) ∈ Set.uIcc (G μ_k) (G x) := by
        rw [Set.uIcc_of_ge (le_trans hle (le_of_lt hpos))]; exact ⟨hle, le_of_lt hpos⟩
      obtain ⟨y, hy_mem, hy_eq⟩ := h_ivt hzero_mem
      have hy_in : y ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := hseg hy_mem
      have := hGlbx y hy_in
      rw [hy_eq] at this; simp at this; linarith
    have hax : |G x| = G x := abs_of_pos hGxpos
    have := hGlbx x hx
    rw [hax] at this; linarith

/-! ### Center-window ≤2-zeros: the genuine remaining analytic `sorry`

The naive "≤1 zero per flank via monotonicity" decomposition is **FALSE** for a
window of FIXED radius `δ`: on a flank `[μ_k+β(v), μ_k+δ]` the bump derivative
magnitude `|a_k·N'| = |a_k|·((x−μ_k)/v)·N(x)` blows up at the INNER edge
(`v^{−3/4}·√(log(1/v)/2)/√(2π) → ∞`) but DECAYS to `0` at the OUTER edge `μ_k+δ`
(`exp(−δ²/2v)·v^{−3/2} · |x−μ_k| → 0`), so `deriv h = g' + a_k·N'` can change
sign once on a flank — `h` need NOT be strictly monotone there.  Concrete
witness (verified numerically): `g(x)=x`, `a_k=1`, `μ_k=0` gives a sign change of
`deriv h` on the right flank, so the `innerSplit_encard_zeros_le_two` (per-flank
strict-monotone) route is unsound.

Moreover the `δ`-FIXED-at-`1` "flank zeros ≤ 2" claim is itself **FALSE**:
`g(x)=sin(20x)` has many zeros in `(μ_k, μ_k+1)`, and for small `v` the bump is
negligible there, so `h ≈ g` has ≫2 zeros outside the band.  The window radius
`δ` MUST be chosen SMALL (depending on `g`'s local zero structure near `μ_k`),
which is exactly the paper's choice via heat-equation continuity (`g₀` has no zero
within `δ` of `μ_k`).

The honest ≤2-zeros conclusion on the SMALL window is split into:

* the BAND part — zero-free, fully discharged by `bandZeroFree` (PROVED above);
* the FLANK part — the zeros at distance `≥ β(v)` from `μ_k`, captured by the
  precise true `sorry` `flankZerosLeTwoSmallDelta` below.

`flankZerosLeTwoSmallDelta` quantifies `δ` EXISTENTIALLY (chosen small, depending
on `g`'s local zero structure near `μ_k`) — which is exactly the paper's choice
via heat-equation continuity (`g₀` has no zero within `δ` of `μ_k`).  It is a TRUE
proposition (numerically verified for the would-be counterexamples once `δ` is
small).  Its proof needs the paper's per-side sign/value argument that the bump
cannot add more than one zero per side; this is the single remaining precise
analytic `sorry`, and it introduces NO new axioms. -/
set_option maxHeartbeats 2000000 in
theorem flankZerosLeTwoSmallDelta
    (g : ℝ → ℝ) (hg : AnalyticOnNhd ℝ g Set.univ)
    (a_k : ℝ) (ha_k : a_k ≠ 0) (μ_k : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
    ∃ v₀ : ℝ, 0 < v₀ ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
        {x ∈ Set.Ioo (μ_k - δ) (μ_k + δ) |
            (g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0)
            ∧ bandRadius v ≤ |x - μ_k|}.encard ≤ 2 := by
  -- Smoothness of `g`.
  have hcd : ContDiff ℝ 2 g := contDiffOn_univ.mp (hg.contDiffOn_of_completeSpace (n := 2))
  have hgd : Differentiable ℝ g := hcd.differentiable (by norm_num)
  have hgc : Continuous g := hgd.continuous
  have hdc : Continuous (deriv g) := hcd.continuous_deriv (by norm_num)
  by_cases hμ : g μ_k = 0
  · -- ====================================================================
    -- Centre-VANISHING case `g μ_k = 0`: the SINGLE remaining precise gap.
    -- ====================================================================
    -- This is the only residue.  The generic case `g μ_k ≠ 0` below is proved
    -- in FULL (Mathlib-only), via the `φ = h/N` strict-monotonicity engine
    -- (`flank_subsingleton`) and the `v ≪ β(v)` comparison (`cmp_aux`).
    --
    -- For `g μ_k = 0` the same engine still applies once one factors
    -- `g x = (x − μ_k)^n · G x` (Mathlib:
    -- `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff`) with `G μ_k ≠ 0`,
    -- `G` analytic.  Then on a small flank
    --   `ψ(x) = v·g'(x) + (x−μ_k)·g(x)
    --        = (x−μ_k)^{n-1} · [v·n·G x + v(x−μ_k)·G'(x) + (x−μ_k)²·G x]`,
    -- and the bracket is sign-definite for small `v` because the term
    -- `(x−μ_k)²·G x` (size `≥ β(v)²·m_G = v·log(1/v)/2·m_G`) dominates the two
    -- `O(v)` terms once `log(1/v) > 2(n·M_G + δ·M_{G'})/m_G`.  Since
    -- `(x−μ_k)^{n-1}` is itself sign-constant on each (μ_k-free) flank, `ψ` is
    -- sign-definite there and `flank_subsingleton` applies verbatim — giving the
    -- identical `≤ 1 + 1 = 2` bound.  The `g ≡ 0` near `μ_k` sub-case is trivial:
    -- `h = a_k·N` has no zeros (`N > 0`, `a_k ≠ 0`), so the flank set is empty.
    --
    -- Formalizing the factorization + its derivative + the local sign/bounds for
    -- `G` is the one analytic development left open here; it adds NO new axioms.
    by_cases hflat : ∀ᶠ z in nhds μ_k, g z = 0
    · -- `g ≡ 0` near μ_k: on a small window `h = a_k·N ≠ 0`, so the flank set is empty.
      rw [Metric.eventually_nhds_iff] at hflat
      obtain ⟨ε, hε, hball⟩ := hflat
      refine ⟨ε / 2, by linarith, 1, by norm_num, ?_⟩
      intro v hv hvle
      -- the set is empty.
      have hempty : {x | x ∈ Set.Ioo (μ_k - ε / 2) (μ_k + ε / 2) ∧
          (g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0)
          ∧ bandRadius v ≤ |x - μ_k|} = (∅ : Set ℝ) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxIoo hzero _
        -- x is within ε of μ_k ⇒ g x = 0 ⇒ a_k·N = 0, impossible.
        have hxdist : dist x μ_k < ε := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> [linarith [hxIoo.1]; linarith [hxIoo.2]]
        have hgx0 : g x = 0 := hball hxdist
        rw [hgx0, zero_add] at hzero
        have hN_pos : 0 < Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x := by
          rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
          apply mul_pos
          · apply div_pos one_pos
            apply Real.sqrt_pos.mpr; positivity
          · exact Real.exp_pos _
        exact ha_k (by
          rcases mul_eq_zero.mp hzero with h | h
          · exact h
          · exact absurd h (ne_of_gt hN_pos))
      rw [hempty, Set.encard_empty]; exact zero_le _
    · -- `g` not eventually zero: use the local factorization.
      obtain ⟨δ₁, hδ₁, n, hn1, G, hfacx, hderivx, m_G, M_G, M_G', hm_G, hM_G, hM_G',
        hGsign, hGub, hGdub⟩ := centerVanishing_factor_facts g hg μ_k hμ hflat
      -- Threshold constant `K = n·M_G + δ₁·M_{G'} ≥ 0`.
      set K : ℝ := (n : ℝ) * M_G + δ₁ * M_G' with hK
      have hKnn : 0 ≤ K := by
        rw [hK]; positivity
      -- `v` small ⇒ `β(v) < δ₁` and `log(1/v) > 2K/m_G` (⇒ `v·K < β²·m_G`).
      obtain ⟨vd, hvd_pos, hvd⟩ := bandRadius_lt_of_small (δ := δ₁) hδ₁
      set thr : ℝ := Real.exp (-(2 * K / m_G + 1)) with hthr
      have hthr_pos : 0 < thr := Real.exp_pos _
      refine ⟨δ₁, hδ₁, min vd (min thr (1/2)), by positivity, ?_⟩
      intro v hv hvle
      have hvD : v ≤ vd := le_trans hvle (min_le_left _ _)
      have hvthr : v ≤ thr := le_trans hvle (le_trans (min_le_right _ _) (min_le_left _ _))
      have hvhalf : v ≤ 1/2 := le_trans hvle (le_trans (min_le_right _ _) (min_le_right _ _))
      have hv1 : v < 1 := by linarith
      set β : ℝ := bandRadius v with hβ
      have hβlt : β < δ₁ := hvd v hv hvD
      have hβpos : 0 < β := bandRadius_pos hv hv1
      -- `β² = v·log(1/v)/2`.
      have hβsq : β ^ 2 = v * Real.log (1 / v) / 2 := by
        rw [hβ]; unfold bandRadius
        rw [Real.sq_sqrt (by
          have : 0 < Real.log (1 / v) := by
            apply Real.log_pos; rw [lt_div_iff₀ hv]; linarith
          positivity)]
      -- key: `v · K < β² · m_G`.
      have hlog_gt : 2 * K / m_G < Real.log (1 / v) := by
        have h1 : Real.log (1 / v) = - Real.log v := by rw [one_div, Real.log_inv]
        have h2 : Real.log v ≤ Real.log thr := Real.log_le_log hv hvthr
        rw [hthr, Real.log_exp] at h2
        rw [h1]; linarith
      have hVKβ : v * K < β ^ 2 * m_G := by
        rw [hβsq]
        have hstep : 2 * K / m_G * m_G < Real.log (1 / v) * m_G :=
          mul_lt_mul_of_pos_right hlog_gt hm_G
        rw [div_mul_cancel₀ _ (ne_of_gt hm_G)] at hstep
        nlinarith [hstep, hv]
      -- `p := n - 1`, so `n = p + 1`.
      set p : ℕ := n - 1 with hp_def
      have hp1 : n = p + 1 := by omega
      -- ψ factorization: `ψ x = (x−μ_k)^p · B x` with
      -- `B x = (x−μ_k)²·G x + v·n·G x + v·(x−μ_k)·G' x`.
      have hψfac : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁),
          v * deriv g x + (x - μ_k) * g x
            = (x - μ_k) ^ p *
              ((x - μ_k) ^ 2 * G x + v * (n : ℝ) * G x + v * (x - μ_k) * deriv G x) := by
        intro x hx
        rw [hderivx x hx, hfacx x hx, hp1]
        ring
      -- Generic bracket-bound machinery: cross-term control on the window.
      have hcross : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁),
          |v * (x - μ_k) * deriv G x| ≤ v * δ₁ * M_G' := by
        intro x hx
        have hxabs : |x - μ_k| ≤ δ₁ := by
          rw [abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
        have hd := hGdub x hx
        calc |v * (x - μ_k) * deriv G x|
            = v * |x - μ_k| * |deriv G x| := by
              rw [abs_mul, abs_mul, abs_of_pos hv]
          _ ≤ v * δ₁ * M_G' := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hxabs (le_of_lt hv)
              · exact hd
              · exact abs_nonneg _
              · positivity
      -- `(x−μ_k)² ≥ β²` on the flank, and `v·δ₁·M_G' ≤ v·K < β²·m_G`.
      have hδMK : v * δ₁ * M_G' ≤ v * K := by
        rw [hK]; nlinarith [hM_G, hM_G', hv, hKnn, mul_nonneg (le_of_lt hv)
          (mul_nonneg (Nat.cast_nonneg n) hM_G)]
      -- ψ sign-definite on the RIGHT flank `Icc (μ_k+β) (μ_k+δ₁)`.
      have hψ_right :
          (∀ x ∈ Set.Icc (μ_k + β) (μ_k + δ₁), 0 < v * deriv g x + (x - μ_k) * g x)
            ∨ (∀ x ∈ Set.Icc (μ_k + β) (μ_k + δ₁), v * deriv g x + (x - μ_k) * g x < 0) := by
        rcases hGsign with hGpos | hGneg
        · left
          intro x hx
          have hxw : x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨by linarith [hx.1, hβpos], hx.2⟩
          have hxμ : 0 < x - μ_k := by linarith [hx.1, hβpos]
          have hβle : β ≤ |x - μ_k| := by rw [abs_of_pos hxμ]; linarith [hx.1]
          have hsq : β ^ 2 ≤ (x - μ_k) ^ 2 := by
            have h1 : β ^ 2 ≤ |x - μ_k| ^ 2 := by
              nlinarith [hβle, hβpos, abs_nonneg (x - μ_k)]
            rwa [sq_abs] at h1
          have hGx : m_G ≤ G x := hGpos x hxw
          have hcr := hcross x hxw
          have ht1 : β ^ 2 * m_G ≤ (x - μ_k) ^ 2 * G x := by
            apply mul_le_mul hsq hGx (le_of_lt hm_G); positivity
          have hcr' : -(v * δ₁ * M_G') ≤ v * (x - μ_k) * deriv G x := (abs_le.mp hcr).1
          have ht2 : 0 ≤ v * (n : ℝ) * G x :=
            mul_nonneg (by positivity) (le_trans (le_of_lt hm_G) hGx)
          have hBpos : 0 < (x - μ_k) ^ 2 * G x + v * (n : ℝ) * G x + v * (x - μ_k) * deriv G x := by
            nlinarith [ht1, ht2, hcr', hδMK, hVKβ]
          rw [hψfac x hxw]
          exact mul_pos (pow_pos hxμ p) hBpos
        · right
          intro x hx
          have hxw : x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨by linarith [hx.1, hβpos], hx.2⟩
          have hxμ : 0 < x - μ_k := by linarith [hx.1, hβpos]
          have hβle : β ≤ |x - μ_k| := by rw [abs_of_pos hxμ]; linarith [hx.1]
          have hsq : β ^ 2 ≤ (x - μ_k) ^ 2 := by
            have h1 : β ^ 2 ≤ |x - μ_k| ^ 2 := by
              nlinarith [hβle, hβpos, abs_nonneg (x - μ_k)]
            rwa [sq_abs] at h1
          have hGx : G x ≤ -m_G := hGneg x hxw
          have hcr := hcross x hxw
          have ht1 : (x - μ_k) ^ 2 * G x ≤ -(β ^ 2 * m_G) := by
            have hh : (x - μ_k) ^ 2 * (-G x) ≥ β ^ 2 * m_G := by
              apply mul_le_mul hsq (by linarith [hGx]) (le_of_lt hm_G); positivity
            nlinarith [hh]
          have hcr'' : v * (x - μ_k) * deriv G x ≤ v * δ₁ * M_G' := (abs_le.mp hcr).2
          have ht2 : v * (n : ℝ) * G x ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hGx, hm_G])
          have hBneg : (x - μ_k) ^ 2 * G x + v * (n : ℝ) * G x + v * (x - μ_k) * deriv G x < 0 := by
            nlinarith [ht1, ht2, hcr'', hδMK, hVKβ]
          rw [hψfac x hxw]
          exact mul_neg_of_pos_of_neg (pow_pos hxμ p) hBneg
      -- ψ sign-definite on the LEFT flank `Icc (μ_k-δ₁) (μ_k-β)`.
      have hψ_left :
          (∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k - β), 0 < v * deriv g x + (x - μ_k) * g x)
            ∨ (∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k - β), v * deriv g x + (x - μ_k) * g x < 0) := by
        -- helper: on the left flank, B is sign-definite (sign of G).
        have hBflank : ∀ x ∈ Set.Icc (μ_k - δ₁) (μ_k - β),
            (((∀ y ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), m_G ≤ G y) →
                0 < (x - μ_k) ^ 2 * G x + v * (n : ℝ) * G x + v * (x - μ_k) * deriv G x))
            ∧ (((∀ y ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁), G y ≤ -m_G) →
                (x - μ_k) ^ 2 * G x + v * (n : ℝ) * G x + v * (x - μ_k) * deriv G x < 0)) := by
          intro x hx
          have hxw : x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
          have hxμ : x - μ_k < 0 := by linarith [hx.2, hβpos]
          have hβle : β ≤ |x - μ_k| := by rw [abs_of_neg hxμ]; linarith [hx.2]
          have hsq : β ^ 2 ≤ (x - μ_k) ^ 2 := by
            have h1 : β ^ 2 ≤ |x - μ_k| ^ 2 := by
              nlinarith [hβle, hβpos, abs_nonneg (x - μ_k)]
            rwa [sq_abs] at h1
          have hcr := hcross x hxw
          refine ⟨fun hGpos => ?_, fun hGneg => ?_⟩
          · have hGx : m_G ≤ G x := hGpos x hxw
            have ht1 : β ^ 2 * m_G ≤ (x - μ_k) ^ 2 * G x := by
              apply mul_le_mul hsq hGx (le_of_lt hm_G); positivity
            have hcr' : -(v * δ₁ * M_G') ≤ v * (x - μ_k) * deriv G x := (abs_le.mp hcr).1
            have ht2 : 0 ≤ v * (n : ℝ) * G x :=
            mul_nonneg (by positivity) (le_trans (le_of_lt hm_G) hGx)
            nlinarith [ht1, ht2, hcr', hδMK, hVKβ]
          · have hGx : G x ≤ -m_G := hGneg x hxw
            have ht1 : (x - μ_k) ^ 2 * G x ≤ -(β ^ 2 * m_G) := by
              have hh : (x - μ_k) ^ 2 * (-G x) ≥ β ^ 2 * m_G := by
                apply mul_le_mul hsq (by linarith [hGx]) (le_of_lt hm_G); positivity
              nlinarith [hh]
            have hcr'' : v * (x - μ_k) * deriv G x ≤ v * δ₁ * M_G' := (abs_le.mp hcr).2
            have ht2 : v * (n : ℝ) * G x ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [hGx, hm_G])
            nlinarith [ht1, ht2, hcr'', hδMK, hVKβ]
        -- sign of `(x−μ_k)^p` on the left flank: case on parity of p.
        rcases Nat.even_or_odd p with hpar | hpar
        · -- p even ⇒ (x−μ_k)^p > 0 ⇒ sign(ψ) = sign(B).
          rcases hGsign with hGpos | hGneg
          · left
            intro x hx
            have hxw : x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
            have hxμ : x - μ_k < 0 := by linarith [hx.2, hβpos]
            have hpow : 0 < (x - μ_k) ^ p := hpar.pow_pos (ne_of_lt hxμ)
            rw [hψfac x hxw]
            exact mul_pos hpow ((hBflank x hx).1 hGpos)
          · right
            intro x hx
            have hxw : x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
            have hxμ : x - μ_k < 0 := by linarith [hx.2, hβpos]
            have hpow : 0 < (x - μ_k) ^ p := hpar.pow_pos (ne_of_lt hxμ)
            rw [hψfac x hxw]
            exact mul_neg_of_pos_of_neg hpow ((hBflank x hx).2 hGneg)
        · -- p odd ⇒ (x−μ_k)^p < 0 ⇒ sign(ψ) = -sign(B).
          rcases hGsign with hGpos | hGneg
          · right
            intro x hx
            have hxw : x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
            have hxμ : x - μ_k < 0 := by linarith [hx.2, hβpos]
            have hpow : (x - μ_k) ^ p < 0 := hpar.pow_neg hxμ
            rw [hψfac x hxw]
            exact mul_neg_of_neg_of_pos hpow ((hBflank x hx).1 hGpos)
          · left
            intro x hx
            have hxw : x ∈ Set.Icc (μ_k - δ₁) (μ_k + δ₁) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
            have hxμ : x - μ_k < 0 := by linarith [hx.2, hβpos]
            have hpow : (x - μ_k) ^ p < 0 := hpar.pow_neg hxμ
            rw [hψfac x hxw]
            exact mul_pos_of_neg_of_neg hpow ((hBflank x hx).2 hGneg)
      -- Each flank's zero set is a subsingleton (engine).
      have hsubR := flank_subsingleton g hgd a_k μ_k v hv (μ_k + β) (μ_k + δ₁) hψ_right
      have hsubL := flank_subsingleton g hgd a_k μ_k v hv (μ_k - δ₁) (μ_k - β) hψ_left
      -- Cover and bound by 1 + 1.
      set ZR : Set ℝ := {x ∈ Set.Icc (μ_k + β) (μ_k + δ₁) |
          g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0} with hZR
      set ZL : Set ℝ := {x ∈ Set.Icc (μ_k - δ₁) (μ_k - β) |
          g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0} with hZL
      have hcover :
          {x ∈ Set.Ioo (μ_k - δ₁) (μ_k + δ₁) |
              (g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0)
              ∧ bandRadius v ≤ |x - μ_k|} ⊆ ZR ∪ ZL := by
        intro x hx
        obtain ⟨hxIoo, hxz, hxβ⟩ := hx
        rw [← hβ] at hxβ
        rcases le_or_gt μ_k x with hle | hlt
        · left
          have : β ≤ x - μ_k := by rwa [abs_of_nonneg (by linarith)] at hxβ
          exact ⟨⟨by linarith, le_of_lt hxIoo.2⟩, hxz⟩
        · right
          rw [abs_of_neg (by linarith)] at hxβ
          have : β ≤ μ_k - x := by linarith [hxβ]
          exact ⟨⟨le_of_lt hxIoo.1, by linarith⟩, hxz⟩
      calc {x ∈ Set.Ioo (μ_k - δ₁) (μ_k + δ₁) |
              (g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0)
              ∧ bandRadius v ≤ |x - μ_k|}.encard
          ≤ (ZR ∪ ZL).encard := Set.encard_le_encard hcover
        _ ≤ ZR.encard + ZL.encard := Set.encard_union_le _ _
        _ ≤ 1 + 1 := add_le_add (Set.encard_le_one_iff_subsingleton.mpr hsubR)
                                (Set.encard_le_one_iff_subsingleton.mpr hsubL)
        _ = 2 := by norm_num
  · -- Generic case `g μ_k ≠ 0`: full φ = h/N monotonicity argument.
    obtain ⟨δ, hδ, m₀, hm₀, hsign⟩ := g_signConst_near g hgc μ_k hμ
    -- Bound `|deriv g| ≤ M` on the compact window.
    obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Set.Icc (μ_k - δ) (μ_k + δ), |deriv g x| ≤ M := by
      have hne : (Set.Icc (μ_k - δ) (μ_k + δ)).Nonempty := Set.nonempty_Icc.mpr (by linarith)
      obtain ⟨x₀, _hx₀, hx₀max⟩ :=
        (isCompact_Icc (a := μ_k - δ) (b := μ_k + δ)).exists_isMaxOn hne
          (f := fun x => |deriv g x|) (hdc.abs.continuousOn)
      exact ⟨|deriv g x₀|, fun x hx => hx₀max hx⟩
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM μ_k ⟨by linarith, by linarith⟩)
    -- The `v ≪ β(v)` comparison with `K = M / m₀`.
    have hKnn : 0 ≤ M / m₀ := by positivity
    obtain ⟨vc, hvc_pos, _hvc_lt1, hvc⟩ := cmp_aux (M / m₀) hKnn
    -- `bandRadius v < δ` for small `v`.
    obtain ⟨vd, hvd_pos, hvd⟩ := bandRadius_lt_of_small (δ := δ) hδ
    refine ⟨δ, hδ, min vc vd, lt_min hvc_pos hvd_pos, ?_⟩
    intro v hv hvle
    have hvleC : v ≤ vc := le_trans hvle (min_le_left _ _)
    have hvleD : v ≤ vd := le_trans hvle (min_le_right _ _)
    set β : ℝ := bandRadius v with hβ
    have hβlt : β < δ := hvd v hv hvleD
    have hv1 : v < 1 := lt_of_le_of_lt hvleC _hvc_lt1
    have hβpos : 0 < β := bandRadius_pos hv hv1
    -- Key inequality: `M·v < β·m₀`.
    have hMvβ : M * v < β * m₀ := by
      have hc := hvc v hv hvleC          -- (M/m₀)·v < β
      rw [div_mul_eq_mul_div, div_lt_iff₀ hm₀] at hc
      linarith [hc]
    -- `v·deriv g x` is bounded by `±M·v` on the window.
    have hvderiv : ∀ x ∈ Set.Icc (μ_k - δ) (μ_k + δ),
        -(M * v) ≤ v * deriv g x ∧ v * deriv g x ≤ M * v := by
      intro x hx
      have habs : |deriv g x| ≤ M := hM x hx
      have h1 : deriv g x ≤ M := le_of_abs_le habs
      have h2 : -M ≤ deriv g x := neg_le_of_abs_le habs
      constructor
      · have : -M * v ≤ deriv g x * v := mul_le_mul_of_nonneg_right h2 (le_of_lt hv)
        nlinarith [this]
      · have : deriv g x * v ≤ M * v := mul_le_mul_of_nonneg_right h1 (le_of_lt hv)
        nlinarith [this]
    -- ψ is sign-definite on each flank.  Right flank `Icc (μ_k+β) (μ_k+δ)`.
    have hψ_right : (∀ x ∈ Set.Icc (μ_k + β) (μ_k + δ), 0 < v * deriv g x + (x - μ_k) * g x)
        ∨ (∀ x ∈ Set.Icc (μ_k + β) (μ_k + δ), v * deriv g x + (x - μ_k) * g x < 0) := by
      rcases hsign with hpos | hneg
      · left
        intro x hx
        have hxw : x ∈ Set.Icc (μ_k - δ) (μ_k + δ) := ⟨by linarith [hx.1], hx.2⟩
        have hgx : m₀ ≤ g x := hpos x hxw
        have hxμ : β ≤ x - μ_k := by linarith [hx.1]
        have hprod : β * m₀ ≤ (x - μ_k) * g x :=
          mul_le_mul hxμ hgx (le_of_lt hm₀) (by linarith [hβpos, hxμ])
        have hvd' := (hvderiv x hxw).1
        linarith [hprod, hvd', hMvβ]
      · right
        intro x hx
        have hxw : x ∈ Set.Icc (μ_k - δ) (μ_k + δ) := ⟨by linarith [hx.1], hx.2⟩
        have hgx : g x ≤ -m₀ := hneg x hxw
        have hxμ : β ≤ x - μ_k := by linarith [hx.1]
        have hxμpos : 0 < x - μ_k := by linarith [hβpos]
        have hprod : (x - μ_k) * g x ≤ (x - μ_k) * (-m₀) :=
          mul_le_mul_of_nonneg_left hgx (le_of_lt hxμpos)
        have hbound : (x - μ_k) * (-m₀) ≤ β * (-m₀) := by nlinarith [hxμ, hm₀]
        have hvd' := (hvderiv x hxw).2
        nlinarith [hprod, hbound, hvd', hMvβ]
    -- Left flank `Icc (μ_k-δ) (μ_k-β)`.
    have hψ_left : (∀ x ∈ Set.Icc (μ_k - δ) (μ_k - β), 0 < v * deriv g x + (x - μ_k) * g x)
        ∨ (∀ x ∈ Set.Icc (μ_k - δ) (μ_k - β), v * deriv g x + (x - μ_k) * g x < 0) := by
      rcases hsign with hpos | hneg
      · right
        intro x hx
        have hxw : x ∈ Set.Icc (μ_k - δ) (μ_k + δ) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
        have hgx : m₀ ≤ g x := hpos x hxw
        have hxμ : x - μ_k ≤ -β := by linarith [hx.2]
        have hxμneg : x - μ_k < 0 := by linarith [hβpos]
        -- (x-μ_k)*g x ≤ -β*m₀
        have hprod : (x - μ_k) * g x ≤ (x - μ_k) * m₀ :=
          mul_le_mul_of_nonpos_left hgx (le_of_lt hxμneg)
        have hbound : (x - μ_k) * m₀ ≤ -β * m₀ := by nlinarith [hxμ, hm₀]
        have hvd' := (hvderiv x hxw).2
        nlinarith [hprod, hbound, hvd', hMvβ]
      · left
        intro x hx
        have hxw : x ∈ Set.Icc (μ_k - δ) (μ_k + δ) := ⟨hx.1, by linarith [hx.2, hβpos]⟩
        have hgx : g x ≤ -m₀ := hneg x hxw
        have hxμ : x - μ_k ≤ -β := by linarith [hx.2]
        have hxμneg : x - μ_k < 0 := by linarith [hβpos]
        -- (x-μ_k)*g x ≥ β*m₀
        have hprod : (x - μ_k) * (-m₀) ≤ (x - μ_k) * g x :=
          mul_le_mul_of_nonpos_left hgx (le_of_lt hxμneg)
        have hbound : β * m₀ ≤ (x - μ_k) * (-m₀) := by nlinarith [hxμ, hm₀]
        have hvd' := (hvderiv x hxw).1
        nlinarith [hprod, hbound, hvd', hMvβ]
    -- Each flank's zero set is a subsingleton.
    have hsubR := flank_subsingleton g hgd a_k μ_k v hv (μ_k + β) (μ_k + δ) hψ_right
    have hsubL := flank_subsingleton g hgd a_k μ_k v hv (μ_k - δ) (μ_k - β) hψ_left
    -- Bound the encard by 1 + 1.
    set ZR : Set ℝ := {x ∈ Set.Icc (μ_k + β) (μ_k + δ) |
        g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0} with hZR
    set ZL : Set ℝ := {x ∈ Set.Icc (μ_k - δ) (μ_k - β) |
        g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0} with hZL
    have hcover :
        {x ∈ Set.Ioo (μ_k - δ) (μ_k + δ) |
            (g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0)
            ∧ bandRadius v ≤ |x - μ_k|} ⊆ ZR ∪ ZL := by
      intro x hx
      obtain ⟨hxIoo, hxz, hxβ⟩ := hx
      rw [← hβ] at hxβ
      rcases le_or_gt μ_k x with hle | hlt
      · -- x ≥ μ_k: |x - μ_k| = x - μ_k ≥ β ⇒ x ∈ ZR
        left
        have : β ≤ x - μ_k := by rwa [abs_of_nonneg (by linarith)] at hxβ
        exact ⟨⟨by linarith, le_of_lt hxIoo.2⟩, hxz⟩
      · -- x < μ_k: |x - μ_k| = μ_k - x ≥ β ⇒ x ∈ ZL
        right
        rw [abs_of_neg (by linarith)] at hxβ
        have : β ≤ μ_k - x := by linarith [hxβ]
        exact ⟨⟨le_of_lt hxIoo.1, by linarith⟩, hxz⟩
    calc {x ∈ Set.Ioo (μ_k - δ) (μ_k + δ) |
            (g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0)
            ∧ bandRadius v ≤ |x - μ_k|}.encard
        ≤ (ZR ∪ ZL).encard := Set.encard_le_encard hcover
      _ ≤ ZR.encard + ZL.encard := Set.encard_union_le _ _
      _ ≤ 1 + 1 := add_le_add (Set.encard_le_one_iff_subsingleton.mpr hsubR)
                              (Set.encard_le_one_iff_subsingleton.mpr hsubL)
      _ = 2 := by norm_num

/-- **(C-assemble core)** The center-window ≤2-zeros bound, with `δ` chosen small.
Fully assembled (Mathlib-only) MODULO the single precise flank `sorry`
(`flankZerosLeTwoSmallDelta`): the open band `(μ_k−β(v), μ_k+β(v))` is zero-free
(`bandZeroFree`), so every zero of `h` in the window lies in the flank region
`{β(v) ≤ |x−μ_k|}`, whose cardinality is `≤ 2`. -/
theorem centerWindowZerosLeTwo
    (g : ℝ → ℝ) (hg : AnalyticOnNhd ℝ g Set.univ)
    (a_k : ℝ) (ha_k : a_k ≠ 0) (μ_k : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
    ∃ v₀ : ℝ, 0 < v₀ ∧
      ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
        {x ∈ Set.Ioo (μ_k - δ) (μ_k + δ) |
            g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x = 0}.encard
          ≤ 2 := by
  -- Pull the small `δ` and the flank bound from `flankZerosLeTwoSmallDelta`.
  obtain ⟨δ, hδ, v₀f, hv₀f, hflank⟩ := flankZerosLeTwoSmallDelta g hg a_k ha_k μ_k
  -- Pull the band-zero-free `v₀` for this same `δ`.
  obtain ⟨v₀b, hv₀b, hband⟩ := bandZeroFree g hg a_k ha_k μ_k hδ
  refine ⟨δ, hδ, min v₀f v₀b, lt_min hv₀f hv₀b, ?_⟩
  intro v hv hvle
  have hvf : v ≤ v₀f := le_trans hvle (min_le_left _ _)
  have hvb : v ≤ v₀b := le_trans hvle (min_le_right _ _)
  set h : ℝ → ℝ := fun x =>
    g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x with hh
  obtain ⟨_hβlt, hmid⟩ := hband v hv hvb
  -- Every zero of `h` in the window lies OUTSIDE the open band (β ≤ |x − μ_k|),
  -- because the band is zero-free.  So the window zero set ⊆ the flank zero set.
  have hsub :
      {x ∈ Set.Ioo (μ_k - δ) (μ_k + δ) | h x = 0}
        ⊆ {x ∈ Set.Ioo (μ_k - δ) (μ_k + δ) |
            h x = 0 ∧ bandRadius v ≤ |x - μ_k|} := by
    intro x hx
    obtain ⟨hxIoo, hxz⟩ := hx
    refine ⟨hxIoo, hxz, ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have hxband : x ∈ Set.Ioo (μ_k - bandRadius v) (μ_k + bandRadius v) := by
      rw [Set.mem_Ioo]
      have := abs_lt.mp hlt
      constructor <;> [linarith [this.1]; linarith [this.2]]
    exact (hmid x hxband) hxz
  exact le_trans (Set.encard_le_encard hsub) (hflank v hv hvf)

/-- Region (c) of Moitra–Valiant §6.1 ("add the k-th Gaussian"): at most two
zeros in a small interval around the perturbation centre `μ_k`.  Genuine
ProofLemmas replacement for the prior-work axiom
`Workspace.PriorWork.HurwitzGaussianPerturbationCenterTwoZeros` (same signature,
so it is a drop-in replacement).

Let `g : ℝ → ℝ` be real-analytic, `a_k ≠ 0`, and `μ_k ∈ ℝ`.  Then there exist
`δ > 0` and `v₀ > 0` such that for every `v ∈ (0, v₀]` the perturbed function
`h(x) = g x + a_k · N(μ_k, v, x)` has at most two distinct zeros in the open
interval `(μ_k − δ, μ_k + δ)`. -/
theorem HurwitzGaussianPerturbationCenterTwoZeros :
    ∀ (g : ℝ → ℝ),
      AnalyticOnNhd ℝ g Set.univ →
        ∀ (a_k : ℝ), a_k ≠ 0 →
        ∀ (μ_k : ℝ),
          ∃ δ : ℝ, 0 < δ ∧
          ∃ v₀ : ℝ, 0 < v₀ ∧
            ∀ (v : ℝ) (hv : 0 < v), v ≤ v₀ →
              (Workspace.Types.ZeroCount.zeroSet
                  (fun x => g x +
                    a_k *
                      Workspace.Types.GaussianPDF.GaussianPDF.density
                        ⟨μ_k, v, hv⟩ x)
                ∩ Set.Ioo (μ_k - δ) (μ_k + δ)).encard
                ≤ (2 : ℕ∞) := by
  intro g hg a_k ha_k μ_k
  obtain ⟨δ, hδ, v₀, hv₀, hbound⟩ :=
    centerWindowZerosLeTwo g hg a_k ha_k μ_k
  refine ⟨δ, hδ, v₀, hv₀, ?_⟩
  intro v hv hvle
  -- Name the perturbed function.
  set h : ℝ → ℝ := fun x =>
    g x + a_k * Workspace.Types.GaussianPDF.GaussianPDF.density ⟨μ_k, v, hv⟩ x with hh
  -- Rewrite the (zeroSet h ∩ Ioo) as the {x ∈ Ioo | h x = 0} form used by the core lemma.
  have hset_eq :
      (Workspace.Types.ZeroCount.zeroSet h ∩ Set.Ioo (μ_k - δ) (μ_k + δ))
        = {x ∈ Set.Ioo (μ_k - δ) (μ_k + δ) | h x = 0} := by
    ext x
    simp only [Workspace.Types.ZeroCount.zeroSet_def, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_Ioo]
    tauto
  rw [hset_eq]
  exact hbound v hv hvle

end Workspace.ProofLemmas
