import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.Lemma29TailMomentVarLeTwo
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open MeasureTheory

/-- The tail set `T = {x : ℝ | 2/ε ≤ |x|}` is measurable. -/
private lemma SDL1TB_T_measurable (ε : ℝ) :
    MeasurableSet {x : ℝ | 2 / ε ≤ |x|} :=
  measurableSet_le measurable_const continuous_abs.measurable

/-- Integrable for `G.density` on `volume`. -/
private lemma SDL1TB_integrable_density
    (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    Integrable (fun x : ℝ => G.density x) volume := by
  have h : Integrable (fun x : ℝ => x ^ 0 * G.density x) volume :=
    SublemmaIntegrabilityXPowGaussian G 0
  simpa using h

/-- IntegrableOn for `G.density` on any set. -/
private lemma SDL1TB_integrableOn_density
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (T : Set ℝ) :
    IntegrableOn (fun x : ℝ => G.density x) T volume :=
  (SDL1TB_integrable_density G).integrableOn

/-- IntegrableOn for `c * G.density` on any set. -/
private lemma SDL1TB_integrableOn_const_mul
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (T : Set ℝ) (c : ℝ) :
    IntegrableOn (fun x : ℝ => c * G.density x) T volume :=
  (SDL1TB_integrableOn_density G T).const_mul c

/-- Triangle inequality for sum: `|Σ_x∈l, f x| ≤ Σ_x∈l, |f x|`. -/
private lemma SDL1TB_abs_list_sum_le_sum_abs
    {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map (fun x => |f x|)).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    calc |f a + (rest.map f).sum|
        ≤ |f a| + |(rest.map f).sum| := abs_add_le _ _
      _ ≤ |f a| + (rest.map (fun x => |f x|)).sum := by linarith

/-- Sum of mapped constant equals length times constant. -/
private lemma SDL1TB_list_map_const_sum {α : Type*} (l : List α) (b : ℝ) :
    (l.map (fun _ : α => b)).sum = l.length • b := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [add_smul, one_smul, add_comm]

/-- Bound on list sum from pointwise bound + length bound. -/
private lemma SDL1TB_list_sum_le_of_pointwise_le_of_length_le
    {α : Type*} (l : List α) (f : α → ℝ) (b : ℝ) (n : ℕ)
    (hb : 0 ≤ b) (hf : ∀ x ∈ l, f x ≤ b) (hlen : l.length ≤ n) :
    (l.map f).sum ≤ n * b := by
  have h1 : (l.map f).sum ≤ (l.map (fun _ : α => b)).sum := by
    apply List.sum_le_sum
    intro x hx
    exact hf x hx
  have h2 : (l.map (fun _ : α => b)).sum = l.length * b := by
    rw [SDL1TB_list_map_const_sum]
    rw [nsmul_eq_mul]
  have h3 : (l.length : ℝ) * b ≤ (n : ℝ) * b := by
    apply mul_le_mul_of_nonneg_right _ hb
    exact_mod_cast hlen
  linarith

/-- Per-component absolute tail bound for the density (i = 0 case of
`Lemma29TailMomentVarLeTwo`), reformulated in terms of `G.density`. -/
private lemma SDL1TB_per_component_density_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G : Workspace.Types.GaussianPDF.GaussianPDF) (ε : ℝ),
        0 < ε → ε ≤ 1 → |G.mean| ≤ 1 / ε →
        G.varSq ≤ 2 →
        |∫ x in {x : ℝ | 2 / ε ≤ |x|}, G.density x|
          ≤ K * (1 / ε) ^ 6 * Real.exp (-1 / (4 * ε ^ 2)) := by
  obtain ⟨K_29', hK_pos, hK⟩ := Lemma29TailMomentVarLeTwo
  refine ⟨K_29', hK_pos, ?_⟩
  intro G ε hε_pos hε_le hμ hσ_hi
  have hres := hK G.mean G.varSq ε 0 hε_pos hε_le G.varSq_pos hσ_hi hμ (by omega)
  -- Convert: x^0 = 1, and rewrite G.density in the explicit form.
  have hdens : ∀ x : ℝ,
      G.density x =
        (1 : ℝ) * (1 / Real.sqrt (2 * Real.pi * G.varSq))
          * Real.exp (-((x - G.mean) ^ 2) / (2 * G.varSq)) := by
    intro x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
    ring
  have h_eq_integral :
      (∫ x in {x : ℝ | 2 / ε ≤ |x|}, G.density x)
        = ∫ x in {x : ℝ | 2 / ε ≤ |x|},
            x ^ 0 * (1 / Real.sqrt (2 * Real.pi * G.varSq))
              * Real.exp (-((x - G.mean) ^ 2) / (2 * G.varSq)) ∂volume := by
    refine setIntegral_congr_fun (SDL1TB_T_measurable ε) ?_
    intro x _
    simp only [pow_zero]
    have := hdens x
    linarith [hdens x]
  rw [h_eq_integral]
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hpow_eq : (1 : ℝ) / ε ^ 6 = (1 / ε) ^ 6 := by
    rw [one_div, one_div, inv_pow]
  calc |∫ x in {x : ℝ | 2 / ε ≤ |x|},
            x ^ 0 * (1 / Real.sqrt (2 * Real.pi * G.varSq))
              * Real.exp (-((x - G.mean) ^ 2) / (2 * G.varSq)) ∂volume|
      ≤ K_29' * (1 / ε ^ (0 + 6)) * Real.exp (-1 / (4 * ε ^ 2)) := hres
    _ = K_29' * (1 / ε) ^ 6 * Real.exp (-1 / (4 * ε ^ 2)) := by
        rw [show (0 : ℕ) + 6 = 6 from rfl, hpow_eq]

/-- The density of a Gaussian PDF is nonneg. -/
private lemma SDL1TB_density_nn
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (x : ℝ) :
    0 ≤ G.density x := by
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
  have hv_pos : 0 < G.varSq := G.varSq_pos
  have hsq : 0 < 2 * Real.pi * G.varSq := by positivity
  have hsqrt_nn : 0 ≤ Real.sqrt (2 * Real.pi * G.varSq) := Real.sqrt_nonneg _
  have hexp_nn : 0 ≤ Real.exp (-(x - G.mean) ^ 2 / (2 * G.varSq)) :=
    (Real.exp_pos _).le
  have hinv_nn : 0 ≤ (1 : ℝ) / Real.sqrt (2 * Real.pi * G.varSq) :=
    div_nonneg (by linarith) hsqrt_nn
  exact mul_nonneg hinv_nn hexp_nn

/-- Pointwise bound: for `|q.1| ≤ 1`, `|q.1 * q.2.density x| ≤ q.2.density x`. -/
private lemma SDL1TB_abs_component_le
    (q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF) (x : ℝ)
    (hq1 : |q.1| ≤ 1) :
    |q.1 * q.2.density x| ≤ q.2.density x := by
  rw [abs_mul]
  have h_dens_nn : 0 ≤ q.2.density x := SDL1TB_density_nn q.2 x
  have h_dens_abs : |q.2.density x| = q.2.density x := abs_of_nonneg h_dens_nn
  rw [h_dens_abs]
  -- |q.1| * G_q.density x ≤ 1 * G_q.density x = G_q.density x
  calc |q.1| * q.2.density x ≤ 1 * q.2.density x :=
        mul_le_mul_of_nonneg_right hq1 h_dens_nn
    _ = q.2.density x := one_mul _

/-- Pointwise bound aggregated over a list: if for every `q ∈ l`, `|q.1| ≤ 1`,
then `Σ_q |q.1 * q.2.density x| ≤ Σ_q q.2.density x`. -/
private lemma SDL1TB_list_abs_sum_le_density_sum
    (l : List (ℝ × Workspace.Types.GaussianPDF.GaussianPDF)) (x : ℝ)
    (hl : ∀ q ∈ l, |q.1| ≤ 1) :
    (l.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
        |q.1 * q.2.density x|)).sum
    ≤ (l.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
        q.2.density x)).sum := by
  induction l with
  | nil => simp
  | cons q rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hq_mem : q ∈ q :: rest := List.mem_cons_self
    have hq1 : |q.1| ≤ 1 := hl q hq_mem
    have hq_bd : |q.1 * q.2.density x| ≤ q.2.density x :=
      SDL1TB_abs_component_le q x hq1
    have hrest_all : ∀ q' ∈ rest, |q'.1| ≤ 1 := by
      intro q' hq'
      exact hl q' (List.mem_cons_of_mem _ hq')
    have hrest := ih hrest_all
    linarith

theorem SublemmaSignedDensityL1TailBound :
    ∃ K_T : ℝ, 0 < K_T ∧
      ∀ (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
        (ε : ℝ), 0 < ε → ε ≤ 1 →
        S.components.length ≤ 4 →
        (∀ q ∈ S.components,
          |q.fst| ≤ 1 ∧ |q.snd.mean| ≤ 1 / ε
          ∧ ε ^ 12 ≤ q.snd.varSq ∧ q.snd.varSq ≤ 2) →
        ∫ x in {x : ℝ | 2 / ε ≤ |x|}, |S.density x| ≤
          K_T * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := by
  obtain ⟨K, hK_pos, hK_bound⟩ := SDL1TB_per_component_density_bound
  refine ⟨4 * K, by positivity, ?_⟩
  intro S ε hε_pos hε_le hS_len hS_bounds
  set T : Set ℝ := {x : ℝ | 2 / ε ≤ |x|} with hT_def
  have hT_meas : MeasurableSet T := SDL1TB_T_measurable ε
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hinv_pos : (0 : ℝ) < 1 / ε := by positivity
  have hinv_ge : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε_pos]; linarith
  have hinv_pow_pos : ∀ k : ℕ, (0 : ℝ) < (1 / ε) ^ k := fun k => by positivity
  have hinv_pow_nn : ∀ k : ℕ, (0 : ℝ) ≤ (1 / ε) ^ k := fun k => (hinv_pow_pos k).le
  have hexp_pos : 0 < Real.exp (-1 / (4 * ε ^ 2)) := Real.exp_pos _
  have hexp_nn : 0 ≤ Real.exp (-1 / (4 * ε ^ 2)) := hexp_pos.le
  have hK_nn : 0 ≤ K := hK_pos.le
  -- Step A: pointwise |S.density x| ≤ Σ_q G_q.density x for any x.
  have h_pointwise : ∀ x : ℝ,
      |S.density x|
        ≤ (S.components.map
            (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              q.2.density x)).sum := by
    intro x
    rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq]
    -- |Σ_q (q.1 * q.2.density x)| ≤ Σ_q |q.1 * q.2.density x| ≤ Σ_q q.2.density x
    have h1 := SDL1TB_abs_list_sum_le_sum_abs S.components
      (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF => q.1 * q.2.density x)
    -- Show Σ_q |q.1 * q.2.density x| ≤ Σ_q q.2.density x via list induction.
    have h2 :
        (S.components.map
          (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            |q.1 * q.2.density x|)).sum
        ≤ (S.components.map
          (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            q.2.density x)).sum := by
      apply SDL1TB_list_abs_sum_le_density_sum
      intro q hq
      exact (hS_bounds q hq).1
    exact h1.trans h2
  -- Step B: define the per-component tail integral bound and the per-component
  -- absolute value identity (G_q.density ≥ 0 so |∫| = ∫).
  have h_density_int_eq : ∀ q ∈ S.components,
      |∫ x in T, q.2.density x| = ∫ x in T, q.2.density x := by
    intro q hq
    apply abs_of_nonneg
    apply MeasureTheory.integral_nonneg
    intro x
    exact SDL1TB_density_nn q.2 x
  have h_per_component_int_le : ∀ q ∈ S.components,
      ∫ x in T, q.2.density x ≤ K * (1 / ε) ^ 6 * Real.exp (-1 / (4 * ε ^ 2)) := by
    intro q hq
    obtain ⟨_, hμ, _, hσ_hi⟩ := hS_bounds q hq
    have h := hK_bound q.2 ε hε_pos hε_le hμ hσ_hi
    rw [h_density_int_eq q hq] at h
    exact h
  -- Step C: Each integral is nonneg.
  have h_per_component_int_nn : ∀ q ∈ S.components,
      0 ≤ ∫ x in T, q.2.density x := by
    intro q hq
    apply MeasureTheory.integral_nonneg
    intro x
    exact SDL1TB_density_nn q.2 x
  -- Step D: ∫_T |S.density x| dx ≤ ∫_T (Σ_q G_q.density x) dx.
  -- For this, we need:
  --   (a) |S.density| is integrable on T.
  --   (b) Σ_q G_q.density is integrable on T.
  --   (c) pointwise bound holds a.e.
  -- (a) is automatic via `S.density`'s integrability... let me first establish
  -- integrability of the sum.
  have h_sum_density_integrable :
      Integrable (fun x : ℝ =>
        (S.components.map
          (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            q.2.density x)).sum) volume := by
    clear h_per_component_int_le h_density_int_eq h_per_component_int_nn
    induction S.components with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact integrable_zero _ _ _
    | cons q rest ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Integrable.add
      · exact SDL1TB_integrable_density q.2
      · exact ih
  have h_sum_density_integrableOn :
      IntegrableOn (fun x : ℝ =>
        (S.components.map
          (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            q.2.density x)).sum) T volume :=
    h_sum_density_integrable.integrableOn
  -- S.density is integrable on T:
  have h_S_density_integrable : Integrable (fun x : ℝ => S.density x) volume := by
    have : (fun x : ℝ => S.density x) =
        (fun x : ℝ =>
          (S.components.map
            (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              q.1 * q.2.density x)).sum) := by
      funext x
      rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq]
    rw [this]
    clear h_per_component_int_le h_density_int_eq h_per_component_int_nn
      h_sum_density_integrable h_sum_density_integrableOn h_pointwise
    induction S.components with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact integrable_zero _ _ _
    | cons q rest ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Integrable.add
      · exact (SDL1TB_integrable_density q.2).const_mul q.1
      · exact ih
  have h_S_density_abs_integrable : Integrable (fun x : ℝ => |S.density x|) volume :=
    h_S_density_integrable.abs
  have h_S_density_abs_integrableOn :
      IntegrableOn (fun x : ℝ => |S.density x|) T volume :=
    h_S_density_abs_integrable.integrableOn
  -- Now do the integral inequality.
  have h_integral_bound :
      ∫ x in T, |S.density x| ≤
      ∫ x in T,
        (S.components.map
          (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            q.2.density x)).sum := by
    apply MeasureTheory.setIntegral_mono_on h_S_density_abs_integrableOn
      h_sum_density_integrableOn hT_meas
    intro x _
    exact h_pointwise x
  -- Step E: integral of the sum = sum of integrals.
  have h_sum_integral_eq :
      ∫ x in T,
          (S.components.map
            (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              q.2.density x)).sum
        = (S.components.map
            (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              ∫ x in T, q.2.density x)).sum := by
    clear h_per_component_int_le h_density_int_eq h_per_component_int_nn
      h_S_density_abs_integrable h_S_density_abs_integrableOn h_integral_bound
      h_pointwise h_S_density_integrable
    induction S.components with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      rw [show (fun _ : ℝ => (0 : ℝ)) = (0 : ℝ → ℝ) from rfl]
      exact integral_zero _ _
    | cons q rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hq : IntegrableOn (fun x : ℝ => q.2.density x) T volume :=
        SDL1TB_integrableOn_density q.2 T
      have hrest :
          IntegrableOn (fun x : ℝ =>
            (rest.map (fun r : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              r.2.density x)).sum) T volume := by
        clear ih
        induction rest with
        | nil =>
          simp only [List.map_nil, List.sum_nil]
          exact (integrable_zero _ _ _).integrableOn
        | cons r rest2 ih2 =>
          simp only [List.map_cons, List.sum_cons]
          apply Integrable.add
          · exact SDL1TB_integrableOn_density r.2 T
          · exact ih2
      rw [integral_add hq hrest, ih]
  rw [h_sum_integral_eq] at h_integral_bound
  -- Step F: bound the list-sum by 4 * K * (1/ε)^6 * exp(-1/(4ε²)).
  have h_list_bound :
      (S.components.map
        (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
          ∫ x in T, q.2.density x)).sum
      ≤ 4 * (K * (1 / ε) ^ 6 * Real.exp (-1 / (4 * ε ^ 2))) := by
    apply SDL1TB_list_sum_le_of_pointwise_le_of_length_le
      S.components _ _ 4 (by positivity) ?_ hS_len
    intro q hq
    exact h_per_component_int_le q hq
  -- Step G: combine: ∫ ≤ 4 * K * (1/ε)^6 * exp(...) ≤ 4 * K * (1/ε)^12 * exp(...).
  -- since (1/ε)^6 ≤ (1/ε)^12 (using hinv_ge : 1 ≤ 1/ε).
  have hpow_mono : (1 / ε) ^ 6 ≤ (1 / ε) ^ 12 := by
    apply pow_le_pow_right₀ hinv_ge
    omega
  calc ∫ x in T, |S.density x|
      ≤ (S.components.map
            (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              ∫ x in T, q.2.density x)).sum := h_integral_bound
    _ ≤ 4 * (K * (1 / ε) ^ 6 * Real.exp (-1 / (4 * ε ^ 2))) := h_list_bound
    _ ≤ 4 * (K * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2))) := by
        have hKpow : K * (1 / ε) ^ 6 ≤ K * (1 / ε) ^ 12 :=
          mul_le_mul_of_nonneg_left hpow_mono hK_nn
        have hKexp : K * (1 / ε) ^ 6 * Real.exp (-1 / (4 * ε ^ 2))
                  ≤ K * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) :=
          mul_le_mul_of_nonneg_right hKpow hexp_nn
        linarith
    _ = 4 * K * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := by ring

end Workspace.ProofLemmas
