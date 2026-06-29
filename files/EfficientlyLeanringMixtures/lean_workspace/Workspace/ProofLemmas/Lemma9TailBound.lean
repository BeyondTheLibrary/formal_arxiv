import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.MomentIntegralLinearity
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian
import Workspace.ProofLemmas.Lemma29TailMomentVarLeTwo

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open MeasureTheory

/-- Per-component tail moment bound, derived from `Lemma29TailMomentVarLeTwo`. -/
private lemma per_component_tail_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (G : Workspace.Types.GaussianPDF.GaussianPDF) (ε : ℝ) (i : ℕ),
        0 < ε → ε ≤ 1 → |G.mean| ≤ 1 / ε →
        ε ^ 12 ≤ G.varSq → G.varSq ≤ 2 → i ≤ 6 →
        |∫ x in {x : ℝ | 2 / ε ≤ |x|}, x ^ i * G.density x|
          ≤ K * (1 / ε) ^ (i + 6) * Real.exp (-1 / (4 * ε ^ 2)) := by
  obtain ⟨K_29', hK_pos, hK⟩ := Lemma29TailMomentVarLeTwo
  refine ⟨K_29', hK_pos, ?_⟩
  intro G ε i hε_pos hε_le hμ hσ_lo hσ_hi hi
  -- G.density x = (1/√(2π·G.varSq)) * exp(-(x-G.mean)²/(2·G.varSq))
  have hdens : ∀ x : ℝ,
      x ^ i * G.density x =
        x ^ i * (1 / Real.sqrt (2 * Real.pi * G.varSq))
          * Real.exp (-((x - G.mean) ^ 2) / (2 * G.varSq)) := by
    intro x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq]
    ring
  rw [show (∫ x in {x : ℝ | 2 / ε ≤ |x|}, x ^ i * G.density x)
        = ∫ x in {x : ℝ | 2 / ε ≤ |x|},
            x ^ i * (1 / Real.sqrt (2 * Real.pi * G.varSq))
              * Real.exp (-((x - G.mean) ^ 2) / (2 * G.varSq)) ∂volume from by
    refine setIntegral_congr_fun ?_ ?_
    · refine measurableSet_le measurable_const continuous_abs.measurable
    · intro x _; exact hdens x]
  have hres := hK G.mean G.varSq ε i hε_pos hε_le G.varSq_pos hσ_hi hμ hi
  -- The lemma's conclusion uses `(1/ε^(i+6))`. Convert to `(1/ε)^(i+6)`.
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hpow_eq : (1 : ℝ) / ε ^ (i + 6) = (1 / ε) ^ (i + 6) := by
    rw [one_div, one_div, inv_pow]
  calc |∫ x in {x : ℝ | 2 / ε ≤ |x|},
            x ^ i * (1 / Real.sqrt (2 * Real.pi * G.varSq))
              * Real.exp (-((x - G.mean) ^ 2) / (2 * G.varSq)) ∂volume|
      ≤ K_29' * (1 / ε ^ (i + 6)) * Real.exp (-1 / (4 * ε ^ 2)) := hres
    _ = K_29' * (1 / ε) ^ (i + 6) * Real.exp (-1 / (4 * ε ^ 2)) := by rw [hpow_eq]

/-- The set `T = {x : ℝ | 2/ε ≤ |x|}` is measurable. -/
private lemma T_measurable (ε : ℝ) : MeasurableSet {x : ℝ | 2 / ε ≤ |x|} :=
  measurableSet_le measurable_const continuous_abs.measurable

/-- Integrability of `fun x => x ^ i * G.density x` on the tail set. -/
private lemma integrableOn_xpow_density
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (i : ℕ) (T : Set ℝ) :
    IntegrableOn (fun x : ℝ => x ^ i * G.density x) T volume :=
  (SublemmaIntegrabilityXPowGaussian G i).integrableOn

/-- Integrability of `fun x => c * (x^i * G.density x)` on T. -/
private lemma integrableOn_const_mul
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (i : ℕ) (T : Set ℝ) (c : ℝ) :
    IntegrableOn (fun x : ℝ => c * (x ^ i * G.density x)) T volume :=
  (integrableOn_xpow_density G i T).const_mul c

/-- Triangle inequality for sum: `|Σ_x∈l, f x| ≤ Σ_x∈l, |f x|`. -/
private lemma abs_list_sum_le_sum_abs {α : Type*} (l : List α) (f : α → ℝ) :
    |(l.map f).sum| ≤ (l.map (fun x => |f x|)).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    calc |f a + (rest.map f).sum|
        ≤ |f a| + |(rest.map f).sum| := abs_add_le _ _
      _ ≤ |f a| + (rest.map (fun x => |f x|)).sum := by linarith

/-- Sum of mapped constant equals length times constant (as natural number scalar). -/
private lemma list_map_const_sum {α : Type*} (l : List α) (b : ℝ) :
    (l.map (fun _ : α => b)).sum = l.length • b := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rw [add_smul, one_smul, add_comm]

/-- Bound on list sum from pointwise bound + length bound. -/
private lemma list_sum_le_of_pointwise_le_of_length_le
    {α : Type*} (l : List α) (f : α → ℝ) (b : ℝ) (n : ℕ)
    (hb : 0 ≤ b) (hf : ∀ x ∈ l, f x ≤ b) (hlen : l.length ≤ n) :
    (l.map f).sum ≤ n * b := by
  have h1 : (l.map f).sum ≤ (l.map (fun _ : α => b)).sum := by
    apply List.sum_le_sum
    intro x hx
    exact hf x hx
  have h2 : (l.map (fun _ : α => b)).sum = l.length * b := by
    rw [list_map_const_sum]
    rw [nsmul_eq_mul]
  have h3 : (l.length : ℝ) * b ≤ (n : ℝ) * b := by
    apply mul_le_mul_of_nonneg_right _ hb
    exact_mod_cast hlen
  linarith

theorem Lemma9TailBound :
    ∃ K_tail : ℝ, 0 < K_tail ∧
      ∀ (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
        (p : Polynomial ℝ) (ε C : ℝ),
        0 < ε → ε ≤ 1 →
        0 < C →
        S.components.length ≤ 4 →
        (∀ q ∈ S.components,
            |q.fst| ≤ 1 ∧ |q.snd.mean| ≤ 1 / ε
            ∧ ε ^ 12 ≤ q.snd.varSq ∧ q.snd.varSq ≤ 2) →
        p.natDegree ≤ 6 →
        (∀ i ≤ 6, |p.coeff i| ≤ C * (1 / ε) ^ (6 - i)) →
        |∫ x in {x : ℝ | 2 / ε ≤ |x|}, Polynomial.eval x p * S.density x|
          ≤ K_tail * C * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := by
  obtain ⟨K, hK_pos, hK⟩ := per_component_tail_bound
  refine ⟨28 * K, by positivity, ?_⟩
  intro S p ε C hε_pos hε_le hC_pos hS_len hS_bounds hp_deg hp_coeff
  set T : Set ℝ := {x : ℝ | 2 / ε ≤ |x|} with hT_def
  have hT_meas : MeasurableSet T := T_measurable ε
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hinv_pos : (0 : ℝ) < 1 / ε := by positivity
  have hinv_ge : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε_pos]; linarith
  have hinv_pow_pos : ∀ k : ℕ, (0 : ℝ) < (1 / ε) ^ k := fun k => by positivity
  have hinv_pow_nn : ∀ k : ℕ, (0 : ℝ) ≤ (1 / ε) ^ k := fun k => (hinv_pow_pos k).le
  have hexp_pos : 0 < Real.exp (-1 / (4 * ε ^ 2)) := Real.exp_pos _
  have hexp_nn : 0 ≤ Real.exp (-1 / (4 * ε ^ 2)) := hexp_pos.le
  have hC_nn : 0 ≤ C := hC_pos.le
  have hK_nn : 0 ≤ K := hK_pos.le
  -- Step 1: rewrite Polynomial.eval x p over Finset.range 7.
  have hp_deg' : p.natDegree < 7 := by omega
  have h_eval : ∀ x : ℝ,
      Polynomial.eval x p = ∑ i ∈ Finset.range 7, p.coeff i * x ^ i := fun x =>
    Polynomial.eval_eq_sum_range' (n := 7) hp_deg' x
  -- Step 2: substitute into the integrand.
  rw [show (∫ x in T, Polynomial.eval x p * S.density x)
        = ∫ x in T, (∑ i ∈ Finset.range 7, p.coeff i * x ^ i) * S.density x from by
    refine setIntegral_congr_fun hT_meas ?_
    intro x _; simp only; rw [h_eval]]
  -- Distribute multiplication and expand S.density:
  -- (Σ_i c_i x^i) * S.density x = Σ_i Σ_q (c_i * q.1) * (x^i * q.2.density x)
  have h_distribute : ∀ x : ℝ,
      (∑ i ∈ Finset.range 7, p.coeff i * x ^ i) * S.density x
        = ∑ i ∈ Finset.range 7,
            (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum := by
    intro x
    rw [Workspace.Types.SignedGaussianCombination.SignedGaussianCombination.density_eq,
        Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    -- p.coeff i * x^i * (Σ_q q.1 * q.2.density x)
    --   = Σ_q (p.coeff i * q.1) * (x^i * q.2.density x)
    induction S.components with
    | nil => simp
    | cons q rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih]
      ring
  rw [show (∫ x in T, (∑ i ∈ Finset.range 7, p.coeff i * x ^ i) * S.density x)
        = ∫ x in T, ∑ i ∈ Finset.range 7,
            (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
              (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum from by
    refine setIntegral_congr_fun hT_meas ?_
    intro x _; simp only; exact h_distribute x]
  -- Step 3: pull the finite sum out of the integral.
  have h_int_each : ∀ i ∈ Finset.range 7,
      IntegrableOn
        (fun x : ℝ => (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum) T volume := by
    intro i _
    -- Sum of integrables.
    have : ∀ q ∈ S.components,
        IntegrableOn (fun x : ℝ => (p.coeff i * q.1) * (x ^ i * q.2.density x))
          T volume := fun q _ => integrableOn_const_mul q.2 i T (p.coeff i * q.1)
    -- Build integrability of the list sum.
    revert this
    induction S.components with
    | nil =>
      intro _
      simp only [List.map_nil, List.sum_nil]
      exact (integrable_zero _ _ _).integrableOn
    | cons q rest ih =>
      intro hall
      simp only [List.map_cons, List.sum_cons]
      apply Integrable.add
      · exact hall q (List.mem_cons_self)
      · apply ih
        intro r hr
        exact hall r (List.mem_cons_of_mem _ hr)
  rw [MeasureTheory.integral_finset_sum _ h_int_each]
  -- Step 4: pull list sum out of each integral.
  have h_pull_list : ∀ i ∈ Finset.range 7,
      ∫ x in T,
          (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum
        = (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            ∫ x in T, (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum := by
    intro i _
    -- Induction on S.components.
    induction S.components with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      rw [show (fun _ : ℝ => (0 : ℝ)) = (0 : ℝ → ℝ) from rfl]
      exact integral_zero _ _
    | cons q rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hq : IntegrableOn (fun x : ℝ => (p.coeff i * q.1) * (x ^ i * q.2.density x))
          T volume := integrableOn_const_mul q.2 i T (p.coeff i * q.1)
      have hrest : IntegrableOn
          (fun x : ℝ => (rest.map (fun r : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            (p.coeff i * r.1) * (x ^ i * r.2.density x))).sum) T volume := by
        -- Same as h_int_each but for rest.
        clear ih
        induction rest with
        | nil =>
          simp only [List.map_nil, List.sum_nil]
          exact (integrable_zero _ _ _).integrableOn
        | cons r rest2 ih2 =>
          simp only [List.map_cons, List.sum_cons]
          apply Integrable.add
          · exact integrableOn_const_mul r.2 i T (p.coeff i * r.1)
          · exact ih2
      rw [integral_add hq hrest, ih]
  -- Apply h_pull_list within the outer finset sum.
  rw [show ∑ i ∈ Finset.range 7,
        ∫ x in T,
          (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum
        = ∑ i ∈ Finset.range 7,
          (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            ∫ x in T, (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum from by
    apply Finset.sum_congr rfl
    intro i hi
    exact h_pull_list i hi]
  -- Step 5: pull the constant out of each per-component integral.
  rw [show ∑ i ∈ Finset.range 7,
        (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
          ∫ x in T, (p.coeff i * q.1) * (x ^ i * q.2.density x))).sum
        = ∑ i ∈ Finset.range 7,
          (S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            (p.coeff i * q.1) * ∫ x in T, x ^ i * q.2.density x)).sum from by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply List.map_congr_left
    intro q _
    exact MeasureTheory.integral_const_mul _ _]
  -- Step 6: triangle inequality on the finset sum.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Now bound each summand.
  have h_summand_bound : ∀ i ∈ Finset.range 7,
      |(S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
        (p.coeff i * q.1) * ∫ x in T, x ^ i * q.2.density x)).sum|
      ≤ 4 * (C * K * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2))) := by
    intro i hi
    have hi_le : i ≤ 6 := by
      have := Finset.mem_range.mp hi
      omega
    -- Apply triangle inequality on the list sum.
    refine (abs_list_sum_le_sum_abs S.components _).trans ?_
    -- Now bound each (component) summand: |(c_i · a_q) · ∫_T x^i · G_q.density| ≤
    -- C·(1/ε)^(6-i) · 1 · K·(1/ε)^(i+6)·exp(-1/(4ε²)) = C·K·(1/ε)^12·exp(-1/(4ε²)).
    -- Then # components ≤ 4 ⇒ sum ≤ 4 · C · K · (1/ε)^12 · exp(-1/(4ε²)).
    apply list_sum_le_of_pointwise_le_of_length_le S.components _ _ 4
      (by positivity) ?_ hS_len
    intro q hq
    obtain ⟨ha_q, hμ_q, hσ_lo_q, hσ_hi_q⟩ := hS_bounds q hq
    rw [abs_mul]
    have h1 : |p.coeff i * q.1| ≤ C * (1 / ε) ^ (6 - i) := by
      rw [abs_mul]
      calc |p.coeff i| * |q.1|
          ≤ (C * (1 / ε) ^ (6 - i)) * 1 := by
            apply mul_le_mul (hp_coeff i hi_le) ha_q (abs_nonneg _)
            positivity
        _ = C * (1 / ε) ^ (6 - i) := by ring
    have h2 : |∫ x in T, x ^ i * q.2.density x|
        ≤ K * (1 / ε) ^ (i + 6) * Real.exp (-1 / (4 * ε ^ 2)) :=
      hK q.2 ε i hε_pos hε_le hμ_q hσ_lo_q hσ_hi_q hi_le
    have habs_pq_nn : 0 ≤ |p.coeff i * q.1| := abs_nonneg _
    have habs_int_nn : 0 ≤ |∫ x in T, x ^ i * q.2.density x| := abs_nonneg _
    have hbound_int_nn : (0 : ℝ) ≤ K * (1 / ε) ^ (i + 6) * Real.exp (-1 / (4 * ε ^ 2)) := by
      positivity
    have hbound_pq_nn : (0 : ℝ) ≤ C * (1 / ε) ^ (6 - i) := by positivity
    calc |p.coeff i * q.1| * |∫ x in T, x ^ i * q.2.density x|
        ≤ (C * (1 / ε) ^ (6 - i)) * (K * (1 / ε) ^ (i + 6) * Real.exp (-1 / (4 * ε ^ 2))) := by
          apply mul_le_mul h1 h2 habs_int_nn hbound_pq_nn
      _ = C * K * ((1 / ε) ^ (6 - i) * (1 / ε) ^ (i + 6)) * Real.exp (-1 / (4 * ε ^ 2)) := by
          ring
      _ = C * K * (1 / ε) ^ ((6 - i) + (i + 6)) * Real.exp (-1 / (4 * ε ^ 2)) := by
          rw [← pow_add]
      _ = C * K * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := by
          have : (6 - i) + (i + 6) = 12 := by omega
          rw [this]
  -- Sum bound: 7 (finite-summand count) × per-summand bound.
  calc ∑ i ∈ Finset.range 7,
          |(S.components.map (fun q : ℝ × Workspace.Types.GaussianPDF.GaussianPDF =>
            (p.coeff i * q.1) * ∫ x in T, x ^ i * q.2.density x)).sum|
      ≤ ∑ _i ∈ Finset.range 7,
          4 * (C * K * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact h_summand_bound i hi
    _ = 7 * (4 * (C * K * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)))) := by
        rw [Finset.sum_const]
        simp [Finset.card_range]
    _ = 28 * K * C * (1 / ε) ^ 12 * Real.exp (-1 / (4 * ε ^ 2)) := by ring

end Workspace.ProofLemmas
