import Mathlib
import Workspace.ProofLemmas.PigeonholeOverSubIntervals

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open MeasureTheory intervalIntegral Polynomial

namespace Workspace.ProofLemmas

/-- Evaluation of the `foldr` product of linear factors. -/
private lemma bulk_eval_foldr (xs : List ℝ) (x : ℝ) :
    Polynomial.eval x (xs.foldr (fun a q => q * (Polynomial.X - Polynomial.C a))
      (1 : Polynomial ℝ)) = (xs.map (fun a => x - a)).prod := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [Polynomial.eval_mul, ih]
    simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring

/-- `|∏ (x - z)| = ∏ |x - z|`. -/
private lemma bulk_abs_prod (x : ℝ) (l : List ℝ) :
    |(l.map (fun z => x - z)).prod| = (l.map (fun z => |x - z|)).prod := by
  induction l with
  | nil => simp
  | cons y ys ih => simp only [List.map_cons, List.prod_cons, abs_mul, ih]

/-- One-sided / two-sided floor for the absolute value of the foldr-product
polynomial `p₀ = ∏ (x - z_j)`, on a trimmed interval.  We trim by `γ` only at
the ends where roots lie: `loTrim`/`hiTrim` are booleans saying whether to trim
the lower/upper end.  Concretely, for `x ∈ [a + (if loTrim then γ else 0),
b - (if hiTrim then γ else 0)]`, if every root that is `≤ a` is accounted by
`loTrim = true` and every root that is `≥ b` by `hiTrim = true`, then
`γ ^ xs.length ≤ ∏ |x - z_j|`. -/
private lemma bulk_floor_general
    (γ : ℝ) (hγ : 0 < γ) (a b : ℝ)
    (xs : List ℝ)
    (loTrim hiTrim : Bool)
    (h_roots : ∀ z ∈ xs, z ≤ a ∨ b ≤ z)
    (h_lo : ∀ z ∈ xs, z ≤ a → loTrim = true)
    (h_hi : ∀ z ∈ xs, b ≤ z → hiTrim = true) :
    ∀ x : ℝ,
      a + (if loTrim then γ else 0) ≤ x →
      x ≤ b - (if hiTrim then γ else 0) →
      γ ^ xs.length ≤ (xs.map (fun z => |x - z|)).prod := by
  intro x hx_lo hx_hi
  have h_each : ∀ z ∈ xs, γ ≤ |x - z| := by
    intro z hz
    rcases h_roots z hz with hle | hge
    · -- z ≤ a, so loTrim = true, so a + γ ≤ x, hence x - z ≥ x - a ≥ γ
      have hlt : loTrim = true := h_lo z hz hle
      simp only [hlt, if_true] at hx_lo
      have h1 : γ ≤ x - z := by linarith
      have h2 : 0 ≤ x - z := le_trans hγ.le h1
      rw [abs_of_nonneg h2]; exact h1
    · -- b ≤ z, so hiTrim = true, so x ≤ b - γ, hence z - x ≥ b - x ≥ γ
      have hht : hiTrim = true := h_hi z hz hge
      simp only [hht, if_true] at hx_hi
      have h1 : x - z ≤ -γ := by linarith
      have h2 : x - z ≤ 0 := le_trans h1 (by linarith)
      rw [abs_of_nonpos h2]; linarith
  -- ∏ |x - z| ≥ γ ^ length
  clear hx_lo hx_hi h_roots h_lo h_hi
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have hy : γ ≤ |x - y| := h_each y (List.mem_cons_self)
    have hys : ∀ z ∈ ys, γ ≤ |x - z| := fun z hz => h_each z (List.mem_cons_of_mem _ hz)
    have ih' := ih hys
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    have hprods_nn : 0 ≤ (List.map (fun z => |x - z|) ys).prod := by
      apply List.prod_nonneg
      intro u hu
      simp only [List.mem_map] at hu
      obtain ⟨w, _, hw⟩ := hu
      rw [← hw]; exact abs_nonneg _
    calc γ ^ ys.length * γ
        ≤ (List.map (fun z => |x - z|) ys).prod * γ :=
          mul_le_mul_of_nonneg_right ih' hγ.le
      _ ≤ (List.map (fun z => |x - z|) ys).prod * |x - y| :=
          mul_le_mul_of_nonneg_left hy hprods_nn
      _ = |x - y| * (List.map (fun z => |x - z|) ys).prod := by ring

/-- Generic pigeonhole extraction of a sign-constant sub-interval for a
continuous `h` on `[-R, R]`, whose zeros are exactly the sorted list `xs`
(length ≤ 6).  Returns a piece `(a, b)` with `-R ≤ a < b ≤ R`, no zero strictly
inside, mass at least `δ / 7`, and endpoints each either `±R` or a zero of `h`.
Mirrors `SublemmaExtractSignConstantSubInterval` but for a generic `h`. -/
theorem bulk_extract_piece
    (R δ : ℝ) (hRpos : 0 < R) (hδ : 0 < δ)
    (h : ℝ → ℝ) (hcont : Continuous h)
    (xs : List ℝ) (hxs_sorted : xs.Pairwise (· < ·))
    (hxs_length : xs.length ≤ 6)
    (hxs_in_I : ∀ x ∈ xs, -R ≤ x ∧ x ≤ R)
    (hxs_zeros : ∀ x ∈ xs, h x = 0)
    (hxs_complete : ∀ y : ℝ, -R ≤ y → y ≤ R → h y = 0 → y ∈ xs)
    (h_L1 : δ ≤ ∫ x in Set.Icc (-R) R, |h x|) :
    ∃ a b : ℝ, -R ≤ a ∧ a < b ∧ b ≤ R ∧
      (a = -R ∨ h a = 0) ∧ (b = R ∨ h b = 0) ∧
      (∀ z ∈ xs, z ≤ a ∨ b ≤ z) ∧
      δ / 7 ≤ ∫ x in a..b, |h x| := by
  have habs_cont : Continuous (fun x => |h x|) := continuous_abs.comp hcont
  set a₀ : ℝ := -R with ha₀_def
  set b₀ : ℝ := R with hb₀_def
  have hab : a₀ < b₀ := by rw [ha₀_def, hb₀_def]; linarith
  have habLe : a₀ ≤ b₀ := hab.le
  have h_Icc_eq_Ioc : ∫ x in Set.Icc a₀ b₀, |h x| = ∫ x in Set.Ioc a₀ b₀, |h x| :=
    MeasureTheory.integral_Icc_eq_integral_Ioc
  have h_L1' : δ ≤ ∫ x in a₀..b₀, |h x| := by
    rw [intervalIntegral.integral_of_le habLe, ← h_Icc_eq_Ioc]; exact h_L1
  set n : ℕ := xs.length with hn_def
  have hn_le : n ≤ 6 := hxs_length
  let p : Fin (n + 2) → ℝ := fun i =>
    if i.val = 0 then a₀
    else if i.val = n + 1 then b₀
    else xs.getD (i.val - 1) 0
  have hp_0 : p ⟨0, by omega⟩ = a₀ := by
    show (if (0 : ℕ) = 0 then a₀ else _) = a₀
    rfl
  have hp_last : p (Fin.last (n + 1)) = b₀ := by
    show (if (n + 1) = 0 then a₀ else if (n+1) = n+1 then b₀ else _) = b₀
    simp
  have hp_mid : ∀ k : ℕ, ∀ (hk : k < n),
      p ⟨k + 1, by omega⟩ = xs.get ⟨k, hk⟩ := by
    intro k hk
    show (if k + 1 = 0 then a₀ else if k + 1 = n + 1 then b₀ else xs.getD ((k + 1) - 1) 0)
        = xs.get ⟨k, hk⟩
    have h1 : ¬ (k + 1 = 0) := by omega
    have h2 : ¬ (k + 1 = n + 1) := by omega
    rw [if_neg h1, if_neg h2]
    have h3 : k + 1 - 1 = k := by omega
    rw [h3, List.getD_eq_get xs 0 ⟨k, hk⟩]
  have hp_mono : Monotone p := by
    intro i j hij
    have hi_lt : i.val < n + 2 := i.isLt
    have hj_lt : j.val < n + 2 := j.isLt
    rcases Nat.lt_or_ge i.val 1 with hi_zero | hi_pos
    · have hi_eq : i.val = 0 := by omega
      have hpi : p i = a₀ := by
        show (if i.val = 0 then a₀ else _) = a₀
        rw [if_pos hi_eq]
      rw [hpi]
      rcases Nat.lt_or_ge j.val 1 with hj_zero | hj_pos
      · have hj_eq : j.val = 0 := by omega
        have hpj : p j = a₀ := by
          show (if j.val = 0 then a₀ else _) = a₀
          rw [if_pos hj_eq]
        rw [hpj]
      · rcases Nat.lt_or_ge j.val (n + 1) with hj_lt_n1 | hj_ge_n1
        · have hjne0 : ¬ (j.val = 0) := by omega
          have hjnen1 : ¬ (j.val = n + 1) := by omega
          have hpj : p j = xs.getD (j.val - 1) 0 := by
            show (if j.val = 0 then a₀ else if j.val = n + 1 then b₀ else xs.getD (j.val - 1) 0) = _
            rw [if_neg hjne0, if_neg hjnen1]
          rw [hpj]
          have hidx_lt : j.val - 1 < n := by omega
          have hidx_lt' : j.val - 1 < xs.length := hidx_lt
          rw [List.getD_eq_get xs 0 ⟨j.val - 1, hidx_lt'⟩]
          exact (hxs_in_I _ (xs.get_mem ⟨j.val - 1, hidx_lt'⟩)).1
        · have hj_eq : j.val = n + 1 := by omega
          have hjne0 : ¬ (j.val = 0) := by omega
          have hpj : p j = b₀ := by
            show (if j.val = 0 then a₀ else if j.val = n + 1 then b₀ else _) = b₀
            rw [if_neg hjne0, if_pos hj_eq]
          rw [hpj]; exact habLe
    · rcases Nat.lt_or_ge i.val (n + 1) with hi_lt_n1 | hi_ge_n1
      · have hine0 : ¬ (i.val = 0) := by omega
        have hinen1 : ¬ (i.val = n + 1) := by omega
        have hpi : p i = xs.getD (i.val - 1) 0 := by
          show (if i.val = 0 then a₀ else if i.val = n + 1 then b₀ else xs.getD (i.val - 1) 0) = _
          rw [if_neg hine0, if_neg hinen1]
        rw [hpi]
        have hi_idx : i.val - 1 < n := by omega
        have hi_idx' : i.val - 1 < xs.length := hi_idx
        rw [List.getD_eq_get xs 0 ⟨i.val - 1, hi_idx'⟩]
        have hj_pos : j.val ≥ 1 := by
          have : i.val ≤ j.val := hij
          omega
        rcases Nat.lt_or_ge j.val (n + 1) with hj_lt_n1 | hj_ge_n1
        · have hjne0 : ¬ (j.val = 0) := by omega
          have hjnen1 : ¬ (j.val = n + 1) := by omega
          have hpj : p j = xs.getD (j.val - 1) 0 := by
            show (if j.val = 0 then a₀ else if j.val = n + 1 then b₀ else xs.getD (j.val - 1) 0) = _
            rw [if_neg hjne0, if_neg hjnen1]
          rw [hpj]
          have hj_idx : j.val - 1 < n := by omega
          have hj_idx' : j.val - 1 < xs.length := hj_idx
          rw [List.getD_eq_get xs 0 ⟨j.val - 1, hj_idx'⟩]
          have hxs_le_sort : xs.Pairwise (· ≤ ·) := hxs_sorted.imp (fun h => h.le)
          have h_idx_le : (⟨i.val - 1, hi_idx'⟩ : Fin xs.length).val
                        ≤ (⟨j.val - 1, hj_idx'⟩ : Fin xs.length).val := by
            show i.val - 1 ≤ j.val - 1
            have hijv : i.val ≤ j.val := hij
            omega
          exact hxs_le_sort.rel_get_of_le h_idx_le
        · have hj_eq : j.val = n + 1 := by omega
          have hjne0 : ¬ (j.val = 0) := by omega
          have hpj : p j = b₀ := by
            show (if j.val = 0 then a₀ else if j.val = n + 1 then b₀ else _) = b₀
            rw [if_neg hjne0, if_pos hj_eq]
          rw [hpj]
          exact (hxs_in_I _ (xs.get_mem ⟨i.val - 1, hi_idx'⟩)).2
      · have hi_eq : i.val = n + 1 := by omega
        have hj_eq : j.val = n + 1 := by
          have : i.val ≤ j.val := hij
          omega
        have hine0 : ¬ (i.val = 0) := by omega
        have hjne0 : ¬ (j.val = 0) := by omega
        have hpi : p i = b₀ := by
          show (if i.val = 0 then a₀ else if i.val = n + 1 then b₀ else _) = b₀
          rw [if_neg hine0, if_pos hi_eq]
        have hpj : p j = b₀ := by
          show (if j.val = 0 then a₀ else if j.val = n + 1 then b₀ else _) = b₀
          rw [if_neg hjne0, if_pos hj_eq]
        rw [hpi, hpj]
  have hg_nonneg : ∀ x ∈ Set.Icc a₀ b₀, 0 ≤ |h x| := fun x _ => abs_nonneg _
  have hg_intIntegrable : IntervalIntegrable (fun x => |h x|) MeasureTheory.volume a₀ b₀ :=
    habs_cont.intervalIntegrable a₀ b₀
  obtain ⟨k, hk_pigeon⟩ := PigeonholeOverSubIntervals a₀ b₀ habLe
    (fun x => |h x|) hg_nonneg hg_intIntegrable n p hp_0 hp_last hp_mono δ h_L1'
  have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have h7_ge_n1 : (n + 1 : ℝ) ≤ 7 := by
    have : (n : ℝ) ≤ 6 := by exact_mod_cast hn_le
    linarith
  have h_div_le : δ / 7 ≤ δ / (n + 1 : ℝ) :=
    div_le_div_of_nonneg_left hδ.le hn1_pos h7_ge_n1
  have h_lower : δ / 7 ≤ ∫ x in (p k.castSucc)..(p k.succ), |h x| :=
    le_trans h_div_le hk_pigeon
  have hδ7_pos : (0 : ℝ) < δ / 7 := by positivity
  set a : ℝ := p k.castSucc with ha_def
  set b : ℝ := p k.succ with hb_def
  have hcast_succ_lt : k.castSucc.val < k.succ.val := by
    show k.val < k.val + 1
    omega
  have hab_le : a ≤ b := hp_mono hcast_succ_lt.le
  have h_int_pos : 0 < ∫ x in a..b, |h x| := lt_of_lt_of_le hδ7_pos h_lower
  have hab_lt : a < b := by
    by_contra hcon
    push_neg at hcon
    have hab_eq : a = b := le_antisymm hab_le hcon
    rw [hab_eq] at h_int_pos
    simp [intervalIntegral.integral_same] at h_int_pos
  have ha_ge : a₀ ≤ a := by
    have h0 : p ⟨0, by omega⟩ ≤ p k.castSucc := by
      apply hp_mono
      show (0 : ℕ) ≤ k.castSucc.val
      omega
    rw [hp_0] at h0; exact h0
  have hb_le : b ≤ b₀ := by
    have h0 : p k.succ ≤ p (Fin.last (n + 1)) := by
      apply hp_mono
      show k.succ.val ≤ (Fin.last (n + 1)).val
      have := k.isLt
      simp [Fin.last, Fin.succ]; omega
    rw [hp_last] at h0; exact h0
  -- Characterize the endpoint a = p k.castSucc.
  have h_endpoint : ∀ (i : Fin (n + 2)), p i = a₀ ∨ p i = b₀ ∨ ∃ z ∈ xs, p i = z := by
    intro i
    rcases Nat.lt_or_ge i.val 1 with hi0 | hipos
    · left
      have : i.val = 0 := by omega
      show (if i.val = 0 then a₀ else _) = a₀
      rw [if_pos this]
    · rcases Nat.lt_or_ge i.val (n + 1) with hilt | hige
      · right; right
        have hine0 : ¬ (i.val = 0) := by omega
        have hinen1 : ¬ (i.val = n + 1) := by omega
        have hpi : p i = xs.getD (i.val - 1) 0 := by
          show (if i.val = 0 then a₀ else if i.val = n + 1 then b₀ else xs.getD (i.val - 1) 0) = _
          rw [if_neg hine0, if_neg hinen1]
        have hidx : i.val - 1 < n := by omega
        have hidx' : i.val - 1 < xs.length := hidx
        refine ⟨xs.get ⟨i.val - 1, hidx'⟩, xs.get_mem _, ?_⟩
        rw [hpi, List.getD_eq_get xs 0 ⟨i.val - 1, hidx'⟩]
      · right; left
        have hi_eq : i.val = n + 1 := by omega
        have hine0 : ¬ (i.val = 0) := by omega
        show (if i.val = 0 then a₀ else if i.val = n + 1 then b₀ else _) = b₀
        rw [if_neg hine0, if_pos hi_eq]
  -- Endpoint a is either -R or a zero of h.
  have ha_end : a = -R ∨ h a = 0 := by
    rcases h_endpoint k.castSucc with h1 | h2 | h3
    · left; rw [ha_def, h1, ha₀_def]
    · -- a = b₀ = R, but a < b ≤ b₀ gives contradiction.
      exfalso
      have hab2 : a < b := hab_lt
      have : a = b₀ := by rw [ha_def, h2]
      rw [this] at hab2; linarith [hb_le]
    · right; obtain ⟨z, hz, hpz⟩ := h3
      rw [ha_def, hpz]; exact hxs_zeros z hz
  have hb_end : b = R ∨ h b = 0 := by
    rcases h_endpoint k.succ with h1 | h2 | h3
    · -- b = a₀ = -R, but a₀ ≤ a < b gives contradiction.
      exfalso
      have hab2 : a < b := hab_lt
      have : b = a₀ := by rw [hb_def, h1]
      rw [this] at hab2; linarith [ha_ge]
    · left; rw [hb_def, h2, hb₀_def]
    · right; obtain ⟨z, hz, hpz⟩ := h3
      rw [hb_def, hpz]; exact hxs_zeros z hz
  -- Roots are outside (a, b): no zero strictly inside, and xs are zeros.
  have h_roots_outside : ∀ z ∈ xs, z ≤ a ∨ b ≤ z := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    obtain ⟨hza, hzb⟩ := hcon
    -- z ∈ (a, b) and h z = 0; but (a,b) has no zeros. Derive contradiction via partition.
    have hzbound := hxs_in_I z hz
    -- z is one of the partition points (it is in xs), so z = p ⟨i+1,_⟩ for some i < n.
    rw [List.mem_iff_get] at hz
    obtain ⟨i, hxi_eq⟩ := hz
    have hi_lt : i.val < n := by rw [hn_def]; exact i.isLt
    have hp_i1 : z = p ⟨i.val + 1, by omega⟩ := by
      rw [hp_mid i.val hi_lt, ← hxi_eq]
    set j : Fin (n + 2) := ⟨i.val + 1, by omega⟩ with hj_def
    rw [hp_i1] at hza hzb
    have h1 : k.castSucc.val < j.val := by
      by_contra hc
      push_neg at hc
      have : p j ≤ p k.castSucc := hp_mono hc
      rw [← ha_def] at this; linarith
    have h2 : j.val < k.succ.val := by
      by_contra hc
      push_neg at hc
      have : p k.succ ≤ p j := hp_mono hc
      rw [← hb_def] at this; linarith
    have hcs : k.castSucc.val = k.val := rfl
    have hsv : k.succ.val = k.val + 1 := rfl
    omega
  exact ⟨a, b, ha_ge, hab_lt, hb_le, ha_end, hb_end, h_roots_outside, h_lower⟩

/-- Lipschitz MVT bound: if `LipschitzWith M.toNNReal h` and `h z = 0` then
`|h x| ≤ M * |x - z|`. -/
private lemma bulk_lip_bound (h : ℝ → ℝ) (M : ℝ) (hM : 0 < M)
    (hlip : LipschitzWith (Real.toNNReal M) h) {z : ℝ} (hz : h z = 0) (x : ℝ) :
    |h x| ≤ M * |x - z| := by
  have hkey : ‖h x - h z‖ ≤ (Real.toNNReal M : ℝ) * ‖x - z‖ := hlip.norm_sub_le x z
  rw [hz, sub_zero] at hkey
  rw [Real.coe_toNNReal M hM.le] at hkey
  simpa [Real.norm_eq_abs] using hkey

/-- Left trim-loss: if `h c = 0` (Lipschitz from `c`), then
`∫_c^{c+γ} |h| ≤ M γ² / 2`. -/
private lemma bulk_trim_left (h : ℝ → ℝ) (hcont : Continuous h) (M : ℝ) (hM : 0 < M)
    (hlip : LipschitzWith (Real.toNNReal M) h) (c γ : ℝ) (hγ : 0 ≤ γ) (hc : h c = 0) :
    (∫ x in c..(c + γ), |h x|) ≤ M * γ ^ 2 / 2 := by
  have habs_cont : Continuous (fun x => |h x|) := continuous_abs.comp hcont
  have hbound : ∀ x ∈ Set.Icc c (c + γ), |h x| ≤ M * (x - c) := by
    intro x hx
    have hlb := bulk_lip_bound h M hM hlip hc x
    have : |x - c| = x - c := abs_of_nonneg (by linarith [hx.1])
    rwa [this] at hlb
  have hle : c ≤ c + γ := by linarith
  have hcalc : ∫ x in c..(c + γ), M * (x - c) = M * γ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul]
    have hsub : ∫ x in c..(c + γ), (x - c) = (∫ x in c..(c + γ), x) - ∫ _x in c..(c + γ), c :=
      intervalIntegral.integral_sub (continuous_id.intervalIntegrable _ _)
        (_root_.intervalIntegrable_const)
    rw [hsub, integral_id, intervalIntegral.integral_const]; ring
  calc (∫ x in c..(c + γ), |h x|)
      ≤ ∫ x in c..(c + γ), M * (x - c) := by
        apply intervalIntegral.integral_mono_on hle (habs_cont.intervalIntegrable _ _)
          ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
          hbound
    _ = M * γ ^ 2 / 2 := hcalc

/-- Right trim-loss: if `h c = 0`, then `∫_{c-γ}^c |h| ≤ M γ² / 2`. -/
private lemma bulk_trim_right (h : ℝ → ℝ) (hcont : Continuous h) (M : ℝ) (hM : 0 < M)
    (hlip : LipschitzWith (Real.toNNReal M) h) (c γ : ℝ) (hγ : 0 ≤ γ) (hc : h c = 0) :
    (∫ x in (c - γ)..c, |h x|) ≤ M * γ ^ 2 / 2 := by
  have habs_cont : Continuous (fun x => |h x|) := continuous_abs.comp hcont
  have hbound : ∀ x ∈ Set.Icc (c - γ) c, |h x| ≤ M * (c - x) := by
    intro x hx
    have hlb := bulk_lip_bound h M hM hlip hc x
    have : |x - c| = c - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [hx.2])
    rwa [this] at hlb
  have hle : c - γ ≤ c := by linarith
  have hcalc : ∫ x in (c - γ)..c, M * (c - x) = M * γ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul]
    have hsub : ∫ x in (c - γ)..c, (c - x) = (∫ _x in (c - γ)..c, c) - ∫ x in (c - γ)..c, x :=
      intervalIntegral.integral_sub (_root_.intervalIntegrable_const)
        (continuous_id.intervalIntegrable _ _)
    rw [hsub, integral_id, intervalIntegral.integral_const]; ring
  calc (∫ x in (c - γ)..c, |h x|)
      ≤ ∫ x in (c - γ)..c, M * (c - x) := by
        apply intervalIntegral.integral_mono_on hle (habs_cont.intervalIntegrable _ _)
          ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _)
          hbound
    _ = M * γ ^ 2 / 2 := hcalc

/-- Coefficient bound for the foldr-product: every coefficient is bounded by
`2^xs.length * Q^(xs.length)` when all roots have `|z| ≤ Q` and `1 ≤ Q`. -/
private lemma bulk_coeff_aux (Q : ℝ) (hQ1 : 1 ≤ Q) :
    ∀ (xs : List ℝ), (∀ x ∈ xs, |x| ≤ Q) →
      ∀ i : ℕ,
        |(xs.foldr (fun a q => q * (Polynomial.X - Polynomial.C a))
          (1 : Polynomial ℝ)).coeff i| ≤ 2 ^ xs.length * Q ^ xs.length := by
  have hQ0 : (0:ℝ) ≤ Q := by linarith
  intro xs
  induction xs with
  | nil =>
    intro _ i
    simp only [List.foldr_nil, List.length_nil, pow_zero, one_mul]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp
    · rw [Polynomial.coeff_one, if_neg (by omega)]; simp
  | cons a rest ih =>
    intro hbound i
    have ha : |a| ≤ Q := hbound a (List.mem_cons_self)
    have hrest : ∀ x ∈ rest, |x| ≤ Q := fun x hx => hbound x (List.mem_cons_of_mem _ hx)
    have ihr := ih hrest
    simp only [List.foldr_cons, List.length_cons]
    set q : Polynomial ℝ := rest.foldr (fun a q => q * (Polynomial.X - Polynomial.C a)) 1 with hq_def
    -- coeff i of q * (X - C a)
    match i with
    | 0 =>
      rw [Polynomial.mul_coeff_zero]
      have hXC0 : (Polynomial.X - Polynomial.C a).coeff 0 = -a := by simp
      rw [hXC0, abs_mul, abs_neg]
      calc |q.coeff 0| * |a| ≤ (2 ^ rest.length * Q ^ rest.length) * Q :=
            mul_le_mul (ihr 0) ha (abs_nonneg _) (by positivity)
        _ ≤ 2 ^ (rest.length + 1) * Q ^ (rest.length + 1) := by
            rw [pow_succ, pow_succ]; nlinarith [ihr 0, abs_nonneg (q.coeff 0),
              pow_nonneg hQ0 rest.length, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) rest.length, hQ1]
    | i' + 1 =>
      rw [Polynomial.coeff_mul_X_sub_C]
      have hpr : (0:ℝ) ≤ 2 ^ rest.length * Q ^ rest.length := by positivity
      calc |q.coeff i' - q.coeff (i' + 1) * a|
          ≤ |q.coeff i'| + |q.coeff (i' + 1) * a| := abs_sub _ _
        _ = |q.coeff i'| + |q.coeff (i' + 1)| * |a| := by rw [abs_mul]
        _ ≤ (2 ^ rest.length * Q ^ rest.length) + (2 ^ rest.length * Q ^ rest.length) * Q := by
            apply add_le_add (ihr i')
            exact mul_le_mul (ihr (i' + 1)) ha (abs_nonneg _) (by positivity)
        _ ≤ 2 ^ (rest.length + 1) * Q ^ (rest.length + 1) := by
            rw [pow_succ, pow_succ]
            nlinarith [hpr, hQ1, mul_nonneg hpr hQ0]

/-- For roots in `[-Q, Q]` with `1 ≤ Q` and `xs.length ≤ 6`, every coefficient of
the foldr-product is bounded by `64 * Q^6`. -/
theorem bulk_coeff_bound (Q : ℝ) (hQ1 : 1 ≤ Q) (xs : List ℝ)
    (hlen : xs.length ≤ 6) (hbound : ∀ x ∈ xs, |x| ≤ Q) (i : ℕ) :
    |(xs.foldr (fun a q => q * (Polynomial.X - Polynomial.C a))
        (1 : Polynomial ℝ)).coeff i| ≤ 64 * Q ^ 6 := by
  have hQ0 : (0:ℝ) ≤ Q := by linarith
  have := bulk_coeff_aux Q hQ1 xs hbound i
  have h2 : (2:ℝ) ^ xs.length ≤ 64 := by
    calc (2:ℝ) ^ xs.length ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hlen
      _ = 64 := by norm_num
  have hQ : Q ^ xs.length ≤ Q ^ 6 := pow_le_pow_right₀ hQ1 hlen
  calc |(xs.foldr (fun a q => q * (Polynomial.X - Polynomial.C a)) 1).coeff i|
      ≤ 2 ^ xs.length * Q ^ xs.length := this
    _ ≤ 64 * Q ^ 6 := by
        apply mul_le_mul h2 hQ (by positivity) (by norm_num)

/-- `natDegree` of the foldr-product of linear factors is at most the list length. -/
theorem bulk_natDegree_le (xs : List ℝ) :
    (xs.foldr (fun a q => q * (Polynomial.X - Polynomial.C a)) (1 : Polynomial ℝ)).natDegree
      ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldr_cons, List.length_cons]
    apply le_trans Polynomial.natDegree_mul_le
    have hXC : (Polynomial.X - Polynomial.C a).natDegree ≤ 1 := by
      apply le_trans (Polynomial.natDegree_sub_le _ _); simp
    omega

/-- **Generic boundary-trim bulk lower bound.**

For a continuous, `M`-Lipschitz `h : ℝ → ℝ` on `[-R, R]` whose zeros are exactly
the sorted list `xs` (length ≤ 6, all simple), with the sign-matching polynomial
`p₀ = ∏ⱼ (X - zⱼ)` and `σ ∈ {±1}` such that `σ · p₀ · h ≥ 0` on `[-R, R]`, and
total mass `δ ≤ ∫_{[-R,R]} |h|` with `0 < δ ≤ M`, the boundary-trim argument with
trim `γ = √(δ / (28 M))` gives

  `3 · δ⁴ / (28⁴ · M³) ≤ ∫_{-R..R} σ · (eval x p₀) · h x`. -/
theorem bulk_lower_bound
    (R δ M : ℝ) (hR : 1 ≤ R) (hδ : 0 < δ) (hδM : δ ≤ M) (hM : 0 < M)
    (h : ℝ → ℝ) (hcont : Continuous h)
    (hlip : LipschitzWith (Real.toNNReal M) h)
    (xs : List ℝ) (hxs_sorted : xs.Pairwise (· < ·))
    (hxs_length : xs.length ≤ 6)
    (hxs_in_I : ∀ x ∈ xs, -R ≤ x ∧ x ≤ R)
    (hxs_zeros : ∀ x ∈ xs, h x = 0)
    (hxs_complete : ∀ y : ℝ, -R ≤ y → y ≤ R → h y = 0 → y ∈ xs)
    (p₀ : Polynomial ℝ)
    (hp0_def : p₀ = xs.foldr (fun a q => q * (Polynomial.X - Polynomial.C a))
                        (1 : Polynomial ℝ))
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hsign : ∀ x : ℝ, |x| ≤ R → 0 ≤ σ * Polynomial.eval x p₀ * h x)
    (h_L1 : δ ≤ ∫ x in Set.Icc (-R) R, |h x|) :
    3 * δ ^ 4 / (28 ^ 4 * M ^ 3) ≤
      ∫ x in (-R)..R, σ * Polynomial.eval x p₀ * h x := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  -- extract the sign-constant piece
  obtain ⟨a, b, ha_ge, hab_lt, hb_le, ha_end, hb_end, h_roots_outside, h_mass⟩ :=
    bulk_extract_piece R δ hRpos hδ h hcont xs hxs_sorted hxs_length hxs_in_I hxs_zeros
      hxs_complete h_L1
  -- trim parameter γ = √(δ/(28 M))
  set γ : ℝ := Real.sqrt (δ / (28 * M)) with hγ_def
  have h28M_pos : (0 : ℝ) < 28 * M := by positivity
  have hγ_pos : 0 < γ := by
    rw [hγ_def]; exact Real.sqrt_pos.mpr (by positivity)
  have hγ_sq : γ ^ 2 = δ / (28 * M) := by
    rw [hγ_def, sq]
    exact Real.mul_self_sqrt (by positivity)
  have hMγ2 : M * γ ^ 2 = δ / 28 := by
    rw [hγ_sq]; field_simp
  -- γ ≤ 1 since γ² = δ/(28M) ≤ 1/28 ≤ 1 (δ ≤ M)
  have hγ_le1 : γ ≤ 1 := by
    have hγ2_le : γ ^ 2 ≤ 1 := by
      rw [hγ_sq, div_le_one h28M_pos]; nlinarith [hδM, hM.le]
    nlinarith [hγ_pos, hγ2_le]
  -- continuity / integrability
  have habs_cont : Continuous (fun x => |h x|) := continuous_abs.comp hcont
  have hint_abs : ∀ u v : ℝ, IntervalIntegrable (fun x => |h x|) volume u v :=
    fun u v => habs_cont.intervalIntegrable u v
  have hpoly_cont : Continuous (fun x : ℝ => Polynomial.eval x p₀) := p₀.continuous
  -- Width lower bound `2γ ≤ b - a`.
  -- Helper: when a zero endpoint exists, |h| ≤ M*(b-a) on [a,b], so δ/7 ≤ M*(b-a)².
  have hba_pos : 0 < b - a := by linarith
  -- 2γ = √(δ/(7M)).
  have h2γ_sq : (2 * γ) ^ 2 = δ / (7 * M) := by
    have : (2 * γ) ^ 2 = 4 * γ ^ 2 := by ring
    rw [this, hγ_sq]; field_simp; ring
  have h2γ_pos : 0 < 2 * γ := by positivity
  -- width-from-zero-endpoint helper
  have width_from_zero : ∀ z, h z = 0 → (z = a ∨ z = b) → 2 * γ ≤ b - a := by
    intro z hz hzab
    have hbound : ∀ x ∈ Set.Icc a b, |h x| ≤ M * (b - a) := by
      intro x hx
      have hlb := bulk_lip_bound h M hM hlip hz x
      have hxz : |x - z| ≤ b - a := by
        obtain ⟨hxa, hxb⟩ := hx
        rw [abs_le]
        rcases hzab with rfl | rfl
        · constructor <;> linarith
        · constructor <;> linarith
      calc |h x| ≤ M * |x - z| := hlb
        _ ≤ M * (b - a) := by apply mul_le_mul_of_nonneg_left hxz hM.le
    -- δ/7 ≤ ∫_a^b |h| ≤ M*(b-a)*(b-a)
    have hint_le : ∫ x in a..b, |h x| ≤ ∫ _x in a..b, M * (b - a) := by
      apply intervalIntegral.integral_mono_on hab_lt.le (hint_abs a b)
        (_root_.intervalIntegrable_const) hbound
    rw [intervalIntegral.integral_const] at hint_le
    simp only [smul_eq_mul] at hint_le
    have hmass2 : δ / 7 ≤ (b - a) * (M * (b - a)) := le_trans h_mass hint_le
    -- (b-a)² ≥ δ/(7M) = (2γ)²
    have hsq : (2 * γ) ^ 2 ≤ (b - a) ^ 2 := by
      rw [h2γ_sq]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 7 * M)]
      nlinarith [hmass2, hba_pos, hM.le]
    nlinarith [hsq, h2γ_pos, hba_pos]
  have h_2γ_le_width : 2 * γ ≤ b - a := by
    rcases ha_end with haR | haz
    · rcases hb_end with hbR | hbz
      · -- a = -R, b = R: width = 2R ≥ 2 ≥ 2γ
        have : b - a = 2 * R := by rw [haR, hbR]; ring
        rw [this]
        have hγR : 2 * γ ≤ 2 := by nlinarith [hγ_le1, hγ_pos]
        nlinarith [hR, hγR]
      · exact width_from_zero b hbz (Or.inr rfl)
    · exact width_from_zero a haz (Or.inl rfl)
  -- Trim booleans: trim a side iff there is a root on that side.
  classical
  set loT : Bool := decide (∃ z ∈ xs, z ≤ a) with hloT_def
  set hiT : Bool := decide (∃ z ∈ xs, b ≤ z) with hhiT_def
  set lo : ℝ := if loT then a + γ else a with hlo_def
  set hi : ℝ := if hiT then b - γ else b with hhi_def
  -- When loT, a is a zero of h.
  have ha_zero_of_loT : loT = true → h a = 0 := by
    intro hlt
    rw [hloT_def, decide_eq_true_eq] at hlt
    obtain ⟨z, hz, hzle⟩ := hlt
    rcases ha_end with haR | haz
    · -- a = -R and z ≤ a = -R, z ∈ I so z ≥ -R, hence z = -R = a.
      have hzbound := hxs_in_I z hz
      have : z = a := by rw [haR]; linarith [hzbound.1]
      rw [← this]; exact hxs_zeros z hz
    · exact haz
  have hb_zero_of_hiT : hiT = true → h b = 0 := by
    intro hht
    rw [hhiT_def, decide_eq_true_eq] at hht
    obtain ⟨z, hz, hzge⟩ := hht
    rcases hb_end with hbR | hbz
    · have hzbound := hxs_in_I z hz
      have : z = b := by rw [hbR]; linarith [hzbound.2]
      rw [← this]; exact hxs_zeros z hz
    · exact hbz
  -- Floor hypotheses: every root ≤ a forces loT, every root ≥ b forces hiT.
  have h_lo_forces : ∀ z ∈ xs, z ≤ a → loT = true := by
    intro z hz hle; rw [hloT_def, decide_eq_true_eq]; exact ⟨z, hz, hle⟩
  have h_hi_forces : ∀ z ∈ xs, b ≤ z → hiT = true := by
    intro z hz hge; rw [hhiT_def, decide_eq_true_eq]; exact ⟨z, hz, hge⟩
  -- lo, hi ordering.
  have hlo_ge : a ≤ lo := by
    rw [hlo_def]; split <;> [linarith [hγ_pos]; exact le_refl a]
  have hhi_le : hi ≤ b := by
    rw [hhi_def]; split <;> [linarith [hγ_pos]; exact le_refl b]
  have hlo_le_hi : lo ≤ hi := by
    have hlo' : lo ≤ a + γ := by rw [hlo_def]; split <;> linarith [hγ_pos]
    have hhi' : b - γ ≤ hi := by rw [hhi_def]; split <;> linarith [hγ_pos]
    have : a + γ ≤ b - γ := by linarith [h_2γ_le_width]
    linarith
  -- |p₀| ≥ γ^6 on [lo, hi].
  have hp0_eval : ∀ x : ℝ, Polynomial.eval x p₀ = (xs.map (fun z => x - z)).prod := by
    intro x; rw [hp0_def]; exact bulk_eval_foldr xs x
  have hlo_eq : lo = a + (if loT then γ else 0) := by
    rw [hlo_def]; split <;> ring
  have hhi_eq : hi = b - (if hiT then γ else 0) := by
    rw [hhi_def]; split <;> ring
  have h_floor : ∀ x ∈ Set.Icc lo hi, γ ^ 6 ≤ |Polynomial.eval x p₀| := by
    intro x hx
    have hfl := bulk_floor_general γ hγ_pos a b xs loT hiT h_roots_outside
      h_lo_forces h_hi_forces x (hlo_eq ▸ hx.1) (hhi_eq ▸ hx.2)
    -- hfl : γ ^ xs.length ≤ ∏ |x - z|
    rw [hp0_eval, bulk_abs_prod]
    calc γ ^ 6 ≤ γ ^ xs.length := pow_le_pow_of_le_one hγ_pos.le hγ_le1 hxs_length
      _ ≤ (xs.map (fun z => |x - z|)).prod := hfl
  -- Integrand F = σ * eval p₀ * h.
  set F : ℝ → ℝ := fun x => σ * Polynomial.eval x p₀ * h x with hF_def
  have hF_cont : Continuous F := by
    rw [hF_def]; exact (continuous_const.mul hpoly_cont).mul hcont
  -- F ≥ 0 on [-R, R].
  have hF_nonneg : ∀ x ∈ Set.Icc (-R) R, 0 ≤ F x := by
    intro x hx
    have : |x| ≤ R := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    exact hsign x this
  -- [lo, hi] ⊆ [-R, R].
  have hlo_ge_R : -R ≤ lo := le_trans ha_ge hlo_ge
  have hhi_le_R : hi ≤ R := le_trans hhi_le hb_le
  -- On [lo, hi]: γ⁶ * |h x| ≤ F x.
  have hF_eq_abs : ∀ x ∈ Set.Icc lo hi, F x = |Polynomial.eval x p₀| * |h x| := by
    intro x hx
    have hxR : |x| ≤ R := by
      rw [abs_le]; exact ⟨le_trans hlo_ge_R hx.1, le_trans hx.2 hhi_le_R⟩
    have hnn := hsign x hxR
    show σ * Polynomial.eval x p₀ * h x = |Polynomial.eval x p₀| * |h x|
    rw [show σ * Polynomial.eval x p₀ * h x = |σ * Polynomial.eval x p₀ * h x| from
        (abs_of_nonneg hnn).symm]
    have habsσ : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    rw [abs_mul, abs_mul, habsσ, one_mul]
  have h_pointwise : ∀ x ∈ Set.Icc lo hi, γ ^ 6 * |h x| ≤ F x := by
    intro x hx
    rw [hF_eq_abs x hx]
    exact mul_le_mul_of_nonneg_right (h_floor x hx) (abs_nonneg _)
  -- Mass on [lo, hi] ≥ 3δ/28.
  have h_trim_loss : (∫ x in a..lo, |h x|) + (∫ x in hi..b, |h x|) ≤ δ / 28 := by
    have hL : (∫ x in a..lo, |h x|) ≤ M * γ ^ 2 / 2 := by
      by_cases hl : loT = true
      · have : lo = a + γ := by rw [hlo_def, hl]; simp
        rw [this]
        exact bulk_trim_left h hcont M hM hlip a γ hγ_pos.le (ha_zero_of_loT hl)
      · have hlf : loT = false := by simpa using hl
        have hlo_a : lo = a := by rw [hlo_def, hlf]; simp
        rw [hlo_a, intervalIntegral.integral_same]; positivity
    have hRr : (∫ x in hi..b, |h x|) ≤ M * γ ^ 2 / 2 := by
      by_cases hr : hiT = true
      · have : hi = b - γ := by rw [hhi_def, hr]; simp
        rw [this]
        exact bulk_trim_right h hcont M hM hlip b γ hγ_pos.le (hb_zero_of_hiT hr)
      · have hrf : hiT = false := by simpa using hr
        have hhi_b : hi = b := by rw [hhi_def, hrf]; simp
        rw [hhi_b, intervalIntegral.integral_same]; positivity
    have : M * γ ^ 2 / 2 + M * γ ^ 2 / 2 = δ / 28 := by rw [← hMγ2]; ring
    linarith
  have h_mass_lo_hi : 3 * δ / 28 ≤ ∫ x in lo..hi, |h x| := by
    have e1 : (∫ x in a..lo, |h x|) + (∫ x in lo..hi, |h x|) = ∫ x in a..hi, |h x| :=
      intervalIntegral.integral_add_adjacent_intervals (hint_abs a lo) (hint_abs lo hi)
    have e2 : (∫ x in a..hi, |h x|) + (∫ x in hi..b, |h x|) = ∫ x in a..b, |h x| :=
      intervalIntegral.integral_add_adjacent_intervals (hint_abs a hi) (hint_abs hi b)
    linarith [e1, e2, h_trim_loss, h_mass]
  -- Bulk: γ⁶ * ∫_lo^hi |h| ≤ ∫_lo^hi F.
  have h_int_F : ∀ u v : ℝ, IntervalIntegrable F volume u v :=
    fun u v => hF_cont.intervalIntegrable u v
  have h_int_g6 : ∀ u v : ℝ, IntervalIntegrable (fun x => γ ^ 6 * |h x|) volume u v :=
    fun u v => (continuous_const.mul habs_cont).intervalIntegrable u v
  have h_bulk : γ ^ 6 * (∫ x in lo..hi, |h x|) ≤ ∫ x in lo..hi, F x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hlo_le_hi (h_int_g6 lo hi) (h_int_F lo hi)
      h_pointwise
  -- ∫_lo^hi F ≤ ∫_{-R}^R F (F ≥ 0, [lo,hi] ⊆ [-R,R]).
  have h_extend : (∫ x in lo..hi, F x) ≤ ∫ x in (-R)..R, F x := by
    have hRle : -R ≤ R := by linarith
    have e3 : (∫ x in (-R)..lo, F x) + (∫ x in lo..hi, F x) + (∫ x in hi..R, F x)
        = ∫ x in (-R)..R, F x := by
      rw [intervalIntegral.integral_add_adjacent_intervals (h_int_F (-R) lo) (h_int_F lo hi),
        intervalIntegral.integral_add_adjacent_intervals (h_int_F (-R) hi) (h_int_F hi R)]
    have hleft : 0 ≤ ∫ x in (-R)..lo, F x := by
      apply intervalIntegral.integral_nonneg hlo_ge_R
      intro x hx
      exact hF_nonneg x ⟨hx.1, le_trans hx.2 (le_trans hlo_le_hi hhi_le_R)⟩
    have hright : 0 ≤ ∫ x in hi..R, F x := by
      apply intervalIntegral.integral_nonneg hhi_le_R
      intro x hx
      exact hF_nonneg x ⟨le_trans (le_trans hlo_ge_R hlo_le_hi) hx.1, hx.2⟩
    linarith [e3, hleft, hright]
  -- Assemble: 3δ⁴/(28⁴M³) = γ⁶·3δ/28 ≤ γ⁶·∫_lo^hi|h| ≤ ∫_lo^hi F ≤ ∫_{-R}^R F.
  have hγ6_val : γ ^ 6 = (δ / (28 * M)) ^ 3 := by
    rw [show γ ^ 6 = (γ ^ 2) ^ 3 by ring, hγ_sq]
  have h_const : γ ^ 6 * (3 * δ / 28) = 3 * δ ^ 4 / (28 ^ 4 * M ^ 3) := by
    rw [hγ6_val]; field_simp
  have hγ6_nn : (0 : ℝ) ≤ γ ^ 6 := by positivity
  calc 3 * δ ^ 4 / (28 ^ 4 * M ^ 3)
      = γ ^ 6 * (3 * δ / 28) := h_const.symm
    _ ≤ γ ^ 6 * (∫ x in lo..hi, |h x|) := mul_le_mul_of_nonneg_left h_mass_lo_hi hγ6_nn
    _ ≤ ∫ x in lo..hi, F x := h_bulk
    _ ≤ ∫ x in (-R)..R, F x := h_extend

end Workspace.ProofLemmas
