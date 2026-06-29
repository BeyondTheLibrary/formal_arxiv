import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.ProofLemmas.FinitenessOfSignedGaussianZeros
import Workspace.ProofLemmas.FirstReductionCountNonDecrease
import Workspace.ProofLemmas.SublemmaGenericSimpleZeros
import Workspace.ProofLemmas.SignedGaussianFirstReduction

/-!
# Sub-lemma B (Step 2, First Reduction: general → simple zeros)

A signed Gaussian combination `S` (with `k ≥ 1` components, a nonzero coefficient,
`S.density ≢ 0`) can be perturbed in a single nonzero coefficient by an
arbitrarily small amount to obtain `S_ε` whose real zeros are all simple, while
preserving the component count, a nonzero coefficient, non-vanishing density, and
not decreasing the number of distinct real zeros.

Packages the genericity "make zeros simple" half (countable bad set) with the
count-non-decrease half (`FirstReductionCountNonDecrease`).
-/

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.ZeroCount
open scoped Real

set_option maxHeartbeats 1000000

private theorem fin_sum_split (n : ℕ) (hn : 1 ≤ n) (F : Fin n → ℝ) :
    (Finset.univ : Finset (Fin n)).sum F
      = F ⟨0, by omega⟩ + (Finset.univ : Finset (Fin (n-1))).sum (fun i => F ⟨i.val+1, by omega⟩) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_succ]; congr 1

private theorem density_fin_sum (S : SignedGaussianCombination) (x : ℝ) :
    S.density x = (Finset.univ : Finset (Fin S.components.length)).sum
      (fun j => (S.components.get j).1 * (S.components.get j).2.density x) := by
  rw [SignedGaussianCombination.density_eq,
      ← List.ofFn_getElem_eq_map S.components (fun p => p.1 * p.2.density x),
      List.sum_ofFn]
  rfl

private theorem cst_exp_eq_density (G : GaussianPDF) (x : ℝ) :
    (1 / Real.sqrt (2 * Real.pi * G.varSq)) * Real.exp (-(x - G.mean)^2 / (2 * G.varSq))
      = G.density x := (GaussianPDF.density_eq G x).symm

private theorem cps_density (S : SignedGaussianCombination) (i₀ : Fin S.components.length) (η : ℝ) (x : ℝ) :
    (coeffPerturbSub S i₀ η).density x
      = S.density x - η * (S.components.get i₀).2.density x := by
  unfold coeffPerturbSub
  rw [SignedGaussianCombination.density_eq, SignedGaussianCombination.density_eq]
  simp only [List.map_set]
  rw [List.sum_set']
  have hlen : i₀.val < (S.components.map (fun p => p.1 * p.2.density x)).length := by
    simp [i₀.isLt]
  rw [dif_pos hlen]
  have hget : (S.components.map (fun p => p.1 * p.2.density x))[i₀.val] =
      (S.components.get i₀).1 * (S.components.get i₀).2.density x := by
    simp [List.getElem_map, List.get_eq_getElem]
  rw [hget]; ring

private theorem cps_length (S : SignedGaussianCombination) (i₀ : Fin S.components.length) (η : ℝ) :
    (coeffPerturbSub S i₀ η).components.length = S.components.length := by
  unfold coeffPerturbSub; simp [List.length_set]

private theorem genericity_family_eq
    (S : SignedGaussianCombination) (hk : 1 ≤ S.components.length)
    (i₀ : Fin S.components.length) (η : ℝ) (x : ℝ) :
    let n := S.components.length
    let e : Equiv.Perm (Fin n) := Equiv.swap ⟨0, by omega⟩ i₀
    let μ : Fin n → ℝ := fun j => (S.components.get (e j)).2.mean
    let τ : Fin n → ℝ := fun j => (S.components.get (e j)).2.varSq
    let cst : Fin n → ℝ := fun j => 1 / Real.sqrt (2 * Real.pi * (S.components.get j).2.varSq)
    let a_rest : Fin (n-1) → ℝ := fun i => (S.components.get (e ⟨i.val+1, by omega⟩)).1 * cst (e ⟨i.val+1, by omega⟩)
    let a₁ : ℝ := ((S.components.get i₀).1 - η) * cst i₀
    (a₁ * Real.exp (-(x - μ ⟨0, by omega⟩)^2 / (2 * τ ⟨0, by omega⟩))
      + (Finset.univ : Finset (Fin (n - 1))).sum
          (fun i => a_rest i *
            Real.exp (-(x - μ ⟨i.val + 1, by omega⟩)^2 /
                      (2 * τ ⟨i.val + 1, by omega⟩))))
    = (coeffPerturbSub S i₀ η).density x := by
  intro n e μ τ cst a_rest a₁
  rw [cps_density S i₀ η x]
  set F : Fin n → ℝ := fun j => (S.components.get (e j)).1 * (S.components.get (e j)).2.density x with hF
  have he0 : e ⟨0, by omega⟩ = i₀ := Equiv.swap_apply_left _ _
  have hexp : ∀ j : Fin n, cst (e j) * Real.exp (-(x - μ j)^2 / (2 * τ j))
      = (S.components.get (e j)).2.density x := by
    intro j; simp only [μ, τ, cst]; exact cst_exp_eq_density _ x
  have hterm0 : a₁ * Real.exp (-(x - μ ⟨0, by omega⟩)^2 / (2 * τ ⟨0, by omega⟩))
      = F ⟨0, by omega⟩ - η * (S.components.get i₀).2.density x := by
    simp only [a₁]
    have hμ0 : μ ⟨0, by omega⟩ = (S.components.get i₀).2.mean := by simp only [μ, he0]
    have hτ0 : τ ⟨0, by omega⟩ = (S.components.get i₀).2.varSq := by simp only [τ, he0]
    rw [hμ0, hτ0]
    have hd : cst i₀ * Real.exp (-(x - (S.components.get i₀).2.mean)^2 / (2 * (S.components.get i₀).2.varSq))
        = (S.components.get i₀).2.density x := by
      simp only [cst]; exact cst_exp_eq_density _ x
    rw [hF]; simp only [he0]
    rw [show ((S.components.get i₀).1 - η) * cst i₀ *
        Real.exp (-(x - (S.components.get i₀).2.mean)^2 / (2 * (S.components.get i₀).2.varSq))
      = (S.components.get i₀).1 * (cst i₀ * Real.exp (-(x - (S.components.get i₀).2.mean)^2 / (2 * (S.components.get i₀).2.varSq)))
        - η * (cst i₀ * Real.exp (-(x - (S.components.get i₀).2.mean)^2 / (2 * (S.components.get i₀).2.varSq))) by ring,
        hd]
  have htermi : ∀ i : Fin (n-1),
      a_rest i * Real.exp (-(x - μ ⟨i.val+1, by omega⟩)^2 / (2 * τ ⟨i.val+1, by omega⟩))
        = F ⟨i.val+1, by omega⟩ := by
    intro i
    simp only [a_rest, hF]
    have h := hexp ⟨i.val+1, by omega⟩
    rw [show (S.components.get (e ⟨i.val + 1, by omega⟩)).1 * cst (e ⟨i.val + 1, by omega⟩) *
        Real.exp (-(x - μ ⟨i.val + 1, by omega⟩) ^ 2 / (2 * τ ⟨i.val + 1, by omega⟩))
      = (S.components.get (e ⟨i.val + 1, by omega⟩)).1 *
        (cst (e ⟨i.val + 1, by omega⟩) * Real.exp (-(x - μ ⟨i.val + 1, by omega⟩) ^ 2 / (2 * τ ⟨i.val + 1, by omega⟩))) by ring,
        h]
  rw [hterm0]
  simp only [htermi]
  have hsplit := fin_sum_split n hk F
  have hperm : (Finset.univ : Finset (Fin n)).sum F = S.density x := by
    rw [density_fin_sum S x]
    have heq : F = (fun j => (S.components.get j).1 * (S.components.get j).2.density x) ∘ e := by
      funext j; rfl
    rw [heq]
    exact Equiv.sum_comp e (fun j => (S.components.get j).1 * (S.components.get j).2.density x)
  have hfin : F ⟨0, by omega⟩ + (Finset.univ : Finset (Fin (n-1))).sum (fun i => F ⟨i.val+1, by omega⟩)
      = S.density x := by rw [← hsplit, hperm]
  linarith [hfin]

private theorem badEta_countable
    (S : SignedGaussianCombination) (hk : 1 ≤ S.components.length)
    (i₀ : Fin S.components.length) :
    {η : ℝ | ∃ x, (coeffPerturbSub S i₀ η).density x = 0
        ∧ deriv (coeffPerturbSub S i₀ η).density x = 0}.Countable := by
  set e : Equiv.Perm (Fin S.components.length) := Equiv.swap ⟨0, by omega⟩ i₀ with he_def
  set μ : Fin S.components.length → ℝ := fun j => (S.components.get (e j)).2.mean with hμ_def
  set τ : Fin S.components.length → ℝ := fun j => (S.components.get (e j)).2.varSq with hτ_def
  set cst : Fin S.components.length → ℝ := fun j => 1 / Real.sqrt (2 * Real.pi * (S.components.get j).2.varSq) with hcst_def
  set a_rest : Fin (S.components.length-1) → ℝ := fun i => (S.components.get (e ⟨i.val+1, by omega⟩)).1 * cst (e ⟨i.val+1, by omega⟩) with harest_def
  have hτ_ne : ∀ i : Fin S.components.length, τ i ≠ 0 := by
    intro i; simp only [hτ_def]; exact ne_of_gt (S.components.get (e i)).2.varSq_pos
  have hgen := SublemmaGenericSimpleZeros S.components.length (by omega) μ τ hτ_ne a_rest
  set cst0 : ℝ := cst i₀ with hcst0_def
  have hcst0_ne : cst0 ≠ 0 := by
    simp only [hcst0_def, hcst_def]
    have : (0:ℝ) < 2 * Real.pi * (S.components.get i₀).2.varSq := by
      have := (S.components.get i₀).2.varSq_pos; positivity
    positivity
  set amap : ℝ → ℝ := fun η => ((S.components.get i₀).1 - η) * cst0 with hamap_def
  have hamap_inj : Function.Injective amap := by
    intro a b hab
    simp only [hamap_def] at hab
    have := mul_right_cancel₀ hcst0_ne hab
    linarith
  apply (hgen.preimage hamap_inj).mono
  intro η hη
  obtain ⟨x, hgx, hderiv⟩ := hη
  have hbridge : (fun x => amap η * Real.exp (-(x - μ ⟨0, by omega⟩)^2 / (2 * τ ⟨0, by omega⟩))
      + (Finset.univ : Finset (Fin (S.components.length - 1))).sum
          (fun i => a_rest i *
            Real.exp (-(x - μ ⟨i.val + 1, by omega⟩)^2 /
                      (2 * τ ⟨i.val + 1, by omega⟩))))
      = (coeffPerturbSub S i₀ η).density := by
    funext y
    have hb := genericity_family_eq S hk i₀ η y
    simp only [hamap_def, hcst0_def, hμ_def, hτ_def, hcst_def, harest_def]
    convert hb using 2
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  refine ⟨x, ?_, ?_⟩
  · have hcf := congrFun hbridge x
    rw [hcf]; exact hgx
  · rw [show deriv (fun x => amap η * Real.exp (-(x - μ ⟨0, by omega⟩)^2 / (2 * τ ⟨0, by omega⟩))
        + (Finset.univ : Finset (Fin (S.components.length - 1))).sum
            (fun i => a_rest i *
              Real.exp (-(x - μ ⟨i.val + 1, by omega⟩)^2 /
                        (2 * τ ⟨i.val + 1, by omega⟩)))) x
      = deriv (coeffPerturbSub S i₀ η).density x from by rw [hbridge]]
    exact hderiv

/-- **First reduction: general → simple zeros.**

For every tolerance `tol > 0` there is an index `i₀` and a perturbation amount `η`
with `0 < |η| < tol` such that `S_ε := coeffPerturbSub S i₀ η` (the combination
obtained from `S` by changing the single coefficient `a_{i₀} ↦ a_{i₀} - η`)
satisfies:
1. `S_ε.components.length = k`;
2. `S_ε` has at least one nonzero coefficient;
3. `S_ε.density ≢ 0`;
4. all real zeros of `S_ε.density` are simple
   (`∀ x, S_ε.density x = 0 → deriv S_ε.density x ≠ 0`);
5. `zeroCount S.density ≤ zeroCount S_ε.density`. -/
theorem FirstReductionSimpleZeros
    (S : SignedGaussianCombination)
    (hk : 1 ≤ S.components.length)
    (hcoeff : ∃ p ∈ S.components, p.1 ≠ 0)
    (hne : ∃ x : ℝ, S.density x ≠ 0)
    (tol : ℝ) (htol : 0 < tol) :
    ∃ (i₀ : Fin S.components.length) (η : ℝ),
      0 < |η| ∧ |η| < tol ∧
      (coeffPerturbSub S i₀ η).components.length = S.components.length ∧
      (∃ p ∈ (coeffPerturbSub S i₀ η).components, p.1 ≠ 0) ∧
      (∃ x : ℝ, (coeffPerturbSub S i₀ η).density x ≠ 0) ∧
      (∀ x : ℝ, (coeffPerturbSub S i₀ η).density x = 0 →
        deriv (coeffPerturbSub S i₀ η).density x ≠ 0) ∧
      zeroCount S.density ≤ zeroCount (coeffPerturbSub S i₀ η).density := by
  -- (1) choose i₀ with nonzero coefficient
  obtain ⟨p, hpmem, hp_ne⟩ := hcoeff
  obtain ⟨idx, hidx_lt, hidx_get⟩ := List.mem_iff_getElem.mp hpmem
  set i₀ : Fin S.components.length := ⟨idx, hidx_lt⟩ with hi₀_def
  have ha : (S.components.get i₀).1 ≠ 0 := by
    rw [List.get_eq_getElem, hidx_get]; exact hp_ne
  -- (2) sign + threshold from FirstReductionCountNonDecrease
  obtain ⟨s, hs, ε₀, hε₀, hcount⟩ := FirstReductionCountNonDecrease S hk hne i₀ ha
  -- (3) bad-ε set countable; choose good ε in (0, min tol (min ε₀ |a_{i₀}|))
  set acoef : ℝ := (S.components.get i₀).1 with hacoef_def
  have hacoef_ne : acoef ≠ 0 := ha
  set R : ℝ := min tol (min ε₀ |acoef|) with hR_def
  have hR_pos : 0 < R := by
    have h1 : (0:ℝ) < |acoef| := abs_pos.mpr hacoef_ne
    simp only [hR_def, lt_min_iff]; exact ⟨htol, hε₀, h1⟩
  -- bad-ε in terms of s*ε
  have hbadE : {ε : ℝ | ∃ x, (coeffPerturbSub S i₀ (s * ε)).density x = 0
      ∧ deriv (coeffPerturbSub S i₀ (s * ε)).density x = 0}.Countable := by
    have hbad := badEta_countable S hk i₀
    have hs_ne : s ≠ 0 := by rcases hs with h | h <;> simp [h]
    have hmul_inj : Function.Injective (fun ε : ℝ => s * ε) :=
      fun a b hab => by
        simp only at hab; exact mul_left_cancel₀ hs_ne hab
    have := hbad.preimage hmul_inj
    apply this.mono
    intro ε hε; exact hε
  obtain ⟨ε, hε_mem, hε_not⟩ := ioo_not_subset_of_countable hR_pos hbadE
  obtain ⟨hε_pos, hε_lt⟩ := hε_mem
  have hε_lt_tol : ε < tol := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_lt_ε₀ : ε < ε₀ := lt_of_lt_of_le hε_lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε_lt_a : ε < |acoef| := lt_of_lt_of_le hε_lt (le_trans (min_le_right _ _) (min_le_right _ _))
  -- η := s*ε
  refine ⟨i₀, s * ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 < |s*ε|
    have : |s * ε| = ε := by
      rw [abs_mul]
      rcases hs with h | h <;> simp [h, abs_of_pos hε_pos]
    rw [this]; exact hε_pos
  · -- |s*ε| < tol
    have : |s * ε| = ε := by
      rw [abs_mul]
      rcases hs with h | h <;> simp [h, abs_of_pos hε_pos]
    rw [this]; exact hε_lt_tol
  · -- length preserved
    exact cps_length S i₀ (s * ε)
  · -- nonzero coeff: the i₀-component has coeff acoef - s*ε ≠ 0
    refine ⟨(acoef - s * ε, (S.components.get i₀).2), ?_, ?_⟩
    · -- membership in the set list
      unfold coeffPerturbSub
      simp only [hacoef_def, List.get_eq_getElem]
      rw [List.mem_iff_getElem]
      refine ⟨idx, ?_, ?_⟩
      · rw [List.length_set]; exact hidx_lt
      · rw [List.getElem_set_self]
    · -- coeff ≠ 0 since |s*ε| = ε < |acoef|
      have habs : |s * ε| = ε := by
        rw [abs_mul]; rcases hs with h | h <;> simp [h, abs_of_pos hε_pos]
      intro hzero
      simp only at hzero
      have : acoef = s * ε := by linarith [hzero]
      rw [this] at hε_lt_a
      rw [habs] at hε_lt_a
      exact lt_irrefl _ hε_lt_a
  · -- simple zeros (conjunct 4) and we also use it for conjunct 3 below
    -- first establish simplicity
    have hsimple : ∀ x : ℝ, (coeffPerturbSub S i₀ (s * ε)).density x = 0 →
        deriv (coeffPerturbSub S i₀ (s * ε)).density x ≠ 0 := by
      intro x hzx hdz
      exact hε_not ⟨x, hzx, hdz⟩
    -- conjunct 3: ∃ x, density ≠ 0
    by_contra hall
    simp only [not_exists, not_not] at hall
    -- hall : ∀ x, density x = 0, so density ≡ 0, deriv ≡ 0, contradicts simplicity at x=0
    have hfun0 : (coeffPerturbSub S i₀ (s * ε)).density = (fun _ => (0:ℝ)) := by
      funext x; exact hall x
    have hd0 : deriv (coeffPerturbSub S i₀ (s * ε)).density 0 = 0 := by
      rw [hfun0]; simp
    exact hsimple 0 (hall 0) hd0
  · -- simple zeros (conjunct 4 proper)
    intro x hzx hdz
    exact hε_not ⟨x, hzx, hdz⟩
  · -- count non-decrease
    have hsimple : ∀ x : ℝ, (coeffPerturbSub S i₀ (s * ε)).density x = 0 →
        deriv (coeffPerturbSub S i₀ (s * ε)).density x ≠ 0 := by
      intro x hzx hdz; exact hε_not ⟨x, hzx, hdz⟩
    exact hcount ε hε_pos hε_lt_ε₀ hsimple

end Workspace.ProofLemmas
