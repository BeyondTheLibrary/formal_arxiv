import Mathlib
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.GaussianConvolution
import Workspace.ProofLemmas.FormalToNormalizedBridge
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.ConvSmallPreservesSimpleAndEnvelope
import Workspace.ProofLemmas.MainCaseSimpleTransport
import Workspace.ProofLemmas.FirstReductionSimpleZeros
import Workspace.ProofLemmas.FirstReductionCountNonDecrease
import Workspace.ProofLemmas.FinitenessOfSignedGaussianZeros
import Workspace.ProofLemmas.FormalGaussianNontriviality
import Workspace.ProofLemmas.FirstReductionSimpleZeros
import Workspace.ProofLemmas.FormalGaussianConvolution
import Workspace.ProofLemmas.SublemmaGenericSimpleZeros
import Workspace.ProofLemmas.SignedGaussianFirstReduction
import Workspace.ProofLemmas.SublemmaSGCDensityIsAnalytic
import Workspace.PriorWork.HummelGidasZeroCount

/-!
# `BareMainCaseDualGenericity` — STEP 2: the §6.1 main-case dual-genericity transport.

The main case (`c im ≠ 0`, some rest coefficient nonzero) of the Moitra–Valiant §6.1
inductive step, proved by the dual-genericity recovery route.  This is the consumer of
`mainCaseSimpleTransport` (STEP-1-concrete + recovery + Hummel–Gidas); it supplies the
SIMPLE base `g̃₀'`, the recovery to the perturbed target `fp`, and the count transport
`count f ≤ count fp` via `FirstReductionCountNonDecrease`.
-/

namespace Workspace.ProofLemmas

open Workspace.Types.ZeroCount
open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.GaussianConvolution
open scoped Real

set_option maxHeartbeats 4000000

/-! ## Private helpers (mirroring `FirstReductionSimpleZeros`, copied since they are
`private` there).  These give the countability of the non-simple-zero perturbation
locus of an arbitrary signed Gaussian combination. -/

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

/-- **§6.1 main case (dual-genericity transport).**

Bare `(k+1)`-component model with a smallest-variance index `im` (`him`), a nonzero
smallest coefficient (`hcim`), and a nonzero rest coefficient (`hrem_coeff`), under the
induction hypothesis `IH`, has at most `2k` distinct real zeros. -/
theorem bareMainCaseDualGenericity
    (k : ℕ) (hk : 1 ≤ k)
    (IH : ∀ (a' : Fin k → ℝ) (μ' : Fin k → ℝ) (τ_sq' : Fin k → ℝ),
          (∀ i : Fin k, 0 < τ_sq' i) →
          (∀ i j : Fin k, i ≠ j → τ_sq' i ≠ τ_sq' j) →
          (∃ i : Fin k, a' i ≠ 0) →
          Workspace.Types.ZeroCount.hasAtMostNZeros
            (fun x => (Finset.univ : Finset (Fin k)).sum
              (fun i => a' i * Real.exp (-(x - μ' i)^2 / (2 * τ_sq' i))))
            (2 * (k - 1)))
    (c ν w : Fin (k + 1) → ℝ)
    (hw_pos : ∀ i : Fin (k + 1), 0 < w i)
    (hw_distinct : ∀ i j : Fin (k + 1), i ≠ j → w i ≠ w j)
    (im : Fin (k + 1)) (him : ∀ j, w im ≤ w j)
    (hcim : c im ≠ 0)
    (hrem_coeff : ∃ i : Fin k, c (im.succAbove i) ≠ 0) :
    Workspace.Types.ZeroCount.hasAtMostNZeros
      (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i))))
      (2 * k) := by
  classical
  -- ===== Deconvolution data (mirrors `bareModelSixStepBound` Steps 1–3). =====
  have hrem_larger : ∀ i : Fin k, w im < w (im.succAbove i) := by
    intro i
    have hne : im.succAbove i ≠ im := Fin.succAbove_ne im i
    have hle : w im ≤ w (im.succAbove i) := him _
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd h.symm (hw_distinct _ _ hne)
  have hrem_pos : ∀ i : Fin k, 0 < w (im.succAbove i) - w im := by
    intro i; have := hrem_larger i; linarith
  have hrem_distinct : ∀ i j : Fin k, i ≠ j →
      w (im.succAbove i) - w im ≠ w (im.succAbove j) - w im := by
    intro i j hij
    have hne : im.succAbove i ≠ im.succAbove j := by
      intro h; exact hij (im.succAbove_right_injective h)
    have := hw_distinct _ _ hne
    intro heq; apply this; linarith
  -- The §6.1 dual-genericity transport.
  --
  -- All ANALYTIC content of this step is already banked and used by the proof skeleton:
  --   * `mainCaseSimpleTransport` (this file's main dependency) packages
  --     STEP-1-concrete (`convFamily_diagonal_threshold_concrete`) + the width-`αrec`
  --     recovery + Hummel–Gidas into: a SIMPLE base `S'` with `≤ 2(k-1)` zeros,
  --     `S'.density ν ≠ 0`, a recovery `conv(conv(S'.density,v)+A·N(ν,v), w_im−v) = fp`,
  --     and `count f ≤ count fp`  ⟹  `count f ≤ 2k`.
  --   * STEP-1-concrete itself is fully proven and axiom-clean
  --     (`{propext, Classical.choice, Quot.sound, AnalyticIFTSimpleZeroBranch,
  --       HummelGidasZeroCount}`).
  --
  -- The REMAINING obligation is purely the coefficient-perturbation BOOKKEEPING that
  -- assembles those inputs:
  --   1. Build `S_f` (`FormalToNormalizedBridge (k+1) c ν w hw_pos`); `count f = count S_f`.
  --   2. `FirstReductionCountNonDecrease S_f idx` (idx = `im.succAbove j₀`, a nonzero
  --      rest coeff) → sign `s`, threshold `ε₀`, and `count f ≤ count (coeffPerturbSub
  --      S_f idx (s·ε))` whenever that perturbation is simple.
  --   3. Genericity: pick `ε ∈ (0, ε₀)` avoiding the THREE countable bad sets
  --        {ε | g̃₀'(ε) non-simple} ∪ {ε | g̃₀'(ε)(ν im)=0} ∪ {ε | f'(ε) non-simple}
  --      (`SublemmaGenericSimpleZeros` gives the first/third countable; the centre value
  --      `g̃₀'(ν im)` is affine in ε with nonzero Gaussian slope, so the second is a single
  --      point; `Set.Countable.union`×2 + `ioo_not_subset_of_countable`).
  --   4. Set `δ := s·ε`, `c' := Function.update c idx (c idx − δ/√(2π·w idx))`, and the
  --      deconvolution `cg'` of `c'`'s rest.  Then `S' := bridge(cg', νg, wg)` is the simple
  --      base, `fp := (coeffPerturbSub S_f idx δ).density`, and the recovery for `S'`
  --      reproduces `fp` (the existing recovery derivation with `cg'` in place of `cg`).
  --   5. `count f ≤ count fp` from step 2; IH on `cg'` gives `count S' ≤ 2(k-1)`.
  --   6. `mainCaseSimpleTransport k hk S' … (ν im) (c im·√(2π·w im)) (w im) f fp … h_rec
  --      h_transport`  closes the goal.
  --
  -- This is the documented §6.1 "dual-genericity recovery rewrite" (gap (B)).  The
  -- coefficient identity `(coeffPerturbSub S_f idx δ).density = ∑ (update c idx …)·exp`
  -- and the `cg'`-recovery are mechanical but voluminous; they are the sole residual.
  --
  -- ===== Bookkeeping setup. =====
  -- The smallest-variance term carries the `A := c im·√(2π·w im)` add-Gaussian.
  set A : ℝ := c im * Real.sqrt (2 * Real.pi * w im) with hA_def
  have hA_ne : A ≠ 0 := by
    rw [hA_def]
    have hsq : 0 < Real.sqrt (2 * Real.pi * w im) := by
      apply Real.sqrt_pos.mpr; have := hw_pos im; positivity
    exact mul_ne_zero hcim (ne_of_gt hsq)
  have him_pos : 0 < w im := hw_pos im
  -- Pick a REST index `j₀` with a nonzero coefficient.
  obtain ⟨j₀, hj₀⟩ := hrem_coeff
  -- The full target `f`, as a SignedGaussianCombination via the bridge.
  obtain ⟨S_f, hSf_comp, hSf_density, hSf_coeff_iff, _⟩ :=
    FormalToNormalizedBridge (k + 1) c ν w hw_pos
  have hSf_len : S_f.components.length = k + 1 := by
    rw [hSf_comp]; rw [List.length_ofFn]
  -- The perturbation index, as `Fin S_f.components.length`.
  set idx : Fin S_f.components.length :=
    ⟨(im.succAbove j₀).val, by rw [hSf_len]; exact (im.succAbove j₀).isLt⟩ with hidx_def
  -- The component data at `idx`: coefficient `c(im.succAbove j₀)·√(2π·w(...))`,
  -- mean `ν(im.succAbove j₀)`, variance `w(im.succAbove j₀)`.
  have hget_idx :
      S_f.components.get idx
        = (c (im.succAbove j₀) * Real.sqrt (2 * Real.pi * w (im.succAbove j₀)),
            (⟨ν (im.succAbove j₀), w (im.succAbove j₀), hw_pos (im.succAbove j₀)⟩ : GaussianPDF)) := by
    rw [List.get_of_eq hSf_comp idx, List.get_ofFn]
    congr 1 <;> · apply Fin.ext; simp [hidx_def]
  have hidx_coeff_ne : (S_f.components.get idx).1 ≠ 0 := by
    rw [hget_idx]
    have hsq : 0 < Real.sqrt (2 * Real.pi * w (im.succAbove j₀)) := by
      apply Real.sqrt_pos.mpr; have := hw_pos (im.succAbove j₀); positivity
    exact mul_ne_zero hj₀ (ne_of_gt hsq)
  -- The goal's `f` equals `S_f.density` pointwise.
  have hf_eq : (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))) = S_f.density := by
    funext x; exact hSf_density x
  -- Nontriviality of the full target.
  have hSf_ne : ∃ x : ℝ, S_f.density x ≠ 0 := by
    obtain ⟨x, hx⟩ := FormalGaussianNontriviality (k + 1) (by omega) c ν w
      (fun i => ne_of_gt (hw_pos i)) hw_distinct ⟨im, hcim⟩
    exact ⟨x, by rw [← hSf_density x]; exact hx⟩
  -- ===== Count-non-decrease: get the sign and threshold from the first reduction. =====
  obtain ⟨s, hs_sign, ε₀, hε₀_pos, hcount⟩ :=
    FirstReductionCountNonDecrease S_f (by rw [hSf_len]; omega) hSf_ne idx hidx_coeff_ne
  have hs_abs : |s| = 1 := by rcases hs_sign with h | h <;> rw [h] <;> norm_num
  -- ===== The UNPERTURBED width-`w im` deconvolution `S_g0 = bridge(cg, νg, wg)`. =====
  set cg : Fin k → ℝ := fun i =>
    c (im.succAbove i) * Real.sqrt (2 * Real.pi * w (im.succAbove i))
      / Real.sqrt (2 * Real.pi * (w (im.succAbove i) - w im)) with hcg_def
  set νg : Fin k → ℝ := fun i => ν (im.succAbove i) with hνg_def
  set wg : Fin k → ℝ := fun i => w (im.succAbove i) - w im with hwg_def
  obtain ⟨S_g0, hSg_comp, hSg_density, hSg_coeff_iff, _⟩ :=
    FormalToNormalizedBridge k cg νg wg hrem_pos
  have hSg_len : S_g0.components.length = k := by rw [hSg_comp, List.length_ofFn]
  -- The deconvolution index for `j₀`.
  set jdx : Fin S_g0.components.length :=
    ⟨j₀.val, by rw [hSg_len]; exact j₀.isLt⟩ with hjdx_def
  -- Component data of `S_g0` at `jdx`.
  have hget_jdx :
      S_g0.components.get jdx
        = (cg j₀ * Real.sqrt (2 * Real.pi * wg j₀),
            (⟨νg j₀, wg j₀, hrem_pos j₀⟩ : GaussianPDF)) := by
    rw [List.get_of_eq hSg_comp jdx, List.get_ofFn]
    congr 1 <;> · apply Fin.ext; simp [hjdx_def]
  -- A general Gaussian density is everywhere positive.
  have hgauss_pos : ∀ (G : GaussianPDF) (x : ℝ), 0 < G.density x := by
    intro G x
    rw [GaussianPDF.density_def]
    have h1 : 0 < Real.sqrt (2 * Real.pi * G.varSq) := by
      apply Real.sqrt_pos.mpr; have := G.varSq_pos; positivity
    positivity
  -- The scaling factor relating a perturbation of `S_g0` at `jdx` to a perturbation
  -- of `S_f` at `idx`:  `sc := √(2π·wg j₀) > 0`.
  set sc : ℝ := Real.sqrt (2 * Real.pi * wg j₀) with hsc_def
  have hsc_pos : 0 < sc := by
    rw [hsc_def]; apply Real.sqrt_pos.mpr; have := hrem_pos j₀; positivity
  have hsc_ne : sc ≠ 0 := ne_of_gt hsc_pos
  -- ===== Genericity: choose `ε ∈ (0, ε₀)` outside three countable bad sets. =====
  -- B1: ε making `coeffPerturbSub S_f idx (s·ε)` non-simple  (⊆ preimage of badEta S_f idx).
  have hB1 : {ε : ℝ | ∃ x, (coeffPerturbSub S_f idx (s * ε)).density x = 0
        ∧ deriv (coeffPerturbSub S_f idx (s * ε)).density x = 0}.Countable := by
    have hbad := badEta_countable S_f (by rw [hSf_len]; omega) idx
    have hinj : Function.Injective (fun ε : ℝ => s * ε) := by
      intro a b hab
      have hs_ne : s ≠ 0 := by rcases hs_sign with h | h <;> rw [h] <;> norm_num
      exact mul_left_cancel₀ hs_ne hab
    apply (hbad.preimage hinj).mono
    intro ε hε; exact hε
  -- B2: ε making `coeffPerturbSub S_g0 jdx (s·ε)` non-simple.
  have hB2 : {ε : ℝ | ∃ x, (coeffPerturbSub S_g0 jdx (s * ε)).density x = 0
        ∧ deriv (coeffPerturbSub S_g0 jdx (s * ε)).density x = 0}.Countable := by
    have hbad := badEta_countable S_g0 (by rw [hSg_len]; omega) jdx
    have hinj : Function.Injective (fun ε : ℝ => s * ε) := by
      intro a b hab
      have hs_ne : s ≠ 0 := by rcases hs_sign with h | h <;> rw [h] <;> norm_num
      exact mul_left_cancel₀ hs_ne hab
    apply (hbad.preimage hinj).mono
    intro ε hε; exact hε
  -- B3: ε making `(coeffPerturbSub S_g0 jdx (s·ε)).density (ν im) = 0` — a single point.
  have hB3 : {ε : ℝ | (coeffPerturbSub S_g0 jdx (s * ε)).density (ν im) = 0}.Countable := by
    -- The value is affine in ε with nonzero slope, so the set has ≤ 1 element.
    set G0v : ℝ := S_g0.density (ν im) with hG0v_def
    set Gv : ℝ := (S_g0.components.get jdx).2.density (ν im) with hGv_def
    have hGv_pos : 0 < Gv := by rw [hGv_def]; exact hgauss_pos _ _
    have hslope_ne : s * Gv ≠ 0 := by
      have hs_ne : s ≠ 0 := by rcases hs_sign with h | h <;> rw [h] <;> norm_num
      exact mul_ne_zero hs_ne (ne_of_gt hGv_pos)
    apply Set.Subsingleton.countable
    intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    rw [cps_density S_g0 jdx (s * a) (ν im)] at ha
    rw [cps_density S_g0 jdx (s * b) (ν im)] at hb
    rw [← hG0v_def, ← hGv_def] at ha hb
    -- ha : G0v - (s*a)*Gv = 0 ; hb : G0v - (s*b)*Gv = 0
    have : (s * Gv) * a = (s * Gv) * b := by
      have h1 : s * a * Gv = s * Gv * a := by ring
      have h2 : s * b * Gv = s * Gv * b := by ring
      rw [h1] at ha; rw [h2] at hb; linarith
    exact mul_left_cancel₀ hslope_ne this
  -- Choose ε in (0, ε₀) avoiding B1 ∪ B2 ∪ B3.
  obtain ⟨ε, hε_mem, hε_not⟩ :=
    ioo_not_subset_of_countable hε₀_pos ((hB1.union hB2).union hB3)
  obtain ⟨hε_pos, hε_lt⟩ := hε_mem
  rw [Set.mem_union, Set.mem_union, not_or, not_or] at hε_not
  obtain ⟨⟨hε_B1, hε_B2⟩, hε_B3⟩ := hε_not
  -- ===== The perturbed objects at the chosen ε. =====
  set δ : ℝ := s * ε with hδ_def
  -- The perturbed simple base `S'` (deconvolution of the perturbed rest):
  -- subtract exactly `δ` from `S_g0`'s coefficient at `jdx`.
  set S' : SignedGaussianCombination := coeffPerturbSub S_g0 jdx δ with hS'_def
  -- The perturbed target `fp = (coeffPerturbSub S_f idx δ).density`.
  set Sp : SignedGaussianCombination := coeffPerturbSub S_f idx δ with hSp_def
  -- Perturbed deconvolution coefficients (only `j₀` changes).
  set cg'' : Fin k → ℝ := Function.update cg j₀ (cg j₀ - δ / sc) with hcg''_def
  -- `S'.density` is the bare-exp combination with coefficients `cg''`.
  have hS'_density_eq : ∀ x : ℝ, S'.density x
      = (Finset.univ : Finset (Fin k)).sum
          (fun i => cg'' i * Real.exp (-(x - νg i)^2 / (2 * wg i))) := by
    intro x
    rw [hS'_def, cps_density S_g0 jdx δ x, ← hSg_density x, hget_jdx]
    -- The Gaussian density of `⟨νg j₀, wg j₀⟩` at x.
    have hGd : (⟨νg j₀, wg j₀, hrem_pos j₀⟩ : GaussianPDF).density x
        = (1 / sc) * Real.exp (-(x - νg j₀)^2 / (2 * wg j₀)) := by
      rw [GaussianPDF.density_eq]
    rw [hGd]
    -- LHS: split off the j₀ term.
    rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin k))
          (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i))) (Finset.mem_univ j₀)]
    -- RHS: split off the j₀ term.
    rw [hcg''_def,
        ← Finset.add_sum_erase (Finset.univ : Finset (Fin k))
          (fun i => Function.update cg j₀ (cg j₀ - δ / sc) i * Real.exp (-(x - νg i)^2 / (2 * wg i)))
          (Finset.mem_univ j₀)]
    -- Erased sums agree (update is identity off j₀).
    have herase : (Finset.univ.erase j₀).sum
          (fun i => cg i * Real.exp (-(x - νg i)^2 / (2 * wg i)))
        = (Finset.univ.erase j₀).sum
          (fun i => Function.update cg j₀ (cg j₀ - δ / sc) i * Real.exp (-(x - νg i)^2 / (2 * wg i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [herase, Function.update_self]
    ring
  -- `S'.density (ν im) ≠ 0` (from genericity B3).
  have hS'_ν_ne : S'.density (ν im) ≠ 0 := by
    rw [hS'_def, hδ_def]; exact hε_B3
  -- A nonzero deconvolution coefficient (else `S'.density ≡ 0`, contradicting B3).
  have hcg''_nonzero : ∃ i : Fin k, cg'' i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hS'_ν_ne
    rw [hS'_density_eq (ν im)]
    apply Finset.sum_eq_zero
    intro i _; rw [hall i]; ring
  -- IH count: `S'.density` has ≤ 2(k-1) zeros.
  have hS'_count : Workspace.Types.ZeroCount.hasAtMostNZeros S'.density (2 * (k - 1)) := by
    have hih := IH cg'' νg wg
      (fun i => by rw [hwg_def]; exact hrem_pos i)
      (fun i j hij => by rw [hwg_def]; exact hrem_distinct i j hij)
      hcg''_nonzero
    have hfun : S'.density = (fun x => (Finset.univ : Finset (Fin k)).sum
        (fun i => cg'' i * Real.exp (-(x - νg i)^2 / (2 * wg i)))) := by
      funext x; exact hS'_density_eq x
    rw [hfun]; exact hih
  -- `S'.density` has only simple zeros (from genericity B2).
  have hS'_simple : ∀ x, S'.density x = 0 → deriv S'.density x ≠ 0 := by
    intro x hx hderiv
    apply hε_B2
    have hSeq : (coeffPerturbSub S_g0 jdx (s * ε)) = S' := by rw [hS'_def, hδ_def]
    refine ⟨x, ?_, ?_⟩
    · rw [hSeq]; exact hx
    · rw [hSeq]; exact hderiv
  -- ===== Transport: count f ≤ count fp. =====
  -- The perturbed full target `fp = Sp.density` is analytic and has simple zeros.
  have hfp_analytic : AnalyticOnNhd ℝ Sp.density Set.univ :=
    SublemmaSGCDensityIsAnalytic Sp
  have hfp_simple : ∀ x : ℝ, (coeffPerturbSub S_f idx (s * ε)).density x = 0 →
      deriv (coeffPerturbSub S_f idx (s * ε)).density x ≠ 0 := by
    intro x hx hderiv
    exact hε_B1 ⟨x, hx, hderiv⟩
  have h_transport : zeroCount (fun x => (Finset.univ : Finset (Fin (k + 1))).sum
        (fun i => c i * Real.exp (-(x - ν i)^2 / (2 * w i)))) ≤ zeroCount Sp.density := by
    rw [hf_eq, hSp_def, hδ_def]
    exact hcount ε hε_pos hε_lt hfp_simple
  -- ===== The recovery identity (heat semigroup). =====
  -- The "fundamental" bridge identity: width-`w im` heat flow of `S'` plus the
  -- recovered smallest-variance bump reproduces `Sp.density`.
  -- The width-`w im` heat flow of the (unperturbed) deconvolution `S_g0`, as a Fin-k sum.
  have hHeat_Sg0 : ∀ x : ℝ, (heatShift S_g0 (w im) him_pos).density x
      = (Finset.univ : Finset (Fin k)).sum
          (fun i => c (im.succAbove i)
            * Real.exp (-(x - ν (im.succAbove i))^2 / (2 * w (im.succAbove i)))) := by
    intro x
    rw [heatShift, SignedGaussianCombination.density_eq, hSg_comp, List.map_map, List.map_ofFn,
        List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    -- term i = cg_i·√(2π wg_i) · ⟨νg_i, wg_i + w im⟩.density x = c(im.succAbove i)·exp(...)
    simp only [Function.comp, shiftVarG, GaussianPDF.density_eq]
    -- coefficients: cg_i·√(2π wg_i)/√(2π(wg_i + w im)) = c(im.succAbove i)
    rw [hcg_def, hνg_def, hwg_def]
    have hw' : w (im.succAbove i) - w im + w im = w (im.succAbove i) := by ring
    rw [hw']
    have hwgpos : 0 < w (im.succAbove i) - w im := hrem_pos i
    have hs1 : Real.sqrt (2 * Real.pi * (w (im.succAbove i) - w im)) ≠ 0 := by
      apply ne_of_gt; apply Real.sqrt_pos.mpr; positivity
    have hs2 : Real.sqrt (2 * Real.pi * w (im.succAbove i)) ≠ 0 := by
      apply ne_of_gt; apply Real.sqrt_pos.mpr; have := hw_pos (im.succAbove i); positivity
    field_simp
  -- The shifted bump variance `wg j₀ + w im` is positive.
  have hwgbump_pos : 0 < wg j₀ + w im := by
    have h1 := hrem_pos j₀; have h2 := him_pos; linarith
  -- The width-`w im` heat flow of the PERTURBED base `S'` subtracts a single bump.
  have hHeat_S' : ∀ x : ℝ, (heatShift S' (w im) him_pos).density x
      = (heatShift S_g0 (w im) him_pos).density x
        - δ * (⟨νg j₀, wg j₀ + w im, hwgbump_pos⟩ : GaussianPDF).density x := by
    intro x
    rw [hS'_def]
    -- heatShift of a coeffPerturbSub: subtract δ at the (heat-shifted) jdx component.
    rw [heatShift, heatShift, SignedGaussianCombination.density_eq,
        SignedGaussianCombination.density_eq]
    show ((((coeffPerturbSub S_g0 jdx δ).components).map
            (fun p => (p.1, shiftVarG p.2 (w im) him_pos))).map
              (fun p => p.1 * p.2.density x)).sum = _
    unfold coeffPerturbSub
    simp only [List.map_set]
    rw [List.sum_set']
    have hlen : jdx.val < ((S_g0.components.map
        (fun p => (p.1, shiftVarG p.2 (w im) him_pos))).map (fun p => p.1 * p.2.density x)).length := by
      simp [jdx.isLt]
    rw [dif_pos hlen]
    -- The unperturbed heat-shifted sum.
    have hbase : ((S_g0.components.map (fun p => (p.1, shiftVarG p.2 (w im) him_pos))).map
          (fun p => p.1 * p.2.density x)).sum = (heatShift S_g0 (w im) him_pos).density x := by
      rw [heatShift, SignedGaussianCombination.density_eq, List.map_map]
    -- The j₀-th heat-shifted component's value.
    have hjval : ((S_g0.components.map (fun p => (p.1, shiftVarG p.2 (w im) him_pos))).map
          (fun p => p.1 * p.2.density x))[jdx.val]
        = (cg j₀ * Real.sqrt (2 * Real.pi * wg j₀))
          * (⟨νg j₀, wg j₀ + w im, hwgbump_pos⟩ : GaussianPDF).density x := by
      rw [List.getElem_map, List.getElem_map]
      have : S_g0.components[jdx.val] = (cg j₀ * Real.sqrt (2 * Real.pi * wg j₀),
          (⟨νg j₀, wg j₀, hrem_pos j₀⟩ : GaussianPDF)) := by
        have he := hget_jdx; rw [List.get_eq_getElem] at he; exact he
      rw [this]
      show _ * (shiftVarG (⟨νg j₀, wg j₀, hrem_pos j₀⟩ : GaussianPDF) (w im) him_pos).density x = _
      congr 1
    rw [hbase, hjval]
    -- Also `(S_g0.components.get jdx).1 = cg j₀·√(2π wg j₀)`.
    have hget1 : ((S_g0.components.get jdx)).1 = cg j₀ * Real.sqrt (2 * Real.pi * wg j₀) := by
      rw [hget_jdx]
    -- The heat-shifted `get jdx` density equals the bump density.
    have hgetdens : (shiftVarG (S_g0.components.get jdx).2 (w im) him_pos).density x
        = (⟨νg j₀, wg j₀ + w im, hwgbump_pos⟩ : GaussianPDF).density x := by
      rw [hget_jdx]; congr 1
    rw [hget1, hgetdens]
    ring
  -- The unperturbed full recovery: `heatShift S_g0 (w im) + A·N(ν im, w im) = S_f.density`.
  have h_full_recover : ∀ x : ℝ,
      (heatShift S_g0 (w im) him_pos).density x
        + A * (⟨ν im, w im, him_pos⟩ : GaussianPDF).density x
      = S_f.density x := by
    intro x
    rw [hHeat_Sg0 x, ← hSf_density x]
    -- A·N(ν im, w im) x = c im·exp(im term).
    have hAterm : A * (⟨ν im, w im, him_pos⟩ : GaussianPDF).density x
        = c im * Real.exp (-(x - ν im)^2 / (2 * w im)) := by
      rw [hA_def, GaussianPDF.density_eq]
      have hs : Real.sqrt (2 * Real.pi * w im) ≠ 0 := by
        apply ne_of_gt; apply Real.sqrt_pos.mpr; have := hw_pos im; positivity
      field_simp
    rw [hAterm]
    -- Reassemble the (k+1)-sum from the im-term and the rest.
    rw [Fin.sum_univ_succAbove
          (fun j => c j * Real.exp (-(x - ν j)^2 / (2 * w j))) im]
    ring
  have h_bridge_recover : ∀ x : ℝ,
      (heatShift S' (w im) him_pos).density x
        + A * (⟨ν im, w im, him_pos⟩ : GaussianPDF).density x
      = Sp.density x := by
    intro x
    rw [hHeat_S' x]
    -- Sp.density x = S_f.density x - δ·G_idx x.
    rw [hSp_def, cps_density S_f idx δ x, hget_idx]
    -- The two bump terms coincide:  ⟨νg j₀, wg j₀ + w im⟩ = ⟨ν(im.succAbove j₀), w(im.succAbove j₀)⟩.
    have hbump : (⟨νg j₀, wg j₀ + w im, hwgbump_pos⟩ : GaussianPDF).density x
        = (⟨ν (im.succAbove j₀), w (im.succAbove j₀), hw_pos (im.succAbove j₀)⟩ : GaussianPDF).density x := by
      simp only [GaussianPDF.density_eq]
      have hμeq : νg j₀ = ν (im.succAbove j₀) := rfl
      have hτeq : wg j₀ + w im = w (im.succAbove j₀) := by rw [hwg_def]; ring
      rw [hμeq, hτeq]
    rw [hbump]
    -- Now: heatShift S_g0 - δ·G + A·N = S_f - δ·G  ⟸  heatShift S_g0 + A·N = S_f.
    have := h_full_recover x
    linarith [this]
  -- The full recovery `conv(conv(S'.density, v) + A·N(ν im, v), w im - v) = Sp.density`.
  have h_rec : ∀ (v : ℝ) (hv : 0 < v) (hvlt : v < w im),
      convolveWithGaussian
          (fun x => convolveWithGaussian S'.density v hv x
            + A * (⟨ν im, v, hv⟩ : GaussianPDF).density x)
          (w im - v) (by linarith)
        = Sp.density := by
    intro v hv hvlt
    funext x
    -- The combined SGC `Hv = heatShift S' v  ++  [(A, ⟨ν im, v⟩)]`.
    set Hv : SignedGaussianCombination :=
      ⟨(heatShift S' v hv).components ++ [(A, (⟨ν im, v, hv⟩ : GaussianPDF))]⟩ with hHv_def
    -- `Hv.density y = conv(S'.density, v) y + A·N(ν im, v) y`.
    have hHv_density : ∀ y : ℝ, Hv.density y
        = convolveWithGaussian S'.density v hv y + A * (⟨ν im, v, hv⟩ : GaussianPDF).density y := by
      intro y
      rw [hHv_def, SignedGaussianCombination.density_eq]
      simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
        List.map_nil, List.sum_nil, add_zero]
      rw [heatShift_density_eq_convolve S' v hv y]
      congr 1
    -- Convolving `Hv.density` by `w im - v` is the heat flow of `Hv`.
    rw [show (fun x => convolveWithGaussian S'.density v hv x
            + A * (⟨ν im, v, hv⟩ : GaussianPDF).density x) = Hv.density from by
        funext y; rw [hHv_density y]]
    rw [heatShift_density_eq_convolve Hv (w im - v) (by linarith) x]
    -- The heat flow of `Hv` by `w im - v` equals `heatShift S' (w im) ++ [(A, ⟨ν im, w im⟩)]`.
    have hHv_shift : heatShift Hv (w im - v) (by linarith)
        = ⟨(heatShift S' (w im) him_pos).components
            ++ [(A, (⟨ν im, w im, him_pos⟩ : GaussianPDF))]⟩ := by
      rw [hHv_def]
      show (⟨((heatShift S' v hv).components
          ++ [(A, (⟨ν im, v, hv⟩ : GaussianPDF))]).map
            (fun p => (p.1, shiftVarG p.2 (w im - v) (by linarith)))⟩ : SignedGaussianCombination)
        = _
      rw [List.map_append, List.map_cons, List.map_nil]
      refine congrArg SignedGaussianCombination.mk ?_
      refine congr_arg₂ (· ++ ·) ?_ ?_
      · -- `map (shiftVarG · (w im - v)) (heatShift S' v).components = (heatShift S' (w im)).components`
        show ((heatShift S' v hv).components.map
                (fun p => (p.1, shiftVarG p.2 (w im - v) (by linarith))))
          = (heatShift S' (w im) him_pos).components
        rw [heatShift, heatShift, List.map_map]
        apply List.map_congr_left
        intro p _
        simp only [Function.comp]
        -- `(p.1, shiftVarG (shiftVarG p.2 v) (w im-v)) = (p.1, shiftVarG p.2 (w im))`
        congr 1
        rw [shiftVarG, shiftVarG, shiftVarG]
        congr 1
        show p.2.varSq + v + (w im - v) = p.2.varSq + w im
        ring
      · -- the bump shifts to variance `v + (w im - v) = w im`.
        show [((A, (⟨ν im, v, hv⟩ : GaussianPDF)).1,
                shiftVarG (A, (⟨ν im, v, hv⟩ : GaussianPDF)).2 (w im - v) (by linarith))]
          = [(A, (⟨ν im, w im, him_pos⟩ : GaussianPDF))]
        congr 1
        rw [shiftVarG]
        have : v + (w im - v) = w im := by ring
        simp only [this]
    rw [hHv_shift]
    rw [SignedGaussianCombination.density_eq]
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      List.map_nil, List.sum_nil, add_zero]
    rw [← SignedGaussianCombination.density_eq (heatShift S' (w im) him_pos) x]
    exact h_bridge_recover x
  -- ===== Apply the analytic engine. =====
  rw [hf_eq]
  exact mainCaseSimpleTransport k hk S' hS'_simple ⟨ν im, hS'_ν_ne⟩ hS'_count
    (ν im) hS'_ν_ne A hA_ne (w im) him_pos S_f.density Sp.density hfp_analytic
    (by
      intro v hv hvlt
      have := h_rec v hv hvlt
      convert this using 3)
    (by rw [← hf_eq]; exact h_transport)

end Workspace.ProofLemmas
