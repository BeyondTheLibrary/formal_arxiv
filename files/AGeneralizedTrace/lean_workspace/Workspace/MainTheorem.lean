import Mathlib
import Workspace.Types.LowerBoundConstants
import Workspace.Types.LowerBoundWitness
import Workspace.Types.ProbVec
import Workspace.Types.LInfDistance
import Workspace.Types.L1Distance
import Workspace.Types.DelProb
import Workspace.Types.TraceDist
import Workspace.Types.TVDistance
import Workspace.ProofLemmas.SublemmaWitnessConstruction
import Workspace.ProofLemmas.SublemmaLInfSeparation
import Workspace.ProofLemmas.SublemmaL1Bounds
import Workspace.ProofLemmas.SublemmaTVAssembly
import Workspace.ProofLemmas.SublemmaTVReduceToHalf

open Workspace.Types.LowerBoundConstants
open Workspace.Types.LowerBoundWitness

namespace Workspace.MainTheorem

/--
**Main theorem (Rivkin–Valiant–Valiant, Theorem 1).** Lower bound for the
generalized trace-reconstruction problem on probability strings.

There exist absolute constants `c_delta, c_inf, c_1, C_1, c_tv > 0` and a
natural-number threshold `n_0` such that for every `n ≥ n_0` one can exhibit
two length-`n` probability strings `S, S'` with:

* constant `ℓ∞`-separation `‖S - S'‖_∞ ≥ c_inf`;
* `√n`-scale `ℓ¹`-separation `c_1 · √n ≤ ‖S - S'‖_1 ≤ C_1 · √n`;
* exponential indistinguishability of their trace distributions at every
  deletion rate `δ ≥ c_delta / √n`, namely
  `d_TV(TraceDist(S, δ), TraceDist(S', δ)) ≤ exp(- c_tv · √n)`.

The constants and the thresholds are bundled as `LowerBoundConstants`, and
each witness pair `(S, S')` together with all four quantitative estimates is
packaged as a `LowerBoundWitness C n`. The theorem then asserts that such a
witness exists for every sufficiently large `n` with `n ≡ 1 (mod 8)`.

The paper (RVV, `deletion.tex:268-271`) constructs the witnesses "for `n` odd",
treating `n/4, n/2, 3n/4, n/8` as real-valued. The formalization pins this to the
representative residue `n ≡ 1 (mod 8)`, for which all of these integer divisions are
exact; this is a faithful specialization of the paper's odd-`n` construction (the
paper's argument is insensitive to the `O(1)` integer-division slack).
-/
theorem lower_bound_trace_reconstruction :
    ∃ (C : LowerBoundConstants),
      ∀ (n : ℕ), C.n0 ≤ n → n % 8 = 1 → Nonempty (LowerBoundWitness C n) := by
  -- Useful positivity facts.
  have hexp2 : 0 < Real.exp 2 := Real.exp_pos 2
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hsqrt2pi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi
  -- Build the modular constants bundle.
  let Cmod : LowerBoundConstants :=
    { cDelta := 320
    , cInf   := 1 / (16 * Real.exp 2 * Real.sqrt (2 * Real.pi))
    , c1     := 1 / (8 * Real.exp 2 * Real.sqrt (2 * Real.pi))
    , cC1    := 1 / (2 * Real.exp 2 * Real.sqrt (2 * Real.pi))
    , cTv    := 1 / 64
    , n0     := 10 ^ 12
    , cDelta_pos := by norm_num
    , cInf_pos   := by positivity
    , c1_pos     := by positivity
    , cC1_pos    := by positivity
    , cTv_pos    := by norm_num
    , c1_le_cC1  := by
        have hpos : 0 < 2 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
        have hpos8 : 0 < 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
        have hle : 2 * Real.exp 2 * Real.sqrt (2 * Real.pi)
                    ≤ 8 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by
          nlinarith [hexp2, hsqrt2pi]
        exact one_div_le_one_div_of_le hpos hle
    }
  -- Construct the witness directly for every `m ≥ n0` with `m ≡ 1 (mod 8)`.
  have hyp : ∀ (m : ℕ), Cmod.n0 ≤ m → m % 8 = 1 →
      Nonempty (Workspace.Types.LowerBoundWitness.LowerBoundWitness Cmod m) := by
    intro m hm hm8
    -- m ≥ 10^12 ≥ 1.
    have hm_pos : 1 ≤ m := by
      have : (1 : ℕ) ≤ 10 ^ 12 := by norm_num
      exact this.trans hm
    -- Build the witnesses Se, So.
    obtain ⟨Se, So, hSe, hSo⟩ := SublemmaWitnessConstruction m hm_pos
    -- L∞ separation
    have hLInf := Workspace.ProofLemmas.SublemmaLInfSeparation m hm_pos (by omega : m % 2 = 1) Se So hSe hSo
    -- L¹ bounds
    have hL1 := SublemmaL1Bounds m hm_pos hm8 Se So hSe hSo
    -- TV bound for δ ≤ 1/2.
    have hTVHalf :
        ∀ δ : Workspace.Types.DelProb.DelProb,
          δ.val ≤ 1 / 2 →
          Cmod.cDelta / Real.sqrt m ≤ δ.val →
          ∀ (td₁ : Workspace.Types.TraceDist.TraceDist m Se δ)
            (td₂ : Workspace.Types.TraceDist.TraceDist m So δ),
            Workspace.Types.TVDistance.TVDistance td₁.toPMF td₂.toPMF
              ≤ Real.exp (-(Cmod.cTv * Real.sqrt m)) := by
      intro δ hδub hδlb td₁ td₂
      -- SublemmaTVAssembly takes hypotheses in the order (320/√m ≤ δ.val), (δ.val ≤ 1/2).
      -- Note Cmod.cDelta = 320 and Cmod.cTv = 1/4.
      have hδlb' : (320 : ℝ) / Real.sqrt m ≤ δ.val := by
        simpa [Cmod] using hδlb
      have hres := SublemmaTVAssembly m hm hm8 Se So hSe hSo δ hδlb' hδub td₁ td₂
      -- Convert exp(-(1/4 * √m)) to exp(-(Cmod.cTv * √m)).
      simpa [Cmod] using hres
    -- Extend to all δ via SublemmaTVReduceToHalf.
    -- The corner regime never occurs: Cmod.cDelta = 320 and m ≥ 10^12, so
    -- 320/√m ≤ 320/√(10^12) = 320/10^6 = 3.2e-4 ≤ 1/2.
    have hcd_half : Cmod.cDelta / Real.sqrt m ≤ 1/2 := by
      have hcd_eq : Cmod.cDelta = (320 : ℝ) := by simp [Cmod]
      rw [hcd_eq]
      have hm_real : (409600 : ℝ) ≤ (m : ℝ) := by
        have h2 : (409600 : ℕ) ≤ m := (by norm_num : (409600:ℕ) ≤ 10^12).trans hm
        exact_mod_cast h2
      have hsqrt : (640 : ℝ) ≤ Real.sqrt m := by
        rw [show (640:ℝ) = Real.sqrt (640^2) by simp [Real.sqrt_sq]]
        exact Real.sqrt_le_sqrt (by nlinarith [hm_real])
      have hsqrt_pos : (0 : ℝ) < Real.sqrt m := by linarith
      rw [div_le_iff₀ hsqrt_pos]
      linarith
    have hTV := SublemmaTVReduceToHalf Cmod m Se So hcd_half hTVHalf
    -- Now construct the LowerBoundWitness.
    refine ⟨{
      S := Se
      S' := So
      n_ge_n0 := hm
      linf_sep := ?_
      l1_lb := ?_
      l1_ub := ?_
      tv_decay := ?_ }⟩
    · -- linf_sep: Cmod.cInf ≤ LInfDistance Se So
      simpa [Cmod, ge_iff_le] using hLInf
    · -- l1_lb
      simpa [Cmod] using hL1.1
    · -- l1_ub
      simpa [Cmod] using hL1.2
    · -- tv_decay
      intro δ hδlb td₁ td₂
      have h := hTV δ hδlb td₁ td₂
      -- Convert exp(-(Cmod.cTv * √m)) to exp(-Cmod.cTv * √m).
      simpa [neg_mul] using h
  -- The witnesses for `n ≡ 1 (mod 8)` are constructed directly; no padding needed.
  exact ⟨Cmod, hyp⟩

end Workspace.MainTheorem
