import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.MiddleIndicatorSumsToOne
import Workspace.ProofLemmas.DeletionChannelTotalMass
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.CoinFlipDistUnique

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.BinVec
open Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess

open scoped Classical

namespace LengthsOnlyExistsScratch

-- binomial half sum over range
lemma binomial_half_sum (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
      (Nat.choose N k : ENNReal) * (ENNReal.ofReal (1/2)) ^ N = 1 := by
  have hsum_real : ∑ k ∈ Finset.range (N + 1),
      ((1:ℝ)/2) ^ N * (N.choose k : ℝ) = 1 := by
    have hadd := add_pow ((1:ℝ)/2) ((1:ℝ)/2) N
    have hconv : ∑ k ∈ Finset.range (N + 1), ((1:ℝ)/2) ^ N * (N.choose k : ℝ)
        = ∑ k ∈ Finset.range (N + 1), ((1:ℝ)/2)^k * ((1:ℝ)/2)^(N-k) * (N.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have hp : ((1:ℝ)/2)^k * ((1:ℝ)/2)^(N-k) = ((1:ℝ)/2)^N := by
        rw [← pow_add]; congr 1; omega
      rw [hp]
    rw [hconv, ← hadd]
    norm_num
  have hofreal : (ENNReal.ofReal (1/2)) ^ N = ENNReal.ofReal (((1:ℝ)/2)^N) := by
    rw [← ENNReal.ofReal_pow (by norm_num)]
  rw [hofreal]
  have hkey : ∀ k ∈ Finset.range (N + 1),
      (N.choose k : ENNReal) * ENNReal.ofReal (((1:ℝ)/2)^N) =
        ENNReal.ofReal (((1:ℝ)/2)^N * (N.choose k : ℝ)) := by
    intro k _
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    ring
  rw [Finset.sum_congr rfl hkey, ← ENNReal.ofReal_sum_of_nonneg, hsum_real, ENNReal.ofReal_one]
  intro k _
  positivity

-- offsetWeight sum over ℤ
lemma offsetWeight_tsum (n : ℕ) : (∑' r : ℤ, offsetWeight n r) = 1 := by
  classical
  set emb : ℕ ↪ ℤ := ⟨fun k => (k : ℤ) - ((n/4 : ℕ) : ℤ), by
    intro a b h; simp only at h; omega⟩ with hemb
  set s : Finset ℤ := (Finset.range (n/2 + 1)).map emb with hs
  rw [tsum_eq_sum (s := s)]
  · rw [hs, Finset.sum_map]
    have hconv : ∀ k ∈ Finset.range (n/2 + 1),
        offsetWeight n (emb k) =
          (Nat.choose (n / 2) k : ENNReal) * (ENNReal.ofReal (1 / 2)) ^ (n / 2) := by
      intro k hk
      rw [Finset.mem_range] at hk
      unfold offsetWeight
      have hembk : (emb k : ℤ) = (k : ℤ) - ((n/4:ℕ):ℤ) := by
        rw [hemb]; rfl
      have hlo : (0:ℤ) ≤ (emb k) + ((n/4:ℕ):ℤ) := by rw [hembk]; omega
      have hhi : (emb k) + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ) := by
        rw [hembk]
        have : (k:ℤ) ≤ ((n/2:ℕ):ℤ) := by exact_mod_cast Nat.lt_succ_iff.mp hk
        omega
      rw [dif_pos ⟨hlo, hhi⟩]
      have htoNat : ((emb k) + ((n/4:ℕ):ℤ)).toNat = k := by
        rw [hembk]
        have : ((k:ℤ) - ((n/4:ℕ):ℤ)) + ((n/4:ℕ):ℤ) = (k:ℤ) := by ring
        rw [this]; exact Int.toNat_natCast k
      rw [htoNat]
    rw [Finset.sum_congr rfl hconv]
    exact binomial_half_sum (n/2)
  · intro r hr
    unfold offsetWeight
    rw [dif_neg]
    rintro ⟨hlo, hhi⟩
    apply hr
    rw [hs, Finset.mem_map]
    refine ⟨(r + ((n/4:ℕ):ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have : ((r + ((n/4:ℕ):ℤ)).toNat : ℤ) ≤ ((n/2:ℕ):ℤ) := by
        rw [Int.toNat_of_nonneg hlo]; exact hhi
      omega
    · rw [hemb]
      simp only [Function.Embedding.coeFn_mk]
      rw [Int.toNat_of_nonneg hlo]; ring

-- binomialPMF tsum over all ℕ = 1
lemma binomialPMF_tsum (N : ℕ) (δ : DelProb) :
    (∑' z : ℕ, binomialPMF N δ z) = 1 := by
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · exact DeletionChannelTotalMassProof.binomialPMF_sum_eq_one N δ
  · intro z hz
    rw [Finset.mem_range] at hz
    exact DeletionChannelTotalMassProof.binomialPMF_eq_zero_of_gt δ (by omega)

-- prefixLengthWeight tsum over ℕ = 1 for in-range r
lemma prefixLengthWeight_tsum (n : ℕ) (δ : DelProb) (r : ℤ)
    (h : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)) :
    (∑' z : ℕ, prefixLengthWeight n δ r z) = 1 := by
  have hunfold : ∀ z, prefixLengthWeight n δ r z = binomialPMF (r + ((n/4:ℕ):ℤ)).toNat δ z := by
    intro z; unfold prefixLengthWeight; rw [dif_pos h]
  simp only [hunfold]
  exact binomialPMF_tsum _ δ

lemma suffixLengthWeight_tsum (n : ℕ) (δ : DelProb) (r : ℤ)
    (h : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)) :
    (∑' z : ℕ, suffixLengthWeight n δ r z) = 1 := by
  have hunfold : ∀ z, suffixLengthWeight n δ r z =
      binomialPMF (n - n/2 - (r + ((n/4:ℕ):ℤ)).toNat) δ z := by
    intro z; unfold suffixLengthWeight; rw [dif_pos h]
  simp only [hunfold]
  exact binomialPMF_tsum _ δ

-- the mass function for fixed b
noncomputable def gmass (n : ℕ) (δ : DelProb) (b : BinVec n)
    (p : BinVec (n/2) × ℕ × ℕ) : ENNReal :=
  ∑' r : ℤ,
    offsetWeight n r *
      (prefixLengthWeight n δ r p.2.1 *
        (suffixLengthWeight n δ r p.2.2 *
          middleIndicator n b p.1 r))

-- inner factor F(r) = 1 for in-range r
lemma Fr_eq_one (n : ℕ) (δ : DelProb) (b : BinVec n) (r : ℤ)
    (h : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)) :
    (∑' (m : BinVec (n/2)) (zM : ℕ) (zP : ℕ),
        prefixLengthWeight n δ r zM *
          (suffixLengthWeight n δ r zP * middleIndicator n b m r)) = 1 := by
  -- sum over zP first
  have hmid : (∑' m : BinVec (n/2), middleIndicator n b m r) = 1 := by
    apply MiddleIndicatorSumsToOne
    · rw [← DeletionChannelTotalMassProof.nat_div_four_cast]; exact h.1
    · rw [← DeletionChannelTotalMassProof.nat_div_four_cast,
          ← DeletionChannelTotalMassProof.nat_div_two_cast]; exact h.2
  have hpre := prefixLengthWeight_tsum n δ r h
  have hsuf := suffixLengthWeight_tsum n δ r h
  -- collapse zP: ∑' zP, prefixLW zM * (suffixLW zP * mid) = prefixLW zM * (mid * ∑' zP suffixLW)
  have step1 : ∀ (m : BinVec (n/2)) (zM : ℕ),
      (∑' zP : ℕ, prefixLengthWeight n δ r zM *
          (suffixLengthWeight n δ r zP * middleIndicator n b m r))
        = prefixLengthWeight n δ r zM * middleIndicator n b m r := by
    intro m zM
    rw [ENNReal.tsum_mul_left]
    rw [show (∑' zP : ℕ, suffixLengthWeight n δ r zP * middleIndicator n b m r)
          = (∑' zP : ℕ, suffixLengthWeight n δ r zP) * middleIndicator n b m r from by
        rw [ENNReal.tsum_mul_right]]
    rw [hsuf, one_mul]
  simp only [step1]
  -- collapse zM: ∑' zM, prefixLW zM * mid = mid
  have step2 : ∀ (m : BinVec (n/2)),
      (∑' zM : ℕ, prefixLengthWeight n δ r zM * middleIndicator n b m r)
        = middleIndicator n b m r := by
    intro m
    rw [ENNReal.tsum_mul_right, hpre, one_mul]
  simp only [step2]
  exact hmid

lemma gmass_tsum (n : ℕ) (δ : DelProb) (b : BinVec n) :
    (∑' p : BinVec (n/2) × ℕ × ℕ, gmass n δ b p) = 1 := by
  unfold gmass
  -- swap p and r
  rw [ENNReal.tsum_comm]
  -- now ∑' r, ∑' p, offsetWeight r * (...)
  rw [show (∑' (r : ℤ) (p : BinVec (n/2) × ℕ × ℕ),
        offsetWeight n r * (prefixLengthWeight n δ r p.2.1 *
          (suffixLengthWeight n δ r p.2.2 * middleIndicator n b p.1 r)))
      = ∑' r : ℤ, offsetWeight n r from by
    apply tsum_congr
    intro r
    by_cases hr : 0 ≤ r + ((n/4:ℕ):ℤ) ∧ r + ((n/4:ℕ):ℤ) ≤ ((n/2:ℕ):ℤ)
    · -- in range: pull offsetWeight out, inner = 1
      rw [ENNReal.tsum_mul_left]
      have hinner : (∑' (p : BinVec (n/2) × ℕ × ℕ),
            prefixLengthWeight n δ r p.2.1 *
              (suffixLengthWeight n δ r p.2.2 * middleIndicator n b p.1 r)) = 1 := by
        rw [ENNReal.tsum_prod']
        rw [show (∑' (m : BinVec (n/2)) (q : ℕ × ℕ),
              prefixLengthWeight n δ r (m, q).2.1 *
                (suffixLengthWeight n δ r (m, q).2.2 * middleIndicator n b (m, q).1 r))
            = (∑' (m : BinVec (n/2)) (zM : ℕ) (zP : ℕ),
              prefixLengthWeight n δ r zM *
                (suffixLengthWeight n δ r zP * middleIndicator n b m r)) from by
          refine tsum_congr (fun m => ?_)
          rw [ENNReal.tsum_prod']]
        exact Fr_eq_one n δ b r hr
      rw [hinner, mul_one]
    · -- out of range: offsetWeight r = 0
      have : offsetWeight n r = 0 := by unfold offsetWeight; rw [dif_neg hr]
      rw [this]
      simp]
  exact offsetWeight_tsum n

-- the inner PMF built from gmass
noncomputable def innerPMF (n : ℕ) (δ : DelProb) (S : ProbVec n) (b : BinVec n) :
    PMF (BinVec (n/2) × ℕ × ℕ) :=
  ⟨gmass n δ b, (Summable.hasSum_iff ENNReal.summable).mpr (gmass_tsum n δ b)⟩

end LengthsOnlyExistsScratch

theorem lengthsOnly_exists :
    ∀ {n : ℕ} (S : Workspace.Types.ProbVec.ProbVec n) (δ : Workspace.Types.DelProb.DelProb),
      Nonempty (Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n S δ) := by
  intro n S δ
  obtain ⟨cfd₀⟩ := CoinFlipDistExists S
  refine ⟨{
    toPMF := cfd₀.toPMF.bind (fun b => LengthsOnlyExistsScratch.innerPMF n δ S b)
    composition_law := ?_ }⟩
  intro cfd m zMinus zPlus
  simp only [PMF.bind_apply]
  apply tsum_congr; intro b
  rw [CoinFlipDistUnique S cfd₀ cfd]
  conv_rhs => rw [ENNReal.tsum_mul_left]
  congr 1
