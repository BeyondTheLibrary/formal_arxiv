import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.TVPartialBoundedHelpers
import Workspace.ProofLemmas.TVPartialBoundedAssembly
import Workspace.ProofLemmas.TVPartialGoodCollapse

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open TVPartialBoundedHelpers
open TVPartialBoundedAssembly
open TVPartialGoodCollapse

open scoped Classical

namespace TVPartialBoundedFinal

variable {n : ℕ} {Se : Workspace.Types.ProbVec.ProbVec n} {δ : DelProb}

/-- `offsetWeight` is never `⊤`. -/
lemma offsetWeight_ne_top (r : ℤ) : offsetWeight n r ≠ ⊤ := by
  unfold offsetWeight
  simp only []; split_ifs
  · exact ENNReal.mul_ne_top (by simp) (by apply ENNReal.pow_ne_top; simp)
  · simp

lemma bad_summand_ne_top (cfd : CoinFlipDist n Se) (br : (BinVec n) × ℤ) :
    (if badPred n br.1 br.2 then cfd.toPMF br.1 * offsetWeight n br.2 else 0) ≠ ⊤ := by
  split
  · exact ENNReal.mul_ne_top (PMF.apply_ne_top cfd.toPMF br.1) (offsetWeight_ne_top br.2)
  · simp

/-- Bridge: the statement's real bad term equals `(badTotal cfd).toReal`. -/
lemma badTotal_toReal_eq (cfd : CoinFlipDist n Se) :
    (∑' (br : (BinVec n) × ℤ),
        (if badPred n br.1 br.2 then
            (cfd.toPMF br.1).toReal * (offsetWeight n br.2).toReal
          else 0))
      = (badTotal cfd).toReal := by
  have hsum : ∀ br : (BinVec n) × ℤ,
      (if badPred n br.1 br.2 then
          (cfd.toPMF br.1).toReal * (offsetWeight n br.2).toReal
        else 0)
        = (if badPred n br.1 br.2 then cfd.toPMF br.1 * offsetWeight n br.2 else 0).toReal := by
    intro br
    split
    · rw [ENNReal.toReal_mul]
    · simp
  rw [tsum_congr hsum]
  rw [← ENNReal.tsum_toReal_eq (bad_summand_ne_top cfd)]
  congr 1
  unfold badTotal
  rw [← ENNReal.tsum_prod]

lemma badTotal_le_one (cfd : CoinFlipDist n Se) :
    badTotal cfd ≤ 1 := by
  unfold badTotal
  calc ∑' (b : BinVec n) (r : ℤ),
          (if badPred n b r then cfd.toPMF b * offsetWeight n r else 0)
      ≤ ∑' (b : BinVec n) (r : ℤ), cfd.toPMF b * offsetWeight n r := by
        apply ENNReal.tsum_le_tsum; intro b
        apply ENNReal.tsum_le_tsum; intro r
        split
        · exact le_refl _
        · exact zero_le _
    _ = ∑' (b : BinVec n), cfd.toPMF b * (∑' r : ℤ, offsetWeight n r) := by
        apply tsum_congr; intro b
        rw [ENNReal.tsum_mul_left]
    _ = ∑' (b : BinVec n), cfd.toPMF b := by
        apply tsum_congr; intro b
        rw [LengthsOnlyExistsScratch.offsetWeight_tsum n, mul_one]
    _ = 1 := PMF.tsum_coe cfd.toPMF

lemma badTotal_ne_top (cfd : CoinFlipDist n Se) :
    badTotal cfd ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (badTotal_le_one cfd)

lemma tsum_badMass_toReal_le (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ) :
    (∑' p : (BinVec (n / 2) × Trace n × Trace n),
        (badMass (δ := δ) cfd p.1 p.2.1 p.2.2).toReal)
      ≤ (badTotal cfd).toReal := by
  have hconv : (∑' p : (BinVec (n / 2) × Trace n × Trace n),
        (badMass (δ := δ) cfd p.1 p.2.1 p.2.2).toReal)
      = (∑' p : (BinVec (n / 2) × Trace n × Trace n),
          badMass (δ := δ) cfd p.1 p.2.1 p.2.2).toReal := by
    rw [ENNReal.tsum_toReal_eq]
    intro p; exact badMass_ne_top cfd partE p.1 p.2.1 p.2.2
  rw [hconv]
  apply ENNReal.toReal_mono (badTotal_ne_top cfd)
  exact sum_badMass_le_badTotal cfd

lemma tsum_badLenMass_toReal_le (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ) :
    (∑' c : (BinVec (n / 2) × ℕ × ℕ),
        (badLenMass (δ := δ) cfd c.1 c.2.1 c.2.2).toReal)
      ≤ (badTotal cfd).toReal := by
  have hconv : (∑' c : (BinVec (n / 2) × ℕ × ℕ),
        (badLenMass (δ := δ) cfd c.1 c.2.1 c.2.2).toReal)
      = (∑' c : (BinVec (n / 2) × ℕ × ℕ),
          badLenMass (δ := δ) cfd c.1 c.2.1 c.2.2).toReal := by
    rw [ENNReal.tsum_toReal_eq]
    intro c; exact badLenMass_ne_top cfd lenE c.1 c.2.1 c.2.2
  rw [hconv]
  apply ENNReal.toReal_mono (badTotal_ne_top cfd)
  exact sum_badLenMass_le_badTotal cfd

lemma trace_triangle_sum {So : Workspace.Types.ProbVec.ProbVec n}
    (cfdE : CoinFlipDist n Se) (cfdO : CoinFlipDist n So)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (partO : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n So δ) :
    (∑' s : (BinVec (n / 2) × Trace n × Trace n),
        |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|)
      ≤ (∑' p : (BinVec (n / 2) × Trace n × Trace n),
            |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
              - (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal|)
        + (badTotal cfdE).toReal + (badTotal cfdO).toReal := by
  have hGE : Summable (fun p : (BinVec (n / 2) × Trace n × Trace n) =>
      (goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal) :=
    summable_toReal_of_le_partMass cfdE partE _ (fun p => goodMass_le_partMass cfdE p.1 p.2.1 p.2.2)
  have hGO : Summable (fun p : (BinVec (n / 2) × Trace n × Trace n) =>
      (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal) :=
    summable_toReal_of_le_partMass cfdO partO _ (fun p => goodMass_le_partMass cfdO p.1 p.2.1 p.2.2)
  have hBE : Summable (fun p : (BinVec (n / 2) × Trace n × Trace n) =>
      (badMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal) :=
    summable_toReal_of_le_partMass cfdE partE _ (fun p => badMass_le_partMass cfdE p.1 p.2.1 p.2.2)
  have hBO : Summable (fun p : (BinVec (n / 2) × Trace n × Trace n) =>
      (badMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal) :=
    summable_toReal_of_le_partMass cfdO partO _ (fun p => badMass_le_partMass cfdO p.1 p.2.1 p.2.2)
  have hgooddiff : Summable (fun p : (BinVec (n / 2) × Trace n × Trace n) =>
      |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
        - (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal|) := by
    apply Summable.of_nonneg_of_le (fun p => abs_nonneg _) ?_ (hGE.add hGO)
    intro p
    calc |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
            - (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal|
        ≤ |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal|
          + |(goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal| := abs_sub _ _
      _ = (goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
          + (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal := by
          rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]
  have hpartdiff : Summable (fun s : (BinVec (n / 2) × Trace n × Trace n) =>
      |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|) := by
    apply Summable.of_nonneg_of_le (fun s => abs_nonneg _) ?_
      (((hGE.add hGO).add hBE).add hBO)
    intro s
    obtain ⟨m, t₁, t₂⟩ := s
    simp only
    rw [part_toReal_split cfdE partE m t₁ t₂, part_toReal_split cfdO partO m t₁ t₂]
    have hge := ENNReal.toReal_nonneg (a := goodMass (δ := δ) cfdE m t₁ t₂)
    have hgo := ENNReal.toReal_nonneg (a := goodMass (δ := δ) cfdO m t₁ t₂)
    have hbe := ENNReal.toReal_nonneg (a := badMass (δ := δ) cfdE m t₁ t₂)
    have hbo := ENNReal.toReal_nonneg (a := badMass (δ := δ) cfdO m t₁ t₂)
    rw [abs_le]
    constructor <;> nlinarith [hge, hgo, hbe, hbo]
  have hpt : ∀ s : (BinVec (n / 2) × Trace n × Trace n),
      |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|
        ≤ |(goodMass (δ := δ) cfdE s.1 s.2.1 s.2.2).toReal
            - (goodMass (δ := δ) cfdO s.1 s.2.1 s.2.2).toReal|
          + (badMass (δ := δ) cfdE s.1 s.2.1 s.2.2).toReal
          + (badMass (δ := δ) cfdO s.1 s.2.1 s.2.2).toReal := by
    intro s
    obtain ⟨m, t₁, t₂⟩ := s
    rw [part_toReal_split cfdE partE m t₁ t₂, part_toReal_split cfdO partO m t₁ t₂]
    have hbe := ENNReal.toReal_nonneg (a := badMass (δ := δ) cfdE m t₁ t₂)
    have hbo := ENNReal.toReal_nonneg (a := badMass (δ := δ) cfdO m t₁ t₂)
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le ((goodMass (δ := δ) cfdE m t₁ t₂).toReal
                - (goodMass (δ := δ) cfdO m t₁ t₂).toReal)]
    · nlinarith [le_abs_self ((goodMass (δ := δ) cfdE m t₁ t₂).toReal
                - (goodMass (δ := δ) cfdO m t₁ t₂).toReal)]
  calc (∑' s : (BinVec (n / 2) × Trace n × Trace n),
          |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|)
      ≤ ∑' s : (BinVec (n / 2) × Trace n × Trace n),
          (|(goodMass (δ := δ) cfdE s.1 s.2.1 s.2.2).toReal
              - (goodMass (δ := δ) cfdO s.1 s.2.1 s.2.2).toReal|
            + (badMass (δ := δ) cfdE s.1 s.2.1 s.2.2).toReal
            + (badMass (δ := δ) cfdO s.1 s.2.1 s.2.2).toReal) :=
        Summable.tsum_le_tsum hpt hpartdiff ((hgooddiff.add hBE).add hBO)
    _ = (∑' p : (BinVec (n / 2) × Trace n × Trace n),
            |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
              - (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal|)
          + (∑' p : (BinVec (n / 2) × Trace n × Trace n),
              (badMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal)
          + (∑' p : (BinVec (n / 2) × Trace n × Trace n),
              (badMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal) := by
        rw [Summable.tsum_add (hgooddiff.add hBE) hBO, Summable.tsum_add hgooddiff hBE]
    _ ≤ (∑' p : (BinVec (n / 2) × Trace n × Trace n),
            |(goodMass (δ := δ) cfdE p.1 p.2.1 p.2.2).toReal
              - (goodMass (δ := δ) cfdO p.1 p.2.1 p.2.2).toReal|)
          + (badTotal cfdE).toReal + (badTotal cfdO).toReal := by
        gcongr
        · exact tsum_badMass_toReal_le cfdE partE
        · exact tsum_badMass_toReal_le cfdO partO

lemma length_triangle_sum {So : Workspace.Types.ProbVec.ProbVec n}
    (cfdE : CoinFlipDist n Se) (cfdO : CoinFlipDist n So)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ) :
    (∑' c : (BinVec (n / 2) × ℕ × ℕ),
        |(goodLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
          - (goodLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal|)
      ≤ (∑' c : (BinVec (n / 2) × ℕ × ℕ),
            |((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|)
        + (badTotal cfdE).toReal + (badTotal cfdO).toReal := by
  have hGE : Summable (fun c : (BinVec (n / 2) × ℕ × ℕ) =>
      (goodLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal) :=
    summable_toReal_of_le_lenMass cfdE lenE _ (fun c => goodLenMass_le_lenMass cfdE c.1 c.2.1 c.2.2)
  have hGO : Summable (fun c : (BinVec (n / 2) × ℕ × ℕ) =>
      (goodLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal) :=
    summable_toReal_of_le_lenMass cfdO lenO _ (fun c => goodLenMass_le_lenMass cfdO c.1 c.2.1 c.2.2)
  have hBE : Summable (fun c : (BinVec (n / 2) × ℕ × ℕ) =>
      (badLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal) :=
    summable_toReal_of_le_lenMass cfdE lenE _ (fun c => badLenMass_le_lenMass cfdE c.1 c.2.1 c.2.2)
  have hBO : Summable (fun c : (BinVec (n / 2) × ℕ × ℕ) =>
      (badLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal) :=
    summable_toReal_of_le_lenMass cfdO lenO _ (fun c => badLenMass_le_lenMass cfdO c.1 c.2.1 c.2.2)
  have hlendiff : Summable (fun c : (BinVec (n / 2) × ℕ × ℕ) =>
      |((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|) := by
    apply Summable.of_nonneg_of_le (fun c => abs_nonneg _) ?_
      (((hGE.add hGO).add hBE).add hBO)
    intro c
    obtain ⟨m, zM, zP⟩ := c
    simp only
    rw [len_toReal_split cfdE lenE m zM zP, len_toReal_split cfdO lenO m zM zP]
    have hge := ENNReal.toReal_nonneg (a := goodLenMass (δ := δ) cfdE m zM zP)
    have hgo := ENNReal.toReal_nonneg (a := goodLenMass (δ := δ) cfdO m zM zP)
    have hbe := ENNReal.toReal_nonneg (a := badLenMass (δ := δ) cfdE m zM zP)
    have hbo := ENNReal.toReal_nonneg (a := badLenMass (δ := δ) cfdO m zM zP)
    rw [abs_le]
    constructor <;> nlinarith [hge, hgo, hbe, hbo]
  have hpt : ∀ c : (BinVec (n / 2) × ℕ × ℕ),
      |(goodLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
          - (goodLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal|
        ≤ |((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|
          + (badLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
          + (badLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal := by
    intro c
    obtain ⟨m, zM, zP⟩ := c
    rw [len_toReal_split cfdE lenE m zM zP, len_toReal_split cfdO lenO m zM zP]
    have hbe := ENNReal.toReal_nonneg (a := badLenMass (δ := δ) cfdE m zM zP)
    have hbo := ENNReal.toReal_nonneg (a := badLenMass (δ := δ) cfdO m zM zP)
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le ((goodLenMass (δ := δ) cfdE m zM zP).toReal
                + (badLenMass (δ := δ) cfdE m zM zP).toReal
                - ((goodLenMass (δ := δ) cfdO m zM zP).toReal
                  + (badLenMass (δ := δ) cfdO m zM zP).toReal))]
    · nlinarith [le_abs_self ((goodLenMass (δ := δ) cfdE m zM zP).toReal
                + (badLenMass (δ := δ) cfdE m zM zP).toReal
                - ((goodLenMass (δ := δ) cfdO m zM zP).toReal
                  + (badLenMass (δ := δ) cfdO m zM zP).toReal))]
  calc (∑' c : (BinVec (n / 2) × ℕ × ℕ),
          |(goodLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
            - (goodLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal|)
      ≤ ∑' c : (BinVec (n / 2) × ℕ × ℕ),
          (|((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|
            + (badLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
            + (badLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal) :=
        Summable.tsum_le_tsum hpt (hGE.sub hGO |>.abs) ((hlendiff.add hBE).add hBO)
    _ = (∑' c : (BinVec (n / 2) × ℕ × ℕ),
            |((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|)
          + (∑' c : (BinVec (n / 2) × ℕ × ℕ),
              (badLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal)
          + (∑' c : (BinVec (n / 2) × ℕ × ℕ),
              (badLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal) := by
        rw [Summable.tsum_add (hlendiff.add hBE) hBO, Summable.tsum_add hlendiff hBE]
    _ ≤ (∑' c : (BinVec (n / 2) × ℕ × ℕ),
            |((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|)
          + (badTotal cfdE).toReal + (badTotal cfdO).toReal := by
        gcongr
        · exact tsum_badLenMass_toReal_le cfdE lenE
        · exact tsum_badLenMass_toReal_le cfdO lenO

/-- **Main theorem** (paper Lemma 6, structural good/bad TV decomposition). -/
theorem tvPartialBounded {So : Workspace.Types.ProbVec.ProbVec n}
    (cfdE : CoinFlipDist n Se) (cfdO : CoinFlipDist n So)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (partO : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n So δ)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ) :
    ((1/2) : ℝ) * ∑' s : (BinVec (n / 2) × Trace n × Trace n),
       |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|
      ≤ ((1/2) : ℝ) * ∑' s : (BinVec (n / 2) × ℕ × ℕ),
           |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|
        + (∑' (br : (BinVec n) × ℤ),
            (if badPred n br.1 br.2 then
              ((cfdE.toPMF br.1).toReal *
               (Workspace.Types.PartialDeletionProcess.offsetWeight n br.2).toReal)
             else 0))
        + (∑' (br : (BinVec n) × ℤ),
            (if badPred n br.1 br.2 then
              ((cfdO.toPMF br.1).toReal *
               (Workspace.Types.PartialDeletionProcess.offsetWeight n br.2).toReal)
             else 0)) := by
  rw [badTotal_toReal_eq cfdE, badTotal_toReal_eq cfdO]
  set BTE := (badTotal cfdE).toReal with hBTE
  set BTO := (badTotal cfdO).toReal with hBTO
  have htrace := trace_triangle_sum cfdE cfdO partE partO
  have hpush := good_pushforward (δ := δ) cfdE cfdO
  have hlen := length_triangle_sum cfdE cfdO lenE lenO
  rw [hpush] at htrace
  have hcomb : (∑' s : (BinVec (n / 2) × Trace n × Trace n),
        |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|)
      ≤ (∑' c : (BinVec (n / 2) × ℕ × ℕ),
            |((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|)
          + BTE + BTO + BTE + BTO := by
    calc (∑' s : (BinVec (n / 2) × Trace n × Trace n),
            |((partE.toPMF s).toReal) - ((partO.toPMF s).toReal)|)
        ≤ (∑' c : (BinVec (n / 2) × ℕ × ℕ),
              |(goodLenMass (δ := δ) cfdE c.1 c.2.1 c.2.2).toReal
                - (goodLenMass (δ := δ) cfdO c.1 c.2.1 c.2.2).toReal|)
            + BTE + BTO := htrace
      _ ≤ ((∑' c : (BinVec (n / 2) × ℕ × ℕ),
              |((lenE.toPMF c).toReal) - ((lenO.toPMF c).toReal)|)
            + BTE + BTO) + BTE + BTO := by gcongr
  have hhalf : (0:ℝ) ≤ 1/2 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hcomb hhalf,
    ENNReal.toReal_nonneg (a := badTotal cfdE),
    ENNReal.toReal_nonneg (a := badTotal cfdO)]

end TVPartialBoundedFinal
