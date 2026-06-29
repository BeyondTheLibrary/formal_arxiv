import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.Trace
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.DeletionLengthMarginal
import Workspace.ProofLemmas.TraceFromZeroIsLengthBinomial
import Workspace.ProofLemmas.TVPartialBoundedHelpers

open Workspace.Types.BinVec
open Workspace.Types.Trace
open Workspace.Types.DelProb
open Workspace.Types.CoinFlipDist
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open TVPartialBoundedHelpers

open scoped Classical

namespace TVPartialBoundedAssembly

variable {n : ℕ} {Se : Workspace.Types.ProbVec.ProbVec n} {δ : DelProb}

/-- PMF values are `≠ ⊤`. -/
lemma partMass_ne_top (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (m : BinVec (n / 2)) (t₁ t₂ : Trace n) :
    partMass (δ := δ) cfd m t₁ t₂ ≠ ⊤ := by
  rw [← partE_eq_partMass cfd partE]
  exact PMF.apply_ne_top partE.toPMF (m, t₁, t₂)

/-- good ≤ part, so goodMass ≠ ⊤. -/
lemma goodMass_le_partMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (t₁ t₂ : Trace n) :
    goodMass (δ := δ) cfd m t₁ t₂ ≤ partMass (δ := δ) cfd m t₁ t₂ := by
  rw [partMass_eq_good_add_bad]; exact le_self_add

/-- bad ≤ part. -/
lemma badMass_le_partMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (t₁ t₂ : Trace n) :
    badMass (δ := δ) cfd m t₁ t₂ ≤ partMass (δ := δ) cfd m t₁ t₂ := by
  rw [partMass_eq_good_add_bad]; exact le_add_self

lemma goodMass_ne_top (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (m : BinVec (n / 2)) (t₁ t₂ : Trace n) :
    goodMass (δ := δ) cfd m t₁ t₂ ≠ ⊤ :=
  ne_top_of_le_ne_top (partMass_ne_top cfd partE m t₁ t₂) (goodMass_le_partMass cfd m t₁ t₂)

lemma badMass_ne_top (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (m : BinVec (n / 2)) (t₁ t₂ : Trace n) :
    badMass (δ := δ) cfd m t₁ t₂ ≠ ⊤ :=
  ne_top_of_le_ne_top (partMass_ne_top cfd partE m t₁ t₂) (badMass_le_partMass cfd m t₁ t₂)

/-- Real-valued partial decomposition. -/
lemma part_toReal_split (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (m : BinVec (n / 2)) (t₁ t₂ : Trace n) :
    (partE.toPMF (m, t₁, t₂)).toReal
      = (goodMass (δ := δ) cfd m t₁ t₂).toReal + (badMass (δ := δ) cfd m t₁ t₂).toReal := by
  rw [partE_eq_partMass cfd partE, partMass_eq_good_add_bad,
    ENNReal.toReal_add (goodMass_ne_top cfd partE m t₁ t₂) (badMass_ne_top cfd partE m t₁ t₂)]

/-! ## Total-mass and summability facts. -/

lemma tsum_partMass_eq_one (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ) :
    (∑' p : (BinVec (n / 2) × Trace n × Trace n),
        partMass (δ := δ) cfd p.1 p.2.1 p.2.2) = 1 := by
  have : (∑' p : (BinVec (n / 2) × Trace n × Trace n),
        partMass (δ := δ) cfd p.1 p.2.1 p.2.2)
      = ∑' p : (BinVec (n / 2) × Trace n × Trace n), partE.toPMF p := by
    apply tsum_congr; intro p
    rw [partE_eq_partMass cfd partE]
  rw [this, PMF.tsum_coe]

lemma tsum_lenMass_eq_one (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ) :
    (∑' c : (BinVec (n / 2) × ℕ × ℕ),
        lenMass (δ := δ) cfd c.1 c.2.1 c.2.2) = 1 := by
  have : (∑' c : (BinVec (n / 2) × ℕ × ℕ),
        lenMass (δ := δ) cfd c.1 c.2.1 c.2.2)
      = ∑' c : (BinVec (n / 2) × ℕ × ℕ), lenE.toPMF c := by
    apply tsum_congr; intro c
    rw [lenE_eq_lenMass cfd lenE]
  rw [this, PMF.tsum_coe]

lemma summable_toReal_of_le_partMass (cfd : CoinFlipDist n Se)
    (partE : Workspace.Types.PartialDeletionProcess.PartialDeletionProcess n Se δ)
    (F : (BinVec (n / 2) × Trace n × Trace n) → ENNReal)
    (hF : ∀ p, F p ≤ partMass (δ := δ) cfd p.1 p.2.1 p.2.2) :
    Summable (fun p => (F p).toReal) := by
  apply ENNReal.summable_toReal
  have hle : (∑' p, F p) ≤ ∑' p : (BinVec (n / 2) × Trace n × Trace n),
      partMass (δ := δ) cfd p.1 p.2.1 p.2.2 :=
    ENNReal.tsum_le_tsum hF
  rw [tsum_partMass_eq_one cfd partE] at hle
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

lemma summable_toReal_of_le_lenMass (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (F : (BinVec (n / 2) × ℕ × ℕ) → ENNReal)
    (hF : ∀ c, F c ≤ lenMass (δ := δ) cfd c.1 c.2.1 c.2.2) :
    Summable (fun c => (F c).toReal) := by
  apply ENNReal.summable_toReal
  have hle : (∑' c, F c) ≤ ∑' c : (BinVec (n / 2) × ℕ × ℕ),
      lenMass (δ := δ) cfd c.1 c.2.1 c.2.2 :=
    ENNReal.tsum_le_tsum hF
  rw [tsum_lenMass_eq_one cfd lenE] at hle
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hle

/-! ## Lengths-side analogues. -/

lemma lenMass_ne_top (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (m : BinVec (n / 2)) (zM zP : ℕ) :
    lenMass (δ := δ) cfd m zM zP ≠ ⊤ := by
  rw [← lenE_eq_lenMass cfd lenE]
  exact PMF.apply_ne_top lenE.toPMF (m, zM, zP)

lemma goodLenMass_le_lenMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zM zP : ℕ) :
    goodLenMass (δ := δ) cfd m zM zP ≤ lenMass (δ := δ) cfd m zM zP := by
  rw [lenMass_eq_good_add_bad]; exact le_self_add

lemma badLenMass_le_lenMass (cfd : CoinFlipDist n Se) (m : BinVec (n / 2))
    (zM zP : ℕ) :
    badLenMass (δ := δ) cfd m zM zP ≤ lenMass (δ := δ) cfd m zM zP := by
  rw [lenMass_eq_good_add_bad]; exact le_add_self

lemma goodLenMass_ne_top (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (m : BinVec (n / 2)) (zM zP : ℕ) :
    goodLenMass (δ := δ) cfd m zM zP ≠ ⊤ :=
  ne_top_of_le_ne_top (lenMass_ne_top cfd lenE m zM zP) (goodLenMass_le_lenMass cfd m zM zP)

lemma badLenMass_ne_top (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (m : BinVec (n / 2)) (zM zP : ℕ) :
    badLenMass (δ := δ) cfd m zM zP ≠ ⊤ :=
  ne_top_of_le_ne_top (lenMass_ne_top cfd lenE m zM zP) (badLenMass_le_lenMass cfd m zM zP)

/-- Real-valued lengths decomposition. -/
lemma len_toReal_split (cfd : CoinFlipDist n Se)
    (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
    (m : BinVec (n / 2)) (zM zP : ℕ) :
    (lenE.toPMF (m, zM, zP)).toReal
      = (goodLenMass (δ := δ) cfd m zM zP).toReal + (badLenMass (δ := δ) cfd m zM zP).toReal := by
  rw [lenE_eq_lenMass cfd lenE, lenMass_eq_good_add_bad,
    ENNReal.toReal_add (goodLenMass_ne_top cfd lenE m zM zP) (badLenMass_ne_top cfd lenE m zM zP)]

end TVPartialBoundedAssembly
