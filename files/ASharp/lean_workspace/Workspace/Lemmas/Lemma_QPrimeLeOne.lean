import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Workspace.Lemmas.Lemma_QPrimeLePDivSix

open Real

namespace Workspace.Lemmas.QPrimeLeOne

/-- **Theorem: q'_le_one_axiom_final**
Under the same conditions as q'_le_p_div_6, we have q' ≤ 1.

**Proof**: Since p ≤ 1 and q' ≤ p/6 (from q'_le_p_div_6), we have q' ≤ p/6 ≤ 1/6 ≤ 1.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 1, Proof of Main Theorem)
-/
theorem q_prime_le_one (p c_sel : ℝ) (t : ℕ) (s : ℕ) (q q' : ℝ)
    (hp_pos : 0 < p) (hp_le1 : p ≤ 1)
    (hc_sel : 0 < c_sel) (hc_sel_le : c_sel ≤ 100 * log 2)
    (ht : 2 ≤ t) (hs : s = Nat.ceil (log (2 * t) / log 2))
    (hq : q = (c_sel / 100000) * p / log t)
    (hq' : q' = 16 * s * q) :
    q' ≤ 1 := by
  have h := Workspace.Lemmas.QPrimeLePDivSix.q_prime_le_p_div_6 p c_sel t s q q' hp_pos hp_le1 hc_sel hc_sel_le ht hs hq hq'
  calc q'
      ≤ p / 6 := h
    _ ≤ 1 / 6 := by
        apply div_le_div_of_nonneg_right hp_le1
        norm_num
    _ ≤ 1 := by norm_num

end Workspace.Lemmas.QPrimeLeOne
