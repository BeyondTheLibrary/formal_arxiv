import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.LInfDistance
import Workspace.ProofLemmas.SublemmaCentralBinomialBounds
import Workspace.ProofLemmas.OddNConstructionArith

/-!
# L∞ separation for ALL odd `n` (GREEN-SAFE generalisation)

`Workspace.ProofLemmas.SublemmaLInfSeparation` proves the L∞-separation lower
bound under the gate `n % 8 = 1`.  That gate is a Lean integer-division
artifact: the paper construction (`deletion.tex` 268-271) is for **all odd `n`**.

This file proves `LInfSeparation_odd`, the SAME conclusion with the SAME constant
`c_inf = 1/(16 · e² · √(2π))`, under the faithful hypothesis `n % 2 = 1`.

## Why the gate appears, and how we remove it

The separation argument evaluates the even-witness `Se` at an even index `k*`,
where `Se.p k* = c' · √n · C(n, k*) · 2^(-n)` and `So.p k* = 0`, then lower-bounds
the central binomial coefficient.  It needs `k* % 2 = 0`.

* `n ≡ 1 (mod 4)`: the central index `k* = (n-1)/2 = m/2` (with `n = m+1`) is
  **even** (`OddNConstructionArith.centralIndex_even_of_mod4_eq_one`), so the
  even witness fires there — exactly the old proof.

* `n ≡ 3 (mod 4)`: the central index `(n-1)/2 = m/2` is **odd**
  (`OddNConstructionArith.centralIndex_odd_of_mod4_eq_three`).  We instead use the
  ADJACENT even index `k* = m/2 + 1`
  (`OddNConstructionArith.centralIndex_succ_even_of_mod4_eq_three`, valid in
  `Fin (m+1)` by `centralIndex_succ_lt`).  Crucially, for odd `n = m+1`,
  `C(m+1, m/2+1) = C(m+1, m/2)` by binomial symmetry
  (`m/2 + 1 = (m+1) - m/2`), so the witness VALUE at `m/2+1` equals the value at
  the centre — **no rescaling of the constant**.  The same central-binomial
  lower bound `C(m+1, m/2) · 2^(-(m+1)) ≥ 1/(2√n)` then closes both branches
  identically.

So the conclusion's constant is IDENTICAL to `SublemmaLInfSeparation`; only the
index choice differs between the two `n % 4` branches.
-/

open Workspace.Types.ProbVec
open Workspace.Types.LInfDistance

namespace Workspace.ProofLemmas

theorem LInfSeparation_odd :
    ∀ n : ℕ, 1 ≤ n → n % 2 = 1 →
      ∀ Se So : Workspace.Types.ProbVec.ProbVec n,
        (∀ i : Fin n, Se.p i =
          (if (i.val) % 2 = 0
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        (∀ i : Fin n, So.p i =
          (if (i.val) % 2 = 1
           then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0)) →
        Workspace.Types.LInfDistance.LInfDistance Se So ≥
          (1 / (16 * Real.exp 2 * Real.sqrt (2 * Real.pi))) := by
  intro n hn1 hodd Se So hSe hSo
  -- Write n = m + 1 (m even, since n odd) so LInfDistance unfolds.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hm2 : m % 2 = 0 := by omega
  -- Choose the even, nonzero witness index `k` depending on n % 4.
  -- For n ≡ 1 (mod 4): k = m/2 (central, even).
  -- For n ≡ 3 (mod 4): k = m/2 + 1 (adjacent, even), with C(n, m/2+1) = C(n, m/2).
  -- In BOTH cases the witness value equals c' * √n * C(n, m/2) * 2^(-n).
  -- We package this as: there is an even k whose choose value equals C(m+1, m/2).
  obtain ⟨k, hk_even, hk_choose⟩ :
      ∃ k : Fin (m + 1), (k.val) % 2 = 0 ∧
        (Nat.choose (m + 1) k.val) = Nat.choose (m + 1) (m / 2) := by
    rcases (by omega : (m + 1) % 4 = 1 ∨ (m + 1) % 4 = 3) with h4 | h4
    · -- n ≡ 1 (mod 4): central index m/2 is even.
      refine ⟨⟨m / 2, by omega⟩, ?_, rfl⟩
      have := Workspace.ProofLemmas.OddNConstructionArith.centralIndex_even_of_mod4_eq_one (m + 1) h4
      simpa using this
    · -- n ≡ 3 (mod 4): adjacent index m/2 + 1 is even, and C(n, m/2+1) = C(n, m/2).
      have hlt : m / 2 + 1 < m + 1 := by omega
      refine ⟨⟨m / 2 + 1, hlt⟩, ?_, ?_⟩
      · have := Workspace.ProofLemmas.OddNConstructionArith.centralIndex_succ_even_of_mod4_eq_three (m + 1) h4
        simpa using this
      · -- C(m+1, m/2+1) = C(m+1, m/2) since (m/2+1) = (m+1) - (m/2) (m even).
        show Nat.choose (m + 1) (m / 2 + 1) = Nat.choose (m + 1) (m / 2)
        have hsymm : Nat.choose (m + 1) (m / 2 + 1) = Nat.choose (m + 1) (m + 1 - (m / 2 + 1)) :=
          (Nat.choose_symm (by omega)).symm
        rw [hsymm]
        congr 1
        omega
  -- Abbreviations and positivity (verbatim from SublemmaLInfSeparation).
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  have he2 : Real.exp 2 > 0 := Real.exp_pos 2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsqrt2pi : Real.sqrt (2 * Real.pi) > 0 := Real.sqrt_pos.mpr h2pi
  have hc'_pos : c' > 0 := by
    show 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) > 0
    have : 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) > 0 := by positivity
    positivity
  have hncast : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hsqrtn : Real.sqrt ((m + 1 : ℕ) : ℝ) > 0 := Real.sqrt_pos.mpr hncast
  -- Witness values at k: Se.p k = c' √n C(n,k) 2^(-n), So.p k = 0.
  have hSek : Se.p k =
      c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) k.val : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    rw [hSe k]
    simp [hk_even, hc'_def]
  have hSok : So.p k = 0 := by
    rw [hSo k]
    simp [hk_even]
  -- |Se.p k - So.p k|, then rewrite C(n,k) = C(n, m/2) via hk_choose.
  have habs : |Se.p k - So.p k| =
      c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) (m / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    rw [hSek, hSok, sub_zero]
    rw [show (Nat.choose (m + 1) k.val : ℝ) = (Nat.choose (m + 1) (m / 2) : ℝ) by
          exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hk_choose]
    apply abs_of_nonneg
    have hC : (0 : ℝ) ≤ (Nat.choose (m + 1) (m / 2) : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2pow : (0 : ℝ) ≤ (2 ^ (m + 1) : ℝ)⁻¹ := by positivity
    have hsqrtn' : (0 : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
    have hc'nn : (0 : ℝ) ≤ c' := le_of_lt hc'_pos
    positivity
  -- LInfDistance ≥ |Se.p k - So.p k|.
  have hLInf_eq : Workspace.Types.LInfDistance.LInfDistance Se So =
      (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
        (fun i => |Se.p i - So.p i|) := rfl
  have hLInf_ge : |Se.p k - So.p k| ≤ Workspace.Types.LInfDistance.LInfDistance Se So := by
    rw [hLInf_eq]
    exact Finset.le_sup' (f := fun i => |Se.p i - So.p i|) (Finset.mem_univ k)
  refine le_trans ?_ hLInf_ge
  rw [habs]
  -- c_inf = c'/4.
  have hcInf : (1 / (16 * Real.exp 2 * Real.sqrt (2 * Real.pi))) = c' / 4 := by
    show (1 / (16 * Real.exp 2 * Real.sqrt (2 * Real.pi))) =
         (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) / 4
    field_simp
    ring
  rw [hcInf]
  -- (n+1)/2 = m/2 since m even.
  have hk_eq_floor : (m / 2) = (m + 1) / 2 := by omega
  -- Central binomial lower bound (part b), at the central index (m+1)/2 = m/2.
  have hCB : (1 : ℝ) / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤
      (Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹ := by
    have hCBfull := SublemmaCentralBinomialBounds (m + 1) hn1
    have hb := hCBfull.2
    simpa using hb
  -- Rewrite goal's C(n, m/2) into C(n, (m+1)/2).
  rw [show c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) (m / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) =
       c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) from by
       rw [hk_eq_floor]]
  -- √n · (C · 2^(-n)) ≥ 1/2.
  have hsqrtn_nn : (0 : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsqrtn_ne : Real.sqrt ((m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hsqrtn
  have hCB' : (1 : ℝ) / 2 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) *
      ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    have h := mul_le_mul_of_nonneg_left hCB hsqrtn_nn
    have heq : Real.sqrt ((m + 1 : ℕ) : ℝ) * (1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))) = 1/2 := by
      field_simp
    linarith [heq ▸ h]
  -- c' · 1/2 ≤ witness value.
  have hmain : c' * (1/2) ≤ c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
      ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    have h := mul_le_mul_of_nonneg_left hCB' (le_of_lt hc'_pos)
    have hassoc : c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) =
        c' * (Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹)) := by ring
    rw [hassoc]
    exact h
  -- c'/4 ≤ c' · 1/2.
  have hquarter_half : c' / 4 ≤ c' * (1/2) := by
    have : c' / 4 = c' * (1/4) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by norm_num : (1:ℝ)/4 ≤ 1/2) (le_of_lt hc'_pos)
  linarith

end Workspace.ProofLemmas
