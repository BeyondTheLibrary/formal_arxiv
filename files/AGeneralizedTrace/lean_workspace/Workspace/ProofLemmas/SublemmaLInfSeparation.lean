import Mathlib
import Workspace.Types.ProbVec
import Workspace.ProofLemmas.SublemmaCentralBinomialBounds
import Workspace.Types.LInfDistance
import Workspace.ProofLemmas.LInfSeparationOdd

open Workspace.Types.ProbVec
open Workspace.Types.LInfDistance

namespace Workspace.ProofLemmas

/--
Sublemma: L∞ separation of the witnesses.

Fix `c' := 1/(4 · e² · √(2π))` and `c_inf := c'/4 = 1/(16 · e² · √(2π))`.
For every `n ≥ 1` with `n` **odd** (`n % 2 = 1`), two probability vectors `Se, So`
that satisfy the per-index identities of `SublemmaWitnessConstruction`
(with `α = c' · √n`) have
`LInfDistance Se So ≥ c_inf`.

GREEN-SAFE generalisation (F90 / pad wave 1): the hypothesis was relaxed from
`n % 8 = 1` to the faithful `n % 2 = 1` (the paper construction
`deletion.tex:268-271` is for all odd `n`; the mod-8 gate was a Lean
integer-division artifact). The proof now delegates verbatim to
`Workspace.ProofLemmas.LInfSeparation_odd`, which has the IDENTICAL conclusion
and constant under `n % 2 = 1` (handling the `n ≡ 3 (mod 4)` central-index
parity via an adjacent even witness index, no constant rescaling).

The proof uses the central index `k* = (n-1)/2` (which is even because
`8 | n-1`), evaluating `|Se.p k* - So.p k*| = α · C(n, (n-1)/2) · 2^(-n)`,
and applies the central-binomial lower bound
`C(n, n/2) ≥ 2^n / (2 √n)` to conclude `|Se.p k* - So.p k*| ≥ c'/2 ≥ c_inf`.

This lemma is stated as a *transformation*: the per-index identities of
`SublemmaWitnessConstruction` are taken as hypotheses on `Se, So`, and the
conclusion is the L∞ lower bound. The construction lemma supplies witnesses
satisfying these identities; combining the two gives the existence of the
separated pair.
-/
theorem SublemmaLInfSeparation :
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
  -- GREEN-SAFE drop-in: delegate to the all-odd-n version, whose statement and
  -- constant are identical modulo the relaxed hypothesis `n % 2 = 1`.
  exact Workspace.ProofLemmas.LInfSeparation_odd

end Workspace.ProofLemmas

/-
ARCHIVED ORIGINAL PROOF (under the old `n % 8 = 1` gate), kept for provenance.
The live theorem above now delegates to `LInfSeparation_odd` (all odd `n`).

  intro n hn1 hn8 Se So hSe hSo
  -- We will pick the central index k* = (n-1)/2 and lower-bound the sup' by the value there.
  -- First convert n into the form (m+1) so LInfDistance unfolds.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  -- Now n = m+1, hn8 : (m+1) % 8 = 1, hn1 : 1 ≤ m+1.
  -- The central index in Fin (m+1) is m/2 (which equals ((m+1)-1)/2).
  set k : Fin (m + 1) := ⟨m / 2, by omega⟩ with hk_def
  -- k.val % 2 = 0 because m % 2 = 0 and m/2 has same parity as it does (we'll show m % 2 = 0
  -- from (m+1) % 8 = 1, hence m % 8 = 0, hence m % 2 = 0).
  -- Also m/2 even comes from m % 8 = 0, but we only need m/2 % 2 = 0 for the witness identities.
  have hm8 : m % 8 = 0 := by omega
  have hm2 : m % 2 = 0 := by omega
  -- We need k.val % 2 = 0. k.val = m/2. From m % 8 = 0, m = 8q, m/2 = 4q, even.
  have hk_even : (k.val) % 2 = 0 := by
    show (m / 2) % 2 = 0
    have hm8' : 8 ∣ m := Nat.dvd_of_mod_eq_zero hm8
    obtain ⟨q, rfl⟩ := hm8'
    -- m = 8 * q, m / 2 = 4 * q
    rw [show 8 * q / 2 = 4 * q from by omega]
    omega
  -- Set abbreviations.
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  -- Pre-positivity facts.
  have he2 : Real.exp 2 > 0 := Real.exp_pos 2
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsqrt2pi : Real.sqrt (2 * Real.pi) > 0 := Real.sqrt_pos.mpr h2pi
  have hc'_pos : c' > 0 := by
    show 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) > 0
    have : 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) > 0 := by positivity
    positivity
  -- n = m+1 ≥ 1, so √n > 0.
  have hncast : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
  have hsqrtn : Real.sqrt ((m + 1 : ℕ) : ℝ) > 0 := Real.sqrt_pos.mpr hncast
  -- Compute Se.p k = c' * √n * C(n, k) * 2^(-n)
  have hSek : Se.p k =
      c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) k.val : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    rw [hSe k]
    simp [hk_even, hc'_def]
  have hSok : So.p k = 0 := by
    rw [hSo k]
    simp [hk_even]
  -- The pointwise difference at index k.
  have habs : |Se.p k - So.p k| =
      c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) k.val : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    rw [hSek, hSok, sub_zero]
    apply abs_of_nonneg
    have hC : (0 : ℝ) ≤ (Nat.choose (m + 1) k.val : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2pow : (0 : ℝ) ≤ (2 ^ (m + 1) : ℝ)⁻¹ := by positivity
    have hsqrtn' : (0 : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
    have hc'nn : (0 : ℝ) ≤ c' := le_of_lt hc'_pos
    positivity
  -- LInfDistance Se So unfolds, since n = m+1.
  have hLInf_eq : Workspace.Types.LInfDistance.LInfDistance Se So =
      (Finset.univ : Finset (Fin (m + 1))).sup' Finset.univ_nonempty
        (fun i => |Se.p i - So.p i|) := rfl
  -- LInfDistance ≥ |Se.p k - So.p k|
  have hLInf_ge : |Se.p k - So.p k| ≤ Workspace.Types.LInfDistance.LInfDistance Se So := by
    rw [hLInf_eq]
    exact Finset.le_sup' (f := fun i => |Se.p i - So.p i|) (Finset.mem_univ k)
  -- Now we need |Se.p k - So.p k| ≥ 1/(16 e² √(2π)).
  -- |Se.p k - So.p k| = c' * √n * (C(n, k) * 2^(-n))
  -- Goal: this ≥ c'/4.
  -- Suffices: √n * C(n, k) * 2^(-n) ≥ 1/4.
  -- We use the central-binomial lower bound: C(n, ⌊n/2⌋) * 2^(-n) ≥ 1/(2 √n)
  -- => √n * C(n, ⌊n/2⌋) * 2^(-n) ≥ 1/2 ≥ 1/4.
  -- Note k.val = m/2 = ⌊n/2⌋ since n = m+1 odd (m even).
  -- Goal rewrite:
  refine le_trans ?_ hLInf_ge
  rw [habs]
  -- Need: 1/(16 e² √(2π)) ≤ c' * √n * (C(n, k) * 2^(-n))
  -- Note c'/4 = 1/(16 e² √(2π)).
  have hcInf : (1 / (16 * Real.exp 2 * Real.sqrt (2 * Real.pi))) = c' / 4 := by
    show (1 / (16 * Real.exp 2 * Real.sqrt (2 * Real.pi))) =
         (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) / 4
    field_simp
    ring
  rw [hcInf]
  -- Need c'/4 ≤ c' * √n * (C(n, k) * 2^(-n))
  -- Note k.val = m/2, and ⌊n/2⌋ = m/2 since n = m+1 with m even.
  have hk_eq_floor : k.val = (m + 1) / 2 := by
    show m / 2 = (m + 1) / 2
    omega
  -- Central binomial lower bound from SublemmaCentralBinomialBounds (part b).
  have hCB : (1 : ℝ) / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ)) ≤
      (Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹ := by
    have hCBfull := SublemmaCentralBinomialBounds (m + 1) hn1
    have hb : (Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹ ≥
        1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ)) := by
      have := hCBfull.2
      -- The conjunct's `Real.sqrt n` with `n = m + 1` reduces to `Real.sqrt ((m + 1 : ℕ) : ℝ)`.
      simpa using this
    exact hb
  -- Convert Se.p k uses k.val; rewrite the goal so we use the form (m+1)/2.
  have habs' : |Se.p k - So.p k| =
      c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    rw [habs, hk_eq_floor]
  -- Rewrite the goal in habs' form.
  rw [show c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) k.val : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) =
       c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) from by
       rw [hk_eq_floor]]
  -- Goal: c' / 4 ≤ c' * √n * (C * 2^(-n))
  -- Multiply hCB by √n: √n / (2 √n) = 1/2.
  have hsqrtn_nn : (0 : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hsqrtn_ne : Real.sqrt ((m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hsqrtn
  have hCB' : (1 : ℝ) / 2 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) *
      ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    have h := mul_le_mul_of_nonneg_left hCB hsqrtn_nn
    have heq : Real.sqrt ((m + 1 : ℕ) : ℝ) * (1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))) = 1/2 := by
      field_simp
    linarith [heq ▸ h]
  -- Multiply by c' > 0 and combine with c' * 1/2 ≥ c' / 4 (using c' ≥ 0).
  have hmain : c' * (1/2) ≤ c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
      ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) := by
    have h := mul_le_mul_of_nonneg_left hCB' (le_of_lt hc'_pos)
    have hassoc : c' * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹) =
        c' * (Real.sqrt ((m + 1 : ℕ) : ℝ) *
        ((Nat.choose (m + 1) ((m + 1) / 2) : ℝ) * (2 ^ (m + 1) : ℝ)⁻¹)) := by ring
    rw [hassoc]
    exact h
  -- c' / 4 ≤ c' * (1/2) since c' > 0.
  have hquarter_half : c' / 4 ≤ c' * (1/2) := by
    have : c' / 4 = c' * (1/4) := by ring
    rw [this]
    have : c' * (1/4) ≤ c' * (1/2) :=
      mul_le_mul_of_nonneg_left (by norm_num : (1:ℝ)/4 ≤ 1/2) (le_of_lt hc'_pos)
    exact this
  linarith
-/
