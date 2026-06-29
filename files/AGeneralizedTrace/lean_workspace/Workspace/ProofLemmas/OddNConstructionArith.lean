import Mathlib

/-!
# Odd-`n` construction arithmetic (GREEN-SAFE foundation)

This file proves, **sorry-free**, the foundational integer-arithmetic and parity
facts needed to rework the witness construction from the current
`n % 8 = 1` gate to **all odd `n`**, matching the paper
(`deletion.tex` 268-271: "for the sake of symmetry, we consider `n` odd").

It is a NEW, self-contained file: it imports only `Mathlib` and edits nothing
else, so the build stays green.  Two mod-8 gates currently enter the proof:

* `SublemmaLInfSeparation` needs the central index `(n-1)/2` to be **even** so
  that the `if i % 2 = 0` even-witness branch fires there.  Under `n % 8 = 1`,
  `(n-1)/2 = 4q` is even.  For general odd `n` the parity of `(n-1)/2`
  alternates with `n % 4`: even iff `n ≡ 1 (mod 4)`, odd iff `n ≡ 3 (mod 4)`.
  Lemmas `centralIndex_even_of_mod4_eq_one` / `centralIndex_odd_of_mod4_eq_three`
  give SublemmaLInfSeparation the correct-parity nonzero index in each case.

* `PartialDominatesHCore` gates on `2 * (n / 4) = n / 2`, which holds for
  `n % 4 ∈ {0, 1}` but FAILS for `n ≡ 3 (mod 4)` (e.g. `n = 7`:
  `2 * (7/4) = 2 ≠ 3 = 7/2`).  Lemmas below characterise the slice sizes
  `n/4, n/2, 3*(n/4), 2*(n/4)` for every odd residue `n % 8 ∈ {1,3,5,7}` and
  pin the exact off-by-one in the `n ≡ 3 (mod 4)` middle window.
-/

namespace Workspace.ProofLemmas.OddNConstructionArith

/-! ## 1. Central-index parity for all odd `n`

The central index used by `SublemmaLInfSeparation` is `(n-1)/2`.  For odd `n`
this equals `m/2` where `n = m + 1` (`m` even).  Its parity is governed by
`n % 4`. -/

/-- For `n ≡ 1 (mod 4)`, the central index `(n-1)/2` is **even**.
This is the all-odd-`n` generalisation of the `n % 8 = 1` parity fact used in
`SublemmaLInfSeparation` (which currently derives `(m/2) % 2 = 0` from
`m % 8 = 0`). -/
theorem centralIndex_even_of_mod4_eq_one (n : ℕ) (h : n % 4 = 1) :
    ((n - 1) / 2) % 2 = 0 := by
  omega

/-- For `n ≡ 3 (mod 4)`, the central index `(n-1)/2` is **odd**.  In this case
`SublemmaLInfSeparation` must pick its nonzero witness index from the ODD
(`So`) branch at the centre, or pick an even index adjacent to it. -/
theorem centralIndex_odd_of_mod4_eq_three (n : ℕ) (h : n % 4 = 3) :
    ((n - 1) / 2) % 2 = 1 := by
  omega

/-- Unified statement: for odd `n`, the central index parity equals
`(n % 4 = 1 → even) ∧ (n % 4 = 3 → odd)`. -/
theorem centralIndex_parity_odd (n : ℕ) (hodd : n % 2 = 1) :
    (n % 4 = 1 → ((n - 1) / 2) % 2 = 0) ∧
    (n % 4 = 3 → ((n - 1) / 2) % 2 = 1) := by
  constructor <;> intro h <;> omega

/-- The central index lies strictly inside `[0, n)` for `n ≥ 1` (so it is a valid
`Fin n` coordinate). -/
theorem centralIndex_lt (n : ℕ) (hn : 1 ≤ n) : (n - 1) / 2 < n := by
  omega

/-- For odd `n`, `(n-1)/2 = (n-1)/2` agrees with the `m/2` form
(`n = m+1`): the central index in `Fin n` used by the separation lemma. -/
theorem centralIndex_eq_pred_div_two (n : ℕ) : (n - 1) / 2 = (n - 1) / 2 := rfl

/-! ### Adjacent-index fallback for `n ≡ 3 (mod 4)`

When `(n-1)/2` is odd, the even-witness `Se` is zero there.  But the index
`(n-1)/2 - 1` (one below the centre) IS even and is a valid `Fin n` coordinate
for `n ≥ 3`, and `(n-1)/2 + 1` IS even and valid for odd `n ≥ 3`.  Either gives
`SublemmaLInfSeparation` a nonzero even-witness coordinate near the binomial
mode (so the central-binomial bound still applies up to a `C(n,·)/C(n, n/2)`
ratio that is `Θ(1)`). -/

/-- For `n ≡ 3 (mod 4)` (hence `(n-1)/2` odd), the index just below the centre
is even. -/
theorem centralIndex_pred_even_of_mod4_eq_three (n : ℕ) (h : n % 4 = 3) :
    ((n - 1) / 2 - 1) % 2 = 0 := by
  omega

/-- For `n ≡ 3 (mod 4)`, the index just above the centre is even. -/
theorem centralIndex_succ_even_of_mod4_eq_three (n : ℕ) (h : n % 4 = 3) :
    ((n - 1) / 2 + 1) % 2 = 0 := by
  omega

/-- The below-centre even index is `< n` for `n ≥ 1`. -/
theorem centralIndex_pred_lt (n : ℕ) (hn : 1 ≤ n) : (n - 1) / 2 - 1 < n := by
  omega

/-- The above-centre even index is `< n` for odd `n` (`n = 2t+1`, centre `= t`,
`t+1 ≤ 2t < n` once `t ≥ 1`, i.e. `n ≥ 3`). -/
theorem centralIndex_succ_lt (n : ℕ) (hodd : n % 2 = 1) (hn : 3 ≤ n) :
    (n - 1) / 2 + 1 < n := by
  omega

/-! ## 2. Middle-window slicing for all odd `n`

The construction slices `[n]` into prefix (length `n/4 + r`), middle
(length `n/2`), suffix (length `n - n/4 - n/2`).  We record the exact slice
relations per odd residue `n % 8 ∈ {1,3,5,7}`, and the `2*(n/4)` vs `n/2`
relationship that the `PartialDominatesHCore` gate depends on. -/

/-- **Slice covers `[n]`** for ALL odd `n`: prefix + middle + suffix lengths sum
to `n`.  This is just floor arithmetic and holds unconditionally (no gate). -/
theorem slice_covers (n : ℕ) :
    n / 4 + n / 2 + (n - n / 4 - n / 2) = n := by
  omega

/-- The `PartialDominatesHCore` gate `2 * (n / 4) = n / 2` holds **iff**
`n % 4 ∈ {0, 1}`.  For odd `n` this is exactly `n % 4 = 1`. -/
theorem gate_iff_mod4 (n : ℕ) : 2 * (n / 4) = n / 2 ↔ (n % 4 = 0 ∨ n % 4 = 1) := by
  omega

/-- For odd `n` the gate is exactly the `n ≡ 1 (mod 4)` case. -/
theorem gate_iff_mod4_odd (n : ℕ) (hodd : n % 2 = 1) :
    2 * (n / 4) = n / 2 ↔ n % 4 = 1 := by
  omega

/-- **The `n ≡ 3 (mod 4)` off-by-one (the key obstruction quantified).**
For `n ≡ 3 (mod 4)`, `2 * (n / 4) = n / 2 - 1`, i.e. the middle window
`r + {n/4+1, …, 3n/4}` is ONE SHORT of `n/2` slots when measured by the floor
`n/4`.  Equivalently `n / 2 = 2 * (n / 4) + 1`. -/
theorem gate_off_by_one_of_mod4_eq_three (n : ℕ) (h : n % 4 = 3) :
    n / 2 = 2 * (n / 4) + 1 := by
  omega

/-- Per-residue middle-window slice table for odd `n`.  Writing `n = 8q + s`
with `s ∈ {1,3,5,7}`:
* `s = 1`: `n/4 = 2q`,   `n/2 = 4q`,   `3n/4 = 6q`,   `2*(n/4) = 4q = n/2`.
* `s = 3`: `n/4 = 2q`,   `n/2 = 4q+1`, `3n/4 = 6q+2`, `2*(n/4) = 4q = n/2-1`.
* `s = 5`: `n/4 = 2q+1`, `n/2 = 4q+2`, `3n/4 = 6q+3`, `2*(n/4) = 4q+2 = n/2`.
* `s = 7`: `n/4 = 2q+3/... `  -- see exact statements below.
The four lemmas below state each residue's relations precisely. -/

theorem slice_mod8_eq_one (q : ℕ) :
    let n := 8 * q + 1
    n / 4 = 2 * q ∧ n / 2 = 4 * q ∧ 3 * (n / 4) = 6 * q ∧ 2 * (n / 4) = n / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem slice_mod8_eq_three (q : ℕ) :
    let n := 8 * q + 3
    n / 4 = 2 * q ∧ n / 2 = 4 * q + 1 ∧ 3 * (n / 4) = 6 * q ∧ 2 * (n / 4) = n / 2 - 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem slice_mod8_eq_five (q : ℕ) :
    let n := 8 * q + 5
    n / 4 = 2 * q + 1 ∧ n / 2 = 4 * q + 2 ∧ 3 * (n / 4) = 6 * q + 3 ∧ 2 * (n / 4) = n / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem slice_mod8_eq_seven (q : ℕ) :
    let n := 8 * q + 7
    n / 4 = 2 * q + 1 ∧ n / 2 = 4 * q + 3 ∧ 3 * (n / 4) = 6 * q + 3 ∧ 2 * (n / 4) = n / 2 - 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ### Prefix/middle/suffix length identities for all odd `n`

These hold unconditionally and feed the `K₁ + n/2 + K₃ = n` three-cut sum in
`PartialDominatesHCore.per_r_identity` (where `K₁ = (n/4 + r).toNat`,
`K₃ = n - (3*(n/4) + r).toNat`).  The crucial fact the current proof uses is
that the gate makes the `r`'s cancel; we record the gate-free and the
`n ≡ 3 (mod 4)` versions. -/

/-- Suffix length (`n - 3*(n/4)`) for all odd `n`: equals `n/4 + (n % 4)`.
For `n ≡ 1 (mod 4)` this is `n/4 + 1`; for `n ≡ 3 (mod 4)` it is `n/4 + 3`.
This is the "two extra slots" the suffix gains exactly when the middle window
loses one (the `gate_off_by_one` deficit), so prefix+middle+suffix still totals
`n`. -/
theorem suffix_length_odd (n : ℕ) (hodd : n % 2 = 1) :
    n - 3 * (n / 4) = n / 4 + n % 4 := by
  omega

/-- Three-cut consistency: for the GATE-satisfying case (`n ≡ 1 (mod 4)`),
`(n/4) + (n/2) + (n - 3*(n/4)) = n`, matching the current `hcore` cut sum
`K₁ + n/2 + K₃ = n` at `r = 0`. -/
theorem three_cut_gate (n : ℕ) (h : n % 4 = 1) :
    (n / 4) + (n / 2) + (n - 3 * (n / 4)) = n := by
  omega

/-- Three-cut consistency for the OFF-BY-ONE case (`n ≡ 3 (mod 4)`):
the cut sum STILL equals `n` (floor arithmetic), but now the middle window has
length `n/2 = 2*(n/4) + 1`, NOT `2*(n/4)`.  Concretely the slice is
prefix `n/4`, middle `2*(n/4) + 1`, suffix `n/4 + 2`.  The `+1` on the middle
and the `+2` (instead of `+1`) on the suffix are the quantified boundary shift. -/
theorem three_cut_off_by_one (n : ℕ) (h : n % 4 = 3) :
    (n / 4) + (2 * (n / 4) + 1) + (n / 4 + 2) = n ∧
    n / 2 = 2 * (n / 4) + 1 := by
  refine ⟨?_, ?_⟩ <;> omega

/-! ### Where the gate `2*(n/4) = n/2` is genuinely used (feasibility)

In `PartialDominatesHCore.per_r_identity`, the gate is used ONLY to prove the
integer bound `3*(n/4) + r ≤ n` (so the suffix cut start is in range) via
`3*(n/4)+r = (n/4+r) + 2*(n/4) ≤ n/2 + n/2 = n`.  Without the gate, for
`n ≡ 3 (mod 4)`, `2*(n/4) = n/2 - 1`, so `3*(n/4)+r ≤ n/2 + (n/2 - 1) = n - 1 < n`
— the bound is actually EASIER (strict), the suffix start stays in range with a
slot to spare.  The following lemma proves the in-range bound holds for ALL odd
`n` on the offset support `0 ≤ r + n/4 ≤ n/2`, NO gate needed — the gate was a
sufficient-but-not-necessary convenience. -/

theorem suffix_start_in_range_odd (n : ℕ) (hodd : n % 2 = 1) (r : ℤ)
    (hr0 : 0 ≤ r + (n / 4 : ℕ)) (hr2 : r + (n / 4 : ℕ) ≤ (n / 2 : ℕ)) :
    ((3 * (n / 4) : ℕ) : ℤ) + r ≤ (n : ℤ) := by
  have h1 : ((n / 4 : ℕ) : ℤ) + r ≤ (n / 2 : ℕ) := by linarith [hr2]
  -- 3*(n/4) + r = (n/4 + r) + 2*(n/4) ≤ n/2 + 2*(n/4) ≤ n  (since 2*(n/4) ≤ n/2 ≤ n - n/2)
  have hkey : 2 * (n / 4) ≤ n / 2 := by omega
  have hkeyZ : ((2 * (n / 4) : ℕ) : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by exact_mod_cast hkey
  have hn2 : ((n / 2 : ℕ) : ℤ) + ((n / 2 : ℕ) : ℤ) ≤ (n : ℤ) := by
    have : n / 2 + n / 2 ≤ n := by omega
    exact_mod_cast this
  have he : ((3 * (n / 4) : ℕ) : ℤ) + r = (((n / 4 : ℕ) : ℤ) + r) + ((2 * (n / 4) : ℕ) : ℤ) := by
    push_cast; ring
  rw [he]; linarith

/-- The suffix-start bound is even STRICT (`< n`) for `n ≡ 3 (mod 4)` on the
offset support, confirming the off-by-one is absorbed with a slot to spare. -/
theorem suffix_start_strict_of_mod4_eq_three (n : ℕ) (h : n % 4 = 3) (r : ℤ)
    (hr0 : 0 ≤ r + (n / 4 : ℕ)) (hr2 : r + (n / 4 : ℕ) ≤ (n / 2 : ℕ)) :
    ((3 * (n / 4) : ℕ) : ℤ) + r < (n : ℤ) := by
  have h1 : ((n / 4 : ℕ) : ℤ) + r ≤ (n / 2 : ℕ) := by linarith [hr2]
  have hkey : 2 * (n / 4) = n / 2 - 1 := by omega
  have hkeyZ : ((2 * (n / 4) : ℕ) : ℤ) = ((n / 2 : ℕ) : ℤ) - 1 := by
    have hpos : 1 ≤ n / 2 := by omega
    omega
  have hn2 : ((n / 2 : ℕ) : ℤ) + ((n / 2 : ℕ) : ℤ) ≤ (n : ℤ) := by
    have : n / 2 + n / 2 ≤ n := by omega
    exact_mod_cast this
  have he : ((3 * (n / 4) : ℕ) : ℤ) + r = (((n / 4 : ℕ) : ℤ) + r) + ((2 * (n / 4) : ℕ) : ℤ) := by
    push_cast; ring
  rw [he, hkeyZ]; linarith

end Workspace.ProofLemmas.OddNConstructionArith
