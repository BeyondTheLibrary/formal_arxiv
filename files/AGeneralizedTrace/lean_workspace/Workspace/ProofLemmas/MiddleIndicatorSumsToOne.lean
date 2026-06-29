import Mathlib
import Workspace.Types.BinVec
import Workspace.Types.PartialDeletionProcess

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess

theorem MiddleIndicatorSumsToOne :
    ∀ {n : ℕ} (b : Workspace.Types.BinVec.BinVec n) (r : ℤ),
      0 ≤ r + (n / 4 : ℤ) →
      r + (n / 4 : ℤ) ≤ (n / 2 : ℤ) →
      (∑' m : Workspace.Types.BinVec.BinVec (n / 2),
        Workspace.Types.PartialDeletionProcess.middleIndicator n b m r) = 1 := by
  intro n b r hlo hhi
  -- Cast helpers between (n / k : ℕ) : ℤ and (n / k : ℤ)
  have hcast4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := by push_cast; ring
  have hcast2 : ((n / 2 : ℕ) : ℤ) = (n / 2 : ℤ) := by push_cast; ring
  -- Show the inner condition holds: for all j : Fin (n/2), 0 ≤ n/4+r+j < n.
  have hcond : ∀ j : Fin (n / 2),
      0 ≤ ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) ∧
        ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) < (n : ℤ) := by
    intro j
    have hjnn : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
    have hjlt : ((j : ℕ) : ℤ) < ((n / 2 : ℕ) : ℤ) := by exact_mod_cast j.is_lt
    have hsum : (n / 2 : ℤ) + (n / 2 : ℤ) ≤ (n : ℤ) := by
      have : n / 2 + n / 2 ≤ n := by omega
      exact_mod_cast this
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  -- Define m_star : BinVec (n/2)
  let mstar : BinVec (n / 2) :=
    { bit := fun j =>
        b.bit ⟨(((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat,
          by
            have hj := hcond j
            have hlt := hj.2
            have hnonneg := hj.1
            have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) := Int.toNat_of_nonneg hnonneg
            have : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ) < (n : ℤ) := by
              rw [h0]; exact hlt
            exact_mod_cast this⟩ }
  -- Show all other m give 0
  have key : ∀ m : BinVec (n / 2),
      m ≠ mstar → middleIndicator n b m r = 0 := by
    intro m hne
    unfold middleIndicator
    rw [dif_pos hcond]
    rw [if_neg]
    intro hall
    apply hne
    cases m with
    | mk mbit =>
      show ({ bit := mbit } : BinVec (n / 2)) = mstar
      have : mbit = mstar.bit := by
        funext j
        have h1 := hall j
        simp only at h1
        exact h1.symm
      rw [this]
  rw [tsum_eq_single mstar key]
  -- Now reduce middleIndicator n b mstar r to 1
  unfold middleIndicator
  rw [dif_pos hcond]
  rw [if_pos]
  intro j
  rfl
