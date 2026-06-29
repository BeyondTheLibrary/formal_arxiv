import Mathlib

namespace Workspace.Types.BinVec

/-- A length-`n` binary vector, represented as a function from `Fin n` to `Bool`.
    This is the output of the coin-flip stage of trace generation: the underlying
    binary sample before any deletions are applied. -/
structure BinVec (n : ℕ) where
  /-- The `i`-th bit of the vector. -/
  bit : Fin n → Bool

/-- Equivalence between `BinVec n` and `Fin n → Bool`. -/
def equivFun {n : ℕ} : BinVec n ≃ (Fin n → Bool) where
  toFun b := b.bit
  invFun f := ⟨f⟩
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

instance instDecidableEq {n : ℕ} : DecidableEq (BinVec n) :=
  fun a b => decidable_of_iff (a.bit = b.bit) (by
    constructor
    · intro h; cases a; cases b; simp_all
    · intro h; rw [h])

instance instFintype {n : ℕ} : Fintype (BinVec n) :=
  Fintype.ofEquiv (Fin n → Bool) equivFun.symm

end Workspace.Types.BinVec
