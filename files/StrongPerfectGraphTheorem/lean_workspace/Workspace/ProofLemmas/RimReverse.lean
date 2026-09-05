import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.HoleBasics

/-!
# Reversing the rim

Several printed arguments of §16 run *"(by replacing `P` by its reverse if necessary) we may
assume that `i` is odd"* (16.1, printed p. 96).  The rim of a wheel is presented in these
modules by a base offset `k` and the position function `D t = C[(k+t) mod n]`, so *"replacing
`P` by its reverse"* means passing from `C` to `C.reverse` with a new base offset.

`exists_reverse_rim` performs that change of base once and for all: given a rim function `D`
for `C` at base `k`, and a distinguished forward offset `b`, it produces a rim function `D₂`
for `C.reverse` at some base `k₂` such that

    `t + u ≡ b (mod n)  →  D₂ t = D u`,

i.e. `D₂` runs backwards from the rim vertex `D b`.  In particular `D₂ 0 = D b`, `D₂ b = D 0`
and `D₂ t = D (b - t)` for `t ≤ b`.

Every other hypothesis the §16 modules impose on the rim is invariant under reversal —
`C.reverse.length = C.length`, `w ∈ C.reverse ↔ w ∈ C`, and `IsHoleList G C.reverse`
(`HoleBasics.isHoleList_reverse`) — so the transport is complete.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.RimReverse

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

private theorem getElem_congr_idx (q : List V) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- The arithmetic behind `exists_reverse_rim`: the position `A` of the reversed rim's `t`-th
vertex, measured along `C.reverse`, corresponds to the position `(k+u) mod n` along `C`. -/
private theorem index_key {n k b t u A : ℕ} (hn : 0 < n) (hAlt : A < n)
    (hA : A = ((k + b + 1) * (n - 1) + t) % n)
    (htu : (t + u) % n = b % n) :
    n - 1 - A = (k + u) % n := by
  have hAeq : A ≡ (k + b + 1) * (n - 1) + t [MOD n] := by
    unfold Nat.ModEq
    rw [Nat.mod_eq_of_lt hAlt]
    exact hA
  have hK2 : (k + b + 1) * (n - 1) + (k + b + 1) ≡ 0 [MOD n] := by
    have hsucc : n - 1 + 1 = n := by omega
    have he : (k + b + 1) * (n - 1) + (k + b + 1) = (k + b + 1) * n := by
      calc (k + b + 1) * (n - 1) + (k + b + 1) = (k + b + 1) * (n - 1 + 1) := by ring
        _ = (k + b + 1) * n := by rw [hsucc]
    unfold Nat.ModEq
    rw [he]
    simp
  have htu' : t + u ≡ b [MOD n] := htu
  have hz : (k + u) + (A + 1) ≡ 0 [MOD n] := by
    have step1 : (k + u) + (A + 1) + (k + b + 1)
        ≡ (k + u) + ((k + b + 1) * (n - 1) + t + 1) + (k + b + 1) [MOD n] :=
      Nat.ModEq.add_right (k + b + 1)
        (Nat.ModEq.add_left (k + u) (Nat.ModEq.add_right 1 hAeq))
    have step2 : (k + u) + ((k + b + 1) * (n - 1) + t + 1) + (k + b + 1)
        = (k + u + t + 1) + ((k + b + 1) * (n - 1) + (k + b + 1)) := by ring
    have step3 : (k + u + t + 1) + ((k + b + 1) * (n - 1) + (k + b + 1))
        ≡ (k + u + t + 1) + 0 [MOD n] := Nat.ModEq.add_left _ hK2
    have step4 : (k + u + t + 1) ≡ (k + b + 1) [MOD n] := by
      have h0 : (t + u) + (k + 1) ≡ b + (k + 1) [MOD n] := Nat.ModEq.add_right (k + 1) htu'
      calc k + u + t + 1 = (t + u) + (k + 1) := by ring
        _ ≡ b + (k + 1) [MOD n] := h0
        _ = k + b + 1 := by ring
    have final : (k + u) + (A + 1) + (k + b + 1) ≡ 0 + (k + b + 1) [MOD n] := by
      calc (k + u) + (A + 1) + (k + b + 1)
          ≡ (k + u) + ((k + b + 1) * (n - 1) + t + 1) + (k + b + 1) [MOD n] := step1
        _ = (k + u + t + 1) + ((k + b + 1) * (n - 1) + (k + b + 1)) := step2
        _ ≡ (k + u + t + 1) + 0 [MOD n] := step3
        _ = (k + u + t + 1) := by ring
        _ ≡ (k + b + 1) [MOD n] := step4
        _ = 0 + (k + b + 1) := by ring
    exact Nat.ModEq.add_right_cancel' (k + b + 1) final
  have hz2 : (n - 1 - A) + (A + 1) ≡ 0 [MOD n] := by
    have he : (n - 1 - A) + (A + 1) = n := by omega
    unfold Nat.ModEq
    rw [he]
    simp
  have hfin : (n - 1 - A) ≡ (k + u) [MOD n] :=
    Nat.ModEq.add_right_cancel' (A + 1) (hz2.trans hz.symm)
  unfold Nat.ModEq at hfin
  rwa [Nat.mod_eq_of_lt (show n - 1 - A < n by omega)] at hfin

/-- **The reversed rim.**  `D₂` runs backwards around `C` starting from the rim vertex `D b`. -/
theorem exists_reverse_rim {C : List V} {D : ℕ → V} {k n : ℕ}
    (hn : 0 < C.length) (hnn : C.length = n)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (b : ℕ) :
    ∃ (k₂ : ℕ) (D₂ : ℕ → V),
      (∀ t : ℕ, C.reverse[(k₂ + t) % C.reverse.length]? = some (D₂ t)) ∧
      (∀ t u : ℕ, (t + u) % n = b % n → D₂ t = D u) := by
  subst hnn
  have hrl : C.reverse.length = C.length := List.length_reverse
  have hn2 : 0 < C.reverse.length := by rw [hrl]; exact hn
  refine ⟨(k + b + 1) * (C.length - 1),
    fun t => C.reverse[((k + b + 1) * (C.length - 1) + t) % C.reverse.length]'(Nat.mod_lt _ hn2),
    fun t => List.getElem?_eq_getElem _, ?_⟩
  intro t u htu
  show C.reverse[((k + b + 1) * (C.length - 1) + t) % C.reverse.length]'
      (Nat.mod_lt _ hn2) = D u
  have hkey : C.length - 1 - (((k + b + 1) * (C.length - 1) + t) % C.reverse.length)
      = (k + u) % C.length := by
    rw [hrl]
    exact index_key hn (Nat.mod_lt _ hn) rfl htu
  rw [List.getElem_reverse]
  rw [getElem_congr_idx C hkey _ (Nat.mod_lt _ hn)]
  have hDu := hD u
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hDu
  exact Option.some_injective _ hDu

end Workspace.ProofLemmas.RimReverse
