import Mathlib.Combinatorics.SimpleGraph.Circulant
import Workspace.Types.Core

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- A hole list enumerates its support as the corresponding Mathlib cycle graph. -/
theorem HoleSupportCycleIso
    {V : Type*} [DecidableEq V] (K : SimpleGraph V) (c : List V)
    (hc : IsHoleList K c) :
    ∃ e : SimpleGraph.cycleGraph c.length ≃g K.induce (c.toFinset : Set V),
      ∀ i : Fin c.length, (e i : V) = c.get i := by
  rcases hc with ⟨hlen, hnodup, hadj⟩
  let f : Fin c.length ≃ {x : V // x ∈ (c.toFinset : Set V)} :=
    { toFun := fun i => ⟨c.get i, by simp⟩
      invFun := fun x =>
        ⟨c.idxOf x.1, List.idxOf_lt_length_iff.mpr (by simpa using x.2)⟩
      left_inv := fun i => by
        apply Fin.ext
        simp [hnodup]
      right_inv := fun x => by
        apply Subtype.ext
        simp }
  have hn0 : c.length ≠ 0 := by omega
  letI : NeZero c.length := ⟨hn0⟩
  have hone : 1 % c.length = 1 := Nat.mod_eq_of_lt (by omega)
  have hsucc (i j : Fin c.length) :
      j.val = (i.val + 1) % c.length ↔ j = i + 1 := by
    constructor
    · intro h
      apply Fin.ext
      simpa [Fin.val_add, Fin.val_one', hone] using h
    · intro h
      have hv := congrArg Fin.val h
      simpa [Fin.val_add, Fin.val_one', hone] using hv
  let e : SimpleGraph.cycleGraph c.length ≃g K.induce (c.toFinset : Set V) :=
    { toEquiv := f
      map_rel_iff' := by
        intro i j
        change K.Adj (c.get i) (c.get j) ↔
          (SimpleGraph.cycleGraph c.length).Adj i j
        calc
          K.Adj (c.get i) (c.get j) ↔
              (j.val = (i.val + 1) % c.length ∨
                i.val = (j.val + 1) % c.length) :=
            hadj i j i.isLt j.isLt
          _ ↔ (j = i + 1 ∨ i = j + 1) := by
            rw [hsucc i j, hsucc j i]
          _ ↔ (SimpleGraph.cycleGraph c.length).Adj i j := by
            rw [SimpleGraph.cycleGraph_adj']
            constructor
            · rintro (hji | hij)
              · right
                have hs : j - i = (1 : Fin c.length) :=
                  sub_eq_iff_eq_add'.2 (by simpa [add_comm] using hji)
                simpa [Fin.ext_iff, Fin.val_one', hone] using hs
              · left
                have hs : i - j = (1 : Fin c.length) :=
                  sub_eq_iff_eq_add'.2 (by simpa [add_comm] using hij)
                simpa [Fin.ext_iff, Fin.val_one', hone] using hs
            · rintro (hij | hji)
              · right
                have hs : i - j = (1 : Fin c.length) := by
                  apply Fin.ext
                  simpa [Fin.val_one', hone] using hij
                have heq := sub_eq_iff_eq_add'.1 hs
                simpa [add_comm] using heq
              · left
                have hs : j - i = (1 : Fin c.length) := by
                  apply Fin.ext
                  simpa [Fin.val_one', hone] using hji
                have heq := sub_eq_iff_eq_add'.1 hs
                simpa [add_comm] using heq }
  refine ⟨e, ?_⟩
  intro i
  rfl

end Workspace.ProofLemmas
