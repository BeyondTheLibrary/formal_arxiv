import Workspace.ProofLemmas.Thm232Claim3C2
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleBasics

/-!
# Two facts about the set `A₀` of 23.2

PAPER (23.2, printed p. 139): *"Let `A₀ = V(C) \ {z, x₀, x₁}`."*

`A₀` is the rim with three consecutive vertices deleted, so it is the vertex set of an arc:
this gives its connectedness, used to build the path of claim (5).  The second fact is the
one silently used when 2.11 is applied there: no rim vertex other than `z` is adjacent to
both `x₀` and `x₁`, because the rim has length at least six.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232RimFacts

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.Thm232Claim3C2

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- No rim vertex other than `z` has both `x₀` and `x₁` as neighbours: on a hole of length at
least six, the two neighbours of `x₀` are `z` and the vertex at cyclic position `-1`, while
those of `x₁` are `z` and the vertex at cyclic position `3`. -/
theorem not_complete_to_pair {C : List V} (hC : IsHoleList G C) (hn6 : 6 ≤ C.length)
    {k : ℕ} {x₀ z x₁ : V} (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (v : V) (hv : v ∈ C) (hvz : v ≠ z) :
    ¬ (G.Adj v x₀ ∧ G.Adj v x₁) := by
  rintro ⟨ha0, ha1⟩
  have hD : IsHoleList G (C.rotate k) := HoleBasics.isHoleList_rotate hC k
  have hlen : (C.rotate k).length = C.length := by simp
  have hvD : v ∈ C.rotate k := List.mem_rotate.mpr hv
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hvD
  have e0 : (C.rotate k)[0]'(by omega) = x₀ :=
    (hpre1.getElem (show 0 < ([x₀, z, x₁] : List V).length by simp)).symm
  have e1 : (C.rotate k)[1]'(by omega) = z :=
    (hpre1.getElem (show 1 < ([x₀, z, x₁] : List V).length by simp)).symm
  have e2 : (C.rotate k)[2]'(by omega) = x₁ :=
    (hpre1.getElem (show 2 < ([x₀, z, x₁] : List V).length by simp)).symm
  have hi1 : i ≠ 1 := by
    intro he
    exact hvz (hiv.symm.trans ((hD.2.1.getElem_inj_iff.mpr he).trans e1))
  have h0 := WheelParity.hole_adj_index hD hi (show 0 < (C.rotate k).length by omega)
    (by rw [hiv, e0]; exact ha0)
  have h1 := WheelParity.hole_adj_index hD hi (show 2 < (C.rotate k).length by omega)
    (by rw [hiv, e2]; exact ha1)
  omega

/-- The set `A₀ = V(C) \ {z, x₀, x₁}` is the vertex set of the arc of `C` running from the
successor of `x₁` to the predecessor of `x₀`, hence is connected. -/
theorem a0_connected {C : List V} (hC : IsHoleList G C) (hn6 : 6 ≤ C.length)
    {k : ℕ} {x₀ z x₁ : V} (hpre1 : [x₀, z, x₁] <+: C.rotate k) :
    ConnectedSet G ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)) := by
  have hn : 0 < C.length := by omega
  have p0 : C[(k + 0) % C.length]'(Nat.mod_lt _ hn) = x₀ :=
    (prefix_getElem hn hpre1 (i := 0) (j := k + 0) (by simp) rfl).symm
  have p1 : C[(k + 1) % C.length]'(Nat.mod_lt _ hn) = z :=
    (prefix_getElem hn hpre1 (i := 1) (j := k + 1) (by simp) rfl).symm
  have p2 : C[(k + 2) % C.length]'(Nat.mod_lt _ hn) = x₁ :=
    (prefix_getElem hn hpre1 (i := 2) (j := k + 2) (by simp) rfl).symm
  have harc : IsPathList G ((C.rotate (k + 3)).take (C.length - 3)) :=
    WheelParity.isPathList_rotate_take hC (by omega) (by omega)
  have hset : {v : V | v ∈ (C.rotate (k + 3)).take (C.length - 3)}
      = {v : V | v ∈ C} \ ({z, x₀, x₁} : Set V) := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or]
    constructor
    · intro hv
      obtain ⟨t, ht, rfl⟩ := (mem_rotate_take hn (by omega)).mp hv
      have hkey : k + 3 + t = k + (3 + t) := by omega
      rw [hkey]
      refine ⟨List.getElem_mem _, ?_, ?_, ?_⟩
      · rw [← p1]
        exact fun h => pos_ne hC.2.1 hn k (3 + t) 1
          (by rw [mod_le_self hn (by omega), mod_le_self hn (by omega)];
              split_ifs <;> omega) h
      · rw [← p0]
        exact fun h => pos_ne hC.2.1 hn k (3 + t) 0
          (by rw [mod_le_self hn (by omega), mod_le_self hn (by omega)];
              split_ifs <;> omega) h
      · rw [← p2]
        exact fun h => pos_ne hC.2.1 hn k (3 + t) 2
          (by rw [mod_le_self hn (by omega), mod_le_self hn (by omega)];
              split_ifs <;> omega) h
    · rintro ⟨hvC, hvz, hv0, hv1⟩
      obtain ⟨m, hm, hmv⟩ := List.getElem_of_mem hvC
      obtain ⟨t, ht, hkt⟩ := OddWheelParityFacts.exists_offset (C := C) hn k m
      have hvpos : C[(k + t) % C.length]'(Nat.mod_lt _ hn) = v := by
        have hidx : (k + t) % C.length = m := hkt.trans (Nat.mod_eq_of_lt hm)
        exact (hC.2.1.getElem_inj_iff.mpr hidx).trans hmv
      have ht0 : t ≠ 0 := by rintro rfl; exact hv0 (hvpos.symm.trans p0)
      have ht1 : t ≠ 1 := by rintro rfl; exact hvz (hvpos.symm.trans p1)
      have ht2 : t ≠ 2 := by rintro rfl; exact hv1 (hvpos.symm.trans p2)
      refine (mem_rotate_take hn (by omega)).mpr ⟨t - 3, by omega, ?_⟩
      exact hvpos.symm.trans (hC.2.1.getElem_inj_iff.mpr
        (congrArg (fun a => a % C.length) (show k + t = k + 3 + (t - 3) by omega)))
  rw [← hset]
  exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList harc

end Workspace.ProofLemmas.Thm232RimFacts
