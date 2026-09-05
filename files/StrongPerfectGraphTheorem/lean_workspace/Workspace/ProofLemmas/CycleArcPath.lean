import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# Cyclically contiguous blocks of a cycle

Several proofs in the paper (15.3, 15.6, …) work with a **cycle** `C` of `G` that is *not*
assumed induced: it is given as the list of its vertices in cyclic order, cyclically
consecutive vertices are adjacent, and the only adjacency of `C` that is allowed to be a
chord is one designated pair `C[hh] C[jj]`.  ("Let `C` be induced except possibly for an
edge `p_h p_j`.")

Such a cycle is *not* an `IsHoleList`, so none of `HoleBasics` applies to it.  What every
one of those proofs needs is: *a cyclically contiguous block of `C` which misses at least
one end of the chord is an induced path of `G`.*  That is `arc_isPathFrom` below.

The block is presented as
`arc C x₀ a L = [cycAt C x₀ a, cycAt C x₀ (a+1), …, cycAt C x₀ (a+L-1)]`,
where `cycAt C x₀ t = C[t % C.length]` is the vertex of `C` at cyclic position `t`
(`x₀ : V` is an arbitrary default, only needed to avoid an `Inhabited` instance; it is
never returned when `C ≠ []`).  Working with `cycAt` at *unbounded* indices is what keeps
the wrap-around case (`p_{j+1}-⋯-p_n-p_1-⋯-p_{h-1}`) free of case analysis: it is the
single arc `arc C x₀ j (n-j+h-1)`.

Everything here is elementary and `sorry`-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CycleArcPath

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- The vertex of the cycle `C` at cyclic position `t`. -/
def cycAt (C : List V) (x₀ : V) (t : ℕ) : V := C.getD (t % C.length) x₀

/-- The cyclically contiguous block of `C` of length `L` starting at cyclic position `a`. -/
def arc (C : List V) (x₀ : V) (a L : ℕ) : List V :=
  (List.range L).map (fun t => cycAt C x₀ (a + t))

theorem arc_length (C : List V) (x₀ : V) (a L : ℕ) : (arc C x₀ a L).length = L := by
  simp [arc]

theorem arc_getElem (C : List V) (x₀ : V) (a L t : ℕ) (ht : t < (arc C x₀ a L).length) :
    (arc C x₀ a L)[t]'ht = cycAt C x₀ (a + t) := by
  simp [arc]

theorem mem_arc_iff (C : List V) (x₀ : V) (a L : ℕ) (x : V) :
    x ∈ arc C x₀ a L ↔ ∃ t, t < L ∧ x = cycAt C x₀ (a + t) := by
  simp only [arc, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

theorem cycAt_of_lt {C : List V} {x₀ : V} {t : ℕ} (ht : t < C.length) :
    cycAt C x₀ t = C[t]'ht := by
  rw [cycAt, Nat.mod_eq_of_lt ht, List.getD_eq_getElem C x₀ ht]

theorem cycAt_mod_lt {C : List V} {x₀ : V} (hpos : 0 < C.length) (t : ℕ) :
    cycAt C x₀ t = C[t % C.length]'(Nat.mod_lt _ hpos) := by
  rw [cycAt, List.getD_eq_getElem C x₀ (Nat.mod_lt _ hpos)]

theorem cycAt_mem {C : List V} {x₀ : V} (hpos : 0 < C.length) (t : ℕ) :
    cycAt C x₀ t ∈ C := by
  rw [cycAt_mod_lt hpos]; exact List.getElem_mem _

theorem cycAt_inj {C : List V} {x₀ : V} (hnd : C.Nodup) (hpos : 0 < C.length) {s t : ℕ}
    (h : cycAt C x₀ s = cycAt C x₀ t) : s % C.length = t % C.length := by
  rw [cycAt_mod_lt hpos, cycAt_mod_lt hpos] at h
  exact (List.Nodup.getElem_inj_iff hnd).mp h

theorem cycAt_ne {C : List V} {x₀ : V} (hnd : C.Nodup) (hpos : 0 < C.length) {s t : ℕ}
    (h : s % C.length ≠ t % C.length) : cycAt C x₀ s ≠ cycAt C x₀ t :=
  fun he => h (cycAt_inj hnd hpos he)

theorem cycAt_congr {C : List V} {x₀ : V} {s t : ℕ} (h : s % C.length = t % C.length) :
    cycAt C x₀ s = cycAt C x₀ t := by
  rw [cycAt, cycAt, h]

theorem mod_cancel_left {a s t n : ℕ} (h : (a + s) % n = (a + t) % n) : s % n = t % n :=
  Nat.ModEq.add_left_cancel' a h

/-- The `%`-eliminator used everywhere below: for `x < 2n` the residue is either `x` or
`x - n`.  `omega` cannot reason about `%` with a variable modulus, so every index argument
goes through this. -/
theorem mod_two_cases {x n : ℕ} (hn : 0 < n) (h : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **A cyclically contiguous block of a cycle is an induced path.**

`C` is a cycle of `G` (cyclically consecutive vertices adjacent, `hcycle`) which is induced
except possibly for the chord `C[hh] C[jj]` (`hinduced`).  A block of `L` consecutive cyclic
positions starting at `a`, with `1 ≤ L ≤ |C| - 1`, whose position set does not contain both
`hh` and `jj` (`hexc`), is a path of `G` from `C[a]` to `C[a+L-1]`. -/
theorem arc_isPathFrom {G : SimpleGraph V} {C : List V} {hh jj : ℕ}
    (hnd : C.Nodup) (hn4 : 4 ≤ C.length)
    (hcycle : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length),
      (b = (a + 1) % C.length ∨ a = (b + 1) % C.length) → G.Adj C[a] C[b])
    (hinduced : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length),
      G.Adj C[a] C[b] →
        ((b = (a + 1) % C.length ∨ a = (b + 1) % C.length) ∨
          ((a = hh ∧ b = jj) ∨ (a = jj ∧ b = hh))))
    (x₀ : V) (a L : ℕ) (hL : 1 ≤ L) (hLn : L ≤ C.length - 1)
    (hexc : ∀ t, t < L → ∀ u, u < L →
      ¬ ((a + t) % C.length = hh ∧ (a + u) % C.length = jj)) :
    IsPathFrom G (arc C x₀ a L) (cycAt C x₀ a) (cycAt C x₀ (a + L - 1)) := by
  have hpos : 0 < C.length := by omega
  have hlenA : (arc C x₀ a L).length = L := arc_length C x₀ a L
  have hidx : ∀ t, t < L → ∀ u, u < L →
      ((a + t) % C.length = (a + u) % C.length → t = u) := by
    intro t ht u hu he
    have h2 := mod_cancel_left he
    rwa [Nat.mod_eq_of_lt (show t < C.length by omega),
      Nat.mod_eq_of_lt (show u < C.length by omega)] at h2
  have hkey : ∀ t, t < L → ∀ u, u < L →
      (G.Adj (cycAt C x₀ (a + t)) (cycAt C x₀ (a + u)) ↔ (t + 1 = u ∨ u + 1 = t)) := by
    intro t ht u hu
    have hA : (a + t) % C.length < C.length := Nat.mod_lt _ hpos
    have hB : (a + u) % C.length < C.length := Nat.mod_lt _ hpos
    rw [cycAt_mod_lt hpos (a + t), cycAt_mod_lt hpos (a + u)]
    constructor
    · intro hadj
      rcases hinduced _ _ hA hB hadj with hc | he
      · rcases hc with hc | hc
        · rw [Nat.mod_add_mod] at hc
          have h2 := mod_cancel_left (a := a) (s := u) (t := t + 1) hc
          rw [Nat.mod_eq_of_lt (show u < C.length by omega),
            Nat.mod_eq_of_lt (show t + 1 < C.length by omega)] at h2
          omega
        · rw [Nat.mod_add_mod] at hc
          have h2 := mod_cancel_left (a := a) (s := t) (t := u + 1) hc
          rw [Nat.mod_eq_of_lt (show t < C.length by omega),
            Nat.mod_eq_of_lt (show u + 1 < C.length by omega)] at h2
          omega
      · exfalso
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hexc t ht u hu ⟨h1, h2⟩
        · exact hexc u hu t ht ⟨h2, h1⟩
    · intro hc
      refine hcycle _ _ hA hB ?_
      rcases hc with hc | hc
      · left; rw [Nat.mod_add_mod]; congr 1; omega
      · right; rw [Nat.mod_add_mod]; congr 1; omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro he
    rw [he] at hlenA
    simp only [List.length_nil] at hlenA
    omega
  · rw [arc]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro s hs t ht hst
    rw [List.mem_range] at hs ht
    exact hidx s hs t ht (cycAt_inj hnd hpos hst)
  · intro t u ht hu
    have ht' : t < L := hlenA ▸ ht
    have hu' : u < L := hlenA ▸ hu
    rw [arc_getElem C x₀ a L t ht, arc_getElem C x₀ a L u hu]
    exact hkey t ht' u hu'
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      arc_getElem C x₀ a L 0 (by omega)]
    simp
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega),
      arc_getElem C x₀ a L _ (by omega), hlenA]
    have he : a + (L - 1) = a + L - 1 := by omega
    rw [he]

end Workspace.ProofLemmas.CycleArcPath
