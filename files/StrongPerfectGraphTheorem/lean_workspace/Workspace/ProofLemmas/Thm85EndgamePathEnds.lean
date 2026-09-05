import Mathlib
import Workspace.Types.Core

/-!
# The ends of a path are determined by its vertex set

In the endgame of 8.5 the path supplied by 5.8 has its vertex set equal to `F`, and `F` is
also the vertex set of the path `f₁, …, f_n` produced earlier in the proof.  The printed proof
then speaks of the ends of that path as `f₁` and `f_n` without further comment.  This module
supplies the missing step: a path of `G` (an *induced* path, `Core.IsPathList`) is determined
by its vertex set up to reversal, so its two ends are.

The argument is the obvious one.  In an induced path, the first vertex has at most one
neighbour inside the path, and so does the last one, while a vertex strictly inside the path
has two distinct neighbours inside it.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85EndgamePathEnds

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- The first vertex of a path list, as an indexed entry. -/
theorem getElem_zero {A : List V} {x y : V} (hA : IsPathFrom G A x y) :
    ∃ h : 0 < A.length, A[0]'h = x := by
  have hne : A ≠ [] := hA.1.1
  have hpos : 0 < A.length := List.length_pos_iff.mpr hne
  refine ⟨hpos, ?_⟩
  have h := hA.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at h
  exact Option.some_injective _ h

/-- The last vertex of a path list, as an indexed entry. -/
theorem getElem_last {A : List V} {x y : V} (hA : IsPathFrom G A x y) :
    ∃ h : A.length - 1 < A.length, A[A.length - 1]'h = y := by
  have hne : A ≠ [] := hA.1.1
  have hpos : 0 < A.length := List.length_pos_iff.mpr hne
  have hlt : A.length - 1 < A.length := by omega
  refine ⟨hlt, ?_⟩
  have h := hA.2.2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlt] at h
  exact Option.some_injective _ h

/-- The first vertex of a path has at most one neighbour on the path. -/
theorem head_neighbour_unique {A : List V} {x y : V} (hA : IsPathFrom G A x y)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A) (hxu : G.Adj x u) (hxv : G.Adj x v) : u = v := by
  obtain ⟨h0, hx0⟩ := getElem_zero hA
  obtain ⟨ku, hku, hkeu⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨kv, hkv, hkev⟩ := List.mem_iff_getElem.mp hv
  have hadju : G.Adj (A[0]'h0) (A[ku]'hku) := by rw [hx0, hkeu]; exact hxu
  have hadjv : G.Adj (A[0]'h0) (A[kv]'hkv) := by rw [hx0, hkev]; exact hxv
  have hu1 : ku = 1 := by
    rcases (hA.1.2.2 0 ku h0 hku).mp hadju with h | h <;> omega
  have hv1 : kv = 1 := by
    rcases (hA.1.2.2 0 kv h0 hkv).mp hadjv with h | h <;> omega
  rw [← hkeu, ← hkev]
  subst hu1; subst hv1; rfl

/-- The last vertex of a path has at most one neighbour on the path. -/
theorem last_neighbour_unique {A : List V} {x y : V} (hA : IsPathFrom G A x y)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A) (hyu : G.Adj y u) (hyv : G.Adj y v) : u = v := by
  obtain ⟨hl, hxl⟩ := getElem_last hA
  obtain ⟨ku, hku, hkeu⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨kv, hkv, hkev⟩ := List.mem_iff_getElem.mp hv
  have hadju : G.Adj (A[A.length - 1]'hl) (A[ku]'hku) := by rw [hxl, hkeu]; exact hyu
  have hadjv : G.Adj (A[A.length - 1]'hl) (A[kv]'hkv) := by rw [hxl, hkev]; exact hyv
  have hu1 : ku = A.length - 2 := by
    rcases (hA.1.2.2 _ ku hl hku).mp hadju with h | h <;> omega
  have hv1 : kv = A.length - 2 := by
    rcases (hA.1.2.2 _ kv hl hkv).mp hadjv with h | h <;> omega
  rw [← hkeu, ← hkev]
  subst hu1; subst hv1; rfl

/-- A vertex strictly inside a path has two distinct neighbours on the path. -/
theorem interior_two_neighbours {A : List V} {x y : V} (hA : IsPathFrom G A x y)
    {k : ℕ} (hk : k < A.length) (hk0 : k ≠ 0) (hklast : k + 1 ≠ A.length) :
    ∃ u v : V, u ∈ A ∧ v ∈ A ∧ u ≠ v ∧ G.Adj (A[k]'hk) u ∧ G.Adj (A[k]'hk) v := by
  have hk1 : k - 1 < A.length := by omega
  have hk2 : k + 1 < A.length := by omega
  refine ⟨A[k - 1]'hk1, A[k + 1]'hk2, List.getElem_mem hk1, List.getElem_mem hk2, ?_, ?_, ?_⟩
  · intro h
    have := (hA.1.2.1.getElem_inj_iff (i := k - 1) (j := k + 1) (hi := hk1) (hj := hk2)).mp h
    omega
  · exact (hA.1.2.2 k (k - 1) hk hk1).mpr (by omega)
  · exact (hA.1.2.2 k (k + 1) hk hk2).mpr (by omega)

/-- **The ends of a path are determined by its vertex set.**

If two paths of `G` have the same vertex set, then their end pairs coincide. -/
theorem ends_eq_of_vertex_set_eq {A B : List V} {x y z w : V}
    (hA : IsPathFrom G A x y) (hB : IsPathFrom G B z w)
    (hset : ∀ v : V, v ∈ A ↔ v ∈ B) :
    (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
  classical
  -- an end of `B` cannot sit strictly inside `A`
  have hend : ∀ t : V, t ∈ B →
      (∀ u v : V, u ∈ B → v ∈ B → G.Adj t u → G.Adj t v → u = v) → t = x ∨ t = y := by
    intro t htB huniq
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp ((hset t).mpr htB)
    by_cases hk0 : k = 0
    · left
      obtain ⟨h0, hx0⟩ := getElem_zero hA
      rw [← hke, ← hx0]
      congr 1
    · by_cases hklast : k + 1 = A.length
      · right
        obtain ⟨hl, hyl⟩ := getElem_last hA
        rw [← hke, ← hyl]
        congr 1
        omega
      · exfalso
        obtain ⟨u, v, huA, hvA, huv, hadju, hadjv⟩ :=
          interior_two_neighbours hA hk hk0 hklast
        rw [hke] at hadju hadjv
        exact huv (huniq u v ((hset u).mp huA) ((hset v).mp hvA) hadju hadjv)
  have hzB : z ∈ B := List.mem_of_mem_head? hB.2.1
  have hwB : w ∈ B := List.mem_of_getLast? hB.2.2
  have hz := hend z hzB (fun u v hu hv h1 h2 => head_neighbour_unique hB hu hv h1 h2)
  have hw := hend w hwB (fun u v hu hv h1 h2 => last_neighbour_unique hB hu hv h1 h2)
  -- if the two ends of `B` coincide then `B`, hence `A`, is a single vertex
  by_cases hzw : z = w
  · have hB1 : B.length = 1 := by
      obtain ⟨h0, hz0⟩ := getElem_zero hB
      obtain ⟨hl, hwl⟩ := getElem_last hB
      have : (0 : ℕ) = B.length - 1 := by
        refine (hB.1.2.1.getElem_inj_iff (hi := h0) (hj := hl)).mp ?_
        rw [hz0, hwl, hzw]
      omega
    have hA1 : A.length = 1 := by
      have hfin : A.toFinset = B.toFinset := by
        ext v; simpa using hset v
      have := congrArg Finset.card hfin
      rw [List.toFinset_card_of_nodup hA.1.2.1, List.toFinset_card_of_nodup hB.1.2.1] at this
      omega
    have hxy : x = y := by
      obtain ⟨h0, hx0⟩ := getElem_zero hA
      obtain ⟨hl, hyl⟩ := getElem_last hA
      rw [← hx0, ← hyl]
      congr 1
      omega
    rcases hz with h | h
    · exact Or.inl ⟨h, by rw [← hzw, h, hxy]⟩
    · exact Or.inr ⟨h, by rw [← hzw, h, ← hxy]⟩
  · rcases hz with hz1 | hz1 <;> rcases hw with hw1 | hw1
    · exact absurd (hz1.trans hw1.symm) hzw
    · exact Or.inl ⟨hz1, hw1⟩
    · exact Or.inr ⟨hz1, hw1⟩
    · exact absurd (hz1.trans hw1.symm) hzw

/-- A path whose two ends coincide is a single vertex. -/
theorem eq_of_ends_eq {A : List V} {x y : V} (hA : IsPathFrom G A x y) (hxy : x = y) :
    ∀ z ∈ A, z = x := by
  classical
  obtain ⟨h0, hx0⟩ := getElem_zero hA
  obtain ⟨hl, hyl⟩ := getElem_last hA
  have hA1 : A.length = 1 := by
    have : (0 : ℕ) = A.length - 1 := by
      refine (hA.1.2.1.getElem_inj_iff (hi := h0) (hj := hl)).mp ?_
      rw [hx0, hyl, hxy]
    omega
  intro z hz
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp hz
  rw [← hke, ← hx0]
  congr 1
  omega

end Workspace.ProofLemmas.Thm85EndgamePathEnds
