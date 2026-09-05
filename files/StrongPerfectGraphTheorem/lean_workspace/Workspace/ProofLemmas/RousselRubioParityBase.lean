import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathCompleteEdgeIndexEquiv

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- The empty-set and short-path base cases of the strengthened
Roussel--Rubio parity argument. -/
theorem RousselRubioParityBase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Set V) (P : List V) (r s : V)
    (hP : IsPathFrom G P r s) (hPT : ∀ w ∈ P, w ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    (hbase : T = ∅ ∨ pathLength P ≤ 2) :
    let completeEdgeIndices : Set ℕ :=
      {i | i + 1 < P.length ∧
        ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
          EdgeComplete G T u v}
    completeEdgeIndices.ncard % 2 = pathLength P % 2 := by
  classical
  intro CEI
  have hmem : ∀ i : ℕ, i ∈ CEI ↔ (i + 1 < P.length ∧
      ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
        EdgeComplete G T u v) := fun _ => Iff.rfl
  obtain ⟨hpath, hhead, hlast⟩ := hP
  have hpos : 0 < P.length := PathBasics.path_length_pos hpath
  have hP0 : P[0]? = some r := by rw [← List.head?_eq_getElem?]; exact hhead
  have hPn : P[P.length - 1]? = some s := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  -- membership of an index whose two entries are known
  have hmemAt : ∀ (i : ℕ) (a b : V), P[i]? = some a → P[i + 1]? = some b →
      (i ∈ CEI ↔ (VertexComplete G a T ∧ VertexComplete G b T)) := by
    intro i a b ha hb
    have hi1 : i + 1 < P.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hb
      simp at hb
    have hai : i < P.length := by omega
    rw [hmem i]
    constructor
    · rintro ⟨-, u, v, hu, hv, hE⟩
      rw [ha] at hu
      rw [hb] at hv
      obtain rfl : a = u := Option.some_injective _ hu
      obtain rfl : b = v := Option.some_injective _ hv
      exact ⟨hE.2.1, hE.2.2⟩
    · rintro ⟨hA, hB⟩
      refine ⟨hi1, a, b, ha, hb, ?_, hA, hB⟩
      have ea : P[i]'hai = a := by
        rw [List.getElem?_eq_getElem hai] at ha; exact Option.some_injective _ ha
      have eb : P[i + 1]'hi1 = b := by
        rw [List.getElem?_eq_getElem hi1] at hb; exact Option.some_injective _ hb
      rw [← ea, ← eb]
      exact (hpath.2.2 i (i + 1) hai hi1).mpr (Or.inl rfl)
  have hnotmem : ∀ i : ℕ, P.length ≤ i + 1 → i ∉ CEI := by
    intro i h hc
    have := ((hmem i).mp hc).1
    omega
  rcases hbase with hT | hm
  · -- Empty `T`: every path edge is `T`-complete.
    subst hT
    have hall : CEI = Set.Iio (P.length - 1) := by
      ext i
      simp only [Set.mem_Iio]
      constructor
      · intro hi
        have := ((hmem i).mp hi).1
        omega
      · intro hi
        have hi1 : i + 1 < P.length := by omega
        have hai : i < P.length := by omega
        refine (hmemAt i (P[i]'hai) (P[i + 1]'hi1)
          (List.getElem?_eq_getElem hai) (List.getElem?_eq_getElem hi1)).mpr ⟨?_, ?_⟩
        · intro x hx; exact absurd hx (Set.notMem_empty x)
        · intro x hx; exact absurd hx (Set.notMem_empty x)
    have hpl : pathLength P = P.length - 1 := rfl
    rw [hall, Set.ncard_Iio_nat, hpl]
  · -- Short paths.
    have hlen3 : P.length ≤ 3 := by
      have : pathLength P = P.length - 1 := rfl
      omega
    have hcases : P.length = 1 ∨ P.length = 2 ∨ P.length = 3 := by omega
    rcases hcases with hn | hn | hn
    · have hempty : CEI = ∅ := by
        ext i
        simp only [Set.mem_empty_iff_false, iff_false]
        exact hnotmem i (by omega)
      have hpl : pathLength P = 0 := by
        have : pathLength P = P.length - 1 := rfl
        omega
      rw [hempty, Set.ncard_empty, hpl]
    · have hP1 : P[1]? = some s := by
        have he : P.length - 1 = 1 := by omega
        rw [he] at hPn; exact hPn
      have hsingle : CEI = {0} := by
        ext i
        simp only [Set.mem_singleton_iff]
        constructor
        · intro hi
          have := ((hmem i).mp hi).1
          omega
        · rintro rfl
          exact (hmemAt 0 r s hP0 hP1).mpr ⟨hr, hs⟩
      have hpl : pathLength P = 1 := by
        have : pathLength P = P.length - 1 := rfl
        omega
      rw [hsingle, Set.ncard_singleton, hpl]
    · have h1lt : 1 < P.length := by omega
      set z : V := P[1]'h1lt with hzdef
      have hP1 : P[1]? = some z := List.getElem?_eq_getElem h1lt
      have hP2 : P[2]? = some s := by
        have he : P.length - 1 = 2 := by omega
        rw [he] at hPn; exact hPn
      have hpl : pathLength P = 2 := by
        have : pathLength P = P.length - 1 := rfl
        omega
      have hzero : (0 : ℕ) ∈ CEI ↔ VertexComplete G z T := by
        rw [hmemAt 0 r z hP0 hP1]
        exact ⟨fun h => h.2, fun h => ⟨hr, h⟩⟩
      have hone : (1 : ℕ) ∈ CEI ↔ VertexComplete G z T := by
        rw [hmemAt 1 z s hP1 hP2]
        exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩
      by_cases hz : VertexComplete G z T
      · have hpair : CEI = {0, 1} := by
          ext i
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · intro hi
            have := ((hmem i).mp hi).1
            omega
          · rintro (rfl | rfl)
            · exact hzero.mpr hz
            · exact hone.mpr hz
        rw [hpair, Set.ncard_pair (by norm_num : (0 : ℕ) ≠ 1), hpl]
      · have hempty : CEI = ∅ := by
          ext i
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hi
          have hb := ((hmem i).mp hi).1
          have hi2 : i = 0 ∨ i = 1 := by omega
          rcases hi2 with rfl | rfl
          · exact hz (hzero.mp hi)
          · exact hz (hone.mp hi)
        rw [hempty, Set.ncard_empty, hpl]

end Workspace.ProofLemmas
