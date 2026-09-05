import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.TrackSlice

/-!
# A shortest crossing subpath

This is the list bookkeeping for the path used near the end of 8.6, claim (1).  Starting with a
path in a connected set from `A` to `B`, it keeps a shortest interval whose ends still lie in
the two sets.  Its internal vertices avoid both.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoMajorVerticesCleanPath

open Workspace.Types.Core Workspace.Types.Core.SPGT

/-- A connected set meeting two disjoint sets contains an induced crossing path whose interior
avoids both sets. -/
theorem exists_clean_path
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {D A B : Set V} {u v : V}
    (hD : ConnectedSet G D) (huD : u ∈ D) (huA : u ∈ A)
    (hvD : v ∈ D) (hvB : v ∈ B) (hAB : Disjoint A B) :
    ∃ (p : List V) (a b : V),
      IsPathFrom G p a b ∧ a ∈ A ∧ b ∈ B ∧
      (∀ z ∈ p, z ∈ D) ∧
      ∀ z ∈ SPGT.interior p, z ∉ A ∧ z ∉ B := by
  obtain ⟨q, hq, hqD⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected hD huD hvD
  have huv : u ≠ v := by
    intro h
    subst h
    exact (Set.disjoint_left.mp hAB huA) hvB
  have hpos : 0 < q.length := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
  have hlen : 2 ≤ q.length := by
    by_contra h
    have hq1 : q.length = 1 := by omega
    have h0 := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hq.2.1 hpos
    have hl := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hq.2.2 hpos
    apply huv
    rw [← h0, ← hl]
    congr 1
    omega
  have hq0 : q[0]'hpos = u :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hq.2.1 hpos
  have hqlast : q[q.length - 1]'(by omega) = v :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hq.2.2 hpos
  obtain ⟨i, j, hi0, hij, hjlast, hi, hj, hiA, hjB, hclean⟩ :=
    Workspace.ProofLemmas.TrackSlice.exists_clean_indices
      (R := q) (A := A) (B := B) (q.length - 1) 0 (q.length - 1)
      (by omega) (by omega) (by omega) (by simpa [hq0] using huA)
      (by simpa [hqlast] using hvB)
  refine ⟨(q.drop i).take (j - i + 1), q[i]'hi, q[j]'hj,
    Workspace.ProofLemmas.PathBasics.isPathFrom_slice hq.1 hij hj, hiA, hjB, ?_, ?_⟩
  · intro z hz
    rw [Workspace.ProofLemmas.PathBasics.mem_slice_iff q (le_of_lt hij) hj] at hz
    obtain ⟨k, hk, -, -, rfl⟩ := hz
    exact hqD _ (List.getElem_mem hk)
  · intro z hz
    rw [Workspace.ProofLemmas.PathBasics.mem_interior_slice_iff hq.1 hij hj] at hz
    obtain ⟨k, hk, hik, hkj, rfl⟩ := hz
    exact hclean k hk hik hkj

end Workspace.ProofLemmas.NoMajorVerticesCleanPath
