import Workspace.ProofLemmas.Thm192Claim6Basics
import Workspace.ProofLemmas.PathAttach

/-! The two-hole parity argument in claim (6) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim6FirstNeighbour

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (claim (6)): "From the hole `z-x₂-p₁-⋯-pⱼ-y-z` we deduce that `j`
is odd, and therefore `x₀-p₁-⋯-pⱼ-y-x₀` is not a hole, that is, `j = 1`." -/
theorem first_neighbour {G : SimpleGraph V} (hG : Berge G)
    {P : List V} {a b z u y : V} (hP : IsPathFrom G P a b) (hlen : 3 ≤ P.length)
    (hzP : z ∉ P) (huP : u ∉ P) (hyP : y ∉ P)
    (hzI : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w)
    (hzu : G.Adj z u) (hzy : G.Adj z y) (hya : G.Adj y a)
    (huy : ¬ G.Adj u y)
    (hu1 : G.Adj u (P[1]'(by omega)))
    (huonly : ∀ i (hi : i < P.length), 1 ≤ i → i + 1 < P.length →
      G.Adj u (P[i]'hi) → i = 1)
    (hyI : ∃ w ∈ SPGT.interior P, G.Adj y w) :
    G.Adj y (P[1]'(by omega)) := by
  classical
  obtain ⟨w, hw, hyw⟩ := hyI
  obtain ⟨k, hk, hk1, hk2, hkw⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hw
  have hex : ∃ j : ℕ, ∃ hj : j < P.length,
      1 ≤ j ∧ j + 1 < P.length ∧ G.Adj y (P[j]'hj) :=
    ⟨k, hk, hk1, by omega, by rwa [hkw]⟩
  obtain ⟨hj, hj1, hjn, hyj⟩ := Nat.find_spec hex
  set j := Nat.find hex with hjdef
  have hyj' : G.Adj y (P[j]'hj) := hyj
  have hmin : ∀ i (hi : i < P.length), 1 ≤ i → i < j → ¬ G.Adj y (P[i]'hi) := by
    intro i hi hi1 hij hyi
    exact Nat.find_min hex hij ⟨hi, hi1, by omega, hyi⟩
  by_cases hjone : j = 1
  · simpa only [hjone] using hyj'
  have hj2 : 2 ≤ j := by omega
  have hp0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hL : IsPathFrom G ((P.drop 0).take (j - 0 + 1)) a (P[j]'hj) := by
    simpa only [hp0] using PathBasics.isPathFrom_slice hP.1 (by omega : 0 < j) hj
  have hLI : ∀ v ∈ SPGT.interior ((P.drop 0).take (j - 0 + 1)), ¬ G.Adj y v := by
    intro v hv
    obtain ⟨i, hi, hi0, hij, rfl⟩ :=
      (PathBasics.mem_interior_slice_iff hP.1 (by omega : 0 < j) hj).mp hv
    exact hmin i hi (by omega) hij
  have hLC : IsHoleList G (y :: ((P.drop 0).take (j - 0 + 1))) :=
    PrismBasics.isHoleList_of_path_add_vertex hL
      (by rw [pathLength, PathBasics.length_slice P (by omega) hj]; omega) hya hyj
      (fun h => hyP (List.mem_of_mem_drop (List.mem_of_mem_take h))) hLI
  have hR : IsPathFrom G ((P.drop 1).take (j - 1 + 1)) (P[1]'(by omega)) (P[j]'hj) :=
    PathBasics.isPathFrom_slice hP.1 (by omega) hj
  have hRmem : ∀ v ∈ (P.drop 1).take (j - 1 + 1), v ∈ SPGT.interior P := by
    intro v hv
    obtain ⟨i, hi, hi1, hij, rfl⟩ := (PathBasics.mem_slice_iff P (by omega : 1 ≤ j) hj).mp hv
    exact PathBasics.getElem_mem_interior hP.1 hi (by omega) (by omega)
  have hRsub : ∀ v ∈ (P.drop 1).take (j - 1 + 1), v ∈ P :=
    fun v hv => PathBasics.interior_subset (hRmem v hv)
  have hRy : IsPathFrom G (((P.drop 1).take (j - 1 + 1)) ++ [y]) (P[1]'(by omega)) y := by
    apply PathAttach.isPathFrom_concat hR hyj (fun h => hyP (hRsub y h))
    intro v hv hvj
    obtain ⟨i, hi, hi1, hij, hvi⟩ := (PathBasics.mem_slice_iff P (by omega : 1 ≤ j) hj).mp hv
    have hij' : i < j := by
      by_contra h
      have he : i = j := by omega
      subst i
      exact hvj hvi.symm
    rw [← hvi]
    exact hmin i hi hi1 hij'
  have huyne : u ≠ y := by
    intro he
    have : G.Adj y (P[1]'(by omega)) := he ▸ hu1
    exact hmin 1 (by omega) le_rfl (by omega) this
  have huR : u ∉ ((P.drop 1).take (j - 1 + 1)) ++ [y] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨fun h => huP (hRsub u h), huyne⟩
  have hzR : z ∉ ((P.drop 1).take (j - 1 + 1)) ++ [y] := by
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨fun h => hzP (hRsub z h), hzy.ne⟩
  have hRC : IsHoleList G (z :: u :: (((P.drop 1).take (j - 1 + 1)) ++ [y])) := by
    apply PrismBasics.isHoleList_of_path_add_two_vertices hRy
      (by simp only [pathLength, List.length_append, List.length_cons, List.length_nil,
        PathBasics.length_slice P (by omega : 1 ≤ j) hj]; omega)
      hu1 hzy hzu.symm huR hzR huy (hzI _ (hRmem _ (PathBasics.head_mem hR.2.1)))
    · intro v hv huv
      have hvRy := PathBasics.interior_subset hv
      have hvy := ((PathBasics.mem_interior_iff_of_pathFrom hRy).mp hv).2.2
      have hv1 := ((PathBasics.mem_interior_iff_of_pathFrom hRy).mp hv).2.1
      rcases List.mem_append.mp hvRy with hvR | hv
      · obtain ⟨i, hi, hi1, hij, hvi⟩ := (PathBasics.mem_slice_iff P (by omega : 1 ≤ j) hj).mp hvR
        have he := huonly i hi hi1 (by omega) (by rwa [hvi])
        subst i
        exact hv1 hvi.symm
      · exact hvy (by simpa using hv)
    · intro v hv
      have hvRy := PathBasics.interior_subset hv
      have hvy := ((PathBasics.mem_interior_iff_of_pathFrom hRy).mp hv).2.2
      rcases List.mem_append.mp hvRy with hvR | hv
      · exact hzI v (hRmem v hvR)
      · exact (hvy (by simpa using hv)).elim
  have heL := hG.1 _ hLC
  have heR := hG.1 _ hRC
  rw [Nat.even_iff] at heL heR
  simp only [holeLength, List.length_cons, List.length_append, List.length_nil,
    PathBasics.length_slice P (by omega : 0 ≤ j) hj] at heL
  simp only [holeLength, List.length_cons, List.length_append, List.length_nil,
    PathBasics.length_slice P (by omega : 1 ≤ j) hj] at heR
  omega

end Workspace.ProofLemmas.Thm192Claim6FirstNeighbour
