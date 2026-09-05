import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Types.RousselRubio

/-!
# Cutting a hole into the two paths of a triangle link

PAPER (5.8 (7), printed p. 28): *"There correspond two paths in `L(H)`, say `P`
and `Q`, from `N_{u₁}` and `N_{v₁}` respectively to `N_{u₂}`, disjoint from each
other, and there is a third path `R` say from `p₁` to `N_{u₂}` via `F` and a
subpath of `R_{u₂v₂}`.  There are no edges between these paths except within the
triangle `T` formed by their ends in `N_{u₂}`."*

The two paths `P` and `Q` are obtained from the hole of `G` carried by the cycle
of `H`: delete its first vertex, and cut the remaining path between positions
`j` and `j + 1`, the two vertices of the hole in `N_{u₂}`.  Everything in this
file is elementary bookkeeping about lists; the geometry is elsewhere.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranchCut

open Workspace.Types.Core.SPGT Workspace.Types.RousselRubio.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- A hole with its first vertex deleted is a path. -/
theorem isPathList_hole_drop_one {Z : List V} (hZ : IsHoleList G Z) :
    IsPathList G (Z.drop 1) := by
  obtain ⟨h4, hnd, hadj⟩ := hZ
  have hlen : (Z.drop 1).length = Z.length - 1 := List.length_drop
  refine ⟨?_, List.Nodup.sublist (List.drop_sublist 1 Z) hnd, ?_⟩
  · intro hc
    have h0 : (Z.drop 1).length = 0 := by rw [hc]; rfl
    omega
  · intro i j hi hj
    have hi' : 1 + i < Z.length := by omega
    have hj' : 1 + j < Z.length := by omega
    simp only [List.getElem_drop]
    rw [hadj (1 + i) (1 + j) hi' hj', PathGlue.succ_mod_eq hi', PathGlue.succ_mod_eq hj']
    split_ifs <;> omega


/-- The two arcs of the cut, together with everything the triangle link needs.

`Z` is the hole; its first vertex is deleted, and the cut edge is the one
between positions `j` and `j + 1`, whose ends `α` and `β` are two of the three
triangle vertices.  `R` is the third path, with end `t`. -/
theorem link_of_hole_cut {Z R : List V} {j : ℕ} {α β t v : V}
    (hZ : IsHoleList G Z) (hj : 1 ≤ j) (hj' : j + 1 < Z.length)
    (hα : Z[j]? = some α) (hβ : Z[j + 1]? = some β)
    (hR : IsPathList G R) (hRhead : R.head? = some t)
    (hRZ : ∀ z ∈ R, z ∉ Z)
    (hcross : ∀ z ∈ R, ∀ zz ∈ Z.drop 1, (G.Adj z zz ↔ (z = t ∧ (zz = α ∨ zz = β))))
    (hnA : ∃ i, 1 ≤ i ∧ i ≤ j ∧ ∃ z, Z[i]? = some z ∧ G.Adj v z)
    (hnB : ∃ k, j + 1 ≤ k ∧ k < Z.length ∧ ∃ z, Z[k]? = some z ∧ G.Adj v z)
    (hnR : ∃ z ∈ R, G.Adj v z) :
    VertexCanBeLinkedOntoTriangle G v α β t := by
  classical
  obtain ⟨h4, hnd, hZadj⟩ := hZ
  set L := Z.length with hL
  set W : List V := Z.drop 1 with hW
  have hWlen : W.length = L - 1 := List.length_drop
  have hWpath : IsPathList G W := isPathList_hole_drop_one ⟨h4, hnd, hZadj⟩
  have hWget : ∀ i : ℕ, W[i]? = Z[1 + i]? := fun i => List.getElem?_drop
  set A : List V := W.take j with hA
  set B : List V := W.drop j with hB
  have hAlen : A.length = j := by simp only [hA, List.length_take, hWlen]; omega
  have hBlen : B.length = L - 1 - j := by simp only [hB, List.length_drop, hWlen]
  have hAget : ∀ i : ℕ, i < j → A[i]? = Z[1 + i]? := by
    intro i hi
    rw [hA, List.getElem?_take_of_lt hi, hWget]
  have hBget : ∀ i : ℕ, B[i]? = Z[1 + j + i]? := by
    intro i
    rw [hB, List.getElem?_drop, hWget]
    congr 1
    omega
  -- membership dictionaries
  have hmemA : ∀ x, x ∈ A ↔ ∃ i, i < j ∧ Z[1 + i]? = some x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hi
      exact ⟨i, by omega, by rw [← hAget i (by omega)]; exact hi⟩
    · rintro ⟨i, hi, hz⟩
      exact List.mem_iff_getElem?.mpr ⟨i, by rw [hAget i hi]; exact hz⟩
  have hmemB : ∀ x, x ∈ B ↔ ∃ i, 1 + j + i < L ∧ Z[1 + j + i]? = some x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      obtain ⟨hilt, -⟩ := List.getElem?_eq_some_iff.mp hi
      refine ⟨i, by omega, by rw [← hBget i]; exact hi⟩
    · rintro ⟨i, hi, hz⟩
      exact List.mem_iff_getElem?.mpr ⟨i, by rw [hBget i]; exact hz⟩
  have hmemZ2 : ∀ x ∈ W, x ∈ Z := fun x hx => List.mem_of_mem_drop hx
  have key : ∀ (a b : ℕ) (x y : V), Z[a]? = some x → Z[b]? = some y →
      (G.Adj x y ↔ (b = (a + 1) % L ∨ a = (b + 1) % L)) := by
    intro a b x y hx hy
    obtain ⟨ha, rfl⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hb, rfl⟩ := List.getElem?_eq_some_iff.mp hy
    exact hZadj a b ha hb
  have hinj : ∀ (a b : ℕ) (x : V), Z[a]? = some x → Z[b]? = some x → a = b := by
    intro a b x hx hy
    obtain ⟨ha, hxa⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hb, hxb⟩ := List.getElem?_eq_some_iff.mp hy
    exact hnd.getElem_inj_iff.mp (hxa.trans hxb.symm)
  have hαA : α ∈ A := (hmemA α).mpr ⟨j - 1, by omega, by
    have : 1 + (j - 1) = j := by omega
    rw [this]; exact hα⟩
  have hβB : β ∈ B := (hmemB β).mpr ⟨0, by omega, by
    have : 1 + j + 0 = j + 1 := by omega
    rw [this]; exact hβ⟩
  have hdisjAB : ∀ x ∈ A, x ∉ B := by
    intro x hx hx'
    obtain ⟨i, hi, hzi⟩ := (hmemA x).mp hx
    obtain ⟨k, hk, hzk⟩ := (hmemB x).mp hx'
    have := hinj _ _ _ hzi hzk
    omega
  have hAW : ∀ x ∈ A, x ∈ W := fun x hx => List.mem_of_mem_take hx
  have hBW : ∀ x ∈ B, x ∈ W := fun x hx => List.mem_of_mem_drop hx
  have hApath : IsPathList G A := PathBasics.isPathList_take hWpath (by omega)
  have hBpath : IsPathList G B := PathBasics.isPathList_drop hWpath (by omega)
  have hAlast : A.getLast? = some α := by
    rw [List.getLast?_eq_getElem?, hAlen, hAget (j - 1) (by omega)]
    have : 1 + (j - 1) = j := by omega
    rw [this]; exact hα
  have hBhead : B.head? = some β := by
    rw [List.head?_eq_getElem?, hBget 0]
    have : 1 + j + 0 = j + 1 := by omega
    rw [this]; exact hβ
  refine ⟨A, B, R, ⟨hApath, hBpath, hR⟩, ⟨hdisjAB, ?_, ?_⟩,
    ⟨Or.inr hAlast, Or.inl hBhead, Or.inl hRhead⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, hnR⟩
  · exact fun x hx hx' => hRZ x hx' (hmemZ2 x (hAW x hx))
  · exact fun x hx hx' => hRZ x hx' (hmemZ2 x (hBW x hx))
  · -- the unique edge between the two arcs is `αβ`
    intro x hx y hy
    obtain ⟨i, hi, hzi⟩ := (hmemA x).mp hx
    obtain ⟨k, hk, hzk⟩ := (hmemB y).mp hy
    rw [key _ _ _ _ hzi hzk, PathGlue.succ_mod_eq (show 1 + i < L by omega),
      PathGlue.succ_mod_eq (show 1 + j + k < L by omega)]
    constructor
    · intro h
      have hik : i = j - 1 ∧ k = 0 := by split_ifs at h <;> omega
      refine ⟨?_, ?_⟩
      · have := hik.1
        subst this
        exact Option.some_injective _ (hzi.symm.trans (by
          have : 1 + (j - 1) = j := by omega
          rw [this]; exact hα))
      · have := hik.2
        subst this
        exact Option.some_injective _ (hzk.symm.trans (by
          have : 1 + j + 0 = j + 1 := by omega
          rw [this]; exact hβ))
    · rintro ⟨rfl, rfl⟩
      have h1 : 1 + i = j := hinj _ _ _ hzi hα
      have h2 : 1 + j + k = j + 1 := hinj _ _ _ hzk hβ
      split_ifs <;> omega
  · intro x hx y hy
    have hxβ : x ≠ β := fun hh => hdisjAB x hx (hh ▸ hβB)
    rw [SimpleGraph.adj_comm, hcross y hy x (hAW x hx)]
    constructor
    · rintro ⟨rfl, (rfl | rfl)⟩
      · exact ⟨rfl, rfl⟩
      · exact absurd rfl hxβ
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inl rfl⟩
  · intro x hx y hy
    have hxα : x ≠ α := fun hh => hdisjAB α hαA (hh ▸ hx)
    rw [SimpleGraph.adj_comm, hcross y hy x (hBW x hx)]
    constructor
    · rintro ⟨rfl, (rfl | rfl)⟩
      · exact absurd rfl hxα
      · exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inr rfl⟩
  · obtain ⟨i, hi1, hi2, z, hz, hvz⟩ := hnA
    refine ⟨z, (hmemA z).mpr ⟨i - 1, by omega, ?_⟩, hvz⟩
    have : 1 + (i - 1) = i := by omega
    rw [this]; exact hz
  · obtain ⟨k, hk1, hk2, z, hz, hvz⟩ := hnB
    refine ⟨z, (hmemB z).mpr ⟨k - (1 + j), by omega, ?_⟩, hvz⟩
    have : 1 + j + (k - (1 + j)) = k := by omega
    rw [this]; exact hz

end Workspace.ProofLemmas.Thm58BranchBranchCut
