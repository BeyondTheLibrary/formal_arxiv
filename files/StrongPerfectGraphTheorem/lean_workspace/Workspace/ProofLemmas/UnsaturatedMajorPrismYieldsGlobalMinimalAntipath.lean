import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

private theorem two_outside_of_triple_ncard_lt_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : Fin 3 → V) (X : Set V)
    (hc : ∀ i j, i ≠ j → c i ≠ c j)
    (hlt : ¬ 2 ≤ (({c 0, c 1, c 2} : Set V) ∩ X).ncard) :
    ∃ i j : Fin 3, i ≠ j ∧ c i ∉ X ∧ c j ∉ X := by
  classical
  have pair_forces (i j : Fin 3) (hij : i ≠ j)
      (hi : c i ∈ X) (hj : c j ∈ X)
      (hiT : c i ∈ ({c 0, c 1, c 2} : Set V))
      (hjT : c j ∈ ({c 0, c 1, c 2} : Set V)) : False := by
    have hsub : ({c i, c j} : Set V) ⊆ (({c 0, c 1, c 2} : Set V) ∩ X) := by
      intro x hx
      rcases hx with (rfl | rfl)
      · exact ⟨hiT, hi⟩
      · exact ⟨hjT, hj⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair (hc i j hij)] at hle
    exact hlt hle
  by_cases h0 : c 0 ∈ X
  · by_cases h1 : c 1 ∈ X
    · exact (pair_forces 0 1 (by decide) h0 h1 (by simp) (by simp)).elim
    · by_cases h2 : c 2 ∈ X
      · exact (pair_forces 0 2 (by decide) h0 h2 (by simp) (by simp)).elim
      · exact ⟨1, 2, by decide, h1, h2⟩
  · by_cases h1 : c 1 ∈ X
    · by_cases h2 : c 2 ∈ X
      · exact (pair_forces 1 2 (by decide) h1 h2 (by simp) (by simp)).elim
      · exact ⟨0, 2, by decide, h0, h2⟩
    · exact ⟨0, 1, by decide, h0, h1⟩

private theorem eq_cons_interior_append_of_isPathFrom
    {V : Type*} {G : SimpleGraph V} {p : List V} {u v : V}
    (h : IsPathFrom G p u v) (huv : u ≠ v) :
    p = u :: (interior p ++ [v]) := by
  rcases p with _ | ⟨x, l⟩
  · simp [IsPathFrom, IsPathList] at h
  · have hxu : x = u := by simpa using h.2.1
    subst x
    have hlne : l ≠ [] := by
      intro hl
      subst l
      have huv' : u = v := by simpa using h.2.2
      exact huv huv'
    have hlast : l.getLast? = some v := by
      have hgl := h.2.2
      rwa [List.getLast?_cons_of_ne_nil hlne] at hgl
    simp only [Workspace.Types.Core.SPGT.interior, List.tail_cons]
    rw [List.dropLast_append_getLast? v hlast]

theorem UnsaturatedMajorPrismYieldsGlobalMinimalAntipath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y : Set V)
    (a b : Fin 3 → V) (P : Fin 3 → List V)
    (hY : AnticonnectedSet G Y)
    (hprism : FormPrism G a b (P 0) (P 1) (P 2))
    (hPoutside : ∀ i v, v ∈ P i → v ∉ Y)
    (hPlength : ∀ i, 1 < pathLength (P i))
    (hYmajor : ∀ y ∈ Y, MajorForPrism G a b y)
    (hunsaturated : ¬ SaturatesPrism a b {x : V | VertexComplete G x Y}) :
    ∃ (σ : Equiv.Perm (Fin 3)) (swapped : Bool)
      (α β : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V),
      (swapped = false →
        ∀ i, α i = a (σ i) ∧ β i = b (σ i) ∧ R i = P (σ i)) ∧
      (swapped = true →
        ∀ i, α i = b (σ i) ∧ β i = a (σ i) ∧ R i = (P (σ i)).reverse) ∧
      FormPrism G α β (R 0) (R 1) (R 2) ∧
      (∀ i v, v ∈ R i → v ∉ Y) ∧
      (∀ i, 1 < pathLength (R i)) ∧
      (∀ y ∈ Y, MajorForPrism G α β y) ∧
      Q = α 0 :: (q ++ [α 1]) ∧
      IsAntipathFrom G Q (α 0) (α 1) ∧
      (∀ x ∈ q, x ∈ Y) ∧
      ¬ VertexComplete G (α 0) Y ∧
      ¬ VertexComplete G (α 1) Y ∧
      ∀ (u v : V) (S : List V),
        u ≠ v →
        ((u ∈ ({α 0, α 1, α 2} : Set V) ∧ v ∈ ({α 0, α 1, α 2} : Set V)) ∨
          (u ∈ ({β 0, β 1, β 2} : Set V) ∧ v ∈ ({β 0, β 1, β 2} : Set V))) →
        ¬ VertexComplete G u Y →
        ¬ VertexComplete G v Y →
        IsAntipathFrom G S u v →
        (∀ x ∈ interior S, x ∈ Y) →
        pathLength Q ≤ pathLength S := by
  classical
  let X : Set V := {x : V | VertexComplete G x Y}
  have hfamily := PrismSymmetry.formPrism_family.mp hprism
  have haout : ∀ i, a i ∉ Y := by
    intro i
    exact hPoutside i (a i) (PathBasics.isPathFrom_ends_mem (hfamily.2.2.2.1 i)).1
  have hbout : ∀ i, b i ∉ Y := by
    intro i
    exact hPoutside i (b i) (PathBasics.isPathFrom_ends_mem (hfamily.2.2.2.1 i)).2
  have badpair :
      (∃ i j : Fin 3, i ≠ j ∧ ¬ VertexComplete G (a i) Y ∧ ¬ VertexComplete G (a j) Y) ∨
      (∃ i j : Fin 3, i ≠ j ∧ ¬ VertexComplete G (b i) Y ∧ ¬ VertexComplete G (b j) Y) := by
    by_cases hA : 2 ≤ (({a 0, a 1, a 2} : Set V) ∩ X).ncard
    · have hB : ¬ 2 ≤ (({b 0, b 1, b 2} : Set V) ∩ X).ncard := by
        intro hB
        exact hunsaturated ⟨hA, hB⟩
      obtain ⟨i, j, hij, hi, hj⟩ :=
        two_outside_of_triple_ncard_lt_two b X
          (fun i j hij => (hfamily.2.1 i j hij).ne) hB
      exact Or.inr ⟨i, j, hij, by simpa [X] using hi, by simpa [X] using hj⟩
    · obtain ⟨i, j, hij, hi, hj⟩ :=
        two_outside_of_triple_ncard_lt_two a X
          (fun i j hij => (hfamily.1 i j hij).ne) hA
      exact Or.inl ⟨i, j, hij, by simpa [X] using hi, by simpa [X] using hj⟩
  let Good : V → V → List V → Prop := fun u v S =>
    u ≠ v ∧
    ((u ∈ ({a 0, a 1, a 2} : Set V) ∧ v ∈ ({a 0, a 1, a 2} : Set V)) ∨
      (u ∈ ({b 0, b 1, b 2} : Set V) ∧ v ∈ ({b 0, b 1, b 2} : Set V))) ∧
    ¬ VertexComplete G u Y ∧ ¬ VertexComplete G v Y ∧
    IsAntipathFrom G S u v ∧ ∀ x ∈ interior S, x ∈ Y
  have hGood : ∃ u v S, Good u v S := by
    rcases badpair with ⟨i, j, hij, hi, hj⟩ | ⟨i, j, hij, hi, hj⟩
    · have hiw : ∃ y ∈ Y, ¬ G.Adj (a i) y := by
        simpa [VertexComplete] using hi
      have hjw : ∃ y ∈ Y, ¬ G.Adj (a j) y := by
        simpa [VertexComplete] using hj
      obtain ⟨S, hS, hSint⟩ :=
        InducedPathExtraction.exists_antipath_interior_in hY (haout i) (haout j) hiw hjw
      have hai : a i ∈ ({a 0, a 1, a 2} : Set V) := by fin_cases i <;> simp
      have haj : a j ∈ ({a 0, a 1, a 2} : Set V) := by fin_cases j <;> simp
      exact ⟨a i, a j, S, (hfamily.1 i j hij).ne, Or.inl ⟨hai, haj⟩,
        hi, hj, hS, hSint⟩
    · have hiw : ∃ y ∈ Y, ¬ G.Adj (b i) y := by
        simpa [VertexComplete] using hi
      have hjw : ∃ y ∈ Y, ¬ G.Adj (b j) y := by
        simpa [VertexComplete] using hj
      obtain ⟨S, hS, hSint⟩ :=
        InducedPathExtraction.exists_antipath_interior_in hY (hbout i) (hbout j) hiw hjw
      have hbi : b i ∈ ({b 0, b 1, b 2} : Set V) := by fin_cases i <;> simp
      have hbj : b j ∈ ({b 0, b 1, b 2} : Set V) := by fin_cases j <;> simp
      exact ⟨b i, b j, S, (hfamily.2.1 i j hij).ne, Or.inr ⟨hbi, hbj⟩,
        hi, hj, hS, hSint⟩
  have hex : ∃ n : ℕ, ∃ u v S, Good u v S ∧ pathLength S = n := by
    obtain ⟨u, v, S, hS⟩ := hGood
    exact ⟨pathLength S, u, v, S, hS, rfl⟩
  obtain ⟨u, v, Q, hQ, hQlen⟩ := Nat.find_spec hex
  have hmin : ∀ u' v' S, Good u' v' S → pathLength Q ≤ pathLength S := by
    intro u' v' S hS
    rw [hQlen]
    exact Nat.find_min' hex ⟨u', v', S, hS, rfl⟩
  rcases hQ with ⟨huv, hside, hnu, hnv, hanti, hint⟩
  have hshape : Q = u :: (interior Q ++ [v]) :=
    eq_cons_interior_append_of_isPathFrom hanti huv
  have finishA (σ : Equiv.Perm (Fin 3)) (hu : u = a (σ 0)) (hv : v = a (σ 1)) :
      ∃ (σ : Equiv.Perm (Fin 3)) (swapped : Bool)
        (α β : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V),
        (swapped = false →
          ∀ i, α i = a (σ i) ∧ β i = b (σ i) ∧ R i = P (σ i)) ∧
        (swapped = true →
          ∀ i, α i = b (σ i) ∧ β i = a (σ i) ∧ R i = (P (σ i)).reverse) ∧
        FormPrism G α β (R 0) (R 1) (R 2) ∧
        (∀ i v, v ∈ R i → v ∉ Y) ∧
        (∀ i, 1 < pathLength (R i)) ∧
        (∀ y ∈ Y, MajorForPrism G α β y) ∧
        Q = α 0 :: (q ++ [α 1]) ∧
        IsAntipathFrom G Q (α 0) (α 1) ∧
        (∀ x ∈ q, x ∈ Y) ∧
        ¬ VertexComplete G (α 0) Y ∧
        ¬ VertexComplete G (α 1) Y ∧
        ∀ (u v : V) (S : List V),
          u ≠ v →
          ((u ∈ ({α 0, α 1, α 2} : Set V) ∧ v ∈ ({α 0, α 1, α 2} : Set V)) ∨
            (u ∈ ({β 0, β 1, β 2} : Set V) ∧ v ∈ ({β 0, β 1, β 2} : Set V))) →
          ¬ VertexComplete G u Y → ¬ VertexComplete G v Y →
          IsAntipathFrom G S u v → (∀ x ∈ interior S, x ∈ Y) →
          pathLength Q ≤ pathLength S := by
    let α := fun i => a (σ i)
    let β := fun i => b (σ i)
    let R := fun i => P (σ i)
    refine ⟨σ, false, α, β, R, interior Q, Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ i; exact ⟨rfl, rfl, rfl⟩
    · simp
    · exact PrismSymmetry.formPrism_perm hprism σ
    · intro i x hx; exact hPoutside (σ i) x hx
    · intro i; exact hPlength (σ i)
    · intro y hy; exact (PrismSymmetry.majorForPrism_perm σ).mpr (hYmajor y hy)
    · simpa [α, hu, hv] using hshape
    · simpa [α, hu, hv] using hanti
    · exact hint
    · simpa [α, hu] using hnu
    · simpa [α, hv] using hnv
    · intro x y S hxy hside hx hy hS hSint
      apply hmin x y S
      refine ⟨hxy, ?_, hx, hy, hS, hSint⟩
      simpa only [α, β, PrismSymmetry.triple_perm a σ,
        PrismSymmetry.triple_perm b σ] using hside
  have finishB (σ : Equiv.Perm (Fin 3)) (hu : u = b (σ 0)) (hv : v = b (σ 1)) :
      ∃ (σ : Equiv.Perm (Fin 3)) (swapped : Bool)
        (α β : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V),
        (swapped = false →
          ∀ i, α i = a (σ i) ∧ β i = b (σ i) ∧ R i = P (σ i)) ∧
        (swapped = true →
          ∀ i, α i = b (σ i) ∧ β i = a (σ i) ∧ R i = (P (σ i)).reverse) ∧
        FormPrism G α β (R 0) (R 1) (R 2) ∧
        (∀ i v, v ∈ R i → v ∉ Y) ∧
        (∀ i, 1 < pathLength (R i)) ∧
        (∀ y ∈ Y, MajorForPrism G α β y) ∧
        Q = α 0 :: (q ++ [α 1]) ∧
        IsAntipathFrom G Q (α 0) (α 1) ∧
        (∀ x ∈ q, x ∈ Y) ∧
        ¬ VertexComplete G (α 0) Y ∧
        ¬ VertexComplete G (α 1) Y ∧
        ∀ (u v : V) (S : List V),
          u ≠ v →
          ((u ∈ ({α 0, α 1, α 2} : Set V) ∧ v ∈ ({α 0, α 1, α 2} : Set V)) ∨
            (u ∈ ({β 0, β 1, β 2} : Set V) ∧ v ∈ ({β 0, β 1, β 2} : Set V))) →
          ¬ VertexComplete G u Y → ¬ VertexComplete G v Y →
          IsAntipathFrom G S u v → (∀ x ∈ interior S, x ∈ Y) →
          pathLength Q ≤ pathLength S := by
    let α := fun i => b (σ i)
    let β := fun i => a (σ i)
    let R := fun i => (P (σ i)).reverse
    refine ⟨σ, true, α, β, R, interior Q, Q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro _ i; exact ⟨rfl, rfl, rfl⟩
    · exact PrismSymmetry.formPrism_swap (PrismSymmetry.formPrism_perm hprism σ)
    · intro i x hx; exact hPoutside (σ i) x (List.mem_reverse.mp hx)
    · intro i
      rw [PathBasics.pathLength_reverse]
      exact hPlength (σ i)
    · intro y hy
      exact PrismSymmetry.majorForPrism_swap.mpr
        ((PrismSymmetry.majorForPrism_perm σ).mpr (hYmajor y hy))
    · simpa [α, hu, hv] using hshape
    · simpa [α, hu, hv] using hanti
    · exact hint
    · simpa [α, hu] using hnu
    · simpa [α, hv] using hnv
    · intro x y S hxy hside hx hy hS hSint
      apply hmin x y S
      refine ⟨hxy, ?_, hx, hy, hS, hSint⟩
      rcases hside with hside | hside
      · exact Or.inr (by simpa only [α, PrismSymmetry.triple_perm b σ] using hside)
      · exact Or.inl (by simpa only [β, PrismSymmetry.triple_perm a σ] using hside)
  rcases hside with hA | hB
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with ⟨(hu0 | hu1 | hu2), (hv0 | hv1 | hv2)⟩
    · exact (huv (hu0.trans hv0.symm)).elim
    · exact finishA (Equiv.refl _) hu0 hv1
    · exact finishA (Equiv.swap (1 : Fin 3) 2) hu0 (by simpa using hv2)
    · exact finishA (Equiv.swap (0 : Fin 3) 1) (by simpa using hu1) (by simpa using hv0)
    · exact (huv (hu1.trans hv1.symm)).elim
    · exact finishA ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1))
        (by simpa using hu1) (by simpa using hv2)
    · exact finishA ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2))
        (by simpa using hu2) (by simpa using hv0)
    · exact finishA (Equiv.swap (0 : Fin 3) 2) (by simpa using hu2) (by simpa using hv1)
    · exact (huv (hu2.trans hv2.symm)).elim
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
    rcases hB with ⟨(hu0 | hu1 | hu2), (hv0 | hv1 | hv2)⟩
    · exact (huv (hu0.trans hv0.symm)).elim
    · exact finishB (Equiv.refl _) hu0 hv1
    · exact finishB (Equiv.swap (1 : Fin 3) 2) hu0 (by simpa using hv2)
    · exact finishB (Equiv.swap (0 : Fin 3) 1) (by simpa using hu1) (by simpa using hv0)
    · exact (huv (hu1.trans hv1.symm)).elim
    · exact finishB ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1))
        (by simpa using hu1) (by simpa using hv2)
    · exact finishB ((Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap (1 : Fin 3) 2))
        (by simpa using hu2) (by simpa using hv0)
    · exact finishB (Equiv.swap (0 : Fin 3) 2) (by simpa using hu2) (by simpa using hv1)
    · exact (huv (hu2.trans hv2.symm)).elim

end Workspace.ProofLemmas
