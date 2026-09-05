import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismSymmetry

/-!
# Setup for the proof of 10.5

The proof of 10.5 chooses a prism and a nonempty anticonnected set of major
vertices so that as few triangle vertices as possible are complete to the
set.  It then enlarges the set while keeping the prism fixed.  This file
packages that finite choice and the elementary facts used with it.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm105Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of triangle vertices of a labelled prism that are `Y`-complete. -/
noncomputable def triangleCompleteCount (G : SimpleGraph V) (a b : Fin 3 → V)
    (Y : Set V) : ℕ :=
  (({a 0, a 1, a 2} : Set V) ∩ {x : V | VertexComplete G x Y}).ncard +
    (({b 0, b 1, b 2} : Set V) ∩ {x : V | VertexComplete G x Y}).ncard

/-- The data over which the opening minimisation in 10.5 is taken. -/
def GoodChoice (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (Y : Set V) : Prop :=
  IsEvenPrism G a b (R 0) (R 1) (R 2) ∧ Y.Nonempty ∧
    AnticonnectedSet G Y ∧ ∀ y ∈ Y, MajorForPrism G a b y

/-- Completeness to a larger set can only lower the number of complete triangle vertices. -/
theorem triangleCompleteCount_mono (G : SimpleGraph V) (a b : Fin 3 → V)
    {Y Y' : Set V} (hYY' : Y ⊆ Y') :
    triangleCompleteCount G a b Y' ≤ triangleCompleteCount G a b Y := by
  unfold triangleCompleteCount
  have hcomplete : {x : V | VertexComplete G x Y'} ⊆ {x : V | VertexComplete G x Y} := by
    intro x hx y hy
    exact hx y (hYY' hy)
  have ha :
      (({a 0, a 1, a 2} : Set V) ∩ {x : V | VertexComplete G x Y'}).ncard ≤
        (({a 0, a 1, a 2} : Set V) ∩ {x : V | VertexComplete G x Y}).ncard :=
    Set.ncard_le_ncard (Set.inter_subset_inter_right _ hcomplete) (Set.toFinite _)
  have hb :
      (({b 0, b 1, b 2} : Set V) ∩ {x : V | VertexComplete G x Y'}).ncard ≤
        (({b 0, b 1, b 2} : Set V) ∩ {x : V | VertexComplete G x Y}).ncard :=
    Set.ncard_le_ncard (Set.inter_subset_inter_right _ hcomplete) (Set.toFinite _)
  omega

/-- Relabelling the three rungs does not change the number being minimised. -/
theorem triangleCompleteCount_perm (G : SimpleGraph V) (a b : Fin 3 → V) (Y : Set V)
    (sigma : Equiv.Perm (Fin 3)) :
    triangleCompleteCount G (fun i ↦ a (sigma i)) (fun i ↦ b (sigma i)) Y =
      triangleCompleteCount G a b Y := by
  unfold triangleCompleteCount
  rw [Workspace.ProofLemmas.PrismSymmetry.triple_perm a sigma,
    Workspace.ProofLemmas.PrismSymmetry.triple_perm b sigma]

/-- Exchanging the two triangles does not change the number being minimised. -/
theorem triangleCompleteCount_swap (G : SimpleGraph V) (a b : Fin 3 → V) (Y : Set V) :
    triangleCompleteCount G b a Y = triangleCompleteCount G a b Y := by
  unfold triangleCompleteCount
  omega

/-- A saturated three-element set contains one of its three pairs. -/
theorem two_members_of_saturated_triple (c : Fin 3 → V) (X : Set V)
    (hsat : 2 ≤ (({c 0, c 1, c 2} : Set V) ∩ X).ncard) :
    (c 0 ∈ X ∧ c 1 ∈ X) ∨ (c 0 ∈ X ∧ c 2 ∈ X) ∨
      (c 1 ∈ X ∧ c 2 ∈ X) := by
  classical
  by_cases h0 : c 0 ∈ X
  · by_cases h1 : c 1 ∈ X
    · exact Or.inl ⟨h0, h1⟩
    · by_cases h2 : c 2 ∈ X
      · exact Or.inr (Or.inl ⟨h0, h2⟩)
      · have hsub : (({c 0, c 1, c 2} : Set V) ∩ X) ⊆ {c 0} := by
          rintro x ⟨hx, hxX⟩
          rcases hx with rfl | rfl | rfl
          · exact rfl
          · exact False.elim (h1 hxX)
          · exact False.elim (h2 hxX)
        have hle : (({c 0, c 1, c 2} : Set V) ∩ X).ncard ≤ 1 := by
          calc
            _ ≤ ({c 0} : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
            _ = 1 := Set.ncard_singleton _
        omega
  · by_cases h1 : c 1 ∈ X
    · by_cases h2 : c 2 ∈ X
      · exact Or.inr (Or.inr ⟨h1, h2⟩)
      · have hsub : (({c 0, c 1, c 2} : Set V) ∩ X) ⊆ {c 1} := by
          rintro x ⟨hx, hxX⟩
          rcases hx with rfl | rfl | rfl
          · exact False.elim (h0 hxX)
          · exact rfl
          · exact False.elim (h2 hxX)
        have hle : (({c 0, c 1, c 2} : Set V) ∩ X).ncard ≤ 1 := by
          calc
            _ ≤ ({c 1} : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
            _ = 1 := Set.ncard_singleton _
        omega
    · have hsub : (({c 0, c 1, c 2} : Set V) ∩ X) ⊆ {c 2} := by
        rintro x ⟨hx, hxX⟩
        rcases hx with rfl | rfl | rfl
        · exact False.elim (h0 hxX)
        · exact False.elim (h1 hxX)
        · exact rfl
      have hle : (({c 0, c 1, c 2} : Set V) ∩ X).ncard ≤ 1 := by
        calc
          _ ≤ ({c 2} : Set V).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
          _ = 1 := Set.ncard_singleton _
      omega

/-- Replacing one complete triangle vertex by a non-complete vertex lowers the count by one. -/
theorem triangleCompleteCount_replace_left (G : SimpleGraph V) (a₀ a₁ a₂ f : V)
    (b : Fin 3 → V) (Y : Set V) (ha₀ : VertexComplete G a₀ Y)
    (hf : ¬ VertexComplete G f Y) (ha₀a₁ : a₀ ≠ a₁) (ha₀a₂ : a₀ ≠ a₂) :
    triangleCompleteCount G ![f, a₁, a₂] b Y + 1 =
      triangleCompleteCount G ![a₀, a₁, a₂] b Y := by
  unfold triangleCompleteCount
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  have hnot : a₀ ∉ ({a₁, a₂} : Set V) ∩ {x : V | VertexComplete G x Y} := by
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, not_and_or]
    exact Or.inl (by push Not; exact ⟨ha₀a₁, ha₀a₂⟩)
  have hold :
      ({a₀, a₁, a₂} : Set V) ∩ {x : V | VertexComplete G x Y} =
        insert a₀ (({a₁, a₂} : Set V) ∩ {x : V | VertexComplete G x Y}) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl | hx, hc⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hx, hc⟩
    · rintro (rfl | ⟨hx, hc⟩)
      · exact ⟨Or.inl rfl, ha₀⟩
      · exact ⟨Or.inr hx, hc⟩
  have hnew :
      ({f, a₁, a₂} : Set V) ∩ {x : V | VertexComplete G x Y} =
        ({a₁, a₂} : Set V) ∩ {x : V | VertexComplete G x Y} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨rfl | hx, hc⟩
      · exact False.elim (hf hc)
      · exact ⟨hx, hc⟩
    · rintro ⟨hx, hc⟩
      exact ⟨Or.inr hx, hc⟩
  rw [hold, hnew, Set.ncard_insert_of_notMem hnot]
  omega

/-- A maximal anticonnected superset of a given finite anticonnected set exists. -/
theorem exists_maximal_anticonnected_superset (G : SimpleGraph V) (P : V → Prop)
    (Y : Set V) (hYanti : AnticonnectedSet G Y) (hYP : ∀ y ∈ Y, P y) :
    ∃ Y' : Set V, Y ⊆ Y' ∧ AnticonnectedSet G Y' ∧ (∀ y ∈ Y', P y) ∧
      ∀ Z : Set V, Y' ⊆ Z → AnticonnectedSet G Z → (∀ z ∈ Z, P z) → Z = Y' := by
  classical
  let C : Set (Set V) :=
    {Z : Set V | Y ⊆ Z ∧ AnticonnectedSet G Z ∧ ∀ z ∈ Z, P z}
  have hYC : Y ∈ C := ⟨subset_rfl, hYanti, hYP⟩
  obtain ⟨Y', hY'max⟩ := Set.Finite.exists_maximal (Set.toFinite C) ⟨Y, hYC⟩
  obtain ⟨hYY', hY'anti, hY'P⟩ := hY'max.1
  refine ⟨Y', hYY', hY'anti, hY'P, ?_⟩
  intro Z hsub hanti hP
  have hZC : Z ∈ C := ⟨hYY'.trans hsub, hanti, hP⟩
  exact Set.Subset.antisymm (hY'max.2 hZC hsub) hsub

/-- The opening choice in the proof of 10.5, including both forms of optimality. -/
theorem exists_optimal_choice (G : SimpleGraph V) (a₀ b₀ : Fin 3 → V)
    (R₀ : Fin 3 → List V) (v₀ : V)
    (hprism₀ : IsEvenPrism G a₀ b₀ (R₀ 0) (R₀ 1) (R₀ 2))
    (hv₀ : MajorForPrism G a₀ b₀ v₀) :
    ∃ (a b : Fin 3 → V) (R : Fin 3 → List V) (Y : Set V),
      GoodChoice G a b R Y ∧
      (∀ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (Y' : Set V),
        GoodChoice G a' b' R' Y' →
          triangleCompleteCount G a b Y ≤ triangleCompleteCount G a' b' Y') ∧
      (∀ Z : Set V, Y ⊆ Z → AnticonnectedSet G Z →
        (∀ z ∈ Z, MajorForPrism G a b z) → Z = Y) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ (a b : Fin 3 → V) (R : Fin 3 → List V) (Y : Set V),
      GoodChoice G a b R Y ∧ n = triangleCompleteCount G a b Y
  have hsingleAnti : AnticonnectedSet G ({v₀} : Set V) := by
    intro x y
    have hxy : x = y := Subtype.ext (by simpa using (x.2.trans y.2.symm))
    exact hxy ▸ SimpleGraph.Reachable.refl x
  have hex : ∃ n, P n := by
    refine ⟨triangleCompleteCount G a₀ b₀ {v₀}, a₀, b₀, R₀, {v₀}, ?_, rfl⟩
    exact ⟨hprism₀, Set.singleton_nonempty v₀, hsingleAnti,
      fun y hy ↦ by
        have hyv : y = v₀ := by simpa using hy
        simpa [hyv] using hv₀⟩
  obtain ⟨a, b, R, Y₁, hgood₁, hcount₁⟩ := Nat.find_spec hex
  obtain ⟨Y, hY₁Y, hYanti, hYmajor, hYmax⟩ :=
    exists_maximal_anticonnected_superset G (fun y ↦ MajorForPrism G a b y)
      Y₁ hgood₁.2.2.1 hgood₁.2.2.2
  have hYne : Y.Nonempty := hgood₁.2.1.mono hY₁Y
  have hgood : GoodChoice G a b R Y := ⟨hgood₁.1, hYne, hYanti, hYmajor⟩
  have hmin₁ : ∀ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (Y' : Set V),
      GoodChoice G a' b' R' Y' →
        triangleCompleteCount G a b Y₁ ≤ triangleCompleteCount G a' b' Y' := by
    intro a' b' R' Y' hgood'
    rw [← hcount₁]
    exact Nat.find_min' hex ⟨a', b', R', Y', hgood', rfl⟩
  have heq : triangleCompleteCount G a b Y = triangleCompleteCount G a b Y₁ := by
    apply Nat.le_antisymm
    · exact triangleCompleteCount_mono G a b hY₁Y
    · exact hmin₁ a b R Y hgood
  refine ⟨a, b, R, Y, hgood, ?_, hYmax⟩
  intro a' b' R' Y' hgood'
  rw [heq]
  exact hmin₁ a' b' R' Y' hgood'

/-- A major vertex cannot lie on an even prism. -/
theorem major_not_mem_evenPrism (G : SimpleGraph V) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (hprism : IsEvenPrism G a b (R 0) (R 1) (R 2))
    (y : V) (hymajor : MajorForPrism G a b y) :
    y ∉ {x : V | x ∈ R 0} ∪ {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2} := by
  classical
  intro hyK
  obtain ⟨i, hyRi⟩ : ∃ i : Fin 3, y ∈ R i := by
    rcases hyK with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hform := hprism.1
  have hpath := Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hform i
  have hlenList := Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length hform i
  have heven : Even (pathLength (R i)) := by
    fin_cases i
    exacts [hprism.2.1, hprism.2.2.1, hprism.2.2.2]
  have hlenPath : 2 ≤ pathLength (R i) := by
    obtain ⟨k, hk⟩ := heven
    have hpos : 1 ≤ pathLength (R i) := by simp only [pathLength]; omega
    omega
  have hlen3 : 3 ≤ (R i).length := by simp only [pathLength] at hlenPath; omega
  have haMem : ∀ j : Fin 3, a j ∈ R j := fun j ↦
    Workspace.ProofLemmas.PathBasics.head_mem
      (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hform j).2.1
  have hbMem : ∀ j : Fin 3, b j ∈ R j := fun j ↦
    Workspace.ProofLemmas.PathBasics.getLast_mem
      (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hform j).2.2
  by_cases hyai : y = a i
  · have hBempty :
        ({b 0, b 1, b 2} : Set V) ∩ G.neighborSet y = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzB, hyz⟩
      rw [Workspace.ProofLemmas.PrismSymmetry.triple_eq_range] at hzB
      obtain ⟨j, rfl⟩ := hzB
      by_cases hij : i = j
      · subst j
        rw [hyai] at hyz
        have hn := Workspace.ProofLemmas.PathBasics.path_ends_not_adj hpath.1 hlen3
        rw [Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hpath.2.1 (by omega),
          Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hpath.2.2 (by omega)] at hn
        exact hn hyz
      · have hcross :=
          (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross hform hij
            y hyRi (b j) (hbMem j)).mp hyz
        rcases hcross with h | h
        · exact hform.2.2.1 j j (h.2.symm)
        · exact hform.2.2.1 i i (hyai.symm.trans h.1)
    have hzero : (({b 0, b 1, b 2} : Set V) ∩ G.neighborSet y).ncard = 0 := by
      rw [hBempty, Set.ncard_empty]
    exact (by omega : ¬ (2 ≤ (({b 0, b 1, b 2} : Set V) ∩ G.neighborSet y).ncard))
      hymajor.2
  · have hAsub :
        ({a 0, a 1, a 2} : Set V) ∩ G.neighborSet y ⊆ {a i} := by
      rintro z ⟨hzA, hyz⟩
      rw [Workspace.ProofLemmas.PrismSymmetry.triple_eq_range] at hzA
      obtain ⟨j, rfl⟩ := hzA
      by_cases hij : i = j
      · subst j
        exact rfl
      · have hcross :=
          (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross hform hij
            y hyRi (a j) (haMem j)).mp hyz
        rcases hcross with h | h
        · exact False.elim (hyai h.1)
        · exact False.elim (hform.2.2.1 j j h.2)
    have hle : (({a 0, a 1, a 2} : Set V) ∩ G.neighborSet y).ncard ≤ 1 := by
      calc
        _ ≤ ({a i} : Set V).ncard := Set.ncard_le_ncard hAsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    exact (by omega : ¬ (2 ≤ (({a 0, a 1, a 2} : Set V) ∩ G.neighborSet y).ncard))
      hymajor.1

end Workspace.ProofLemmas.Thm105Setup
