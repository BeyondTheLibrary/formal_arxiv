import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Types.Replication
import Workspace.Types.Classes
import Workspace.Types.Prisms
import Workspace.ProofLemmas.ConnectedTwoJoinBlocksPerfectIff
import Workspace.ProofLemmas.SpanningMinimumAttachmentPathHasDegreeTwoVertex
import Workspace.ProofLemmas.MinimumImperfectHasNoDegreeTwoVertex
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect
import Workspace.Statements.S01.Thm_E5_perfect_implies_berge

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Workspace.MainTheorem

open Workspace.Types.Core Workspace.Types.Decompositions
open Workspace.Types.BasicClasses Workspace.Types.Replication
open Workspace.Types.Classes Workspace.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem side_three_le
    (G : SimpleGraph V) (X A B : Set V)
    (hA : A ⊆ X) (hB : B ⊆ X)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : Disjoint A B)
    (a b : V) (ha : a ∈ A) (hb : b ∈ B)
    (Q : List V) (hQ : SPGT.IsPathFrom G Q a b)
    (hQX : ∀ z ∈ Q, z ∈ X)
    (hsidepath : ∀ a b : V, A = {a} → B = {b} → ∀ p : List V,
      SPGT.IsPathFrom G p a b → {v : V | v ∈ p} = X →
        Odd (SPGT.pathLength p) ∧ 3 ≤ SPGT.pathLength p) :
    3 ≤ X.ncard := by
  classical
  by_contra hthree
  have hle : X.ncard ≤ 2 := by omega
  have hab : a ≠ b := by
    intro hab
    subst b
    exact (Set.disjoint_left.1 hAB) ha hb
  have haX : a ∈ X := hA ha
  have hbX : b ∈ X := hB hb
  have habsub : ({a, b} : Set V) ⊆ X := by
    intro x hx
    rcases hx with (rfl | rfl)
    · exact haX
    · exact hbX
  have hge : 2 ≤ X.ncard := by
    have h := Set.ncard_le_ncard habsub
    simpa [hab] using h
  have hX : ({a, b} : Set V) = X := by
    exact (Set.subset_iff_eq_of_ncard_le (s := ({a, b} : Set V)) (t := X)
      (by simpa [hab] using hle)).mp habsub
  have hAeq : A = {a} := by
    ext x
    constructor
    · intro hx
      have hxX := hA hx
      rw [← hX] at hxX
      rcases hxX with (rfl | rfl)
      · rfl
      · exact False.elim ((Set.disjoint_left.1 hAB) hx hb)
    · intro hx
      simpa using hx ▸ ha
  have hBeq : B = {b} := by
    ext x
    constructor
    · intro hx
      have hxX := hB hx
      rw [← hX] at hxX
      rcases hxX with (rfl | rfl)
      · exact False.elim ((Set.disjoint_left.1 hAB) ha hx)
      · rfl
    · intro hx
      simpa using hx ▸ hb
  have hsupport : {v : V | v ∈ Q} = X := by
    rw [← hX]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hx
      have hxX := hQX x hx
      rw [← hX] at hxX
      exact hxX
    · rintro (rfl | rfl)
      · exact List.mem_of_mem_head? hQ.2.1
      · exact List.mem_of_mem_getLast? hQ.2.2
  have hlong : 3 ≤ SPGT.pathLength Q :=
    (hsidepath a b hAeq hBeq Q hQ hsupport).2
  have hfinSub : Q.toFinset ⊆ ({a, b} : Finset V) := by
    intro x hx
    have hxQ : x ∈ Q := by simpa using hx
    have hxX := hQX x hxQ
    rw [← hX] at hxX
    simpa using hxX
  have hlen : Q.length ≤ 2 := by
    rw [← List.toFinset_card_of_nodup hQ.1.2.1]
    have hc := Finset.card_le_card hfinSub
    simpa [hab] using hc
  simp only [SPGT.pathLength] at hlong
  omega

theorem thm_E2_no_proper_2_join_in_minimum_imperfect
    (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G) :
    ¬ SPGT.AdmitsProper2Join G := by
  classical
  intro hJoin
  have hNotPerfect : ¬ SPGT.IsPerfect G :=
    _root_.Workspace.ProofLemmas.IsoTransport.minimumImperfect_not_perfect hG
      (fun h => thm_E5_perfect_implies_berge G h)
  have hBerge : SPGT.Berge G :=
    _root_.Workspace.ProofLemmas.IsoTransport.minimumImperfect_berge hG
      (fun h => thm_E5_perfect_implies_berge G h)
  rcases hJoin with
    ⟨X₁, X₂, hUnion, hDisj, A₁, B₁, A₂, B₂,
      hA₁, hB₁, hA₂, hB₂, hA₁ne, hB₁ne, hA₂ne, hB₂ne,
      hAB₁, hAB₂, hcross, hcomp₁, hcomp₂, hsidepath₁, hsidepath₂⟩

  have hex₁ : ∃ n : ℕ, ∃ a ∈ A₁, ∃ b ∈ B₁, ∃ p : List V,
      SPGT.IsPathFrom G p a b ∧ (∀ z ∈ p, z ∈ X₁) ∧ SPGT.pathLength p = n := by
    obtain ⟨a, ha⟩ := hA₁ne
    obtain ⟨C, hC, haC⟩ :=
      _root_.Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G X₁ (hA₁ ha)
    obtain ⟨b, hbC, hb⟩ := (hcomp₁ C hC).2
    obtain ⟨p, hp, hpC⟩ :=
      _root_.Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hC.2.1 haC hbC
    exact ⟨SPGT.pathLength p, a, ha, b, hb, p, hp,
      fun z hz => hC.1 (hpC z hz), rfl⟩
  obtain ⟨a₁, ha₁, b₁, hb₁, Q₁, hQ₁, hQ₁X₁, hQ₁len⟩ := Nat.find_spec hex₁
  have hmin₁ : ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ p : List V,
      SPGT.IsPathFrom G p a b → (∀ z ∈ p, z ∈ X₁) →
        SPGT.pathLength Q₁ ≤ SPGT.pathLength p := by
    intro a ha b hb p hp hpX
    rw [hQ₁len]
    exact Nat.find_min' hex₁ ⟨a, ha, b, hb, p, hp, hpX, rfl⟩

  have hex₂ : ∃ n : ℕ, ∃ a ∈ A₂, ∃ b ∈ B₂, ∃ p : List V,
      SPGT.IsPathFrom G p a b ∧ (∀ z ∈ p, z ∈ X₂) ∧ SPGT.pathLength p = n := by
    obtain ⟨a, ha⟩ := hA₂ne
    obtain ⟨C, hC, haC⟩ :=
      _root_.Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G X₂ (hA₂ ha)
    obtain ⟨b, hbC, hb⟩ := (hcomp₂ C hC).2
    obtain ⟨p, hp, hpC⟩ :=
      _root_.Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        hC.2.1 haC hbC
    exact ⟨SPGT.pathLength p, a, ha, b, hb, p, hp,
      fun z hz => hC.1 (hpC z hz), rfl⟩
  obtain ⟨a₂, ha₂, b₂, hb₂, Q₂, hQ₂, hQ₂X₂, hQ₂len⟩ := Nat.find_spec hex₂
  have hmin₂ : ∀ a ∈ A₂, ∀ b ∈ B₂, ∀ p : List V,
      SPGT.IsPathFrom G p a b → (∀ z ∈ p, z ∈ X₂) →
        SPGT.pathLength Q₂ ≤ SPGT.pathLength p := by
    intro a ha b hb p hp hpX
    rw [hQ₂len]
    exact Nat.find_min' hex₂ ⟨a, ha, b, hb, p, hp, hpX, rfl⟩

  have hcard₁ : 3 ≤ X₁.ncard :=
    side_three_le G X₁ A₁ B₁ hA₁ hB₁ hA₁ne hB₁ne hAB₁
      a₁ b₁ ha₁ hb₁ Q₁ hQ₁ hQ₁X₁ hsidepath₁
  have hcard₂ : 3 ≤ X₂.ncard :=
    side_three_le G X₂ A₂ B₂ hA₂ hB₂ hA₂ne hB₂ne hAB₂
      a₂ b₂ ha₂ hb₂ Q₂ hQ₂ hQ₂X₂ hsidepath₂
  have hblocks := _root_.Workspace.ProofLemmas.ConnectedTwoJoinBlocksPerfectIff
    G X₁ X₂ A₁ B₁ A₂ B₂ hUnion hDisj hA₁ hB₁ hA₂ hB₂
    hA₁ne hB₁ne hA₂ne hB₂ne hAB₁ hAB₂ hcross hcard₁ hcard₂
    Q₁ Q₂ a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂ hQ₁ hQ₂
    hQ₁X₁ hQ₂X₂ hmin₁ hmin₂
  have hnotBoth : ¬ (SPGT.IsPerfect (G.induce (X₁ ∪ {v : V | v ∈ Q₂})) ∧
      SPGT.IsPerfect (G.induce (X₂ ∪ {v : V | v ∈ Q₁}))) := by
    intro h
    exact hNotPerfect (hblocks.mpr h)
  rw [not_and_or] at hnotBoth
  rcases hnotBoth with hbad₁ | hbad₂
  · have hspan₂ : {v : V | v ∈ Q₂} = X₂ := by
      have hcover : X₁ ∪ {v : V | v ∈ Q₂} = Set.univ := by
        by_contra hproper
        exact hbad₁
          (_root_.Workspace.ProofLemmas.SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ
            hG hproper)
      apply Set.Subset.antisymm
      · intro x hx
        exact hQ₂X₂ x hx
      · intro x hx
        have hall : x ∈ X₁ ∪ {v : V | v ∈ Q₂} := by
          rw [hcover]
          trivial
        rcases hall with hx₁ | hxQ
        · exact False.elim ((Set.disjoint_left.1 hDisj) hx₁ hx)
        · exact hxQ
    have houtside : ∀ z ∈ X₂, z ∉ A₂ → z ∉ B₂ →
        ∀ u, u ∉ X₂ → ¬ G.Adj z u := by
      intro z hzX₂ hzA₂ hzB₂ u huX₂ hzu
      have huX₁ : u ∈ X₁ := by
        have hu : u ∈ X₁ ∪ X₂ := by
          rw [hUnion]
          trivial
        exact hu.resolve_right huX₂
      rcases (hcross u huX₁ z hzX₂).mp hzu.symm with hA | hB
      · exact hzA₂ hA.2
      · exact hzB₂ hB.2
    obtain ⟨v, hv⟩ :=
      _root_.Workspace.ProofLemmas.SpanningMinimumAttachmentPathHasDegreeTwoVertex
        G X₂ A₂ B₂ a₂ b₂ Q₂ hA₂ hB₂ ha₂ hb₂ hAB₂ hQ₂ hmin₂
        hspan₂ hsidepath₂ houtside
    exact (_root_.Workspace.ProofLemmas.MinimumImperfectHasNoDegreeTwoVertex G hG v) hv
  · have hspan₁ : {v : V | v ∈ Q₁} = X₁ := by
      have hcover : X₂ ∪ {v : V | v ∈ Q₁} = Set.univ := by
        by_contra hproper
        exact hbad₂
          (_root_.Workspace.ProofLemmas.SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ
            hG hproper)
      apply Set.Subset.antisymm
      · intro x hx
        exact hQ₁X₁ x hx
      · intro x hx
        have hall : x ∈ X₂ ∪ {v : V | v ∈ Q₁} := by
          rw [hcover]
          trivial
        rcases hall with hx₂ | hxQ
        · exact False.elim ((Set.disjoint_left.1 hDisj) hx hx₂)
        · exact hxQ
    have houtside : ∀ z ∈ X₁, z ∉ A₁ → z ∉ B₁ →
        ∀ u, u ∉ X₁ → ¬ G.Adj z u := by
      intro z hzX₁ hzA₁ hzB₁ u huX₁ hzu
      have huX₂ : u ∈ X₂ := by
        have hu : u ∈ X₁ ∪ X₂ := by
          rw [hUnion]
          trivial
        exact hu.resolve_left huX₁
      rcases (hcross z hzX₁ u huX₂).mp hzu with hA | hB
      · exact hzA₁ hA.1
      · exact hzB₁ hB.1
    obtain ⟨v, hv⟩ :=
      _root_.Workspace.ProofLemmas.SpanningMinimumAttachmentPathHasDegreeTwoVertex
        G X₁ A₁ B₁ a₁ b₁ Q₁ hA₁ hB₁ ha₁ hb₁ hAB₁ hQ₁ hmin₁
        hspan₁ hsidepath₁ houtside
    exact (_root_.Workspace.ProofLemmas.MinimumImperfectHasNoDegreeTwoVertex G hG v) hv

end SPGT

end Workspace.MainTheorem
