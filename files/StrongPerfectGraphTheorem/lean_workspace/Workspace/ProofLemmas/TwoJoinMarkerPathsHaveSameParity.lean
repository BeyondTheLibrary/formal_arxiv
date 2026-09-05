import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.MinimumAttachmentPathInternalVerticesAvoidAttachments
import Workspace.ProofLemmas.OddCycleCliqueAndTwoColoringObstruction
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleSupportCycleIso
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.PerfectInducedSubgraph
import Workspace.ProofLemmas.CliqueNumOfInducedSet

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core

namespace TwoJoinMarkerPathsHaveSameParityAux

/-- Perfection is inherited by an induced subgraph on a *subset* of the ambient
vertex set (the "heredity" step of §1 of the detailed proof). -/
theorem perfect_induce_subset {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (Y S : Set W) (hSY : S ⊆ Y)
    (h : SPGT.IsPerfect (K.induce Y)) : SPGT.IsPerfect (K.induce S) := by
  classical
  have h2 := Workspace.ProofLemmas.PerfectInducedSubgraph (K.induce Y)
    {y : ↥Y | (y : W) ∈ S} h
  let e : (K.induce Y).induce {y : ↥Y | (y : W) ∈ S} ≃g
      K.induce (Subtype.val '' {y : ↥Y | (y : W) ∈ S}) :=
    { Equiv.Set.image (Subtype.val : ↥Y → W) {y : ↥Y | (y : W) ∈ S} Subtype.val_injective with
      map_rel_iff' := by
        intro a b
        rfl }
  have himg : (Subtype.val '' {y : ↥Y | (y : W) ∈ S}) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSY hx⟩, hx, rfl⟩
  have hfin := Workspace.ProofLemmas.IsoTransport.isPerfect_of_iso e h2
  rwa [himg] at hfin

end TwoJoinMarkerPathsHaveSameParityAux

open TwoJoinMarkerPathsHaveSameParityAux

/-- Minimum attachment paths on the two sides of a connected two-join have
the same parity whenever the first marker-path block is perfect. -/
theorem TwoJoinMarkerPathsHaveSameParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V)
    (X₁ X₂ A₁ B₁ A₂ B₂ : Set V)
    (hsides : Disjoint X₁ X₂)
    (hA₁ : A₁ ⊆ X₁) (hB₁ : B₁ ⊆ X₁)
    (hA₂ : A₂ ⊆ X₂) (hB₂ : B₂ ⊆ X₂)
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hcross : ∀ u ∈ X₁, ∀ v ∈ X₂,
      F.Adj u v ↔ (u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂))
    (Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ : V)
    (ha₁ : a₁ ∈ A₁) (hb₁ : b₁ ∈ B₁)
    (ha₂ : a₂ ∈ A₂) (hb₂ : b₂ ∈ B₂)
    (hQ₁ : SPGT.IsPathFrom F Q₁ a₁ b₁)
    (hQ₂ : SPGT.IsPathFrom F Q₂ a₂ b₂)
    (hQ₁X₁ : ∀ v ∈ Q₁, v ∈ X₁)
    (hQ₂X₂ : ∀ v ∈ Q₂, v ∈ X₂)
    (hmin₁ : ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ p : List V,
      SPGT.IsPathFrom F p a b → (∀ v ∈ p, v ∈ X₁) →
        SPGT.pathLength Q₁ ≤ SPGT.pathLength p)
    (hmin₂ : ∀ a ∈ A₂, ∀ b ∈ B₂, ∀ p : List V,
      SPGT.IsPathFrom F p a b → (∀ v ∈ p, v ∈ X₂) →
        SPGT.pathLength Q₂ ≤ SPGT.pathLength p)
    (hblock₁ : SPGT.IsPerfect (F.induce (X₁ ∪ {v : V | v ∈ Q₂}))) :
    SPGT.pathLength Q₁ % 2 = SPGT.pathLength Q₂ % 2 := by
  classical
  -- §2: the exact structure of each minimum attachment path
  obtain ⟨-, hlen₁, -, hAmem₁, hBmem₁⟩ :=
    MinimumAttachmentPathInternalVerticesAvoidAttachments F X₁ A₁ B₁ a₁ b₁ Q₁
      hA₁ hB₁ hAB₁ ha₁ hb₁ hQ₁ hQ₁X₁ hmin₁
  obtain ⟨-, hlen₂, -, hAmem₂, hBmem₂⟩ :=
    MinimumAttachmentPathInternalVerticesAvoidAttachments F X₂ A₂ B₂ a₂ b₂ Q₂
      hA₂ hB₂ hAB₂ ha₂ hb₂ hQ₂ hQ₂X₂ hmin₂
  -- §3: suppose the two lengths have different parity
  by_contra hpar
  -- the two path vertex sets are disjoint
  have hdisjPQ : ∀ x ∈ Q₁, x ∉ Q₂ := by
    intro x hx hx2
    exact Set.disjoint_left.mp hsides (hQ₁X₁ x hx) (hQ₂X₂ x hx2)
  have hdisj : ∀ x ∈ Q₁, x ∉ Q₂.reverse := by
    intro x hx
    rw [List.mem_reverse]
    exact hdisjPQ x hx
  -- §2.5: the exact cross-edge pattern between the two marker paths
  have hcross' : ∀ x ∈ Q₁, ∀ y ∈ Q₂.reverse,
      (F.Adj x y ↔ (x = b₁ ∧ y = b₂) ∨ (x = a₁ ∧ y = a₂)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    have h := hcross x (hQ₁X₁ x hx) y (hQ₂X₂ y hy)
    rw [hAmem₁ x hx, hAmem₂ y hy, hBmem₁ x hx, hBmem₂ y hy] at h
    rw [h]
    tauto
  -- §3: the cyclic concatenation is a hole
  have hQ₂rev : SPGT.IsPathFrom F Q₂.reverse b₂ a₂ := PathBasics.isPathFrom_reverse hQ₂
  have hlQ₁ : Q₁.length = SPGT.pathLength Q₁ + 1 :=
    PathBasics.length_eq_pathLength_add_one hQ₁.1
  have hlQ₂ : Q₂.length = SPGT.pathLength Q₂ + 1 :=
    PathBasics.length_eq_pathLength_add_one hQ₂.1
  have hrevlen : Q₂.reverse.length = Q₂.length := List.length_reverse
  have hlenC : (Q₁ ++ Q₂.reverse).length = Q₁.length + Q₂.length := by
    rw [List.length_append, hrevlen]
  have hhole : SPGT.IsHoleList F (Q₁ ++ Q₂.reverse) :=
    PathGlue.glue_hole hQ₁ hQ₂rev hdisj hcross' (by omega)
  set c : List V := Q₁ ++ Q₂.reverse with hc
  have hcL : c.length = SPGT.pathLength Q₁ + SPGT.pathLength Q₂ + 2 := by
    rw [hc, hlenC]; omega
  have hodd : Odd c.length := by
    rw [Nat.odd_iff, hcL]
    omega
  have hge5 : 5 ≤ c.length := by
    rw [hcL]
    omega
  -- the hole lives inside the first marker block
  have hsub : (↑c.toFinset : Set V) ⊆ X₁ ∪ {v : V | v ∈ Q₂} := by
    intro x hx
    simp only [Finset.coe_sort_coe, Set.mem_setOf_eq, Finset.mem_coe,
      List.mem_toFinset] at hx
    rw [hc, List.mem_append, List.mem_reverse] at hx
    rcases hx with hx | hx
    · exact Or.inl (hQ₁X₁ x hx)
    · exact Or.inr hx
  have hperfS : SPGT.IsPerfect (F.induce (↑c.toFinset : Set V)) :=
    perfect_induce_subset F (X₁ ∪ {v : V | v ∈ Q₂}) (↑c.toFinset : Set V) hsub hblock₁
  -- transport to the Mathlib cycle graph
  obtain ⟨e, -⟩ := Workspace.ProofLemmas.HoleSupportCycleIso F c hhole
  obtain ⟨hcliq, hnotcol⟩ := OddCycleCliqueAndTwoColoringObstruction c.length hge5 hodd
  have hcliq2 : (F.induce (↑c.toFinset : Set V)).cliqueNum = 2 := by
    rw [← Workspace.ProofLemmas.IsoTransport.cliqueNum_iso e]
    exact hcliq
  have hchrom : (F.induce (↑c.toFinset : Set V)).chromaticNumber
      = (((F.induce (↑c.toFinset : Set V)).cliqueNum : ℕ) : ℕ∞) :=
    Workspace.ProofLemmas.CliqueNumOfInducedSet.chromaticNumber_eq_cliqueNum_of_isPerfect
      _ hperfS
  have hchrom2 : (SimpleGraph.cycleGraph c.length).chromaticNumber ≤ (2 : ℕ) := by
    rw [Workspace.ProofLemmas.IsoTransport.chromaticNumber_iso e, hchrom, hcliq2]
  exact hnotcol (SimpleGraph.chromaticNumber_le_iff_colorable.mp hchrom2)

end Workspace.ProofLemmas
