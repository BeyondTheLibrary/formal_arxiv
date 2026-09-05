import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.DoubleDiamond
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.FiveHoleBasics
import Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore

/-!
# 14.2: the full `A`--`B` attachment case

This file isolates the short branch in the last paragraph of the proof of 14.2 where the
paper's sets `A'` and `B'` are all of `A` and `B`:

> *"If `A' = A` and `B' = B`, then `f₁` is `A`-complete, and so there are no edges between
> `{f₁, …, f_{k-1}}` and `B`, from the minimality of `k`; and similarly `f_k` is
> `B`-complete and there are no edges between `{f₂, …, f_k}` and `A`.  Choose a square
> `a₁-b₁-b₂-a₂-a₁`; then `a₁-b₁`, `a₂-b₂`, `f₁-⋯-f_k` form a prism, so `k = 2`, and we can
> add `f₁` to `C` and `f₂` to `D`, contrary to the maximality of the cube."*

The extra `hCD` hypothesis is the ambient fact, available in this branch of 14.2 from
`X ⊆ A ∪ B`, that the path in the outside component is anticomplete to `C ∪ D`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm142FullCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore

/-- The `A' = A`, `B' = B` branch in the printed proof of 14.2 is impossible.

The two quantified completeness hypotheses use an explicit bound proof so that callers do not
have to transport `GetElem` proof terms.  The two non-neighbour hypotheses are precisely the
endpoint restrictions supplied by the minimal choice of the attachment path. -/
theorem full_case_false {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF5 G)
    (A B C D : Set V) (hcube : MaximalCube G A B C D)
    {f : List V} (hfpath : IsPathList G f) (hlen : 2 ≤ f.length)
    (hfout : ∀ z ∈ f, z ∉ A ∪ B ∪ C ∪ D)
    (hAcomplete : ∀ a ∈ A, ∀ h0 : 0 < f.length, G.Adj (f[0]'h0) a)
    (hBcomplete : ∀ b ∈ B, ∀ hlast : f.length - 1 < f.length,
      G.Adj (f[f.length - 1]'hlast) b)
    (hnoB : ∀ b ∈ B, ∀ (i : ℕ) (hi : i < f.length), i < f.length - 1 →
      ¬ G.Adj b (f[i]'hi))
    (hnoA : ∀ a ∈ A, ∀ (i : ℕ) (hi : i < f.length), 0 < i →
      ¬ G.Adj a (f[i]'hi))
    (hCD : Anticomplete G (C ∪ D) {z : V | z ∈ f}) : False := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  have hfpos : 0 < f.length := by omega
  have hlast : f.length - 1 < f.length := by omega
  have hfnd : f.Nodup := hfpath.2.1
  have hmA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inl h))
  have hmB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inl (Or.inr h))
  have hmC : ∀ {u : V}, u ∈ C → u ∈ A ∪ B ∪ C ∪ D :=
    fun h => Or.inl (Or.inr h)
  have hmD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun h => Or.inr h
  have hfne : ∀ z ∈ f, ∀ w, w ∈ A ∪ B ∪ C ∪ D → z ≠ w := by
    rintro z hz w hw rfl
    exact hfout z hz hw

  -- PAPER: *"Choose a square `a₁-b₁-b₂-a₂-a₁`."*
  obtain ⟨a₁, ha₁A⟩ := nA
  obtain ⟨b₁, b₂, a₂, hsq⟩ := exists_square_of_mem_left sAB ha₁A
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq

  have hcross12 : ∀ u ∈ [a₁, b₁], ∀ v ∈ [a₂, b₂],
      (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => e30.symm⟩
    · exact ⟨fun hadj => absurd hadj n02,
        by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [absurd h ne23, absurd h ne01]⟩
    · exact ⟨fun hadj => absurd hadj n13,
        by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [absurd h ne01.symm, absurd h ne23.symm]⟩
    · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => e12⟩

  have hcross13 : ∀ u ∈ [a₁, b₁], ∀ v ∈ f,
      (G.Adj u v ↔ (u = a₁ ∧ v = f[0]'hfpos) ∨
        (u = b₁ ∧ v = f[f.length - 1]'hlast)) := by
    intro u hu v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with hua | hub
    · subst u
      constructor
      · intro hadj
        have hi0 : i = 0 := by
          by_contra hi0
          exact hnoA a₁ ha₁A i hi (by omega) hadj
        exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr hi0⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · rw [h]
          exact (hAcomplete a₁ ha₁A hfpos).symm
        · exact absurd h ne01
    · subst u
      constructor
      · intro hadj
        have hilast : i = f.length - 1 := by
          by_contra hilast
          exact hnoB b₁ hb₁B i hi (by omega) hadj
        exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hi hlast).mpr hilast⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h ne01.symm
        · rw [h]
          exact (hBcomplete b₁ hb₁B hlast).symm

  have hcross23 : ∀ u ∈ [a₂, b₂], ∀ v ∈ f,
      (G.Adj u v ↔ (u = a₂ ∧ v = f[0]'hfpos) ∨
        (u = b₂ ∧ v = f[f.length - 1]'hlast)) := by
    intro u hu v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with hua | hub
    · subst u
      constructor
      · intro hadj
        have hi0 : i = 0 := by
          by_contra hi0
          exact hnoA a₂ ha₂A i hi (by omega) hadj
        exact Or.inl ⟨rfl, (getElem_eq_iff hfnd hi hfpos).mpr hi0⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · rw [h]
          exact (hAcomplete a₂ ha₂A hfpos).symm
        · exact absurd h ne23.symm
    · subst u
      constructor
      · intro hadj
        have hilast : i = f.length - 1 := by
          by_contra hilast
          exact hnoB b₂ hb₂B i hi (by omega) hadj
        exact Or.inr ⟨rfl, (getElem_eq_iff hfnd hi hlast).mpr hilast⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h ne23
        · rw [h]
          exact (hBcomplete b₂ hb₂B hlast).symm

  -- PAPER: the two square edges and `f` form a prism.
  have hprism : FormPrism G ![a₁, a₂, f[0]'hfpos]
      ![b₁, b₂, f[f.length - 1]'hlast] [a₁, b₁] [a₂, b₂] f := by
    refine formPrism_of_data e30.symm (hAcomplete a₁ ha₁A hfpos).symm
      (hAcomplete a₂ ha₂A hfpos).symm e12
      (hBcomplete b₁ hb₁B hlast).symm (hBcomplete b₂ hb₂B hlast).symm
      ne01 ne02 (hfne _ (List.getElem_mem hlast) a₁ (hmA ha₁A)).symm
      ne13.symm ne23.symm (hfne _ (List.getElem_mem hlast) a₂ (hmA ha₂A)).symm
      (hfne _ (List.getElem_mem hfpos) b₁ (hmB hb₁B))
      (hfne _ (List.getElem_mem hfpos) b₂ (hmB hb₂B)) ?_
      ⟨PathBasics.isPathList_pair e01, rfl, rfl⟩
      ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩
      (isPathFrom_self hfpath hfpos) hcross12 hcross13 hcross23
    intro he
    have := (getElem_eq_iff hfnd hfpos hlast).mp he
    omega

  -- PAPER: F5 has no long prism, so the third rung has just two vertices.
  have hflen : f.length = 2 := by
    have hle : f.length ≤ 2 := by
      by_contra hle
      have hlong : 1 < pathLength f := by simp [pathLength]; omega
      exact hG.2.1 ⟨_, _, _, _, _, hprism, Or.inr (Or.inr hlong)⟩
    omega
  have hi1 : 1 < f.length := by omega
  have hf01 : G.Adj (f[0]'hfpos) (f[1]'hi1) := by
    rw [PathBasics.path_adj_iff hfpath hfpos hi1]
    omega
  have hlast_eq_one : f[f.length - 1]'hlast = f[1]'hi1 :=
    (getElem_eq_iff hfnd hlast hi1).mpr (by omega)

  -- A chord of an old antisquare supplies the old `C`--`D` edge needed by the new one.
  obtain ⟨d, hdD⟩ := nD
  obtain ⟨c, hcC, hcd⟩ := exists_adj_of_mem_right dCD sCD hdD
  have hf0D : ∀ z ∈ D, ¬ G.Adj (f[0]'hfpos) z := by
    intro z hz hadj
    exact hCD z (Or.inr hz) (f[0]'hfpos) (List.getElem_mem hfpos) hadj.symm
  have hf1D : ∀ z ∈ D, ¬ G.Adj (f[1]'hi1) z := by
    intro z hz hadj
    exact hCD z (Or.inr hz) (f[1]'hi1) (List.getElem_mem hi1) hadj.symm
  have hf0C : ∀ z ∈ C, ¬ G.Adj (f[0]'hfpos) z := by
    intro z hz hadj
    exact hCD z (Or.inl hz) (f[0]'hfpos) (List.getElem_mem hfpos) hadj.symm
  have hf1C : ∀ z ∈ C, ¬ G.Adj (f[1]'hi1) z := by
    intro z hz hadj
    exact hCD z (Or.inl hz) (f[1]'hi1) (List.getElem_mem hi1) hadj.symm

  have hnewSquare : IsSquare Gᶜ (C ∪ {f[0]'hfpos}) (D ∪ {f[1]'hi1})
      (f[0]'hfpos) d (f[1]'hi1) c := by
    refine ⟨?_, Or.inr rfl, Or.inl hcC, Or.inl hdD, Or.inr rfl⟩
    apply FiveHoleBasics.isHoleList_four
    · apply FiveHoleBasics.nodup_four
      · exact hfne _ (List.getElem_mem hfpos) d (hmD hdD)
      · intro he
        have := (getElem_eq_iff hfnd hfpos hi1).mp he
        omega
      · exact hfne _ (List.getElem_mem hfpos) c (hmC hcC)
      · exact (hfne _ (List.getElem_mem hi1) d (hmD hdD)).symm
      · intro he
        exact Set.disjoint_left.mp dCD hcC (he ▸ hdD)
      · exact hfne _ (List.getElem_mem hi1) c (hmC hcC)
    · simpa [SimpleGraph.compl_adj] using
        ⟨hfne _ (List.getElem_mem hfpos) d (hmD hdD), hf0D d hdD⟩
    · simpa [SimpleGraph.compl_adj] using
        ⟨(hfne _ (List.getElem_mem hi1) d (hmD hdD)).symm,
          fun h => hf1D d hdD h.symm⟩
    · simpa [SimpleGraph.compl_adj] using
        ⟨hfne _ (List.getElem_mem hi1) c (hmC hcC), hf1C c hcC⟩
    · simpa [SimpleGraph.compl_adj] using
        ⟨(hfne _ (List.getElem_mem hfpos) c (hmC hcC)).symm,
          fun h => hf0C c hcC h.symm⟩
    · simp only [SimpleGraph.compl_adj, not_and, not_not]
      exact fun _ => hf01
    · simp only [SimpleGraph.compl_adj, not_and, not_not]
      exact fun _ => hcd.symm

  have hsCD' : SquareConnected Gᶜ (C ∪ {f[0]'hfpos}) (D ∪ {f[1]'hi1}) := by
    apply squareConnected_adjoin_both sCD
      (fun h => hfout _ (List.getElem_mem hfpos) (hmC h))
      (fun h => hfout _ (List.getElem_mem hi1) (hmD h))
    · exact ⟨d, f[1]'hi1, c, hnewSquare, hcC⟩
    · exact ⟨c, d, f[0]'hfpos, isSquare_rev hnewSquare, hdD⟩

  -- PAPER: *"we can add `f₁` to `C` and `f₂` to `D`"*.
  have hnewCube : IsCube G A B (C ∪ {f[0]'hfpos}) (D ∪ {f[1]'hi1}) := by
    refine ⟨⟨⟨dAB, ?_, ?_, ?_, ?_, ?_⟩, ⟨a₁, ha₁A⟩, nB,
      nC.mono Set.subset_union_left, ⟨d, Or.inl hdD⟩⟩,
      ⟨?_, ?_, ?_, ?_⟩, sAB, hsCD'⟩
    · rw [Set.disjoint_left]
      rintro x hxA (hxC | hx0)
      · exact Set.disjoint_left.mp dAC hxA hxC
      · rw [Set.mem_singleton_iff] at hx0
        subst x
        exact hfout _ (List.getElem_mem hfpos) (hmA hxA)
    · rw [Set.disjoint_left]
      rintro x hxA (hxD | hx1)
      · exact Set.disjoint_left.mp dAD hxA hxD
      · rw [Set.mem_singleton_iff] at hx1
        subst x
        exact hfout _ (List.getElem_mem hi1) (hmA hxA)
    · rw [Set.disjoint_left]
      rintro x hxB (hxC | hx0)
      · exact Set.disjoint_left.mp dBC hxB hxC
      · rw [Set.mem_singleton_iff] at hx0
        subst x
        exact hfout _ (List.getElem_mem hfpos) (hmB hxB)
    · rw [Set.disjoint_left]
      rintro x hxB (hxD | hx1)
      · exact Set.disjoint_left.mp dBD hxB hxD
      · rw [Set.mem_singleton_iff] at hx1
        subst x
        exact hfout _ (List.getElem_mem hi1) (hmB hxB)
    · rw [Set.disjoint_left]
      rintro x (hxC | hx0) (hxD | hx1)
      · exact Set.disjoint_left.mp dCD hxC hxD
      · rw [Set.mem_singleton_iff] at hx1
        subst x
        exact hfout _ (List.getElem_mem hi1) (hmC hxC)
      · rw [Set.mem_singleton_iff] at hx0
        subst x
        exact hfout _ (List.getElem_mem hfpos) (hmD hxD)
      · rw [Set.mem_singleton_iff] at hx0 hx1
        have := (getElem_eq_iff hfnd hfpos hi1).mp (hx0.symm.trans hx1)
        omega
    · rintro x hxA y (hyC | hy0)
      · exact cAC x hxA y hyC
      · rw [Set.mem_singleton_iff] at hy0
        subst y
        exact (hAcomplete x hxA hfpos).symm
    · rintro x hxB y (hyD | hy1)
      · exact cBD x hxB y hyD
      · rw [Set.mem_singleton_iff] at hy1
        subst y
        rw [← hlast_eq_one]
        exact (hBcomplete x hxB hlast).symm
    · rintro x hxA y (hyD | hy1)
      · exact aAD x hxA y hyD
      · rw [Set.mem_singleton_iff] at hy1
        subst y
        exact hnoA x hxA 1 hi1 (by omega)
    · rintro x hxB y (hyC | hy0)
      · exact aBC x hxB y hyC
      · rw [Set.mem_singleton_iff] at hy0
        subst y
        exact hnoB x hxB 0 hfpos (by omega)

  obtain ⟨-, -, hCeq, -⟩ := hcube.2 A B (C ∪ {f[0]'hfpos})
    (D ∪ {f[1]'hi1}) hnewCube (le_refl A) (le_refl B)
    Set.subset_union_left Set.subset_union_left
  have hf0C' : f[0]'hfpos ∈ C ∪ {f[0]'hfpos} := Or.inr (by simp)
  have hf0Cmem : f[0]'hfpos ∈ C := by
    rw [hCeq]
    exact hf0C'
  exact hfout _ (List.getElem_mem hfpos) (hmC hf0Cmem)

end Workspace.ProofLemmas.Thm142FullCase
