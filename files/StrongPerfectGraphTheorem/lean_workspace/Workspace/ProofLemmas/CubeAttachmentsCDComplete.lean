import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.DoubleDiamond
import Workspace.Types.Prisms
import Workspace.Types.Appearances
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.CubeMajorCoreContradiction

/-!
# 14.2, the `C ∪ D` half of the *"Moreover"* clause

PAPER (printed p. 89):

> *"Suppose first that `X ⊆ C ∪ D`.  If possible, choose `c ∈ C ∩ X` and `d ∈ D ∩ X`,
> nonadjacent, and choose a path `P` joining them with interior in `F`.  Let `a₁-b₁-b₂-a₂-a₁` be
> a square; then the three paths `a₁-b₁`, `a₂-b₂`, `c-P-d` form a long prism, a contradiction.
> So there are no such `c, d`, and the theorem holds."*

The prism's two triangles are `{a₁, a₂, c}` and `{b₁, b₂, d}` — these are triangles because `A`
is complete to `C` and `B` is complete to `D`, and the two are disjoint because the four sets of
the cube are.  There are no edges between the interior of `P` and `V(K)` other than through `X`,
and `X ⊆ C ∪ D` misses `A ∪ B` entirely, which is what makes the three paths induce a prism.
It is long because `c` and `d` were chosen nonadjacent, so `P` has length `≥ 2`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- Assembling `FormPrism` from the data the paper writes down: two triangles and three paths,
with the cross-adjacencies described pair by pair. -/
private theorem formPrism_of_data {V : Type*} {G : SimpleGraph V}
    {a₁ a₂ a₃ b₁ b₂ b₃ : V} {P₁ P₂ P₃ : List V}
    (ha12 : G.Adj a₁ a₂) (ha13 : G.Adj a₁ a₃) (ha23 : G.Adj a₂ a₃)
    (hb12 : G.Adj b₁ b₂) (hb13 : G.Adj b₁ b₃) (hb23 : G.Adj b₂ b₃)
    (n11 : a₁ ≠ b₁) (n12 : a₁ ≠ b₂) (n13 : a₁ ≠ b₃)
    (n21 : a₂ ≠ b₁) (n22 : a₂ ≠ b₂) (n23 : a₂ ≠ b₃)
    (n31 : a₃ ≠ b₁) (n32 : a₃ ≠ b₂) (n33 : a₃ ≠ b₃)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂) (hP₃ : IsPathFrom G P₃ a₃ b₃)
    (h12 : ∀ u ∈ P₁, ∀ v ∈ P₂, (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)))
    (h13 : ∀ u ∈ P₁, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a₁ ∧ v = a₃) ∨ (u = b₁ ∧ v = b₃)))
    (h23 : ∀ u ∈ P₂, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a₂ ∧ v = a₃) ∨ (u = b₂ ∧ v = b₃))) :
    FormPrism G ![a₁, a₂, a₃] ![b₁, b₂, b₃] P₁ P₂ P₃ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact ha12 | exact ha13 | exact ha23
        | exact ha12.symm | exact ha13.symm | exact ha23.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact hb12 | exact hb13 | exact hb23
        | exact hb12.symm | exact hb13.symm | exact hb23.symm
  · intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  · simpa using hP₁
  · simpa using hP₂
  · simpa using hP₃
  · simpa using h12
  · simpa using h13
  · simpa using h23

/-- The `C`--`D` row of the attachment conclusion in 14.2. -/
theorem CubeAttachmentsCDComplete {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF5 G)
    (A B C D : Set V) (hcube : IsCube G A B C D)
    (F : Set V) (hF : F ⊆ (A ∪ B ∪ C ∪ D)ᶜ) (hFconn : ConnectedSet G F)
    (X : Set V) (hX : X = attachments G F (A ∪ B ∪ C ∪ D))
    (hXCD : X ⊆ C ∪ D) :
    Complete G (X ∩ C) (X ∩ D) := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube
  have memA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inl (Or.inl hu))
  have memB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inl (Or.inr hu))
  -- no vertex of `F` has a neighbour in `A ∪ B`, since every attachment lies in `C ∪ D`
  have hFnoA : ∀ u ∈ A, ∀ f ∈ F, ¬ G.Adj u f := by
    intro u hu f hf hadj
    have : u ∈ X := by rw [hX]; exact ⟨memA hu, f, hf, hadj⟩
    rcases hXCD this with h | h
    · exact (Set.disjoint_left.mp dAC hu) h
    · exact (Set.disjoint_left.mp dAD hu) h
  have hFnoB : ∀ u ∈ B, ∀ f ∈ F, ¬ G.Adj u f := by
    intro u hu f hf hadj
    have : u ∈ X := by rw [hX]; exact ⟨memB hu, f, hf, hadj⟩
    rcases hXCD this with h | h
    · exact (Set.disjoint_left.mp dBC hu) h
    · exact (Set.disjoint_left.mp dBD hu) h
  have hFnotK : ∀ f ∈ F, f ∉ A ∪ B ∪ C ∪ D := fun f hf => hF hf
  -- *"If possible, choose `c ∈ C ∩ X` and `d ∈ D ∩ X`, nonadjacent"*
  rintro c ⟨hcX, hcC⟩ d ⟨hdX, hdD⟩
  by_contra hcd
  have hcd' : c ≠ d := fun he => (Set.disjoint_left.mp dCD hcC) (he ▸ hdD)
  -- *"and choose a path `P` joining them with interior in `F`"*
  obtain ⟨-, fc, hfcF, hcfc⟩ : c ∈ A ∪ B ∪ C ∪ D ∧ ∃ f ∈ F, G.Adj c f := by
    rw [hX] at hcX; exact hcX
  obtain ⟨-, fd, hfdF, hdfd⟩ : d ∈ A ∪ B ∪ C ∪ D ∧ ∃ f ∈ F, G.Adj d f := by
    rw [hX] at hdX; exact hdX
  have hconn1 : ConnectedSet G (F ∪ {c}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hFconn ⟨fc, hfcF, hcfc⟩
  have hconn2 : ConnectedSet G ((F ∪ {c}) ∪ {d}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hconn1 ⟨fd, Or.inl hfdF, hdfd⟩
  obtain ⟨P, hP, hPmem⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hconn2
    (Or.inl (Or.inr rfl) : c ∈ (F ∪ {c}) ∪ {d}) (Or.inr rfl : d ∈ (F ∪ {c}) ∪ {d})
  -- every vertex of `P` is `c`, `d`, or an interior vertex lying in `F`
  have hPcase : ∀ z ∈ P, z = c ∨ z = d ∨ z ∈ F := by
    intro z hz
    rcases hPmem z hz with (h | h) | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Set.mem_singleton_iff.mp h)
    · exact Or.inr (Or.inl (Set.mem_singleton_iff.mp h))
  -- *"Let `a₁-b₁-b₂-a₂-a₁` be a square"*
  obtain ⟨⟨⟨x, hxA, y, hyA, hxy⟩, -⟩, hsq1, -⟩ := sAB
  obtain ⟨a₁, b₁, b₂, a₂, hsq, -, -⟩ :=
    hsq1 {x} (A \ {x}) (by
        ext u
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_diff]
        constructor
        · rintro (rfl | ⟨hu, -⟩)
          · exact hxA
          · exact hu
        · intro hu
          by_cases h : u = x
          · exact Or.inl h
          · exact Or.inr ⟨hu, h⟩)
      (by rw [Set.disjoint_left]; rintro u rfl hu; exact hu.2 rfl)
      ⟨x, rfl⟩ ⟨y, hyA, hxy.symm⟩
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq
  have ha₁A : a₁ ∈ A := hsq.2.1
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  -- *"then the three paths `a₁-b₁`, `a₂-b₂`, `c-P-d` form a long prism"*
  have hPath1 : IsPathFrom G [a₁, b₁] a₁ b₁ := ⟨PathBasics.isPathList_pair e01, rfl, rfl⟩
  have hPath2 : IsPathFrom G [a₂, b₂] a₂ b₂ := ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩
  -- cross-adjacencies between a first-triangle vertex of `A` and a vertex of `P`
  have hcrossA : ∀ (u : V), u ∈ A → G.Adj u c → ∀ v ∈ P, (G.Adj u v ↔ v = c) := by
    intro u huA huc v hv
    rcases hPcase v hv with rfl | rfl | hvF
    · exact ⟨fun _ => rfl, fun _ => huc⟩
    · exact ⟨fun hadj => absurd hadj (aAD u huA v hdD), fun he => absurd he hcd'.symm⟩
    · exact ⟨fun hadj => absurd hadj (hFnoA u huA v hvF),
        fun he => absurd (he ▸ hvF) (fun h => hFnotK v hvF (he ▸ Or.inl (Or.inr hcC)))⟩
  have hcrossB : ∀ (u : V), u ∈ B → G.Adj u d → ∀ v ∈ P, (G.Adj u v ↔ v = d) := by
    intro u huB hud v hv
    rcases hPcase v hv with rfl | rfl | hvF
    · exact ⟨fun hadj => absurd hadj (aBC u huB v hcC), fun he => absurd he hcd'⟩
    · exact ⟨fun _ => rfl, fun _ => hud⟩
    · exact ⟨fun hadj => absurd hadj (hFnoB u huB v hvF),
        fun he => absurd (he ▸ hvF) (fun h => hFnotK v hvF (he ▸ Or.inr hdD))⟩
  have hprism : FormPrism G ![a₁, a₂, c] ![b₁, b₂, d] [a₁, b₁] [a₂, b₂] P := by
    refine formPrism_of_data (G := G)
      e30.symm (cAC a₁ ha₁A c hcC) (cAC a₂ ha₂A c hcC)
      e12 (cBD b₁ hb₁B d hdD) (cBD b₂ hb₂B d hdD)
      ne01 ne02 (fun he => (Set.disjoint_left.mp dAD ha₁A) (he ▸ hdD))
      ne13.symm ne23.symm (fun he => (Set.disjoint_left.mp dAD ha₂A) (he ▸ hdD))
      (fun he => (Set.disjoint_left.mp dBC hb₁B) (he ▸ hcC))
      (fun he => (Set.disjoint_left.mp dBC hb₂B) (he ▸ hcC))
      hcd' hPath1 hPath2 hP ?_ ?_ ?_
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with hu | hu <;> rcases hv with hv | hv <;> rw [hu, hv]
      · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => e30.symm⟩
      · exact ⟨fun hadj => absurd hadj n02,
          by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [absurd h ne23, absurd h ne01]⟩
      · exact ⟨fun hadj => absurd hadj n13,
          by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [absurd h ne01.symm, absurd h ne23.symm]⟩
      · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => e12⟩
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu <;> rw [hu]
      · rw [hcrossA a₁ ha₁A (cAC a₁ ha₁A c hcC) v hv]
        exact ⟨fun h => Or.inl ⟨rfl, h⟩, by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [h, absurd h ne01]⟩
      · rw [hcrossB b₁ hb₁B (cBD b₁ hb₁B d hdD) v hv]
        exact ⟨fun h => Or.inr ⟨rfl, h⟩,
          by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [absurd h ne01.symm, h]⟩
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with hu | hu <;> rw [hu]
      · rw [hcrossA a₂ ha₂A (cAC a₂ ha₂A c hcC) v hv]
        exact ⟨fun h => Or.inl ⟨rfl, h⟩,
          by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [h, absurd h ne23.symm]⟩
      · rw [hcrossB b₂ hb₂B (cBD b₂ hb₂B d hdD) v hv]
        exact ⟨fun h => Or.inr ⟨rfl, h⟩,
          by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [absurd h ne23, h]⟩
  -- the prism is long: `P` has length `≥ 2` because `c` and `d` are nonadjacent and distinct
  have hlong : 1 < pathLength P := by
    by_contra hcon
    push_neg at hcon
    interval_cases h : (pathLength P)
    · have hlen : P.length = 1 := by
        have := PathBasics.length_eq_pathLength_add_one hP.1
        omega
      obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hlen
      rw [hz] at hP
      have hc' : z = c := by simpa using hP.2.1
      have hd' : z = d := by simpa using hP.2.2
      exact hcd' (hc'.symm.trans hd')
    · exact hcd (PathBasics.isPathFrom_ends_adj_of_length_one hP h)
  exact hG.2.1 ⟨![a₁, a₂, c], ![b₁, b₂, d], [a₁, b₁], [a₂, b₂], P, hprism, Or.inr (Or.inr hlong)⟩

end Workspace.ProofLemmas
