import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.AnticompleteUnionComponents
import Workspace.ProofLemmas.CubeComplement
import Workspace.ProofLemmas.CubeExtraction
import Workspace.ProofLemmas.CubeClaimTwo
import Workspace.ProofLemmas.CubeClaimThree
import Workspace.ProofLemmas.CubeClaimFour
import Workspace.Statements.S04.Thm_4_2
import Workspace.Statements.S14.Thm_14_2

/-!
# The closing construction of 14.3

PAPER (printed p. 91), the second half of the closing paragraph, from *"So `Y` is nonempty"*:

> *"Choose an anticomponent `Y₁` of `Y`.  By (3) and 14.2, `Y₁` is not `A`-complete or
> `B`-complete.  Let `X` be the set of `Y₁`-complete vertices in `A ∪ B ∪ C ∪ D`.  Let `L` be the
> union of `A \ X` and all components of `F` that have an attachment in `A \ X`; and let `M` be
> the union of `B \ X` and all other components of `F`.  By (1) there are no edges between
> `A \ X` and `B \ X`; and therefore by 14.2, no component of `F` has attachments in both
> `A \ X` and `B \ X`.  Hence there is no edge between `L` and `M`.  Since
> `L, M, X ∪ (Y \ Y₁), Y₁` is a partition of `V(G)`, and `Y₁` is complete to `X ∪ (Y \ Y₁)`, it
> follows that `(L ∪ M, X ∪ (Y \ Y₁) ∪ Y₁)` is a skew partition of `G`.  No vertex of `D` has a
> neighbour in `L`, and so it is loose, contrary to 4.2.  Hence there is no such graph `G`.
> This proves 14.3."*

`cube_finish` starts exactly where the paper's preceding sentence leaves off — `Y` nonempty,
`Y` complete to `C ∪ D`, and all attachments of `F` inside `A ∪ B` — and derives the
contradiction.  It is a second 4.5-style argument, the twin of claim (2) and claim (4).

Three points on the transcription.

* **Claim (1)** is *"immediate from 14.2 by taking complements"*, and only its second sentence
  (*"every edge from `A ∪ D` to `B ∪ C` has a `Y₁`-complete end"*) is used here, to get *"there
  are no edges between `A \ X` and `B \ X`"*.  It is produced inline (`hnoedgeAB`) by citing
  14.2 at `Gᶜ` for the complementary cube `(D, C, A, B)`: a vertex of `K` that is **not**
  `Y₁`-complete in `G` is precisely an attachment of `Y₁` in `Gᶜ`, so 14.2's *"Moreover"* clause
  says exactly that two such vertices, one in `A ∪ D` and one in `B ∪ C`, are `Gᶜ`-adjacent.
  This needs the *minor*-half of the complement transport,
  `CubeClaimThree.minorForCube_compl` (`CubeComplement` carries only the *major* half).
* ***"By (3) and 14.2, `Y₁` is not `A`-complete or `B`-complete"*** is claim **(2)** together
  with the standing hypothesis that `Y` is complete to `C ∪ D`: an `A`-complete `Y₁` would be
  complete to `A ∪ D`, and a `B`-complete one to `B ∪ C`, both of which (2) forbids.  The `B`
  half is (2) applied to the swapped cube `(B, A, D, C)` — the paper's *"from the symmetry"* —
  through `CubeClaimThree.majorForCube_swap` and `CubeClaimThree.maximalCube_swap`.
* The printed appeal to **4.2** is made literally.  `loose_of_no_neighbour_in_L` below
  assembles the four sets into the skew partition `(L ∪ M, (X ∪ (Y \ Y₁)) ∪ Y₁)` that the
  paper's preceding sentence names, observes that the vertex of `D` with no neighbour in `L`
  witnesses looseness (`L` contains a whole component of `L ∪ M`, since there are no edges
  between `L` and `M`), and applies `thm_4_2`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.CubeFinish

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-! ### The closing appeal to 4.2 -/

/-- PAPER (printed p. 91, the last sentence of 14.3): *"Since `L, M, X ∪ (Y \ Y₁), Y₁` is a
partition of `V(G)`, and `Y₁` is complete to `X ∪ (Y \ Y₁)`, it follows that
`(L ∪ M, X ∪ (Y \ Y₁) ∪ Y₁)` is a skew partition of `G`.  No vertex of `D` has a neighbour in
`L`, and so it is loose, contrary to 4.2."*

Stated for a general partition `V(G) = X ∪ Y ∪ L ∪ R` into four nonempty sets with no edges
between `L` and `R` and `X` complete to `Y`: the two halves `L ∪ R` and `X ∪ Y` are then
disconnected resp. anticonnected, so `(L ∪ R, X ∪ Y)` is a skew partition; a vertex `v` of
`X ∪ Y` with no neighbour in `L` has no neighbour in the component of `L ∪ R` that lies inside
`L`, so the partition is *loose*; and `4.2` turns that into a balanced skew partition. -/
private theorem loose_of_no_neighbour_in_L [Fintype V] [DecidableEq V]
    (hG : Berge G) (X Y L R : Set V)
    (hcover : X ∪ Y ∪ L ∪ R = Set.univ)
    (hXY : Disjoint X Y) (hXL : Disjoint X L) (hXR : Disjoint X R)
    (hYL : Disjoint Y L) (hYR : Disjoint Y R) (hLR : Disjoint L R)
    (hXne : X.Nonempty) (hYne : Y.Nonempty) (hLne : L.Nonempty) (hRne : R.Nonempty)
    (hnoedge : Anticomplete G L R) (hcomplete : Complete G X Y)
    (v : V) (hv : v ∈ X ∪ Y) (hvL : VertexAnticomplete G v L) :
    AdmitsBalancedSkewPartition G := by
  have hantiCompl : Anticomplete Gᶜ X Y := by
    intro x hx y hy hxy
    exact hxy.2 (hcomplete x hx y hy)
  obtain ⟨hAnconn, A_L, A_R, hALcomp, hALsub, hARcomp, hARsub⟩ :=
    Workspace.Types.AnticompleteUnionComponents.anticompleteUnionComponents
      G L R hLR hLne hRne hnoedge
  obtain ⟨hBnconn, B_X, B_Y, hBXcomp, hBXsub, hBYcomp, hBYsub⟩ :=
    Workspace.Types.AnticompleteUnionComponents.anticompleteUnionComponents
      Gᶜ X Y hXY hXne hYne hantiCompl
  have hcoverAB : (L ∪ R) ∪ (X ∪ Y) = Set.univ := by
    simpa only [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hcover
  have hdisjAB : Disjoint (L ∪ R) (X ∪ Y) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    rcases hzA with hzL | hzR <;> rcases hzB with hzX | hzY
    · exact Set.disjoint_left.1 hXL hzX hzL
    · exact Set.disjoint_left.1 hYL hzY hzL
    · exact Set.disjoint_left.1 hXR hzX hzR
    · exact Set.disjoint_left.1 hYR hzY hzR
  have hAB : IsSkewPartition G (L ∪ R) (X ∪ Y) := by
    refine ⟨hcoverAB, hdisjAB, hAnconn, ?_⟩
    simpa only [AnticonnectedSet] using hBnconn
  -- *"and so it is loose, contrary to 4.2"*
  exact _root_.Workspace.Statements.S04.SPGT.thm_4_2 G hG
    ⟨L ∪ R, X ∪ Y, hAB, Or.inl ⟨v, hv, A_L, hALcomp, fun a ha => hvL a (hALsub ha)⟩⟩

/-! ### The closing construction -/

/-- PAPER (printed p. 91), the closing paragraph of 14.3 from *"So `Y` is nonempty"* onwards.

The hypotheses are the state the paper has reached at *"so by (3), all attachments of `F` belong
to `A ∪ B`"*: `(A, B, C, D)` is a maximal cube of `G ∈ F₅` forming `K`, `F` and `Y` are the sets
of minor and major vertices, `Y` is nonempty and complete to `C ∪ D`, and every attachment of
every component of `F` lies in `A ∪ B`.  The conclusion is the contradiction that finishes the
theorem. -/
theorem cube_finish [Fintype V] [DecidableEq V] {A B C D F Y : Set V}
    (hG : InF5 G) (hno : ¬ AdmitsBalancedSkewPartition G)
    (hcube : MaximalCube G A B C D)
    (hFdef : F = {v : V | MinorForCube G A B C D v})
    (hYdef : Y = {v : V | MajorForCube G A B C D v}) (hYne : Y.Nonempty)
    (hYCD : Complete G Y (C ∪ D))
    (hFatt : ∀ F₁ : Set V, IsComponent G F F₁ →
      ∀ w ∈ attachments G F₁ (A ∪ B ∪ C ∪ D), w ∈ A ∪ B) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, hAne, hBne, hCne, hDne⟩,
    ⟨cAC, cBD, aAD, aBC⟩, hsqAB, hsqCD⟩ := hcube.1
  have hFmin : ∀ v ∈ F, MinorForCube G A B C D v := by intro v hv; rw [hFdef] at hv; exact hv
  have hYmaj : ∀ v ∈ Y, MajorForCube G A B C D v := by intro v hv; rw [hYdef] at hv; exact hv
  have hFK : ∀ v ∈ F, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hFmin v hv).1
  have hYK : ∀ v ∈ Y, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hYmaj v hv).1
  have hFYd : ∀ v : V, v ∈ F → v ∈ Y → False :=
    fun v hvF hvY => CubeClaimFour.not_minor_major hcube.1 (hFmin v hvF) (hYmaj v hvY)
  -- *"Choose an anticomponent `Y₁` of `Y`."*
  obtain ⟨y₀, hy₀⟩ := hYne
  obtain ⟨Y₁, hY₁, hy₀Y₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ Y hy₀
  have hY₁a : IsAnticomponent G Y Y₁ := hY₁
  have hY₁Y : Y₁ ⊆ Y := hY₁.1
  have hY₁ne : Y₁.Nonempty := ⟨y₀, hy₀Y₁⟩
  -- *"`Y₁` is not `A`-complete or `B`-complete"*, by claim (2) and `Y` complete to `C ∪ D`
  have hnotA : ¬ Complete G Y₁ A := by
    intro hcomp
    refine CubeClaimTwo.cube_claim_two hG hno hcube hYdef ⟨y₀, hy₀⟩ Y₁ hY₁a ?_
    intro y hy z hz
    rcases hz with hz | hz
    · exact hcomp y hy z hz
    · exact hYCD y (hY₁Y hy) z (Or.inr hz)
  have hYdef' : Y = {v : V | MajorForCube G B A D C v} := by
    rw [hYdef]
    ext v
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => CubeClaimThree.majorForCube_swap h,
      fun h => CubeClaimThree.majorForCube_swap h⟩
  have hnotB : ¬ Complete G Y₁ B := by
    intro hcomp
    refine CubeClaimTwo.cube_claim_two hG hno (CubeClaimThree.maximalCube_swap hcube) hYdef'
      ⟨y₀, hy₀⟩ Y₁ hY₁a ?_
    intro y hy z hz
    rcases hz with hz | hz
    · exact hcomp y hy z hz
    · exact hYCD y (hY₁Y hy) z (Or.inl hz)
  -- *"Let `X` be the set of `Y₁`-complete vertices in `A ∪ B ∪ C ∪ D`."*
  obtain ⟨Xs, hX⟩ : ∃ S : Set V, S = {v : V | v ∈ A ∪ B ∪ C ∪ D ∧ VertexComplete G v Y₁} :=
    ⟨_, rfl⟩
  have hXK : ∀ v ∈ Xs, v ∈ A ∪ B ∪ C ∪ D := by
    intro v hv; rw [hX] at hv; exact hv.1
  have hCDX : ∀ v ∈ C ∪ D, v ∈ Xs := by
    intro v hv
    rw [hX]
    refine ⟨?_, fun y hy => (hYCD y (hY₁Y hy) v hv).symm⟩
    rcases hv with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  -- `A \ X` and `B \ X` are nonempty
  obtain ⟨a₁, ha₁A, ha₁X⟩ : ∃ a ∈ A, a ∉ Xs := by
    by_contra hcon
    push Not at hcon
    refine hnotA (fun y hy z hz => ?_)
    have hzX : z ∈ Xs := hcon z hz
    rw [hX] at hzX
    exact (hzX.2 y hy).symm
  obtain ⟨b₁, hb₁B, hb₁X⟩ : ∃ b ∈ B, b ∉ Xs := by
    by_contra hcon
    push Not at hcon
    refine hnotB (fun y hy z hz => ?_)
    have hzX : z ∈ Xs := hcon z hz
    rw [hX] at hzX
    exact (hzX.2 y hy).symm
  -- *"By (1) there are no edges between `A \ X` and `B \ X`."*
  have hnoedgeAB : ∀ a ∈ A, a ∉ Xs → ∀ b ∈ B, b ∉ Xs → ¬ G.Adj a b := by
    intro a haA haX b hbB hbX hadj
    have hG' : InF5 Gᶜ := ClassLemmas.inF5_compl.mpr hG
    have hcube' : MaximalCube Gᶜ D C A B := CubeComplement.maximalCube_compl hcube
    have hKeq : D ∪ C ∪ A ∪ B = A ∪ B ∪ C ∪ D := by
      ext u; simp only [Set.mem_union]; tauto
    have hY₁sub : Y₁ ⊆ (D ∪ C ∪ A ∪ B)ᶜ := by
      intro y hy hmem
      rw [hKeq] at hmem
      exact hYK y (hY₁Y hy) hmem
    have hY₁minor : ∀ y ∈ Y₁, MinorForCube Gᶜ D C A B y :=
      fun y hy => CubeClaimThree.minorForCube_compl hcube.1 (hYmaj y (hY₁Y hy))
    have h142 := _root_.Workspace.Statements.S14.SPGT.thm_14_2 Gᶜ hG' D C A B hcube' Y₁
      hY₁sub hY₁.2.1 hY₁minor (attachments Gᶜ Y₁ (D ∪ C ∪ A ∪ B)) rfl
    -- a vertex of `K` that is not `Y₁`-complete is an attachment of `Y₁` in `Gᶜ`
    have hattw : ∀ w : V, w ∈ A ∪ B ∪ C ∪ D → w ∉ Xs →
        w ∈ attachments Gᶜ Y₁ (D ∪ C ∪ A ∪ B) := by
      intro w hwK hwX
      have hex : ∃ y ∈ Y₁, ¬ G.Adj w y := by
        by_contra hcon
        push Not at hcon
        exact hwX (by rw [hX]; exact ⟨hwK, hcon⟩)
      obtain ⟨y, hy, hny⟩ := hex
      refine ⟨by rw [hKeq]; exact hwK, y, hy, ?_⟩
      exact ⟨fun he => hYK y (hY₁Y hy) (he ▸ hwK), hny⟩
    have haA' : a ∈ attachments Gᶜ Y₁ (D ∪ C ∪ A ∪ B) :=
      hattw a (Or.inl (Or.inl (Or.inl haA))) haX
    have hbB' : b ∈ attachments Gᶜ Y₁ (D ∪ C ∪ A ∪ B) :=
      hattw b (Or.inl (Or.inl (Or.inr hbB))) hbX
    exact (h142.2 a ⟨haA', Or.inr haA⟩ b ⟨hbB', Or.inr hbB⟩).2 hadj
  -- *"and therefore by 14.2, no component of `F` has attachments in both `A \ X` and `B \ X`"*
  have hnoboth : ∀ P : Set V, IsComponent G F P → ∀ a ∈ A, a ∉ Xs → ∀ b ∈ B, b ∉ Xs →
      a ∈ attachments G P (A ∪ B ∪ C ∪ D) → b ∈ attachments G P (A ∪ B ∪ C ∪ D) → False := by
    intro P hP a haA haX b hbB hbX hatta hattb
    have h := _root_.Workspace.Statements.S14.SPGT.thm_14_2 G hG A B C D hcube P
      (fun v hv => hFK v (hP.1 hv)) hP.2.1 (fun v hv => hFmin v (hP.1 hv))
      (attachments G P (A ∪ B ∪ C ∪ D)) rfl
    exact hnoedgeAB a haA haX b hbB hbX
      (h.2 a ⟨hatta, Or.inl haA⟩ b ⟨hattb, Or.inl hbB⟩)
  -- *"Let `L` be the union of `A \ X` and all components of `F` that have an attachment in
  -- `A \ X`; and let `M` be the union of `B \ X` and all other components of `F`."*
  obtain ⟨L, hL⟩ : ∃ S : Set V, S = (A \ Xs) ∪
      {v : V | ∃ P : Set V, IsComponent G F P ∧ v ∈ P ∧
        ∃ a ∈ A, a ∉ Xs ∧ a ∈ attachments G P (A ∪ B ∪ C ∪ D)} := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ S : Set V, S = (B \ Xs) ∪
      {v : V | ∃ P : Set V, IsComponent G F P ∧ v ∈ P ∧
        ¬ ∃ a ∈ A, a ∉ Xs ∧ a ∈ attachments G P (A ∪ B ∪ C ∪ D)} := ⟨_, rfl⟩
  obtain ⟨XY, hXY⟩ : ∃ S : Set V, S = Xs ∪ (Y \ Y₁) := ⟨_, rfl⟩
  -- *"Hence there is no edge between `L` and `M`."*
  have hLM : Anticomplete G L M := by
    intro x hx y hy hadj
    rw [hL] at hx
    rw [hM] at hy
    rcases hx with hxA | ⟨P, hP, hxP, hPatt⟩
    · rcases hy with hyB | ⟨Q, hQ, hyQ, hQatt⟩
      · exact hnoedgeAB x hxA.1 hxA.2 y hyB.1 hyB.2 hadj
      · exact hQatt ⟨x, hxA.1, hxA.2, ⟨Or.inl (Or.inl (Or.inl hxA.1)), y, hyQ, hadj⟩⟩
    · rcases hy with hyB | ⟨Q, hQ, hyQ, hQatt⟩
      · obtain ⟨a, haA, haX, hatta⟩ := hPatt
        exact hnoboth P hP a haA haX y hyB.1 hyB.2 hatta
          ⟨Or.inl (Or.inl (Or.inr hyB.1)), x, hxP, hadj.symm⟩
      · have hPQ : P ≠ Q := fun he => hQatt (he ▸ hPatt)
        exact ComponentsOfSetBasics.anticomplete_of_isComponent G hP hQ hPQ x hxP y hyQ hadj
  -- *"`L, M, X ∪ (Y \ Y₁), Y₁` is a partition of `V(G)`"*
  have hcover : XY ∪ Y₁ ∪ L ∪ M = Set.univ := by
    refine Set.eq_univ_of_forall (fun v => ?_)
    by_cases hvK : v ∈ A ∪ B ∪ C ∪ D
    · by_cases hvX : v ∈ Xs
      · exact Or.inl (Or.inl (Or.inl (by rw [hXY]; exact Or.inl hvX)))
      · rcases hvK with ((hv | hv) | hv) | hv
        · exact Or.inl (Or.inr (by rw [hL]; exact Or.inl ⟨hv, hvX⟩))
        · exact Or.inr (by rw [hM]; exact Or.inl ⟨hv, hvX⟩)
        · exact absurd (hCDX v (Or.inl hv)) hvX
        · exact absurd (hCDX v (Or.inr hv)) hvX
    · rcases CubeExtraction.minor_or_major G hG hcube hvK with h | h
      · have hvF : v ∈ F := by rw [hFdef]; exact h
        obtain ⟨P, hP, hvP⟩ := ComponentsOfSetBasics.exists_isComponent_mem G F hvF
        by_cases hatt : ∃ a ∈ A, a ∉ Xs ∧ a ∈ attachments G P (A ∪ B ∪ C ∪ D)
        · exact Or.inl (Or.inr (by rw [hL]; exact Or.inr ⟨P, hP, hvP, hatt⟩))
        · exact Or.inr (by rw [hM]; exact Or.inr ⟨P, hP, hvP, hatt⟩)
      · have hvY : v ∈ Y := by rw [hYdef]; exact h
        by_cases hvY₁ : v ∈ Y₁
        · exact Or.inl (Or.inl (Or.inr hvY₁))
        · exact Or.inl (Or.inl (Or.inl (by rw [hXY]; exact Or.inr ⟨hvY, hvY₁⟩)))
  -- *"`Y₁` is complete to `X ∪ (Y \ Y₁)`"*
  have hcompXY : Complete G XY Y₁ := by
    intro x hx y hy
    rw [hXY] at hx
    rcases hx with hxX | hxY
    · rw [hX] at hxX
      exact hxX.2 y hy
    · exact LooseSkewPartition.vertexComplete_of_notMem_anticomponent hY₁a hxY.1 hxY.2 y hy
  -- *"No vertex of `D` has a neighbour in `L`"*
  obtain ⟨d₀, hd₀⟩ := hDne
  have hd₀L : VertexAnticomplete G d₀ L := by
    intro x hx hadj
    rw [hL] at hx
    rcases hx with hxA | ⟨P, hP, hxP, hPatt⟩
    · exact aAD x hxA.1 d₀ hd₀ hadj.symm
    · have hatt : d₀ ∈ attachments G P (A ∪ B ∪ C ∪ D) := ⟨Or.inr hd₀, x, hxP, hadj⟩
      rcases hFatt P hP d₀ hatt with h | h
      · exact Set.disjoint_left.mp dAD h hd₀
      · exact Set.disjoint_left.mp dBD h hd₀
  -- *"and so it is loose, contrary to 4.2"*
  refine hno (loose_of_no_neighbour_in_L hBerge XY Y₁ L M
    hcover ?_ ?_ ?_ ?_ ?_ ?_ ?_ hY₁ne ?_ ?_ hLM hcompXY
    d₀ (Or.inl (by rw [hXY]; exact Or.inl (hCDX d₀ (Or.inr hd₀)))) hd₀L)
  · -- `Disjoint XY Y₁`
    refine Set.disjoint_left.mpr (fun x hx hx₁ => ?_)
    rw [hXY] at hx
    rcases hx with hxX | hxY
    · exact hYK x (hY₁Y hx₁) (hXK x hxX)
    · exact hxY.2 hx₁
  · -- `Disjoint XY L`
    refine Set.disjoint_left.mpr (fun x hx hxL => ?_)
    rw [hXY] at hx
    rw [hL] at hxL
    rcases hx with hxX | hxY
    · rcases hxL with hxA | ⟨P, hP, hxP, -⟩
      · exact hxA.2 hxX
      · exact hFK x (hP.1 hxP) (hXK x hxX)
    · rcases hxL with hxA | ⟨P, hP, hxP, -⟩
      · exact hYK x hxY.1 (Or.inl (Or.inl (Or.inl hxA.1)))
      · exact hFYd x (hP.1 hxP) hxY.1
  · -- `Disjoint XY M`
    refine Set.disjoint_left.mpr (fun x hx hxM => ?_)
    rw [hXY] at hx
    rw [hM] at hxM
    rcases hx with hxX | hxY
    · rcases hxM with hxB | ⟨P, hP, hxP, -⟩
      · exact hxB.2 hxX
      · exact hFK x (hP.1 hxP) (hXK x hxX)
    · rcases hxM with hxB | ⟨P, hP, hxP, -⟩
      · exact hYK x hxY.1 (Or.inl (Or.inl (Or.inr hxB.1)))
      · exact hFYd x (hP.1 hxP) hxY.1
  · -- `Disjoint Y₁ L`
    refine Set.disjoint_left.mpr (fun x hx₁ hxL => ?_)
    rw [hL] at hxL
    rcases hxL with hxA | ⟨P, hP, hxP, -⟩
    · exact hYK x (hY₁Y hx₁) (Or.inl (Or.inl (Or.inl hxA.1)))
    · exact hFYd x (hP.1 hxP) (hY₁Y hx₁)
  · -- `Disjoint Y₁ M`
    refine Set.disjoint_left.mpr (fun x hx₁ hxM => ?_)
    rw [hM] at hxM
    rcases hxM with hxB | ⟨P, hP, hxP, -⟩
    · exact hYK x (hY₁Y hx₁) (Or.inl (Or.inl (Or.inr hxB.1)))
    · exact hFYd x (hP.1 hxP) (hY₁Y hx₁)
  · -- `Disjoint L M`
    refine Set.disjoint_left.mpr (fun x hxL hxM => ?_)
    rw [hL] at hxL
    rw [hM] at hxM
    rcases hxL with hxA | ⟨P, hP, hxP, hPatt⟩
    · rcases hxM with hxB | ⟨Q, hQ, hxQ, -⟩
      · exact Set.disjoint_left.mp dAB hxA.1 hxB.1
      · exact hFK x (hQ.1 hxQ) (Or.inl (Or.inl (Or.inl hxA.1)))
    · rcases hxM with hxB | ⟨Q, hQ, hxQ, hQatt⟩
      · exact hFK x (hP.1 hxP) (Or.inl (Or.inl (Or.inr hxB.1)))
      · have hPQ : P = Q := by
          by_contra hne
          exact Set.disjoint_left.mp
            (ComponentsOfSetBasics.disjoint_of_isComponent G hP hQ hne) hxP hxQ
        rw [hPQ] at hPatt
        exact hQatt hPatt
  · -- `XY` is nonempty
    obtain ⟨c₀, hc₀⟩ := hCne
    exact ⟨c₀, by rw [hXY]; exact Or.inl (hCDX c₀ (Or.inl hc₀))⟩
  · -- `L` is nonempty
    exact ⟨a₁, by rw [hL]; exact Or.inl ⟨ha₁A, ha₁X⟩⟩
  · -- `M` is nonempty
    exact ⟨b₁, by rw [hM]; exact Or.inl ⟨hb₁B, hb₁X⟩⟩

end Workspace.ProofLemmas.CubeFinish
