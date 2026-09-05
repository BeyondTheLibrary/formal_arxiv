import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.CubeComplement
import Workspace.ProofLemmas.CubeExtraction
import Workspace.ProofLemmas.CubeClaimTwo
import Workspace.ProofLemmas.CubeClaimThree
import Workspace.ProofLemmas.CubeClaimFour
import Workspace.ProofLemmas.CubeClaimFourCD
import Workspace.ProofLemmas.CubeFinish
import Workspace.ProofLemmas.TwoJoinFromSeparation
import Workspace.Statements.S14.Thm_14_2

/-!
# The assembly of 14.3

PAPER (printed p. 91), the opening and the closing paragraph of the proof of 14.3:

> *"We may assume that `G, Ḡ` do not admit proper 2-joins, and `G` does not admit a balanced
> skew partition.  Suppose for a contradiction that `G` contains a double diamond; then it
> contains a cube, and so there is a maximal cube `(A, B, C, D)` in `G`, forming `K`.  Let `F` be
> the set of all minor vertices in `V(G) \ V(K)`, and `Y` the set of all major ones. …*
>
> *Now if `Y = ∅`, then by (3) it follows that `G` admits a proper 2-join, a contradiction.  So
> `Y` is nonempty, and by taking complements, `F` is nonempty.  By (4), passing to the complement
> if necessary, we may assume that there is no anticomponent of `Y` that is complete to `A ∪ B`.
> Hence `Y` is complete to `C ∪ D`, by (1) and (2).  Since `Y` is nonempty, it follows from (4)
> that there is no component `F₁` of `F` with set of attachments contained in `C ∪ D`; so by (3),
> all attachments of `F` belong to `A ∪ B`.  …"*

Three modules do the work of the four numbered claims — `CubeClaimTwo` (2), `CubeClaimThree`
(3), `CubeClaimFour` + `CubeClaimFourCD` (4) — and two more do the two closing constructions,
`TwoJoinFromSeparation` (the `Y = ∅` 2-join) and `CubeFinish` (the second 4.5-style argument
from *"So `Y` is nonempty"* on).  This module supplies claim **(1)**, which the paper disposes of
in one line, and glues everything together.

Three points on the transcription.

* **Claim (1)** — *"Every anticomponent `Y₁` of `Y` is complete to one of `A ∪ B`, `C ∪ D`,
  `A ∪ D`, `B ∪ C` … This is immediate from 14.2 by taking complements"* — is
  `cube_claim_one`.  `Y₁` is a connected set of *minor* vertices of the complementary cube
  `(D, C, A, B)` in `Gᶜ`, so 14.2 applies to it there and confines its `Gᶜ`-attachments to one of
  `D ∪ C`, `A ∪ B`, `D ∪ A`, `C ∪ B`; and a vertex of `K` is a `Gᶜ`-attachment of `Y₁` exactly
  when it is **not** `Y₁`-complete in `G`, so the four alternatives become the four listed
  completeness statements, in the order `A ∪ B`, `C ∪ D`, `B ∪ C`, `A ∪ D`.
* ***"passing to the complement if necessary"*** is real work, because the tail of the argument
  is not symmetric: `cube_tail` is the whole passage from *"Hence `Y` is complete to `C ∪ D`"*
  onwards, stated for an arbitrary graph, and `cube_main` invokes it either at `G` (when no
  anticomponent of `Y` is complete to `A ∪ B`) or at `Gᶜ` with the cube `(D, C, A, B)` (when one
  is — claim (4) then says no component of `F` has all its attachments in `A ∪ B`, which is
  exactly the same hypothesis read in `Gᶜ`, since minor and major vertices swap there).
* ***"by taking complements, `F` is nonempty"*** is the `Y = ∅` 2-join construction run in `Gᶜ`:
  there the majors are `F`, and the two alternatives that claim (3) kills for `G` are the two
  that claim (2) kills for `Gᶜ`.  This is why `cube_main` needs **both** `¬ AdmitsProper2Join G`
  and `¬ AdmitsProper2Join Gᶜ`.

Nothing here corresponds to a numbered result of the paper; `cube_main` is the body of 14.3.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.CubeAssembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*}

/-! ### Complement bookkeeping -/

/-- The converse of `CubeClaimThree.minorForCube_compl`: a minor vertex of the complementary
cube is a major vertex of the original one. -/
theorem majorForCube_of_compl {G : SimpleGraph V} {A B C D : Set V} (hcube : IsCube G A B C D)
    {v : V} (h : MinorForCube Gᶜ D C A B v) : MajorForCube G A B C D v := by
  have hcube' : IsCube Gᶜ D C A B := CubeComplement.isCube_compl hcube
  have h1 : MajorForCube Gᶜᶜ B A D C v := CubeComplement.majorForCube_compl hcube' h
  rw [compl_compl] at h1
  exact CubeClaimThree.majorForCube_swap h1

/-- *"A vertex of `V(K)` is a `Gᶜ`-attachment of `Y₁` exactly when it is not `Y₁`-complete in
`G`"*, in the direction the proof uses: if all `Gᶜ`-attachments of `Y₁` lie in `S`, then `Y₁` is
complete to every part `T` of `V(K)` disjoint from `S`. -/
theorem complete_of_att_compl {G : SimpleGraph V} {A B C D Y Y₁ S T : Set V}
    (hYdef : Y = {v : V | MajorForCube G A B C D v}) (hY₁Y : Y₁ ⊆ Y)
    (hsub : attachments Gᶜ Y₁ (D ∪ C ∪ A ∪ B) ⊆ S)
    (hTK : ∀ t ∈ T, t ∈ A ∪ B ∪ C ∪ D) (hTS : ∀ t ∈ T, t ∉ S) :
    Complete G Y₁ T := by
  have hKeq : D ∪ C ∪ A ∪ B = A ∪ B ∪ C ∪ D := by
    ext u; simp only [Set.mem_union]; tauto
  have hYK : ∀ v ∈ Y, v ∉ A ∪ B ∪ C ∪ D := by
    intro v hv
    rw [hYdef] at hv
    exact hv.1
  intro y hy t ht
  by_contra hnadj
  refine hTS t ht (hsub ⟨by rw [hKeq]; exact hTK t ht, y, hy, ?_, ?_⟩)
  · intro he
    exact hYK y (hY₁Y hy) (by rw [← he]; exact hTK t ht)
  · exact fun hadj => hnadj hadj.symm

/-! ### Claim (1) -/

/-- **Claim (1) of the proof of 14.3** (printed p. 91).

PAPER: *"Every anticomponent `Y₁` of `Y` is complete to one of `A ∪ B`, `C ∪ D`, `A ∪ D`,
`B ∪ C` … This is immediate from 14.2 by taking complements."*

Only the first sentence is proved here; the *"Moreover"* half (*"every edge from `A ∪ D` to
`B ∪ C` has a `Y₁`-complete end"*) is used only inside `CubeFinish`, which derives it inline. -/
theorem cube_claim_one [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D Y : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    (hYdef : Y = {v : V | MajorForCube G A B C D v})
    (Y₁ : Set V) (hY₁ : IsAnticomponent G Y Y₁) :
    Complete G Y₁ (A ∪ B) ∨ Complete G Y₁ (C ∪ D) ∨
      Complete G Y₁ (A ∪ D) ∨ Complete G Y₁ (B ∪ C) := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, -⟩, -, -⟩ := hcube.1
  have hYmaj : ∀ v ∈ Y, MajorForCube G A B C D v := by intro v hv; rw [hYdef] at hv; exact hv
  have hYK : ∀ v ∈ Y, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hYmaj v hv).1
  have hY₁Y : Y₁ ⊆ Y := hY₁.1
  have hKeq : D ∪ C ∪ A ∪ B = A ∪ B ∪ C ∪ D := by
    ext u; simp only [Set.mem_union]; tauto
  -- 14.2, applied in `Gᶜ` to the complementary cube `(D, C, A, B)` and the connected set `Y₁`
  have hG' : InF5 Gᶜ := ClassLemmas.inF5_compl.mpr hG
  have hcube' : MaximalCube Gᶜ D C A B := CubeComplement.maximalCube_compl hcube
  have hY₁sub : Y₁ ⊆ (D ∪ C ∪ A ∪ B)ᶜ := by
    intro y hy hmem
    rw [hKeq] at hmem
    exact hYK y (hY₁Y hy) hmem
  have hY₁minor : ∀ y ∈ Y₁, MinorForCube Gᶜ D C A B y :=
    fun y hy => CubeClaimThree.minorForCube_compl hcube.1 (hYmaj y (hY₁Y hy))
  have h142 := _root_.Workspace.Statements.S14.SPGT.thm_14_2 Gᶜ hG' D C A B hcube' Y₁
    hY₁sub hY₁.2.1 hY₁minor (attachments Gᶜ Y₁ (D ∪ C ∪ A ∪ B)) rfl
  rcases h142.1 with h | h | h | h
  · -- attachments in `D ∪ C`, so `Y₁` is complete to `A ∪ B`
    refine Or.inl (complete_of_att_compl hYdef hY₁Y h ?_ ?_)
    · rintro t (ht | ht)
      · exact Or.inl (Or.inl (Or.inl ht))
      · exact Or.inl (Or.inl (Or.inr ht))
    · rintro t (ht | ht) (hs | hs)
      · exact Set.disjoint_left.mp dAD ht hs
      · exact Set.disjoint_left.mp dAC ht hs
      · exact Set.disjoint_left.mp dBD ht hs
      · exact Set.disjoint_left.mp dBC ht hs
  · -- attachments in `A ∪ B`, so `Y₁` is complete to `C ∪ D`
    refine Or.inr (Or.inl (complete_of_att_compl hYdef hY₁Y h ?_ ?_))
    · rintro t (ht | ht)
      · exact Or.inl (Or.inr ht)
      · exact Or.inr ht
    · rintro t (ht | ht) (hs | hs)
      · exact Set.disjoint_left.mp dAC hs ht
      · exact Set.disjoint_left.mp dBC hs ht
      · exact Set.disjoint_left.mp dAD hs ht
      · exact Set.disjoint_left.mp dBD hs ht
  · -- attachments in `D ∪ A`, so `Y₁` is complete to `B ∪ C`
    refine Or.inr (Or.inr (Or.inr (complete_of_att_compl hYdef hY₁Y h ?_ ?_)))
    · rintro t (ht | ht)
      · exact Or.inl (Or.inl (Or.inr ht))
      · exact Or.inl (Or.inr ht)
    · rintro t (ht | ht) (hs | hs)
      · exact Set.disjoint_left.mp dBD ht hs
      · exact Set.disjoint_left.mp dAB hs ht
      · exact Set.disjoint_left.mp dCD ht hs
      · exact Set.disjoint_left.mp dAC hs ht
  · -- attachments in `C ∪ B`, so `Y₁` is complete to `A ∪ D`
    refine Or.inr (Or.inr (Or.inl (complete_of_att_compl hYdef hY₁Y h ?_ ?_)))
    · rintro t (ht | ht)
      · exact Or.inl (Or.inl (Or.inl ht))
      · exact Or.inr ht
    · rintro t (ht | ht) (hs | hs)
      · exact Set.disjoint_left.mp dAC ht hs
      · exact Set.disjoint_left.mp dAB ht hs
      · exact Set.disjoint_left.mp dCD hs ht
      · exact Set.disjoint_left.mp dBD hs ht

/-! ### The closing paragraph, from *"Hence `Y` is complete to `C ∪ D`"* -/

/-- PAPER (printed p. 91), the closing paragraph of 14.3 from *"By (4), passing to the complement
if necessary, we may assume that there is no anticomponent of `Y` that is complete to `A ∪ B`"*
onwards.

The hypothesis `hnoAB` is exactly the assumption the paper makes at that point.  Everything from
*"Hence `Y` is complete to `C ∪ D`, by (1) and (2)"* to the end is here: claim (1) plus claim (2)
force `Y` complete to `C ∪ D`; the second assertion of claim (4) then kills the components of `F`
with attachments in `C ∪ D`, and claim (3) with 14.2 confines every attachment of `F` to
`A ∪ B`; `CubeFinish.cube_finish` is the resulting contradiction. -/
theorem cube_tail [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D F Y : Set V}
    (hG : InF5 G) (hno : ¬ AdmitsBalancedSkewPartition G)
    (hcube : MaximalCube G A B C D)
    (hFdef : F = {v : V | MinorForCube G A B C D v})
    (hYdef : Y = {v : V | MajorForCube G A B C D v})
    (hFne : F.Nonempty) (hYne : Y.Nonempty)
    (hnoAB : ∀ Y₁ : Set V, IsAnticomponent G Y Y₁ → Y₁.Nonempty → ¬ Complete G Y₁ (A ∪ B)) :
    False := by
  classical
  have hFmin : ∀ v ∈ F, MinorForCube G A B C D v := by intro v hv; rw [hFdef] at hv; exact hv
  have hFK : ∀ v ∈ F, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hFmin v hv).1
  -- claim (2), in both of its two forms
  have hclaim2 : ∀ Y₁ : Set V, IsAnticomponent G Y Y₁ → Y₁.Nonempty →
      ¬ Complete G Y₁ (A ∪ D) ∧ ¬ Complete G Y₁ (B ∪ C) := by
    intro Y₁ hY₁ hY₁ne
    constructor
    · intro hcomp
      exact CubeClaimTwo.cube_claim_two hG hno hcube hYdef hYne Y₁ hY₁ hcomp
    · intro hcomp
      -- *"from the symmetry"*: the swapped cube `(B, A, D, C)` has `A' ∪ D' = B ∪ C`
      have hYdef' : Y = {v : V | MajorForCube G B A D C v} := by
        rw [hYdef]
        ext v
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => CubeClaimThree.majorForCube_swap h,
          fun h => CubeClaimThree.majorForCube_swap h⟩
      exact CubeClaimTwo.cube_claim_two hG hno (CubeClaimThree.maximalCube_swap hcube) hYdef'
        hYne Y₁ hY₁ hcomp
  -- *"Hence `Y` is complete to `C ∪ D`, by (1) and (2)."*
  have hYCD : Complete G Y (C ∪ D) := by
    intro y hy z hz
    obtain ⟨Y₁, hY₁, hyY₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ Y hy
    have hY₁a : IsAnticomponent G Y Y₁ := hY₁
    have hY₁ne : Y₁.Nonempty := ⟨y, hyY₁⟩
    rcases cube_claim_one hG hcube hYdef Y₁ hY₁a with h | h | h | h
    · exact absurd h (hnoAB Y₁ hY₁a hY₁ne)
    · exact h y hyY₁ z hz
    · exact absurd h (hclaim2 Y₁ hY₁a hY₁ne).1
    · exact absurd h (hclaim2 Y₁ hY₁a hY₁ne).2
  -- *"Since `Y` is nonempty, it follows from (4) that there is no component `F₁` of `F` with set
  -- of attachments contained in `C ∪ D`"*
  obtain ⟨y₀, hy₀⟩ := hYne
  obtain ⟨Y₀, hY₀, hy₀Y₀⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ Y hy₀
  have hY₀a : IsAnticomponent G Y Y₀ := hY₀
  have hY₀ne : Y₀.Nonempty := ⟨y₀, hy₀Y₀⟩
  have hY₀CD : Complete G Y₀ (C ∪ D) := fun y hy z hz => hYCD y (hY₀.1 hy) z hz
  have hnoCD : ∀ F₁ : Set V, IsComponent G F F₁ → F₁.Nonempty →
      ¬ (∀ w ∈ attachments G F₁ (A ∪ B ∪ C ∪ D), w ∈ C ∪ D) := by
    intro F₁ hF₁ hF₁ne hatt
    exact CubeClaimFourCD.cube_claim_four_cd hG hno hcube hFdef hYdef F₁ hF₁ hF₁ne hatt
      Y₀ hY₀a hY₀ne hY₀CD
  -- *"so by (3), all attachments of `F` belong to `A ∪ B`"*
  have hFatt : ∀ F₁ : Set V, IsComponent G F F₁ →
      ∀ w ∈ attachments G F₁ (A ∪ B ∪ C ∪ D), w ∈ A ∪ B := by
    intro F₁ hF₁ w hw
    have hF₁ne : F₁.Nonempty := ComponentsOfSetBasics.nonempty_of_isComponent G hFne hF₁
    have h142 := _root_.Workspace.Statements.S14.SPGT.thm_14_2 G hG A B C D hcube F₁
      (fun v hv => hFK v (hF₁.1 hv)) hF₁.2.1 (fun v hv => hFmin v (hF₁.1 hv))
      (attachments G F₁ (A ∪ B ∪ C ∪ D)) rfl
    rcases h142.1 with h | h | h | h
    · exact h hw
    · exact absurd (fun u hu => h hu) (hnoCD F₁ hF₁ hF₁ne)
    · exact (CubeClaimThree.cube_claim_three hG hno hcube hFdef hFne F₁ hF₁
        (Or.inl (fun u hu => h hu))).elim
    · exact (CubeClaimThree.cube_claim_three hG hno hcube hFdef hFne F₁ hF₁
        (Or.inr (fun u hu => h hu))).elim
  -- the second 4.5-style construction
  exact CubeFinish.cube_finish hG hno hcube hFdef hYdef ⟨y₀, hy₀⟩ hYCD hFatt

/-! ### The body of 14.3 -/

/-- PAPER (printed p. 91): the proof of 14.3 from *"Let `F` be the set of all minor vertices in
`V(G) \ V(K)`, and `Y` the set of all major ones"* to the end.

`hG`, `h2G`, `h2Gc`, `hno` are the opening sentence *"We may assume that `G, Ḡ` do not admit
proper 2-joins, and `G` does not admit a balanced skew partition"*, and `hcube` is *"there is a
maximal cube `(A, B, C, D)` in `G`, forming `K`"*. -/
theorem cube_main [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D : Set V}
    (hG : InF5 G) (h2G : ¬ AdmitsProper2Join G) (h2Gc : ¬ AdmitsProper2Join Gᶜ)
    (hno : ¬ AdmitsBalancedSkewPartition G) (hcube : MaximalCube G A B C D) :
    False := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, -⟩, -, -⟩ := hcube.1
  -- *"Let `F` be the set of all minor vertices in `V(G) \ V(K)`, and `Y` the set of all major
  -- ones."*
  obtain ⟨F, hFdef⟩ : ∃ S : Set V, S = {v : V | MinorForCube G A B C D v} := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ S : Set V, S = {v : V | MajorForCube G A B C D v} := ⟨_, rfl⟩
  -- the same data read in `Gᶜ`, where the cube is `(D, C, A, B)` and `F`, `Y` swap roles
  have hG' : InF5 Gᶜ := ClassLemmas.inF5_compl.mpr hG
  have hno' : ¬ AdmitsBalancedSkewPartition Gᶜ := fun hc =>
    hno (ClassLemmas.admitsBalancedSkewPartition_compl.mp hc)
  have hcube' : MaximalCube Gᶜ D C A B := CubeComplement.maximalCube_compl hcube
  have hFdef' : Y = {v : V | MinorForCube Gᶜ D C A B v} := by
    rw [hYdef]
    ext v
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => CubeClaimThree.minorForCube_compl hcube.1 h,
      fun h => majorForCube_of_compl hcube.1 h⟩
  have hYdef' : F = {v : V | MajorForCube Gᶜ D C A B v} := by
    rw [hFdef]
    ext v
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => CubeComplement.majorForCube_compl hcube.1 h,
      fun h => CubeClaimThree.minorForCube_of_compl hcube.1 h⟩
  -- *"Now if `Y = ∅`, then by (3) it follows that `G` admits a proper 2-join, a contradiction.
  -- So `Y` is nonempty"*
  have hYne : Y.Nonempty := by
    rcases Set.eq_empty_or_nonempty Y with hY | hY
    · exfalso
      refine h2G (TwoJoinFromSeparation.cube_admitsProper2Join_of_no_major hG hcube hFdef hYdef
        hY ?_)
      intro F₁ hF₁ hF₁ne
      obtain ⟨x, hx⟩ := hF₁ne
      have hFne : F.Nonempty := ⟨x, hF₁.1 hx⟩
      exact ⟨fun hsub => CubeClaimThree.cube_claim_three hG hno hcube hFdef hFne F₁ hF₁
          (Or.inl (fun u hu => hsub hu)),
        fun hsub => CubeClaimThree.cube_claim_three hG hno hcube hFdef hFne F₁ hF₁
          (Or.inr (fun u hu => hsub hu))⟩
    · exact hY
  -- claim (2), which is what claim (3) becomes in `Gᶜ`
  have hclaim2 : ∀ Y₁ : Set V, IsAnticomponent G Y Y₁ → Y₁.Nonempty →
      ¬ Complete G Y₁ (A ∪ D) ∧ ¬ Complete G Y₁ (B ∪ C) := by
    intro Y₁ hY₁ hY₁ne
    constructor
    · intro hcomp
      exact CubeClaimTwo.cube_claim_two hG hno hcube hYdef hYne Y₁ hY₁ hcomp
    · intro hcomp
      have hYdef₂ : Y = {v : V | MajorForCube G B A D C v} := by
        rw [hYdef]
        ext v
        simp only [Set.mem_setOf_eq]
        exact ⟨fun h => CubeClaimThree.majorForCube_swap h,
          fun h => CubeClaimThree.majorForCube_swap h⟩
      exact CubeClaimTwo.cube_claim_two hG hno (CubeClaimThree.maximalCube_swap hcube) hYdef₂
        hYne Y₁ hY₁ hcomp
  -- *"and by taking complements, `F` is nonempty"*
  have hFne : F.Nonempty := by
    rcases Set.eq_empty_or_nonempty F with hF | hF
    · exfalso
      refine h2Gc (TwoJoinFromSeparation.cube_admitsProper2Join_of_no_major hG' hcube' hFdef'
        hYdef' hF ?_)
      intro Y₁ hY₁ hY₁ne
      have hY₁a : IsAnticomponent G Y Y₁ := hY₁
      constructor
      · intro hsub
        refine (hclaim2 Y₁ hY₁a hY₁ne).2 (complete_of_att_compl hYdef hY₁a.1 hsub ?_ ?_)
        · rintro t (ht | ht)
          · exact Or.inl (Or.inl (Or.inr ht))
          · exact Or.inl (Or.inr ht)
        · rintro t (ht | ht) (hs | hs)
          · exact Set.disjoint_left.mp dBD ht hs
          · exact Set.disjoint_left.mp dAB hs ht
          · exact Set.disjoint_left.mp dCD ht hs
          · exact Set.disjoint_left.mp dAC hs ht
      · intro hsub
        refine (hclaim2 Y₁ hY₁a hY₁ne).1 (complete_of_att_compl hYdef hY₁a.1 hsub ?_ ?_)
        · rintro t (ht | ht)
          · exact Or.inl (Or.inl (Or.inl ht))
          · exact Or.inr ht
        · rintro t (ht | ht) (hs | hs)
          · exact Set.disjoint_left.mp dAC ht hs
          · exact Set.disjoint_left.mp dAB ht hs
          · exact Set.disjoint_left.mp dCD hs ht
          · exact Set.disjoint_left.mp dBD hs ht
    · exact hF
  -- *"By (4), passing to the complement if necessary, we may assume that there is no
  -- anticomponent of `Y` that is complete to `A ∪ B`."*
  by_cases hAB : ∀ Y₁ : Set V, IsAnticomponent G Y Y₁ → Y₁.Nonempty → ¬ Complete G Y₁ (A ∪ B)
  · exact cube_tail hG hno hcube hFdef hYdef hFne hYne hAB
  · -- such an anticomponent exists, so by claim (4) no component of `F` attaches inside `A ∪ B`
    have hex : ∃ Y₁ : Set V, IsAnticomponent G Y Y₁ ∧ Y₁.Nonempty ∧ Complete G Y₁ (A ∪ B) := by
      by_contra hcon
      exact hAB (fun Y₁ h1 h2 h3 => hcon ⟨Y₁, h1, h2, h3⟩)
    obtain ⟨Y₁, hY₁, hY₁ne, hY₁AB⟩ := hex
    -- read in `Gᶜ`, that is *"no anticomponent of the majors is complete to `A' ∪ B' = D ∪ C`"*
    refine cube_tail hG' hno' hcube' hFdef' hYdef' hYne hFne ?_
    intro Z hZ hZne hZcomp
    have hZc : IsComponent G F Z := by
      have hZ' : IsComponent Gᶜᶜ F Z := hZ
      rwa [compl_compl] at hZ'
    have hatt : ∀ w ∈ attachments G Z (A ∪ B ∪ C ∪ D), w ∈ A ∪ B := by
      intro w hw
      obtain ⟨hwK, f, hf, hadj⟩ := hw
      rcases hwK with ((h | h) | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hadj.symm (hZcomp f hf w (Or.inr h)).2
      · exact absurd hadj.symm (hZcomp f hf w (Or.inl h)).2
    exact CubeClaimFour.cube_claim_four hG hno hcube hFdef hYdef Z hZc hZne hatt
      Y₁ hY₁ hY₁ne hY₁AB

end Workspace.ProofLemmas.CubeAssembly
