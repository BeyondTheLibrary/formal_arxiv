import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.CubeExtraction
import Workspace.ProofLemmas.CubeClaimFour
import Workspace.Statements.S04.Thm_4_5
import Workspace.Statements.S14.Thm_14_2

/-!
# Claim (4) of the proof of 14.3 — the second assertion

PAPER (printed p. 91):

> *"(4) There do not exist both a component `F₁` of `F` with set of attachments contained in
> `A ∪ B` and an anticomponent `Y₁` of `Y` complete to `A ∪ B`; **and the same holds with
> `A ∪ B` replaced by `C ∪ D`**.*
>
> *For the first assertion, assume that such `F₁, Y₁` exist.  Define `M = C ∪ D ∪ (F \ F₁)`, and
> `X` to be the set of all `Y₁`-complete vertices in `V(G) \ (M ∪ F₁)`.  So `A ∪ B ⊆ X`, and the
> four sets `F₁, M, Y₁, X` are all nonempty and form a partition of `V(G)`.  Since `Y₁` is
> complete to `X` and there are no edges between `F₁` and `M`, it follows that `(F₁ ∪ M, Y₁ ∪ X)`
> is a skew partition of `G`.  Choose `a ∈ A` and `b ∈ B`, nonadjacent.  By 14.2, not both
> `a, b` are attachments of `F₁`, and therefore the skew partition is loose, and so by 4.5 `G`
> admits a balanced skew partition, a contradiction.  **This proves the first assertion and the
> second is proved similarly.**  This proves (4)."*

`CubeClaimFour.cube_claim_four` is the first assertion.  This module is *"the second is proved
similarly"*: the same six-step argument with `(A, B)` and `(C, D)` interchanged, i.e.
`M = A ∪ B ∪ (F \ F₁)` and `X` the set of `Y₁`-complete vertices outside `M ∪ F₁`, so that
`C ∪ D ⊆ X`.

The second assertion is **not** the first one complemented.  Under the complement transport
`(A, B, C, D) ↦ (D, C, A, B)` of `CubeComplement` the set of minor vertices and the set of major
vertices swap, and the two hypotheses of the first assertion swap with them: *"`F₁` has all its
attachments in `A ∪ B`"* becomes *"`Y₁` is complete to `A ∪ B`"* and vice versa.  So the first
assertion is self-complementary, and the `C ∪ D` assertion has to be run out in full.

Only one step of the printed argument actually changes: *"choose `a ∈ A` and `b ∈ B`,
nonadjacent"* — available because `(A, B)` is square-connected — becomes *"choose `c ∈ C` and
`d ∈ D`, nonadjacent"*, which is available because `(C, D)` is **anti**square-connected, so a
`Gᶜ`-edge of one of its antisquares is a non-edge of `G`
(`CubeClaimFour.exists_nonadj_of_antisquareConnected`).  The appeal to 14.2 goes through
unchanged: `c ∈ C ⊆ A ∪ C` and `d ∈ D ⊆ B ∪ D`, so the *"Moreover"* clause of 14.2 would make
`c, d` adjacent if both were attachments of `F₁`.

As in `CubeClaimFour`, `thm_4_5` consumes the four-set data directly, so no explicit
`IsSkewPartition` is built and the printed appeal to 4.2 is not needed; *"not both `c, d` are
attachments"* becomes 4.5's **first** disjunct.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.CubeClaimFourCD

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*}

/-- **Claim (4) of the proof of 14.3, second assertion** (printed p. 91): *"the same holds with
`A ∪ B` replaced by `C ∪ D`"*, i.e. there do not exist both a component `F₁` of `F` with set of
attachments contained in `C ∪ D` and an anticomponent `Y₁` of `Y` complete to `C ∪ D`. -/
theorem cube_claim_four_cd [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D F Y : Set V}
    (hG : InF5 G) (hno : ¬ AdmitsBalancedSkewPartition G)
    (hcube : MaximalCube G A B C D)
    (hFdef : F = {v : V | MinorForCube G A B C D v})
    (hYdef : Y = {v : V | MajorForCube G A B C D v})
    (F₁ : Set V) (hF₁ : IsComponent G F F₁) (hF₁ne : F₁.Nonempty)
    (hF₁att : ∀ w ∈ attachments G F₁ (A ∪ B ∪ C ∪ D), w ∈ C ∪ D)
    (Y₁ : Set V) (hY₁ : IsAnticomponent G Y Y₁) (hY₁ne : Y₁.Nonempty)
    (hcomp : Complete G Y₁ (C ∪ D)) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, hAne, hBne, hCne, hDne⟩,
    ⟨cAC, cBD, aAD, aBC⟩, hsqAB, hsqCD⟩ := hcube.1
  -- *"Define `M = A ∪ B ∪ (F \ F₁)`, and `X` to be the set of all `Y₁`-complete vertices in
  -- `V(G) \ (M ∪ F₁)`."*
  obtain ⟨M, hM⟩ : ∃ S : Set V, S = A ∪ B ∪ (F \ F₁) := ⟨_, rfl⟩
  obtain ⟨Xs, hX⟩ : ∃ S : Set V, S = {v : V | v ∉ M ∪ F₁ ∧ VertexComplete G v Y₁} := ⟨_, rfl⟩
  -- basic memberships
  have hFmin : ∀ v ∈ F, MinorForCube G A B C D v := by intro v hv; rw [hFdef] at hv; exact hv
  have hYmaj : ∀ v ∈ Y, MajorForCube G A B C D v := by intro v hv; rw [hYdef] at hv; exact hv
  have hFK : ∀ v ∈ F, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hFmin v hv).1
  have hYK : ∀ v ∈ Y, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hYmaj v hv).1
  have hFYd : ∀ v, v ∈ F → v ∈ Y → False :=
    fun v hvF hvY => CubeClaimFour.not_minor_major hcube.1 (hFmin v hvF) (hYmaj v hvY)
  have hF₁F : F₁ ⊆ F := hF₁.1
  have hY₁Y : Y₁ ⊆ Y := hY₁.1
  -- *"So `C ∪ D ⊆ X`"*
  have hCDX : ∀ v ∈ C ∪ D, v ∈ Xs := by
    intro v hv
    have hvK : v ∈ A ∪ B ∪ C ∪ D := by
      rcases hv with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hvF : v ∉ F := fun hc => hFK v hc hvK
    rw [hX]
    refine ⟨?_, fun y hy => (hcomp y hy v hv).symm⟩
    rintro (hvM | hvF₁)
    · rw [hM] at hvM
      rcases hvM with (hvA | hvB) | hvFd
      · exact (hv.elim (fun h => Set.disjoint_left.mp dAC hvA h)
          (fun h => Set.disjoint_left.mp dAD hvA h))
      · exact (hv.elim (fun h => Set.disjoint_left.mp dBC hvB h)
          (fun h => Set.disjoint_left.mp dBD hvB h))
      · exact hvF hvFd.1
    · exact hvF (hF₁F hvF₁)
  -- the cover
  have hcover : ∀ v : V, v ∈ A ∪ B ∪ C ∪ D ∨ v ∈ F ∨ v ∈ Y := by
    intro v
    by_cases hvK : v ∈ A ∪ B ∪ C ∪ D
    · exact Or.inl hvK
    · rcases CubeExtraction.minor_or_major G hG hcube hvK with h | h
      · exact Or.inr (Or.inl (by rw [hFdef]; exact h))
      · exact Or.inr (Or.inr (by rw [hYdef]; exact h))
  -- *"there are no edges between `F₁` and `M`"*
  have hF₁M : Anticomplete G F₁ M := by
    intro f hf m hm hadj
    rw [hM] at hm
    rcases hm with (hmA | hmB) | hmF
    · have hatt : m ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) :=
        ⟨Or.inl (Or.inl (Or.inl hmA)), f, hf, hadj.symm⟩
      rcases hF₁att m hatt with h | h
      · exact Set.disjoint_left.mp dAC hmA h
      · exact Set.disjoint_left.mp dAD hmA h
    · have hatt : m ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) :=
        ⟨Or.inl (Or.inl (Or.inr hmB)), f, hf, hadj.symm⟩
      rcases hF₁att m hatt with h | h
      · exact Set.disjoint_left.mp dBC hmB h
      · exact Set.disjoint_left.mp dBD hmB h
    · obtain ⟨P, hP, hmP⟩ := ComponentsOfSetBasics.exists_isComponent_mem G F hmF.1
      have hPne : P ≠ F₁ := fun he => hmF.2 (by rw [← he]; exact hmP)
      exact ComponentsOfSetBasics.anticomplete_of_isComponent G hP hF₁ hPne m hmP f hf hadj.symm
  -- *"Choose `c ∈ C` and `d ∈ D`, nonadjacent.  By 14.2, not both `c, d` are attachments of
  -- `F₁`."*
  obtain ⟨c, hc, d, hd, hnadjcd⟩ := CubeClaimFour.exists_nonadj_of_antisquareConnected hsqCD
  have h142 := _root_.Workspace.Statements.S14.SPGT.thm_14_2 G hG A B C D hcube F₁
    (fun v hv => hFK v (hF₁F hv)) hF₁.2.1 (fun v hv => hFmin v (hF₁F hv))
    (attachments G F₁ (A ∪ B ∪ C ∪ D)) rfl
  have hnotboth : ¬ (c ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) ∧
      d ∈ attachments G F₁ (A ∪ B ∪ C ∪ D)) := by
    rintro ⟨hC', hD'⟩
    exact hnadjcd (h142.2 c ⟨hC', Or.inr hc⟩ d ⟨hD', Or.inr hd⟩)
  -- whichever of `c, d` is not an attachment is anticomplete to `F₁`
  have hloose : ∃ v ∈ Xs ∪ Y₁, VertexAnticomplete G v F₁ ∨ VertexAnticomplete G v M := by
    by_cases hC' : c ∈ attachments G F₁ (A ∪ B ∪ C ∪ D)
    · have hD' : d ∉ attachments G F₁ (A ∪ B ∪ C ∪ D) := fun hcc => hnotboth ⟨hC', hcc⟩
      refine ⟨d, Or.inl (hCDX d (Or.inr hd)), Or.inl (fun f hf hadj => hD' ?_)⟩
      exact ⟨Or.inr hd, f, hf, hadj⟩
    · refine ⟨c, Or.inl (hCDX c (Or.inl hc)), Or.inl (fun f hf hadj => hC' ?_)⟩
      exact ⟨Or.inl (Or.inr hc), f, hf, hadj⟩
  -- 4.5
  refine hno (_root_.Workspace.Statements.S04.SPGT.thm_4_5 G hBerge Xs Y₁ F₁ M
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hF₁M ?_ (Or.inl hloose))
  · -- cover
    refine Set.eq_univ_of_forall (fun v => ?_)
    rcases hcover v with hvK | hvF | hvY
    · rcases hvK with ((hvA | hvB) | hvC) | hvD
      · exact Or.inr (by rw [hM]; exact Or.inl (Or.inl hvA))
      · exact Or.inr (by rw [hM]; exact Or.inl (Or.inr hvB))
      · exact Or.inl (Or.inl (Or.inl (hCDX v (Or.inl hvC))))
      · exact Or.inl (Or.inl (Or.inl (hCDX v (Or.inr hvD))))
    · by_cases hvF₁ : v ∈ F₁
      · exact Or.inl (Or.inr hvF₁)
      · exact Or.inr (by rw [hM]; exact Or.inr ⟨hvF, hvF₁⟩)
    · by_cases hvY₁ : v ∈ Y₁
      · exact Or.inl (Or.inl (Or.inr hvY₁))
      · refine Or.inl (Or.inl (Or.inl ?_))
        rw [hX]
        refine ⟨?_, LooseSkewPartition.vertexComplete_of_notMem_anticomponent hY₁ hvY hvY₁⟩
        rintro (hvM | hvF₁)
        · rw [hM] at hvM
          rcases hvM with (hvA | hvB) | hvFd
          · exact hYK v hvY (Or.inl (Or.inl (Or.inl hvA)))
          · exact hYK v hvY (Or.inl (Or.inl (Or.inr hvB)))
          · exact hFYd v hvFd.1 hvY
        · exact hFYd v (hF₁F hvF₁) hvY
  · exact Set.disjoint_left.mpr (fun x hxX hxY => by
      rw [hX] at hxX; exact G.irrefl (hxX.2 x hxY))
  · exact Set.disjoint_left.mpr (fun x hxX hxF => by
      rw [hX] at hxX; exact hxX.1 (Or.inr hxF))
  · exact Set.disjoint_left.mpr (fun x hxX hxM => by
      rw [hX] at hxX; exact hxX.1 (Or.inl hxM))
  · exact Set.disjoint_left.mpr (fun x hxY hxF => hFYd x (hF₁F hxF) (hY₁Y hxY))
  · refine Set.disjoint_left.mpr (fun x hxY hxM => ?_)
    rw [hM] at hxM
    rcases hxM with (hxA | hxB) | hxF
    · exact hYK x (hY₁Y hxY) (Or.inl (Or.inl (Or.inl hxA)))
    · exact hYK x (hY₁Y hxY) (Or.inl (Or.inl (Or.inr hxB)))
    · exact hFYd x hxF.1 (hY₁Y hxY)
  · refine Set.disjoint_left.mpr (fun x hxF hxM => ?_)
    rw [hM] at hxM
    rcases hxM with (hxA | hxB) | hxFd
    · exact hFK x (hF₁F hxF) (Or.inl (Or.inl (Or.inl hxA)))
    · exact hFK x (hF₁F hxF) (Or.inl (Or.inl (Or.inr hxB)))
    · exact hxFd.2 hxF
  · obtain ⟨c', hc'⟩ := hCne
    exact ⟨c', hCDX c' (Or.inl hc')⟩
  · exact hY₁ne
  · exact hF₁ne
  · obtain ⟨a', ha'⟩ := hAne
    exact ⟨a', by rw [hM]; exact Or.inl (Or.inl ha')⟩
  · intro v hv
    rw [hX] at hv
    exact hv.2

end Workspace.ProofLemmas.CubeClaimFourCD
