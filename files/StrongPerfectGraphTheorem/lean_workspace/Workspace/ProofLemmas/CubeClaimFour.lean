import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.CubeExtraction
import Workspace.Statements.S04.Thm_4_5
import Workspace.Statements.S14.Thm_14_2

/-!
# Claim (4) of the proof of 14.3

PAPER (printed p. 91):

> *"(4) There do not exist both a component `F₁` of `F` with set of attachments contained in
> `A ∪ B` and an anticomponent `Y₁` of `Y` complete to `A ∪ B` …*
>
> *For the first assertion, assume that such `F₁, Y₁` exist.  Define `M = C ∪ D ∪ (F \ F₁)`, and
> `X` to be the set of all `Y₁`-complete vertices in `V(G) \ (M ∪ F₁)`.  So `A ∪ B ⊆ X`, and the
> four sets `F₁, M, Y₁, X` are all nonempty and form a partition of `V(G)`.  Since `Y₁` is complete
> to `X` and there are no edges between `F₁` and `M`, it follows that `(F₁ ∪ M, Y₁ ∪ X)` is a skew
> partition of `G`.  Choose `a ∈ A` and `b ∈ B`, nonadjacent.  By 14.2, not both `a, b` are
> attachments of `F₁`, and therefore the skew partition is loose, and so by 4.5 `G` admits a
> balanced skew partition, a contradiction."*

Only the first assertion is proved here; the second is this one applied to `Gᶜ` through
`CubeComplement`, exactly as claim (3) is claim (2) complemented.

As in `CubeClaimTwo`, `thm_4_5` consumes the four-set data directly, so no explicit
`IsSkewPartition` is built and the printed appeal to 4.2 is not needed.  *"Not both `a, b` are
attachments"* becomes the **first** disjunct of 4.5's hypothesis: whichever of `a, b` is not an
attachment is a vertex of `X ∪ Y₁` anticomplete to `F₁`.

`not_minor_major` is reproved here (it is `private` in `CubeClaimTwo`) because claim (4), the
`2`-join step and the assembly all need it.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.CubeClaimFour

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*}

/-! ### What a square gives -/

theorem square_ends {G : SimpleGraph V} {A B : Set V} {a₁ b₁ b₂ a₂ : V}
    (h : IsSquare G A B a₁ b₁ b₂ a₂) : ¬ G.Adj a₁ b₂ := by
  obtain ⟨hhole, -, -, -, -⟩ := h
  have h2 := HoleBasics.hole_adj_iff hhole
    (show (0 : ℕ) < ([a₁, b₁, b₂, a₂] : List V).length by simp)
    (show (2 : ℕ) < ([a₁, b₁, b₂, a₂] : List V).length by simp)
  simpa using h2

theorem square_adj {G : SimpleGraph V} {A B : Set V} {a₁ b₁ b₂ a₂ : V}
    (h : IsSquare G A B a₁ b₁ b₂ a₂) : G.Adj a₁ b₁ := by
  obtain ⟨hhole, -, -, -, -⟩ := h
  have h2 := HoleBasics.hole_adj_iff hhole
    (show (0 : ℕ) < ([a₁, b₁, b₂, a₂] : List V).length by simp)
    (show (1 : ℕ) < ([a₁, b₁, b₂, a₂] : List V).length by simp)
  have h3 : G.Adj (([a₁, b₁, b₂, a₂] : List V)[0]'(by simp))
      (([a₁, b₁, b₂, a₂] : List V)[1]'(by simp)) := h2.mpr (Or.inl (by simp))
  simpa using h3

/-- A square-connected pair contains a non-adjacent cross pair. -/
theorem exists_nonadj_of_squareConnected {G : SimpleGraph V} {A B : Set V}
    (h : SquareConnected G A B) : ∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b := by
  obtain ⟨⟨hAnt, -⟩, h1, -⟩ := h
  obtain ⟨a₀, ha₀⟩ := hAnt.nonempty
  obtain ⟨a', ha', hne⟩ := hAnt.exists_ne a₀
  obtain ⟨a₁, b₁, b₂, a₂, hsq, -, -⟩ :=
    h1 ({a₀} : Set V) (A \ ({a₀} : Set V)) (Set.union_diff_cancel (by simpa using ha₀))
      (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx)) ⟨a₀, rfl⟩ ⟨a', ha', hne⟩
  exact ⟨a₁, hsq.2.1, b₂, hsq.2.2.2.2, square_ends hsq⟩

/-- An antisquare-connected pair contains a non-adjacent cross pair too — the two ends of a
`Gᶜ`-**edge** of the antisquare. -/
theorem exists_nonadj_of_antisquareConnected {G : SimpleGraph V} {C D : Set V}
    (h : AntisquareConnected G C D) : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d := by
  obtain ⟨⟨hCnt, -⟩, h1, -⟩ := h
  obtain ⟨c₀, hc₀⟩ := hCnt.nonempty
  obtain ⟨c', hc', hne⟩ := hCnt.exists_ne c₀
  obtain ⟨a₁, b₁, b₂, a₂, hsq, -, -⟩ :=
    h1 ({c₀} : Set V) (C \ ({c₀} : Set V)) (Set.union_diff_cancel (by simpa using hc₀))
      (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx)) ⟨c₀, rfl⟩ ⟨c', hc', hne⟩
  exact ⟨a₁, hsq.2.1, b₁, hsq.2.2.2.1, (square_adj hsq).2⟩

/-! ### No vertex is both minor and major -/

/-- PAPER (printed p. 88): the two cases of 14.1 are exclusive, so the set of minor vertices and
the set of major vertices are disjoint. -/
theorem not_minor_major {G : SimpleGraph V} {A B C D : Set V} (hcube : IsCube G A B C D)
    {v : V} (hmin : MinorForCube G A B C D v) (hmaj : MajorForCube G A B C D v) : False := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, ⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩, ⟨c₀, hc₀⟩, ⟨d₀, hd₀⟩⟩,
    ⟨-, -, -, -⟩, hsqAB, hsqCD⟩ := hcube
  obtain ⟨-, hminsub, hmincomp⟩ := hmin
  obtain ⟨-, hmajsup, -⟩ := hmaj
  have naCD : a₀ ∉ C ∪ D := fun h => h.elim (Set.disjoint_left.mp dAC ha₀)
    (Set.disjoint_left.mp dAD ha₀)
  have naBD : a₀ ∉ B ∪ D := fun h => h.elim (Set.disjoint_left.mp dAB ha₀)
    (Set.disjoint_left.mp dAD ha₀)
  have nbCD : b₀ ∉ C ∪ D := fun h => h.elim (Set.disjoint_left.mp dBC hb₀)
    (Set.disjoint_left.mp dBD hb₀)
  have nbAC : b₀ ∉ A ∪ C := fun h => h.elim (fun hh => Set.disjoint_left.mp dAB hh hb₀)
    (Set.disjoint_left.mp dBC hb₀)
  have ncAB : c₀ ∉ A ∪ B := fun h => h.elim (fun hh => Set.disjoint_left.mp dAC hh hc₀)
    (fun hh => Set.disjoint_left.mp dBC hh hc₀)
  have ncBD : c₀ ∉ B ∪ D := fun h => h.elim (fun hh => Set.disjoint_left.mp dBC hh hc₀)
    (fun hh => Set.disjoint_left.mp dCD hc₀ hh)
  have ndAB : d₀ ∉ A ∪ B := fun h => h.elim (fun hh => Set.disjoint_left.mp dAD hh hd₀)
    (fun hh => Set.disjoint_left.mp dBD hh hd₀)
  have ndAC : d₀ ∉ A ∪ C := fun h => h.elim (fun hh => Set.disjoint_left.mp dAD hh hd₀)
    (fun hh => Set.disjoint_left.mp dCD hh hd₀)
  have hnotAB : ¬ Complete G A B := by
    obtain ⟨a, ha, b, hb, hnadj⟩ := exists_nonadj_of_squareConnected hsqAB
    exact fun hc => hnadj (hc a ha b hb)
  have hnotCD : ¬ Complete G C D := by
    obtain ⟨c, hc, d, hd, hnadj⟩ := exists_nonadj_of_antisquareConnected hsqCD
    exact fun hcp => hnadj (hcp c hc d hd)
  rcases hmajsup with hsup | hsup | hsup | hsup
  · rcases hminsub with hsub | hsub | hsub | hsub
    · exact hnotAB fun x hx y hy =>
        hmincomp x ⟨hsup (Or.inl hx), Or.inl hx⟩ y ⟨hsup (Or.inr hy), Or.inl hy⟩
    · exact nbCD (hsub (hsup (Or.inr hb₀)))
    · exact nbAC (hsub (hsup (Or.inr hb₀)))
    · exact naBD (hsub (hsup (Or.inl ha₀)))
  · rcases hminsub with hsub | hsub | hsub | hsub
    · exact ncAB (hsub (hsup (Or.inl hc₀)))
    · exact hnotCD fun x hx y hy =>
        hmincomp x ⟨hsup (Or.inl hx), Or.inr hx⟩ y ⟨hsup (Or.inr hy), Or.inr hy⟩
    · exact ndAC (hsub (hsup (Or.inr hd₀)))
    · exact ncBD (hsub (hsup (Or.inl hc₀)))
  · rcases hminsub with hsub | hsub | hsub | hsub
    · exact ndAB (hsub (hsup (Or.inr hd₀)))
    · exact naCD (hsub (hsup (Or.inl ha₀)))
    · exact ndAC (hsub (hsup (Or.inr hd₀)))
    · exact naBD (hsub (hsup (Or.inl ha₀)))
  · rcases hminsub with hsub | hsub | hsub | hsub
    · exact ncAB (hsub (hsup (Or.inr hc₀)))
    · exact nbCD (hsub (hsup (Or.inl hb₀)))
    · exact nbAC (hsub (hsup (Or.inl hb₀)))
    · exact ncBD (hsub (hsup (Or.inr hc₀)))

/-! ### Claim (4) -/

theorem cube_claim_four [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D F Y : Set V}
    (hG : InF5 G) (hno : ¬ AdmitsBalancedSkewPartition G)
    (hcube : MaximalCube G A B C D)
    (hFdef : F = {v : V | MinorForCube G A B C D v})
    (hYdef : Y = {v : V | MajorForCube G A B C D v})
    (F₁ : Set V) (hF₁ : IsComponent G F F₁) (hF₁ne : F₁.Nonempty)
    (hF₁att : ∀ w ∈ attachments G F₁ (A ∪ B ∪ C ∪ D), w ∈ A ∪ B)
    (Y₁ : Set V) (hY₁ : IsAnticomponent G Y Y₁) (hY₁ne : Y₁.Nonempty)
    (hcomp : Complete G Y₁ (A ∪ B)) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, hAne, hBne, hCne, hDne⟩,
    ⟨cAC, cBD, aAD, aBC⟩, hsqAB, hsqCD⟩ := hcube.1
  obtain ⟨M, hM⟩ : ∃ S : Set V, S = C ∪ D ∪ (F \ F₁) := ⟨_, rfl⟩
  obtain ⟨Xs, hX⟩ : ∃ S : Set V, S = {v : V | v ∉ M ∪ F₁ ∧ VertexComplete G v Y₁} := ⟨_, rfl⟩
  -- basic memberships
  have hFmin : ∀ v ∈ F, MinorForCube G A B C D v := by intro v hv; rw [hFdef] at hv; exact hv
  have hYmaj : ∀ v ∈ Y, MajorForCube G A B C D v := by intro v hv; rw [hYdef] at hv; exact hv
  have hFK : ∀ v ∈ F, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hFmin v hv).1
  have hYK : ∀ v ∈ Y, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hYmaj v hv).1
  have hFYd : ∀ v, v ∈ F → v ∈ Y → False :=
    fun v hvF hvY => not_minor_major hcube.1 (hFmin v hvF) (hYmaj v hvY)
  have hF₁F : F₁ ⊆ F := hF₁.1
  have hY₁Y : Y₁ ⊆ Y := hY₁.1
  -- `A ∪ B ⊆ X`
  have hABX : ∀ v ∈ A ∪ B, v ∈ Xs := by
    intro v hv
    have hvK : v ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inl hv)
    have hvF : v ∉ F := fun hc => hFK v hc hvK
    rw [hX]
    refine ⟨?_, fun y hy => (hcomp y hy v hv).symm⟩
    rintro (hvM | hvF₁)
    · rw [hM] at hvM
      rcases hvM with (hvC | hvD) | hvFd
      · exact (hv.elim (fun h => Set.disjoint_left.mp dAC h hvC)
          (fun h => Set.disjoint_left.mp dBC h hvC))
      · exact (hv.elim (fun h => Set.disjoint_left.mp dAD h hvD)
          (fun h => Set.disjoint_left.mp dBD h hvD))
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
  -- no edges between `F₁` and `M`
  have hF₁M : Anticomplete G F₁ M := by
    intro f hf m hm hadj
    rw [hM] at hm
    rcases hm with (hmC | hmD) | hmF
    · have hatt : m ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) :=
        ⟨Or.inl (Or.inr hmC), f, hf, hadj.symm⟩
      rcases hF₁att m hatt with h | h
      · exact Set.disjoint_left.mp dAC h hmC
      · exact Set.disjoint_left.mp dBC h hmC
    · have hatt : m ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) := ⟨Or.inr hmD, f, hf, hadj.symm⟩
      rcases hF₁att m hatt with h | h
      · exact Set.disjoint_left.mp dAD h hmD
      · exact Set.disjoint_left.mp dBD h hmD
    · obtain ⟨P, hP, hmP⟩ := ComponentsOfSetBasics.exists_isComponent_mem G F hmF.1
      have hPne : P ≠ F₁ := fun he => hmF.2 (by rw [← he]; exact hmP)
      exact ComponentsOfSetBasics.anticomplete_of_isComponent G hP hF₁ hPne m hmP f hf hadj.symm
  -- "Choose `a ∈ A` and `b ∈ B`, nonadjacent.  By 14.2, not both `a, b` are attachments of `F₁`."
  obtain ⟨a, ha, b, hb, hnadjab⟩ := exists_nonadj_of_squareConnected hsqAB
  have h142 := _root_.Workspace.Statements.S14.SPGT.thm_14_2 G hG A B C D hcube F₁
    (fun v hv => hFK v (hF₁F hv)) hF₁.2.1 (fun v hv => hFmin v (hF₁F hv))
    (attachments G F₁ (A ∪ B ∪ C ∪ D)) rfl
  have hnotboth : ¬ (a ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) ∧
      b ∈ attachments G F₁ (A ∪ B ∪ C ∪ D)) := by
    rintro ⟨hA', hB'⟩
    exact hnadjab (h142.2 a ⟨hA', Or.inl ha⟩ b ⟨hB', Or.inl hb⟩)
  -- whichever of `a, b` is not an attachment is anticomplete to `F₁`
  have hloose : ∃ v ∈ Xs ∪ Y₁, VertexAnticomplete G v F₁ ∨ VertexAnticomplete G v M := by
    by_cases hA' : a ∈ attachments G F₁ (A ∪ B ∪ C ∪ D)
    · have hB' : b ∉ attachments G F₁ (A ∪ B ∪ C ∪ D) := fun hc => hnotboth ⟨hA', hc⟩
      refine ⟨b, Or.inl (hABX b (Or.inr hb)), Or.inl (fun f hf hadj => hB' ?_)⟩
      exact ⟨Or.inl (Or.inl (Or.inr hb)), f, hf, hadj⟩
    · refine ⟨a, Or.inl (hABX a (Or.inl ha)), Or.inl (fun f hf hadj => hA' ?_)⟩
      exact ⟨Or.inl (Or.inl (Or.inl ha)), f, hf, hadj⟩
  -- 4.5
  refine hno (_root_.Workspace.Statements.S04.SPGT.thm_4_5 G hBerge Xs Y₁ F₁ M
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hF₁M ?_ (Or.inl hloose))
  · -- cover
    refine Set.eq_univ_of_forall (fun v => ?_)
    rcases hcover v with hvK | hvF | hvY
    · rcases hvK with ((hvA | hvB) | hvC) | hvD
      · exact Or.inl (Or.inl (Or.inl (hABX v (Or.inl hvA))))
      · exact Or.inl (Or.inl (Or.inl (hABX v (Or.inr hvB))))
      · exact Or.inr (by rw [hM]; exact Or.inl (Or.inl hvC))
      · exact Or.inr (by rw [hM]; exact Or.inl (Or.inr hvD))
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
          rcases hvM with (hvC | hvD) | hvFd
          · exact hYK v hvY (Or.inl (Or.inr hvC))
          · exact hYK v hvY (Or.inr hvD)
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
    rcases hxM with (hxC | hxD) | hxF
    · exact hYK x (hY₁Y hxY) (Or.inl (Or.inr hxC))
    · exact hYK x (hY₁Y hxY) (Or.inr hxD)
    · exact hFYd x hxF.1 (hY₁Y hxY)
  · refine Set.disjoint_left.mpr (fun x hxF hxM => ?_)
    rw [hM] at hxM
    rcases hxM with (hxC | hxD) | hxFd
    · exact hFK x (hF₁F hxF) (Or.inl (Or.inr hxC))
    · exact hFK x (hF₁F hxF) (Or.inr hxD)
    · exact hxFd.2 hxF
  · obtain ⟨a', ha'⟩ := hAne
    exact ⟨a', hABX a' (Or.inl ha')⟩
  · exact hY₁ne
  · exact hF₁ne
  · obtain ⟨c', hc'⟩ := hCne
    exact ⟨c', by rw [hM]; exact Or.inl (Or.inl hc')⟩
  · intro v hv
    rw [hX] at hv
    exact hv.2

end Workspace.ProofLemmas.CubeClaimFour
