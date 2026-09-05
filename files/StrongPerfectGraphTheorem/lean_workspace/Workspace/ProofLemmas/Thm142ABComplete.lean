import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.DoubleDiamond
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm142PathSetup
import Workspace.ProofLemmas.Thm142FullCase
import Workspace.ProofLemmas.Thm142NonFullCase

/-!
# 14.2, the `A ∪ B` half of the *"Moreover"* clause

PAPER (printed pp. 89–90, the closing two paragraphs of the proof of 14.2):

> *"Now assume that `X ⊆ A ∪ B`.  Assume `X ∩ A` is not complete to `X ∩ B`, and choose a path
> `a-f₁-⋯-f_k-b`, where `a ∈ A`, `b ∈ B` are nonadjacent and `f₁, …, f_k ∈ F`, with `k` minimum.
> Since `f₁` is minor, its neighbours in `A` are complete to its neighbours in `B`, and so
> `k ≥ 2`.  Let `A₀` be the set of all vertices `a ∈ A` such that `a` is adjacent to `f₁` and
> there is a nonneighbour `b` of `a` in `B` adjacent to `f_k`.  By assumption `A₀ ≠ ∅`.  Define
> `B₀` similarly in `B`.  If `A₀ = A` and `B₀ = B`, then `f₁` is `A`-complete, and so there are no
> edges between `{f₁, …, f_{k-1}}` and `B`, from the minimality of `k`; and similarly `f_k` is
> `B`-complete and there are no edges between `{f₂, …, f_k}` and `A`.  Choose a square
> `a₁-b₁-b₂-a₂-a₁`; then `a₁-b₁`, `a₂-b₂`, `f₁-⋯-f_k` form a prism, so `k = 2`, and we can add
> `f₁` to `C` and `f₂` to `D`, contrary to the maximality of the cube.  So we may assume that
> `A₀ ≠ A`.  …  But then the set of neighbours of `b` in the prism formed by `a₁-b₁`, `a₂-b₂`,
> `c-d` is not local, and yet none are in the path `a₁-b₁`, contrary to 10.4.  This proves
> 14.2."*

This is the `X ⊆ A ∪ B` branch of the second assertion of 14.2.  The companion `X ⊆ C ∪ D`
branch is `Workspace.ProofLemmas.CubeAttachmentsCDComplete`; the first assertion is
`Workspace.ProofLemmas.CubeMinorAttachmentContainment`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

open Thm142ABComplete

/-- The already isolated maximality contradiction, fed by the two endpoint sets being full. -/
private theorem both_full_false {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C D F : Set V} (hG : InF5 G)
    (hcube : MaximalCube G A B C D) {f : List V} {a b : V}
    (hcfg : ABPathConfig G A B C D F f a b)
    (hleft : ∀ a' ∈ A, G.Adj a' (f[0]'(by have := hcfg.len; omega)) ∧
      ∃ b' ∈ B, ¬ G.Adj a' b' ∧
        G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega)))
    (hright : ∀ b' ∈ B, G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega)) ∧
      ∃ a' ∈ A, ¬ G.Adj a' b' ∧ G.Adj a' (f[0]'(by have := hcfg.len; omega)))
    (hCD : Anticomplete G (C ∪ D) {z : V | z ∈ f}) : False := by
  exact Thm142FullCase.full_case_false G hG A B C D hcube hcfg.path hcfg.len hcfg.outside
    (fun a' ha' _ => (hleft a' ha').1.symm)
    (fun b' hb' _ => (hright b' hb').1.symm)
    (no_B_before_last_of_right_full hcfg hright)
    (no_A_after_first_of_left_full hcfg hleft) hCD

/-- The `A`--`B` row of the attachment conclusion in 14.2. -/
theorem Thm142ABComplete {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF5 G)
    (A B C D : Set V) (hcube : MaximalCube G A B C D)
    (F : Set V) (hF : F ⊆ (A ∪ B ∪ C ∪ D)ᶜ) (hFconn : ConnectedSet G F)
    (hFminor : ∀ v ∈ F, MinorForCube G A B C D v)
    (X : Set V) (hX : X = attachments G F (A ∪ B ∪ C ∪ D))
    (hXAB : X ⊆ A ∪ B) :
    Complete G (X ∩ A) (X ∩ B) := by
  classical
  obtain ⟨⟨⟨dAB, -, -, -, -, -⟩, -, -, -, -⟩, -, -, -⟩ := hcube.1
  intro a₀ ha₀ b₀ hb₀
  by_contra ha₀b₀
  have ha₀att : a₀ ∈ attachments G F (A ∪ B ∪ C ∪ D) := by
    rw [← hX]
    exact ha₀.1
  have hb₀att : b₀ ∈ attachments G F (A ∪ B ∪ C ∪ D) := by
    rw [← hX]
    exact hb₀.1
  obtain ⟨-, x, hxF, ha₀x⟩ := ha₀att
  obtain ⟨-, y, hyF, hb₀y⟩ := hb₀att
  obtain ⟨f, a, b, hcfg⟩ := exists_minimal_ab_path G A B C D F dAB hF hFconn hFminor
    a₀ b₀ ha₀.2 hb₀.2 ha₀b₀ ⟨x, hxF, ha₀x⟩ ⟨y, hyF, hb₀y⟩
  have hCD : Anticomplete G (C ∪ D) {z : V | z ∈ f} :=
    path_anticomplete_cd hcube.1 hcfg hX hXAB
  by_cases hleft : ∀ a' ∈ A,
      G.Adj a' (f[0]'(by have := hcfg.len; omega)) ∧
        ∃ b' ∈ B, ¬ G.Adj a' b' ∧
          G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega))
  · by_cases hright : ∀ b' ∈ B,
        G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega)) ∧
          ∃ a' ∈ A, ¬ G.Adj a' b' ∧
            G.Adj a' (f[0]'(by have := hcfg.len; omega))
    · exact both_full_false hG hcube hcfg hleft hright hCD
    · have hcfg' := config_swap_reverse hcfg
      have hCD' : Anticomplete G (D ∪ C) {z : V | z ∈ f.reverse} := by
        intro z hz w hw
        exact hCD z (hz.elim Or.inr Or.inl) w (List.mem_reverse.mp hw)
      have hrevFirst :
          (f.reverse[0]'(by have := hcfg'.len; omega)) =
            f[f.length - 1]'(by have := hcfg.len; omega) := by
        simp only [List.getElem_reverse, List.length_reverse, Nat.sub_zero]
      have hrevLast :
          (f.reverse[f.reverse.length - 1]'(by have := hcfg'.len; omega)) =
            f[0]'(by have := hcfg.len; omega) := by
        simp only [List.getElem_reverse, List.length_reverse]
        congr 1
        have := hcfg.len
        omega
      have hnonfull : ∃ b' ∈ B,
          ¬ (G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega)) ∧
            ∃ a' ∈ A, ¬ G.Adj a' b' ∧
              G.Adj a' (f[0]'(by have := hcfg.len; omega))) := by
        by_contra hn
        apply hright
        intro b' hb'B
        by_contra hp
        exact hn ⟨b', hb'B, hp⟩
      have hnonfull' : ∃ b' ∈ B,
          ¬ (G.Adj b' (f.reverse[0]'(by have := hcfg'.len; omega)) ∧
            ∃ a' ∈ A, ¬ G.Adj b' a' ∧
              G.Adj a' (f.reverse[f.reverse.length - 1]'(by
                have := hcfg'.len
                omega))) := by
        obtain ⟨b', hb'B, hb'⟩ := hnonfull
        refine ⟨b', hb'B, ?_⟩
        rintro ⟨hb'first, a', ha'A, hb'a', ha'last⟩
        apply hb'
        refine ⟨?_, a', ha'A, ?_, ?_⟩
        · rwa [hrevFirst] at hb'first
        · exact fun ha'b' => hb'a' ha'b'.symm
        · rwa [hrevLast] at ha'last
      exact Thm142NonFullCase.left_nonfull_case_false G hG B A D C F
        (CubeMinorAttachmentContainmentCore.maximalCube_swap hcube) hcfg' hCD' hnonfull'
  · have hnonfull : ∃ a' ∈ A,
        ¬ (G.Adj a' (f[0]'(by have := hcfg.len; omega)) ∧
          ∃ b' ∈ B, ¬ G.Adj a' b' ∧
            G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega))) := by
      by_contra hn
      apply hleft
      intro a' ha'A
      by_contra hp
      exact hn ⟨a', ha'A, hp⟩
    exact Thm142NonFullCase.left_nonfull_case_false G hG A B C D F hcube hcfg hCD hnonfull

end Workspace.ProofLemmas
