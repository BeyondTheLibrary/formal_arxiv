import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Statements.S04.Thm_4_2

/-!
# 12.4, the closing paragraph

PAPER (printed p. 76, the last paragraph of the proof of 12.4):

*"Let `X` be the set of all `Q`-complete vertices in `G`; let `M` be the component of
`G \ (Q ∪ X)` that contains `a₀`, and `N` the union of all the other components.  By (5),
`b₀ ∈ N`, so `N` is nonempty, and hence `(M ∪ N, Q ∪ X)` is a skew partition of `G`.  Choose
`b ∈ B`; then `b ∈ X`, and it has no neighbour in `M` by (5).  Hence the skew partition is
loose, and so `G` admits a balanced skew partition, by 4.2.  This proves 12.4."*

Everything the paragraph uses about the staircase is packaged as an explicit hypothesis:

* `a₀` is a left-star, so it is `A`-complete (`ha₀A`) and, being an end of the banister, it is
  not `Q`-complete and does not lie in `Q`;
* `b₀` is a right-star, so it has a neighbour in `B ∪ C` (`hb₀att`), and again it is neither in
  `Q` nor `Q`-complete;
* claim (2) of the printed proof supplies a `Q`-complete vertex `b ∈ B`;
* claim (5) is the hypothesis `h5`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm124Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closing paragraph of the printed proof of 12.4. -/
theorem thm124Endgame (G : SimpleGraph V) (hG : Berge G)
    (A B C Q : Set V) (a₀ b₀ : V)
    (hQne : Q.Nonempty)
    (ha₀Q : a₀ ∉ Q) (ha₀X : ¬ VertexComplete G a₀ Q)
    (hb₀Q : b₀ ∉ Q) (hb₀X : ¬ VertexComplete G b₀ Q)
    (ha₀A : VertexComplete G a₀ A)
    (hb₀att : ∃ z ∈ B ∪ C, G.Adj b₀ z)
    (b : V) (hbB : b ∈ B) (hbQ : VertexComplete G b Q)
    (h5 : ∀ (p : List V) (u v : V), IsPathFrom G p u v → VertexComplete G u A →
      (∃ z ∈ B ∪ C, G.Adj v z) → ∃ w ∈ p, w ∈ Q ∨ VertexComplete G w Q) :
    AdmitsBalancedSkewPartition G := by
  classical
  -- PAPER: *"Let `X` be the set of all `Q`-complete vertices in `G`"*
  set X : Set V := {v : V | VertexComplete G v Q} with hXdef
  set Y : Set V := (Q ∪ X)ᶜ with hYdef
  have hbX : b ∈ X := hbQ
  -- `X` and `Q` are disjoint, and complete to one another in `G`.
  have hQXdisj : Disjoint Q X := by
    rw [Set.disjoint_left]
    intro v hvQ hvX
    exact G.irrefl (hvX v hvQ)
  have hQXanti : Anticomplete Gᶜ Q X := by
    intro q hq x hx hadj
    exact ((SimpleGraph.compl_adj G q x).mp hadj).2 ((hx : VertexComplete G x Q) q hq).symm
  -- `a₀` and `b₀` lie outside `Q ∪ X`.
  have ha₀Y : a₀ ∈ Y := by
    simp only [hYdef, Set.mem_compl_iff, Set.mem_union, hXdef, Set.mem_setOf_eq]
    exact fun h => h.elim ha₀Q ha₀X
  have hb₀Y : b₀ ∈ Y := by
    simp only [hYdef, Set.mem_compl_iff, Set.mem_union, hXdef, Set.mem_setOf_eq]
    exact fun h => h.elim hb₀Q hb₀X
  -- PAPER: *"let `M` be the component of `G \ (Q ∪ X)` that contains `a₀`"*
  obtain ⟨M, hM, ha₀M⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G Y ha₀Y
  -- PAPER: *"and `N` the union of all the other components"*
  set N : Set V := Y \ M with hNdef
  have hMN : M ∪ N = Y := Set.union_diff_cancel hM.1
  -- The key consequence of (5): no vertex of `M` has a neighbour in `B ∪ C`.
  have hMatt : ∀ m ∈ M, ¬ ∃ z ∈ B ∪ C, G.Adj m z := by
    intro m hmM hm
    obtain ⟨p, hp, hpM⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        (G := G) hM.2.1 ha₀M hmM
    obtain ⟨w, hwp, hw⟩ := h5 p a₀ m hp ha₀A hm
    have hwY : w ∈ Y := hM.1 (hpM w hwp)
    simp only [hYdef, Set.mem_compl_iff, Set.mem_union, hXdef, Set.mem_setOf_eq] at hwY
    exact hwY (hw.elim Or.inl Or.inr)
  -- PAPER: *"By (5), `b₀ ∈ N`, so `N` is nonempty"*
  have hb₀M : b₀ ∉ M := fun h => hMatt b₀ h hb₀att
  have hNne : N.Nonempty := ⟨b₀, hb₀Y, hb₀M⟩
  have hMne : M.Nonempty := ⟨a₀, ha₀M⟩
  -- PAPER: *"hence `(M ∪ N, Q ∪ X)` is a skew partition of `G`"*
  have hskew : IsSkewPartition G Y (Q ∪ X) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hYdef] using (Set.compl_union_self (Q ∪ X))
    · simpa [hYdef] using (disjoint_compl_left : Disjoint ((Q ∪ X)ᶜ) (Q ∪ X))
    · refine Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
        (G := G) (A := Y) (S := M) (T := N) hMN.symm hMne hNne ?_ ?_
      · exact Set.disjoint_sdiff_right
      · exact Workspace.Statements.S04.SPGT.Helpers42.anticomplete_diff hM
    · exact Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
        (G := Gᶜ) (A := Q ∪ X) (S := Q) (T := X) rfl hQne ⟨b, hbX⟩ hQXdisj hQXanti
  -- PAPER: *"Choose `b ∈ B`; then `b ∈ X`, and it has no neighbour in `M` by (5).  Hence the
  -- skew partition is loose"*
  have hbantiM : VertexAnticomplete G b M := by
    intro m hmM hadj
    exact hMatt m hmM ⟨b, Or.inl hbB, hadj.symm⟩
  have hMcomp : IsComponent G Y M := hM
  have hloose : IsLooseSkewPartition G Y (Q ∪ X) :=
    ⟨hskew, Or.inl ⟨b, Or.inr hbX, M, hMcomp, hbantiM⟩⟩
  -- PAPER: *"and so `G` admits a balanced skew partition, by 4.2"*
  exact Workspace.Statements.S04.SPGT.thm_4_2 G hG ⟨Y, Q ∪ X, hloose⟩

end Workspace.ProofLemmas.Thm124Endgame
