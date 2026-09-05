import Mathlib
import Workspace.Types.Core
import Workspace.Types.BasicClasses

/-!
# The class of double split graphs is self-complementary

PAPER (printed p. 2, inside the definition of *basic*):

> *"(Note that if `G` is a double split graph then so is `Ḡ`.)"*

Interchanging the two halves `(a,b)` and `(c,d)` of the presentation turns a presentation of
`G` into a presentation of `Ḡ`.

## Why this lives in its own module

The fact was originally proved inside `Workspace.ProofLemmas.RecalcitrantInF5`, which also
cites **9.7** and therefore imports `Workspace.Statements.S09.Thm_9_7` — and `Thm_9_7` imports
`Thm_9_6`.  The proof of **9.6** needs exactly this one complement-stability fact (it is what
licenses the printed proof's four *"by taking complements"* steps), so importing
`RecalcitrantInF5` from `Thm96Assembly` would drag `Thm_9_6`'s own statement module into
`Thm_9_6`'s proof attempt and re-declare the theorem.  Nothing in the mathematics is circular
— 9.7's proof cites 9.6, not the other way round — the cycle is purely an artefact of the
module layout.  Splitting the lemma out removes it.

`RecalcitrantInF5.isDoubleSplitGraph_compl` is retained there as a re-export of this
declaration, so every existing reference keeps working.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.DoubleSplitSelfComplementary

open Workspace.Types.Core.SPGT
open Workspace.Types.BasicClasses.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- **PAPER (printed p. 2)**: *"(Note that if `G` is a double split graph then so is `Ḡ`.)"* -/
theorem isDoubleSplitGraph_compl (h : IsDoubleSplitGraph G) : IsDoubleSplitGraph Gᶜ := by
  obtain ⟨m, n, a, b, c, d, hm, hn, hbij, hab, hcd, hAA, hCC, hAC⟩ := h
  -- All `2m + 2n` labelled vertices are distinct, because the labelling is a bijection.
  have hne : ∀ x y : (Fin m ⊕ Fin m) ⊕ (Fin n ⊕ Fin n), x ≠ y →
      Sum.elim (Sum.elim a b) (Sum.elim c d) x ≠ Sum.elim (Sum.elim a b) (Sum.elim c d) y :=
    fun _ _ hxy heq => hxy (hbij.1 heq)
  have hne_aa : ∀ i i' : Fin m, i ≠ i' → a i ≠ a i' := fun i i' hii' =>
    hne (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl i')) (by simpa using hii')
  have hne_bb : ∀ i i' : Fin m, i ≠ i' → b i ≠ b i' := fun i i' hii' =>
    hne (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inr i')) (by simpa using hii')
  have hne_ab : ∀ i i' : Fin m, a i ≠ b i' := fun i i' =>
    hne (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inr i')) (by simp)
  have hne_ba : ∀ i i' : Fin m, b i ≠ a i' := fun i i' =>
    hne (Sum.inl (Sum.inr i)) (Sum.inl (Sum.inl i')) (by simp)
  have hne_cd : ∀ j : Fin n, c j ≠ d j := fun j =>
    hne (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr j)) (by simp)
  have hne_ca : ∀ (j : Fin n) (i : Fin m), c j ≠ a i := fun j i =>
    hne (Sum.inr (Sum.inl j)) (Sum.inl (Sum.inl i)) (by simp)
  have hne_cb : ∀ (j : Fin n) (i : Fin m), c j ≠ b i := fun j i =>
    hne (Sum.inr (Sum.inl j)) (Sum.inl (Sum.inr i)) (by simp)
  have hne_da : ∀ (j : Fin n) (i : Fin m), d j ≠ a i := fun j i =>
    hne (Sum.inr (Sum.inr j)) (Sum.inl (Sum.inl i)) (by simp)
  have hne_db : ∀ (j : Fin n) (i : Fin m), d j ≠ b i := fun j i =>
    hne (Sum.inr (Sum.inr j)) (Sum.inl (Sum.inr i)) (by simp)
  refine ⟨n, m, c, d, a, b, hn, hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the relabelling is the old one precomposed with the swap of the two halves
    have hcomp : Sum.elim (Sum.elim c d) (Sum.elim a b)
        = (Sum.elim (Sum.elim a b) (Sum.elim c d)) ∘
            (Equiv.sumComm (Fin n ⊕ Fin n) (Fin m ⊕ Fin m)) := by
      funext x
      rcases x with (x | x) | (x | x) <;> rfl
    rw [hcomp]
    exact hbij.comp (Equiv.sumComm _ _).bijective
  · exact fun j => (SimpleGraph.compl_adj G _ _).mpr ⟨hne_cd j, hcd j⟩
  · exact fun i hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 (hab i)
  · intro j j' hjj'
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hCC j j' hjj'
    exact ⟨fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 e₁,
           fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 e₂,
           fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 e₃,
           fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 e₄⟩
  · intro i i' hii'
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hAA i i' hii'
    exact ⟨(SimpleGraph.compl_adj G _ _).mpr ⟨hne_aa i i' hii', e₁⟩,
           (SimpleGraph.compl_adj G _ _).mpr ⟨hne_ab i i', e₂⟩,
           (SimpleGraph.compl_adj G _ _).mpr ⟨hne_ba i i', e₃⟩,
           (SimpleGraph.compl_adj G _ _).mpr ⟨hne_bb i i' hii', e₄⟩⟩
  · intro j i
    rcases hAC i j with ⟨e₁, e₂, e₃, e₄⟩ | ⟨e₁, e₂, e₃, e₄⟩
    · -- `aᵢcⱼ`, `bᵢdⱼ` are edges of `G`, so `cⱼbᵢ`, `dⱼaᵢ` are the edges of `Ḡ`
      refine Or.inr ⟨fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 (e₁.symm), ?_, ?_, ?_⟩
      · exact fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 (e₂.symm)
      · exact (SimpleGraph.compl_adj G _ _).mpr ⟨hne_cb j i, fun hg => e₄ hg.symm⟩
      · exact (SimpleGraph.compl_adj G _ _).mpr ⟨hne_da j i, fun hg => e₃ hg.symm⟩
    · refine Or.inl ⟨?_, ?_, ?_, ?_⟩
      · exact (SimpleGraph.compl_adj G _ _).mpr ⟨hne_ca j i, fun hg => e₁ hg.symm⟩
      · exact (SimpleGraph.compl_adj G _ _).mpr ⟨hne_db j i, fun hg => e₂ hg.symm⟩
      · exact fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 (e₄.symm)
      · exact fun hadj => ((SimpleGraph.compl_adj G _ _).mp hadj).2 (e₃.symm)

end Workspace.ProofLemmas.DoubleSplitSelfComplementary
