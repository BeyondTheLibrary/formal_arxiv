import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.Statements.S05.Thm_5_1
import Workspace.Statements.S05.Thm_5_2
import Workspace.Statements.S09.Thm_9_6

/-!
# 9.7 — proof attempt 1

PAPER (printed p. 58): *"Proof.  This is immediate from 9.6, 5.1 and 5.2."*

The three cited results are combined in the only way that fits together:

* if some appearance of `K₄` in `G` is nondegenerate, **5.1** applied to `G` gives three of
  the four alternatives directly;
* otherwise, if some appearance of `K₄` in `Ḡ` is nondegenerate, **5.1** applied to `Ḡ`
  gives them for `Ḡ` (a balanced skew partition of `Ḡ` is one of `G`);
* otherwise every appearance of `K₄` in `G` and in `Ḡ` is degenerate.  If `G` contains
  `L(K₃,₃)` as an induced subgraph, **5.2** applies: its first outcome makes `G` itself a
  line graph of a bipartite graph (`K₃,₃` is bipartite), its second outcome produces a
  nondegenerate appearance of `K₄` in `G` or in `Ḡ`, which the two previous cases have
  already excluded, and its third outcome is a balanced skew partition of `G`.
* otherwise **9.6** applies, and its fourth alternative — *"there is no appearance of `K₄`
  in either `G` or `Ḡ`"* — contradicts the hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S09

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `K₃,₃` is bipartite: colour the left half `0` and the right half `1`. -/
private theorem completeBipartite_isBipartite (m n : ℕ) :
    (completeBipartiteGraph (Fin m) (Fin n)).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))) ?_⟩
  intro u v hadj
  cases u <;> cases v <;> simp_all [_root_.completeBipartiteGraph_adj]

/-- A graph isomorphic to `L(K₃,₃)` is the line graph of a bipartite graph.  The only work is
moving `K₃,₃` off `Fin 3 ⊕ Fin 3` onto `Fin 6`, since `IsLineGraphOfBipartite` quantifies over
graphs on `Fin n`. -/
private theorem isLineGraphOfBipartite_of_iso_L33 {W : Type*} (X : SimpleGraph W)
    (h : Nonempty (X ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)) :
    IsLineGraphOfBipartite X := by
  obtain ⟨e⟩ := h
  have hc6 : Fintype.card (Fin 3 ⊕ Fin 3) = 6 := by simp
  have eo : completeBipartiteGraph (Fin 3) (Fin 3) ≃g
      (completeBipartiteGraph (Fin 3) (Fin 3)).overFin hc6 :=
    (completeBipartiteGraph (Fin 3) (Fin 3)).overFinIso hc6
  refine ⟨6, (completeBipartiteGraph (Fin 3) (Fin 3)).overFin hc6, ?_, ?_⟩
  · exact SimpleGraph.Colorable.of_hom eo.symm.toHom (completeBipartite_isBipartite 3 3)
  · exact ⟨e.trans (SimpleGraph.Iso.lineGraph eo)⟩


/-- **9.7** (printed p. 56)

Preceded by: *"It is convenient to combine three earlier results as follows."*

PAPER: *"Let `G` be a Berge graph, such that there is an appearance of `K₄` in `G`.  Then
either one of `G,Ḡ` is a line graph, or `G` is a double split graph, or one of `G,Ḡ` admits a
proper 2-join, or `G` admits a balanced skew partition."*

(Proof of 9.7 in full: *"This is immediate from 9.6, 5.1 and 5.2."*)

Notes on the transcription.

* *"Is a line graph"* is the paper's standing abbreviation for *"is the line graph of a
  bipartite graph"* (`BasicClasses.IsLineGraphOfBipartite`): 9.7 is deduced from 5.1 and 5.2,
  whose corresponding outcomes are *"`G` is a line graph"* and *"`G = L(K₃,₃)`"*, and 5.1 is
  in turn said to give 1.8.1, whose wording is *"`G` is a line graph of a bipartite graph"*.
* *"There is an appearance of `K₄` in `G`"* is `Appearances.Appears G K₄`.
* The four alternatives are transcribed in the printed order; *"proper"* 2-join is the
  published form. -/
theorem thm_9_7 (G : SimpleGraph V) (hG : Berge G)
    (happ : Appears G (⊤ : SimpleGraph (Fin 4))) :
    (IsLineGraphOfBipartite G ∨ IsLineGraphOfBipartite Gᶜ) ∨
    IsDoubleSplitGraph G ∨
    (AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ) ∨
    AdmitsBalancedSkewPartition G := by
  have hGc : Berge Gᶜ := _root_.Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG
  -- Case (i): some appearance of `K₄` in `G` is nondegenerate — this is 5.1 for `G`.
  by_cases hndG : ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H
  · obtain ⟨n, H, K, hap, hnd⟩ := hndG
    rcases _root_.Workspace.Statements.S05.SPGT.thm_5_1 G hG n H K hap hnd with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr h))
  -- Case (ii): some appearance of `K₄` in `Ḡ` is nondegenerate — this is 5.1 for `Ḡ`.
  by_cases hndGc : ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H
  · obtain ⟨n, H, K, hap, hnd⟩ := hndGc
    rcases _root_.Workspace.Statements.S05.SPGT.thm_5_1 Gᶜ hGc n H K hap hnd with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
    · exact Or.inr (Or.inr (Or.inr
        (_root_.Workspace.ProofLemmas.ClassLemmas.admitsBalancedSkewPartition_compl.mp h)))
  -- From here on every appearance of `K₄` in `G` and in `Ḡ` is degenerate.
  -- Case (iii): `G` contains `L(K₃,₃)` as an induced subgraph — this is 5.2.
  by_cases hL33 : ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K)
  · obtain ⟨K, hK⟩ := hL33
    rcases _root_.Workspace.Statements.S05.SPGT.thm_5_2 G hG K hK with
      h | ⟨n, H, hsub, hnd, hh⟩ | h
    · -- `G = L(K₃,₃)`, and `K₃,₃` is bipartite.
      exact Or.inl (Or.inl (isLineGraphOfBipartite_of_iso_L33 G h))
    · -- A nondegenerate appearance of `K₄` in `G` or in `Ḡ`: excluded by (i) and (ii).
      rcases hh with ⟨K', hK'⟩ | ⟨K', hK'⟩
      · exact absurd ⟨n, H, K', ⟨hsub, hK'⟩, hnd⟩ hndG
      · exact absurd ⟨n, H, K', ⟨hsub, hK'⟩, hnd⟩ hndGc
    · exact Or.inr (Or.inr (Or.inr h))
  -- Case (iv): no `L(K₃,₃)` and no nondegenerate appearance — this is 9.6.
  · have hdegG : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
        IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K →
          DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
      intro n H K hap
      by_contra hc
      exact hndG ⟨n, H, K, hap, hc⟩
    have hdegGc : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
        IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K →
          DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
      intro n H K hap
      by_contra hc
      exact hndGc ⟨n, H, K, hap, hc⟩
    rcases thm_9_6 G hG hdegG hdegGc hL33 with h | h | h | ⟨hno, -⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact absurd happ hno


end SPGT

end Workspace.Statements.S09
