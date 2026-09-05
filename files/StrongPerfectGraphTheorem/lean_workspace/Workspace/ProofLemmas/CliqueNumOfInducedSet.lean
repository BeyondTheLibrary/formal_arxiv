import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.IsoTransport

/-!
# The `ω`-dictionary for a set of vertices

The paper writes *"For a subset `X` of `V(G)`, we denote the size of the largest
clique in `X` by `ω(X)`"*; mechanically, `ω(X) := (G.induce X).cliqueNum`.  Three
facts about this notation are used constantly and silently in the proof of 1.5:

* `card_le_cliqueNum_induce` and `exists_clique_card_eq_cliqueNum` are the two
  directions of the translation between *"a clique of `G` contained in `X`"* and
  *"a clique of `G.induce X`"*;
* `cliqueNum_induce_mono` is `X ⊆ Y → ω(X) ≤ ω(Y)`.  Mathlib has **no** counterpart:
  `SimpleGraph.cliqueSet_mono` and friends compare two graphs on a *fixed* vertex
  type, not two induced subgraphs on different subtypes.

To these we add the `χ`/`ω` dictionary for a perfect graph — instantiating
`IsPerfect` at `Set.univ` and transporting along `SimpleGraph.induceUnivIso` — which
is needed at three separate call sites (P7, §5.3, §6) and belongs with the rest of
the dictionary.

None of these lemmas has a counterpart in the paper; they are bookkeeping.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.CliqueNumOfInducedSet

open Workspace.Types.Core Workspace.Types.Core.SPGT

/-- **(i)** A clique of `G` all of whose vertices lie in `X` is no bigger than
`ω(X) = (G.induce X).cliqueNum`. -/
theorem card_le_cliqueNum_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {X : Set V} {K : Finset V}
    (hKX : (↑K : Set V) ⊆ X) (hK : G.IsClique (↑K : Set V)) :
    K.card ≤ (G.induce X).cliqueNum := by
  classical
  -- carry `K` up into the subtype `↥X`
  set K' : Finset ↥X :=
    K.attach.map ⟨fun a => ⟨a.1, hKX (by simp)⟩,
      by intro a b hab; exact Subtype.ext (by simpa using hab)⟩ with hK'
  have hcard : K'.card = K.card := by
    rw [hK', Finset.card_map, Finset.card_attach]
  have hclique : (G.induce X).IsClique (↑K' : Set ↥X) := by
    rintro a ha b hb hab
    simp only [hK', Finset.coe_map, Set.mem_image, Finset.mem_coe, Finset.mem_attach] at ha hb
    obtain ⟨x, -, rfl⟩ := ha
    obtain ⟨y, -, rfl⟩ := hb
    have hxy : (x : V) ≠ (y : V) := fun h => hab (Subtype.ext h)
    exact hK (by simp) (by simp) hxy
  calc K.card = K'.card := hcard.symm
    _ ≤ (G.induce X).cliqueNum := SimpleGraph.IsClique.card_le_cliqueNum (tc := hclique)

/-- **(ii)** The bound of `card_le_cliqueNum_induce` is attained: there is a clique
of `G` inside `X` with exactly `ω(X)` vertices. -/
theorem exists_clique_card_eq_cliqueNum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X : Set V) :
    ∃ K : Finset V, (↑K : Set V) ⊆ X ∧ G.IsClique (↑K : Set V) ∧
      K.card = (G.induce X).cliqueNum := by
  classical
  obtain ⟨s, hs⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := G.induce X)
  refine ⟨s.map ⟨Subtype.val, Subtype.val_injective⟩, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact a.2
  · rintro x hx y hy hxy
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact hs.1 (by simpa using ha) (by simpa using hb) (fun h => hxy (congrArg Subtype.val h))
  · rw [Finset.card_map]; exact hs.2

/-- **(iii)** `ω` is monotone under inclusion of vertex sets.  This is the single
most-used fact of the whole proof of 1.5, and Mathlib does not have it. -/
theorem cliqueNum_induce_mono {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {X Y : Set V} (hXY : X ⊆ Y) :
    (G.induce X).cliqueNum ≤ (G.induce Y).cliqueNum := by
  obtain ⟨K, hKX, hK, hcard⟩ := exists_clique_card_eq_cliqueNum G X
  exact hcard ▸ card_le_cliqueNum_induce G (hKX.trans hXY) hK

/-- **(iv), first half** A perfect graph has `χ = ω` *as a graph*, not merely on
each induced subgraph.  (`IsPerfect` is stated for all induced subgraphs; this is
the instance `X = Set.univ`, transported along `SimpleGraph.induceUnivIso`.) -/
theorem chromaticNumber_eq_cliqueNum_of_isPerfect {W : Type*} [Fintype W]
    (K : SimpleGraph W) (hK : IsPerfect K) :
    K.chromaticNumber = ((K.cliqueNum : ℕ) : ℕ∞) := by
  have h := hK Set.univ
  rw [Workspace.ProofLemmas.IsoTransport.chromaticNumber_iso (SimpleGraph.induceUnivIso K),
    Workspace.ProofLemmas.IsoTransport.cliqueNum_iso (SimpleGraph.induceUnivIso K)] at h
  exact h

/-- **(iv), second half** A perfect graph is `ω`-colourable. -/
theorem colorable_cliqueNum_of_isPerfect {W : Type*} [Fintype W]
    (K : SimpleGraph W) (hK : IsPerfect K) :
    K.Colorable K.cliqueNum := by
  rw [← SimpleGraph.chromaticNumber_le_iff_colorable,
    chromaticNumber_eq_cliqueNum_of_isPerfect K hK]

end Workspace.ProofLemmas.CliqueNumOfInducedSet
