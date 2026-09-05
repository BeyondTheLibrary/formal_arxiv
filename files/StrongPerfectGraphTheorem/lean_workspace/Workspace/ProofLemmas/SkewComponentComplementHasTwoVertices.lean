import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.IsoTransport
import Workspace.Statements.S01.Thm_1_1
import Workspace.Statements.S01.Thm_E5_perfect_implies_berge
import Workspace.Statements.S01.Thm_E6_no_star_cutset_in_minimum_imperfect

/-!
# At least two vertices of `A` lie outside a component of `A`

§5.1 of the proof of 1.5 is the one place where the printed text gives only a
citation:

> *"Now by [6], there are at least two vertices of `G` not in `H` (all the vertices
> in `A \ Aᵢ`), and since `H` has only one new vertex it follows that
> `|V(H)| < |V(G)|`."*

Isolating the claim keeps the reconstruction auditable and keeps claim (2) readable.
The reconstruction has two halves:

* `A \ P ≠ ∅`, because otherwise `A = P` would be connected, contradicting the skew
  hypothesis that `A` is not connected.  Reference [6] cannot be what settles this
  case: with `A \ P = ∅` there is no vertex left over to play the role of a
  star-cutset centre.
* `A \ P ≠ {a}`.  Such an `a` would have no neighbour in `P` — else `P ∪ {a}` is
  connected by `ConnectedSetUnionAttach.connectedSet_union_singleton`, contradicting
  maximality of the component `P` — hence would be `Gᶜ`-adjacent to every other
  vertex of `A`.  Now `Gᶜ` is minimum imperfect
  (`IsoTransport.minimumImperfect_compl`, its hypotheses discharged by the `thm_1_1`
  axiom at `Gᶜ` and by `thm_E5_perfect_implies_berge`), `(B, A)` is a skew partition
  of `Gᶜ` (`ClassLemmas.isSkewPartition_compl`), and so `IsStarCutset Gᶜ B A` holds
  with centre `a` — contradicting `thm_E6_no_star_cutset_in_minimum_imperfect`
  applied to `Gᶜ`.

No circularity: `minimumImperfect_compl` uses only `thm_1_1`, `thm_E5` and
`compl_compl`, never 1.2 or 1.5, and 1.1 is printed two pages before 1.5.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.SkewComponentComplementHasTwoVertices

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

/-- If `(A, B)` is a skew partition of a minimum imperfect graph `G` and `P` is a
component of `A`, then `A \ P` contains at least two distinct vertices. -/
theorem exists_two_mem_sdiff {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : MinimumImperfect G) {A B : Set V}
    (hskew : IsSkewPartition G A B) {P : Set V} (hP : IsComponent G A P) :
    ∃ a ∈ A \ P, ∃ b ∈ A \ P, a ≠ b := by
  classical
  -- `A \ P ≠ ∅`: otherwise `A = P` would be connected, contradicting (S2).
  obtain ⟨a, ha⟩ : (A \ P).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [Set.diff_eq_empty] at h
    exact hskew.2.2.1 (Set.Subset.antisymm h hP.1 ▸ hP.2.1)
  refine ⟨a, ha, ?_⟩
  by_contra hno
  push Not at hno
  -- so `A \ P = {a}`
  have hsingle : ∀ b, b ∈ A \ P → b = a := fun b hb => (hno b hb).symm
  -- `a` has no neighbour in `P`, else `P ∪ {a}` would be a connected subset of `A`
  -- properly containing the component `P`
  have hnoadj : ∀ p ∈ P, ¬ G.Adj a p := by
    intro p hp hadj
    have hcon : ConnectedSet G (P ∪ {a}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hP.2.1 ⟨p, hp, hadj⟩
    have heq : P ∪ {a} = P :=
      hP.2.2 (P ∪ {a}) Set.subset_union_left
        (Set.union_subset hP.1 (Set.singleton_subset_iff.mpr ha.1)) hcon
    exact ha.2 (heq ▸ Set.mem_union_right _ rfl)
  -- hence `a` is `Gᶜ`-adjacent to every other vertex of `A`
  have hstar : ∀ u ∈ A, u ≠ a → Gᶜ.Adj a u := by
    intro u huA hune
    have huP : u ∈ P := by
      by_contra hc
      exact hune (hsingle u ⟨huA, hc⟩)
    exact ⟨fun h => hune h.symm, hnoadj u huP⟩
  -- `Gᶜ` is minimum imperfect, and `(B, A)` is a skew partition of `Gᶜ`;
  -- with centre `a` this is a star cutset of `Gᶜ`, contradicting [6].
  have hGc : MinimumImperfect Gᶜ :=
    IsoTransport.minimumImperfect_compl hG
      (fun hp => Workspace.MainTheorem.SPGT.thm_1_1 Gᶜ hp)
      (fun hp => Workspace.MainTheorem.SPGT.thm_E5_perfect_implies_berge G hp)
  have hskewc : IsSkewPartition Gᶜ B A := ClassLemmas.isSkewPartition_compl.mpr hskew
  exact Workspace.MainTheorem.SPGT.thm_E6_no_star_cutset_in_minimum_imperfect Gᶜ hGc
    ⟨B, A, hskewc, a, ha.1, hstar⟩

end Workspace.ProofLemmas.SkewComponentComplementHasTwoVertices
