import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.CliqueNumOfInducedSet

/-!
# An anticomponent of the `B`-side of a skew partition

Items P3, P4, P8 and the remark `s ≥ 1` of §1 of the proof of 1.5 are one coherent
package about an anticomponent `B₁` of a set `B` that is **not** anticonnected —
the situation of the `B`-side of a skew partition.  They share the same two
hypotheses, so they are collected here:

* `complete_sdiff` (P3): `B₁` is complete to `B \ B₁`.  Maximality of the
  anticomponent: a vertex of `B \ B₁` with a `G`-nonneighbour in `B₁` could be
  attached to `B₁` (`ConnectedSetUnionAttach`, applied in `Gᶜ`) to give a strictly
  larger anticonnected subset of `B`.
* `sdiff_nonempty` (P4): `B \ B₁ ≠ ∅`, since otherwise `B = B₁` would be
  anticonnected.  This is one of only two places where the skew hypothesis
  *"`B` is not anticonnected"* is used.
* `nonempty` and `one_le_cliqueNum` (the remark `s ≥ 1` of §1).
* `cliqueNum_lt` (P8): `ω(B₁) < ω(B)`, obtained from a maximum clique of `B₁`
  together with one vertex of `B \ B₁`, which is complete to it.

Clause `cliqueNum_lt` is deliberately stated with `ω(B)` rather than the paper's
`ω(A ∪ B)` on the right: a caller gets `ω(B₁) < ω(B) ≤ ω(A ∪ B)` from
`CliqueNumOfInducedSet.cliqueNum_induce_mono`, which keeps `A` out of this module's
interface entirely.

`IsAnticomponent G B B₁` is `IsComponent Gᶜ B B₁`, and `AnticonnectedSet G B` is
`ConnectedSet Gᶜ B`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.AnticomponentOfSkewSideBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT

/-- **(i)** = P3.  An anticomponent `B₁` of `B` is complete to `B \ B₁`: every
vertex of `B₁` is `G`-adjacent to every vertex of `B \ B₁`. -/
theorem complete_sdiff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {B B₁ : Set V} (hB₁ : IsAnticomponent G B B₁) :
    Complete G B₁ (B \ B₁) := by
  intro x hx y hy
  by_contra hadj
  -- otherwise `y` is a `Gᶜ`-neighbour of `x ∈ B₁`, so `B₁ ∪ {y}` is anticonnected
  have hxy : y ≠ x := fun h => hy.2 (h ▸ hx)
  have hcadj : Gᶜ.Adj y x := ⟨hxy, fun h => hadj h.symm⟩
  have hcon : ConnectedSet Gᶜ (B₁ ∪ {y}) :=
    Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
      hB₁.2.1 ⟨x, hx, hcadj⟩
  -- ... and maximality of the anticomponent collapses it back onto `B₁`
  have heq : B₁ ∪ {y} = B₁ :=
    hB₁.2.2 (B₁ ∪ {y}) Set.subset_union_left
      (Set.union_subset hB₁.1 (Set.singleton_subset_iff.mpr hy.1)) hcon
  exact hy.2 (heq ▸ (Set.mem_union_right _ rfl))

/-- **(ii)** = P4.  If `B` is not anticonnected then an anticomponent of `B` is a
proper subset of `B`. -/
theorem sdiff_nonempty {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {B B₁ : Set V} (hB₁ : IsAnticomponent G B B₁) (hB : ¬ AnticonnectedSet G B) :
    (B \ B₁).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  rw [Set.diff_eq_empty] at h
  -- `B ⊆ B₁ ⊆ B` would make `B = B₁` anticonnected
  exact hB (Set.Subset.antisymm h hB₁.1 ▸ hB₁.2.1)

/-- **(iii), first half** An anticomponent of a not-anticonnected `B` is
nonempty. -/
theorem nonempty {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {B B₁ : Set V} (hB₁ : IsAnticomponent G B B₁) (hB : ¬ AnticonnectedSet G B) :
    B₁.Nonempty := by
  refine Workspace.ProofLemmas.ComponentsOfSetBasics.nonempty_of_isComponent Gᶜ ?_ hB₁
  -- `B` is nonempty, since `∅` is anticonnected
  rw [Set.nonempty_iff_ne_empty]
  rintro rfl
  exact hB (fun a _ => absurd a.2 (Set.notMem_empty _))

/-- **(iii), second half** Hence `s = ω(B₁) ≥ 1` (the remark at the end of §1 of the
proof). -/
theorem one_le_cliqueNum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {B B₁ : Set V} (hB₁ : IsAnticomponent G B B₁) (hB : ¬ AnticonnectedSet G B) :
    1 ≤ (G.induce B₁).cliqueNum := by
  classical
  obtain ⟨v, hv⟩ := nonempty G hB₁ hB
  have := Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce
    (K := ({v} : Finset V)) G (by simpa using hv) (by simp)
  simpa using this

/-- **(iv)** = P8.  `ω(B₁) < ω(B)`: adjoin to a maximum clique of `B₁` any vertex of
`B \ B₁`, which is complete to it by `complete_sdiff`. -/
theorem cliqueNum_lt {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {B B₁ : Set V} (hB₁ : IsAnticomponent G B B₁) (hB : ¬ AnticonnectedSet G B) :
    (G.induce B₁).cliqueNum < (G.induce B).cliqueNum := by
  classical
  obtain ⟨y, hy⟩ := sdiff_nonempty G hB₁ hB
  obtain ⟨K, hKB₁, hK, hcard⟩ :=
    Workspace.ProofLemmas.CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G B₁
  have hyK : y ∉ K := fun h => hy.2 (hKB₁ (by simpa using h))
  have hcompl := complete_sdiff G hB₁
  -- `y` is complete to `B₁ ⊇ K`, so `insert y K` is a clique of `B`
  have hins : G.IsClique ((↑(insert y K) : Set V)) := by
    rintro a ha b hb hab
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact (hcompl b (hKB₁ (by simpa using hb)) a hy).symm
    · rcases hb with rfl | hb
      · exact hcompl a (hKB₁ (by simpa using ha)) b hy
      · exact hK (by simpa using ha) (by simpa using hb) hab
  have hsub : (↑(insert y K) : Set V) ⊆ B := by
    intro z hz
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hz
    rcases hz with rfl | hz
    · exact hy.1
    · exact hB₁.1 (hKB₁ (by simpa using hz))
  have hle := Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce
    G hsub hins
  rw [Finset.card_insert_of_notMem hyK, hcard] at hle
  omega

end Workspace.ProofLemmas.AnticomponentOfSkewSideBasics
