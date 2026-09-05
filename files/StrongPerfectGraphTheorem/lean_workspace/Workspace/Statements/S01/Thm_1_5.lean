/-  Proof attempt for 1.5 — "If `G` is a minimum imperfect graph, then `G` admits no
    balanced skew partition."  This file reproduces §6 of `proof_tree/thm_1_5/proof_nlp.md`,
    i.e. the closing paragraph of the printed proof:

      "Now let C = B₁ ∪ C₁ ∪ ⋯ ∪ C_m and D = V(G) \ C.  Since there are no edges between
       different A_i's, it follows from (2) that ω(C) = s, and similarly ω(D) ≤ t − s.
       Since |C|, |D| < |V(G)| it follows that G|C, G|D are both perfect; so they are
       s-colourable and (t − s)-colourable, respectively.  But then G is t-colourable,
       a contradiction.  Thus there is no such (A,B).  This proves 1.5."

    Claims (1) and (2) of the printed proof, and all the bookkeeping the authors leave
    implicit, live in `Workspace.ProofLemmas.*`.                                        -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Types.Replication
import Workspace.Types.Classes
import Workspace.Types.Prisms
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.CliqueNumUnionOverComponents
import Workspace.ProofLemmas.AnticomponentOfSkewSideBasics
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect
import Workspace.ProofLemmas.MinimumImperfectNotCliqueNumColorable
import Workspace.ProofLemmas.ColorableSplitJoin
import Workspace.ProofLemmas.ComponentCliqueNumSplit
import Workspace.ProofLemmas.IsoTransport

namespace Workspace.MainTheorem

open Workspace.Types.Core Workspace.Types.Decompositions
open Workspace.Types.BasicClasses Workspace.Types.Replication
open Workspace.Types.Classes Workspace.Types.Prisms
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false


/-- **1.5** (printed p. 3), proved in Section 1 of the paper.

PAPER: *"If `G` is a minimum imperfect graph, then `G` admits no balanced skew
partition."*

*"By a minimum imperfect graph we mean a counterexample to 1.2 with as few vertices as
possible (in particular, any such graph is Berge and not perfect)."* -/
theorem thm_1_5 (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G) :
    ¬ SPGT.AdmitsBalancedSkewPartition G := by
  classical
  -- §1.  "Suppose that `(A, B)` is a balanced skew partition of `G`."
  rintro ⟨A, B, hAB⟩
  obtain ⟨hcov, hdisjAB, hAnc, hBna⟩ := hAB.1
  -- P2: `A` and `B` are nonempty (`∅` is connected and anticonnected).
  have hAne : A.Nonempty := by
    rcases Set.eq_empty_or_nonempty A with rfl | h
    · exact absurd (by intro u v; exact absurd u.2 (Set.notMem_empty _)) hAnc
    · exact h
  have hBne : B.Nonempty := by
    rcases Set.eq_empty_or_nonempty B with rfl | h
    · exact absurd (by intro u v; exact absurd u.2 (Set.notMem_empty _)) hBna
    · exact h
  -- §1.  "... and let `B₁` be an anticomponent of `B`."
  obtain ⟨b, hb⟩ := hBne
  obtain ⟨B₁, hB₁c, hbB₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hb
  have hB₁ : SPGT.IsAnticomponent G B B₁ := hB₁c
  -- §4/P8.  `s := ω(B₁)`, `t := ω(A ∪ B)`, and `s < t`.
  have hst : (G.induce B₁).cliqueNum < (G.induce (A ∪ B)).cliqueNum :=
    lt_of_lt_of_le (AnticomponentOfSkewSideBasics.cliqueNum_lt G hB₁ hBna)
      (CliqueNumOfInducedSet.cliqueNum_induce_mono G Set.subset_union_right)
  -- §5.  Claim (2), one instance per component of `A`; choose the witnesses `C_P`.
  have hsplit : ∀ P : Set V, SPGT.IsComponent G A P →
      ∃ C : Set V, C ⊆ P ∧
        (G.induce (C ∪ B₁)).cliqueNum = (G.induce B₁).cliqueNum ∧
        (G.induce ((P \ C) ∪ (B \ B₁))).cliqueNum ≤
          (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum :=
    fun P hP => ComponentCliqueNumSplit.exists_subset_cliqueNum_split hG hAB hB₁ hP
  choose! f hfsub hfC hfD using hsplit
  -- §6.  `C = B₁ ∪ C₁ ∪ ⋯ ∪ C_m` and `D = V(G) \ C`, the latter written out as
  -- `(B \ B₁) ∪ ⋃_P (P \ C_P)` (the set-algebra identity of §6).
  obtain ⟨CC, hCC⟩ :
      ∃ X : Set V, X = B₁ ∪ ⋃ P ∈ {Q : Set V | SPGT.IsComponent G A Q}, f P := ⟨_, rfl⟩
  obtain ⟨DD, hDD⟩ :
      ∃ X : Set V, X = (B \ B₁) ∪ ⋃ P ∈ {Q : Set V | SPGT.IsComponent G A Q}, (P \ f P) :=
    ⟨_, rfl⟩
  have hmemC : ∀ x : V, x ∈ CC ↔ (x ∈ B₁ ∨ ∃ P, SPGT.IsComponent G A P ∧ x ∈ f P) := by
    intro x
    rw [hCC]
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  have hmemD : ∀ x : V,
      x ∈ DD ↔ (x ∈ B \ B₁ ∨ ∃ P, SPGT.IsComponent G A P ∧ x ∈ P \ f P) := by
    intro x
    rw [hDD]
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  -- "Since there are no edges between different `A_i`'s, it follows from (2) that ω(C) = s"
  have hCle : (G.induce CC).cliqueNum ≤ (G.induce B₁).cliqueNum := by
    rw [hCC]
    refine CliqueNumUnionOverComponents.cliqueNum_union_iUnion_le
      (R := B₁) (f := f) (k := (G.induce B₁).cliqueNum) G hAne
      (fun P hP => hfsub P hP) (fun P hP => ?_)
    rw [Set.union_comm B₁ (f P)]
    exact le_of_eq (hfC P hP)
  have hB₁sub : B₁ ⊆ CC := by rw [hCC]; exact Set.subset_union_left
  have hCeq : (G.induce CC).cliqueNum = (G.induce B₁).cliqueNum :=
    le_antisymm hCle (CliqueNumOfInducedSet.cliqueNum_induce_mono G hB₁sub)
  -- "... and similarly ω(D) ≤ t − s."
  have hDle : (G.induce DD).cliqueNum ≤
      (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum := by
    rw [hDD]
    refine CliqueNumUnionOverComponents.cliqueNum_union_iUnion_le
      (R := B \ B₁) (f := fun P => P \ f P)
      (k := (G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum) G hAne
      (fun P _ => Set.diff_subset) (fun P hP => ?_)
    rw [Set.union_comm (B \ B₁) (P \ f P)]
    exact hfD P hP
  -- `(C, D)` really is a partition of `V(G)`.
  have hcovCD : CC ∪ DD = Set.univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    have hx : x ∈ A ∪ B := by rw [hcov]; exact Set.mem_univ x
    rcases (Set.mem_union x A B).mp hx with hxA | hxB
    · obtain ⟨P, hP, hxP⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A hxA
      by_cases hxf : x ∈ f P
      · exact Or.inl ((hmemC x).mpr (Or.inr ⟨P, hP, hxf⟩))
      · exact Or.inr ((hmemD x).mpr (Or.inr ⟨P, hP, hxP, hxf⟩))
    · by_cases hxB₁ : x ∈ B₁
      · exact Or.inl ((hmemC x).mpr (Or.inl hxB₁))
      · exact Or.inr ((hmemD x).mpr (Or.inl ⟨hxB, hxB₁⟩))
  have hdisjCD : Disjoint CC DD := by
    rw [Set.disjoint_left]
    intro x hxC hxD
    rcases (hmemC x).mp hxC with hxB₁ | ⟨P, hP, hxfP⟩
    · rcases (hmemD x).mp hxD with hxBB₁ | ⟨Q, hQ, hxQ⟩
      · exact hxBB₁.2 hxB₁
      · exact Set.disjoint_left.mp hdisjAB (hQ.1 hxQ.1) (hB₁c.1 hxB₁)
    · rcases (hmemD x).mp hxD with hxBB₁ | ⟨Q, hQ, hxQ⟩
      · exact Set.disjoint_left.mp hdisjAB (hP.1 (hfsub P hP hxfP)) hxBB₁.1
      · -- P5(iii): distinct components are disjoint, so `x ∈ f P ⊆ P` and `x ∈ Q` force `P = Q`.
        by_cases hPQ : P = Q
        · subst hPQ
          exact hxQ.2 hxfP
        · exact Set.disjoint_left.mp
            (ComponentsOfSetBasics.disjoint_of_isComponent G hP hQ hPQ)
            (hfsub P hP hxfP) hxQ.1
  -- "Since |C|, |D| < |V(G)| ..." — via `B₁ ≠ ∅` and `B \ B₁ ≠ ∅`.
  have hB₁ne : B₁.Nonempty := AnticomponentOfSkewSideBasics.nonempty G hB₁ hBna
  have hBB₁ne : (B \ B₁).Nonempty := AnticomponentOfSkewSideBasics.sdiff_nonempty G hB₁ hBna
  have hCuniv : CC ≠ Set.univ := by
    obtain ⟨v, hv⟩ := hBB₁ne
    intro h
    have hvC : v ∈ CC := by rw [h]; exact Set.mem_univ v
    exact Set.disjoint_left.mp hdisjCD hvC ((hmemD v).mpr (Or.inl hv))
  have hDuniv : DD ≠ Set.univ := by
    obtain ⟨v, hv⟩ := hB₁ne
    intro h
    have hvD : v ∈ DD := by rw [h]; exact Set.mem_univ v
    exact Set.disjoint_left.mp hdisjCD ((hmemC v).mpr (Or.inl hv)) hvD
  -- "... it follows that G|C, G|D are both perfect"
  have hpC := SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hCuniv
  have hpD := SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hDuniv
  -- "so they are s-colourable and (t − s)-colourable, respectively."
  have hcolC : (G.induce CC).Colorable ((G.induce B₁).cliqueNum) :=
    SimpleGraph.Colorable.mono (le_of_eq hCeq)
      (CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect (G.induce CC) hpC)
  have hcolD : (G.induce DD).Colorable
      ((G.induce (A ∪ B)).cliqueNum - (G.induce B₁).cliqueNum) :=
    SimpleGraph.Colorable.mono hDle
      (CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect (G.induce DD) hpD)
  -- "But then G is t-colourable"
  have hcolG : G.Colorable ((G.induce (A ∪ B)).cliqueNum) := by
    have h := ColorableSplitJoin.colorable_add_of_partition G hcovCD hdisjCD hcolC hcolD
    rwa [Nat.add_sub_cancel' (le_of_lt hst)] at h
  -- `A ∪ B = V(G)`, so `t = ω(G)` and this contradicts P7.
  have htG : (G.induce (A ∪ B)).cliqueNum = G.cliqueNum := by
    rw [hcov]
    exact IsoTransport.cliqueNum_iso (SimpleGraph.induceUnivIso G)
  rw [htG] at hcolG
  exact MinimumImperfectNotCliqueNumColorable.not_colorable_cliqueNum hG hcolG


end SPGT

end Workspace.MainTheorem
