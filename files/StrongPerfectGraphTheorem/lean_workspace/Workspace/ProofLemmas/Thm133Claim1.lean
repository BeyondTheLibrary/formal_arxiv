/-  **13.3, claim (1)** (printed p. 83).

    PAPER: *"(1) `X ∪ Y ∪ B` meets the interior of every path in `G` from `A ∪ C` to `b₀`."*

    This is the first and longest step of the printed proof of 13.3; the printed argument
    occupies the whole of the paragraph beginning *"For suppose `P` is a path from `A ∪ C` to
    `b₀` with no internal vertex in `X ∪ Y ∪ B`"* and uses 12.3 (a banister or a major vertex
    on `P \ p`), the maximality of the right-sequence, 12.1 and 12.5.  -/
import Mathlib
import Workspace.ProofLemmas.Thm133Setup
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Statements.S12.Thm_12_3
import Workspace.Statements.S12.Thm_12_5

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm133Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm133Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem getElem_eq_of_eq {l : List V} {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h
  rfl

/-- **13.3 (1)** PAPER: *"`X ∪ Y ∪ B` meets the interior of every path in `G` from `A ∪ C` to
`b₀`."* -/
theorem thm133_claim1 {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {x : List V} (c : Ctx G A C B a₀ b₀ R₀ x)
    {u : V} {P : List V} (hu : u ∈ A ∪ C) (hP : IsPathFrom G P u b₀) :
    ∃ w ∈ SPGT.interior P, w ∈ Ws G A C B x := by
  classical
  by_contra hcon
  push_neg at hcon

  have hpos : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
  have hlast : P.length - 1 < P.length := by omega
  have hPzero : P[0]'hpos = u :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 hpos
  have hPlast : P[P.length - 1]'hlast = b₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 hpos

  -- Choose the last vertex of `P` in the strip.  The remaining suffix is the
  -- paper's minimal path `P \ p`.
  let InStrip : ℕ → Prop := fun i =>
    ∃ hi : i < P.length, P[i]'hi ∈ A ∪ B ∪ C
  have hzero : InStrip 0 := by
    refine ⟨hpos, ?_⟩
    rw [hPzero]
    exact hu.elim (fun h => Or.inl (Or.inl h)) Or.inr
  let i := Nat.findGreatest InStrip (P.length - 1)
  have hiStrip : InStrip i := by
    dsimp [i]
    exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _) hzero
  obtain ⟨hiP, hiS⟩ := hiStrip
  have hiLe : i ≤ P.length - 1 := by
    dsimp [i]
    exact Nat.findGreatest_le _
  have hiLt : i < P.length - 1 := by
    rcases lt_or_eq_of_le hiLe with h | h
    · exact h
    · exfalso
      apply c.rightStar_b₀.1
      rw [← hPlast, ← getElem_eq_of_eq hiP hlast h]
      exact hiS
  have hiNext : i + 1 < P.length := by omega

  let R : List V := P.drop (i + 1)
  have hR : IsPathFrom G R (P[i + 1]'hiNext) b₀ := by
    refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_drop hP.1 hiNext, ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem hiNext]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hP.2.2
  have hRpos : ∀ w ∈ R, ∃ (k : ℕ) (hk : k < P.length),
      i + 1 ≤ k ∧ k ≤ P.length - 1 ∧ P[k]'hk = w := by
    intro w hw
    obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp hw
    have hj' : j < P.length - (i + 1) := by simpa [R] using hj
    refine ⟨i + 1 + j, by omega, by omega, by omega, ?_⟩
    calc
      P[i + 1 + j]'(by omega) = R[j]'hj := by simp [R]
      _ = w := hjw
  have hRoutside : ∀ w ∈ R, w ∉ A ∪ B ∪ C := by
    intro w hwR hwS
    obtain ⟨k, hk, hik, hklast, hkw⟩ := hRpos w hwR
    exact Nat.findGreatest_is_greatest (P := InStrip) (n := P.length - 1)
      (by omega) hklast ⟨hk, by rw [hkw]; exact hwS⟩
  have hRoutsideW : ∀ w ∈ R, w ∉ Ws G A C B x := by
    intro w hwR
    obtain ⟨k, hk, hik, hklast, hkw⟩ := hRpos w hwR
    by_cases hkend : k = P.length - 1
    · have hwb : w = b₀ := by
        calc
          w = P[k]'hk := hkw.symm
          _ = P[P.length - 1]'hlast := by subst k; rfl
          _ = b₀ := hPlast
      rw [hwb]
      exact c.b₀_not_mem_W
    · apply hcon w
      rw [Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP]
      refine ⟨hkw ▸ List.getElem_mem hk, ?_, ?_⟩
      · intro hwu
        have heq : P[k]'hk = P[0]'hpos := hkw.trans (hwu.trans hPzero.symm)
        have := (List.Nodup.getElem_inj_iff hP.1.2.1).mp heq
        omega
      · intro hwb
        have heq : P[k]'hk = P[P.length - 1]'hlast :=
          hkw.trans (hwb.trans hPlast.symm)
        have := (List.Nodup.getElem_inj_iff hP.1.2.1).mp heq
        omega

  -- The last strip vertex lies on the near side: it cannot be in `B`, since
  -- then it would itself be a forbidden internal vertex of `P`.
  have hiAC : P[i]'hiP ∈ A ∪ C := by
    rcases hiS with (hiA | hiB) | hiC
    · exact Or.inl hiA
    · exfalso
      have hinu : P[i]'hiP ≠ u := by
        intro heu
        rw [heu] at hiB
        rcases hu with huA | huC
        · exact (Set.disjoint_left.mp c.stepConn.1.1 huA) hiB
        · exact (Set.disjoint_left.mp c.stepConn.1.2.2 hiB) huC
      have hinb : P[i]'hiP ≠ b₀ := by
        intro heb
        exact c.rightStar_b₀.1 (heb ▸ (Or.inl (Or.inr hiB)))
      exact hcon (P[i]'hiP)
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP).mpr
          ⟨List.getElem_mem hiP, hinu, hinb⟩)
        (Or.inr hiB)
    · exact Or.inr hiC

  let F : Set V := {w : V | w ∈ R}
  have hFsub : F ⊆ (B ∪ A ∪ C)ᶜ := by
    intro w hwF
    have hout := hRoutside w hwF
    rintro ((hwB | hwA) | hwC)
    · exact hout (Or.inl (Or.inr hwB))
    · exact hout (Or.inl (Or.inl hwA))
    · exact hout (Or.inr hwC)
  have hFconn : ConnectedSet G F := by
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1
  have hbF : b₀ ∈ F :=
    Workspace.ProofLemmas.PathBasics.getLast_mem hR.2.2
  have hqF : P[i + 1]'hiNext ∈ F :=
    Workspace.ProofLemmas.PathBasics.head_mem hR.2.1
  have hatt : (attachments G F (A ∪ C)).Nonempty := by
    refine ⟨P[i]'hiP, hiAC, P[i + 1]'hiNext, hqF, ?_⟩
    exact Workspace.ProofLemmas.PathBasics.path_adj_succ hP.1 hiNext

  have hmaxswap : MaximalStaircase G B C A b₀ R₀.reverse a₀ :=
    Workspace.ProofLemmas.StaircaseLeftRightSymmetry.maximalStaircase_swap.mp c.maxStaircase
  have hleftb : IsLeftStar G B C A b₀ :=
    Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mp c.rightStar_b₀
  rcases _root_.Workspace.Statements.S12.SPGT.thm_12_3 G c.berge c.noK4 c.noPrism c.no1br
      B C A b₀ a₀ R₀.reverse hmaxswap F hFsub hFconn ⟨b₀, hbF, hleftb⟩ hatt with
    ⟨v, hvF, hvmajSwap⟩ | ⟨r, s, Q, hQF, hbanSwap⟩
  · -- A major vertex on the suffix.
    have hvmaj : MajorForStaircase G A C B a₀ R₀ b₀ v :=
      Workspace.ProofLemmas.StaircaseLeftRightSymmetry.majorForStaircase_swap.mpr hvmajSwap
    have hvW : v ∉ Ws G A C B x := hRoutsideW v hvF
    have hvx : v ∉ x := fun hvx => hvW (Or.inl (Or.inl hvx))
    have hvAX : ¬ VertexComplete G v (A ∪ Xs x) := by
      intro hvcomp
      exact hvW (Or.inl (Or.inr ⟨hRoutside v hvF, hvcomp⟩))
    by_cases hvB : VertexComplete G v B
    · -- Then `v` can be appended to the maximum right-sequence.
      have hseq : IsRightSequence G A C B (x ++ [v]) := by
        apply rightSequence_snoc c.rseq hvx hvB
        · intro hvA
          rw [VertexComplete] at hvAX
          push_neg at hvAX
          obtain ⟨y, hy, hny⟩ := hvAX
          rcases hy with hyA | hyx
          · exact False.elim (hny (hvA y hyA))
          · exact ⟨y, hyx, fun h => hny h.symm⟩
        · intro hvanti
          obtain ⟨a, ha, hva⟩ := hvmaj.2.1
          exact False.elim (hvanti a ha hva)
      have := c.maximal (x ++ [v]) hseq
      simp at this
    · -- Otherwise 12.1 and the absence of a 2-breaker put `v` on the left diagonal.
      have hdiag := major_diagonal_or_central c.berge c.noK4 c.noPrism c.no1br
        c.maxStaircase hvmaj.1 hvmaj
      have hnright : ¬ RightDiagonal G A C B a₀ R₀ b₀ v := by
        intro hr
        exact hvB (fun b hb => hr.2 b (Or.inl hb))
      have hncentral : ¬ CentralForStaircase G A C B a₀ R₀ b₀ v := by
        intro hc
        apply c.no2br
        refine ⟨A, C, B, a₀, R₀, b₀, ({v} : Set V), c.strongMax, ⟨?_, ?_⟩,
          ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
        · intro q hq
          simpa only [Set.mem_singleton_iff] using hq.symm ▸ hvmaj.1
        · intro q₁ q₂
          have heq : q₁ = q₂ := Subtype.ext (q₁.2.trans q₂.2.symm)
          rw [heq]
        · obtain ⟨a, ha⟩ := c.Ane
          refine ⟨a, ha, ?_⟩
          intro q hq
          rw [Set.mem_singleton_iff.mp hq]
          exact (hc.2.1 a (Or.inl ha)).symm
        · obtain ⟨b, hb⟩ := c.Bne
          refine ⟨b, hb, ?_⟩
          intro q hq
          rw [Set.mem_singleton_iff.mp hq]
          exact (hc.2.1 b (Or.inr hb)).symm
        · intro ha₀
          exact hc.2.2.1 ((ha₀ v rfl).symm)
        · intro hb₀
          exact hc.2.2.2 ((hb₀ v rfl).symm)
        · obtain ⟨z, hzR, hvz⟩ := hvmaj.2.2.2
          refine ⟨z, hzR, ?_⟩
          intro q hq
          rw [Set.mem_singleton_iff.mp hq]
          exact hvz.symm
      have hvleft : LeftDiagonal G A C B a₀ R₀ b₀ v := by
        rcases hdiag with hl | hr | hc
        · exact hl
        · exact absurd hr hnright
        · exact absurd hc hncentral
      have hvX : ¬ VertexComplete G v (Xs x) := by
        intro hvcomp
        apply hvAX
        rintro y (hyA | hyX)
        · exact hvleft.2 y (Or.inl hyA)
        · exact hvcomp y hyX
      let LD : V → Prop := fun w => LeftDiagonal G A C B a₀ R₀ b₀ w
      have hLD : ∀ w, LD w → VertexComplete G w A := by
        intro w hw a ha
        exact hw.2 a (Or.inl ha)
      obtain ⟨T, z, hT, hzx, hTint, hznotleft⟩ :=
        exists_chain_from_vertex c.rseq LD hLD hvx (by simpa [Xs] using hvX)
      have hright_of_x : ∀ w ∈ x, RightDiagonal G A C B a₀ R₀ b₀ w := by
        intro w hw
        refine ⟨c.x_not_mem_K w hw, ?_⟩
        rintro y (hyB | rfl)
        · exact c.xComplete w hw y hyB
        · exact c.adj_a₀ w hw
      have hTdiag : ∀ w ∈ SPGT.interior T,
          LeftDiagonal G A C B a₀ R₀ b₀ w ∧
            RightDiagonal G A C B a₀ R₀ b₀ w := by
        intro w hw
        obtain ⟨hwx, hwleft⟩ := hTint w hw
        exact ⟨hwleft, hright_of_x w hwx⟩
      have hzright : RightDiagonal G A C B a₀ R₀ b₀ z := hright_of_x z hzx
      have hstars := _root_.Workspace.Statements.S12.SPGT.thm_12_5 G c.berge c.noK4
        c.noPrism c.no1br c.no2br A C B a₀ b₀ R₀ c.strongMax T v z hT hTdiag
        ⟨hvleft, hnright⟩ ⟨hzright, hznotleft⟩
      obtain ⟨b, hb, hvb⟩ := hvmaj.2.2.1
      exact hstars.1.2.2 b (Or.inl hb) hvb
  · -- A banister on the suffix, read back in the original orientation.
    have hban : IsBanister G A C B s Q.reverse r := by
      refine ⟨Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hbanSwap.1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        have hout := hbanSwap.2.1 w (List.mem_reverse.mp hw)
        rintro ((hwA | hwB) | hwC)
        · exact hout (Or.inl (Or.inr hwA))
        · exact hout (Or.inl (Or.inl hwB))
        · exact hout (Or.inr hwC)
      · exact Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isLeftStar_swap.mpr
          hbanSwap.2.2.2.1
      · exact Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mpr
          hbanSwap.2.2.1
      · intro w hw y hy
        apply hbanSwap.2.2.2.2 w
          (Workspace.ProofLemmas.PathBasics.mem_interior_reverse.mp hw) y
        rcases hy with (hyA | hyB) | hyC
        · exact Or.inl (Or.inr hyA)
        · exact Or.inl (Or.inl hyB)
        · exact Or.inr hyC
    have hrF : r ∈ F := hQF r (Workspace.ProofLemmas.PathBasics.head_mem hbanSwap.1.2.1)
    have hsF : s ∈ F := hQF s (Workspace.ProofLemmas.PathBasics.getLast_mem hbanSwap.1.2.2)
    have hrW : r ∉ Ws G A C B x := hRoutsideW r hrF
    have hsW : s ∉ Ws G A C B x := hRoutsideW s hsF
    have hrx : r ∉ x := fun hrx => hrW (Or.inl (Or.inl hrx))
    have hsX : ¬ VertexComplete G s (Xs x) := by
      intro hscomp
      apply hsW
      refine Or.inl (Or.inr ⟨hban.2.2.1.1, ?_⟩)
      rintro y (hyA | hyX)
      · exact hban.2.2.1.2.1 y hyA
      · exact hscomp y hyX
    rw [VertexComplete] at hsX
    push_neg at hsX
    obtain ⟨y, hyx, hsy⟩ := hsX
    have hseq : IsRightSequence G A C B (x ++ [r]) := by
      apply rightSequence_snoc c.rseq hrx hban.2.2.2.1.2.1
      · intro hrA
        obtain ⟨a, ha⟩ := c.Ane
        exact False.elim (hban.2.2.2.1.2.2 a (Or.inl ha) (hrA a ha))
      · intro _
        exact ⟨s, Q.reverse, hban, y, hyx, hsy⟩
    have := c.maximal (x ++ [r]) hseq
    simp at this

end Workspace.ProofLemmas.Thm133Claim1
