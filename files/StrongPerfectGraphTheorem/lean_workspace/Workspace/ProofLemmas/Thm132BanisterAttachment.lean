import Workspace.ProofLemmas.Thm132BanisterSeparation
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.TwoPathsHole
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The parity attachment argument in claim (1) of 13.2

For two separated banisters `a-P-b` and `r-Q-v`, assume that `v` sees precisely
`b` on `P` and that `a` misses `v`.  The two odd-hole comparisons in the paper
then say that `a` sees precisely `r` on `Q`.  The proof below extracts an
induced `a`--`v` path inside `Q \ {r}` whenever a second neighbour exists; this
is the invariant content of the paper's “path with interior in `R \ r`”.
-/

namespace Workspace.ProofLemmas.Thm132BanisterAttachment

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas.Thm132BanisterSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {R : List V} (hR : IsRungOfStrip G A C B a R b) :
    ∀ z ∈ R, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ hR.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ hR.2.2.1))
  · exact Or.inr (hR.2.2.2.2.2 z
      ((PathBasics.mem_interior_iff_of_pathFrom hR.1).2 ⟨hz, hza, hzb⟩))

private theorem path_length_two_of_ne {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hab : a ≠ b) : 2 ≤ P.length := by
  have hpos : 0 < P.length := PathBasics.path_length_pos hP.1
  by_contra h
  have hone : P.length = 1 := by omega
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hone
  have hza : z = a := by simpa using hP.2.1
  have hzb : z = b := by simpa using hP.2.2
  exact hab (hza.symm.trans hzb)

/-- The parity lemma used to finish the `n = 1` case of claim (1). -/
theorem left_end_sees_exactly_left_end
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} (hS : StepConnected G A C B)
    {a b r v : V} {P Q : List V}
    (hP : IsBanister G A C B a P b)
    (hQ : IsBanister G A C B r Q v)
    (hav : ¬ G.Adj a v)
    (hvonly : ∀ z ∈ P, (G.Adj z v ↔ z = b))
    (hnolink : ¬ ((({z : V | z ∈ P.tail} ∩ {z : V | z ∈ Q.dropLast}).Nonempty) ∨
      ∃ p ∈ P.tail, ∃ q ∈ Q.dropLast, G.Adj p q))
    (hdisj : ∀ z ∈ P, z ∉ Q) :
    ∀ z ∈ Q, (G.Adj a z ↔ z = r) := by
  classical
  obtain ⟨a₁, ha₁⟩ := hS.2.1.1
  have hab : a ≠ v := by
    intro hav'
    exact hQ.2.2.2.1.2.2 a₁ (Or.inl ha₁)
      (hav' ▸ hP.2.2.1.2.1 a₁ ha₁)
  have hPlen : 2 ≤ P.length := path_length_two_of_ne hP.1 (by
    intro hab'
    exact hP.2.2.2.1.2.2 a₁ (Or.inl ha₁)
      (hab' ▸ hP.2.2.1.2.1 a₁ ha₁))
  have hQlen : 2 ≤ Q.length := path_length_two_of_ne hQ.1 (by
    intro hrv
    exact hQ.2.2.2.1.2.2 a₁ (Or.inl ha₁)
      (hrv ▸ hQ.2.2.1.2.1 a₁ ha₁))
  have hvQ : v ∈ Q := PathBasics.getLast_mem hQ.1.2.2
  have haP : a ∈ P := PathBasics.head_mem hP.1.2.1
  have hbP : b ∈ P := PathBasics.getLast_mem hP.1.2.2
  have hvP : v ∉ P := fun hv => hdisj v hv hvQ
  have hvaP : G.Adj v b := (hvonly b hbP).2 rfl |>.symm
  have hvotherP : ∀ z ∈ P, z ≠ b → ¬ G.Adj v z := by
    intro z hz hzb hvz
    exact hzb ((hvonly z hz).1 hvz.symm)
  let P₁ : List V := P ++ [v]
  have hP₁ : IsPathFrom G P₁ a v := by
    dsimp [P₁]
    exact PathAttach.isPathFrom_concat hP.1 hvaP hvP hvotherP
  have hP₁int : ∀ z ∈ interior P₁, z ∈ P.tail := by
    intro z hz
    have hd := (PathBasics.mem_interior_iff_of_pathFrom hP₁).1 hz
    have hzP : z ∈ P := by
      rcases List.mem_append.mp hd.1 with hzP | hzv
      · exact hzP
      · exact absurd (by simpa using hzv) hd.2.2
    exact (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).2 ⟨hzP, hd.2.1⟩
  have hnoMeet : ∀ p ∈ P.tail, ∀ q ∈ Q.dropLast, p ≠ q := by
    intro p hp q hq hpq
    apply hnolink
    exact Or.inl ⟨p, hp, hpq ▸ hq⟩
  have hnoEdge := halves_anticomplete_of_not_linked hnolink

  -- First comparison: if `a` missed all of `Q`, the two displayed paths make
  -- an odd hole.
  have hsome : ∃ z ∈ Q, G.Adj a z := by
    by_contra hn
    push_neg at hn
    have haQnone : ∀ z ∈ Q, ¬ G.Adj a z := hn
    have ha₁Q : a₁ ∉ Q := by
      intro haQ
      exact hQ.2.1 a₁ haQ (Or.inl (Or.inl ha₁))
    have ha₁r : G.Adj a₁ r := (hQ.2.2.1.2.1 a₁ ha₁).symm
    have ha₁other : ∀ z ∈ Q, z ≠ r → ¬ G.Adj a₁ z := by
      intro z hz hzr
      by_cases hzv : z = v
      · subst z
        exact fun h => hQ.2.2.2.1.2.2 a₁ (Or.inl ha₁) h.symm
      · intro h
        exact hQ.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hQ.1).2 ⟨hz, hzr, hzv⟩)
          a₁ (Or.inl (Or.inl ha₁)) h.symm
    have htail : IsPathFrom G (a₁ :: Q) a₁ v :=
      PathAttach.isPathFrom_cons hQ.1 ha₁r ha₁Q ha₁other
    have ha_ne_a₁ : a ≠ a₁ := fun haa =>
      hP.2.2.1.1 (haa ▸ Or.inl (Or.inl ha₁))
    have haQ : a ∉ Q := fun haq => hdisj a haP haq
    have ha_tail : a ∉ a₁ :: Q := by simpa [ha_ne_a₁, haQ]
    have hP₂ : IsPathFrom G (a :: a₁ :: Q) a v :=
      PathAttach.isPathFrom_cons htail (hP.2.2.1.2.1 a₁ ha₁) ha_tail
        (by
          intro z hz hza₁
          rcases List.mem_cons.mp hz with h | h
          · exact absurd h hza₁
          · exact haQnone z h)
    have hP₂int : ∀ z ∈ interior (a :: a₁ :: Q),
        z = a₁ ∨ z ∈ Q.dropLast := by
      intro z hz
      have hd := (PathBasics.mem_interior_iff_of_pathFrom hP₂).1 hz
      rcases List.mem_cons.mp hd.1 with hza | hzrest
      · exact absurd hza hd.2.1
      rcases List.mem_cons.mp hzrest with hza₁ | hzQ
      · exact Or.inl hza₁
      · exact Or.inr
          ((HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2 ⟨hzQ, hd.2.2⟩)
    have hdisjInt : ∀ z ∈ interior P₁, z ∉ interior (a :: a₁ :: Q) := by
      intro z hz₁ hz₂
      have hzTail := hP₁int z hz₁
      rcases hP₂int z hz₂ with hza₁ | hzQ
      · subst z
        exact hP.2.1 a₁ (List.mem_of_mem_tail hzTail) (Or.inl (Or.inl ha₁))
      · exact hnoMeet z hzTail z hzQ rfl
    have hantiInt : ∀ z ∈ interior P₁, ∀ y ∈ interior (a :: a₁ :: Q),
        ¬ G.Adj z y := by
      intro z hz₁ y hy₂
      have hzTail := hP₁int z hz₁
      rcases hP₂int y hy₂ with hya₁ | hyQ
      · subst y
        have hzP : z ∈ P := List.mem_of_mem_tail hzTail
        have hzneA : z ≠ a :=
          (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).1 hzTail |>.2
        by_cases hzb : z = b
        · subst z
          exact hP.2.2.2.1.2.2 a₁ (Or.inl ha₁)
        · exact hP.2.2.2.2 z
            ((PathBasics.mem_interior_iff_of_pathFrom hP.1).2 ⟨hzP, hzneA, hzb⟩)
            a₁ (Or.inl (Or.inl ha₁))
      · exact hnoEdge z hzTail y hyQ
    have hP₁len : 3 ≤ P₁.length := by simp [P₁]; omega
    have hP₂len : 3 ≤ (a :: a₁ :: Q).length := by simp; omega
    obtain ⟨hhole, hhlen⟩ := TwoPathsHole.odd_hole_of_two_paths
      hP₁ hP₂ hP₁len hP₂len hdisjInt hantiInt
    have he := hG.1 _ hhole
    rw [hhlen] at he
    obtain ⟨kp, hkp⟩ :=
      (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a b P hP).2
    obtain ⟨kq, hkq⟩ :=
      (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS r v Q hQ).2
    obtain ⟨ke, hke⟩ := he
    have hPlength := PathBasics.length_eq_pathLength_add_one hP.1.1
    have hQlength := PathBasics.length_eq_pathLength_add_one hQ.1.1
    simp only [P₁, pathLength, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil] at hkp hkq hke hPlength hQlength
    omega

  have honly : ∀ z ∈ Q, G.Adj a z → z = r := by
    intro z hzQ haz
    by_contra hzr
    have hzTail : z ∈ Q.tail :=
      (HyperprismRungStructure.mem_tail_iff_of_pathFrom hQ.1).2 ⟨hzQ, hzr⟩
    have hQtailConn : ConnectedSet G {q : V | q ∈ Q.tail} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (HyperprismRungStructure.isPathList_tail hQ.1.1 hQlen)
    have hconn : ConnectedSet G ({q : V | q ∈ Q.tail} ∪ {a}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hQtailConn ⟨z, hzTail, haz⟩
    have hvTail : v ∈ Q.tail :=
      (HyperprismRungStructure.mem_tail_iff_of_pathFrom hQ.1).2
        ⟨hvQ, by
          intro hvr
          exact hQ.2.2.2.1.2.2 a₁ (Or.inl ha₁)
            (hvr ▸ hQ.2.2.1.2.1 a₁ ha₁)⟩
    obtain ⟨M, hM, hMmem⟩ :=
      InducedPathExtraction.exists_isPathFrom_of_connected hconn (Or.inr rfl) (Or.inl hvTail)
    have hMintQ : ∀ q ∈ interior M, q ∈ interior Q := by
      intro q hq
      have hd := (PathBasics.mem_interior_iff_of_pathFrom hM).1 hq
      rcases hMmem q hd.1 with hqTail | hqa
      · have hqt :=
          (HyperprismRungStructure.mem_tail_iff_of_pathFrom hQ.1).1 hqTail
        exact (PathBasics.mem_interior_iff_of_pathFrom hQ.1).2
          ⟨hqt.1, hqt.2, hd.2.2⟩
      · exact False.elim (hd.2.1 (Set.mem_singleton_iff.mp hqa))
    have hMintDrop : ∀ q ∈ interior M, q ∈ Q.dropLast := by
      intro q hq
      have hqi := (PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 (hMintQ q hq)
      exact (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2
        ⟨hqi.1, hqi.2.2⟩
    have hMlen2 : 2 ≤ M.length := path_length_two_of_ne hM hab
    have hMlen3 : 3 ≤ M.length := by
      by_contra hlt
      have htwo : M.length = 2 := by omega
      have hlength : pathLength M = 1 := by simp [pathLength, htwo]
      exact hav (PathBasics.isPathFrom_ends_adj_of_length_one hM hlength)
    have hM_P₁_disj : ∀ q ∈ interior M, q ∉ interior P₁ := by
      intro q hq hqP
      exact hnoMeet (q := q) (p := q) (hP₁int q hqP) (hMintDrop q hq) rfl
    have hM_P₁_anti : ∀ q ∈ interior M, ∀ p ∈ interior P₁, ¬ G.Adj q p := by
      intro q hq p hp hqp
      exact hnoEdge p (hP₁int p hp) q (hMintDrop q hq) hqp.symm
    obtain ⟨hhole₁, hhlen₁⟩ := TwoPathsHole.odd_hole_of_two_paths
      hM hP₁ hMlen3 (by simpa [P₁] using (show 3 ≤ P.length + 1 by omega))
      hM_P₁_disj hM_P₁_anti

    obtain ⟨c, U, d, hU, ha₁U⟩ :=
      hS.2.2.1 a₁ (Or.inl (Or.inl ha₁))
    have hc : c = a₁ := (hU.2.2.2.1 a₁ ha₁U ha₁).symm
    subst c
    have hUlen : 2 ≤ U.length := path_length_two_of_ne hU.1 (by
      intro ha₁d
      exact Set.disjoint_left.mp hS.1.1 ha₁ (ha₁d ▸ hU.2.2.1))
    have haU : a ∉ U := by
      intro haU
      exact hP.2.2.1.1 (rung_mem_strip hU a haU)
    have hvU : v ∉ U := by
      intro hvU
      exact hQ.2.2.2.1.1 (rung_mem_strip hU v hvU)
    have haotherU : ∀ y ∈ U, y ≠ a₁ → ¬ G.Adj a y := by
      intro y hy hya₁
      rcases rung_mem_strip hU y hy with (hyA | hyB) | hyC
      · exact absurd (hU.2.2.2.1 y hy hyA) hya₁
      · exact hP.2.2.1.2.2 y (Or.inl hyB)
      · exact hP.2.2.1.2.2 y (Or.inr hyC)
    have hvotherU : ∀ y ∈ U, y ≠ d → ¬ G.Adj v y := by
      intro y hy hyd
      rcases rung_mem_strip hU y hy with (hyA | hyB) | hyC
      · exact hQ.2.2.2.1.2.2 y (Or.inl hyA)
      · exact absurd (hU.2.2.2.2.1 y hy hyB) hyd
      · exact hQ.2.2.2.1.2.2 y (Or.inr hyC)
    let P₃ : List V := a :: (U ++ [v])
    have hP₃ : IsPathFrom G P₃ a v := by
      dsimp [P₃]
      exact PathAttach.isPathFrom_cons_concat hU.1
        (hP.2.2.1.2.1 a₁ ha₁) (hQ.2.2.2.1.2.1 d hU.2.2.1)
        hav hab haU hvU haotherU hvotherU
    have hP₃int : ∀ y ∈ interior P₃, y ∈ U := by
      intro y hy
      have hd := (PathBasics.mem_interior_iff_of_pathFrom hP₃).1 hy
      rcases List.mem_cons.mp hd.1 with hya | hyrest
      · exact absurd hya hd.2.1
      rcases List.mem_append.mp hyrest with hyU | hyv
      · exact hyU
      · exact absurd (by simpa using hyv) hd.2.2
    have hM_P₃_disj : ∀ q ∈ interior M, q ∉ interior P₃ := by
      intro q hq hqP
      exact hQ.2.1 q ((PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 (hMintQ q hq)).1
        (rung_mem_strip hU q (hP₃int q hqP))
    have hM_P₃_anti : ∀ q ∈ interior M, ∀ y ∈ interior P₃,
        ¬ G.Adj q y := by
      intro q hq y hy
      exact hQ.2.2.2.2 q (hMintQ q hq) y (rung_mem_strip hU y (hP₃int y hy))
    obtain ⟨hhole₃, hhlen₃⟩ := TwoPathsHole.odd_hole_of_two_paths
      hM hP₃ hMlen3 (by simp [P₃]; omega) hM_P₃_disj hM_P₃_anti
    have he₁ := hG.1 _ hhole₁
    have he₃ := hG.1 _ hhole₃
    rw [hhlen₁] at he₁
    rw [hhlen₃] at he₃
    obtain ⟨kp, hkp⟩ :=
      (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a b P hP).2
    obtain ⟨ku, hku⟩ :=
      (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a b P hP).1
        a₁ U d hU
    obtain ⟨ke₁, hke₁⟩ := he₁
    obtain ⟨ke₃, hke₃⟩ := he₃
    have hPlength := PathBasics.length_eq_pathLength_add_one hP.1.1
    have hUlength := PathBasics.length_eq_pathLength_add_one hU.1.1
    have hMlength := PathBasics.length_eq_pathLength_add_one hM.1
    simp only [P₁, P₃, pathLength, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil] at hkp hku hke₁ hke₃ hPlength hUlength hMlength
    omega
  obtain ⟨z, hzQ, haz⟩ := hsome
  have hzr : z = r := honly z hzQ haz
  have har : G.Adj a r := hzr ▸ haz
  intro z hzQ
  constructor
  · exact honly z hzQ
  · rintro rfl
    exact har

end Workspace.ProofLemmas.Thm132BanisterAttachment
