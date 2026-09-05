import Workspace.ProofLemmas.Thm132Infrastructure

set_option autoImplicit false

/-!
# The minimal-counterexample reduction in 13.2

The printed proof immediately starts manipulating optimal banisters.  Before
doing so, 12.1 and 12.5 give a useful sharpening: a first term of a
right-sequence which misses `a₀` has to be a right-star.  A central term would
itself make a singleton 2-breaker, and a left-diagonal term can be followed
through its predecessors until 12.5 applies.
-/

namespace Workspace.ProofLemmas.Thm132Reduction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem anticonnected_singleton {G : SimpleGraph V} (v : V) :
    AnticonnectedSet G ({v} : Set V) := by
  intro a b
  have hab : a = b := Subtype.ext (a.2.trans b.2.symm)
  subst b
  exact SimpleGraph.Reachable.refl a

/-- If `x[i]` is the first term of a right-sequence not adjacent to `a₀`, then
it is a right-star. -/
theorem first_bad_isRightStar
    {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (hx : IsRightSequence G A C B x)
    (i : ℕ) (hi : i < x.length)
    (hprev : ∀ (j : ℕ) (hj : j < i), G.Adj x[j] a₀)
    (hbad : ¬ G.Adj x[i] a₀) :
    IsRightStar G A C B x[i] := by
  let v : V := x[i]
  have hvB : VertexComplete G v B := hx.1.2 v (List.getElem_mem hi)
  by_cases hvb : v = b₀
  · simpa [v, hvb] using hK.1.1.2.1.2.2.2.1
  have hvout : v ∉ staircaseVertices A C B R₀ :=
    bComplete_not_mem_staircase hK.1.1 hvB hvb
  rcases bComplete_rightStar_or_major hG hK4 heven h1br hK.1 hvout hvB with
    hvstar | hvmajor
  · exact hvstar
  rcases major_diagonal_or_central hG hK4 heven h1br hK.1 hvout hvmajor with
    hvleft | hvright | hvcentral
  · -- Follow predecessors until the first term which is not left-diagonal.
    obtain ⟨L, j, hj, hL, hidx, hleftInt, hnleft⟩ :=
      exists_predecessor_chain hx
        (LeftDiagonal G A C B a₀ R₀ b₀)
        (fun w hw a ha => hw.2 a (Or.inl ha)) i hi
    have hz_ne_v : x[j] ≠ v := by
      intro heq
      apply hnleft
      simpa [v, heq] using hvleft
    have hjle : j ≤ i := by
      obtain ⟨k, hk, hki, hkz⟩ := hidx x[j] (PathBasics.getLast_mem hL.2.2)
      have hkj : k = j := (List.Nodup.getElem_inj_iff hx.1.1).mp hkz
      simpa [hkj] using hki
    have hjlt : j < i := by
      rcases lt_or_eq_of_le hjle with h | h
      · exact h
      · exfalso
        apply hz_ne_v
        subst h
        rfl
    have hza : G.Adj x[j] a₀ := hprev j hjlt
    have hzB : VertexComplete G x[j] B := hx.1.2 _ (List.getElem_mem hj)
    have hzout : x[j] ∉ staircaseVertices A C B R₀ :=
      bComplete_adj_left_not_mem_staircase hK.1.1 hzB hza
    have hzright : RightDiagonal G A C B a₀ R₀ b₀ x[j] := by
      refine ⟨hzout, ?_⟩
      intro y hy
      rcases hy with hyB | hya
      · exact hzB y hyB
      · have : y = a₀ := Set.mem_singleton_iff.mp hya
        simpa [this] using hza
    have hInt : ∀ w ∈ interior L,
        LeftDiagonal G A C B a₀ R₀ b₀ w ∧
          RightDiagonal G A C B a₀ R₀ b₀ w := by
      intro w hw
      have hw_ne_z : w ≠ x[j] :=
        (PathBasics.mem_interior_iff_of_pathFrom hL).mp hw |>.2.2
      have hwleft := hleftInt w
        ((PathBasics.mem_interior_iff_of_pathFrom hL).mp hw).1 hw_ne_z
      obtain ⟨k, hk, hki, hkw⟩ := hidx w
        ((PathBasics.mem_interior_iff_of_pathFrom hL).mp hw).1
      have hw_ne_v : w ≠ v := by
        intro heq
        have hki' : k = i := by
          apply (List.Nodup.getElem_inj_iff hx.1.1).mp
          simpa [v, heq] using hkw
        subst hki'
        exact (PathBasics.mem_interior_iff_of_pathFrom hL).mp hw |>.2.1
          (by simpa [v] using hkw.symm)
      have hki' : k < i := by
        rcases lt_or_eq_of_le hki with h | h
        · exact h
        · exfalso
          apply hw_ne_v
          subst h
          simpa [v] using hkw.symm
      have hwa : G.Adj w a₀ := by
        rw [← hkw]
        exact hprev k hki'
      have hwB : VertexComplete G w B := by
        rw [← hkw]
        exact hx.1.2 _ (List.getElem_mem hk)
      have hwout : w ∉ staircaseVertices A C B R₀ :=
        bComplete_adj_left_not_mem_staircase hK.1.1 hwB hwa
      refine ⟨hwleft, hwout, ?_⟩
      intro y hy
      rcases hy with hyB | hya
      · exact hwB y hyB
      · have : y = a₀ := Set.mem_singleton_iff.mp hya
        simpa [this] using hwa
    have hv_not_right : ¬ RightDiagonal G A C B a₀ R₀ b₀ v := by
      intro hr
      exact hbad (by simpa [v] using hr.2 a₀ (Or.inr rfl))
    have hends := Workspace.Statements.S12.SPGT.thm_12_5 G hG hK4 heven h1br h2br
      A C B a₀ b₀ R₀ hK L v x[j] (by simpa [v] using hL) hInt
      ⟨hvleft, hv_not_right⟩ ⟨hzright, hnleft⟩
    obtain ⟨b, hb⟩ := hK.1.1.1.2.1.2
    exact absurd (hvB b hb) (hends.1.2.2 b (Or.inl hb))
  · exact absurd (hvright.2 a₀ (Or.inr rfl)) (by simpa [v] using hbad)
  · -- A central `B`-complete vertex missing both ends is a singleton 2-breaker.
    apply False.elim
    apply h2br
    refine ⟨A, C, B, a₀, R₀, b₀, ({v} : Set V), ?_⟩
    refine ⟨hK, ⟨?_, anticonnected_singleton v⟩, ?_, ?_, ?_⟩
    · intro q hq
      have hqv : q = v := Set.mem_singleton_iff.mp hq
      simpa [hqv] using hvout
    · obtain ⟨a, ha⟩ := hK.1.1.1.2.1.1
      obtain ⟨b, hb⟩ := hK.1.1.1.2.1.2
      refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩⟩
      · intro q hq
        have hqv : q = v := Set.mem_singleton_iff.mp hq
        subst q
        exact (hvcentral.2.1 a (Or.inl ha)).symm
      · intro q hq
        have hqv : q = v := Set.mem_singleton_iff.mp hq
        subst q
        exact (hvcentral.2.1 b (Or.inr hb)).symm
    · constructor
      · intro hc
        exact hbad (by simpa [v] using (hc v rfl).symm)
      · intro hc
        exact hvcentral.2.2.2 (hc v rfl).symm
    · obtain ⟨r, hr, hvr⟩ := hvmajor.2.2.2
      exact ⟨r, hr, fun q hq => by
        have hqv : q = v := Set.mem_singleton_iff.mp hq
        subst q
        exact hvr.symm⟩

end Workspace.ProofLemmas.Thm132Reduction
