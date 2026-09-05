import Workspace.ProofLemmas.Thm132Optimal
import Workspace.ProofLemmas.HyperprismRungStructure

set_option autoImplicit false

/-!
# The optimal-banister separation used in 13.2

The proof of 13.2 twice uses the phrase “as in the proof of 13.1”: if a
banister whose left end was born earlier met, or had a cross-edge to, an
optimal banister, the two appropriate half-paths would form a connected set.
An induced path through that set is a new banister to the old right end, with
the earlier-born left end, contradicting optimality.  This file isolates that
argument.
-/

namespace Workspace.ProofLemmas.Thm132BanisterSeparation

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem path_length_two_of_star_ends
    {G : SimpleGraph V} {A C B : Set V} {a b : V} {R : List V}
    (hA : A.Nonempty) (hR : IsBanister G A C B a R b) : 2 ≤ R.length := by
  obtain ⟨a₁, ha₁⟩ := hA
  have hab : a ≠ b := by
    intro hab
    have hadj : G.Adj a a₁ := hR.2.2.1.2.1 a₁ ha₁
    have hnon : ¬ G.Adj b a₁ := hR.2.2.2.1.2.2 a₁ (Or.inl ha₁)
    exact hnon (hab ▸ hadj)
  have hpos : 0 < R.length := PathBasics.path_length_pos hR.1.1
  by_contra hlt
  have hone : R.length = 1 := by omega
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hone
  have hza : z = a := by simpa using hR.1.2.1
  have hzb : z = b := by simpa using hR.1.2.2
  exact hab (hza.symm.trans hzb)

/-- If the two half-banisters were linked, extracting an induced path from the
earlier left-star to the optimal right-star would violate optimality. -/
theorem optimal_halves_not_linked
    {G : SimpleGraph V} {A C B : Set V} {x : List V}
    {a b r v u u' : V} {P Q : List V}
    (hA : A.Nonempty)
    (hopt : BOptimalBanister G A C B x a P b)
    (hQ : IsBanister G A C B r Q v)
    (hbirthR : birth G A C B x r u')
    (hbirthP : birth G A C B x a u)
    (hearlier : Earlier x u' u) :
    ¬ ((({z : V | z ∈ P.tail} ∩ {z : V | z ∈ Q.dropLast}).Nonempty) ∨
      ∃ p ∈ P.tail, ∃ q ∈ Q.dropLast, G.Adj p q) := by
  classical
  intro hlink
  have hPlen : 2 ≤ P.length := path_length_two_of_star_ends hA hopt.1
  have hQlen : 2 ≤ Q.length := path_length_two_of_star_ends hA hQ
  have hPconn : ConnectedSet G {z : V | z ∈ P.tail} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (HyperprismRungStructure.isPathList_tail hopt.1.1.1 hPlen)
  have hQconn : ConnectedSet G {z : V | z ∈ Q.dropLast} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (HyperprismRungStructure.isPathList_dropLast hQ.1.1 hQlen)
  have hconn : ConnectedSet G
      ({z : V | z ∈ P.tail} ∪ {z : V | z ∈ Q.dropLast}) :=
    ConnectedSetUnionAttach.connectedSet_union hPconn hQconn hlink
  have hrQ : r ∈ Q.dropLast :=
    (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2
      ⟨PathBasics.head_mem hQ.1.2.1, by
        intro hrv
        obtain ⟨a₁, ha₁⟩ := hA
        exact hQ.2.2.2.1.2.2 a₁ (Or.inl ha₁)
          (hrv ▸ hQ.2.2.1.2.1 a₁ ha₁)⟩
  have hbP : b ∈ P.tail :=
    (HyperprismRungStructure.mem_tail_iff_of_pathFrom hopt.1.1).2
      ⟨PathBasics.getLast_mem hopt.1.1.2.2, by
        intro hba
        obtain ⟨a₁, ha₁⟩ := hA
        exact hopt.1.2.2.2.1.2.2 a₁ (Or.inl ha₁)
          (hba ▸ hopt.1.2.2.1.2.1 a₁ ha₁)⟩
  obtain ⟨T, hT, hTmem⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hconn (Or.inr hrQ) (Or.inl hbP)
  have hTban : IsBanister G A C B r T b := by
    refine ⟨hT, ?_, hQ.2.2.1, hopt.1.2.2.2.1, ?_⟩
    · intro z hz
      rcases hTmem z hz with hzP | hzQ
      · exact hopt.1.2.1 z (List.mem_of_mem_tail hzP)
      · exact hQ.2.1 z (List.dropLast_subset Q hzQ)
    · intro z hz s hs
      have hzdata := (PathBasics.mem_interior_iff_of_pathFrom hT).1 hz
      rcases hTmem z hzdata.1 with hzP | hzQ
      · have hzP' :=
          (HyperprismRungStructure.mem_tail_iff_of_pathFrom hopt.1.1).1 hzP
        exact hopt.1.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hopt.1.1).2
            ⟨hzP'.1, hzP'.2, hzdata.2.2⟩) s hs
      · have hzQ' :=
          (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).1 hzQ
        exact hQ.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hQ.1).2
            ⟨hzQ'.1, hzdata.2.1, hzQ'.2⟩) s hs
  apply hopt.2.2
  exact ⟨r, T, hTban, hbirthR.2.1, u', u, hbirthR, hbirthP, hearlier⟩

/-- The no-link conclusion also rules out a common vertex of the two full
banister paths.  If the common vertex were an excluded end of one half, the
first (respectively last) edge of that path would itself be a forbidden link. -/
theorem banisters_disjoint_of_halves_not_linked
    {G : SimpleGraph V} {A C B : Set V} {a b r v : V} {P Q : List V}
    (hA : A.Nonempty)
    (hP : IsBanister G A C B a P b)
    (hQ : IsBanister G A C B r Q v)
    (hnolink : ¬ ((({z : V | z ∈ P.tail} ∩ {z : V | z ∈ Q.dropLast}).Nonempty) ∨
      ∃ p ∈ P.tail, ∃ q ∈ Q.dropLast, G.Adj p q)) :
    ∀ z ∈ P, z ∉ Q := by
  classical
  have hPlen : 2 ≤ P.length := path_length_two_of_star_ends hA hP
  have hQlen : 2 ≤ Q.length := path_length_two_of_star_ends hA hQ
  have hav : a ≠ v := by
    obtain ⟨a₁, ha₁⟩ := hA
    intro hav
    exact hQ.2.2.2.1.2.2 a₁ (Or.inl ha₁)
      (hav ▸ hP.2.2.1.2.1 a₁ ha₁)
  intro z hzP hzQ
  by_cases hza : z = a
  · have haQdrop : a ∈ Q.dropLast :=
      (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2
        ⟨hza ▸ hzQ, hav⟩
    let p : V := P[1]
    have hpP : p ∈ P := List.getElem_mem (by omega)
    have hpne : p ≠ a := by
      have hzero : P[0]'(by omega) = a :=
        PathBasics.getElem_zero_of_head? hP.1.2.1 (by omega)
      intro hpa
      exact PathBasics.path_ne_of_ne_index hP.1.1 (i := 1) (j := 0)
        (by omega) (by omega) (by omega)
        (by simpa [p, hzero] using hpa)
    have hpTail : p ∈ P.tail :=
      (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).2 ⟨hpP, hpne⟩
    have hpa : G.Adj p a := by
      have h := PathBasics.path_adj_succ hP.1.1 (i := 0) (by omega)
      have hzero : P[0]'(by omega) = a :=
        PathBasics.getElem_zero_of_head? hP.1.2.1 (by omega)
      simpa [p, hzero] using h.symm
    exact hnolink (Or.inr ⟨p, hpTail, a, haQdrop, hpa⟩)
  · have hzTail : z ∈ P.tail :=
      (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).2 ⟨hzP, hza⟩
    by_cases hzv : z = v
    · let q : V := Q[Q.length - 2]
      have hqQ : q ∈ Q := List.getElem_mem (by omega)
      have hqne : q ≠ v := by
        have hlast : Q[Q.length - 1]'(by omega) = v :=
          PathBasics.getElem_last_of_getLast? hQ.1.2.2 (by omega)
        intro hqv
        exact PathBasics.path_ne_of_ne_index hQ.1.1
          (i := Q.length - 2) (j := Q.length - 1) (by omega) (by omega) (by omega)
          (by simpa [q, hlast] using hqv)
      have hqDrop : q ∈ Q.dropLast :=
        (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2 ⟨hqQ, hqne⟩
      have hvq : G.Adj v q := by
        have h := PathBasics.path_adj_succ hQ.1.1 (i := Q.length - 2) (by omega)
        have hlast : Q[Q.length - 1]'(by omega) = v :=
          PathBasics.getElem_last_of_getLast? hQ.1.2.2 (by omega)
        have hs : Q.length - 2 + 1 = Q.length - 1 := by omega
        have hlast' : Q[Q.length - 2 + 1]'(by omega) = v := by
          simpa only [hs] using hlast
        rw [hlast'] at h
        simpa [q] using h.symm
      exact hnolink (Or.inr ⟨z, hzTail, q, hqDrop, hzv ▸ hvq⟩)
    · have hzDrop : z ∈ Q.dropLast :=
        (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2 ⟨hzQ, hzv⟩
      exact hnolink (Or.inl ⟨z, hzTail, hzDrop⟩)

/-- The edge half of the separation, in the convenient pointwise form used by
the parity arguments. -/
theorem halves_anticomplete_of_not_linked
    {G : SimpleGraph V} {P Q : List V}
    (hnolink : ¬ ((({z : V | z ∈ P.tail} ∩ {z : V | z ∈ Q.dropLast}).Nonempty) ∨
      ∃ p ∈ P.tail, ∃ q ∈ Q.dropLast, G.Adj p q)) :
    ∀ p ∈ P.tail, ∀ q ∈ Q.dropLast, ¬ G.Adj p q := by
  intro p hp q hq hpq
  exact hnolink (Or.inr ⟨p, hp, q, hq, hpq⟩)

end Workspace.ProofLemmas.Thm132BanisterSeparation
