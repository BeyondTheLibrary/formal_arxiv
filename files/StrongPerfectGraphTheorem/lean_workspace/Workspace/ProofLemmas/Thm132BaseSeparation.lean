import Workspace.ProofLemmas.Thm132BanisterSeparation

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # Separating an earlier banister from the distinguished banister in 13.2. -/

namespace Workspace.ProofLemmas.Thm132BaseSeparation

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
    exact hR.2.2.2.1.2.2 a₁ (Or.inl ha₁) (hab ▸ hR.2.2.1.2.1 a₁ ha₁)
  have hpos : 0 < R.length := PathBasics.path_length_pos hR.1.1
  by_contra hlt
  have hone : R.length = 1 := by omega
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hone
  have hza : z = a := by simpa using hR.1.2.1
  have hzb : z = b := by simpa using hR.1.2.2
  exact hab (hza.symm.trans hzb)

/-- If the half of the distinguished banister meeting its right end were
linked to the half of an earlier banister meeting its left end, their union
would contain a new banister to the optimal right end. -/
theorem base_halves_not_linked
    {G : SimpleGraph V} {A C B : Set V} {x : List V}
    {a b a₀ r v u u' : V} {E P Q : List V}
    (hA : A.Nonempty)
    (hopt : BOptimalBanister G A C B x a E b)
    (hP : IsBanister G A C B a₀ P b)
    (hQ : IsBanister G A C B r Q v)
    (hbirthR : birth G A C B x r u')
    (hbirthOpt : birth G A C B x a u)
    (hearlier : Earlier x u' u) :
    ¬ ((({z : V | z ∈ P.tail} ∩ {z : V | z ∈ Q.dropLast}).Nonempty) ∨
      ∃ p ∈ P.tail, ∃ q ∈ Q.dropLast, G.Adj p q) := by
  classical
  intro hlink
  have hPlen : 2 ≤ P.length := path_length_two_of_star_ends hA hP
  have hQlen : 2 ≤ Q.length := path_length_two_of_star_ends hA hQ
  have hPconn : ConnectedSet G {z : V | z ∈ P.tail} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (HyperprismRungStructure.isPathList_tail hP.1.1 hPlen)
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
    (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).2
      ⟨PathBasics.getLast_mem hP.1.2.2, by
        intro hba
        obtain ⟨a₁, ha₁⟩ := hA
        exact hP.2.2.2.1.2.2 a₁ (Or.inl ha₁)
          (hba ▸ hP.2.2.1.2.1 a₁ ha₁)⟩
  obtain ⟨T, hT, hTmem⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hconn (Or.inr hrQ) (Or.inl hbP)
  have hTban : IsBanister G A C B r T b := by
    refine ⟨hT, ?_, hQ.2.2.1, hP.2.2.2.1, ?_⟩
    · intro z hz
      rcases hTmem z hz with hzP | hzQ
      · exact hP.2.1 z (List.mem_of_mem_tail hzP)
      · exact hQ.2.1 z (List.dropLast_subset Q hzQ)
    · intro z hz s hs
      have hzdata := (PathBasics.mem_interior_iff_of_pathFrom hT).1 hz
      rcases hTmem z hzdata.1 with hzP | hzQ
      · have hzP' :=
          (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).1 hzP
        exact hP.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hP.1).2
            ⟨hzP'.1, hzP'.2, hzdata.2.2⟩) s hs
      · have hzQ' :=
          (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).1 hzQ
        exact hQ.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hQ.1).2
            ⟨hzQ'.1, hzdata.2.1, hzQ'.2⟩) s hs
  apply hopt.2.2
  exact ⟨r, T, hTban, hbirthR.2.1, u', u, hbirthR, hbirthOpt, hearlier⟩

end Workspace.ProofLemmas.Thm132BaseSeparation
