import Workspace.Types.Core
import Workspace.ProofLemmas.MinimalThreeTerminalWitnesses
import Workspace.ProofLemmas.DeletedWitnessIsUnique
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction

set_option autoImplicit false

namespace Workspace.Types.ThroughPathWhenThirdWitnessOnPath

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm244Shapes

private theorem connectedSet_diff_first_of_isPathFrom
    {V : Type*} {G : SimpleGraph V} {Q : List V} {a b : V}
    (hQ : IsPathFrom G Q a b) (hab : a ≠ b) :
    ConnectedSet G ({w : V | w ∈ Q} \ {a}) := by
  have hpos : 0 < Q.length :=
    Workspace.ProofLemmas.PathBasics.path_length_pos hQ.1
  have hlen : 1 < Q.length := by
    by_contra hnot
    have hlen_one : Q.length = 1 := by omega
    rcases Q with _ | ⟨q, t⟩
    · simp at hlen_one
    · rcases t with _ | ⟨r, s⟩
      · have hqa : q = a := by simpa using hQ.2.1
        have hqb : q = b := by simpa using hQ.2.2
        exact hab (hqa.symm.trans hqb)
      · simp at hlen_one
  have htailPath : IsPathList G (Q.drop 1) :=
    Workspace.ProofLemmas.PathBasics.isPathList_drop hQ.1 hlen
  have htailConn : ConnectedSet G {w : V | w ∈ Q.drop 1} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      htailPath
  convert htailConn using 1
  ext w
  rcases Q with _ | ⟨q, t⟩
  · simp at hpos
  · have hqa : q = a := by simpa using hQ.2.1
    have hqnot : q ∉ t :=
      (List.nodup_cons.mp (Workspace.ProofLemmas.PathBasics.path_nodup hQ.1)).1
    subst q
    constructor
    · rintro ⟨hw, hwa⟩
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hwt
      · exact absurd rfl hwa
      · simpa using hwt
    · intro hwt
      change w ∈ t at hwt
      change w ∈ a :: t ∧ w ≠ a
      refine ⟨by simp only [List.mem_cons]; exact Or.inr hwt, ?_⟩
      intro hwa
      subst w
      exact hqnot hwt

theorem throughPathWhenThirdWitnessOnPath
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V) (v : Fin 3 → V)
    (hv : ∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i)
    (hpair : ∀ i j : Fin 3, i ≠ j → v i ≠ v j)
    (hmin : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ x ∈ S, x ∈ N i) → F.ncard ≤ S.ncard)
    (hfixed : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, v i ∈ S) → S = F)
    (Q : List V) (hQ : IsPathFrom G Q (v 0) (v 1))
    (hQF : ∀ w ∈ Q, w ∈ F) (hv2Q : v 2 ∈ Q) :
    ThroughPath G F N 0 1 2 Q (v 0) (v 1) := by
  classical
  have hQconn : ConnectedSet G {w : V | w ∈ Q} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQ.1
  have hQeq : {w : V | w ∈ Q} = F := by
    apply hfixed _ hQF hQconn
    intro i
    fin_cases i
    · exact (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ).1
    · exact (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ).2
    · exact hv2Q
  have hconn0 : ConnectedSet G (F \ {v 0}) := by
    rw [← hQeq]
    exact connectedSet_diff_first_of_isPathFrom hQ (hpair 0 1 (by decide))
  have hconn1 : ConnectedSet G (F \ {v 1}) := by
    rw [← hQeq]
    simpa only [List.mem_reverse] using
      connectedSet_diff_first_of_isPathFrom
        (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hQ)
        (hpair 1 0 (by decide))
  have hunique0 : ∀ w ∈ F, w ∈ N 0 → w = v 0 :=
    Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
      G F N v hv hpair hmin 0 hconn0
  have hunique1 : ∀ w ∈ F, w ∈ N 1 → w = v 1 :=
    Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
      G F N v hv hpair hmin 1 hconn1
  exact ⟨by decide, by decide, by decide, hQ, hQF, (hv 0).2, (hv 1).2,
    hunique0, hunique1, ⟨v 2, hv2Q, (hv 2).2⟩⟩

end Workspace.Types.ThroughPathWhenThirdWitnessOnPath
