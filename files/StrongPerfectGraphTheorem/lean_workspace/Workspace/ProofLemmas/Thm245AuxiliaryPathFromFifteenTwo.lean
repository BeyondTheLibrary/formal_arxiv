import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Statements.S15.Thm_15_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction

set_option autoImplicit false

namespace Workspace.Types.Thm245AuxiliaryPathFromFifteenTwo

open Workspace.Types.Core.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions.SPGT

theorem thm245AuxiliaryPathFromFifteenTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF6 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (X : Set V) (hX : X.Nonempty)
    (p : List V) (p₁ pₙ z : V)
    (hp : IsPathList G p) (hn : 2 ≤ p.length)
    (hpX : ∀ w ∈ p, w ∉ X)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hzX : z ∉ X) (hzp : z ∉ p)
    (hzcomp : VertexComplete G z X) (hzp₁ : ¬ G.Adj z p₁) :
    ∃ (Q : List V) (q : V),
      IsPathFrom G Q z p₁ ∧
      Q.tail.head? = some q ∧ 3 ≤ Q.length ∧
      q ∈ interior Q ∧ G.Adj z q ∧
      q ∉ X ∧ ¬ VertexComplete G q X ∧
      (∀ v ∈ interior Q, v ∉ X ∧ ¬ VertexComplete G v X) ∧
      ((∃ w ∈ p, G.Adj z w) → ∀ v ∈ Q, v = z ∨ v ∈ p) := by
  have hp₁mem : p₁ ∈ p :=
    Workspace.ProofLemmas.PathBasics.head_mem hhead
  have hpₙmem : pₙ ∈ p :=
    Workspace.ProofLemmas.PathBasics.getLast_mem hlast
  have hpos : 0 < p.length := by omega
  have hp₁val : p[0]'hpos = p₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hhead hpos
  have hpₙval : p[p.length - 1]'(by omega) = pₙ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlast hpos
  have hp₁pₙ : p₁ ≠ pₙ := by
    intro heq
    have hne := Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hp hpos
      (show p.length - 1 < p.length by omega) (show (0 : Nat) ≠ p.length - 1 by omega)
    apply hne
    rw [hp₁val, hpₙval, heq]
  have hpₙnotcomp : ¬ VertexComplete G pₙ X := by
    intro hc
    exact hp₁pₙ ((hXuniq pₙ hpₙmem).mp hc).symm
  have hzp₁ne : z ≠ p₁ := by
    intro heq
    apply hzp
    rw [heq]
    exact hp₁mem
  by_cases hsees : ∃ w ∈ p, G.Adj z w
  · obtain ⟨a, hap, hza⟩ := hsees
    have hpconn : ConnectedSet G {w : V | w ∈ p} :=
      Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp
    have huconn : ConnectedSet G ({w : V | w ∈ p} ∪ {z}) :=
      Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
        hpconn ⟨a, hap, hza⟩
    obtain ⟨Q, hQ, hQmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
        huconn (Or.inr rfl) (Or.inl hp₁mem)
    have hQlen : 3 ≤ Q.length :=
      Workspace.ProofLemmas.MinimalConnectedIsPath.three_le_length_of_not_adj
        hQ hzp₁ne hzp₁
    let q : V := Q[1]'(by omega)
    have hqint : q ∈ interior Q :=
      Workspace.ProofLemmas.PathBasics.getElem_mem_interior hQ.1 (by omega) (by omega) (by omega)
    have hinterP : ∀ v ∈ interior Q, v ∈ p := by
      intro v hv
      rcases hQmem v (Workspace.ProofLemmas.PathBasics.interior_subset hv) with hvp | hvz
      · exact hvp
      · have hvne := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).mp hv
        exact False.elim (hvne.2.1 (by simpa using hvz))
    have hinterGood : ∀ v ∈ interior Q, v ∉ X ∧ ¬ VertexComplete G v X := by
      intro v hv
      have hvp := hinterP v hv
      refine ⟨hpX v hvp, ?_⟩
      intro hc
      have hvp₁ := (hXuniq v hvp).mp hc
      exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).mp hv |>.2.2 hvp₁
    have hzq : G.Adj z q := by
      have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hQ.1
        (show 0 + 1 < Q.length by omega)
      have hzero : Q[0]'(by omega) = z :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
      simpa [q, hzero] using hadj
    refine ⟨Q, q, hQ, ?_, hQlen, hqint, hzq,
      (hinterGood q hqint).1, (hinterGood q hqint).2, hinterGood, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega)]
      congr 1
      simp [q, List.getElem_tail]
    · intro _ v hv
      rcases hQmem v hv with hvp | hvz
      · exact Or.inr hvp
      · exact Or.inl (by simpa using hvz)
  · let C : Set V := {w : V | VertexComplete G w X}
    have hzC : z ∈ C := hzcomp
    have hp₁C : p₁ ∈ C := (hXuniq p₁ hp₁mem).mpr rfl
    have hCX : Disjoint C X := by
      refine Set.disjoint_left.mpr ?_
      intro c hcC hcX
      exact G.irrefl (hcC c hcX)
    have hCcomplete : Complete G C X := by
      intro c hcC x hx
      exact hcC x hx
    have hCne : C.Nonempty := ⟨z, hzC⟩
    have hCnt : C.Nontrivial := ⟨z, hzC, p₁, hp₁C, hzp₁ne⟩
    have hnotuniv : C ∪ X ≠ Set.univ := by
      intro heq
      have hmem : pₙ ∈ C ∪ X := by rw [heq]; exact Set.mem_univ pₙ
      rcases hmem with hpₙC | hpₙX
      · exact hpₙnotcomp hpₙC
      · exact hpX pₙ hpₙmem hpₙX
    have h152 := _root_.Workspace.Statements.S15.SPGT.thm_15_2
      G hG hbsp C X hCne hX hCX hCcomplete
    obtain ⟨hconn, hattach⟩ := h152.2 hnotuniv
    have hzatt : ∃ a ∈ (C ∪ X)ᶜ, G.Adj z a := hattach hCnt z hzC
    have hp₁att : ∃ a ∈ (C ∪ X)ᶜ, G.Adj p₁ a := hattach hCnt p₁ hp₁C
    have hzout : z ∉ (C ∪ X)ᶜ := by
      intro hzout
      exact hzout (Or.inl hzC)
    have hp₁out : p₁ ∉ (C ∪ X)ᶜ := by
      intro hp₁out
      exact hp₁out (Or.inl hp₁C)
    obtain ⟨Q, hQ, hQint⟩ :=
      Workspace.ProofLemmas.PathInteriorIn.exists_path_interior_in
        hconn hzout hp₁out hzatt hp₁att
    have hQlen : 3 ≤ Q.length :=
      Workspace.ProofLemmas.MinimalConnectedIsPath.three_le_length_of_not_adj
        hQ hzp₁ne hzp₁
    let q : V := Q[1]'(by omega)
    have hqint : q ∈ interior Q :=
      Workspace.ProofLemmas.PathBasics.getElem_mem_interior hQ.1 (by omega) (by omega) (by omega)
    have hinterGood : ∀ v ∈ interior Q, v ∉ X ∧ ¬ VertexComplete G v X := by
      intro v hv
      have hvout := hQint v hv
      refine ⟨?_, ?_⟩
      · intro hvX
        exact hvout (Or.inr hvX)
      · intro hvc
        exact hvout (Or.inl hvc)
    have hzq : G.Adj z q := by
      have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hQ.1
        (show 0 + 1 < Q.length by omega)
      have hzero : Q[0]'(by omega) = z :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
      simpa [q, hzero] using hadj
    refine ⟨Q, q, hQ, ?_, hQlen, hqint, hzq,
      (hinterGood q hqint).1, (hinterGood q hqint).2, hinterGood, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega)]
      congr 1
      simp [q, List.getElem_tail]
    · intro hs
      exact False.elim (hsees hs)

end Workspace.Types.Thm245AuxiliaryPathFromFifteenTwo
