import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathCompleteEdgeIndexEquiv
import Workspace.ProofLemmas.RousselRubioParityForm

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-! Helper: a four-vertex list with the prescribed adjacency pattern is an
induced path. -/
namespace ProofAttempts.Thm21Aux

open Workspace.Types.Core Workspace.Types.Core.SPGT

theorem isPathList_four {V : Type*} (H : SimpleGraph V) (w x y z : V)
    (h01 : H.Adj w x) (h12 : H.Adj x y) (h23 : H.Adj y z)
    (h02 : ¬ H.Adj w y) (h03 : ¬ H.Adj w z) (h13 : ¬ H.Adj x z)
    (hnd : ([w, x, y, z] : List V).Nodup) :
    IsPathList H [w, x, y, z] := by
  refine ⟨by simp, hnd, ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  have h02' : ¬ H.Adj y w := fun h => h02 h.symm
  have h03' : ¬ H.Adj z w := fun h => h03 h.symm
  have h13' : ¬ H.Adj z x := fun h => h13 h.symm
  interval_cases i <;> interval_cases j <;>
    simp [h01, h01.symm, h12, h12.symm, h23, h23.symm, h02, h03, h13,
      h02', h03', h13']

end ProofAttempts.Thm21Aux

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_2_1 (G : SimpleGraph V) (hG : Berge G) (X : Set V)
    (hX : AnticonnectedSet G X) (p : List V) (p₁ pn : V)
    (hp : IsPathFrom G p p₁ pn) (hpX : ∀ w ∈ p, w ∉ X)
    (hodd : Odd (pathLength p))
    (hp₁ : VertexComplete G p₁ X) (hpn : VertexComplete G pn X) :
    (∃ u ∈ p, ∃ v ∈ p, EdgeComplete G X u v) ∨
    (5 ≤ pathLength p ∧ ∃ a ∈ X, ∃ b ∈ X, IsLeapForPath G p a b) ∨
    (pathLength p = 3 ∧ ∃ c d : V, SPGT.interior p = [c, d] ∧
      ∃ q : List V, IsAntipathFrom G q c d ∧ Odd (pathLength q) ∧
        ∀ w ∈ SPGT.interior q, w ∈ X) := by
  classical
  have hodd2 : pathLength p % 2 = 1 := Nat.odd_iff.mp hodd
  have hRR := _root_.Workspace.ProofLemmas.RousselRubioParityForm
    G hG X hX p p₁ pn hp hpX hp₁ hpn
  rcases hRR with hpar | hleap | hanti
  · -- §6.1 parity outcome: the complete-edge index count is odd, hence positive
    left
    obtain ⟨-, -, hpos⟩ :=
      _root_.Workspace.ProofLemmas.PathCompleteEdgeIndexEquiv G X p p₁ pn hp
    exact hpos (by omega)
  · -- §6.2 leap outcome
    obtain ⟨-, hge3, a, haX, b, hbX, hlp⟩ := hleap
    by_cases h5 : 5 ≤ pathLength p
    · exact Or.inr (Or.inl ⟨h5, a, haX, b, hbX, hlp⟩)
    · -- the leap lives on a path of length exactly three; convert it to an antipath
      have h3 : pathLength p = 3 := by omega
      have hplen : p.length = 4 := by
        have := _root_.Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hp.1
        omega
      right; right
      clear hodd hodd2 h5 hge3 hX hpX hp₁ hpn hG
      rcases p with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, tl⟩⟩⟩⟩ <;>
        simp only [List.length_cons, List.length_nil] at hplen <;> try omega
      have htl : tl = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst htl
      obtain ⟨hpathlist, -, hab, hnab, ha, hb⟩ := hlp
      -- adjacency data of the leap
      have ha0 := ha 0 (by norm_num)
      have ha1 := ha 1 (by norm_num)
      have ha2 := ha 2 (by norm_num)
      have ha3 := ha 3 (by norm_num)
      have hb0 := hb 0 (by norm_num)
      have hb1 := hb 1 (by norm_num)
      have hb2 := hb 2 (by norm_num)
      have hb3 := hb 3 (by norm_num)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.length_cons,
        List.length_nil] at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      norm_num at ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      -- adjacency data of the path
      have hpadj := hpathlist.2.2
      have hx12 : G.Adj x1 x2 := by
        have := hpadj 1 2 (by norm_num) (by norm_num)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        exact this.mpr (Or.inl trivial)
      have hx02 : ¬ G.Adj x0 x2 := by
        have := hpadj 0 2 (by norm_num) (by norm_num)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        intro h
        rcases this.mp h with h' | h' <;> omega
      have hx13 : ¬ G.Adj x1 x3 := by
        have := hpadj 1 3 (by norm_num) (by norm_num)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        intro h
        rcases this.mp h with h' | h' <;> omega
      have hx1x2 : x1 ≠ x2 := hx12.ne
      -- the four vertices of the antipath are pairwise distinct
      have hx1b : x1 ≠ b := by rintro rfl; exact hx13 hb3
      have hx1a : x1 ≠ a := ha1.ne'
      have hba : b ≠ a := Ne.symm hab
      have hbx2 : b ≠ x2 := hb2.ne
      have hax2 : a ≠ x2 := by rintro rfl; exact hx02 ha0.symm
      -- the antipath `[x1, b, a, x2]`
      have e1 : Gᶜ.Adj x1 b := by
        rw [SimpleGraph.compl_adj]; exact ⟨hx1b, fun h => hb1 h.symm⟩
      have e2 : Gᶜ.Adj b a := by
        rw [SimpleGraph.compl_adj]; exact ⟨hba, fun h => hnab h.symm⟩
      have e3 : Gᶜ.Adj a x2 := by
        rw [SimpleGraph.compl_adj]; exact ⟨hax2, ha2⟩
      have n1 : ¬ Gᶜ.Adj x1 a := by
        rw [SimpleGraph.compl_adj]; rintro ⟨-, h⟩; exact h ha1.symm
      have n2 : ¬ Gᶜ.Adj x1 x2 := by
        rw [SimpleGraph.compl_adj]; rintro ⟨-, h⟩; exact h hx12
      have n3 : ¬ Gᶜ.Adj b x2 := by
        rw [SimpleGraph.compl_adj]; rintro ⟨-, h⟩; exact h hb2
      have hnd : ([x1, b, a, x2] : List V).Nodup := by
        simp [hx1b, hx1a, hx1x2, hba, hbx2, hax2]
      refine ⟨rfl, x1, x2, rfl, [x1, b, a, x2], ⟨?_, rfl, rfl⟩, ?_, ?_⟩
      · exact _root_.ProofAttempts.Thm21Aux.isPathList_four Gᶜ x1 b a x2 e1 e2 e3 n1 n2 n3 hnd
      · exact ⟨1, rfl⟩
      · intro w hw
        simp only [SPGT.interior, List.tail_cons, List.dropLast, List.mem_cons,
          List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact hbX
        · exact haX
  · -- §6.3 antipath outcome: already the frozen third disjunct
    exact Or.inr (Or.inr hanti)

end SPGT

end Workspace.Statements.S02
