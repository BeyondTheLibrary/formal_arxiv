import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.Statements.S13.Thm_13_6

/-!
# The length-two instance of 13.6 used twice in 21.2(5)

PAPER (21.2(5), printed p. 133): *"Then the path `z-x_t-R-r` is odd, and its ends are
`X_{t−1}`-complete, and its internal vertices are not, so by 13.6, it has length 3, that is,
`R` has length 2.  Let `q` be the middle vertex of `R`.  By 13.6 there is an odd antipath `Q`
joining `q, x_t` with interior in `X_{t−1}`."*

The proof of 21.2(5) runs this step twice: once for the path `R` it is given, and once for
the path `x_t-p_{m−1}-p_m`, which is what justifies the printed remark *"and in particular
`x_t` is nonadjacent to `p_m, p_{m−1}`"*.  This file isolates the step, with the four vertices
of the printed path `z-x_t-q-r` named `z, a, b, c`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm212Claim5Antipath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- 13.6 applied to the four-vertex path `z-a-b-c`, whose ends are `X`-complete and whose two
internal vertices are not: it produces the odd antipath between the two internal vertices
`a, b`, with interior in `X`.  Its length is at least `3` because `a` and `b` are adjacent. -/
theorem exists_odd_antipath {G : SimpleGraph V} (hG : InF5 G) {X : Set V}
    (hX : AnticonnectedSet G X) {z a b c : V}
    (hza : G.Adj z a) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hac : ¬ G.Adj a c) (hzb : ¬ G.Adj z b) (hzc : ¬ G.Adj z c)
    (hzbne : z ≠ b) (hzcne : z ≠ c) (hacne : a ≠ c)
    (hzX : VertexComplete G z X) (hcX : VertexComplete G c X)
    (haX : ¬ VertexComplete G a X) (hbX : ¬ VertexComplete G b X)
    (hzmem : z ∉ X) (hamem : a ∉ X) (hbmem : b ∉ X) (hcmem : c ∉ X) :
    ∃ Q : List V, IsAntipathFrom G Q a b ∧ Odd (pathLength Q) ∧ 3 ≤ pathLength Q ∧
      ∀ u ∈ SPGT.interior Q, u ∈ X := by
  classical
  have hzane : z ≠ a := hza.ne
  have habne : a ≠ b := hab.ne
  have hbcne : b ≠ c := hbc.ne
  have hP1 : IsPathFrom G [c] c c := ⟨PathBasics.isPathList_singleton G c, rfl, rfl⟩
  have hP2 : IsPathFrom G [b, c] b c := by
    refine PathAttach.isPathFrom_cons hP1 hbc (by simp [hbcne]) ?_
    intro w hw hwc
    simp only [List.mem_singleton] at hw
    exact absurd hw hwc
  have hP3 : IsPathFrom G [a, b, c] a c := by
    refine PathAttach.isPathFrom_cons hP2 hab (by simp [habne, hacne]) ?_
    intro w hw hwb
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact absurd rfl hwb
    · exact hac
  have hP4 : IsPathFrom G [z, a, b, c] z c := by
    refine PathAttach.isPathFrom_cons hP3 hza (by simp [hzane, hzbne, hzcne]) ?_
    intro w hw hwa
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact absurd rfl hwa
    · exact hzb
    · exact hzc
  have hodd : Odd (pathLength ([z, a, b, c] : List V)) := ⟨1, rfl⟩
  have hXP : X ⊆ {v : V | v ∈ ([z, a, b, c] : List V)}ᶜ := by
    intro u hu hmem
    simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hzmem hu
    · exact hamem hu
    · exact hbmem hu
    · exact hcmem hu
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG [z, a, b, c] z c hP4 hodd X hXP hX
      hzX hcX with ⟨u, hu, v, hv, hedge⟩ | ⟨h3, cc, dd, hcd, Q, hQ, hQodd, hQint⟩
  · exfalso
    have hcomp : ∀ w ∈ ([z, a, b, c] : List V), VertexComplete G w X → w = z ∨ w = c := by
      intro w hw hwc
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hwc haX
      · exact absurd hwc hbX
      · exact Or.inr rfl
    rcases hcomp u hu hedge.2.1 with he | he <;> rcases hcomp v hv hedge.2.2 with he' | he'
    · exact G.irrefl (he ▸ he' ▸ hedge.1)
    · exact hzc (he ▸ he' ▸ hedge.1)
    · exact hzc (he ▸ he' ▸ hedge.1).symm
    · exact G.irrefl (he ▸ he' ▸ hedge.1)
  · have hint : SPGT.interior ([z, a, b, c] : List V) = [a, b] := rfl
    rw [hint] at hcd
    have hca : cc = a := by injection hcd with h1 h2; exact h1.symm
    have hdb : dd = b := by
      injection hcd with h1 h2; injection h2 with h3 h4; exact h3.symm
    rw [hca, hdb] at hQ
    refine ⟨Q, hQ, hQodd, ?_, hQint⟩
    have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
    by_contra hcon
    have hQ2 : Q.length = 2 := by
      obtain ⟨dd', hdd'⟩ := hQodd
      have := PathBasics.pathLength_eq Q
      omega
    have hd0 : Q[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
    have hd1 : Q[1]'(by omega) = b := by
      have hh := PathBasics.getElem_last_of_getLast? hQ.2.2 (show 0 < Q.length by omega)
      rw [HoleArithmetic.getElem_congr_idx Q (show 1 < Q.length by omega)
        (show Q.length - 1 < Q.length by omega) (by omega)]
      exact hh
    have hadjc := PathBasics.path_adj_succ hQ.1 (i := 0) (by omega)
    rw [hd0, HoleArithmetic.getElem_congr_idx Q (show 0 + 1 < Q.length by omega)
      (show 1 < Q.length by omega) rfl, hd1] at hadjc
    exact (SimpleGraph.compl_adj .. |>.mp hadjc).2 hab

end Workspace.ProofLemmas.Thm212Claim5Antipath
