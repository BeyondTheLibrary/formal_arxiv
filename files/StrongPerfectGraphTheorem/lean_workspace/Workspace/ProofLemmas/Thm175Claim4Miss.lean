import Workspace.ProofLemmas.Thm175Claim4Setup
import Workspace.ProofLemmas.Thm175Symmetry

/-! The application of 17.4 shared by claims (4) and (5) of 17.5. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Miss

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup
open Workspace.ProofLemmas.Thm175Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- PAPER: "By 17.4 (with `X` and `Y` exchanged), `p₂` is nonadjacent to
`y_{t₀}`."  Apply 17.4 to the reversed original path and to the reversed
antipath `x_s-y₁-⋯-y_{t₀}-p₁`. -/
theorem second_misses (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (h1 : 1 < c.core.p.length) :
    ¬ G.Adj (c.core.p[1]'h1) (s.qY[s.t₀]'s.ht₀) := by
  have hs := s.hXlong
  have ht := s.ht₀
  let xs : V := s.qX[s.qX.length - 1]'(by omega)
  let R : List V := xs :: (s.qY.take (s.t₀ + 1) ++ [c.core.p₁])
  have hdropX : s.qX.drop (s.qX.length - 1) = [xs] := by
    rw [List.drop_eq_getElem?_toList_append, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some]
    rw [show s.qX.length - 1 + 1 = s.qX.length by omega, List.drop_length]
    rfl
  have hdrop : (antiPrefix s ++ [c.core.p₁]).drop (s.qX.length - 1) = R := by
    change ((s.qX ++ s.qY.take (s.t₀ + 1)) ++ [c.core.p₁]).drop
      (s.qX.length - 1) = R
    rw [List.append_assoc, List.drop_append_of_le_length (by omega), hdropX]
    rfl
  have hRpath : IsPathList Gᶜ R := by
    rw [← hdrop]
    apply PathBasics.isPathList_drop (first_miss_antipath s).1
    simp only [antiPrefix, List.length_append, List.length_singleton, List.length_take]
    omega
  have hR : IsAntipathFrom G R xs c.core.p₁ := by
    refine ⟨hRpath, rfl, ?_⟩
    change (xs :: (s.qY.take (s.t₀ + 1) ++ [c.core.p₁])).getLast? = _
    rw [List.getLast?_cons_of_ne_nil (by simp),
      List.getLast?_append_of_ne_nil _ (by simp)]
    rfl
  have hint : SPGT.interior R = s.qY.take (s.t₀ + 1) := by
    simp [R, SPGT.interior]
  have hQ := PathBasics.isPathFrom_reverse hR
  have hQint : ∀ v ∈ SPGT.interior R.reverse, v ∈ c.Y := by
    intro v hv
    rw [PathBasics.interior_reverse, List.mem_reverse, hint] at hv
    exact (s.hYverts v).mp (List.take_subset _ _ hv)
  have hQhead : (SPGT.interior R.reverse).head? = some (s.qY[s.t₀]'s.ht₀) := by
    rw [PathBasics.interior_reverse, List.head?_reverse, hint, List.getLast?_take]
    simp [List.getElem?_eq_getElem s.ht₀]
  let cs := swapCounterexample G z c hfirst
  have hlast1 : cs.core.p.dropLast.getLast? = some (c.core.p[1]'h1) := by
    change c.core.p.reverse.dropLast.getLast? = _
    rw [List.dropLast_reverse, List.getLast?_reverse, ← List.drop_one,
      List.head?_drop, List.getElem?_eq_getElem h1]
  have hpnNotY : ¬ VertexComplete G c.core.p₁ c.Y := by
    intro hc
    have he := (c.core.hYuniq c.core.p₁ (PathBasics.head_mem c.core.hp.2.1)).mp hc
    exact (PathBasics.isPathFrom_ends_ne c.core.hp (Nat.le_of_lt c.core.hlong)) he
  exact _root_.Workspace.Statements.S17.SPGT.thm_17_4 G hG
    cs.core.p cs.core.p₁ (c.core.p[1]'h1) cs.core.pₙ cs.core.hp.1 cs.core.hlong
    cs.core.hp.2.1 cs.core.hp.2.2 hlast1 cs.X cs.Y cs.core.houtX cs.core.houtY
    cs.hXa cs.hYa cs.hXYa cs.core.hp₁X cs.core.hYuniq z cs.hz cs.core.hzP
    cs.hzXY cs.core.hzanti hpnNotY xs (s.qY[s.t₀]'s.ht₀)
    ((s.hXverts xs).mp (List.getElem_mem (by omega))) R.reverse hQ hQint hQhead

end Workspace.ProofLemmas.Thm175Claim4Miss
