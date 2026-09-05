import Workspace.Statements.S15.Thm_15_4
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PrismBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm211CommonNonneighbor

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (21.1, printed p. 131): "Since ... `n ≥ 5`, and `p₁, pₙ` are
both complete to the interior of `Q`, it follows from 15.4 that `Q` has length
2, that is, there exists `x ∈ X` nonadjacent to both `pᵢ₊₁, pᵢ₊₂`." -/
theorem common_nonneighbor {G : SimpleGraph V} (hG : InF6 G)
    {X : Set V} (hX : AnticonnectedSet G X) {p : List V}
    (hp : IsPathList G p) (hlen : 5 ≤ p.length)
    (hpX : ∀ v ∈ p, v ∉ X)
    (hfirst : VertexComplete G p[0] X)
    (hlast : VertexComplete G p[p.length - 1] X)
    {i : ℕ} (hi : 1 ≤ i) (hiend : i + 2 < p.length)
    (hiX : ¬ VertexComplete G p[i] X)
    (hi1X : ¬ VertexComplete G p[i + 1] X) :
    ∃ x ∈ X, ¬ G.Adj x p[i] ∧ ¬ G.Adj x p[i + 1] := by
  classical
  have hni : ∃ x ∈ X, ¬ G.Adj p[i] x := by
    simpa only [VertexComplete, not_forall, exists_prop] using hiX
  have hni1 : ∃ x ∈ X, ¬ G.Adj p[i + 1] x := by
    simpa only [VertexComplete, not_forall, exists_prop] using hi1X
  obtain ⟨q, hq, hqX⟩ := InducedPathExtraction.exists_antipath_interior_in hX
    (hpX _ (List.getElem_mem _)) (hpX _ (List.getElem_mem _)) hni hni1
  have hq' : IsPathFrom Gᶜ q p[i] p[i + 1] := hq
  have hqpos := PathBasics.path_length_pos hq'.1
  have hq0 := PathBasics.getElem_zero_of_head? hq'.2.1 hqpos
  have hqlast := PathBasics.getElem_last_of_getLast? hq'.2.2 hqpos
  have hq3 : 3 ≤ q.length := by
    by_contra h
    have hn : q.length = 1 ∨ q.length = 2 := by omega
    rcases hn with hn | hn
    · have he : p[i] = p[i + 1] := by
        rw [← hq0, ← hqlast]
        simp only [hn, Nat.sub_self]
      exact (PathBasics.path_ne_of_ne_index hp (by omega) (by omega) (by omega)) he
    · have hqadj := PathBasics.path_adj_succ hq'.1 (show 0 + 1 < q.length by omega)
      have hlast1 : q[1]'(by omega) = p[i + 1] := by simpa only [hn] using hqlast
      rw [hq0, hlast1] at hqadj
      exact hqadj.2 (PathBasics.path_adj_succ hp (by omega))
  have hqle : q.length ≤ 3 := by
    by_contra h
    have h154 := Workspace.Statements.S15.SPGT.thm_15_4 G hG p p.length hp rfl
      (i + 1) (by omega) (by omega) q (q.length - 2) (by omega) (by omega)
      (by simpa only [Nat.add_sub_cancel] using hq)
      (fun v hv => ⟨hfirst v (hqX v hv), hlast v (hqX v hv)⟩)
    omega
  obtain ⟨a, x, b, hqeq⟩ := PrismBasics.length_eq_three (show q.length = 3 by omega)
  subst q
  have ha : a = p[i] := by simpa using hq'.2.1
  have hb : b = p[i + 1] := by simpa using hq'.2.2
  have hxX : x ∈ X := hqX x (by simp [SPGT.interior])
  have hax := PathBasics.path_adj_succ hq'.1 (show 0 + 1 < [a, x, b].length by simp)
  have hxb := PathBasics.path_adj_succ hq'.1 (show 1 + 1 < [a, x, b].length by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hax hxb
  refine ⟨x, hxX, ?_, ?_⟩
  · rw [← ha]
    exact fun h => hax.2 h.symm
  · rw [← hb]
    exact hxb.2

end Workspace.ProofLemmas.Thm211CommonNonneighbor
