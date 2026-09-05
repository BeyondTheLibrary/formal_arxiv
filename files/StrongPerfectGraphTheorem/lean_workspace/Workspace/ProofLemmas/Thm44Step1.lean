import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.Thm44Spread
import Workspace.Statements.S02.Thm_2_1

/-!
# Statement (1) of the proof of 4.4

PAPER (printed p. 16): *"(1) If for some `i, j` there is an odd path of length `≥ 5` with ends in
`B_j` and interior in `A_i`, then the theorem holds.*

*For assume there is such a path for `i = j = 1` say.  Let this path, `P₁` say, have vertices
`b₁-p₁-p₂-…-p_n-b₁'`, where `b₁, b₁' ∈ B₁` and `p₁,…,p_n ∈ A₁`.  Let `2 ≤ j ≤ n`.  Then `P₁` is
an odd path of length `≥ 5` between common neighbours of `B_j`, and no internal vertex of it is
`B_j`-complete since `(A,B)` is not loose.  By 2.1, `B_j` contains a leap; so there exist
nonadjacent `b_j, b_j' ∈ B_j` such that `b_j-p₁-p₂-…-p_n-b_j'` is a path.  Hence `(A₁,B_j)` is a
path pair.  Now let `2 ≤ i ≤ m` and `1 ≤ j ≤ n`.  Since `(A,B)` is not loose, `b_j` and `b_j'`
both have neighbours in `A_i`, and so there is a path `P₂` say joining them with interior in
`A_i`; it is odd by 4.3, and so `(A_i,B_j)` is a path pair.  This proves (1)."*

The conclusion *"then the theorem holds"* is, at this point of the argument, the second
alternative of 4.4: every pair `(A_i,B_j)` is a path pair.

The three alternatives of 2.1 are disposed of as the paper implies: alternative 1 (an
`X`-complete edge) is impossible because an edge of a path of length `≥ 5` always has an interior
endpoint and no interior vertex is `B_j`-complete; alternative 3 needs length `3`.  Only the leap
survives, and `b_j-p₁-…-p_n-b_j'` is `a :: P* ++ [b]` for the leap `a, b` — the very same
construction the proof of 2.7 performs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm44Step1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **(1)** *"If for some `i, j` there is an odd path of length `≥ 5` with ends in `B_j` and
interior in `A_i`, then the theorem holds."* -/
theorem step1 {G : SimpleGraph V} (hG : Berge G) {A B : Set V}
    (hAB : IsSkewPartition G A B) (hnl : ¬ IsLooseSkewPartition G A B)
    {A₁ B₁ : Set V} (hA₁ : IsComponent G A A₁) (hB₁ : IsAnticomponent G B B₁)
    {P : List V} {u v : V} (hu : u ∈ B₁) (hv : v ∈ B₁)
    (hP : IsPathFrom G P u v) (hPint : ∀ x ∈ SPGT.interior P, x ∈ A₁)
    (hPodd : Odd (pathLength P)) (hPlen : 5 ≤ pathLength P) :
    ∀ A' B' : Set V, IsComponent G A A' → IsAnticomponent G B B' →
      IsPathPair G A B A' B' := by
  have hPlist : IsPathList G P := hP.1
  have hlen6 : 6 ≤ P.length := by
    have h := PathBasics.length_eq_pathLength_add_one hPlist
    omega
  have h0 : P[0]'(by omega) = u := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hlast : P[P.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  -- the two ends of a path of length `≥ 2` are nonadjacent
  have hnadjuv : ¬ G.Adj u v := by
    rw [← h0, ← hlast]
    exact PathBasics.path_ends_not_adj hPlist (by omega)
  -- *"no internal vertex of it is `B_j`-complete since `(A,B)` is not loose"*
  have hnotcomp : ∀ x ∈ SPGT.interior P, ∀ B'' : Set V, IsAnticomponent G B B'' →
      ¬ VertexComplete G x B'' := by
    intro x hx B'' hB'' hc
    exact hnl ⟨hAB, Or.inr ⟨x, hA₁.1 (hPint x hx), B'', hB'', hc⟩⟩
  -- For each anticomponent `B'` of `B`: two nonadjacent vertices of `B'` joined by an odd path
  -- with interior in `A`.
  have seed : ∀ B' : Set V, IsAnticomponent G B B' →
      ∃ (u' v' : V) (Q : List V), u' ∈ B' ∧ v' ∈ B' ∧ ¬ G.Adj u' v' ∧
        IsPathFrom G Q u' v' ∧ (∀ x ∈ SPGT.interior Q, x ∈ A) ∧ Odd (pathLength Q) := by
    intro B' hB'
    by_cases hBB : B' = B₁
    · subst hBB
      exact ⟨u, v, P, hu, hv, hnadjuv, hP, fun x hx => hA₁.1 (hPint x hx), hPodd⟩
    have hdisj : Disjoint B₁ B' :=
      ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hB₁ hB' (fun he => hBB he.symm)
    have huB' : u ∉ B' := Set.disjoint_left.mp hdisj hu
    have hvB' : v ∉ B' := Set.disjoint_left.mp hdisj hv
    have hPB' : ∀ w ∈ P, w ∉ B' := by
      intro w hw
      by_cases hwu : w = u
      · exact hwu ▸ huB'
      by_cases hwv : w = v
      · exact hwv ▸ hvB'
      · have hwi : w ∈ SPGT.interior P :=
          (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, hwu, hwv⟩
        exact fun h =>
          (Set.disjoint_left.mp hAB.2.1) (hA₁.1 (hPint w hwi)) (hB'.1 h)
    -- *"`P₁` is an odd path of length `≥ 5` between common neighbours of `B_j`"*
    have hucomp : VertexComplete G u B' :=
      LooseSkewPartition.vertexComplete_of_notMem_anticomponent hB' (hB₁.1 hu) huB'
    have hvcomp : VertexComplete G v B' :=
      LooseSkewPartition.vertexComplete_of_notMem_anticomponent hB' (hB₁.1 hv) hvB'
    -- *"By 2.1, `B_j` contains a leap"*
    rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG B' hB'.2.1 P u v hP hPB' hPodd
      hucomp hvcomp with hc1 | hc2 | hc3
    · -- alternative 1: an `B'`-complete edge; one of its ends is interior
      exfalso
      obtain ⟨x, hx, y, hy, hadj, hxc, hyc⟩ := hc1
      have hxend : x = u ∨ x = v := by
        by_contra hcon
        push_neg at hcon
        exact hnotcomp x ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
          ⟨hx, hcon.1, hcon.2⟩) B' hB' hxc
      have hyend : y = u ∨ y = v := by
        by_contra hcon
        push_neg at hcon
        exact hnotcomp y ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
          ⟨hy, hcon.1, hcon.2⟩) B' hB' hyc
      rcases hxend with rfl | rfl
      · rcases hyend with rfl | rfl
        · exact G.irrefl hadj
        · exact hnadjuv hadj
      · rcases hyend with rfl | rfl
        · exact hnadjuv hadj.symm
        · exact G.irrefl hadj
    · -- alternative 2: the leap `a, b ∈ B'`; `a-p₁-⋯-p_n-b` is the required path
      obtain ⟨-, a, haB', b, hbB', hleap⟩ := hc2
      obtain ⟨-, -, hab, hnab, hAd, hBd⟩ := hleap
      have hIP : IsPathFrom G (SPGT.interior P)
          (P[1]'(by omega)) (P[P.length - 2]'(by omega)) :=
        PathGlue.isPathFrom_interior hPlist (by omega)
      have hsu : G.Adj a (P[1]'(by omega)) := (hAd 1 (by omega)).mpr (Or.inr (Or.inl rfl))
      have htv : G.Adj b (P[P.length - 2]'(by omega)) :=
        (hBd (P.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
      have haP : a ∉ SPGT.interior P := fun h => hPB' a (PathBasics.interior_subset h) haB'
      have hbP : b ∉ SPGT.interior P := fun h => hPB' b (PathBasics.interior_subset h) hbB'
      have hsother : ∀ x ∈ SPGT.interior P, x ≠ (P[1]'(by omega)) → ¬ G.Adj a x := by
        intro x hx hxne
        obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hPlist hx
        intro hadj
        have hc := (hAd k hk).mp hadj
        have hkne : k ≠ 1 := by intro h; exact hxne (by subst h; rfl)
        omega
      have htother : ∀ x ∈ SPGT.interior P, x ≠ (P[P.length - 2]'(by omega)) →
          ¬ G.Adj b x := by
        intro x hx hxne
        obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hPlist hx
        intro hadj
        have hc := (hBd k hk).mp hadj
        have hkne : k ≠ P.length - 2 := by intro h; exact hxne (by subst h; rfl)
        omega
      have hW : IsPathFrom G (a :: (SPGT.interior P ++ [b])) a b :=
        PathAttach.isPathFrom_cons_concat hIP hsu htv hnab hab haP hbP hsother htother
      have hWlen : pathLength (a :: (SPGT.interior P ++ [b])) = pathLength P := by
        rw [PathAttach.pathLength_cons_append_singleton, PathBasics.interior_length]
        simp only [pathLength]
        omega
      have hWint : SPGT.interior (a :: (SPGT.interior P ++ [b])) = SPGT.interior P := by
        simp [SPGT.interior]
      refine ⟨a, b, _, haB', hbB', hnab, hW, ?_, ?_⟩
      · intro x hx
        rw [hWint] at hx
        exact hA₁.1 (hPint x hx)
      · rw [hWlen]; exact hPodd
    · -- alternative 3: length `3`, contradicting `≥ 5`
      exfalso
      omega
  -- *"Now let `2 ≤ i ≤ m` and `1 ≤ j ≤ n` … and so `(A_i,B_j)` is a path pair."*
  intro A' B' hA' hB'
  obtain ⟨u', v', Q, hu', hv', hnadj', hQ, hQint, hQodd⟩ := seed B' hB'
  obtain ⟨R, hR, hRint, hRodd⟩ :=
    Thm44Spread.spread hG hAB hnl (hB'.1 hu') (hB'.1 hv') hQ hQint hQodd hA'
  exact ⟨hAB, hA', hB', R, u', v', hu', hv', hnadj', hR, hRint, hRodd⟩

end Workspace.ProofLemmas.Thm44Step1
