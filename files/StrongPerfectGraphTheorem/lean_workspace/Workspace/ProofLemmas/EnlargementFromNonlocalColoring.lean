import Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.SubdivisionCounting

/-! Extending a two-colouring along the added track. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.EnlargementFromNonlocalColoring

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
open Workspace.ProofLemmas.SubdivisionCounting

/-- The old colouring extends precisely when the new track has the parity
prescribed by its ends. This is the colouring check in the paper's assertion
that the enlarged line graph is an appearance. -/
theorem bipartite_of_parity {W Z : Type*} {H : SimpleGraph W} {D : SimpleGraph Z}
    {a b : W} {rho : W → Z} {p : List Z}
    (hext : IsBranchExtension H a b D rho p) (col : H.Coloring Bool)
    (hpar : Even (trackLength p) ↔ col a = col b) : D.IsBipartite := by
  classical
  let color : Z → Bool := fun v =>
    if h : ∃ u, rho u = v then col h.choose
    else if p.idxOf v % 2 = 0 then col a else !(col a)
  have hold : ∀ u, color (rho u) = col u := by
    intro u
    dsimp only [color]
    rw [dif_pos (show ∃ w, rho w = rho u from ⟨u, rfl⟩)]
    congr 1
    exact hext.inj (Exists.choose_spec (show ∃ w, rho w = rho u from ⟨u, rfl⟩))
  have hpath : ∀ i (hi : i < p.length),
      color p[i] = if i % 2 = 0 then col a else !(col a) := by
    intro i hi
    by_cases hr : ∃ u, rho u = p[i]
    · obtain ⟨u, hu⟩ := hr
      have hiends : i = 0 ∨ i = p.length - 1 := by
        by_contra hn
        have hint : p[i] ∈ trackInterior p := by
          apply (mem_trackInterior_iff p _).mpr
          exact ⟨i - 1, by omega, getElem_eq_of_index_eq p (by omega) _ _⟩
        exact hext.newInterior _ hint ⟨u, hu⟩
      rcases hiends with rfl | rfl
      · rw [track_head hext.track (by omega), hold]
        simp
      · have hlast : p[p.length - 1]'hi = rho b := by
          have h := hext.track.2.2
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hi] at h
          exact Option.some.inj h
        rw [hlast, hold]
        change col b = if trackLength p % 2 = 0 then col a else !(col a)
        by_cases he : Even (trackLength p)
        · rw [if_pos (Nat.even_iff.mp he)]
          exact (hpar.mp he).symm
        · rw [if_neg (fun h => he (Nat.even_iff.mpr h))]
          have hn : col a ≠ col b := fun h => he (hpar.mpr h)
          exact (show ∀ x y : Bool, x ≠ y → y = !x by decide) _ _ hn
    · dsimp only [color]
      rw [dif_neg hr, hext.track.1.2.1.idxOf_getElem i hi]
  have hvalid : ∀ u v, D.Adj u v → color u ≠ color v := by
    intro u v huv
    have he : s(u, v) ∈ D.edgeSet := huv
    rw [hext.edges] at he
    rcases he with ⟨e, he, heq⟩ | ⟨i, hi, heq⟩
    · induction e using Sym2.ind with
      | _ x y =>
        have heq' : s(rho x, rho y) = s(u, v) := heq
        rcases Sym2.eq_iff.mp heq' with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · rw [← hx, ← hy, hold, hold]
          exact col.valid he
        · rw [← hx, ← hy, hold, hold]
          exact (col.valid he).symm
    · have hd : (if i % 2 = 0 then col a else !(col a)) ≠
          (if (i + 1) % 2 = 0 then col a else !(col a)) := by
        by_cases h0 : i % 2 = 0
        · rw [if_pos h0, if_neg (by omega)]
          exact (show ∀ x : Bool, x ≠ !x by decide) _
        · rw [if_neg h0, if_pos (by omega)]
          exact ((show ∀ x : Bool, x ≠ !x by decide) _).symm
      rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [hu, hv, hpath i (by omega), hpath (i + 1) hi]
        exact hd
      · rw [hu, hv, hpath i (by omega), hpath (i + 1) hi]
        exact hd.symm
  have c : D.Coloring Bool := SimpleGraph.Coloring.mk color (by
    intro u v huv
    exact hvalid u v huv)
  exact ⟨D.recolorOfEquiv finTwoEquiv.symm c⟩

end Workspace.ProofLemmas.EnlargementFromNonlocalColoring
