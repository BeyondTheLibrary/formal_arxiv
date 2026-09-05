import Workspace.ProofLemmas.Thm61OddAddBranch

/-! The parity check for the new branch in 6.1(7). -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm61OddBranchBipartite
open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.ThetaData Workspace.ProofLemmas.SubdivisionCounting

/-- Paper, 6.1(7): "there is a `J`-enlargement that appears in the complement
of `G`." An even branch joining two vertices of colour zero preserves a
bipartite colouring of the host graph. -/
theorem bipartite_of_even_extension {m n : ℕ} (D : SimpleGraph (Fin m))
    (z z' : Fin m) (col : D.Coloring (Fin 2)) (hz : col z = 0) (hz' : col z' = 0)
    (H : SimpleGraph (Fin n)) (ρ : Fin m → Fin n) (p : List (Fin n))
    (hext : IsThetaBranchExtension D z z' H ρ p) (heven : Even (trackLength p)) :
    H.IsBipartite := by
  classical
  obtain ⟨hρ, hhom, hp, hplen, hint, hcover, hedges⟩ := hext
  let color : Fin n → Fin 2 := fun v =>
    if h : ∃ u, ρ u = v then col h.choose else ⟨p.idxOf v % 2, Nat.mod_lt _ (by decide)⟩
  have hold : ∀ u, color (ρ u) = col u := by
    intro u
    dsimp only [color]
    rw [dif_pos (show ∃ w, ρ w = ρ u from ⟨u, rfl⟩)]
    congr 1
    exact hρ (Exists.choose_spec (show ∃ w, ρ w = ρ u from ⟨u, rfl⟩))
  have hlast : p[p.length - 1]'(by omega) = ρ z' := by
    have h := hp.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  have hpath : ∀ (i : ℕ) (hi : i < p.length),
      color p[i] = (⟨i % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) := by
    intro i hi
    by_cases hr : ∃ u, ρ u = p[i]
    · obtain ⟨u, hu⟩ := hr
      have hiends : i = 0 ∨ i = p.length - 1 := by
        by_contra h
        have hi0 : 0 < i := by omega
        have hiL : i + 1 < p.length := by omega
        have hiI : p[i] ∈ trackInterior p := by
          apply (mem_trackInterior_iff p _).mpr
          refine ⟨i - 1, by omega, ?_⟩
          exact getElem_eq_of_index_eq p (by omega) _ _
        exact hint _ hiI ⟨u, hu⟩
      rcases hiends with rfl | rfl
      · rw [track_head hp (by omega), hold, hz]
        rfl
      · rw [hlast, hold, hz']
        apply Fin.ext
        have hmod : (p.length - 1) % 2 = 0 := Nat.even_iff.mp heven
        exact hmod.symm
    · dsimp only [color]
      rw [dif_neg hr, hp.1.2.1.idxOf_getElem i hi]
  refine ⟨SimpleGraph.Coloring.mk color ?_⟩
  intro u v huv
  have he : s(u, v) ∈ H.edgeSet := huv
  rw [hedges] at he
  rcases he with ⟨e, he, heq⟩ | ⟨i, hi, heq⟩
  · induction e using Sym2.ind with
    | _ a b =>
      have heq' : s(ρ a, ρ b) = s(u, v) := heq
      rcases Sym2.eq_iff.mp heq' with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [← ha, ← hb, hold, hold]; exact col.valid he
      · rw [← ha, ← hb, hold, hold]; exact (col.valid he).symm
  · rcases Sym2.eq_iff.mp heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [hu, hv, hpath i (by omega), hpath (i + 1) hi]
      intro h
      have hm := congrArg Fin.val h
      dsimp only at hm
      omega
    · rw [hu, hv, hpath i (by omega), hpath (i + 1) hi]
      intro h
      have hm := congrArg Fin.val h
      dsimp only at hm
      omega

end Workspace.ProofLemmas.Thm61OddBranchBipartite
