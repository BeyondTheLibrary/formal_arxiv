import Workspace.ProofLemmas.Thm61OddAddBranch
import Workspace.ProofLemmas.Thm61OddBranchSubdivision
import Workspace.ProofLemmas.TrackSlice

/-!
# Branch bookkeeping for a one-track extension

`Workspace.ProofLemmas.ThetaData.IsThetaBranchExtension Θ z z' H ρ p` says that `H` is `Θ`
with one extra track `p` from `ρ z` to `ρ z'`.  The `K₄` endgame of 6.1 reads off the
branch-vertices of such an `H` from the theta structure of `Θ`
(`Thm101ThetaBranchVerticesAreK4`), which is not available for the `K₃,₃` endgame of claim
(12).  The three lemmas here get the same information straight from the definition:

* `interior_not_branchVertex` — an internal vertex of the new track has degree `2`;
* `end_mem_branchVertices` — an end of the new track has degree `≥ 3` as soon as it has two
  further neighbours in `Θ`;
* `bipartite_of_odd_extension` — the odd-length counterpart of
  `Thm61OddBranchBipartite.bipartite_of_even_extension`: a track of odd length joining two
  vertices of *different* colour again preserves a bipartition.

`reverse_extension` lets the second lemma be used at both ends.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61Claim12RookBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.ThetaData Workspace.ProofLemmas.SubdivisionCounting

variable {m m' : ℕ} {Θ : SimpleGraph (Fin m)} {z z' : Fin m}
  {H : SimpleGraph (Fin m')} {ρ : Fin m → Fin m'} {p : List (Fin m')}

/-- Reading the new track backwards exchanges its two ends. -/
theorem reverse_extension (hext : IsThetaBranchExtension Θ z z' H ρ p) :
    IsThetaBranchExtension Θ z' z H ρ p.reverse := by
  obtain ⟨hρ, hhom, hp, hp2, hint, hcover, hedges⟩ := hext
  refine ⟨hρ, hhom, Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hp, by
    simpa using hp2, ?_, ?_, ?_⟩
  · intro v hv
    rw [Workspace.ProofLemmas.TrackSlice.trackInterior_reverse, List.mem_reverse] at hv
    exact hint v hv
  · intro v
    rcases hcover v with h | h
    · exact Or.inl h
    · exact Or.inr (by
        rw [Workspace.ProofLemmas.TrackSlice.trackInterior_reverse, List.mem_reverse]
        exact h)
  · rw [hedges, trackEdges_reverse]

/-- An internal vertex of the new track has exactly the two track neighbours, so it is not a
branch-vertex of `H`. -/
theorem interior_not_branchVertex (hext : IsThetaBranchExtension Θ z z' H ρ p) :
    ∀ v ∈ trackInterior p, v ∉ branchVertices H := by
  classical
  obtain ⟨hρ, hhom, hp, hp2, hint, hcover, hedges⟩ := hext
  intro v hv hbv
  have hvr : v ∉ Set.range ρ := hint v hv
  obtain ⟨j, hj, hjv⟩ := (mem_trackInterior_iff p v).mp hv
  have hnd : p.Nodup := hp.1.2.1
  have hsub : H.neighborSet v ⊆
      ({p[j]'(by omega), p[j + 2]'(by omega)} : Set (Fin m')) := by
    intro u hu
    have hmem : s(v, u) ∈ H.edgeSet := hu
    rw [hedges] at hmem
    rcases hmem with ⟨e, he, heq⟩ | ⟨i, hi, heq⟩
    · exfalso
      have hvin : v ∈ Sym2.map ρ e := by rw [heq]; exact Sym2.mem_mk_left _ _
      obtain ⟨c, -, hcv⟩ := Sym2.mem_map.mp hvin
      exact hvr ⟨c, hcv⟩
    · rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hidx : j + 1 = i := hnd.getElem_inj_iff.mp (hjv.trans h1)
        right
        rw [h2]
        exact Set.mem_singleton_iff.mpr
          (getElem_eq_of_index_eq p (by omega) _ _)
      · have hidx : j + 1 = i + 1 := hnd.getElem_inj_iff.mp (hjv.trans h1)
        left
        rw [h2]
        exact getElem_eq_of_index_eq p (by omega) _ _
  have hle : (H.neighborSet v).ncard ≤ 2 := by
    refine le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
    refine le_trans (Set.ncard_insert_le _ _) ?_
    simp
  have h3 : 3 ≤ (H.neighborSet v).ncard := hbv
  omega

/-- An end of the new track that has two further neighbours in `Θ` is a branch-vertex of `H`. -/
theorem end_mem_branchVertices (hext : IsThetaBranchExtension Θ z z' H ρ p)
    (hp3 : 3 ≤ p.length) {c d : Fin m} (hcd : c ≠ d)
    (hzc : Θ.Adj z c) (hzd : Θ.Adj z d) :
    ρ z ∈ branchVertices H := by
  classical
  obtain ⟨hρ, hhom, hp, hp2, hint, hcover, hedges⟩ := hext
  have h0 : p[0]'(by omega) = ρ z := track_head hp (by omega)
  have hadj1 : H.Adj (ρ z) (p[1]'(by omega)) := by
    have h := hp.1.2.2 0 (by omega)
    rwa [h0] at h
  have hint1 : p[1]'(by omega) ∈ trackInterior p := by
    have := mem_trackInterior_getElem p 0 (by omega)
    simpa using this
  have hnr : p[1]'(by omega) ∉ Set.range ρ := hint _ hint1
  have hne1 : ρ c ≠ p[1]'(by omega) := fun h => hnr ⟨c, h⟩
  have hne2 : ρ d ≠ p[1]'(by omega) := fun h => hnr ⟨d, h⟩
  have hcard : ({ρ c, ρ d, p[1]'(by omega)} : Set (Fin m')).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨ρ c, ρ d, p[1]'(by omega), fun h => hcd (hρ h), hne1, hne2, rfl⟩
  have hsub : ({ρ c, ρ d, p[1]'(by omega)} : Set (Fin m')) ⊆ H.neighborSet (ρ z) := by
    intro x hx
    rcases hx with rfl | hx
    · exact hhom z c hzc
    rcases hx with rfl | hx
    · exact hhom z d hzd
    · rw [Set.mem_singleton_iff.mp hx]
      exact hadj1
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard] at this
  exact this

/-- The odd-length counterpart of `Thm61OddBranchBipartite.bipartite_of_even_extension`: an
odd branch joining a vertex of colour `0` to a vertex of colour `1` preserves a bipartite
colouring of the host graph. -/
theorem bipartite_of_odd_extension (col : Θ.Coloring (Fin 2))
    (hz : col z = 0) (hz' : col z' = 1)
    (hext : IsThetaBranchExtension Θ z z' H ρ p) (hodd : Odd (trackLength p)) :
    H.IsBipartite := by
  classical
  obtain ⟨hρ, hhom, hp, hplen, hint, hcover, hedges⟩ := hext
  let color : Fin m' → Fin 2 := fun v =>
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
        have hmod : (p.length - 1) % 2 = 1 := by
          have := Nat.odd_iff.mp hodd
          simpa only [trackLength] using this
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

end Workspace.ProofLemmas.Thm61Claim12RookBranch
