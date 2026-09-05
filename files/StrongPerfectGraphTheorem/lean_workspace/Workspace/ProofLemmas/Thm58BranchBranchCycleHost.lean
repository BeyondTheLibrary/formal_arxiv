import Workspace.ProofLemmas.Thm58BranchBranchBasics
import Workspace.ProofLemmas.Connectivity58CycleBuild
import Workspace.ProofLemmas.Connectivity58CycleAvoid
import Workspace.ProofLemmas.Connectivity58Cycle
import Workspace.ProofLemmas.Thm58BranchBranchThirdTrack
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.CyclicThreeConnectedAttachments
import Workspace.ProofLemmas.LineGraphDegree
import Workspace.ProofLemmas.LineGraphK4Chords
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.TrackSlice

/-!
# The cycle of 5.8 (7), and the third track leaving it

PAPER (5.8 (7), printed p. 28): *"There is a cycle in `H` using the branch between `u₁` and
`v₁`, and using `u₂` and not `v₂` … and there is a third path `R` say from `p₁` to `N_{u₂}` via
`F` and a subpath of `R_{u₂v₂}`."*

The cycle is built here from the first branch `q₁` and a return track `D` joining the two ends
of `q₁` and meeting `q₁` only there, which `Connectivity58Cycle.exists_return_track` produces
once one end of the second branch `q₂` is known to lie off `q₁`.  The cycle misses that end, so
by `Connectivity58CycleAvoid` it misses the whole interior of `q₂`, and therefore uses no edge
of `q₂` at all.  A track from the cycle to `q₂`, prolonged along `q₂` and cut at the first
attachment of `p₂`, is the third track; `Thm58BranchBranchThirdTrack.exists_third_track_any`
does the prolonging and the cutting.

The cycle is listed starting at `q₁[s]`, so that the edge `q₁[s]q₁[s+1]` is the first edge of
the cycle and the edge `q₁[s-1]q₁[s]` is the last.  The vertex `w` where the third track leaves
the cycle is never an internal vertex of `q₁`, because an internal vertex of a branch has both
its neighbours on the branch; that pins the position of `w` on the cycle past all of
`q₁[s], …, q₁[|q₁| - 2]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm58BranchBranchCycleHost

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm58BranchBranch
open Workspace.ProofLemmas.Thm58BranchBranchCycleRung
open Workspace.ProofLemmas.Connectivity58CycleBuild
open Workspace.ProofLemmas.TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- A branch read backwards is a branch. -/
theorem isBranch_reverse {W : Type*} [DecidableEq W] {H : SimpleGraph W} {q : List W}
    (hq : IsBranch H q) : IsBranch H q.reverse := by
  refine ⟨TrackSlice.isTrackList_reverse hq.1, ?_, ?_⟩
  · intro v hv
    rw [LineGraphK4Chords.trackInterior_reverse, List.mem_reverse] at hv
    exact hq.2.1 v hv
  · intro q' hq' hq'int hsubE hsubV
    rw [SubdivisionCounting.trackEdges_reverse]
    refine hq.2.2 q' hq' hq'int ?_ (fun v hv => hsubV v (List.mem_reverse.mpr hv))
    rwa [SubdivisionCounting.trackEdges_reverse] at hsubE

/-- A vertex of a track is its first vertex, its last vertex, or an internal vertex. -/
theorem mem_track_cases {W : Type*} {q : List W} {z : W} (hz : z ∈ q) (hq : 0 < q.length) :
    z = q[0]'hq ∨ z = q[q.length - 1]'(by omega) ∨ z ∈ trackInterior q := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
  by_cases h0 : i = 0
  · exact Or.inl (by subst h0; rfl)
  by_cases hl : i = q.length - 1
  · exact Or.inr (Or.inl (by subst hl; rfl))
  refine Or.inr (Or.inr ((SubdivisionCounting.mem_trackInterior_iff q _).mpr ⟨i - 1, by omega, ?_⟩))
  exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _


/-- A vertex of the interior of a track is a vertex of the track. -/
theorem mem_of_mem_trackInterior {W : Type*} {q : List W} {x : W}
    (h : x ∈ trackInterior q) : x ∈ q := by
  obtain ⟨t, ht, hxt⟩ := (SubdivisionCounting.mem_trackInterior_iff q x).mp h
  exact hxt ▸ List.getElem_mem _

/-- **The cycle of 5.8 (7) and the third track leaving it**, when the last vertex of the second
branch is known to lie off the first branch. -/
theorem exists_cycle_and_track_aux
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    (hq₂2 : 2 ≤ q₂.length)
    (hclast : q₂[q₂.length - 1]'(by omega) ∉ q₁)
    {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s + 3 ≤ q₁.length) :
    ∃ (D : List (Fin n)) (hcyc : IsCycleList H (cycleFrom q₁ D s)),
      3 ≤ D.length ∧
      (∀ z ∈ q₁, z ∈ cycleFrom q₁ D s) ∧
      (∀ (i : ℕ) (hi : i < (cycleFrom q₁ D s).length),
        cycleEdge (cycleFrom q₁ D s) i hi ∉ trackEdges q₂) ∧
      ∃ (T : List (Fin n)) (hT : IsTrackList H T) (w : Fin n) (pw : ℕ),
        2 ≤ T.length ∧ T.head? = some w ∧
        (∀ z ∈ T, z ∈ cycleFrom q₁ D s → z = w) ∧
        (∃ zl, (trackRung φ T hT).getLast? = some zl ∧
          ∀ z ∈ trackRung φ T hT, (G.Adj p₂ z ↔ z = zl)) ∧
        (cycleFrom q₁ D s)[pw]? = some w ∧ q₁.length - 1 - s ≤ pw := by
  classical
  have hJ : IsKConnected J 3 := h.2.1
  have hsub : IsSubdivision J H := h.2.2.1.1
  have hc3 : CyclicallyThreeConnected H := ⟨m, J, hJ, hsub⟩
  have hdeg2 : ∀ w : Fin n, 2 ≤ (H.neighborSet w).ncard :=
    LineGraphDegree.two_le_degree_of_isSubdivision hJ hsub
  have hq₁2 : 2 ≤ q₁.length := by omega
  have hq₁ne : q₁ ≠ [] := hq₁.1.1
  have hq₂ne : q₂ ≠ [] := hq₂.1.1
  have hq₁from : IsTrackFrom H q₁ (q₁[0]'(by omega)) (q₁[q₁.length - 1]'(by omega)) := by
    refine ⟨hq₁.1, ?_, ?_⟩
    · rw [List.head?_eq_head hq₁ne, List.head_eq_getElem]
    · rw [List.getLast?_eq_getLast hq₁ne, List.getLast_eq_getElem]
  have hq₂from : IsTrackFrom H q₂ (q₂[0]'(by omega)) (q₂[q₂.length - 1]'(by omega)) := by
    refine ⟨hq₂.1, ?_, ?_⟩
    · rw [List.head?_eq_head hq₂ne, List.head_eq_getElem]
    · rw [List.getLast?_eq_getLast hq₂ne, List.getLast_eq_getElem]
  obtain ⟨hbv₁, hbv₂⟩ := Thm75BranchEnds.branchEnds_mem_branchVertices J hJ H hsub q₁ _ _
    hq₁ hq₁from (by simp only [trackLength]; omega)
  obtain ⟨hbc₀, hbc₁⟩ := Thm75BranchEnds.branchEnds_mem_branchVertices J hJ H hsub q₂ _ _
    hq₂ hq₂from (by simp only [trackLength]; omega)
  -- the return track
  obtain ⟨D, hDfrom, hcD, hDq₁, hDedges, z₀, hz₀D, hz₀b, hz₀1, hz₀2⟩ :=
    Connectivity58Cycle.exists_return_track hJ hsub hq₁ hq₁2 hq₁from hbv₁ hbv₂ hbc₁ hclast
  have hDpos : 0 < D.length := List.length_pos_of_ne_nil hDfrom.1.1
  have hD0 := Connectivity58CycleBuild.track_first hDfrom hDpos
  have hDl := Connectivity58CycleBuild.track_last hDfrom hDpos
  have hDnd : D.Nodup := hDfrom.1.2.1
  have hD3 : 3 ≤ D.length := by
    by_contra hcon
    obtain ⟨i, hi, hiz⟩ := List.mem_iff_getElem.mp hz₀D
    have hi2 : i = 0 ∨ i = 1 := by omega
    rcases hi2 with rfl | rfl
    · exact hz₀1 (hiz.symm.trans hD0)
    · refine hz₀2 (hiz.symm.trans ?_)
      rw [SubdivisionCounting.getElem_eq_of_index_eq D (by omega : 1 = D.length - 1) hi
        (by omega), hDl]
  have hdisjDq₁ : ∀ x ∈ trackInterior D, x ∉ q₁ := by
    intro x hx hxq
    obtain ⟨t, ht, hxt⟩ := (SubdivisionCounting.mem_trackInterior_iff D x).mp hx
    have hxD : x ∈ D := hxt ▸ List.getElem_mem _
    rcases hDq₁ x hxD hxq with hh | hh
    · have he : D[t + 1]'(by omega) = D[0]'(by omega) := by rw [hxt, hh, ← hD0]
      have := (List.Nodup.getElem_inj_iff hDnd).mp he
      omega
    · have he : D[t + 1]'(by omega) = D[D.length - 1]'(by omega) := by rw [hxt, hh, ← hDl]
      have := (List.Nodup.getElem_inj_iff hDnd).mp he
      omega
  have hcyc : IsCycleList H (cycleFrom q₁ D s) :=
    isCycleList_cycleFrom hq₁from hDfrom hq₁2 hD3 hdisjDq₁ s
  have hcylen : (cycleFrom q₁ D s).length = q₁.length + (D.length - 2) := cycleFrom_length q₁ D s
  have hq₁cy : ∀ z ∈ q₁, z ∈ cycleFrom q₁ D s := fun z hz => mem_cycleFrom.mpr (Or.inl hz)
  -- the cycle misses the interior of the second branch
  have hint₂q₁ : ∀ x ∈ trackInterior q₂, x ∉ q₁ := by
    intro x hx hxq
    exact branches_ne h hq₁ hX₁ hX₂
      (branch_edges_eq_of_internal hJ hsub hq₂ hq₁ hx hxq).symm
  have hint₂D : ∀ x ∈ trackInterior q₂, x ∉ D := by
    refine Connectivity58CycleAvoid.interior_disjoint_of_last_not_mem hdeg2 hq₂ hq₂2
      hDfrom.1 ?_ hcD
    intro x _ hxend hxint
    have hxb : x ∈ branchVertices H := by
      rcases hxend with hh | hh
      · have : x = q₁[0]'(by omega) := Option.some_injective _ (hh.symm.trans hDfrom.2.1)
        exact this ▸ hbv₁
      · have : x = q₁[q₁.length - 1]'(by omega) :=
          Option.some_injective _ (hh.symm.trans hDfrom.2.2)
        exact this ▸ hbv₂
    exact hq₂.2.1 x hxint hxb
  have hint₂cy : ∀ x ∈ trackInterior q₂, x ∉ cycleFrom q₁ D s := by
    intro x hx hxcy
    rcases mem_cycleFrom.mp hxcy with hh | hh
    · exact hint₂q₁ x hx hh
    · exact hint₂D x hx (mem_of_mem_trackInterior hh)
  have hcnotcy : q₂[q₂.length - 1]'(by omega) ∉ cycleFrom q₁ D s := by
    intro hh
    rcases mem_cycleFrom.mp hh with h1 | h1
    · exact hclast h1
    · exact hcD (mem_of_mem_trackInterior h1)
  have hcy₂ : ∀ z ∈ cycleFrom q₁ D s, z ∈ q₂ → z = q₂[0]'(by omega) := by
    intro z hzcy hzq
    rcases mem_track_cases hzq (by omega) with hh | hh | hh
    · exact hh
    · exact absurd (hh ▸ hzcy) hcnotcy
    · exact absurd hzcy (hint₂cy z hh)
  have hcyq₂ : ∀ (i : ℕ) (hi : i < (cycleFrom q₁ D s).length),
      cycleEdge (cycleFrom q₁ D s) i hi ∉ trackEdges q₂ := by
    intro i hi he
    obtain ⟨l, hl, hle⟩ := he
    rw [cycleEdge_eq _ i hi (nxt_lt hi)] at hle
    have hmem1 : q₂[l]'(by omega) ∈ cycleFrom q₁ D s := by
      have hm : q₂[l]'(by omega) ∈ s((cycleFrom q₁ D s)[i]'hi,
          (cycleFrom q₁ D s)[nxt (cycleFrom q₁ D s) i]'(nxt_lt hi)) := by
        rw [hle]; exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.mp hm with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
    have hmem2 : q₂[l + 1]'hl ∈ cycleFrom q₁ D s := by
      have hm : q₂[l + 1]'hl ∈ s((cycleFrom q₁ D s)[i]'hi,
          (cycleFrom q₁ D s)[nxt (cycleFrom q₁ D s) i]'(nxt_lt hi)) := by
        rw [hle]; exact Sym2.mem_mk_right _ _
      rcases Sym2.mem_iff.mp hm with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
    have e1 := hcy₂ _ hmem1 (List.getElem_mem _)
    have e2 := hcy₂ _ hmem2 (List.getElem_mem _)
    have : l = l + 1 := (List.Nodup.getElem_inj_iff hq₂.1.2.1).mp (e1.trans e2.symm)
    omega
  -- the attachment of `p₂` on the second branch
  obtain ⟨y₂, hy₂K, hy₂adj⟩ := first_end_has_neighbor (ready_reverse h) hq₁ hX₁
  have hPF : {x : V | x ∈ P} = F := h.2.2.2.2.2.2.2.1
  have hPfrom : IsPathFrom G P p₁ p₂ := h.2.2.2.2.2.2.1
  have hp₂F : p₂ ∈ F := by rw [← hPF]; exact PathBasics.getLast_mem hPfrom.2.2
  have hne := ends_ne h
  have hval : (↑(φ (φ.symm ⟨y₂, hy₂K⟩)) : V) = y₂ :=
    congrArg Subtype.val (φ.apply_symm_apply ⟨y₂, hy₂K⟩)
  have hvalK : (↑(φ (φ.symm ⟨y₂, hy₂K⟩)) : V) ∈ K := by rw [hval]; exact hy₂K
  have hvaladj : G.Adj (↑(φ (φ.symm ⟨y₂, hy₂K⟩)) : V) p₂ := by rw [hval]; exact hy₂adj.symm
  have he₂ : (φ.symm ⟨y₂, hy₂K⟩).1 ∈ edgeAttachments φ (F \ {p₁}) :=
    ⟨(φ.symm ⟨y₂, hy₂K⟩).2, hvalK, p₂, ⟨hp₂F, hne.symm⟩, hvaladj⟩
  obtain ⟨l₀, hl₀, hle₀⟩ := hX₂ he₂
  have hex : ∃ (l : ℕ) (hl : l + 1 < q₂.length),
      G.Adj p₂ (↑(φ ⟨s(q₂[l]'(by omega), q₂[l + 1]'hl),
        trackEdge_mem_edgeSet hq₂.1 l hl⟩) : V) := by
    refine ⟨l₀, hl₀, ?_⟩
    have hsub' : (⟨s(q₂[l₀]'(by omega), q₂[l₀ + 1]'hl₀),
        trackEdge_mem_edgeSet hq₂.1 l₀ hl₀⟩ : H.edgeSet) = φ.symm ⟨y₂, hy₂K⟩ :=
      Subtype.ext hle₀.symm
    rw [hsub', hval]; exact hy₂adj
  by_cases hmeet : ∃ z, z ∈ cycleFrom q₁ D s ∧ z ∈ q₂
  · -- the cycle already meets the second branch, at its first vertex
    obtain ⟨z, hzcy, hzq⟩ := hmeet
    have hz0 : z = q₂[0]'(by omega) := hcy₂ z hzcy hzq
    have hwcy : q₂[0]'(by omega) ∈ cycleFrom q₁ D s := hz0 ▸ hzcy
    have hSfrom : IsTrackFrom H [q₂[0]'(by omega)] (q₂[0]'(by omega)) (q₂[0]'(by omega)) := by
      refine ⟨⟨by simp, by simp, ?_⟩, rfl, rfl⟩
      intro i hi; simp at hi
    have hSc : ∀ z' ∈ [q₂[0]'(by omega)], z' ∈ cycleFrom q₁ D s → z' = q₂[0]'(by omega) := by
      intro z' hz' _; simpa using hz'
    have hSq : ∀ z' ∈ [q₂[0]'(by omega)], z' ∈ q₂ → z' = q₂[0]'(by omega) := by
      intro z' hz' _; simpa using hz'
    have hcut : ∀ z' ∈ q₂, z' ∈ cycleFrom q₁ D s → z' ∈ [q₂[0]'(by omega)] := by
      intro z' hz'q hz'cy; simp [hcy₂ z' hz'cy hz'q]
    have hyq : q₂[0]'(by omega) ∈ q₂ := List.getElem_mem _
    have hwnotint : q₂[0]'(by omega) ∉ trackInterior q₁ := by
      intro hh
      exact branches_ne h hq₁ hX₁ hX₂ (branch_edges_eq_of_internal hJ hsub hq₁ hq₂ hh hyq)
    obtain ⟨T, hT, hT2, hThead, hTcy, hTattach⟩ :=
      Thm58BranchBranchThirdTrack.exists_third_track_any φ hq₂.1 hSfrom hSc hSq hcut hyq hex
    obtain ⟨pw, hpwlt, hpweq⟩ := List.mem_iff_getElem.mp hwcy
    refine ⟨D, hcyc, hD3, hq₁cy, hcyq₂, T, hT, _, pw, hT2, hThead, hTcy, hTattach, ?_, ?_⟩
    · rw [List.getElem?_eq_getElem hpwlt, hpweq]
    · by_contra hcon
      have hpw' : pw < q₁.length - 1 - s := by omega
      have hget : (cycleFrom q₁ D s)[pw]'hpwlt = q₁[s + pw]'(by omega) :=
        cycleFrom_getElem_branch q₁ D s pw (by omega) hpwlt
      apply hwnotint
      rw [← hpweq, hget]
      refine (SubdivisionCounting.mem_trackInterior_iff q₁ _).mpr ⟨s + pw - 1, by omega, ?_⟩
      exact SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _
  · -- the cycle is disjoint from the second branch: connect them
    push_neg at hmeet
    have hcypos : 0 < (cycleFrom q₁ D s).length := by omega
    have hcy0q₂ : (cycleFrom q₁ D s)[0]'hcypos ≠ q₂[0]'(by omega) := by
      intro hh; exact hmeet _ (List.getElem_mem _) (by rw [hh]; exact List.getElem_mem _)
    obtain ⟨walk⟩ := CyclicThreeConnectedAttachments.preconnected_of_cyclicallyThreeConnected hc3
      ((cycleFrom q₁ D s)[0]'hcypos) (q₂[0]'(by omega))
    obtain ⟨R, hR, -, -⟩ := NoCrossTrackBranch.exists_track_of_walk walk
    have hRpos : 0 < R.length := List.length_pos_of_ne_nil hR.1.1
    have hR0 := Connectivity58CycleBuild.track_first hR hRpos
    have hRl := Connectivity58CycleBuild.track_last hR hRpos
    have hR2 : 2 ≤ R.length := by
      by_contra hcc
      apply hcy0q₂
      rw [← hR0, ← hRl]
      exact SubdivisionCounting.getElem_eq_of_index_eq R (by omega) _ _
    obtain ⟨S, a, b, hSfrom, haA, hbB, hS2, hSint, hSR⟩ :=
      TrackSlice.exists_clean_subtrack hR.1 (A := {z : Fin n | z ∈ cycleFrom q₁ D s})
        (B := {z : Fin n | z ∈ q₂}) (i₀ := 0) (j₀ := R.length - 1) (by omega) (by omega)
        (by rw [hR0]; exact List.getElem_mem _) (by rw [hRl]; exact List.getElem_mem _)
    have hacy : a ∈ cycleFrom q₁ D s := haA
    have hbq : b ∈ q₂ := hbB
    have hS0 : S[0]'(by omega) = a := Connectivity58CycleBuild.track_first hSfrom (by omega)
    have hSl : S[S.length - 1]'(by omega) = b :=
      Connectivity58CycleBuild.track_last hSfrom (by omega)
    have hSc : ∀ z ∈ S, z ∈ cycleFrom q₁ D s → z = a := by
      intro z hz hzcy
      rcases mem_track_cases hz (by omega) with hh | hh | hh
      · rw [hh, hS0]
      · exact absurd (by rw [hh, hSl]; exact hbq) (hmeet z hzcy)
      · exact absurd hzcy ((hSint z hh).1)
    have hSq : ∀ z ∈ S, z ∈ q₂ → z = b := by
      intro z hz hzq
      rcases mem_track_cases hz (by omega) with hh | hh | hh
      · exact absurd hzq (hmeet z (by rw [hh, hS0]; exact hacy))
      · rw [hh, hSl]
      · exact absurd hzq ((hSint z hh).2)
    have hcut : ∀ z ∈ q₂, z ∈ cycleFrom q₁ D s → z ∈ S :=
      fun z hzq hzcy => absurd hzq (hmeet z hzcy)
    obtain ⟨T, hT, hT2, hThead, hTcy, hTattach⟩ :=
      Thm58BranchBranchThirdTrack.exists_third_track_any φ hq₂.1 hSfrom hSc hSq hcut hbq hex
    have hS1cy : S[1]'(by omega) ∉ cycleFrom q₁ D s := by
      intro hh
      have h1 := hSc _ (List.getElem_mem _) hh
      have := (List.Nodup.getElem_inj_iff hSfrom.1.2.1).mp (h1.trans hS0.symm)
      omega
    have hwnotint : a ∉ trackInterior q₁ := by
      intro hh
      obtain ⟨j, hj, hja⟩ := (SubdivisionCounting.mem_trackInterior_iff q₁ a).mp hh
      have hadjS : H.Adj (q₁[j + 1]'(by omega)) (S[1]'(by omega)) := by
        rw [hja, ← hS0]; exact hSfrom.1.2.2 0 (by omega)
      rcases Connectivity58CycleAvoid.nbr_of_branch_interior hdeg2 hq₁ hj hadjS with hcc | hcc
      · exact hS1cy (by rw [hcc]; exact hq₁cy _ (List.getElem_mem _))
      · exact hS1cy (by rw [hcc]; exact hq₁cy _ (List.getElem_mem _))
    obtain ⟨pw, hpwlt, hpweq⟩ := List.mem_iff_getElem.mp hacy
    refine ⟨D, hcyc, hD3, hq₁cy, hcyq₂, T, hT, a, pw, hT2, hThead, hTcy, hTattach, ?_, ?_⟩
    · rw [List.getElem?_eq_getElem hpwlt, hpweq]
    · by_contra hcon
      have hpw' : pw < q₁.length - 1 - s := by omega
      have hget : (cycleFrom q₁ D s)[pw]'hpwlt = q₁[s + pw]'(by omega) :=
        cycleFrom_getElem_branch q₁ D s pw (by omega) hpwlt
      apply hwnotint
      rw [← hpweq, hget]
      refine (SubdivisionCounting.mem_trackInterior_iff q₁ _).mpr ⟨s + pw - 1, by omega, ?_⟩
      exact SubdivisionCounting.getElem_eq_of_index_eq q₁ (by omega) _ _


/-- **The cycle of 5.8 (7) and the third track leaving it.**  The cycle runs along the first
branch `q₁` from `q₁[s]`, and the track `T` leaves it at a vertex `w` sitting past all of
`q₁[s], …, q₁[|q₁| - 2]`, ending at the first attachment of `p₂` on the second branch. -/
theorem exists_cycle_and_track
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {s : ℕ} (hs1 : 1 ≤ s) (hs2 : s + 3 ≤ q₁.length) :
    ∃ (D : List (Fin n)) (hcyc : IsCycleList H (cycleFrom q₁ D s)),
      3 ≤ D.length ∧
      (∀ z ∈ q₁, z ∈ cycleFrom q₁ D s) ∧
      (∀ (i : ℕ) (hi : i < (cycleFrom q₁ D s).length),
        cycleEdge (cycleFrom q₁ D s) i hi ∉ trackEdges q₂) ∧
      ∃ (T : List (Fin n)) (hT : IsTrackList H T) (w : Fin n) (pw : ℕ),
        2 ≤ T.length ∧ T.head? = some w ∧
        (∀ z ∈ T, z ∈ cycleFrom q₁ D s → z = w) ∧
        (∃ zl, (trackRung φ T hT).getLast? = some zl ∧
          ∀ z ∈ trackRung φ T hT, (G.Adj p₂ z ↔ z = zl)) ∧
        (cycleFrom q₁ D s)[pw]? = some w ∧ q₁.length - 1 - s ≤ pw := by
  classical
  have hJ : IsKConnected J 3 := h.2.1
  have hsub : IsSubdivision J H := h.2.2.1.1
  have hq₁2 : 2 ≤ q₁.length := by omega
  -- the second branch carries an attachment of `p₂`, so it has an edge
  obtain ⟨y₂, hy₂K, hy₂adj⟩ := first_end_has_neighbor (ready_reverse h) hq₁ hX₁
  have hPF : {x : V | x ∈ P} = F := h.2.2.2.2.2.2.2.1
  have hPfrom : IsPathFrom G P p₁ p₂ := h.2.2.2.2.2.2.1
  have hp₂F : p₂ ∈ F := by rw [← hPF]; exact PathBasics.getLast_mem hPfrom.2.2
  have hne := ends_ne h
  have hval : (↑(φ (φ.symm ⟨y₂, hy₂K⟩)) : V) = y₂ :=
    congrArg Subtype.val (φ.apply_symm_apply ⟨y₂, hy₂K⟩)
  have hvalK : (↑(φ (φ.symm ⟨y₂, hy₂K⟩)) : V) ∈ K := by rw [hval]; exact hy₂K
  have hvaladj : G.Adj (↑(φ (φ.symm ⟨y₂, hy₂K⟩)) : V) p₂ := by rw [hval]; exact hy₂adj.symm
  have he₂ : (φ.symm ⟨y₂, hy₂K⟩).1 ∈ edgeAttachments φ (F \ {p₁}) :=
    ⟨(φ.symm ⟨y₂, hy₂K⟩).2, hvalK, p₂, ⟨hp₂F, hne.symm⟩, hvaladj⟩
  obtain ⟨l₀, hl₀, -⟩ := hX₂ he₂
  have hq₂2 : 2 ≤ q₂.length := by omega
  by_cases hclast : q₂[q₂.length - 1]'(by omega) ∈ q₁
  · -- the other end of the second branch is the one off the first branch
    have hq₂ne : q₂ ≠ [] := hq₂.1.1
    have hq₁ne : q₁ ≠ [] := hq₁.1.1
    have hq₁from : IsTrackFrom H q₁ (q₁[0]'(by omega)) (q₁[q₁.length - 1]'(by omega)) := by
      refine ⟨hq₁.1, ?_, ?_⟩
      · rw [List.head?_eq_head hq₁ne, List.head_eq_getElem]
      · rw [List.getLast?_eq_getLast hq₁ne, List.getLast_eq_getElem]
    have hq₂from : IsTrackFrom H q₂ (q₂[0]'(by omega)) (q₂[q₂.length - 1]'(by omega)) := by
      refine ⟨hq₂.1, ?_, ?_⟩
      · rw [List.head?_eq_head hq₂ne, List.head_eq_getElem]
      · rw [List.getLast?_eq_getLast hq₂ne, List.getLast_eq_getElem]
    obtain ⟨hbv₁, hbv₂⟩ := Thm75BranchEnds.branchEnds_mem_branchVertices J hJ H hsub q₁ _ _
      hq₁ hq₁from (by simp only [trackLength]; omega)
    obtain ⟨hbc₀, hbc₁⟩ := Thm75BranchEnds.branchEnds_mem_branchVertices J hJ H hsub q₂ _ _
      hq₂ hq₂from (by simp only [trackLength]; omega)
    have hends : ∀ z, z ∈ q₁ → z ∈ branchVertices H →
        z = q₁[0]'(by omega) ∨ z = q₁[q₁.length - 1]'(by omega) := by
      intro z hz hzb
      rcases mem_track_cases hz (by omega) with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact absurd hzb (hq₁.2.1 z hh)
    have hq₂0 : q₂[0]'(by omega) ∉ q₁ := by
      intro hmem
      have hd : q₂[0]'(by omega) ≠ q₂[q₂.length - 1]'(by omega) := by
        intro hh
        have := (List.Nodup.getElem_inj_iff hq₂.1.2.1).mp hh
        omega
      obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
      have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
      have hmatch : (q₂[0]'(by omega) = q₁[0]'(by omega) ∧
          q₂[q₂.length - 1]'(by omega) = q₁[q₁.length - 1]'(by omega)) ∨
          (q₂[0]'(by omega) = q₁[q₁.length - 1]'(by omega) ∧
          q₂[q₂.length - 1]'(by omega) = q₁[0]'(by omega)) := by
        rcases hends _ hmem hbc₀ with h0 | h0 <;> rcases hends _ hclast hbc₁ with h1 | h1
        · exact absurd (h0.trans h1.symm) hd
        · exact Or.inl ⟨h0, h1⟩
        · exact Or.inr ⟨h0, h1⟩
        · exact absurd (h0.trans h1.symm) hd
      exact branches_ne h hq₁ hX₁ hX₂
        (BranchClassification.trackEdges_eq_of_same_ends hι htrack hlen hrev hdisjint hnew
          hcover hedges hdeg hq₁ hq₁2 hq₁from hq₂ hq₂2 hq₂from hbv₁ hbv₂ hmatch)
    have hrevlen : q₂.reverse.length = q₂.length := List.length_reverse
    have hrevlast : q₂.reverse[q₂.reverse.length - 1]'(by omega) = q₂[0]'(by omega) := by
      rw [List.getElem_reverse]
      exact SubdivisionCounting.getElem_eq_of_index_eq q₂ (by omega) _ _
    obtain ⟨D, hcyc, hD3, hq₁cy, hcyq₂, rest⟩ :=
      exists_cycle_and_track_aux h hq₁ (isBranch_reverse hq₂) hX₁
        (by rwa [SubdivisionCounting.trackEdges_reverse]) (by omega)
        (by rw [hrevlast]; exact hq₂0) hs1 hs2
    refine ⟨D, hcyc, hD3, hq₁cy, ?_, rest⟩
    intro i hi
    rw [← SubdivisionCounting.trackEdges_reverse q₂]
    exact hcyq₂ i hi
  · exact exists_cycle_and_track_aux h hq₁ hq₂ hX₁ hX₂ hq₂2 hclast hs1 hs2

end Workspace.ProofLemmas.Thm58BranchBranchCycleHost
