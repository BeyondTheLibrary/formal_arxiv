import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61Claim1Helpers
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.AntiholeCompletion

/-!
# Geometric helpers for 6.1(1)

This module contains the bookkeeping used by the proof of claim (1).  Each lemma follows one
of the sentences in the printed proof on pp. 29--30: identify the source as `K₄`, split two
non-complete incident edges between `X₁` and `X₂`, read a leap on a line-graph path, and
exclude a common neighbour by closing an odd path into a hole.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm61Claim1Geometry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61Claim1Helpers

/-- If a subdivision of a 3-connected graph has exactly four branch-vertices, then its source
is `K₄`.  This is the first sentence after claim (1) in the paper. -/
theorem source_is_k4
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    {n : ℕ} (H : SimpleGraph (Fin n)) (hsub : IsSubdivision J H)
    (w₁ w₂ w₃ w₄ : Fin n) (hnd : [w₁, w₂, w₃, w₄].Nodup)
    (hbv : branchVertices H = ({w₁, w₂, w₃, w₄} : Set (Fin n))) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) H := by
  classical
  have hsub' := hsub
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub'
  have hdeg : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrange : Set.range ι = branchVertices H :=
    Set.Subset.antisymm
      (SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdeg)
      (SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges)
  have h12 : w₁ ≠ w₂ := by rintro rfl; simp at hnd
  have h13 : w₁ ≠ w₃ := by rintro rfl; simp at hnd
  have h14 : w₁ ≠ w₄ := by rintro rfl; simp at hnd
  have h23 : w₂ ≠ w₃ := by rintro rfl; simp at hnd
  have h24 : w₂ ≠ w₄ := by rintro rfl; simp at hnd
  have h34 : w₃ ≠ w₄ := by rintro rfl; simp at hnd
  have hfour : ({w₁, w₂, w₃, w₄} : Set (Fin n)).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [h12, h13, h14]),
      Set.ncard_insert_of_notMem (by simp [h23, h24]),
      Set.ncard_insert_of_notMem (by simp [h34]), Set.ncard_singleton]
  have hm4 : m = 4 := by
    have hc : (Set.range ι).ncard = m := by
      rw [Set.ncard_range_of_injective hι, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hrange, hbv, hfour] at hc
    exact hc.symm
  subst m
  have hJtop : J = (⊤ : SimpleGraph (Fin 4)) := by
    ext u v
    rw [SimpleGraph.top_adj]
    constructor
    · exact SimpleGraph.Adj.ne
    · intro huv
      by_contra hn
      have hsubN : J.neighborSet u ⊆ ({u, v} : Set (Fin 4))ᶜ := by
        intro x hx
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => J.irrefl (h ▸ hx), fun h => hn (h ▸ hx)⟩
      have hle := Set.ncard_le_ncard hsubN (Set.toFinite _)
      have hpair : ({u, v} : Set (Fin 4)).ncard = 2 := Set.ncard_pair huv
      have hsum := Set.ncard_add_ncard_compl ({u, v} : Set (Fin 4))
      rw [hpair, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
      have hdegU := SubdivisionCounting.three_le_degree_of_three_connected J hJ u
      omega
  constructor
  · rw [hJtop]
    exact ⟨SimpleGraph.Iso.refl⟩
  · rwa [hJtop] at hsub

/-- The two non-`X` edges at one branch-vertex are split between `X₁` and `X₂`.
This packages the saturation argument used twice in claim (1). -/
theorem split_two_extra
    {W : Type*} {H : SimpleGraph W} {X X₁ X₂ : Set (Sym2 W)} {v : W}
    (hv : v ∈ branchVertices H) (hsat₁ : SaturatesLineGraph H (X ∪ X₁))
    (hsat₂ : SaturatesLineGraph H (X ∪ X₂)) (hdisj : Disjoint X₁ X₂)
    {e f : Sym2 W} (he : e ∈ incidentEdges H v) (hf : f ∈ incidentEdges H v)
    (hef : e ≠ f) (heX : e ∉ X) (hfX : f ∉ X) :
    (e ∈ X₁ ∧ f ∈ X₂) ∨ (e ∈ X₂ ∧ f ∈ X₁) := by
  have h₁ : e ∈ X₁ ∨ f ∈ X₁ := by
    by_contra h
    push Not at h
    exact hef (hsat₁ v hv ⟨he, by simpa [heX] using h.1⟩ ⟨hf, by simpa [hfX] using h.2⟩)
  have h₂ : e ∈ X₂ ∨ f ∈ X₂ := by
    by_contra h
    push Not at h
    exact hef (hsat₂ v hv ⟨he, by simpa [heX] using h.1⟩ ⟨hf, by simpa [hfX] using h.2⟩)
  rcases h₁ with he₁ | hf₁ <;> rcases h₂ with he₂ | hf₂
  · exact False.elim (Set.disjoint_left.mp hdisj he₁ he₂)
  · exact Or.inl ⟨he₁, hf₂⟩
  · exact Or.inr ⟨he₂, hf₁⟩
  · exact False.elim (Set.disjoint_left.mp hdisj hf₁ hf₂)

/-- Consecutive edges of a repetition-free track have the same unordered pair exactly when
they occur at the same index. -/
theorem track_edge_injective
    {W : Type*} {B : List W} (hnd : B.Nodup) {i j : ℕ}
    (hi : i + 1 < B.length) (hj : j + 1 < B.length) :
    (s(B[i]'(by omega), B[i + 1]'hi) = s(B[j]'(by omega), B[j + 1]'hj) ↔ i = j) := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
    · exact hnd.getElem_inj_iff.mp h₁
    · have h₁' := hnd.getElem_inj_iff.mp h₁
      have h₂' := hnd.getElem_inj_iff.mp h₂
      omega
  · rintro rfl
    rfl

/-- The edge in position `i` of the middle track `B` sits in position `i+1` of the
line-graph path obtained by hanging one extra edge at each end. -/
theorem hung_track_edge_image
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K)
    {B : List W} {x y u v : W} (hB : IsTrackFrom H B x y) (hB2 : 2 ≤ B.length)
    (hu : H.Adj u x) (hv : H.Adj y v) (hun : u ∉ B) (hvn : v ∉ B) (huv : u ≠ v)
    (T : List W) (hTdef : T = u :: (B ++ [v])) (hT : IsTrackList H T)
    (i : ℕ) (hi : i + 1 < B.length)
    (he : s(B[i]'(by omega), B[i + 1]'hi) ∈ H.edgeSet) :
    (TrackToRungPath.trackRung phi T hT)[i + 1]'(by
        rw [TrackToRungPath.trackRung_length, trackLength, hTdef]
        simp only [List.length_cons, List.length_append, List.length_nil]
        omega) =
      (↑(phi ⟨s(B[i]'(by omega), B[i + 1]'hi), he⟩) : V) := by
  subst T
  have hTlen : (u :: (B ++ [v])).length = B.length + 2 := by simp
  have hEdges := hang_edges (u := u) (v := v) hB hB2
  have hEq := hEdges.2.2 (i + 1) (by omega)
    (show i + 1 + 2 < (u :: (B ++ [v])).length by rw [hTlen]; omega)
  have heT : s((u :: (B ++ [v]))[i + 1]'(by omega),
      (u :: (B ++ [v]))[i + 1 + 1]'(by omega)) ∈ H.edgeSet :=
    TrackToRungPath.trackEdge_mem_edgeSet hT (i + 1) (by rw [hTlen]; omega)
  have hv := TrackToRungPath.trackRung_getElem phi (u :: (B ++ [v])) hT
    (i + 1) (by
      rw [TrackToRungPath.trackRung_length, trackLength, hTlen]
      omega)
    (by rw [hTlen]; omega) heT
  calc
    (TrackToRungPath.trackRung phi (u :: (B ++ [v])) hT)[i + 1]'(by
        rw [TrackToRungPath.trackRung_length, trackLength, hTlen]
        omega) = (↑(phi ⟨_, heT⟩) : V) := hv
    _ = (↑(phi ⟨s(B[i]'(by omega), B[i + 1]'hi), he⟩) : V) :=
      congrArg (fun z : ↑H.edgeSet => (↑(phi z) : V))
        (edge_subtype_congr heT he hEq)

/-- Read the two non-end neighbours supplied by a leap on the line-graph path of
`u-B-v`.  On the edges of `B`, the first leap vertex sees exactly the first edge and the
second sees exactly the last edge. -/
theorem leap_hung_track_edges
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K)
    {B : List W} {x y u v : W} (hB : IsTrackFrom H B x y) (hB2 : 2 ≤ B.length)
    (hu : H.Adj u x) (hv : H.Adj y v) (hun : u ∉ B) (hvn : v ∉ B) (huv : u ≠ v)
    (T : List W) (hTdef : T = u :: (B ++ [v])) (hT : IsTrackList H T)
    {alpha beta : V}
    (hleap : IsLeapForPath G (TrackToRungPath.trackRung phi T hT) alpha beta) :
    (∀ (e : Sym2 W) (he : e ∈ H.edgeSet), e ∈ trackEdges B →
      (G.Adj alpha (↑(phi ⟨e, he⟩) : V) ↔
        e = s(B[0]'(by omega), B[1]'(by omega)))) ∧
    (∀ (e : Sym2 W) (he : e ∈ H.edgeSet), e ∈ trackEdges B →
      (G.Adj beta (↑(phi ⟨e, he⟩) : V) ↔
        e = s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)))) := by
  subst T
  let L := TrackToRungPath.trackRung phi (u :: (B ++ [v])) hT
  have hTlen : (u :: (B ++ [v])).length = B.length + 2 := by
    simp only [List.length_cons, List.length_append, List.length_nil]
  have hLlen : L.length = B.length + 1 := by
    dsimp only [L]
    rw [TrackToRungPath.trackRung_length]
    simp only [trackLength, hTlen]
    omega
  obtain ⟨-, -, -, -, hAlpha, hBeta⟩ := hleap
  change ∀ (i : ℕ) (hi : i < L.length),
    (G.Adj alpha (L[i]'hi) ↔ (i = 0 ∨ i = 1 ∨ i = L.length - 1)) at hAlpha
  change ∀ (i : ℕ) (hi : i < L.length),
    (G.Adj beta (L[i]'hi) ↔
      (i = 0 ∨ i = L.length - 2 ∨ i = L.length - 1)) at hBeta
  have hlastEdge :
      s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) =
        s(B[B.length - 2]'(by omega), B[B.length - 2 + 1]'(by omega)) := by
    rw [geq B (show B.length - 1 = B.length - 2 + 1 by omega) (by omega) (by omega)]
  have hEdges := hang_edges (u := u) (v := v) hB hB2
  have hread : ∀ (i : ℕ) (hi : i + 1 < B.length)
      (he : s(B[i]'(by omega), B[i + 1]'hi) ∈ H.edgeSet),
      L[i + 1]'(by rw [hLlen]; omega) =
        (↑(phi ⟨s(B[i]'(by omega), B[i + 1]'hi), he⟩) : V) := by
    intro i hi he
    have hEq := hEdges.2.2 (i + 1) (by omega)
      (show i + 1 + 2 < (u :: (B ++ [v])).length by rw [hTlen]; omega)
    have heT : s((u :: (B ++ [v]))[i + 1]'(by omega),
        (u :: (B ++ [v]))[i + 1 + 1]'(by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hT (i + 1) (by rw [hTlen]; omega)
    have hv := TrackToRungPath.trackRung_getElem phi (u :: (B ++ [v])) hT
      (i + 1) (show i + 1 < L.length by rw [hLlen]; omega)
      (show i + 1 + 1 < (u :: (B ++ [v])).length by rw [hTlen]; omega) heT
    change L[i + 1]'(by rw [hLlen]; omega) = _ at hv ⊢
    rw [hv]
    exact congrArg (fun z : ↑H.edgeSet => (↑(phi z) : V))
      (edge_subtype_congr heT he hEq)
  constructor
  · intro e he heB
    obtain ⟨i, hi, rfl⟩ := heB
    rw [← hread i hi he, hAlpha (i + 1) (by rw [hLlen]; omega)]
    constructor
    · intro h
      apply (track_edge_injective hB.1.2.1 hi (show 0 + 1 < B.length by omega)).mpr
      rcases h with h | h | h <;> omega
    · intro h
      have hi0 := (track_edge_injective hB.1.2.1 hi
        (show 0 + 1 < B.length by omega)).mp h
      exact Or.inr (Or.inl (by omega))
  · intro e he heB
    obtain ⟨i, hi, rfl⟩ := heB
    rw [← hread i hi he, hBeta (i + 1) (by rw [hLlen]; omega)]
    rw [hlastEdge]
    constructor
    · intro h
      apply (track_edge_injective hB.1.2.1 hi
        (show B.length - 2 + 1 < B.length by omega)).mpr
      rcases h with h | h | h <;> omega
    · intro h
      have hil := (track_edge_injective hB.1.2.1 hi
        (show B.length - 2 + 1 < B.length by omega)).mp h
      exact Or.inr (Or.inl (by omega))

/-- The path between the two vertices of a leap, with the old path's interior as its interior. -/
theorem leap_inner_path
    {V : Type*} {G : SimpleGraph V} {T : Set V}
    {P : List V} {p₀ pₙ u v : V}
    (hP : IsPathFrom G P p₀ pₙ) (hP5 : 5 ≤ pathLength P)
    (hPT : ∀ z ∈ P, z ∉ T) (huT : u ∈ T) (hvT : v ∈ T)
    (hleap : IsLeapForPath G P u v) :
    IsPathFrom G (u :: (interior P ++ [v])) u v ∧
      pathLength (u :: (interior P ++ [v])) = pathLength P := by
  obtain ⟨-, -, huv, hnuv, huadj, hvadj⟩ := hleap
  have hP6 : 6 ≤ P.length := by rw [PathBasics.pathLength_eq] at hP5; omega
  have hIP : IsPathFrom G (interior P) (P[1]'(by omega))
      (P[P.length - 2]'(by omega)) := PathGlue.isPathFrom_interior hP.1 (by omega)
  have huFirst : G.Adj u (P[1]'(by omega)) :=
    (huadj 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hvLast : G.Adj v (P[P.length - 2]'(by omega)) :=
    (hvadj (P.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
  have huNot : u ∉ interior P := fun hm => hPT u (PathBasics.interior_subset hm) huT
  have hvNot : v ∉ interior P := fun hm => hPT v (PathBasics.interior_subset hm) hvT
  have huOther : ∀ z ∈ interior P, z ≠ P[1]'(by omega) → ¬ G.Adj u z := by
    intro z hz hzne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hz
    have hkne : k ≠ 1 := fun he => hzne (hP.1.2.1.getElem_inj_iff.mpr he)
    rcases (huadj k hk).mp hadj with h | h | h <;> omega
  have hvOther : ∀ z ∈ interior P, z ≠ P[P.length - 2]'(by omega) →
      ¬ G.Adj v z := by
    intro z hz hzne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hz
    have hkne : k ≠ P.length - 2 :=
      fun he => hzne (hP.1.2.1.getElem_inj_iff.mpr he)
    rcases (hvadj k hk).mp hadj with h | h | h <;> omega
  have hQ := PathAttach.isPathFrom_cons_concat hIP huFirst hvLast hnuv huv
    huNot hvNot huOther hvOther
  refine ⟨hQ, ?_⟩
  rw [PathAttach.pathLength_cons_append_singleton, PathBasics.interior_length,
    PathBasics.pathLength_eq]
  omega

/-- An odd induced path cannot be closed through one further vertex in a Berge graph. -/
theorem no_common_closer
    {V : Type*} {G : SimpleGraph V} (hG : Berge G)
    {P : List V} {u v z : V} (hP : IsPathFrom G P u v)
    (hodd : Odd (pathLength P)) (h3 : 3 ≤ P.length) (hzP : z ∉ P)
    (hends : G.Adj z u ∧ G.Adj z v)
    (hint : ∀ x ∈ interior P, ¬ G.Adj z x) : False := by
  have hh := PrismBasics.isHoleList_of_path_add_vertex hP (by
    rw [PathBasics.pathLength_eq]; omega) hends.1 hends.2 hzP hint
  have heven := hG.1 _ hh
  rw [Nat.odd_iff] at hodd
  simp only [holeLength, List.length_cons] at heven
  rw [Nat.even_iff] at heven
  rw [PathBasics.pathLength_eq] at hodd
  omega

/-- The exceptional length-three outcome of 2.1 fixes the order of its two internal
vertices.  This is the paper's sentence *"It follows that `y₁` is nonadjacent to `q`, and
`y₂` is adjacent to `q`"*: the vertex adjacent to the right end cannot be the last internal
vertex of the complementary path. -/
theorem short_antipath_pair
    {V : Type*} {G : SimpleGraph V} {q s alpha beta : V} {Q : List V}
    (hab : alpha ≠ beta)
    (hpairEnds : alpha ≠ q ∧ alpha ≠ s ∧ beta ≠ q ∧ beta ≠ s)
    (hqs : G.Adj q s) (has : G.Adj alpha s)
    (hQ : IsAntipathFrom G Q q s) (hodd : Odd (pathLength Q))
    (hint : ∀ z ∈ interior Q, z ∈ ({alpha, beta} : Set V)) :
    ¬ G.Adj alpha q ∧ G.Adj beta q := by
  classical
  have hndI : (interior Q).Nodup :=
    hQ.1.2.1.sublist ((List.dropLast_sublist Q.tail).trans (List.tail_sublist Q))
  have hfin : (interior Q).toFinset ⊆ ({alpha, beta} : Finset V) := by
    intro z hz
    simpa using hint z (List.mem_toFinset.mp hz)
  have hIle : (interior Q).length ≤ 2 := by
    have hc := Finset.card_le_card hfin
    rw [List.toFinset_card_of_nodup hndI, Finset.card_pair hab] at hc
    exact hc
  have hQ3 : 3 ≤ Q.length :=
    AntiholeCompletion.three_le_length_of_antipath hQ hqs
  have hQ4 : Q.length ≤ 4 := by
    rw [PathBasics.interior_length] at hIle
    omega
  have hlen : Q.length = 4 := by
    obtain ⟨k, hk⟩ := hodd
    rw [pathLength] at hk
    omega
  obtain ⟨z₀, z₁, z₂, z₃, rfl⟩ := PathGlue.length_eq_four hlen
  have hz₀ : z₀ = q := by simpa using hQ.2.1
  have hz₃ : z₃ = s := by simpa using hQ.2.2
  subst z₀
  subst z₃
  have hnd : ([q, z₁, z₂, s] : List V).Nodup := hQ.1.2.1
  have hz₁ : z₁ = alpha ∨ z₁ = beta := by
    simpa using hint z₁ (by simp [SPGT.interior])
  have hz₂ : z₂ = alpha ∨ z₂ = beta := by
    simpa using hint z₂ (by simp [SPGT.interior])
  have h12 : z₁ ≠ z₂ := by rintro rfl; simp at hnd
  have hz₂b : z₂ = beta := by
    rcases hz₂ with h | h
    · have hc : Gᶜ.Adj z₂ s :=
        PathBasics.path_adj_succ hQ.1 (i := 2) (by simp)
      rw [h] at hc
      exact absurd has hc.2
    · exact h
  have hz₁a : z₁ = alpha := by
    rcases hz₁ with h | h
    · exact h
    · exact absurd (h.trans hz₂b.symm) h12
  subst z₁
  subst z₂
  have hqaC : Gᶜ.Adj q alpha :=
    PathBasics.path_adj_succ hQ.1 (i := 0) (by simp)
  have hqbNotC : ¬ Gᶜ.Adj q beta := by
    intro h
    have hc := (PathBasics.path_adj_iff hQ.1 (i := 0) (j := 2)
      (by simp) (by simp)).mp h
    omega
  refine ⟨fun h => hqaC.2 h.symm, ?_⟩
  by_contra hn
  exact hqbNotC ⟨hpairEnds.2.2.1.symm, fun h => hn h.symm⟩

/-- Apply 2.1 to the second diagonal branch.  In the leap outcome its order is fixed by
`alpha` seeing the last edge.  In the exceptional outcome `short_antipath_pair` gives the
same order.  Thus the conclusion is uniform across the two outcomes. -/
theorem second_hung_track_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K)
    {B : List (Fin n)} {x y u v : Fin n}
    (hB : IsTrackFrom H B x y) (hB2 : 2 ≤ B.length)
    (hu : H.Adj u x) (hv : H.Adj y v) (hun : u ∉ B) (hvn : v ∉ B) (huv : u ≠ v)
    (T : List (Fin n)) (hTdef : T = u :: (B ++ [v])) (hT : IsTrackList H T)
    (hT5 : 5 ≤ T.length) (hpar : T.length % 2 = 1)
    (alpha beta : V) (hab : alpha ≠ beta) (haK : alpha ∉ K) (hbK : beta ∉ K)
    (hanti : AnticonnectedSet G ({alpha, beta} : Set V))
    (h0 : s(T[0]'(by omega), T[1]'(by omega)) ∈
      completeEdges G H K phi ({alpha, beta} : Set V))
    (hlast : s(T[T.length - 2]'(by omega), T[T.length - 1]'(by omega)) ∈
      completeEdges G H K phi ({alpha, beta} : Set V))
    (hint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < T.length,
      s(T[i]'(by omega), T[i + 1]'(by omega)) ∉
        completeEdges G H K phi ({alpha, beta} : Set V))
    (haLast : ∀ he : s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) ∈
        H.edgeSet,
      G.Adj alpha (↑(phi ⟨s(B[B.length - 2]'(by omega),
        B[B.length - 1]'(by omega)), he⟩) : V))
    (hNoCommon : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges B →
      ¬ (G.Adj alpha (↑(phi ⟨e, he⟩) : V) ∧
        G.Adj beta (↑(phi ⟨e, he⟩) : V))) :
    (∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges B →
      (G.Adj alpha (↑(phi ⟨e, he⟩) : V) ↔
        e = s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)))) ∧
    (∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges B →
      (G.Adj beta (↑(phi ⟨e, he⟩) : V) ↔
        e = s(B[0]'(by omega), B[1]'(by omega)))) := by
  classical
  have hZK : ∀ z ∈ ({alpha, beta} : Set V), z ∉ K := by
    intro z hz
    rcases hz with (rfl | rfl)
    · exact haK
    · exact hbK
  have hRR := two_one_track G hG phi ({alpha, beta} : Set V) hanti hZK
    T hT hT5 hpar h0 hlast hint
  rcases hRR with hLeap | hShort
  · obtain ⟨-, a, ha, b, hb, hleap⟩ := hLeap
    obtain ⟨haEdges, hbEdges⟩ := leap_hung_track_edges phi hB hB2 hu hv hun hvn huv
      T hTdef hT hleap
    have hLastNorm :
        s(B[B.length - 2]'(by omega), B[B.length - 2 + 1]'(by omega)) =
          s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) := by
      apply congrArg (fun z => s(B[B.length - 2]'(by omega), z))
      apply geq
      omega
    have hLastEdge : s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) ∈
        H.edgeSet := by
      have h := TrackToRungPath.trackEdge_mem_edgeSet hB.1 (B.length - 2) (by omega)
      rwa [hLastNorm] at h
    have haNot : a ≠ alpha := by
      have hB3 : 3 ≤ B.length := by
        rw [hTdef] at hT5
        simp only [List.length_cons, List.length_append, List.length_nil] at hT5
        omega
      intro hae
      subst a
      have heq := (haEdges _ hLastEdge ⟨B.length - 2, by omega, hLastNorm.symm⟩).mp
        (haLast hLastEdge)
      have hi := (track_edge_injective hB.1.2.1 (show B.length - 2 + 1 < B.length by omega)
        (show 0 + 1 < B.length by omega)).mp (hLastNorm.trans heq)
      omega
    have haBeta : a = beta := by
      simpa [haNot] using ha
    have hbAlpha : b = alpha := by
      rcases hb with h | h
      · exact h
      · exact absurd (haBeta.trans h.symm) hleap.2.2.1
    subst a
    subst b
    exact ⟨hbEdges, haEdges⟩
  · obtain ⟨hPL, cc, dd, hInt, Q, hQ, hodd, hQint⟩ := hShort
    let L := TrackToRungPath.trackRung phi T hT
    have hLlen : L.length = 4 := by
      change pathLength L = 3 at hPL
      rw [pathLength] at hPL
      omega
    have hBlen : B.length = 3 := by
      have hTlen : T.length = B.length + 2 := by
        rw [hTdef]
        simp
      have hRlen := TrackToRungPath.trackRung_length phi T hT
      change L.length = T.length - 1 at hRlen
      omega
    have hFirstEdge : s(B[0]'(by omega), B[1]'(by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hB.1 0 (by omega)
    have hLastNorm :
        s(B[B.length - 2]'(by omega), B[B.length - 2 + 1]'(by omega)) =
          s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) := by
      apply congrArg (fun z => s(B[B.length - 2]'(by omega), z))
      apply geq
      omega
    have hLastRaw : s(B[B.length - 2]'(by omega), B[B.length - 2 + 1]'(by omega)) ∈
        H.edgeSet := TrackToRungPath.trackEdge_mem_edgeSet hB.1 (B.length - 2) (by omega)
    have hLastEdge : s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) ∈
        H.edgeSet := by rwa [← hLastNorm]
    let qv : V := ↑(phi ⟨s(B[0]'(by omega), B[1]'(by omega)), hFirstEdge⟩)
    let sv : V := ↑(phi ⟨s(B[B.length - 2]'(by omega),
      B[B.length - 1]'(by omega)), hLastEdge⟩)
    have hqv : L[1]'(by omega) = qv := by
      dsimp only [L, qv]
      exact hung_track_edge_image phi hB hB2 hu hv hun hvn huv T hTdef hT 0 (by omega)
        hFirstEdge
    have hsv : L[2]'(by omega) = sv := by
      have hm := hung_track_edge_image phi hB hB2 hu hv hun hvn huv T hTdef hT
        (B.length - 2) (by omega) hLastRaw
      calc
        L[2]'(by omega) = L[B.length - 2 + 1]'(by omega) := by
          apply geq
          omega
        _ = (↑(phi ⟨s(B[B.length - 2]'(by omega),
              B[B.length - 2 + 1]'(by omega)), hLastRaw⟩) : V) := hm
        _ = sv := by
          dsimp only [sv]
          exact congrArg (fun z : ↑H.edgeSet => (↑(phi z) : V))
            (edge_subtype_congr hLastRaw hLastEdge hLastNorm)
    obtain ⟨z₀, z₁, z₂, z₃, hshape⟩ := PathGlue.length_eq_four hLlen
    change interior L = [cc, dd] at hInt
    rw [hshape] at hInt
    simp [SPGT.interior] at hInt
    have hcc : cc = L[1]'(by omega) := by
      simpa [hshape] using hInt.1.symm
    have hdd : dd = L[2]'(by omega) := by
      simpa [hshape] using hInt.2.symm
    have hLpath : IsPathList G L := TrackToRungPath.trackRung_isPathList phi T hT (by
      simp only [trackLength]
      omega)
    have hqs : G.Adj qv sv := by
      rw [← hqv, ← hsv]
      exact PathBasics.path_adj_succ hLpath (i := 1) (by omega)
    have hqK : qv ∈ K := by exact Subtype.coe_prop _
    have hsK : sv ∈ K := by exact Subtype.coe_prop _
    have hQ' : IsAntipathFrom G Q qv sv := by
      rw [← hqv, ← hsv, ← hcc, ← hdd]
      exact hQ
    have hshort := short_antipath_pair hab
      ⟨fun h => haK (h ▸ hqK), fun h => haK (h ▸ hsK),
        fun h => hbK (h ▸ hqK), fun h => hbK (h ▸ hsK)⟩
      hqs (haLast hLastEdge) hQ' hodd hQint
    have haFirst : ¬ G.Adj alpha qv := hshort.1
    have hbFirst : G.Adj beta qv := hshort.2
    have haLast' : G.Adj alpha sv := haLast hLastEdge
    have hbLast : ¬ G.Adj beta sv := by
      intro h
      exact hNoCommon _ hLastEdge ⟨B.length - 2, by omega, hLastNorm.symm⟩ ⟨haLast', h⟩
    constructor
    · intro e he heB
      obtain ⟨i, hi, rfl⟩ := heB
      have hic : i = 0 ∨ i = B.length - 2 := by omega
      rcases hic with rfl | hiLast
      · have himage : (↑(phi ⟨s(B[0]'(by omega), B[0 + 1]'hi), he⟩) : V) = qv := by
          rfl
        rw [himage]
        constructor
        · exact fun h => absurd h haFirst
        · intro h
          have := (track_edge_injective hB.1.2.1 hi (show B.length - 2 + 1 < B.length by
            omega)).mp (h.trans hLastNorm.symm)
          omega
      · subst i
        have himage : (↑(phi ⟨s(B[B.length - 2]'(by omega),
            B[B.length - 2 + 1]'hi), he⟩) : V) = sv := by
          dsimp only [sv]
          exact congrArg (fun z : ↑H.edgeSet => (↑(phi z) : V))
            (edge_subtype_congr he hLastEdge (by
              exact hLastNorm))
        rw [himage]
        constructor
        · intro _
          exact hLastNorm
        · exact fun _ => haLast'
    · intro e he heB
      obtain ⟨i, hi, rfl⟩ := heB
      have hic : i = 0 ∨ i = B.length - 2 := by omega
      rcases hic with rfl | hiLast
      · have himage : (↑(phi ⟨s(B[0]'(by omega), B[0 + 1]'hi), he⟩) : V) = qv := by
          rfl
        rw [himage]
        constructor
        · exact fun _ => rfl
        · exact fun _ => hbFirst
      · subst i
        have himage : (↑(phi ⟨s(B[B.length - 2]'(by omega),
            B[B.length - 2 + 1]'hi), he⟩) : V) = sv := by
          dsimp only [sv]
          exact congrArg (fun z : ↑H.edgeSet => (↑(phi z) : V))
            (edge_subtype_congr he hLastEdge (by
              exact hLastNorm))
        rw [himage]
        constructor
        · exact fun h => absurd h hbLast
        · intro h
          have := (track_edge_injective hB.1.2.1
            (show B.length - 2 + 1 < B.length by omega) (show 0 + 1 < B.length by omega)).mp
            h
          omega

/-- Both ends of an edge of a track occur on the track's vertex list. -/
theorem vertices_mem_of_track_edge
    {W : Type*} {B : List W} {e : Sym2 W} (he : e ∈ trackEdges B) :
    ∀ z ∈ e, z ∈ B := by
  obtain ⟨i, hi, rfl⟩ := he
  intro z hz
  rcases Sym2.mem_iff.mp hz with h | h
  · exact h ▸ List.getElem_mem _
  · exact h ▸ List.getElem_mem _

/-- Vertex-disjoint tracks have distinct edges. -/
theorem disjoint_track_edge_ne
    {W : Type*} {B C : List W} (hdisj : ∀ z ∈ B, z ∉ C)
    {e f : Sym2 W} (he : e ∈ trackEdges B) (hf : f ∈ trackEdges C) : e ≠ f := by
  intro hef
  obtain ⟨i, hi, rfl⟩ := he
  have hzB : B[i]'(by omega) ∈ B := List.getElem_mem _
  have hze : B[i]'(by omega) ∈ s(B[i]'(by omega), B[i + 1]'hi) := by simp
  exact hdisj _ hzB (vertices_mem_of_track_edge (hef ▸ hf) _ hze)

/-- Images of edges on two vertex-disjoint tracks are nonadjacent in the appearing line graph. -/
theorem disjoint_track_images_nonadj
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K)
    {B C : List W} (hdisj : ∀ z ∈ B, z ∉ C)
    {e f : Sym2 W} (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet)
    (heB : e ∈ trackEdges B) (hfC : f ∈ trackEdges C) :
    ¬ G.Adj (↑(phi ⟨e, he⟩) : V) (↑(phi ⟨f, hf⟩) : V) := by
  intro hadj
  have hline : H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := phi.map_rel_iff.mp hadj
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hline
  obtain ⟨-, z, hze, hzf⟩ := hline
  exact hdisj z (vertices_mem_of_track_edge heB z hze)
    (vertices_mem_of_track_edge hfC z hzf)

/-- The odd path supplied by a leap cannot have a common neighbour on a vertex-disjoint
track.  Otherwise that neighbour closes the path into an odd hole. -/
theorem no_common_neighbor_on_disjoint_track
    {V : Type*} {G : SimpleGraph V} (hG : Berge G)
    {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (phi : H.lineGraph ≃g G.induce K)
    {B C : List (Fin n)} {x y u v : Fin n}
    (hB : IsTrackFrom H B x y) (hB2 : 2 ≤ B.length)
    (hu : H.Adj u x) (hv : H.Adj y v) (hun : u ∉ B) (hvn : v ∉ B) (huv : u ≠ v)
    (T : List (Fin n)) (hTdef : T = u :: (B ++ [v])) (hT : IsTrackList H T)
    (hP5 : 5 ≤ pathLength (TrackToRungPath.trackRung phi T hT))
    (hodd : Odd (pathLength (TrackToRungPath.trackRung phi T hT)))
    (hdisj : ∀ z ∈ B, z ∉ C)
    {alpha beta : V} (haK : alpha ∉ K) (hbK : beta ∉ K)
    (hleap : IsLeapForPath G (TrackToRungPath.trackRung phi T hT) alpha beta)
    {f : Sym2 (Fin n)} (hf : f ∈ H.edgeSet) (hfC : f ∈ trackEdges C) :
    ¬ (G.Adj alpha (↑(phi ⟨f, hf⟩) : V) ∧
      G.Adj beta (↑(phi ⟨f, hf⟩) : V)) := by
  let L := TrackToRungPath.trackRung phi T hT
  have hLpath : IsPathList G L := hleap.1
  have hLlen : 6 ≤ L.length := by
    change 5 ≤ pathLength L at hP5
    rw [PathBasics.pathLength_eq] at hP5
    omega
  have hLfrom : IsPathFrom G L (L[0]'(by omega)) (L[L.length - 1]'(by omega)) := by
    refine ⟨hLpath, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < L.length by omega)]
    · rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (show L.length - 1 < L.length by omega)]
  have hLK : ∀ z ∈ L, z ∈ K := TrackToRungPath.trackRung_subset_K phi T hT
  have hLpair : ∀ z ∈ L, z ∉ ({alpha, beta} : Set V) := by
    intro z hz hpair
    rcases hpair with h | h
    · exact haK (h ▸ hLK z hz)
    · exact hbK (h ▸ hLK z hz)
  obtain ⟨hInner, hInnerLen⟩ := leap_inner_path hLfrom hP5 hLpair
    (by simp) (by simp) hleap
  let P := alpha :: (interior L ++ [beta])
  have hP3 : 3 ≤ P.length := by
    dsimp only [P]
    rw [List.length_cons, List.length_append, List.length_singleton,
      PathBasics.interior_length]
    omega
  have hfK : (↑(phi ⟨f, hf⟩) : V) ∈ K := Subtype.coe_prop _
  have hTlen : T.length = B.length + 2 := by
    rw [hTdef]
    simp
  have hHungLen : (u :: (B ++ [v])).length = T.length :=
    congrArg List.length hTdef.symm
  have hLlenT : L.length = T.length - 1 := by
    dsimp only [L]
    rw [TrackToRungPath.trackRung_length, trackLength]
  have hhang := hang_edges (u := u) (v := v) hB hB2
  have hdecode : ∀ z ∈ interior L,
      ∃ e : Sym2 (Fin n), ∃ he : e ∈ H.edgeSet, e ∈ trackEdges B ∧
        z = (↑(phi ⟨e, he⟩) : V) := by
    intro z hz
    obtain ⟨i, hi, hi1, hi2, hiz⟩ := PathBasics.exists_getElem_of_mem_interior hLpath hz
    have hiT : i + 1 < T.length := by omega
    let e := s(T[i]'(by omega), T[i + 1]'hiT)
    have he : e ∈ H.edgeSet := TrackToRungPath.trackEdge_mem_edgeSet hT i hiT
    have heq := hhang.2.2 i hi1 (by omega)
    have heB : e ∈ trackEdges B := by
      refine ⟨i - 1, by omega, ?_⟩
      dsimp only [e]
      simp only [hTdef]
      rw [heq]
      apply congrArg (fun z => s(B[i - 1]'(by omega), z))
      apply geq
      omega
    refine ⟨e, he, heB, ?_⟩
    rw [← hiz]
    exact TrackToRungPath.trackRung_getElem phi T hT i hi hiT he
  have hfP : (↑(phi ⟨f, hf⟩) : V) ∉ P := by
    intro hm
    rcases List.mem_cons.mp hm with h | hm
    · exact haK (h.symm ▸ hfK)
    · rcases List.mem_append.mp hm with hm | h
      · obtain ⟨e, he, heB, hez⟩ := hdecode _ hm
        have hef : e ≠ f := disjoint_track_edge_ne hdisj heB hfC
        have hphi : (⟨e, he⟩ : ↑H.edgeSet) = ⟨f, hf⟩ :=
          EquivLike.injective phi (Subtype.ext hez.symm)
        exact hef (congrArg Subtype.val hphi)
      · have hfb : (↑(phi ⟨f, hf⟩) : V) = beta := List.eq_of_mem_singleton h
        exact hbK (hfb.symm ▸ hfK)
  have hfInterior : ∀ z ∈ interior P, ¬ G.Adj (↑(phi ⟨f, hf⟩) : V) z := by
    intro z hz
    have hzL : z ∈ interior L := by
      dsimp only [P] at hz
      simpa [SPGT.interior] using hz
    obtain ⟨e, he, heB, rfl⟩ := hdecode z hzL
    exact fun hadj => disjoint_track_images_nonadj phi hdisj he hf heB hfC hadj.symm
  have hoddP : Odd (pathLength P) := by
    change Odd (pathLength L) at hodd
    change pathLength P = pathLength L at hInnerLen
    rw [hInnerLen]
    exact hodd
  intro hboth
  exact no_common_closer hG hInner hoddP hP3 hfP
    ⟨hboth.1.symm, hboth.2.symm⟩ hfInterior

end Workspace.ProofLemmas.Thm61Claim1Geometry
