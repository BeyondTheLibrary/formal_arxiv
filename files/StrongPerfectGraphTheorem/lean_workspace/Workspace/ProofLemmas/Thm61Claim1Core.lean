import Mathlib
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Claim1Geometry
import Workspace.ProofLemmas.Thm61Claim1Card

/-!
# The canonical long-diagonal case of 6.1(1)

The cycle edge `w₁w₂` is the missing complete edge.  The adjacent cycle edges are
complete, the diagonal from `w₂` to `w₄` is long, and its first edge lies in the opposite
extra set from `w₁w₂`.  This is the orientation used in the printed proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Workspace.ProofLemmas.Thm61Claim1Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61Claim1Geometry

/-- The long-diagonal argument of claim (1), after orienting `X₁,X₂`. -/
theorem canonical_long_oriented
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (phi : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K phi y)
    (yA yB : V)
    (XA XB : Set (Sym2 (Fin n)))
    (hXAdef : XA = extraEdges G H K phi Y yA)
    (hXBdef : XB = extraEdges G H K phi Y yB)
    (hdisjAB : Disjoint XA XB)
    (hsatA : SaturatesLineGraph H (completeEdges G H K phi Y ∪ XA))
    (hsatB : SaturatesLineGraph H (completeEdges G H K phi Y ∪ XB))
    (hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (w₁ w₂ w₃ w₄ : Fin n) (hnd : [w₁, w₂, w₃, w₄].Nodup)
    (hbv : branchVertices H = ({w₁, w₂, w₃, w₄} : Set (Fin n)))
    (hc₁ : H.Adj w₁ w₂) (hc₂ : H.Adj w₂ w₃)
    (hc₃ : H.Adj w₃ w₄) (hc₄ : H.Adj w₄ w₁)
    (Bp Bq : List (Fin n))
    (hBp : IsTrackFrom H Bp w₂ w₄) (hBq : IsTrackFrom H Bq w₃ w₁)
    (hlenP : 2 ≤ trackLength Bp) (hlenQ : 2 ≤ trackLength Bq)
    (hevenP : Even (trackLength Bp)) (hevenQ : Even (trackLength Bq))
    (hdisjPQ : ∀ z ∈ Bp, z ∉ Bq)
    (havoidP : ∀ z ∈ Bp, z ≠ w₁ ∧ z ≠ w₃)
    (havoidQ : ∀ z ∈ Bq, z ≠ w₂ ∧ z ≠ w₄)
    (hedges : H.edgeSet =
      ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} :
        Set (Sym2 (Fin n))) ∪ trackEdges Bp ∪ trackEdges Bq)
    (hLong : 4 ≤ trackLength Bp)
    (hXC : completeEdges G H K phi Y ⊆
      ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} :
        Set (Sym2 (Fin n))))
    (haNotX : s(w₁, w₂) ∉ completeEdges G H K phi Y)
    (hbX : s(w₂, w₃) ∈ completeEdges G H K phi Y)
    (hdX : s(w₄, w₁) ∈ completeEdges G H K phi Y)
    (haXA : s(w₁, w₂) ∈ XA)
    (hpXB : s(Bp[0]'(by
        simp only [trackLength] at hlenP; omega), Bp[1]'(by
        simp only [trackLength] at hlenP; omega)) ∈ XB) :
    Thm61Concl G m J n H K phi Y := by
  classical
  let a := s(w₁, w₂)
  let b := s(w₂, w₃)
  let c := s(w₃, w₄)
  let d := s(w₄, w₁)
  have hBp2 : 2 ≤ Bp.length := by simp only [trackLength] at hlenP; omega
  have hBq2 : 2 ≤ Bq.length := by simp only [trackLength] at hlenQ; omega
  let p := s(Bp[0]'(by omega), Bp[1]'(by omega))
  let r := s(Bp[Bp.length - 2]'(by omega), Bp[Bp.length - 1]'(by omega))
  let q := s(Bq[0]'(by omega), Bq[1]'(by omega))
  let s' := s(Bq[Bq.length - 2]'(by omega), Bq[Bq.length - 1]'(by omega))
  have hpnorm : p = s(Bp[0]'(by omega), Bp[0 + 1]'(by omega)) := rfl
  have hrnorm :
      s(Bp[Bp.length - 2]'(by omega), Bp[Bp.length - 2 + 1]'(by omega)) = r := by
    dsimp only [r]
    apply congrArg (fun z => s(Bp[Bp.length - 2]'(by omega), z))
    apply geq
    omega
  have hqnorm : q = s(Bq[0]'(by omega), Bq[0 + 1]'(by omega)) := rfl
  have hsnorm :
      s(Bq[Bq.length - 2]'(by omega), Bq[Bq.length - 2 + 1]'(by omega)) = s' := by
    dsimp only [s']
    apply congrArg (fun z => s(Bq[Bq.length - 2]'(by omega), z))
    apply geq
    omega
  have hpB : p ∈ trackEdges Bp := ⟨0, by omega, hpnorm⟩
  have hrB : r ∈ trackEdges Bp := ⟨Bp.length - 2, by omega, hrnorm.symm⟩
  have hqB : q ∈ trackEdges Bq := ⟨0, by omega, hqnorm⟩
  have hsB : s' ∈ trackEdges Bq := ⟨Bq.length - 2, by omega, hsnorm.symm⟩
  have hpE : p ∈ H.edgeSet := by
    dsimp only [p]
    exact TrackToRungPath.trackEdge_mem_edgeSet hBp.1 0 (by omega)
  have hrE : r ∈ H.edgeSet := by
    have h := TrackToRungPath.trackEdge_mem_edgeSet hBp.1 (Bp.length - 2) (by omega)
    rwa [hrnorm] at h
  have hqE : q ∈ H.edgeSet := by
    dsimp only [q]
    exact TrackToRungPath.trackEdge_mem_edgeSet hBq.1 0 (by omega)
  have hsE : s' ∈ H.edgeSet := by
    have h := TrackToRungPath.trackEdge_mem_edgeSet hBq.1 (Bq.length - 2) (by omega)
    rwa [hsnorm] at h
  have h12 : w₁ ≠ w₂ := by rintro rfl; simp at hnd
  have h13 : w₁ ≠ w₃ := by rintro rfl; simp at hnd
  have h14 : w₁ ≠ w₄ := by rintro rfl; simp at hnd
  have h23 : w₂ ≠ w₃ := by rintro rfl; simp at hnd
  have h24 : w₂ ≠ w₄ := by rintro rfl; simp at hnd
  have h34 : w₃ ≠ w₄ := by rintro rfl; simp at hnd
  have hpInc : p ∈ incidentEdges H w₂ := by
    refine ⟨hpE, ?_⟩
    dsimp only [p]
    simp only [Sym2.mem_iff]
    exact Or.inl (head_getElem hBp.2.1 (by omega)).symm
  have hrInc : r ∈ incidentEdges H w₄ := by
    refine ⟨hrE, ?_⟩
    dsimp only [r]
    simp only [Sym2.mem_iff]
    exact Or.inr (last_getElem hBp.2.2 (by omega)).symm
  have hqInc : q ∈ incidentEdges H w₃ := by
    refine ⟨hqE, ?_⟩
    dsimp only [q]
    simp only [Sym2.mem_iff]
    exact Or.inl (head_getElem hBq.2.1 (by omega)).symm
  have hsInc : s' ∈ incidentEdges H w₁ := by
    refine ⟨hsE, ?_⟩
    dsimp only [s']
    simp only [Sym2.mem_iff]
    exact Or.inr (last_getElem hBq.2.2 (by omega)).symm
  have hBpNotX : ∀ e ∈ trackEdges Bp, e ∉ completeEdges G H K phi Y := by
    intro e heB heX
    have heCycle := hXC heX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heCycle
    have hw1 : w₁ ∉ e := trackEdge_avoids (fun hw => (havoidP w₁ hw).1 rfl) heB
    have hw3 : w₃ ∉ e := trackEdge_avoids (fun hw => (havoidP w₃ hw).2 rfl) heB
    rcases heCycle with h | h | h | h
    · exact hw1 (h ▸ (by simp))
    · exact hw3 (h ▸ (by simp))
    · exact hw3 (h ▸ (by simp))
    · exact hw1 (h ▸ (by simp))
  have hBqNotX : ∀ e ∈ trackEdges Bq, e ∉ completeEdges G H K phi Y := by
    intro e heB heX
    have heCycle := hXC heX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heCycle
    have hw2 : w₂ ∉ e := trackEdge_avoids (fun hw => (havoidQ w₂ hw).1 rfl) heB
    have hw4 : w₄ ∉ e := trackEdge_avoids (fun hw => (havoidQ w₄ hw).2 rfl) heB
    rcases heCycle with h | h | h | h
    · exact hw2 (h ▸ (by simp))
    · exact hw2 (h ▸ (by simp))
    · exact hw4 (h ▸ (by simp))
    · exact hw4 (h ▸ (by simp))
  have hsNotX : s' ∉ completeEdges G H K phi Y := hBqNotX s' hsB
  have haInc1 : a ∈ incidentEdges H w₁ := by
    exact ⟨(SimpleGraph.mem_edgeSet H).mpr hc₁, by simp [a]⟩
  have haInc2 : a ∈ incidentEdges H w₂ := by
    exact ⟨(SimpleGraph.mem_edgeSet H).mpr hc₁, by simp [a]⟩
  have hbInc2 : b ∈ incidentEdges H w₂ := by
    exact ⟨(SimpleGraph.mem_edgeSet H).mpr hc₂, by simp [b]⟩
  have hcInc3 : c ∈ incidentEdges H w₃ := by
    exact ⟨(SimpleGraph.mem_edgeSet H).mpr hc₃, by simp [c]⟩
  have hdInc1 : d ∈ incidentEdges H w₁ := by
    exact ⟨(SimpleGraph.mem_edgeSet H).mpr hc₄, by simp [d]⟩
  have hpa : p ≠ a := by
    intro h
    have hw1 : w₁ ∉ p := trackEdge_avoids (fun hw => (havoidP w₁ hw).1 rfl) hpB
    exact hw1 (h ▸ (by simp [a]))
  have hsb : s' ≠ a := by
    intro h
    have hw2 : w₂ ∉ s' := trackEdge_avoids (fun hw => (havoidQ w₂ hw).1 rfl) hsB
    exact hw2 (h ▸ (by simp [a]))
  have hsXB : s' ∈ XB := by
    rcases split_two_extra (by rw [hbv]; simp) hsatA hsatB hdisjAB
      haInc1 hsInc hsb.symm haNotX hsNotX with h | h
    · exact h.2
    · exact False.elim (Set.disjoint_left.mp hdisjAB haXA h.1)
  have hT1 := hang_track hBp hBp2 hc₂.symm hc₄
    (fun hw => (havoidP w₃ hw).2 rfl) (fun hw => (havoidP w₁ hw).1 rfl) h13.symm
  let T1 := w₃ :: (Bp ++ [w₁])
  have hT1def : T1 = w₃ :: (Bp ++ [w₁]) := rfl
  have hT1track : IsTrackList H T1 := hT1.1.1
  have hT1len : T1.length = Bp.length + 2 := hT1.2.1
  have hT1five : 5 ≤ T1.length := by simp only [trackLength] at hLong; omega
  have hT1par : T1.length % 2 = 1 := by
    obtain ⟨k, hk⟩ := hevenP
    simp only [trackLength] at hk
    omega
  have hhangP := hang_edges (u := w₃) (v := w₁) hBp hBp2
  have hT1first : s(T1[0]'(by omega), T1[1]'(by omega)) ∈ completeEdges G H K phi Y := by
    change s((w₃ :: (Bp ++ [w₁]))[0]'(by omega),
      (w₃ :: (Bp ++ [w₁]))[1]'(by omega)) ∈ completeEdges G H K phi Y
    rw [hhangP.1, Sym2.eq_swap]
    exact hbX
  have hT1last : s(T1[T1.length - 2]'(by omega), T1[T1.length - 1]'(by omega)) ∈
      completeEdges G H K phi Y := by
    change s((w₃ :: (Bp ++ [w₁]))[(w₃ :: (Bp ++ [w₁])).length - 2]'(by omega),
      (w₃ :: (Bp ++ [w₁]))[(w₃ :: (Bp ++ [w₁])).length - 1]'(by omega)) ∈
        completeEdges G H K phi Y
    rw [hhangP.2.1]
    exact hdX
  have hT1internal : ∀ i : ℕ, 1 ≤ i → ∀ hi : i + 2 < T1.length,
      s(T1[i]'(by omega), T1[i + 1]'(by omega)) ∉ completeEdges G H K phi Y := by
    intro i hi1 hi heX
    change s((w₃ :: (Bp ++ [w₁]))[i]'(by omega),
      (w₃ :: (Bp ++ [w₁]))[i + 1]'(by omega)) ∈ completeEdges G H K phi Y at heX
    rw [hhangP.2.2 i hi1 (by simpa [T1] using hi)] at heX
    exact hBpNotX _ ⟨i - 1, by
      have hilen : i + 2 < Bp.length + 2 := by simpa [T1] using hi
      omega, by
      apply congrArg (fun z => s(Bp[i - 1]'(by omega), z))
      apply geq
      omega⟩ heX
  have hYK : ∀ y ∈ Y, y ∉ K := fun y hy => (hYmajor y hy).1
  have hRR := two_one_track G hG phi Y hYanti hYK T1 hT1track hT1five hT1par
    hT1first hT1last hT1internal
  obtain ⟨hP5, alpha, haY, beta, hbY, hleap⟩ := hRR.resolve_right (by
    rintro ⟨h3, -⟩
    rw [TrackToRungPath.trackRung_pathLength, trackLength] at h3
    simp only [T1, List.length_cons, List.length_append, List.length_nil] at h3
    simp only [trackLength] at hLong
    omega)
  obtain ⟨haP, hbP⟩ := leap_hung_track_edges phi hBp hBp2 hc₂.symm hc₄
    (fun hw => (havoidP w₃ hw).2 rfl) (fun hw => (havoidP w₁ hw).1 rfl) h13.symm
    T1 hT1def hT1track hleap
  have hbNotP : ¬ G.Adj beta (↑(phi ⟨p, hpE⟩) : V) := by
    intro hadj
    have heq := (hbP p hpE hpB).mp hadj
    have hi := (track_edge_injective hBp.1.2.1 (show 0 + 1 < Bp.length by omega)
      (show Bp.length - 2 + 1 < Bp.length by omega)).mp (heq.trans hrnorm.symm)
    simp only [trackLength] at hLong
    omega
  have hbeta : beta = yB := by
    by_contra hne
    rw [hXBdef, extraEdges] at hpXB
    have hadj := hpXB.1.2 beta ⟨hbY, hne⟩
    exact hbNotP hadj.symm
  have hab : alpha ≠ beta := hleap.2.2.1
  have haS : G.Adj alpha (↑(phi ⟨s', hsE⟩) : V) := by
    rw [hXBdef, extraEdges] at hsXB
    exact (hsXB.1.2 alpha ⟨haY, fun h => hab (h.trans hbeta.symm)⟩).symm
  have hNoCommon : ∀ e (he : e ∈ H.edgeSet), e ∈ trackEdges Bq →
      ¬ (G.Adj alpha (↑(phi ⟨e, he⟩) : V) ∧ G.Adj beta (↑(phi ⟨e, he⟩) : V)) := by
    intro e he heB
    exact no_common_neighbor_on_disjoint_track hG phi hBp hBp2 hc₂.symm hc₄
      (fun hw => (havoidP w₃ hw).2 rfl) (fun hw => (havoidP w₁ hw).1 rfl) h13.symm
      T1 hT1def hT1track hP5 (by
        rw [TrackToRungPath.trackRung_pathLength, trackLength]
        obtain ⟨k, hk⟩ := hevenP
        simp only [trackLength] at hk
        simp only [T1, List.length_cons, List.length_append, List.length_nil]
        exact ⟨k, by omega⟩)
      hdisjPQ (hYmajor alpha haY).1 (hYmajor beta hbY).1 hleap he heB
  have hT2 := hang_track hBq hBq2 hc₂ hc₄.symm
    (fun hw => (havoidQ w₂ hw).1 rfl) (fun hw => (havoidQ w₄ hw).2 rfl) h24
  let T2 := w₂ :: (Bq ++ [w₄])
  have hT2def : T2 = w₂ :: (Bq ++ [w₄]) := rfl
  have hT2track : IsTrackList H T2 := hT2.1.1
  have hT2len : T2.length = Bq.length + 2 := hT2.2.1
  have hT2five : 5 ≤ T2.length := by simp only [trackLength] at hlenQ; omega
  have hT2par : T2.length % 2 = 1 := by
    obtain ⟨k, hk⟩ := hevenQ
    simp only [trackLength] at hk
    omega
  have hhangQ := hang_edges (u := w₂) (v := w₄) hBq hBq2
  have hpairY : ∀ z ∈ ({alpha, beta} : Set V), z ∈ Y := by
    intro z hz
    rcases hz with h | h
    · exact h ▸ haY
    · exact h ▸ hbY
  have hcomplete_mono : ∀ e, e ∈ completeEdges G H K phi Y →
      e ∈ completeEdges G H K phi ({alpha, beta} : Set V) := by
    rintro e ⟨he, hc⟩
    exact ⟨he, fun z hz => hc z (hpairY z hz)⟩
  have hT2first : s(T2[0]'(by omega), T2[1]'(by omega)) ∈
      completeEdges G H K phi ({alpha, beta} : Set V) := by
    change s((w₂ :: (Bq ++ [w₄]))[0]'(by omega),
      (w₂ :: (Bq ++ [w₄]))[1]'(by omega)) ∈
        completeEdges G H K phi ({alpha, beta} : Set V)
    rw [hhangQ.1]
    exact hcomplete_mono b hbX
  have hT2last : s(T2[T2.length - 2]'(by omega), T2[T2.length - 1]'(by omega)) ∈
      completeEdges G H K phi ({alpha, beta} : Set V) := by
    change s((w₂ :: (Bq ++ [w₄]))[(w₂ :: (Bq ++ [w₄])).length - 2]'(by omega),
      (w₂ :: (Bq ++ [w₄]))[(w₂ :: (Bq ++ [w₄])).length - 1]'(by omega)) ∈
        completeEdges G H K phi ({alpha, beta} : Set V)
    rw [hhangQ.2.1, Sym2.eq_swap]
    exact hcomplete_mono d hdX
  have hT2internal : ∀ i : ℕ, 1 ≤ i → ∀ hi : i + 2 < T2.length,
      s(T2[i]'(by omega), T2[i + 1]'(by omega)) ∉
        completeEdges G H K phi ({alpha, beta} : Set V) := by
    intro i hi1 hi hcomp
    change s((w₂ :: (Bq ++ [w₄]))[i]'(by omega),
      (w₂ :: (Bq ++ [w₄]))[i + 1]'(by omega)) ∈
        completeEdges G H K phi ({alpha, beta} : Set V) at hcomp
    rw [hhangQ.2.2 i hi1 (by simpa [T2] using hi)] at hcomp
    obtain ⟨he, hc⟩ := hcomp
    have heB : s(Bq[i - 1]'(by omega), Bq[i]'(by omega)) ∈ trackEdges Bq := by
      refine ⟨i - 1, ?_, ?_⟩
      · have hilen : i + 2 < Bq.length + 2 := by simpa [T2] using hi
        omega
      apply congrArg (fun z => s(Bq[i - 1]'(by omega), z))
      apply geq
      omega
    exact hNoCommon _ he heB ⟨(hc alpha (by simp)).symm, (hc beta (by simp)).symm⟩
  have hpairAnti : AnticonnectedSet G ({alpha, beta} : Set V) := by
    apply (SimpleGraph.induce_pair_connected_of_adj (G := Gᶜ) ?_).preconnected
    rw [SimpleGraph.compl_adj]
    exact ⟨hab, hleap.2.2.2.1⟩
  obtain ⟨haQ, hbQ⟩ := second_hung_track_edges G hG phi hBq hBq2 hc₂ hc₄.symm
    (fun hw => (havoidQ w₂ hw).1 rfl) (fun hw => (havoidQ w₄ hw).2 rfl) h24
    T2 hT2def hT2track hT2five hT2par alpha beta hab (hYmajor alpha haY).1
    (hYmajor beta hbY).1 hpairAnti hT2first hT2last hT2internal
    (fun he => by
      have heq : (⟨s', hsE⟩ : ↑H.edgeSet) =
          ⟨s(Bq[Bq.length - 2]'(by omega), Bq[Bq.length - 1]'(by omega)), he⟩ := by
        apply Subtype.ext
        rfl
      simpa [s'] using congrArg (fun z : ↑H.edgeSet => (↑(phi z) : V)) heq ▸ haS)
    hNoCommon
  have hbNotPset : p ∉ {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      G.Adj beta (↑(phi ⟨e, he⟩) : V)} := by
    rintro ⟨he, hadj⟩
    exact hbNotP (by simpa only using hadj)
  have hbetaA : G.Adj beta (↑(phi ⟨a, haInc2.1⟩) : V) := by
    by_contra hn
    have haN : a ∉ {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        G.Adj beta (↑(phi ⟨e, he⟩) : V)} := by
      rintro ⟨he, hadj⟩
      exact hn (by simpa only using hadj)
    have heq := (hYmajor beta hbY).2 w₂ (by rw [hbv]; simp)
      ⟨hpInc, hbNotPset⟩ ⟨haInc2, haN⟩
    exact hpa heq
  have haNotQ : q ∉ {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      G.Adj alpha (↑(phi ⟨e, he⟩) : V)} := by
    rintro ⟨he, hadj⟩
    have heq := (haQ q he hqB).mp hadj
    have hi := (track_edge_injective hBq.1.2.1 (show 0 + 1 < Bq.length by omega)
      (show Bq.length - 2 + 1 < Bq.length by omega)).mp (heq.trans hsnorm.symm)
    omega
  have hqc : q ≠ c := by
    intro h
    have hw4 : w₄ ∉ q := trackEdge_avoids (fun hw => (havoidQ w₄ hw).2 rfl) hqB
    exact hw4 (h ▸ (by simp [c]))
  have halphaC : G.Adj alpha (↑(phi ⟨c, hcInc3.1⟩) : V) := by
    by_contra hn
    have hcN : c ∉ {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        G.Adj alpha (↑(phi ⟨e, he⟩) : V)} := by
      rintro ⟨he, hadj⟩
      exact hn (by simpa only using hadj)
    have heq := (hYmajor alpha haY).2 w₃ (by rw [hbv]; simp)
      ⟨hqInc, haNotQ⟩ ⟨hcInc3, hcN⟩
    exact hqc heq
  have hdeg : DegenerateAppearance J H := Or.inl ⟨hJiso,
    w₁, w₂, w₃, w₄, hnd, hc₁, hc₂, hc₃, hc₄, by rw [hbv]⟩
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hJiso, hdeg, beta, hbY, alpha, haY,
    (fun h => hleap.2.2.2.1 h.symm), w₁, w₂, w₃, w₄, a, b, c, d, p, q, r, s', hnd, hbv,
    hc₁, hc₂, hc₃, hc₄, rfl, rfl, rfl, rfl, hpInc, hpa, ?_, hqInc, ?_, hqc,
    hrInc, ?_, ?_, hsInc, ?_, hsb, ?_, ?_, ?_, ?_⟩)))
  · intro h
    have hw3 : w₃ ∉ p := trackEdge_avoids (fun hw => (havoidP w₃ hw).2 rfl) hpB
    exact hw3 (h ▸ (by simp [b]))
  · intro h
    have hw2 : w₂ ∉ q := trackEdge_avoids (fun hw => (havoidQ w₂ hw).1 rfl) hqB
    exact hw2 (h ▸ (by simp [b]))
  · intro h
    have hw3 : w₃ ∉ r := trackEdge_avoids (fun hw => (havoidP w₃ hw).2 rfl) hrB
    exact hw3 (h ▸ (by simp [c]))
  · intro h
    have hw1 : w₁ ∉ r := trackEdge_avoids (fun hw => (havoidP w₁ hw).1 rfl) hrB
    exact hw1 (h ▸ (by simp [d]))
  · intro h
    have hw4 : w₄ ∉ s' := trackEdge_avoids (fun hw => (havoidQ w₄ hw).2 rfl) hsB
    exact hw4 (h ▸ (by simp [d]))
  · -- lower neighbourhood of `beta`
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact ⟨haInc2.1, hbetaA⟩
    · obtain ⟨he, hc⟩ := hbX; exact ⟨he, (hc beta hbY).symm⟩
    · obtain ⟨he, hc⟩ := hdX; exact ⟨he, (hc beta hbY).symm⟩
    · exact ⟨hqE, (hbQ q hqE hqB).mpr rfl⟩
    · exact ⟨hrE, (hbP r hrE hrB).mpr rfl⟩
  · -- upper neighbourhood of `beta`
    rintro e ⟨he, hadj⟩
    rw [hedges] at he
    rcases he with (he | he) | he
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp [a, b, c, d]
    · have := (hbP e _ he).mp hadj
      change e = r at this
      simp [this]
    · have := (hbQ e _ he).mp hadj
      change e = q at this
      simp [this]
  · -- lower neighbourhood of `alpha`
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨he, hc⟩ := hbX; exact ⟨he, (hc alpha haY).symm⟩
    · exact ⟨hcInc3.1, halphaC⟩
    · obtain ⟨he, hc⟩ := hdX; exact ⟨he, (hc alpha haY).symm⟩
    · exact ⟨hpE, (haP p hpE hpB).mpr rfl⟩
    · exact ⟨hsE, haS⟩
  · -- upper neighbourhood of `alpha`
    rintro e ⟨he, hadj⟩
    rw [hedges] at he
    rcases he with (he | he) | he
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp [a, b, c, d]
    · have := (haP e _ he).mp hadj
      change e = p at this
      simp [this]
    · have := (haQ e _ he).mp hadj
      change e = s' at this
      simp [this]

/-- Orient the two extra-edge sets at the missing cycle edge, then invoke
`canonical_long_oriented`. -/
theorem canonical_long
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (phi : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K phi y)
    (hmin : ∀ Y₀ : Set V, Y₀ ⊂ Y → AnticonnectedSet G Y₀ →
      SaturatesLineGraph H (completeEdges G H K phi Y₀))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ z : V, z ∈ Q ↔ z ∈ Y) (hy : y₁ ≠ y₂)
    (hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (w₁ w₂ w₃ w₄ : Fin n) (hnd : [w₁, w₂, w₃, w₄].Nodup)
    (hbv : branchVertices H = ({w₁, w₂, w₃, w₄} : Set (Fin n)))
    (hc₁ : H.Adj w₁ w₂) (hc₂ : H.Adj w₂ w₃)
    (hc₃ : H.Adj w₃ w₄) (hc₄ : H.Adj w₄ w₁)
    (Bp Bq : List (Fin n))
    (hBp : IsTrackFrom H Bp w₂ w₄) (hBq : IsTrackFrom H Bq w₃ w₁)
    (hlenP : 2 ≤ trackLength Bp) (hlenQ : 2 ≤ trackLength Bq)
    (hevenP : Even (trackLength Bp)) (hevenQ : Even (trackLength Bq))
    (hdisjPQ : ∀ z ∈ Bp, z ∉ Bq)
    (havoidP : ∀ z ∈ Bp, z ≠ w₁ ∧ z ≠ w₃)
    (havoidQ : ∀ z ∈ Bq, z ≠ w₂ ∧ z ≠ w₄)
    (hedges : H.edgeSet =
      ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} :
        Set (Sym2 (Fin n))) ∪ trackEdges Bp ∪ trackEdges Bq)
    (hLong : 4 ≤ trackLength Bp)
    (hXC : completeEdges G H K phi Y ⊆
      ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} :
        Set (Sym2 (Fin n))))
    (haNotX : s(w₁, w₂) ∉ completeEdges G H K phi Y)
    (hbX : s(w₂, w₃) ∈ completeEdges G H K phi Y)
    (hdX : s(w₄, w₁) ∈ completeEdges G H K phi Y) :
    Thm61Concl G m J n H K phi Y := by
  classical
  let X₁ := extraEdges G H K phi Y y₁
  let X₂ := extraEdges G H K phi Y y₂
  obtain ⟨-, -, -, -, -, hdisj₁₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K phi Y hmin y₁ y₂ Q hQ hQY hy
  have hBp2 : 2 ≤ Bp.length := by simp only [trackLength] at hlenP; omega
  let p := s(Bp[0]'(by omega), Bp[1]'(by omega))
  have hpE : p ∈ H.edgeSet := by
    dsimp only [p]
    exact TrackToRungPath.trackEdge_mem_edgeSet hBp.1 0 (by omega)
  have hpB : p ∈ trackEdges Bp := ⟨0, by omega, rfl⟩
  have hpInc : p ∈ incidentEdges H w₂ := by
    refine ⟨hpE, ?_⟩
    dsimp only [p]
    simp only [Sym2.mem_iff]
    exact Or.inl (head_getElem hBp.2.1 (by omega)).symm
  have hpa : p ≠ s(w₁, w₂) := by
    intro h
    have hw1 : w₁ ∉ p := trackEdge_avoids (fun hw => (havoidP w₁ hw).1 rfl) hpB
    exact hw1 (h ▸ (by simp))
  have hpNotX : p ∉ completeEdges G H K phi Y := by
    intro hpX
    have hpC := hXC hpX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpC
    have hw1 : w₁ ∉ p := trackEdge_avoids (fun hw => (havoidP w₁ hw).1 rfl) hpB
    have hw3 : w₃ ∉ p := trackEdge_avoids (fun hw => (havoidP w₃ hw).2 rfl) hpB
    rcases hpC with h | h | h | h
    · exact hw1 (h ▸ (by simp))
    · exact hw3 (h ▸ (by simp))
    · exact hw3 (h ▸ (by simp))
    · exact hw1 (h ▸ (by simp))
  have haInc : s(w₁, w₂) ∈ incidentEdges H w₂ :=
    ⟨(SimpleGraph.mem_edgeSet H).mpr hc₁, by simp⟩
  rcases split_two_extra (by rw [hbv]; simp) hsat₁ hsat₂ hdisj₁₂
    haInc hpInc hpa.symm haNotX hpNotX with h | h
  · exact canonical_long_oriented G hG m J n H K phi Y hYanti hYmajor
      y₁ y₂ X₁ X₂ rfl rfl hdisj₁₂ hsat₁ hsat₂ hJiso
      w₁ w₂ w₃ w₄ hnd hbv hc₁ hc₂ hc₃ hc₄ Bp Bq hBp hBq hlenP hlenQ
      hevenP hevenQ hdisjPQ havoidP havoidQ hedges hLong hXC haNotX hbX hdX h.1 h.2
  · exact canonical_long_oriented G hG m J n H K phi Y hYanti hYmajor
      y₂ y₁ X₂ X₁ rfl rfl hdisj₁₂.symm hsat₂ hsat₁ hJiso
      w₁ w₂ w₃ w₄ hnd hbv hc₁ hc₂ hc₃ hc₄ Bp Bq hBp hBq hlenP hlenQ
      hevenP hevenQ hdisjPQ havoidP havoidQ hedges hLong hXC haNotX hbX hdX h.1 h.2

/-- The canonical missing-edge case.  If both diagonal branches are short, use the six-vertex
outcome.  Otherwise reflect the four-cycle if needed so that the first diagonal is long. -/
theorem canonical_case
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (phi : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K phi y)
    (hmin : ∀ Y₀ : Set V, Y₀ ⊂ Y → AnticonnectedSet G Y₀ →
      SaturatesLineGraph H (completeEdges G H K phi Y₀))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ z : V, z ∈ Q ↔ z ∈ Y) (hy : y₁ ≠ y₂)
    (hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (hsub4 : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H) (hbip : H.IsBipartite)
    (w₁ w₂ w₃ w₄ : Fin n) (hnd : [w₁, w₂, w₃, w₄].Nodup)
    (hbv : branchVertices H = ({w₁, w₂, w₃, w₄} : Set (Fin n)))
    (hc₁ : H.Adj w₁ w₂) (hc₂ : H.Adj w₂ w₃)
    (hc₃ : H.Adj w₃ w₄) (hc₄ : H.Adj w₄ w₁)
    (hXC : completeEdges G H K phi Y ⊆
      ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} :
        Set (Sym2 (Fin n))))
    (haNotX : s(w₁, w₂) ∉ completeEdges G H K phi Y)
    (hbX : s(w₂, w₃) ∈ completeEdges G H K phi Y)
    (hdX : s(w₄, w₁) ∈ completeEdges G H K phi Y) :
    Thm61Concl G m J n H K phi Y := by
  classical
  obtain ⟨Bp, Bq, hBp, hBq, hlenP, hlenQ, hevenP, hevenQ, hdisjPQ,
      havoidP, havoidQ, hedges⟩ :=
    k4_structure hsub4 hbip w₁ w₂ w₃ w₄ hnd hbv hc₁ hc₂ hc₃ hc₄
  by_cases hp2 : trackLength Bp = 2
  · by_cases hq2 : trackLength Bq = 2
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hJiso,
        Thm61Claim1Card.card_six_of_short_diagonals hsub4 w₁ w₂ w₃ w₄ hnd
          Bp Bq hBp hBq hp2 hq2 hdisjPQ havoidP havoidQ hedges⟩)))
    · have hLongQ : 4 ≤ trackLength Bq := by
        obtain ⟨k, hk⟩ := hevenQ
        omega
      have hnd' : [w₂, w₁, w₄, w₃].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
          List.nodup_singleton] at hnd ⊢
        aesop
      have hbv' : branchVertices H = ({w₂, w₁, w₄, w₃} : Set (Fin n)) := by
        rw [hbv]
        ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        aesop
      have hP' : IsTrackFrom H Bq.reverse w₁ w₃ :=
        TrackSlice.isTrackFrom_reverse hBq
      have hQ' : IsTrackFrom H Bp.reverse w₄ w₂ :=
        TrackSlice.isTrackFrom_reverse hBp
      have hdisj' : ∀ z ∈ Bq.reverse, z ∉ Bp.reverse := by
        intro z hzQ hzP
        rw [List.mem_reverse] at hzQ hzP
        exact hdisjPQ z hzP hzQ
      have hAvoidP' : ∀ z ∈ Bq.reverse, z ≠ w₂ ∧ z ≠ w₄ := by
        intro z hz
        rw [List.mem_reverse] at hz
        exact havoidQ z hz
      have hAvoidQ' : ∀ z ∈ Bp.reverse, z ≠ w₁ ∧ z ≠ w₃ := by
        intro z hz
        rw [List.mem_reverse] at hz
        exact havoidP z hz
      have e21 : s(w₂, w₁) = s(w₁, w₂) := Sym2.eq_swap
      have e14 : s(w₁, w₄) = s(w₄, w₁) := Sym2.eq_swap
      have e43 : s(w₄, w₃) = s(w₃, w₄) := Sym2.eq_swap
      have e32 : s(w₃, w₂) = s(w₂, w₃) := Sym2.eq_swap
      have hcycle :
          ({s(w₂, w₁), s(w₁, w₄), s(w₄, w₃), s(w₃, w₂)} :
            Set (Sym2 (Fin n))) =
          ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} :
            Set (Sym2 (Fin n))) := by
        ext e
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, e21, e14, e43, e32]
        aesop
      have hedges' : H.edgeSet =
          ({s(w₂, w₁), s(w₁, w₄), s(w₄, w₃), s(w₃, w₂)} :
            Set (Sym2 (Fin n))) ∪ trackEdges Bq.reverse ∪ trackEdges Bp.reverse := by
        rw [hcycle, SubdivisionCounting.trackEdges_reverse,
          SubdivisionCounting.trackEdges_reverse, hedges]
        ext e
        simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
        aesop
      have hXC' : completeEdges G H K phi Y ⊆
          ({s(w₂, w₁), s(w₁, w₄), s(w₄, w₃), s(w₃, w₂)} :
            Set (Sym2 (Fin n))) := by
        rw [hcycle]
        exact hXC
      exact canonical_long G hG m J n H K phi Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy
        hJiso w₂ w₁ w₄ w₃ hnd' hbv' hc₁.symm hc₄.symm hc₃.symm hc₂.symm
        Bq.reverse Bp.reverse hP' hQ' (by simpa [trackLength] using hlenQ)
        (by simpa [trackLength] using hlenP) (by simpa [trackLength] using hevenQ)
        (by simpa [trackLength] using hevenP) hdisj' hAvoidP' hAvoidQ' hedges'
        (by simpa [trackLength] using hLongQ) hXC' (by simpa [e21] using haNotX)
        (by simpa [e14] using hdX) (by simpa [e32] using hbX)
  · have hLongP : 4 ≤ trackLength Bp := by
      obtain ⟨k, hk⟩ := hevenP
      omega
    exact canonical_long G hG m J n H K phi Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy
      hJiso w₁ w₂ w₃ w₄ hnd hbv hc₁ hc₂ hc₃ hc₄ Bp Bq hBp hBq hlenP hlenQ
      hevenP hevenQ hdisjPQ havoidP havoidQ hedges hLongP hXC haNotX hbX hdX

end Workspace.ProofLemmas.Thm61Claim1Core
