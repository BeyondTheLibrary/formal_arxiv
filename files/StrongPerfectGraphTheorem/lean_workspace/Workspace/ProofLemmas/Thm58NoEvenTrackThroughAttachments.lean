import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.SubdivisionCounting

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58NoEvenTrackThroughAttachments

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm58NoEvenTrackThroughAttachments
    (G : SimpleGraph V) (hG : Berge G)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K)
    (y : V) (hyK : y ∉ K) :
    ¬ ∃ (q : List (Fin n)) (_hq : 5 ≤ q.length),
      IsTrackList H q ∧ Even (trackLength q) ∧
      s(q[0], q[1]) ∈ {f : Sym2 (Fin n) | ∃ hf : f ∈ H.edgeSet,
        (↑(φ ⟨f, hf⟩) : V) ∈ attachments G {y} K} ∧
      s(q[q.length - 2], q[q.length - 1]) ∈ {f : Sym2 (Fin n) | ∃ hf : f ∈ H.edgeSet,
        (↑(φ ⟨f, hf⟩) : V) ∈ attachments G {y} K} ∧
      ∀ e ∈ trackEdges q, e ≠ s(q[0], q[1]) →
        e ≠ s(q[q.length - 2], q[q.length - 1]) →
        e ∉ {f : Sym2 (Fin n) | ∃ hf : f ∈ H.edgeSet,
          (↑(φ ⟨f, hf⟩) : V) ∈ attachments G {y} K} := by
  rintro ⟨q, hq5, hqt, hqeven, hfirst, hlast, hother⟩
  -- the induced path of `G` carried by the track (`TrackToRungPath`)
  have hlen1 : 1 ≤ trackLength q := by simp only [trackLength]; omega
  have hRlen : (TrackToRungPath.trackRung φ q hqt).length = trackLength q :=
    TrackToRungPath.trackRung_length φ q hqt
  have hRlen' : (TrackToRungPath.trackRung φ q hqt).length = q.length - 1 := by
    rw [hRlen]; rfl
  have hRpos : 0 < (TrackToRungPath.trackRung φ q hqt).length := by omega
  have hpath : IsPathList G (TrackToRungPath.trackRung φ q hqt) :=
    TrackToRungPath.trackRung_isPathList φ q hqt hlen1
  obtain ⟨s, t, hpf⟩ := TrackToRungPath.trackRung_exists_isPathFrom φ q hqt hlen1
  have hnd : q.Nodup := hqt.2.1
  -- `y` is not a vertex of the rung
  have hyR : y ∉ TrackToRungPath.trackRung φ q hqt := fun hc =>
    hyK (TrackToRungPath.trackRung_subset_K φ q hqt y hc)
  -- an attachment of `y` is a `G`-neighbour of `y`
  have hattach : ∀ (f : Sym2 (Fin n)) (hf : f ∈ H.edgeSet),
      (↑(φ ⟨f, hf⟩) : V) ∈ attachments G {y} K → G.Adj y (↑(φ ⟨f, hf⟩) : V) := by
    intro f hf hmem
    obtain ⟨-, z, hz, hadj⟩ := hmem
    have : z = y := hz
    subst this
    exact hadj.symm
  -- the first vertex of the rung is the `φ`-image of the first edge of the track
  have he0 : s(q[0]'(by omega), q[0 + 1]'(by omega)) ∈ H.edgeSet :=
    TrackToRungPath.trackEdge_mem_edgeSet hqt 0 (by omega)
  have hR0 : (TrackToRungPath.trackRung φ q hqt)[0]'hRpos
      = (↑(φ ⟨s(q[0]'(by omega), q[0 + 1]'(by omega)), he0⟩) : V) :=
    TrackToRungPath.trackRung_getElem φ q hqt 0 hRpos (by omega) he0
  have hxu : G.Adj y s := by
    have hs : (TrackToRungPath.trackRung φ q hqt)[0]'hRpos = s :=
      PathBasics.getElem_zero_of_head? hpf.2.1 hRpos
    obtain ⟨hf, hmem⟩ := hfirst
    have := hattach _ he0 hmem
    rw [← hs, hR0]
    exact this
  -- the last vertex of the rung is the `φ`-image of the last edge of the track
  have hidx : q.length - 2 + 1 < q.length := by omega
  have heL : s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'hidx) ∈ H.edgeSet :=
    TrackToRungPath.trackEdge_mem_edgeSet hqt (q.length - 2) hidx
  have hqL : q[q.length - 2 + 1]'hidx = q[q.length - 1]'(by omega) :=
    SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
  have hRlast : (TrackToRungPath.trackRung φ q hqt)[(TrackToRungPath.trackRung φ q hqt).length - 1]'
        (by omega)
      = (↑(φ ⟨s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'hidx), heL⟩) : V) := by
    have hii : (TrackToRungPath.trackRung φ q hqt).length - 1 = q.length - 2 := by omega
    rw [SubdivisionCounting.getElem_eq_of_index_eq (TrackToRungPath.trackRung φ q hqt) hii
      (by omega) (by omega)]
    exact TrackToRungPath.trackRung_getElem φ q hqt (q.length - 2) (by omega) hidx heL
  have hxw : G.Adj y t := by
    have ht : (TrackToRungPath.trackRung φ q hqt)[(TrackToRungPath.trackRung φ q hqt).length - 1]'
        (by omega) = t :=
      PathBasics.getElem_last_of_getLast? hpf.2.2 hRpos
    obtain ⟨hf, hmem⟩ := hlast
    have hsub : (⟨s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'hidx), heL⟩ : ↥H.edgeSet)
        = ⟨s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)), hf⟩ := by
      apply Subtype.ext
      simp only [hqL]
    have hmem' : (↑(φ ⟨s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'hidx), heL⟩) : V)
        ∈ attachments G {y} K := by
      rw [hsub]; exact hmem
    have := hattach _ heL hmem'
    rw [← ht, hRlast]
    exact this
  -- no interior vertex of the rung is a neighbour of `y`
  have hxint : ∀ z ∈ SPGT.interior (TrackToRungPath.trackRung φ q hqt), ¬ G.Adj y z := by
    intro z hz hadj
    obtain ⟨k, hk, hk1, hk2, hkz⟩ := PathBasics.exists_getElem_of_mem_interior hpath hz
    have hkq : k + 1 < q.length := by omega
    have hek : s(q[k]'(by omega), q[k + 1]'hkq) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hqt k hkq
    have hRk : (TrackToRungPath.trackRung φ q hqt)[k]'hk
        = (↑(φ ⟨s(q[k]'(by omega), q[k + 1]'hkq), hek⟩) : V) :=
      TrackToRungPath.trackRung_getElem φ q hqt k hk hkq hek
    have hmemE : s(q[k]'(by omega), q[k + 1]'hkq) ∈ trackEdges q := ⟨k, hkq, rfl⟩
    have hinj : ∀ (a b : ℕ) (ha : a < q.length) (hb : b < q.length),
        (q[a]'ha = q[b]'hb ↔ a = b) := fun a b ha hb => hnd.getElem_inj_iff
    have hne1 : s(q[k]'(by omega), q[k + 1]'hkq) ≠ s(q[0]'(by omega), q[1]'(by omega)) := by
      intro hcon
      rcases Sym2.eq_iff.mp hcon with ⟨e1, -⟩ | ⟨e1, e2⟩
      · have : k = 0 := (hinj _ _ _ _).mp e1
        omega
      · have p1 : k = 1 := (hinj _ _ _ _).mp e1
        have p2 : k + 1 = 0 := (hinj _ _ _ _).mp e2
        omega
    have hne2 : s(q[k]'(by omega), q[k + 1]'hkq)
        ≠ s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)) := by
      intro hcon
      rcases Sym2.eq_iff.mp hcon with ⟨e1, -⟩ | ⟨e1, e2⟩
      · have : k = q.length - 2 := (hinj _ _ _ _).mp e1
        omega
      · have p1 : k = q.length - 1 := (hinj _ _ _ _).mp e1
        have p2 : k + 1 = q.length - 2 := (hinj _ _ _ _).mp e2
        omega
    have hno := hother _ hmemE hne1 hne2
    refine hno ⟨hek, ?_⟩
    refine ⟨Subtype.coe_prop _, y, rfl, ?_⟩
    rw [← hRk, hkz]
    exact hadj.symm
  -- the rung closes into an odd hole through `y`
  have h4 : 4 ≤ (TrackToRungPath.trackRung φ q hqt).length := by omega
  have hev := PrismBasics.even_of_path_closed_by_vertex hG hpf h4 hyR hxu hxw hxint
  rw [hRlen] at hev
  rcases hqeven with ⟨m, hm⟩
  rcases hev with ⟨m', hm'⟩
  omega

end Workspace.ProofLemmas.Thm58NoEvenTrackThroughAttachments
