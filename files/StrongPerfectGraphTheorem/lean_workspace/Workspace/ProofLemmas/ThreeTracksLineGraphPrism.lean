import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Prisms
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Three tracks with common ends give a prism in the line graph

This is the elementary line-graph bridge used in the proof of 7.5.  If three tracks of `H`
join the same two nonadjacent vertices and meet only in those vertices, their ordered edge
lists are three induced paths in `L(H)`.  The first edges form one triangle, the last edges form
the other, and there are no other edges between the three paths.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.ThreeTracksLineGraphPrism

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.TrackToRungPath

variable {V W : Type*}

def firstTrackEdge (q : List W) (h : 2 ≤ q.length) : Sym2 W :=
  s(q[0]'(by omega), q[1]'(by omega))

def lastTrackEdge (q : List W) (h : 2 ≤ q.length) : Sym2 W :=
  s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega))

theorem firstTrackEdge_mem {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    (h : 2 ≤ q.length) : firstTrackEdge q h ∈ H.edgeSet := by
  exact hq.2.2 0 (by omega)

theorem lastTrackEdge_mem {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q)
    (h : 2 ≤ q.length) : lastTrackEdge q h ∈ H.edgeSet := by
  have hi : q.length - 2 + 1 = q.length - 1 := by omega
  simpa only [lastTrackEdge, SubdivisionCounting.getElem_eq_of_index_eq q hi (by omega)
    (by omega)] using hq.2.2 (q.length - 2) (by omega)

def firstRungVertex {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q)
    (h : 2 ≤ q.length) : V :=
  (φ ⟨firstTrackEdge q h, firstTrackEdge_mem hq h⟩ : V)

def lastRungVertex {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (q : List W) (hq : IsTrackList H q)
    (h : 2 ≤ q.length) : V :=
  (φ ⟨lastTrackEdge q h, lastTrackEdge_mem hq h⟩ : V)

private theorem head_getElem {α : Type*} {q : List α} {a : α}
    (h : q.head? = some a) (hpos : 0 < q.length) : q[0]'hpos = a := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos] at h
  exact Option.some_injective _ h

private theorem last_getElem {α : Type*} {q : List α} {b : α}
    (h : q.getLast? = some b) (hpos : 0 < q.length) :
    q[q.length - 1]'(by omega) = b := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
  exact Option.some_injective _ h

theorem firstTrackEdge_mem_trackEdges {q : List W} (h : 2 ≤ q.length) :
    firstTrackEdge q h ∈ trackEdges q := by
  exact ⟨0, by omega, rfl⟩

theorem lastTrackEdge_mem_trackEdges {q : List W} (h : 2 ≤ q.length) :
    lastTrackEdge q h ∈ trackEdges q := by
  have hi : q.length - 2 + 1 = q.length - 1 := by omega
  refine ⟨q.length - 2, by omega, ?_⟩
  simp only [lastTrackEdge]
  congr 1
  exact (SubdivisionCounting.getElem_eq_of_index_eq q hi (by omega) (by omega)).symm

theorem firstTrackEdge_contains {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (h : 2 ≤ q.length) : a ∈ firstTrackEdge q h := by
  have h0 : q[0]'(by omega) = a := head_getElem hq.2.1 (by omega)
  rw [firstTrackEdge, h0]
  exact Sym2.mem_mk_left _ _

theorem lastTrackEdge_contains {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (h : 2 ≤ q.length) : b ∈ lastTrackEdge q h := by
  have hl : q[q.length - 1]'(by omega) = b := last_getElem hq.2.2 (by omega)
  rw [lastTrackEdge, hl]
  exact Sym2.mem_mk_right _ _

private theorem mem_track_of_mem_trackEdges {q : List W} {e : Sym2 W}
    (he : e ∈ trackEdges q) {w : W} (hw : w ∈ e) : w ∈ q := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

theorem edge_eq_firstTrackEdge {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (h : 2 ≤ q.length) {e : Sym2 W}
    (he : e ∈ trackEdges q) (ha : a ∈ e) : e = firstTrackEdge q h := by
  obtain ⟨i, hi, rfl⟩ := he
  have h0 : q[0]'(by omega) = a := head_getElem hq.2.1 (by omega)
  have hm : a = q[i]'(by omega) ∨ a = q[i + 1]'hi := by simpa using ha
  have hi0 : i = 0 := by
    rcases hm with hm | hm
    · have helem : q[0]'(by omega) = q[i]'(by omega) := h0.trans hm
      exact hq.1.2.1.getElem_inj_iff.mp helem.symm
    · have helem : q[0]'(by omega) = q[i + 1]'hi := h0.trans hm
      have hz := hq.1.2.1.getElem_inj_iff.mp helem
      omega
  subst i
  rfl

theorem edge_eq_lastTrackEdge {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (h : 2 ≤ q.length) {e : Sym2 W}
    (he : e ∈ trackEdges q) (hb : b ∈ e) : e = lastTrackEdge q h := by
  obtain ⟨i, hi, rfl⟩ := he
  have hl : q[q.length - 1]'(by omega) = b := last_getElem hq.2.2 (by omega)
  have hm : b = q[i]'(by omega) ∨ b = q[i + 1]'hi := by simpa using hb
  have hil : i = q.length - 2 := by
    rcases hm with hm | hm
    · have helem : q[q.length - 1]'(by omega) = q[i]'(by omega) := hl.trans hm
      have hz := hq.1.2.1.getElem_inj_iff.mp helem
      omega
    · have helem : q[q.length - 1]'(by omega) = q[i + 1]'hi := hl.trans hm
      have hz := hq.1.2.1.getElem_inj_iff.mp helem
      omega
  subst i
  have hi' : q.length - 2 + 1 = q.length - 1 := by omega
  simp only [lastTrackEdge]
  congr 1
  exact SubdivisionCounting.getElem_eq_of_index_eq q hi' (by omega) (by omega)

/-- Membership in a rung is exactly membership of the corresponding edge in the track. -/
theorem mem_trackRung_iff {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} (hq : IsTrackList H q) {x : V} :
    x ∈ trackRung φ q hq ↔ ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges q ∧ x = (φ ⟨e, he⟩ : V) := by
  constructor
  · intro hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    change e ∈ trackEdgeVerts H q hq at he
    simp only [trackEdgeVerts, List.mem_ofFn] at he
    obtain ⟨j, hj⟩ := he
    refine ⟨e, e.2, ⟨j.1, ?_, ?_⟩, rfl⟩
    · have := j.2
      simp only [trackLength] at this
      omega
    · exact congrArg Subtype.val hj.symm
  · rintro ⟨e, he, ⟨i, hi, hie⟩, rfl⟩
    apply List.mem_map.mpr
    have hidx : i < (trackEdgeVerts H q hq).length := by
      simp only [trackEdgeVerts, List.length_ofFn, trackLength]
      omega
    let f : H.edgeSet := (trackEdgeVerts H q hq)[i]'hidx
    have hfe : f = ⟨e, he⟩ := by
      apply Subtype.ext
      simpa [f, trackEdgeVerts] using hie.symm
    exact ⟨f, List.getElem_mem _, by rw [hfe]⟩

theorem firstRungVertex_mem {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} (hq : IsTrackList H q)
    (h : 2 ≤ q.length) : firstRungVertex φ q hq h ∈ trackRung φ q hq := by
  apply (mem_trackRung_iff φ hq).mpr
  exact ⟨firstTrackEdge q h, firstTrackEdge_mem hq h,
    firstTrackEdge_mem_trackEdges h, rfl⟩

theorem lastRungVertex_mem {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} (hq : IsTrackList H q)
    (h : 2 ≤ q.length) : lastRungVertex φ q hq h ∈ trackRung φ q hq := by
  apply (mem_trackRung_iff φ hq).mpr
  exact ⟨lastTrackEdge q h, lastTrackEdge_mem hq h,
    lastTrackEdge_mem_trackEdges h, rfl⟩

theorem trackRung_isPathFrom_ends {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (h : 2 ≤ q.length) :
    IsPathFrom G (trackRung φ q hq.1)
      (firstRungVertex φ q hq.1 h) (lastRungVertex φ q hq.1 h) := by
  have hpath : IsPathList G (trackRung φ q hq.1) :=
    trackRung_isPathList φ q hq.1 (by simp only [trackLength]; omega)
  refine ⟨hpath, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
      rw [trackRung_length]; simp only [trackLength]; omega)]
    congr 1
    exact trackRung_getElem φ q hq.1 0 (by
      rw [trackRung_length]; simp only [trackLength]; omega) (by omega)
      (firstTrackEdge_mem hq.1 h)
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by
      rw [trackRung_length]; simp only [trackLength]; omega)]
    congr 1
    have hidx : (trackRung φ q hq.1).length - 1 = q.length - 2 := by
      rw [trackRung_length]
      simp only [trackLength]
      omega
    rw [SubdivisionCounting.getElem_eq_of_index_eq _ hidx (by
      rw [trackRung_length]; simp only [trackLength]; omega) (by
      rw [trackRung_length]; simp only [trackLength]; omega)]
    have hi : q.length - 2 + 1 = q.length - 1 := by omega
    have heRaw : s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)) ∈
        H.edgeSet := hq.1.2.2 (q.length - 2) (by omega)
    rw [trackRung_getElem φ q hq.1 (q.length - 2) (by
      rw [trackRung_length]; simp only [trackLength]; omega) (by omega) heRaw]
    apply congrArg (fun e : H.edgeSet => (φ e : V))
    apply Subtype.ext
    simp only [lastTrackEdge]
    congr 1
    exact SubdivisionCounting.getElem_eq_of_index_eq q hi (by omega) (by omega)

/-- An odd track between nonadjacent ends has at least three edges. -/
theorem three_le_trackLength_of_odd_of_nonadj {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) (hodd : Odd (trackLength q))
    (hnadj : ¬ H.Adj a b) : 3 ≤ trackLength q := by
  have hne1 : trackLength q ≠ 1 := by
    intro hlen
    have hqLen : q.length = 2 := by
      simp only [trackLength] at hlen
      have hpos : 0 < q.length := List.length_pos_of_ne_nil hq.1.1
      omega
    have h0 : q[0]'(by omega) = a := head_getElem hq.2.1 (by omega)
    have h1 : q[1]'(by omega) = b := by
      have hl := last_getElem hq.2.2 (by omega)
      have hi : q.length - 1 = 1 := by omega
      exact (SubdivisionCounting.getElem_eq_of_index_eq q hi (by omega) (by omega)).symm.trans hl
    exact hnadj (by
      have hadj := hq.1.2.2 0 (by omega)
      rwa [h0, h1] at hadj)
  obtain ⟨k, hk⟩ := hodd
  omega

private theorem first_edges_ne {H : SimpleGraph W} {p q : List W} {a b : W}
    (hp : IsTrackFrom H p a b) (hq : IsTrackFrom H q a b)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hab : a ≠ b) (hnadj : ¬ H.Adj a b)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a ∨ z = b) :
    firstTrackEdge p hp2 ≠ firstTrackEdge q hq2 := by
  intro heq
  have hpE := firstTrackEdge_mem hp.1 hp2
  have ha : a ∈ firstTrackEdge p hp2 := firstTrackEdge_contains hp hp2
  have hx : p[1]'(by omega) ∈ firstTrackEdge p hp2 := by
    rw [firstTrackEdge]
    exact Sym2.mem_mk_right _ _
  have hxp : p[1]'(by omega) ∈ p := List.getElem_mem _
  have hx' : p[1]'(by omega) ∈ firstTrackEdge q hq2 := by
    rw [← heq]
    exact hx
  have hxq : p[1]'(by omega) ∈ q :=
    mem_track_of_mem_trackEdges (firstTrackEdge_mem_trackEdges hq2) hx'
  rcases hmeet _ hxp hxq with hxa | hxb
  · have h0 : p[0]'(by omega) = a := head_getElem hp.2.1 (by omega)
    have helem : p[0]'(by omega) = p[1]'(by omega) := h0.trans hxa.symm
    have := hp.1.2.1.getElem_inj_iff.mp helem
    omega
  · have heab : firstTrackEdge p hp2 = s(a, b) :=
      (Sym2.mem_and_mem_iff hab).mp ⟨ha, hxb ▸ hx⟩
    apply hnadj
    show s(a, b) ∈ H.edgeSet
    rw [← heab]
    exact hpE

private theorem last_edges_ne {H : SimpleGraph W} {p q : List W} {a b : W}
    (hp : IsTrackFrom H p a b) (hq : IsTrackFrom H q a b)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hab : a ≠ b) (hnadj : ¬ H.Adj a b)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a ∨ z = b) :
    lastTrackEdge p hp2 ≠ lastTrackEdge q hq2 := by
  intro heq
  have hpE := lastTrackEdge_mem hp.1 hp2
  have hb : b ∈ lastTrackEdge p hp2 := lastTrackEdge_contains hp hp2
  have hx : p[p.length - 2]'(by omega) ∈ lastTrackEdge p hp2 := by
    rw [lastTrackEdge]
    exact Sym2.mem_mk_left _ _
  have hxp : p[p.length - 2]'(by omega) ∈ p := List.getElem_mem _
  have hx' : p[p.length - 2]'(by omega) ∈ lastTrackEdge q hq2 := by
    rw [← heq]
    exact hx
  have hxq : p[p.length - 2]'(by omega) ∈ q :=
    mem_track_of_mem_trackEdges (lastTrackEdge_mem_trackEdges hq2) hx'
  rcases hmeet _ hxp hxq with hxa | hxb
  · have heab : lastTrackEdge p hp2 = s(a, b) :=
      (Sym2.mem_and_mem_iff hab).mp ⟨hxa ▸ hx, hb⟩
    apply hnadj
    show s(a, b) ∈ H.edgeSet
    rw [← heab]
    exact hpE
  · have hl : p[p.length - 1]'(by omega) = b := last_getElem hp.2.2 (by omega)
    have helem : p[p.length - 1]'(by omega) = p[p.length - 2]'(by omega) :=
      hl.trans hxb.symm
    have := hp.1.2.1.getElem_inj_iff.mp helem
    omega

private theorem first_last_ne {H : SimpleGraph W} {p q : List W} {a b : W}
    (hp : IsTrackFrom H p a b) (hq : IsTrackFrom H q a b)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hab : a ≠ b) (hnadj : ¬ H.Adj a b) :
    firstTrackEdge p hp2 ≠ lastTrackEdge q hq2 := by
  intro heq
  have ha : a ∈ firstTrackEdge p hp2 := firstTrackEdge_contains hp hp2
  have hb : b ∈ lastTrackEdge q hq2 := lastTrackEdge_contains hq hq2
  have heab : firstTrackEdge p hp2 = s(a, b) :=
    (Sym2.mem_and_mem_iff hab).mp ⟨ha, heq ▸ hb⟩
  apply hnadj
  show s(a, b) ∈ H.edgeSet
  rw [← heab]
  exact firstTrackEdge_mem hp.1 hp2

private theorem rung_cross {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {p q : List W} {a b : W}
    (hp : IsTrackFrom H p a b) (hq : IsTrackFrom H q a b)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hab : a ≠ b) (hnadj : ¬ H.Adj a b)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a ∨ z = b) :
    ∀ x ∈ trackRung φ p hp.1, ∀ y ∈ trackRung φ q hq.1,
      (G.Adj x y ↔
        (x = firstRungVertex φ p hp.1 hp2 ∧ y = firstRungVertex φ q hq.1 hq2) ∨
        (x = lastRungVertex φ p hp.1 hp2 ∧ y = lastRungVertex φ q hq.1 hq2)) := by
  intro x hx y hy
  obtain ⟨e, heE, hep, rfl⟩ := (mem_trackRung_iff φ hp.1).mp hx
  obtain ⟨f, hfE, hfq, rfl⟩ := (mem_trackRung_iff φ hq.1).mp hy
  have hmap :
      G.Adj (φ ⟨e, heE⟩ : V) (φ ⟨f, hfE⟩ : V) ↔
        H.lineGraph.Adj ⟨e, heE⟩ ⟨f, hfE⟩ := φ.map_rel_iff
  rw [hmap, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hef, z, hze, hzf⟩
    have hzp : z ∈ p := mem_track_of_mem_trackEdges hep hze
    have hzq : z ∈ q := mem_track_of_mem_trackEdges hfq hzf
    rcases hmeet z hzp hzq with rfl | rfl
    · left
      constructor
      · apply congrArg (fun t : H.edgeSet => (φ t : V))
        apply Subtype.ext
        exact edge_eq_firstTrackEdge hp hp2 hep hze
      · apply congrArg (fun t : H.edgeSet => (φ t : V))
        apply Subtype.ext
        exact edge_eq_firstTrackEdge hq hq2 hfq hzf
    · right
      constructor
      · apply congrArg (fun t : H.edgeSet => (φ t : V))
        apply Subtype.ext
        exact edge_eq_lastTrackEdge hp hp2 hep hze
      · apply congrArg (fun t : H.edgeSet => (φ t : V))
        apply Subtype.ext
        exact edge_eq_lastTrackEdge hq hq2 hfq hzf
  · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · have hxe : (⟨e, heE⟩ : H.edgeSet) =
          ⟨firstTrackEdge p hp2, firstTrackEdge_mem hp.1 hp2⟩ := by
        apply φ.injective
        apply Subtype.ext
        exact hx
      have hye : (⟨f, hfE⟩ : H.edgeSet) =
          ⟨firstTrackEdge q hq2, firstTrackEdge_mem hq.1 hq2⟩ := by
        apply φ.injective
        apply Subtype.ext
        exact hy
      rw [hxe, hye]
      exact ⟨fun h => first_edges_ne hp hq hp2 hq2 hab hnadj hmeet
          (congrArg Subtype.val h), a,
        firstTrackEdge_contains hp hp2, firstTrackEdge_contains hq hq2⟩
    · have hxe : (⟨e, heE⟩ : H.edgeSet) =
          ⟨lastTrackEdge p hp2, lastTrackEdge_mem hp.1 hp2⟩ := by
        apply φ.injective
        apply Subtype.ext
        exact hx
      have hye : (⟨f, hfE⟩ : H.edgeSet) =
          ⟨lastTrackEdge q hq2, lastTrackEdge_mem hq.1 hq2⟩ := by
        apply φ.injective
        apply Subtype.ext
        exact hy
      rw [hxe, hye]
      exact ⟨fun h => last_edges_ne hp hq hp2 hq2 hab hnadj hmeet
          (congrArg Subtype.val h), b,
        lastTrackEdge_contains hp hp2, lastTrackEdge_contains hq hq2⟩

/-- Three internally disjoint tracks with common nonadjacent ends form a prism after passing
to their ordered edge lists through a line-graph isomorphism. -/
theorem threeTracksLineGraphPrism {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K)
    {Q₀ Q₁ Q₂ : List W} {c₁ c₂ : W}
    (h₀ : IsTrackFrom H Q₀ c₁ c₂) (h₁ : IsTrackFrom H Q₁ c₁ c₂)
    (h₂ : IsTrackFrom H Q₂ c₁ c₂)
    (hl₀ : 2 ≤ Q₀.length) (hl₁ : 2 ≤ Q₁.length) (hl₂ : 2 ≤ Q₂.length)
    (hc : c₁ ≠ c₂) (hnadj : ¬ H.Adj c₁ c₂)
    (hd₀₁ : ∀ z ∈ Q₀, z ∈ Q₁ → z = c₁ ∨ z = c₂)
    (hd₀₂ : ∀ z ∈ Q₀, z ∈ Q₂ → z = c₁ ∨ z = c₂)
    (hd₁₂ : ∀ z ∈ Q₁, z ∈ Q₂ → z = c₁ ∨ z = c₂) :
    FormPrism G
      ![firstRungVertex φ Q₀ h₀.1 hl₀, firstRungVertex φ Q₁ h₁.1 hl₁,
        firstRungVertex φ Q₂ h₂.1 hl₂]
      ![lastRungVertex φ Q₀ h₀.1 hl₀, lastRungVertex φ Q₁ h₁.1 hl₁,
        lastRungVertex φ Q₂ h₂.1 hl₂]
      (trackRung φ Q₀ h₀.1) (trackRung φ Q₁ h₁.1) (trackRung φ Q₂ h₂.1) := by
  apply Workspace.ProofLemmas.PrismBasics.formPrism_of_data
  · apply φ.map_rel_iff.mpr
    exact ⟨fun h => first_edges_ne h₀ h₁ hl₀ hl₁ hc hnadj hd₀₁
        (congrArg Subtype.val h), c₁,
      firstTrackEdge_contains h₀ hl₀, firstTrackEdge_contains h₁ hl₁⟩
  · apply φ.map_rel_iff.mpr
    exact ⟨fun h => first_edges_ne h₀ h₂ hl₀ hl₂ hc hnadj hd₀₂
        (congrArg Subtype.val h), c₁,
      firstTrackEdge_contains h₀ hl₀, firstTrackEdge_contains h₂ hl₂⟩
  · apply φ.map_rel_iff.mpr
    exact ⟨fun h => first_edges_ne h₁ h₂ hl₁ hl₂ hc hnadj hd₁₂
        (congrArg Subtype.val h), c₁,
      firstTrackEdge_contains h₁ hl₁, firstTrackEdge_contains h₂ hl₂⟩
  · apply φ.map_rel_iff.mpr
    exact ⟨fun h => last_edges_ne h₀ h₁ hl₀ hl₁ hc hnadj hd₀₁
        (congrArg Subtype.val h), c₂,
      lastTrackEdge_contains h₀ hl₀, lastTrackEdge_contains h₁ hl₁⟩
  · apply φ.map_rel_iff.mpr
    exact ⟨fun h => last_edges_ne h₀ h₂ hl₀ hl₂ hc hnadj hd₀₂
        (congrArg Subtype.val h), c₂,
      lastTrackEdge_contains h₀ hl₀, lastTrackEdge_contains h₂ hl₂⟩
  · apply φ.map_rel_iff.mpr
    exact ⟨fun h => last_edges_ne h₁ h₂ hl₁ hl₂ hc hnadj hd₁₂
        (congrArg Subtype.val h), c₂,
      lastTrackEdge_contains h₁ hl₁, lastTrackEdge_contains h₂ hl₂⟩
  · intro h
    exact first_last_ne h₀ h₀ hl₀ hl₀ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₀ h₁ hl₀ hl₁ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₀ h₂ hl₀ hl₂ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₁ h₀ hl₁ hl₀ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₁ h₁ hl₁ hl₁ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₁ h₂ hl₁ hl₂ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₂ h₀ hl₂ hl₀ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₂ h₁ hl₂ hl₁ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · intro h
    exact first_last_ne h₂ h₂ hl₂ hl₂ hc hnadj
      (congrArg Subtype.val (EquivLike.injective φ (Subtype.ext h)))
  · exact trackRung_isPathFrom_ends φ h₀ hl₀
  · exact trackRung_isPathFrom_ends φ h₁ hl₁
  · exact trackRung_isPathFrom_ends φ h₂ hl₂
  · exact rung_cross φ h₀ h₁ hl₀ hl₁ hc hnadj hd₀₁
  · exact rung_cross φ h₀ h₂ hl₀ hl₂ hc hnadj hd₀₂
  · exact rung_cross φ h₁ h₂ hl₁ hl₂ hc hnadj hd₁₂

end Workspace.ProofLemmas.ThreeTracksLineGraphPrism
