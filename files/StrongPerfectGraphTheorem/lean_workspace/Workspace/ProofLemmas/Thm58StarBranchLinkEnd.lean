import Workspace.ProofLemmas.Thm58StarBranchLinkTracks
import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Connectivity58Concat
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.Connectivity58Minimal
import Workspace.ProofLemmas.LineGraphDegree

/-!
# The branch-end case of 5.8 (6)

PAPER (proof of 5.8 (6), printed p. 28): *"Choose a cycle `C₁` of `H` using the branch between
`v₁` and `v₂` and not using `u`, and choose a minimal track `S` in `H \ {v₁,v₂}` between `u`
and `V(C₁)`."*

The printed proof does not separate the case where every neighbour of `p₁` in the star `N_u`
is an edge of `H` from `u` to an end of the branch.  This file shows that case cannot happen
at all: writing `u = c` and `v₁` for that end of the branch, the two tracks of `H`

* `c`, `v₁`, then the return track `D` to `v₂`, then back along the branch to `q[t]`, and
* `v₁`, `c`, then the minimal track to `w`, then along `D` to `v₂`, then back to `q[t]`,

both end at the last neighbour `q[t]` of `pₙ` on the branch, and both rungs close into a hole
of `G` through `p₁`-`P`-`pₙ`.  Their lengths have different parity, because `c` and `v₁` are
adjacent in the bipartite graph `H`, so one of the two holes is odd, contrary to `Berge G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchLinkEnd

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-! ### Edges of a slice -/

/-- Every edge of a slice of a track is an edge of the track, at an index inside the slice. -/
theorem mem_trackEdges_slice {W : Type*} {R : List W} {i j : ℕ} (hj : j < R.length)
    (hij : i ≤ j) {e : Sym2 W} (he : e ∈ trackEdges (TrackSlice.slice R i j)) :
    ∃ (u : ℕ) (hu : u + 1 < R.length), i ≤ u ∧ u < j ∧
      e = s(R[u]'(by omega), R[u + 1]'hu) := by
  obtain ⟨k, hk, rfl⟩ := he
  have hlen := TrackSlice.length_slice R hj hij
  rw [hlen] at hk
  refine ⟨i + k, by omega, by omega, by omega, ?_⟩
  rw [TrackSlice.getElem_slice R (by rw [hlen]; omega) (show i + k < R.length by omega),
    TrackSlice.getElem_slice R (by rw [hlen]; omega) (show i + (k + 1) < R.length by omega)]
  congr 2

/-- The first edge of a slice is the edge of the track at the slice's first index. -/
theorem mem_trackEdges_slice_of {W : Type*} {R : List W} {i j u : ℕ} (hj : j < R.length)
    (hu : u + 1 < R.length) (hiu : i ≤ u) (huj : u < j) :
    s(R[u]'(by omega), R[u + 1]'hu) ∈ trackEdges (TrackSlice.slice R i j) := by
  have hij : i ≤ j := by omega
  have hlen := TrackSlice.length_slice R hj hij
  refine ⟨u - i, by rw [hlen]; omega, ?_⟩
  rw [TrackSlice.getElem_slice R (by rw [hlen]; omega) (show i + (u - i) < R.length by omega),
    TrackSlice.getElem_slice R (by rw [hlen]; omega)
      (show i + (u - i + 1) < R.length by omega)]
  rw [SubdivisionCounting.getElem_eq_of_index_eq R (show i + (u - i) = u by omega)
      (show i + (u - i) < R.length by omega) (by omega),
    SubdivisionCounting.getElem_eq_of_index_eq R (show i + (u - i + 1) = u + 1 by omega)
      (show i + (u - i + 1) < R.length by omega) (by omega)]


/-! ### One hole of the branch-end case -/

/-- **The completion *"via `F`"* of the rung of a track from the star edge `c v₁` to the last
branch edge that `pₙ` sees.**  The rung is a path of `G` whose first vertex is the only
neighbour of `p₁` on it and whose last vertex is the only neighbour of `pₙ` on it, so together
with `P` it closes into a hole. -/
theorem hole_of_track (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ : Fin n} {t : ℕ} (htq : t + 1 < q.length)
    (hcv : s(c, v₁) ∈ H.edgeSet)
    (hqt : s(q[t]'(by omega), q[t + 1]'htq) ∈ H.edgeSet)
    (hp1a : G.Adj p₁ (φ ⟨s(c, v₁), hcv⟩ : V))
    (hp2r : G.Adj p₂ (φ ⟨s(q[t]'(by omega), q[t + 1]'htq), hqt⟩ : V))
    (hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q)
    {WW : List (Fin n)} {aa bb : Fin n} (hW : IsTrackFrom H WW aa bb)
    (hW3 : 3 ≤ WW.length)
    (hfirst : firstTrackEdge WW (by omega) = s(c, v₁))
    (hlast : lastTrackEdge WW (by omega) = s(q[t]'(by omega), q[t + 1]'htq))
    (honly1 : ∀ e ∈ trackEdges WW, ∀ x : Fin n, e = s(c, x) → x ∈ q → e = s(c, v₁))
    (honly2 : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges WW →
        G.Adj p₂ (φ ⟨e, he⟩ : V) → e = s(q[t]'(by omega), q[t + 1]'htq)) :
    IsHoleList G (trackRung φ WW hW.1 ++ P.reverse) := by
  classical
  have hW2 : 2 ≤ WW.length := by omega
  have hSpath := trackRung_isPathFrom_ends φ hW hW2
  have hfv : firstRungVertex φ WW hW.1 hW2 = (φ ⟨s(c, v₁), hcv⟩ : V) :=
    congrArg (fun e : H.edgeSet => (φ e : V)) (Subtype.ext hfirst)
  have hlv : lastRungVertex φ WW hW.1 hW2
      = (φ ⟨s(q[t]'(by omega), q[t + 1]'htq), hqt⟩ : V) :=
    congrArg (fun e : H.edgeSet => (φ e : V)) (Subtype.ext hlast)
  have hSK : ∀ x ∈ trackRung φ WW hW.1, x ∈ K := fun x hx => by
    obtain ⟨e, he, -, rfl⟩ := (mem_trackRung_iff φ hW.1).mp hx
    exact (φ ⟨e, he⟩).2
  have hFK : F ⊆ Kᶜ := h.ready.2.2.2.2.1
  have hdisj : ∀ x ∈ trackRung φ WW hW.1, x ∉ P.reverse := by
    intro x hx hmem
    have hxP : x ∈ P := List.mem_reverse.mp hmem
    exact hFK (by rw [← vertices h]; exact hxP) (hSK x hx)
  have hcross : ∀ x ∈ trackRung φ WW hW.1, ∀ y ∈ P.reverse,
      (G.Adj x y ↔ (x = lastRungVertex φ WW hW.1 hW2 ∧ y = p₂) ∨
        (x = firstRungVertex φ WW hW.1 hW2 ∧ y = p₁)) := by
    intro x hx y hy
    have hyP : y ∈ P := List.mem_reverse.mp hy
    obtain ⟨e, he, heW, rfl⟩ := (mem_trackRung_iff φ hW.1).mp hx
    constructor
    · intro hadj
      rcases edges_of_disjoint h (star_disjoint_branch h hcq) y hyP _ (φ ⟨e, he⟩).2 hadj.symm
        with ⟨rfl, hxN⟩ | ⟨rfl, hxR⟩
      · refine Or.inr ⟨?_, rfl⟩
        rw [star_eq h c] at hxN
        have hec : e ∈ incidentEdges H c := (image_mem_iff (φ := φ) he).mp hxN
        obtain ⟨x', hx'⟩ := Sym2.mem_iff_exists.mp hec.2
        have hex : e = s(c, x') := hx'
        have hxq : x' ∈ q := by
          refine hbranchend x' (hex ▸ he) ?_
          have : (φ ⟨s(c, x'), hex ▸ he⟩ : V) = (φ ⟨e, he⟩ : V) :=
            congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hex.symm)
          rw [this]
          exact hadj.symm
        rw [hfv]
        exact congrArg (fun z : H.edgeSet => (φ z : V))
          (Subtype.ext (honly1 e heW x' hex hxq))
      · refine Or.inl ⟨?_, rfl⟩
        rw [hlv]
        exact congrArg (fun z : H.edgeSet => (φ z : V))
          (Subtype.ext (honly2 e he heW hadj.symm))
    · rintro (⟨hx1, rfl⟩ | ⟨hx1, rfl⟩)
      · rw [hx1, hlv]; exact hp2r.symm
      · rw [hx1, hfv]; exact hp1a.symm
  refine PathGlue.glue_hole hSpath (PathBasics.isPathFrom_reverse (path h)) hdisj hcross ?_
  have h1 : (trackRung φ WW hW.1).length = trackLength WW := trackRung_length φ WW hW.1
  have h2 := two_le_length h
  simp only [List.length_reverse]
  simp only [trackLength] at h1
  omega


/-- The hole of `hole_of_track` is even, since `G` is Berge. -/
theorem even_of_track (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ : Fin n} {t : ℕ} (htq : t + 1 < q.length)
    (hcv : s(c, v₁) ∈ H.edgeSet)
    (hqt : s(q[t]'(by omega), q[t + 1]'htq) ∈ H.edgeSet)
    (hp1a : G.Adj p₁ (φ ⟨s(c, v₁), hcv⟩ : V))
    (hp2r : G.Adj p₂ (φ ⟨s(q[t]'(by omega), q[t + 1]'htq), hqt⟩ : V))
    (hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q)
    {WW : List (Fin n)} {aa bb : Fin n} (hW : IsTrackFrom H WW aa bb)
    (hW3 : 3 ≤ WW.length)
    (hfirst : firstTrackEdge WW (by omega) = s(c, v₁))
    (hlast : lastTrackEdge WW (by omega) = s(q[t]'(by omega), q[t + 1]'htq))
    (honly1 : ∀ e ∈ trackEdges WW, ∀ x : Fin n, e = s(c, x) → x ∈ q → e = s(c, v₁))
    (honly2 : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges WW →
        G.Adj p₂ (φ ⟨e, he⟩ : V) → e = s(q[t]'(by omega), q[t + 1]'htq)) :
    Even (trackLength WW + P.length) := by
  have hh := h.ready.1.1 _ (hole_of_track h hcq htq hcv hqt hp1a hp2r hbranchend hW hW3
    hfirst hlast honly1 honly2)
  simpa [holeLength, trackRung_length] using hh

/-! ### Reading the edges of the two composite tracks -/

/-- Both ends of an edge of a track are vertices of the track. -/
theorem mem_of_mem_trackEdges {W : Type*} {R : List W} {e : Sym2 W} (he : e ∈ trackEdges R)
    {z : W} (hz : z ∈ e) : z ∈ R := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hz with hh | hh <;> rw [hh] <;> exact List.getElem_mem _

section Pieces

variable {v₁ : Fin n} {D Sm : List (Fin n)} {t : ℕ} {WW : List (Fin n)}

/-- The star edge `c v₁` is the only edge of the composite track that joins `c` to the
branch. -/
theorem honly1_of_pieces (hcq : c ∉ q) (hcD : c ∉ D) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hE : ∀ e ∈ trackEdges WW, e = s(c, v₁) ∨ e ∈ trackEdges D ∨ e ∈ trackEdges Sm ∨
      e ∈ trackEdges (TrackSlice.slice q t (q.length - 1))) :
    ∀ e ∈ trackEdges WW, ∀ x : Fin n, e = s(c, x) → x ∈ q → e = s(c, v₁) := by
  intro e he x hex hxq
  have hce : c ∈ e := by rw [hex]; exact Sym2.mem_mk_left _ _
  have hxe : x ∈ e := by rw [hex]; exact Sym2.mem_mk_right _ _
  rcases hE e he with hh | hh | hh | hh
  · exact hh
  · exact absurd (mem_of_mem_trackEdges hh hce) hcD
  · exact absurd hxq (hSmq x (mem_of_mem_trackEdges hh hxe))
  · exact absurd (TrackSlice.mem_of_mem_slice (mem_of_mem_trackEdges hh hce)) hcq

/-- The branch edge at `q[t]` is the only edge of the composite track that `pₙ` sees. -/
theorem honly2_of_pieces (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (htq : t + 1 < q.length)
    (hmax : ∀ (u : ℕ) (hu : u + 1 < q.length), t < u →
      ∀ he : s(q[u]'(by omega), q[u + 1]'hu) ∈ H.edgeSet,
        ¬ G.Adj p₂ (φ ⟨s(q[u]'(by omega), q[u + 1]'hu), he⟩ : V))
    (hE : ∀ e ∈ trackEdges WW, e = s(c, v₁) ∨ e ∈ trackEdges D ∨ e ∈ trackEdges Sm ∨
      e ∈ trackEdges (TrackSlice.slice q t (q.length - 1))) :
    ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges WW →
      G.Adj p₂ (φ ⟨e, he⟩ : V) → e = s(q[t]'(by omega), q[t + 1]'htq) := by
  intro e he heW hadj
  have heq : e ∈ trackEdges q :=
    (image_mem_iff (φ := φ) he).mp (last_adj_mem h (φ ⟨e, he⟩).2 hadj)
  rcases hE e heW with hh | hh | hh | hh
  · exact absurd (mem_of_mem_trackEdges heq
      (by rw [hh]; exact Sym2.mem_mk_left _ _)) hcq
  · exact absurd heq (hDe e hh)
  · exact absurd (mem_of_mem_trackEdges heq (Sym2.out_fst_mem e))
      (hSmq _ (mem_of_mem_trackEdges hh (Sym2.out_fst_mem e)))
  · obtain ⟨u, hu, htu, huL, rfl⟩ :=
      mem_trackEdges_slice (show q.length - 1 < q.length by omega)
        (show t ≤ q.length - 1 by omega) hh
    have hut : u = t := by
      by_contra hne
      exact hmax u hu (by omega) he hadj
    subst hut
    rfl

/-- The branch edge at `q[t]` is the only edge of the composite track containing `q[t]`, so it
is the last edge of that track. -/
theorem hlast_of_pieces (hcq : c ∉ q) (hSmq : ∀ x ∈ Sm, x ∉ q) (hqnd : q.Nodup)
    {v₂ : Fin n} (ht1 : 1 ≤ t) (htq : t + 1 < q.length)
    (hq0 : q[0]'(by omega) = v₁) (hqL : q[q.length - 1]'(by omega) = v₂)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hE : ∀ e ∈ trackEdges WW, e = s(c, v₁) ∨ e ∈ trackEdges D ∨ e ∈ trackEdges Sm ∨
      e ∈ trackEdges (TrackSlice.slice q t (q.length - 1))) :
    ∀ e ∈ trackEdges WW, (q[t]'(by omega)) ∈ e →
      e = s(q[t]'(by omega), q[t + 1]'htq) := by
  intro e he hmem
  have hqt : (q[t]'(by omega : t < q.length)) ∈ q := List.getElem_mem _
  have hnot1 : (q[t]'(by omega : t < q.length)) ≠ v₁ := by
    intro hc
    have : t = 0 := hqnd.getElem_inj_iff.mp (by rw [hc, hq0])
    omega
  have hnot2 : (q[t]'(by omega : t < q.length)) ≠ v₂ := by
    intro hc
    have : t = q.length - 1 := hqnd.getElem_inj_iff.mp (by rw [hc, hqL])
    omega
  rcases hE e he with hh | hh | hh | hh
  · rw [hh] at hmem
    rcases Sym2.mem_iff.mp hmem with hc | hc
    · exact absurd (hc ▸ hqt) hcq
    · exact absurd hc hnot1
  · rcases hDq _ (mem_of_mem_trackEdges hh hmem) hqt with hc | hc
    · exact absurd hc hnot1
    · exact absurd hc hnot2
  · exact absurd hqt (hSmq _ (mem_of_mem_trackEdges hh hmem))
  · obtain ⟨u, hu, htu, huL, rfl⟩ :=
      mem_trackEdges_slice (show q.length - 1 < q.length by omega)
        (show t ≤ q.length - 1 by omega) hh
    have hut : u = t := by
      rcases Sym2.mem_iff.mp hmem with hc | hc
      · exact hqnd.getElem_inj_iff.mp hc.symm
      · have : t = u + 1 := hqnd.getElem_inj_iff.mp hc
        omega
    subst hut
    rfl

end Pieces


/-! ### Locating the neighbours -/

/-- A neighbour of the star vertex `c` that lies on the branch is one of the two branch
ends: an internal vertex of a branch has degree `2` in `H`, with both neighbours on the
branch, and `c` is not on the branch. -/
theorem eq_end_of_adj_star (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ v₂ x : Fin n} (hqe : IsTrackFrom H q v₁ v₂) (hx : x ∈ q) (hadj : H.Adj c x) :
    x = v₁ ∨ x = v₂ := by
  classical
  by_contra hcon
  push_neg at hcon
  have hqlen := branch_two_le_length h
  have hq0 : q[0]'(by omega) = v₁ := by
    have hh := hqe.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hqL : q[q.length - 1]'(by omega) = v₂ := by
    have hh := hqe.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
  have hj0 : j ≠ 0 := by
    intro hc
    exact hcon.1 (by rw [← hq0]; exact SubdivisionCounting.getElem_eq_of_index_eq q hc hj _)
  have hjL : j ≠ q.length - 1 := by
    intro hc
    exact hcon.2 (by rw [← hqL]; exact SubdivisionCounting.getElem_eq_of_index_eq q hc hj _)
  have hint : (q[j]'hj) ∈ trackInterior q := by
    refine (SubdivisionCounting.mem_trackInterior_iff q _).mpr ⟨j - 1, by omega, ?_⟩
    exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) (by omega) hj
  have hdeg2 :=
    LineGraphDegree.two_le_degree_of_isSubdivision h.ready.2.1 h.ready.2.2.1.1
  exact hcq (Connectivity58Minimal.neighbors_of_branch_interior hdeg2 h.branch hint c hadj.symm)

/-- The smallest and the largest index of a branch edge that `pₙ` sees. -/
theorem exists_extreme_index (h : Context G m J n H K φ N F P p₁ p₂ c q)
    {r : V} (hr : r ∈ edgeImage φ (trackEdges q)) (hpr : G.Adj p₂ r) :
    ∃ (tmin tmax : ℕ) (hmn : tmin + 1 < q.length) (hmx : tmax + 1 < q.length),
      G.Adj p₂ (φ ⟨s(q[tmin]'(by omega), q[tmin + 1]'hmn),
        h.branch.1.2.2 tmin hmn⟩ : V) ∧
      G.Adj p₂ (φ ⟨s(q[tmax]'(by omega), q[tmax + 1]'hmx),
        h.branch.1.2.2 tmax hmx⟩ : V) ∧
      ∀ (u : ℕ) (hu : u + 1 < q.length)
        (he : s(q[u]'(by omega), q[u + 1]'hu) ∈ H.edgeSet),
        G.Adj p₂ (φ ⟨s(q[u]'(by omega), q[u + 1]'hu), he⟩ : V) → tmin ≤ u ∧ u ≤ tmax := by
  classical
  set Sf : Finset ℕ := (Finset.range (q.length - 1)).filter
    (fun u => ∀ (hu : u + 1 < q.length)
      (he : s(q[u]'(by omega), q[u + 1]'hu) ∈ H.edgeSet),
      G.Adj p₂ (φ ⟨s(q[u]'(by omega), q[u + 1]'hu), he⟩ : V)) with hSf
  obtain ⟨e, he, ⟨i, hi, hie⟩, rfl⟩ := hr
  have hiS : i ∈ Sf := by
    rw [hSf, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    intro hu he'
    have : (φ ⟨s(q[i]'(by omega), q[i + 1]'hu), he'⟩ : V) = (φ ⟨e, he⟩ : V) :=
      congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hie.symm)
    rw [this]
    exact hpr
  have hne : Sf.Nonempty := ⟨i, hiS⟩
  have hmaxmem := Sf.max'_mem hne
  have hminmem := Sf.min'_mem hne
  obtain ⟨hmaxr, hmaxp⟩ := Finset.mem_filter.mp hmaxmem
  obtain ⟨hminr, hminp⟩ := Finset.mem_filter.mp hminmem
  have hmaxr' := Finset.mem_range.mp hmaxr
  have hminr' := Finset.mem_range.mp hminr
  refine ⟨Sf.min' hne, Sf.max' hne, by omega, by omega,
    hminp _ _, hmaxp _ _, ?_⟩
  intro u hu he' hadj
  have huS : u ∈ Sf := by
    rw [hSf, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr (by omega), fun _ _ => hadj⟩
  exact ⟨Sf.min'_le u huS, Sf.le_max' u huS⟩

/-! ### The branch-end case is impossible -/

/-- **PAPER, proof of 5.8 (6), printed p. 28.**  The case the printed proof does not separate:
every neighbour of `p₁` in the star `N_u` is an edge of `H` from `u = c` to a vertex of the
branch, so (an internal branch vertex having degree `2` with both neighbours on the branch) to
an end `v₁` of the branch.  Two tracks of `H` from the star edge `c v₁` to the last branch edge
that `pₙ` sees close, with `p₁`-`P`-`pₙ`, into two holes of `G` whose lengths differ in parity,
because `c` and `v₁` are adjacent in the bipartite graph `H`.  That contradicts `Berge G`. -/
theorem branch_end_false
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k t : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hcv : s(c, v₁) ∈ H.edgeSet)
    (hp1a : G.Adj p₁ (φ ⟨s(c, v₁), hcv⟩ : V))
    (hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q)
    (ht1 : 1 ≤ t) (htq : t + 1 < q.length)
    (hp2r : G.Adj p₂ (φ ⟨s(q[t]'(by omega), q[t + 1]'htq), hqe.1.2.2 t htq⟩ : V))
    (hmax : ∀ (u : ℕ) (hu : u + 1 < q.length), t < u →
      ∀ he : s(q[u]'(by omega), q[u + 1]'hu) ∈ H.edgeSet,
        ¬ G.Adj p₂ (φ ⟨s(q[u]'(by omega), q[u + 1]'hu), he⟩ : V)) :
    False := by
  classical
  have hqnd : q.Nodup := hqe.1.2.1
  have hq0 : q[0]'(by omega) = v₁ := by
    have hh := hqe.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hqL : q[q.length - 1]'(by omega) = v₂ := by
    have hh := hqe.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hDnd : D.Nodup := hD.1.2.1
  have hD0 : D[0]'(by omega) = v₁ := by
    have hh := hD.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hDL : D[D.length - 1]'(by omega) = v₂ := by
    have hh := hD.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hDk : D[k]'(by omega) = w := by
    rw [List.getElem?_eq_getElem (by omega : k < D.length)] at hkw
    exact Option.some_injective _ hkw
  -- the tail of the branch, from `v₂` back to `q[t]`
  have hsliceT : IsTrackFrom H (TrackSlice.slice q t (q.length - 1))
      (q[t]'(by omega)) (q[q.length - 1]'(by omega)) :=
    TrackSlice.isTrackFrom_slice hqe.1 (by omega) (by omega)
  have hTl : IsTrackFrom H (TrackSlice.slice q t (q.length - 1)).reverse v₂
      (q[t]'(by omega)) := by
    have hh := TrackSlice.isTrackFrom_reverse hsliceT
    rwa [hqL] at hh
  have hTlq : ∀ z ∈ (TrackSlice.slice q t (q.length - 1)).reverse, z ∈ q := fun z hz =>
    TrackSlice.mem_of_mem_slice (List.mem_reverse.mp hz)
  have hTlidx : ∀ z ∈ (TrackSlice.slice q t (q.length - 1)).reverse,
      ∃ (u : ℕ) (hu : u < q.length), t ≤ u ∧ q[u]'hu = z := by
    intro z hz
    obtain ⟨u, hu, htu, -, hz'⟩ :=
      (TrackSlice.mem_slice_iff (show q.length - 1 < q.length by omega)
        (show t ≤ q.length - 1 by omega)).mp (List.mem_reverse.mp hz)
    exact ⟨u, hu, htu, hz'⟩
  have hv₁Tl : v₁ ∉ (TrackSlice.slice q t (q.length - 1)).reverse := by
    intro hc
    obtain ⟨u, hu, htu, hz⟩ := hTlidx v₁ hc
    have : u = 0 := hqnd.getElem_inj_iff.mp (by rw [hz, hq0])
    omega
  have hcTl : c ∉ (TrackSlice.slice q t (q.length - 1)).reverse := fun hc => hcq (hTlq c hc)
  have hTllen : 2 ≤ (TrackSlice.slice q t (q.length - 1)).reverse.length := by
    rw [List.length_reverse,
      TrackSlice.length_slice q (show q.length - 1 < q.length by omega)
        (show t ≤ q.length - 1 by omega)]
    omega

  -- the two composite tracks
  have hcvadj : H.Adj c v₁ := (SimpleGraph.mem_edgeSet H).mp hcv
  have hcv1ne : c ≠ v₁ := H.ne_of_adj hcvadj
  have hA : IsTrackFrom H (D ++ (TrackSlice.slice q t (q.length - 1)).reverse.tail) v₁
      (q[t]'(by omega)) := by
    refine Connectivity58Concat.isTrackFrom_append hD hTl ?_
    intro z hz1 hz2
    rcases hDq z hz1 (hTlq z hz2) with rfl | rfl
    · exact absurd hz2 hv₁Tl
    · rfl
  have hAmem : ∀ z ∈ D ++ (TrackSlice.slice q t (q.length - 1)).reverse.tail,
      z ∈ D ∨ z ∈ (TrackSlice.slice q t (q.length - 1)).reverse := by
    intro z hz
    rcases List.mem_append.mp hz with hh | hh
    · exact Or.inl hh
    · exact Or.inr (List.mem_of_mem_tail hh)
  have hcv1trk : IsTrackFrom H [c, v₁] c v₁ := by
    refine ⟨⟨by simp, by simp [hcv1ne], ?_⟩, by simp, by simp⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    simpa using hcvadj
  have hW₁ : IsTrackFrom H ([c, v₁] ++ (D ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail) c (q[t]'(by omega)) := by
    refine Connectivity58Concat.isTrackFrom_append hcv1trk hA ?_
    intro z hz1 hz2
    have hz : z = c ∨ z = v₁ := by simpa using hz1
    rcases hz with rfl | rfl
    · rcases hAmem z hz2 with hh | hh
      · exact absurd hh hcD
      · exact absurd hh hcTl
    · rfl
  have hDarc : IsTrackFrom H (TrackSlice.slice D k (D.length - 1)) w v₂ := by
    have hh := TrackSlice.isTrackFrom_slice hD.1 (show D.length - 1 < D.length by omega)
      (show k ≤ D.length - 1 by omega)
    rwa [hDk, hDL] at hh
  have hDarcD : ∀ z ∈ TrackSlice.slice D k (D.length - 1), z ∈ D := fun z hz =>
    TrackSlice.mem_of_mem_slice hz
  have hv₁Darc : v₁ ∉ TrackSlice.slice D k (D.length - 1) := by
    intro hc
    obtain ⟨u, hu, hku, -, hz⟩ :=
      (TrackSlice.mem_slice_iff (show D.length - 1 < D.length by omega)
        (show k ≤ D.length - 1 by omega)).mp hc
    have : u = 0 := hDnd.getElem_inj_iff.mp (by rw [hz, hD0])
    omega
  have hB0 : IsTrackFrom H (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail) w (q[t]'(by omega)) := by
    refine Connectivity58Concat.isTrackFrom_append hDarc hTl ?_
    intro z hz1 hz2
    rcases hDq z (hDarcD z hz1) (hTlq z hz2) with rfl | rfl
    · exact absurd hz2 hv₁Tl
    · rfl
  have hB0mem : ∀ z ∈ TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail,
      z ∈ TrackSlice.slice D k (D.length - 1) ∨
        z ∈ (TrackSlice.slice q t (q.length - 1)).reverse := by
    intro z hz
    rcases List.mem_append.mp hz with hh | hh
    · exact Or.inl hh
    · exact Or.inr (List.mem_of_mem_tail hh)
  have hB : IsTrackFrom H (Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail) c (q[t]'(by omega)) := by
    refine Connectivity58Concat.isTrackFrom_append hSm hB0 ?_
    intro z hz1 hz2
    rcases hB0mem z hz2 with hh | hh
    · exact hSmD z hz1 (hDarcD z hh)
    · exact absurd (hTlq z hh) (hSmq z hz1)
  have hBmem : ∀ z ∈ Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail,
      z ∈ Sm ∨ z ∈ TrackSlice.slice D k (D.length - 1) ∨
        z ∈ (TrackSlice.slice q t (q.length - 1)).reverse := by
    intro z hz
    rcases List.mem_append.mp hz with hh | hh
    · exact Or.inl hh
    · exact Or.inr (hB0mem z (List.mem_of_mem_tail hh))
  have hv1ctrk : IsTrackFrom H [v₁, c] v₁ c := by
    refine ⟨⟨by simp, by simp [hcv1ne.symm], ?_⟩, by simp, by simp⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    simpa using hcvadj.symm
  have hW₂ : IsTrackFrom H ([v₁, c] ++ (Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail).tail) v₁
      (q[t]'(by omega)) := by
    refine Connectivity58Concat.isTrackFrom_append hv1ctrk hB ?_
    intro z hz1 hz2
    have hz : z = v₁ ∨ z = c := by simpa using hz1
    rcases hz with rfl | rfl
    · rcases hBmem z hz2 with hh | hh | hh
      · exact absurd (List.getElem_mem (show 0 < q.length by omega)) (hq0 ▸ hSmq z hh)
      · exact absurd hh hv₁Darc
      · exact absurd hh hv₁Tl
    · rfl


  -- the edges of the two composite tracks
  have hEcv : ∀ e ∈ trackEdges ([c, v₁] : List (Fin n)), e = s(c, v₁) := by
    rintro e ⟨i, hi, rfl⟩
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    rfl
  have hEvc : ∀ e ∈ trackEdges ([v₁, c] : List (Fin n)), e = s(c, v₁) := by
    rintro e ⟨i, hi, rfl⟩
    simp only [List.length_cons, List.length_nil] at hi
    have : i = 0 := by omega
    subst this
    exact Sym2.eq_swap
  have hErev : trackEdges (TrackSlice.slice q t (q.length - 1)).reverse
      = trackEdges (TrackSlice.slice q t (q.length - 1)) :=
    SubdivisionCounting.trackEdges_reverse _
  have hEDarc : ∀ e ∈ trackEdges (TrackSlice.slice D k (D.length - 1)),
      e ∈ trackEdges D := by
    intro e he
    obtain ⟨u, hu, -, -, rfl⟩ :=
      mem_trackEdges_slice (show D.length - 1 < D.length by omega)
        (show k ≤ D.length - 1 by omega) he
    exact ⟨u, hu, rfl⟩
  have hEA : ∀ e ∈ trackEdges (D ++ (TrackSlice.slice q t (q.length - 1)).reverse.tail),
      e ∈ trackEdges D ∨ e ∈ trackEdges (TrackSlice.slice q t (q.length - 1)) := by
    intro e he
    have hh := Thm58StarBranchLinkTracks.trackEdges_append_tail_subset hD.1.1
      (hD.2.2.trans hTl.2.1.symm) he
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (hErev ▸ hh)
  have hEW₁ : ∀ e ∈ trackEdges ([c, v₁] ++ (D ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail),
      e = s(c, v₁) ∨ e ∈ trackEdges D ∨ e ∈ trackEdges Sm ∨
        e ∈ trackEdges (TrackSlice.slice q t (q.length - 1)) := by
    intro e he
    rcases Thm58StarBranchLinkTracks.trackEdges_append_tail_subset (by simp)
      (by rw [hA.2.1]; rfl) he with hh | hh
    · exact Or.inl (hEcv e hh)
    · rcases hEA e hh with hh' | hh'
      · exact Or.inr (Or.inl hh')
      · exact Or.inr (Or.inr (Or.inr hh'))
  have hEB0 : ∀ e ∈ trackEdges (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail),
      e ∈ trackEdges D ∨ e ∈ trackEdges (TrackSlice.slice q t (q.length - 1)) := by
    intro e he
    rcases Thm58StarBranchLinkTracks.trackEdges_append_tail_subset hDarc.1.1
      (hDarc.2.2.trans hTl.2.1.symm) he with hh | hh
    · exact Or.inl (hEDarc e hh)
    · exact Or.inr (hErev ▸ hh)
  have hEB : ∀ e ∈ trackEdges (Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail),
      e ∈ trackEdges Sm ∨ e ∈ trackEdges D ∨
        e ∈ trackEdges (TrackSlice.slice q t (q.length - 1)) := by
    intro e he
    rcases Thm58StarBranchLinkTracks.trackEdges_append_tail_subset hSm.1.1
      (hSm.2.2.trans hB0.2.1.symm) he with hh | hh
    · exact Or.inl hh
    · exact Or.inr (hEB0 e hh)
  have hEW₂ : ∀ e ∈ trackEdges ([v₁, c] ++ (Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail).tail),
      e = s(c, v₁) ∨ e ∈ trackEdges D ∨ e ∈ trackEdges Sm ∨
        e ∈ trackEdges (TrackSlice.slice q t (q.length - 1)) := by
    intro e he
    rcases Thm58StarBranchLinkTracks.trackEdges_append_tail_subset (by simp)
      (by rw [hB.2.1]; rfl) he with hh | hh
    · exact Or.inl (hEvc e hh)
    · rcases hEB e hh with hh' | hh' | hh'
      · exact Or.inr (Or.inr (Or.inl hh'))
      · exact Or.inr (Or.inl hh')
      · exact Or.inr (Or.inr (Or.inr hh'))


  -- lengths
  have lenA := Connectivity58Concat.length_append D
    (TrackSlice.slice q t (q.length - 1)).reverse
  have lenW1 := Connectivity58Concat.length_append ([c, v₁] : List (Fin n))
    (D ++ (TrackSlice.slice q t (q.length - 1)).reverse.tail)
  have lenDarc : (TrackSlice.slice D k (D.length - 1)).length = D.length - 1 - k + 1 :=
    TrackSlice.length_slice D (show D.length - 1 < D.length by omega)
      (show k ≤ D.length - 1 by omega)
  have lenB0 := Connectivity58Concat.length_append (TrackSlice.slice D k (D.length - 1))
    (TrackSlice.slice q t (q.length - 1)).reverse
  have lenB := Connectivity58Concat.length_append Sm
    (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail)
  have lenW2 := Connectivity58Concat.length_append ([v₁, c] : List (Fin n))
    (Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail)
  simp only [List.length_cons, List.length_nil] at lenW1 lenW2
  have hW₁3 : 3 ≤ ([c, v₁] ++ (D ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail).length := by omega
  have hW₂3 : 3 ≤ ([v₁, c] ++ (Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail).tail).length := by omega
  -- first and last edges
  have hfirst₁ : firstTrackEdge ([c, v₁] ++ (D ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail) (by omega) = s(c, v₁) := by
    rw [Thm58StarBranchLinkTracks.firstTrackEdge_append_tail
      (show 2 ≤ ([c, v₁] : List (Fin n)).length by simp)]
    rfl
  have hfirst₂ : firstTrackEdge ([v₁, c] ++ (Sm ++ (TrackSlice.slice D k (D.length - 1) ++
      (TrackSlice.slice q t (q.length - 1)).reverse.tail).tail).tail) (by omega)
      = s(c, v₁) := by
    rw [Thm58StarBranchLinkTracks.firstTrackEdge_append_tail
      (show 2 ≤ ([v₁, c] : List (Fin n)).length by simp)]
    exact Sym2.eq_swap
  have hlast₁ := hlast_of_pieces (v₂ := v₂) hcq hSmq hqnd ht1 htq hq0 hqL hDq hEW₁ _
    (lastTrackEdge_mem_trackEdges (show 2 ≤ _ by omega))
    (lastTrackEdge_contains hW₁ (show 2 ≤ _ by omega))
  have hlast₂ := hlast_of_pieces (v₂ := v₂) hcq hSmq hqnd ht1 htq hq0 hqL hDq hEW₂ _
    (lastTrackEdge_mem_trackEdges (show 2 ≤ _ by omega))
    (lastTrackEdge_contains hW₂ (show 2 ≤ _ by omega))
  -- the two holes are even
  have hev₁ := even_of_track h hcq htq hcv (hqe.1.2.2 t htq) hp1a hp2r hbranchend hW₁ hW₁3
    hfirst₁ hlast₁ (honly1_of_pieces hcq hcD hSmq hEW₁)
    (honly2_of_pieces h hcq hSmq hDe htq hmax hEW₁)
  have hev₂ := even_of_track h hcq htq hcv (hqe.1.2.2 t htq) hp1a hp2r hbranchend hW₂ hW₂3
    hfirst₂ hlast₂ (honly1_of_pieces hcq hcD hSmq hEW₂)
    (honly2_of_pieces h hcq hSmq hDe htq hmax hEW₂)
  -- but their lengths have different parity, since `c` and `v₁` are adjacent
  obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite h.ready.2.2.1.2
  have e1 := BipartiteClosedWalkEven.even_trackLength_iff col hW₁
  have e2 := BipartiteClosedWalkEven.even_trackLength_iff col hW₂
  have hpar : (col c = col (q[t]'(show t < q.length by omega))) ↔
      (col v₁ = col (q[t]'(show t < q.length by omega))) := by
    rw [← e1, ← e2]
    rw [Nat.even_add] at hev₁ hev₂
    exact hev₁.trans hev₂.symm
  have hb : ∀ a b d : Bool, ((a = d) ↔ (b = d)) → a = b := by decide
  exact col.valid hcvadj (hb _ _ _ hpar)


/-! ### The same statement read from the other end of the branch -/

/-- A branch read backwards is a branch. -/
theorem isBranch_reverse {W : Type*} {Hg : SimpleGraph W} {qq : List W}
    (hq : IsBranch Hg qq) : IsBranch Hg qq.reverse := by
  refine ⟨TrackSlice.isTrackList_reverse hq.1, ?_, ?_⟩
  · intro v hv
    exact hq.2.1 v (TrackSlice.mem_trackInterior_reverse.mp hv)
  · intro q' hq' hq'' hsub hmem
    rw [SubdivisionCounting.trackEdges_reverse]
    refine hq.2.2 q' hq' hq'' ?_ ?_
    · rwa [SubdivisionCounting.trackEdges_reverse] at hsub
    · intro v hv
      exact hmem v (List.mem_reverse.mpr hv)

/-- The star--branch context does not care in which direction the branch is read. -/
theorem context_reverse (h : Context G m J n H K φ N F P p₁ p₂ c q) :
    Context G m J n H K φ N F P p₁ p₂ c q.reverse where
  ready := h.ready
  star := h.star
  branch := isBranch_reverse h.branch
  first := h.first
  last := by rw [SubdivisionCounting.trackEdges_reverse]; exact h.last

/-- `branch_end_false` with the branch read from `v₂`. -/
theorem branch_end_false_right
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k t : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hcv : s(c, v₂) ∈ H.edgeSet)
    (hp1a : G.Adj p₁ (φ ⟨s(c, v₂), hcv⟩ : V))
    (hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q)
    (htq : t + 2 < q.length)
    (hp2r : ∀ he : s(q[t]'(by omega), q[t + 1]'(by omega)) ∈ H.edgeSet,
      G.Adj p₂ (φ ⟨s(q[t]'(by omega), q[t + 1]'(by omega)), he⟩ : V))
    (hmin : ∀ (u : ℕ) (hu : u + 1 < q.length), u < t →
      ∀ he : s(q[u]'(by omega), q[u + 1]'hu) ∈ H.edgeSet,
        ¬ G.Adj p₂ (φ ⟨s(q[u]'(by omega), q[u + 1]'hu), he⟩ : V)) :
    False := by
  classical
  have hrq : ∀ (j : ℕ) (hj : j < q.reverse.length),
      q.reverse[j]'hj = q[q.length - 1 - j]'(by
        rw [List.length_reverse] at hj; omega) := fun j hj => List.getElem_reverse _
  have hqlen : q.reverse.length = q.length := List.length_reverse
  have hDlen : D.reverse.length = D.length := List.length_reverse
  refine branch_end_false (t := q.length - 2 - t) (k := D.length - 1 - k)
    (context_reverse h) (by rwa [List.mem_reverse])
    (TrackSlice.isTrackFrom_reverse hqe) (TrackSlice.isTrackFrom_reverse hD)
    (by rwa [List.mem_reverse]) ?_ ?_ (by omega) (by omega) ?_ hSm hSm2 ?_
    (by intro x hx; rw [List.mem_reverse]; exact hSmq x hx) hcv hp1a
    (by intro x hx hax; rw [List.mem_reverse]; exact hbranchend x hx hax)
    (by omega) (by rw [hqlen]; omega) ?_ ?_
  · intro z hz hz'
    rw [List.mem_reverse] at hz hz'
    exact (hDq z hz hz').symm
  · intro e he
    rw [SubdivisionCounting.trackEdges_reverse] at he ⊢
    exact hDe e he
  · rw [List.getElem?_eq_getElem (by rw [hDlen]; omega),
      List.getElem_reverse, SubdivisionCounting.getElem_eq_of_index_eq D
        (show D.length - 1 - (D.length - 1 - k) = k by omega) (by omega) (by omega)]
    rw [List.getElem?_eq_getElem (show k < D.length by omega)] at hkw
    exact hkw
  · intro x hx hxD
    rw [List.mem_reverse] at hxD
    exact hSmD x hx hxD
  · -- the marked branch edge, read backwards
    have e1 : q.reverse[q.length - 2 - t]'(by rw [hqlen]; omega)
        = q[t + 1]'(by omega) := by
      rw [hrq]
      exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) (by omega) (by omega)
    have e2 : q.reverse[q.length - 2 - t + 1]'(by rw [hqlen]; omega)
        = q[t]'(by omega) := by
      rw [hrq]
      exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) (by omega) (by omega)
    have hedge : s(q.reverse[q.length - 2 - t]'(by rw [hqlen]; omega),
        q.reverse[q.length - 2 - t + 1]'(by rw [hqlen]; omega))
        = s(q[t]'(by omega), q[t + 1]'(by omega)) := by
      rw [e1, e2]; exact Sym2.eq_swap
    refine Eq.mpr ?_ (hp2r (hqe.1.2.2 t (by omega)))
    exact congrArg (fun z : V => G.Adj p₂ z)
      (congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hedge))
  · -- maximality, read backwards
    intro u hu htu he hadj
    have e1 : q.reverse[u]'(by rw [hqlen]; omega)
        = q[q.length - 1 - u]'(by omega) := hrq u _
    have e2 : q.reverse[u + 1]'(by rw [hqlen]; omega)
        = q[q.length - 2 - u]'(by omega) := by
      rw [hrq]
      exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) (by omega) (by omega)
    have hedge : s(q.reverse[u]'(by rw [hqlen]; omega),
        q.reverse[u + 1]'(by rw [hqlen]; omega))
        = s(q[q.length - 2 - u]'(by omega), q[q.length - 2 - u + 1]'(by omega)) := by
      rw [e1, e2]
      rw [SubdivisionCounting.getElem_eq_of_index_eq q
        (show q.length - 1 - u = q.length - 2 - u + 1 by omega) (by omega) (by omega)]
      exact Sym2.eq_swap
    have hem : s(q[q.length - 2 - u]'(by omega), q[q.length - 2 - u + 1]'(by omega))
        ∈ H.edgeSet := hqe.1.2.2 (q.length - 2 - u) (by omega)
    have hcong : (φ ⟨_, he⟩ : V) = (φ ⟨_, hem⟩ : V) :=
      congrArg (fun z : H.edgeSet => (φ z : V)) (Subtype.ext hedge)
    exact hmin (q.length - 2 - u) (by omega) (by omega) hem
      (Eq.mp (congrArg (fun z : V => G.Adj p₂ z) hcong) hadj)



/-! ### The branch-end hypothesis is contradictory -/

/-- **The branch-end case of 5.8 (6) cannot occur.**

Assume every neighbour of `p₁` in the star `N_u` at `u = c` is an edge of `H` from `c` to a
vertex of the branch.  Such a vertex is an end `v₁` or `v₂` of the branch, by
`eq_end_of_adj_star`.  If `pₙ` sees a branch edge that is not the branch edge at that end, then
`branch_end_false` (or `branch_end_false_right`) produces two holes of different parity.
Otherwise every attachment of `F` is an edge of `H` at that end, so the attachments are local,
contrary to the hypothesis of 5.8 — unless the branch has length `1` and `c` is joined to both
its ends, which is a triangle of the bipartite graph `H`. -/
theorem branch_end_absurd
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hbv₁ : v₁ ∈ branchVertices H)
    (hbv₂ : v₂ ∈ branchVertices H)
    (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q)
    {r : V} (hr : r ∈ edgeImage φ (trackEdges q)) (hpr : G.Adj p₂ r) :
    False := by
  classical
  have hqlen := branch_two_le_length h
  have hq0 : q[0]'(by omega) = v₁ := by
    have hh := hqe.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hqL : q[q.length - 1]'(by omega) = v₂ := by
    have hh := hqe.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  obtain ⟨tmin, tmax, hmn, hmx, hadjmin, hadjmax, hbound⟩ := exists_extreme_index h hr hpr
  have hmnmx : tmin ≤ tmax := (hbound tmax hmx _ hadjmax).1
  -- the two possible star edges at `p₁`
  by_cases hA1 : ∃ hh : s(c, v₁) ∈ H.edgeSet, G.Adj p₁ (φ ⟨s(c, v₁), hh⟩ : V)
  · obtain ⟨hcv1, hp1a1⟩ := hA1
    by_cases htmax : 1 ≤ tmax
    · exact branch_end_false h hcq hqe hD hcD hDq hDe hk0 hklt hkw hSm hSm2 hSmD hSmq
        hcv1 hp1a1 hbranchend htmax hmx hadjmax
        (fun u hu htu he hadj => by
          have := (hbound u hu he hadj).2
          omega)
    · -- `pₙ` sees only the branch edge at `v₁`
      have htm0 : tmax = 0 := by omega
      have htn0 : tmin = 0 := by omega
      by_cases hA2 : ∃ hh : s(c, v₂) ∈ H.edgeSet, G.Adj p₁ (φ ⟨s(c, v₂), hh⟩ : V)
      · -- `c v₁`, `c v₂` and the branch would give a triangle of the bipartite graph `H`
        obtain ⟨hcv2, hp1a2⟩ := hA2
        exfalso
        have hq2 : q.length = 2 := by
          rcases (hbound tmin hmn _ hadjmin).2 with hh
          have hmin2 : tmin + 2 ≤ q.length := by omega
          by_contra hne
          have hlong : tmin + 2 < q.length := by omega
          exact branch_end_false_right h hcq hqe hD hcD hDq hDe hk0 hklt hkw hSm hSm2 hSmD
            hSmq hcv2 hp1a2 hbranchend hlong (fun _ => hadjmin)
            (fun u hu hut he hadj => by
              have := (hbound u hu he hadj).1
              omega)
        have hv12 : H.Adj v₁ v₂ := by
          have hadj := hqe.1.2.2 0 (by omega)
          rw [show q[0]'(by omega) = v₁ from hq0,
            show q[0 + 1]'(by omega) = v₂ from by
              refine (SubdivisionCounting.getElem_eq_of_index_eq q (by omega) (by omega)
                (by omega)).trans hqL] at hadj
          exact (SimpleGraph.mem_edgeSet H).mp hadj
        obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite
          h.ready.2.2.1.2
        have e1 : col c ≠ col v₁ := col.valid ((SimpleGraph.mem_edgeSet H).mp hcv1)
        have e2 : col c ≠ col v₂ := col.valid ((SimpleGraph.mem_edgeSet H).mp hcv2)
        have e3 : col v₁ ≠ col v₂ := col.valid hv12
        have hb : ∀ a b d : Bool, a ≠ b → a ≠ d → b ≠ d → False := by decide
        exact hb _ _ _ e1 e2 e3
      · -- all attachments are edges of `H` at `v₁`
        exfalso
        refine h.ready.2.2.2.2.2.1 (Or.inl ⟨v₁, hbv₁, ?_⟩)
        rintro e ⟨he, hK, z, hzF, hadj⟩
        have hzP : z ∈ P := by rw [← vertices h] at hzF; exact hzF
        rcases edges_of_disjoint h (star_disjoint_branch h hcq) z hzP _ hK hadj.symm with
          ⟨rfl, hxN⟩ | ⟨rfl, hxR⟩
        · rw [star_eq h c] at hxN
          have hec : e ∈ incidentEdges H c := (image_mem_iff (φ := φ) he).mp hxN
          obtain ⟨x', hx'⟩ := Sym2.mem_iff_exists.mp hec.2
          subst hx'
          have hxq : x' ∈ q := hbranchend x' he hadj.symm
          rcases eq_end_of_adj_star h hcq hqe hxq ((SimpleGraph.mem_edgeSet H).mp he) with
            rfl | rfl
          · exact ⟨he, Sym2.mem_mk_right _ _⟩
          · exact absurd ⟨he, hadj.symm⟩ hA2
        · have heq : e ∈ trackEdges q := (image_mem_iff (φ := φ) he).mp hxR
          obtain ⟨u, hu, rfl⟩ := heq
          have hu0 : u = 0 := by
            have := (hbound u hu he hadj.symm).2
            omega
          subst hu0
          refine ⟨he, ?_⟩
          rw [hq0]
          exact Sym2.mem_mk_left _ _
  · -- the neighbour of `p₁` in the star is the edge `c v₂`
    have hA2 : ∃ hh : s(c, v₂) ∈ H.edgeSet, G.Adj p₁ (φ ⟨s(c, v₂), hh⟩ : V) := by
      obtain ⟨a, ⟨haN, -⟩, hp1a⟩ := first_outside_branch h
      rw [star_eq h c] at haN
      obtain ⟨e, he, hec, rfl⟩ := haN
      obtain ⟨x', hx'⟩ := Sym2.mem_iff_exists.mp hec.2
      subst hx'
      have hxq : x' ∈ q := hbranchend x' he hp1a
      rcases eq_end_of_adj_star h hcq hqe hxq ((SimpleGraph.mem_edgeSet H).mp he) with
        rfl | rfl
      · exact absurd ⟨he, hp1a⟩ hA1
      · exact ⟨he, hp1a⟩
    obtain ⟨hcv2, hp1a2⟩ := hA2
    by_cases htmin : tmin + 2 < q.length
    · exact branch_end_false_right h hcq hqe hD hcD hDq hDe hk0 hklt hkw hSm hSm2 hSmD hSmq
        hcv2 hp1a2 hbranchend htmin (fun _ => hadjmin)
        (fun u hu hut he hadj => by
          have := (hbound u hu he hadj).1
          omega)
    · -- all attachments are edges of `H` at `v₂`
      have htn : tmin = q.length - 2 := by omega
      have htx : tmax = q.length - 2 := by
        have := (hbound tmax hmx _ hadjmax).1
        omega
      refine h.ready.2.2.2.2.2.1 (Or.inl ⟨v₂, hbv₂, ?_⟩)
      rintro e ⟨he, hK, z, hzF, hadj⟩
      have hzP : z ∈ P := by rw [← vertices h] at hzF; exact hzF
      rcases edges_of_disjoint h (star_disjoint_branch h hcq) z hzP _ hK hadj.symm with
        ⟨rfl, hxN⟩ | ⟨rfl, hxR⟩
      · rw [star_eq h c] at hxN
        have hec : e ∈ incidentEdges H c := (image_mem_iff (φ := φ) he).mp hxN
        obtain ⟨x', hx'⟩ := Sym2.mem_iff_exists.mp hec.2
        subst hx'
        have hxq : x' ∈ q := hbranchend x' he hadj.symm
        rcases eq_end_of_adj_star h hcq hqe hxq ((SimpleGraph.mem_edgeSet H).mp he) with
          rfl | rfl
        · exact absurd ⟨he, hadj.symm⟩ hA1
        · exact ⟨he, Sym2.mem_mk_right _ _⟩
      · have heq : e ∈ trackEdges q := (image_mem_iff (φ := φ) he).mp hxR
        obtain ⟨u, hu, rfl⟩ := heq
        have hu0 : u = q.length - 2 := by
          have h1 := (hbound u hu he hadj.symm).1
          have h2 := (hbound u hu he hadj.symm).2
          omega
        subst hu0
        refine ⟨he, ?_⟩
        rw [show q[q.length - 2 + 1]'(by omega) = v₂ from by
          refine (SubdivisionCounting.getElem_eq_of_index_eq q (by omega) (by omega)
            (by omega)).trans hqL]
        exact Sym2.mem_mk_right _ _

end Workspace.ProofLemmas.Thm58StarBranchLinkEnd
