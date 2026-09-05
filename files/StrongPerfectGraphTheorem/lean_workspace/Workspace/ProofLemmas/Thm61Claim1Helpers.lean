import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.DegenerateK4Cycle
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_1

/-!
# Track surgery for the proof of 6.1(1) — reusable helpers

Everything in this module compiles with **no `sorry`**.  It is the structural half of the open
goal of `Workspace.ProofLemmas.Thm61Claim1.thm_6_1_claim_1`; the geometric half (the two appeals
to 2.1 and the assembly of the fifth outcome) is not here.

| declaration | printed sentence it discharges |
|---|---|
| `k4_structure` | *"For in this case `H` has only four branch-vertices and `J = K₄`. Let the edges of `C` be `a, b, c, d` in order, and let `p, q, r, s` be edges of `H \ {a,b,c,d}` such that the sets of edges incident with branch-vertices of `H` are `{a,b,p}`, `{b,c,q}`, `{c,d,r}` and `{d,a,s}`."*  Produces the two *diagonal* branches `Bp : w₂ ⇝ w₄` and `Bq : w₃ ⇝ w₁`, proves both are **even** (bipartiteness closes each of them into a 4-cycle), vertex-disjoint, internally disjoint from the four branch-vertices, and gives the exact edge decomposition `E(H) = {a,b,c,d} ∪ E(Bp) ∪ E(Bq)`.  The edges `p, q, r, s` of the printed sentence are the first/last edges of `Bp` and `Bq`. |
| `two_one_track` | *"The path `b-p-P-r-d` is odd and has length `≥ 5`; its ends are `Y`-complete and its internal vertices are not, so by 2.1, `Y` contains a leap."*  Applies `Workspace.Statements.S02.SPGT.thm_2_1` to the path `L(T)` of a track `T` of `H` (through `TrackToRungPath.trackRung`) and **discharges 2.1's first outcome**, which cannot occur because two consecutive vertices of `L(T)` always include an internal one.  What is returned is exactly the leap alternative or the length-3 antipath alternative. |
| `hang_track`, `hang_edges` | the construction of the paper's tracks `w₃-w₂-Bp-w₄-w₁` and `w₂-w₃-Bq-w₁-w₄`, whose `L`-paths are `b-p-P-r-d` and `b-q-Q-s-d`.  `hang_edges` is the index dictionary: the two end-edges of `u :: (B ++ [v])` are `ux` and `yv`, and its internal edges are exactly the edges of `B` — i.e. the hypothesis package `two_one_track` consumes. |
| `isTrackFrom_cons` | hanging a vertex on the *front* of a track (`TrackSlice` only has the `concat` direction). |
| `trackEdge_at_head`, `trackEdge_at_last`, `trackEdge_avoids` | *"the sets of edges incident with branch-vertices of `H` are `{a,b,p}`, …"*: the only edge of a branch containing an end of that branch is the corresponding end-edge, and an edge of a branch never contains a vertex off it. |
| `trackEdges_of_len_two` | the four cycle edges `a, b, c, d` are whole branches. |
| `geq`, `head_getElem`, `last_getElem`, `edge_subtype_congr` | index bookkeeping. |

Written by the §6.1 proving lane; see `PROVING_NOTES.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm61Claim1Helpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm61Setup

theorem geq {α : Type*} (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i]'hi = l[j]'hj := by subst h; rfl

theorem head_getElem {α : Type*} {l : List α} {a : α} (h : l.head? = some a)
    (h0 : 0 < l.length) : l[0]'h0 = a := by
  cases l with
  | nil => simp at h0
  | cons x t => simpa using h

theorem last_getElem {α : Type*} {l : List α} {a : α} (h : l.getLast? = some a)
    (h0 : 0 < l.length) : l[l.length - 1]'(by omega) = a := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (show l.length - 1 < l.length by
    omega)] at h
  exact Option.some_inj.mp h

/-- The edge set of a two-vertex track is the single edge joining its ends. -/
theorem trackEdges_of_len_two {W : Type*} {D : SimpleGraph W} {q : List W} {x y : W}
    (h : IsTrackFrom D q x y) (hlen : q.length = 2) :
    trackEdges q = ({s(x, y)} : Set (Sym2 W)) := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, q = [u, v] := by
    match q, hlen with
    | [u, v], _ => exact ⟨u, v, rfl⟩
  have hu : u = x := by simpa using h.2.1
  have hv : v = y := by simpa using h.2.2
  subst hu; subst hv
  ext e
  simp only [trackEdges, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
    subst this
    rfl
  · rintro rfl
    exact ⟨0, by simp, rfl⟩

/-- Hanging one further vertex on the *front* of a track. -/
theorem isTrackFrom_cons {W : Type*} {D : SimpleGraph W} {q : List W} {a b x : W}
    (hq : IsTrackFrom D q a b) (hadj : D.Adj x a) (hx : x ∉ q) :
    IsTrackFrom D (x :: q) x b := by
  have hrev : IsTrackFrom D q.reverse b a := TrackSlice.isTrackFrom_reverse hq
  have hxr : x ∉ q.reverse := by rwa [List.mem_reverse]
  have hcat : IsTrackFrom D (q.reverse ++ [x]) b x :=
    TrackSlice.isTrackFrom_concat hrev hadj.symm hxr
  have h := TrackSlice.isTrackFrom_reverse hcat
  rwa [List.reverse_append, List.reverse_reverse] at h

/-- **`u-B-v`**: hang one further vertex on each end of a track, with the index dictionary. -/
theorem hang_track {W : Type*} {D : SimpleGraph W} {B : List W} {x y u v : W}
    (hB : IsTrackFrom D B x y) (hB2 : 2 ≤ B.length)
    (hu : D.Adj u x) (hv : D.Adj y v) (hun : u ∉ B) (hvn : v ∉ B) (huv : u ≠ v) :
    IsTrackFrom D (u :: (B ++ [v])) u v ∧
    (u :: (B ++ [v])).length = B.length + 2 ∧
    (∀ (k : ℕ) (hk : k < B.length) (hk' : k + 1 < (u :: (B ++ [v])).length),
      (u :: (B ++ [v]))[k + 1]'hk' = B[k]'hk) ∧
    (∀ h0 : 0 < (u :: (B ++ [v])).length, (u :: (B ++ [v]))[0]'h0 = u) ∧
    (∀ h : B.length + 1 < (u :: (B ++ [v])).length,
      (u :: (B ++ [v]))[B.length + 1]'h = v) := by
  have hlen : (u :: (B ++ [v])).length = B.length + 2 := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]
  have hvn' : v ∉ B := hvn
  have hcat : IsTrackFrom D (B ++ [v]) x v := TrackSlice.isTrackFrom_concat hB hv hvn'
  have hun' : u ∉ B ++ [v] := by
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hun h
    · exact huv (List.eq_of_mem_singleton h)
  refine ⟨isTrackFrom_cons hcat hu hun', hlen, ?_, ?_, ?_⟩
  · intro k hk hk'
    rw [List.getElem_cons_succ, List.getElem_append_left hk]
  · intro h0
    rfl
  · intro h
    rw [List.getElem_cons_succ,
      List.getElem_append_right (show B.length ≤ B.length by omega)]
    simp

/-- The edges of `u-B-v`: the two end-edges are `ux` and `yv`, and the internal edges are
exactly the edges of `B`.  This is the dictionary that turns the paper's *"the path
`b-p-P-r-d`"* into a hypothesis package for `two_one_track`. -/
theorem hang_edges {W : Type*} {D : SimpleGraph W} {B : List W} {x y u v : W}
    (hB : IsTrackFrom D B x y) (hB2 : 2 ≤ B.length) :
    s((u :: (B ++ [v]))[0]'(by simp),
      (u :: (B ++ [v]))[1]'(by simp only [List.length_cons, List.length_append,
        List.length_singleton, List.length_nil]; omega)) = s(u, x) ∧
    s((u :: (B ++ [v]))[(u :: (B ++ [v])).length - 2]'(by
        simp only [List.length_cons, List.length_append, List.length_singleton,
          List.length_nil]; omega),
      (u :: (B ++ [v]))[(u :: (B ++ [v])).length - 1]'(by
        simp only [List.length_cons, List.length_append, List.length_singleton,
          List.length_nil]; omega)) = s(y, v) ∧
    ∀ i : ℕ, 1 ≤ i → ∀ hi : i + 2 < (u :: (B ++ [v])).length,
      s((u :: (B ++ [v]))[i]'(by omega), (u :: (B ++ [v]))[i + 1]'(by omega))
        = s(B[i - 1]'(by
              simp only [List.length_cons, List.length_append, List.length_singleton,
                List.length_nil] at hi; omega),
            B[i]'(by
              simp only [List.length_cons, List.length_append, List.length_singleton,
                List.length_nil] at hi; omega)) := by
  have hlen : (u :: (B ++ [v])).length = B.length + 2 := by
    simp only [List.length_cons, List.length_append, List.length_singleton, List.length_nil]
  have hpos : 0 < B.length := by omega
  have hx : B[0]'hpos = x := head_getElem hB.2.1 hpos
  have hy : B[B.length - 1]'(by omega) = y := last_getElem hB.2.2 hpos
  have hget : ∀ (k : ℕ) (hk : k < B.length) (hk' : k + 1 < (u :: (B ++ [v])).length),
      (u :: (B ++ [v]))[k + 1]'hk' = B[k]'hk := by
    intro k hk hk'
    rw [List.getElem_cons_succ, List.getElem_append_left hk]
  have hlast : ∀ h : B.length + 1 < (u :: (B ++ [v])).length,
      (u :: (B ++ [v]))[B.length + 1]'h = v := by
    intro h
    rw [List.getElem_cons_succ, List.getElem_append_right (show B.length ≤ B.length by omega)]
    simp
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (u :: (B ++ [v]))[1]'(by omega) = x := by
      have h := hget 0 hpos (show 0 + 1 < (u :: (B ++ [v])).length by omega)
      rw [hx] at h
      exact h
    rw [h1]
    rfl
  · have e1 : (u :: (B ++ [v]))[(u :: (B ++ [v])).length - 2]'(by omega) = y := by
      have h := hget (B.length - 1) (show B.length - 1 < B.length by omega)
        (show (B.length - 1) + 1 < (u :: (B ++ [v])).length by omega)
      rw [hy] at h
      rw [geq (u :: (B ++ [v]))
        (show (u :: (B ++ [v])).length - 2 = (B.length - 1) + 1 by omega) (by omega) (by omega)]
      exact h
    have e2 : (u :: (B ++ [v]))[(u :: (B ++ [v])).length - 1]'(by omega) = v := by
      rw [geq (u :: (B ++ [v]))
        (show (u :: (B ++ [v])).length - 1 = B.length + 1 by omega) (by omega) (by omega)]
      exact hlast (by omega)
    rw [e1, e2]
  · intro i hi1 hi
    have hi' : i + 2 < B.length + 2 := by rwa [hlen] at hi
    have e1 : (u :: (B ++ [v]))[i]'(by omega) = B[i - 1]'(by omega) := by
      rw [geq (u :: (B ++ [v])) (show i = (i - 1) + 1 by omega) (by omega) (by omega)]
      exact hget (i - 1) (by omega) (by omega)
    have e2 : (u :: (B ++ [v]))[i + 1]'(by omega) = B[i]'(by omega) :=
      hget i (by omega) (by omega)
    rw [e1, e2]

theorem edge_subtype_congr {W : Type*} {H : SimpleGraph W} {e f : Sym2 W}
    (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) (h : e = f) :
    (⟨e, he⟩ : ↥H.edgeSet) = ⟨f, hf⟩ := Subtype.ext h

/-- **2.1, applied to the path `L(T)` of a track `T` of `H`.**

PAPER (proof of 6.1(1), printed p. 29): *"The path `b-p-P-r-d` is odd and has length `≥ 5`; its
ends are `Y`-complete and its internal vertices are not, so by 2.1, `Y` contains a leap."*

The first outcome of 2.1 — an `X`-complete edge of the path — is impossible here, because two
consecutive vertices of `L(T)` always include an internal one. -/
theorem two_one_track
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    (Z : Set V) (hZanti : AnticonnectedSet G Z) (hZK : ∀ y ∈ Z, y ∉ K)
    (T : List (Fin n)) (hT : IsTrackList H T) (h5 : 5 ≤ T.length)
    (hpar : T.length % 2 = 1)
    (h0 : s(T[0]'(by omega), T[1]'(by omega)) ∈ completeEdges G H K φ Z)
    (hlast : s(T[T.length - 2]'(by omega), T[T.length - 1]'(by omega))
      ∈ completeEdges G H K φ Z)
    (hint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < T.length,
      s(T[i]'(by omega), T[i + 1]'(by omega)) ∉ completeEdges G H K φ Z) :
    (5 ≤ pathLength (TrackToRungPath.trackRung φ T hT) ∧
      ∃ α ∈ Z, ∃ β ∈ Z, IsLeapForPath G (TrackToRungPath.trackRung φ T hT) α β) ∨
    (pathLength (TrackToRungPath.trackRung φ T hT) = 3 ∧
      ∃ cc dd : V, SPGT.interior (TrackToRungPath.trackRung φ T hT) = [cc, dd] ∧
        ∃ qq : List V, IsAntipathFrom G qq cc dd ∧ Odd (pathLength qq) ∧
          ∀ w ∈ SPGT.interior qq, w ∈ Z) := by
  classical
  set p : List V := TrackToRungPath.trackRung φ T hT with hpdef
  have hlen : p.length = T.length - 1 := by
    simp [hpdef, TrackToRungPath.trackRung_length, trackLength]
  have hplen : 4 ≤ p.length := by omega
  have hval : ∀ (i : ℕ) (hi : i < p.length) (hi' : i + 1 < T.length)
      (he : s(T[i]'(by omega), T[i + 1]'hi') ∈ H.edgeSet),
      p[i]'hi = (φ ⟨s(T[i]'(by omega), T[i + 1]'hi'), he⟩ : V) := by
    intro i hi hi' he
    exact TrackToRungPath.trackRung_getElem φ T hT i hi hi' he
  have hpath : IsPathList G p := TrackToRungPath.trackRung_isPathList φ T hT (by
    simp only [trackLength]; omega)
  have hpfrom : IsPathFrom G p (p[0]'(by omega)) (p[p.length - 1]'(by omega)) := by
    refine ⟨hpath, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < p.length by omega)]
    · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (show p.length - 1 < p.length by
        omega)]
  have hpK : ∀ x ∈ p, x ∈ K := TrackToRungPath.trackRung_subset_K φ T hT
  have hend0 : VertexComplete G (p[0]'(by omega)) Z := by
    obtain ⟨he, hc⟩ := h0
    rw [hval 0 (by omega) (by omega) he]
    exact hc
  have hendl : VertexComplete G (p[p.length - 1]'(by omega)) Z := by
    obtain ⟨he, hc⟩ := hlast
    have hek : s(T[p.length - 1]'(show p.length - 1 < T.length by omega),
        T[p.length - 1 + 1]'(show p.length - 1 + 1 < T.length by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hT (p.length - 1) (by omega)
    have hEq : s(T[p.length - 1]'(show p.length - 1 < T.length by omega),
        T[p.length - 1 + 1]'(show p.length - 1 + 1 < T.length by omega))
        = s(T[T.length - 2]'(show T.length - 2 < T.length by omega),
            T[T.length - 1]'(show T.length - 1 < T.length by omega)) := by
      rw [geq T (show p.length - 1 = T.length - 2 by omega)
        (show p.length - 1 < T.length by omega) (show T.length - 2 < T.length by omega),
        geq T (show p.length - 1 + 1 = T.length - 1 by omega)
        (show p.length - 1 + 1 < T.length by omega) (show T.length - 1 < T.length by omega)]
    rw [hval (p.length - 1) (by omega) (by omega) hek, edge_subtype_congr hek he hEq]
    exact hc
  have hnotc : ∀ (i : ℕ) (hi : i < p.length), 1 ≤ i → i + 1 < p.length →
      ¬ VertexComplete G (p[i]'hi) Z := by
    intro i hi hi1 hi2 hcon
    refine hint i hi1 (by omega) ⟨TrackToRungPath.trackEdge_mem_edgeSet hT i (by omega), ?_⟩
    rw [hval i hi (by omega) (TrackToRungPath.trackEdge_mem_edgeSet hT i (by omega))] at hcon
    exact hcon
  have hpZ : ∀ w ∈ p, w ∉ Z := by
    intro w hw hwZ
    exact hZK w hwZ (hpK w hw)
  have hnoedge : ¬ ∃ u ∈ p, ∃ v ∈ p, EdgeComplete G Z u v := by
    rintro ⟨u, hu, v, hv, hadj, hcu, hcv⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    have hcons := (PathBasics.path_adj_iff hpath hi hj).mp hadj
    rcases hcons with h | h
    · rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact hnotc j hj (by omega) (by omega) hcv
      · exact hnotc i hi hipos (by omega) hcu
    · rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact hnotc i hi (by omega) (by omega) hcu
      · exact hnotc j hj hjpos (by omega) hcv
  have hoddp : Odd (pathLength p) := by
    rw [pathLength, hlen]
    exact Nat.odd_iff.mpr (by omega)
  rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG Z hZanti p (p[0]'(by omega))
      (p[p.length - 1]'(by omega)) hpfrom hpZ hoddp hend0 hendl with h | h | h
  · exact absurd h hnoedge
  · exact Or.inl h
  · exact Or.inr h

/-- The only edge of a track containing its first vertex is its first edge. -/
theorem trackEdge_at_head {W : Type*} {D : SimpleGraph W} {B : List W} {x y : W}
    (hB : IsTrackFrom D B x y) (h2 : 2 ≤ B.length)
    {e : Sym2 W} (he : e ∈ trackEdges B) (hx : x ∈ e) :
    e = s(B[0]'(by omega), B[1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  have hnd : B.Nodup := hB.1.2.1
  have hx0 : B[0]'(by omega) = x := head_getElem hB.2.1 (by omega)
  have h : x = B[i]'(by omega) ∨ x = B[i + 1]'hi := by simpa using hx
  have hi0 : i = 0 := by
    rcases h with h | h
    · have := hnd.getElem_inj_iff.mp (hx0.trans h) ; omega
    · have := hnd.getElem_inj_iff.mp (hx0.trans h) ; omega
  subst hi0
  rfl

/-- The only edge of a track containing its last vertex is its last edge. -/
theorem trackEdge_at_last {W : Type*} {D : SimpleGraph W} {B : List W} {x y : W}
    (hB : IsTrackFrom D B x y) (h2 : 2 ≤ B.length)
    {e : Sym2 W} (he : e ∈ trackEdges B) (hy : y ∈ e) :
    e = s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  have hnd : B.Nodup := hB.1.2.1
  have hyl : B[B.length - 1]'(by omega) = y := last_getElem hB.2.2 (by omega)
  have h : y = B[i]'(by omega) ∨ y = B[i + 1]'hi := by simpa using hy
  have hi0 : i = B.length - 2 := by
    rcases h with h | h
    · have := hnd.getElem_inj_iff.mp (hyl.trans h) ; omega
    · have := hnd.getElem_inj_iff.mp (hyl.trans h) ; omega
  subst hi0
  congr 1
  exact geq B (by omega) _ _

/-- An edge of a track never contains a vertex off the track. -/
theorem trackEdge_avoids {W : Type*} {B : List W} {v : W} (hv : v ∉ B)
    {e : Sym2 W} (he : e ∈ trackEdges B) : v ∉ e := by
  obtain ⟨i, hi, rfl⟩ := he
  intro hmem
  have h : v = B[i]'(by omega) ∨ v = B[i + 1]'hi := by simpa using hmem
  rcases h with rfl | rfl
  · exact hv (List.getElem_mem _)
  · exact hv (List.getElem_mem _)

/-- **The structure of a bipartite `K₄`-subdivision whose branch-vertices form a 4-cycle.**

PAPER (proof of 6.1(1), printed p. 29): *"Let the edges of `C` be `a, b, c, d` in order, and let
`p, q, r, s` be edges of `H \ {a,b,c,d}` such that the sets of edges incident with
branch-vertices of `H` are `{a,b,p}`, `{b,c,q}`, `{c,d,r}` and `{d,a,s}`."*

`Bp` is the branch of `H` from `w₂` to `w₄` (it carries `p` and `r`); `Bq` is the branch from
`w₃` to `w₁` (it carries `q` and `s`).  Both are even, because `H` is bipartite and the
4-cycle closes them up. -/
theorem k4_structure {n : ℕ} {H : SimpleGraph (Fin n)}
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H) (hbip : H.IsBipartite)
    (w₁ w₂ w₃ w₄ : Fin n) (hnd : [w₁, w₂, w₃, w₄].Nodup)
    (hbv : branchVertices H = ({w₁, w₂, w₃, w₄} : Set (Fin n)))
    (hc₁ : H.Adj w₁ w₂) (hc₂ : H.Adj w₂ w₃) (hc₃ : H.Adj w₃ w₄) (hc₄ : H.Adj w₄ w₁) :
    ∃ Bp Bq : List (Fin n),
      IsTrackFrom H Bp w₂ w₄ ∧ IsTrackFrom H Bq w₃ w₁ ∧
      2 ≤ trackLength Bp ∧ 2 ≤ trackLength Bq ∧
      Even (trackLength Bp) ∧ Even (trackLength Bq) ∧
      (∀ x ∈ Bp, x ∉ Bq) ∧
      (∀ x ∈ Bp, x ≠ w₁ ∧ x ≠ w₃) ∧ (∀ x ∈ Bq, x ≠ w₂ ∧ x ≠ w₄) ∧
      H.edgeSet =
        ({s(w₁, w₂), s(w₂, w₃), s(w₃, w₄), s(w₄, w₁)} : Set (Sym2 (Fin n)))
          ∪ trackEdges Bp ∪ trackEdges Bq := by
  classical
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  obtain ⟨col⟩ := hbip
  have top : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v huv; rw [SimpleGraph.top_adj]; exact huv
  -- the four cycle vertices are pairwise distinct
  have d12 : w₁ ≠ w₂ := by rintro rfl; simp at hnd
  have d13 : w₁ ≠ w₃ := by rintro rfl; simp at hnd
  have d14 : w₁ ≠ w₄ := by rintro rfl; simp at hnd
  have d23 : w₂ ≠ w₃ := by rintro rfl; simp at hnd
  have d24 : w₂ ≠ w₄ := by rintro rfl; simp at hnd
  have d34 : w₃ ≠ w₄ := by rintro rfl; simp at hnd
  -- `range ι = branchVertices H = {w₁, w₂, w₃, w₄}`
  have hdeg4 : ∀ u : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected (⊤ : SimpleGraph (Fin 4))
      SubdivisionCounting.k4_three_connected
  have hA : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlenT hdisjint hnew hdeg4
  have hB : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  have hrange : Set.range ι = ({w₁, w₂, w₃, w₄} : Set (Fin n)) := by
    rw [← hbv]; exact Set.Subset.antisymm hA hB
  obtain ⟨a₁, ha₁⟩ : w₁ ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨a₂, ha₂⟩ : w₂ ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨a₃, ha₃⟩ : w₃ ∈ Set.range ι := by rw [hrange]; simp
  obtain ⟨a₄, ha₄⟩ : w₄ ∈ Set.range ι := by rw [hrange]; simp
  have i12 : a₁ ≠ a₂ := fun h => d12 (by rw [← ha₁, ← ha₂, h])
  have i13 : a₁ ≠ a₃ := fun h => d13 (by rw [← ha₁, ← ha₃, h])
  have i14 : a₁ ≠ a₄ := fun h => d14 (by rw [← ha₁, ← ha₄, h])
  have i23 : a₂ ≠ a₃ := fun h => d23 (by rw [← ha₂, ← ha₃, h])
  have i24 : a₂ ≠ a₄ := fun h => d24 (by rw [← ha₂, ← ha₄, h])
  have i34 : a₃ ≠ a₄ := fun h => d34 (by rw [← ha₃, ← ha₄, h])
  -- the four indices exhaust `Fin 4`
  have huniv : ({a₁, a₂, a₃, a₄} : Finset (Fin 4)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_insert_of_notMem (by simp [i12, i13, i14]),
      Finset.card_insert_of_notMem (by simp [i23, i24]),
      Finset.card_insert_of_notMem (by simp [i34]), Finset.card_singleton]
    simp
  have hall : ∀ x : Fin 4, x = a₁ ∨ x = a₂ ∨ x = a₃ ∨ x = a₄ := by
    intro x
    have hx : x ∈ ({a₁, a₂, a₃, a₄} : Finset (Fin 4)) := by rw [huniv]; exact Finset.mem_univ x
    simpa using hx
  -- an edge between two branch-vertices is a whole track
  have hshort : ∀ p q : Fin 4, H.Adj (ι p) (ι q) → (T p q).length = 2 := fun p q hpq =>
    DegenerateK4Cycle.adj_branch_forces_short_track hι htrack hrev hnew hedges hpq
  have hs12 : (T a₁ a₂).length = 2 := hshort a₁ a₂ (by rw [ha₁, ha₂]; exact hc₁)
  have hs23 : (T a₂ a₃).length = 2 := hshort a₂ a₃ (by rw [ha₂, ha₃]; exact hc₂)
  have hs34 : (T a₃ a₄).length = 2 := hshort a₃ a₄ (by rw [ha₃, ha₄]; exact hc₃)
  have hs41 : (T a₄ a₁).length = 2 := hshort a₄ a₁ (by rw [ha₄, ha₁]; exact hc₄)
  -- the two diagonal branches
  have hBp : IsTrackFrom H (T a₂ a₄) w₂ w₄ := by
    have := htrack a₂ a₄ (top _ _ i24); rwa [ha₂, ha₄] at this
  have hBq : IsTrackFrom H (T a₃ a₁) w₃ w₁ := by
    have := htrack a₃ a₁ (top _ _ i13.symm); rwa [ha₃, ha₁] at this
  -- parity: `H` is bipartite and the 4-cycle closes each diagonal branch
  have hcolval : ∀ u v : Fin n, H.Adj u v → (col u : ℕ) ≠ (col v : ℕ) :=
    fun u v h hcon => col.valid h (Fin.val_injective hcon)
  have hb1 := (col w₁).isLt
  have hb2 := (col w₂).isLt
  have hb3 := (col w₃).isLt
  have hb4 := (col w₄).isLt
  have hc24 : (col w₂ : ℕ) = (col w₄ : ℕ) := by
    have e1 := hcolval w₁ w₂ hc₁
    have e2 := hcolval w₄ w₁ hc₄
    omega
  have hc31 : (col w₃ : ℕ) = (col w₁ : ℕ) := by
    have e1 := hcolval w₂ w₃ hc₂
    have e2 := hcolval w₁ w₂ hc₁
    omega
  have hposP : 0 < (T a₂ a₄).length := List.length_pos_of_ne_nil hBp.1.1
  have hposQ : 0 < (T a₃ a₁).length := List.length_pos_of_ne_nil hBq.1.1
  have hevenP : Even (trackLength (T a₂ a₄)) := by
    have hcc := DegenerateK4Tracks.track_color col hBp.1 ((T a₂ a₄).length - 1)
      (by omega) hposP
    rw [last_getElem hBp.2.2 hposP, head_getElem hBp.2.1 hposP] at hcc
    rw [trackLength, Nat.even_iff]
    omega
  have hevenQ : Even (trackLength (T a₃ a₁)) := by
    have hcc := DegenerateK4Tracks.track_color col hBq.1 ((T a₃ a₁).length - 1)
      (by omega) hposQ
    rw [last_getElem hBq.2.2 hposQ, head_getElem hBq.2.1 hposQ] at hcc
    rw [trackLength, Nat.even_iff]
    omega
  have h1P : 1 ≤ trackLength (T a₂ a₄) := hlenT a₂ a₄ (top _ _ i24)
  have h1Q : 1 ≤ trackLength (T a₃ a₁) := hlenT a₃ a₁ (top _ _ i13.symm)
  -- every vertex of a diagonal branch is an end or is not a branch-vertex
  have hendsP : ∀ x ∈ T a₂ a₄, x ∈ trackInterior (T a₂ a₄) ∨ x = w₂ ∨ x = w₄ := by
    intro x hx
    by_cases hint : x ∈ trackInterior (T a₂ a₄)
    · exact Or.inl hint
    · rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hx hint hposP with h | h
      · exact Or.inr (Or.inl (by rw [h, head_getElem hBp.2.1 hposP]))
      · exact Or.inr (Or.inr (by rw [h, last_getElem hBp.2.2 hposP]))
  have hendsQ : ∀ x ∈ T a₃ a₁, x ∈ trackInterior (T a₃ a₁) ∨ x = w₃ ∨ x = w₁ := by
    intro x hx
    by_cases hint : x ∈ trackInterior (T a₃ a₁)
    · exact Or.inl hint
    · rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hx hint hposQ with h | h
      · exact Or.inr (Or.inl (by rw [h, head_getElem hBq.2.1 hposQ]))
      · exact Or.inr (Or.inr (by rw [h, last_getElem hBq.2.2 hposQ]))
  have hintP : ∀ x ∈ trackInterior (T a₂ a₄), x ∉ ({w₁, w₂, w₃, w₄} : Set (Fin n)) := by
    intro x hx
    rw [← hrange]
    exact hnew a₂ a₄ (top _ _ i24) x hx
  have hintQ : ∀ x ∈ trackInterior (T a₃ a₁), x ∉ ({w₁, w₂, w₃, w₄} : Set (Fin n)) := by
    intro x hx
    rw [← hrange]
    exact hnew a₃ a₁ (top _ _ i13.symm) x hx
  have hpairne : s(a₂, a₄) ≠ s(a₃, a₁) := by
    intro hcon
    rcases Sym2.eq_iff.mp hcon with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact i23 h1
    · exact i12 h1.symm
  have hpP : trackLength (T a₂ a₄) % 2 = 0 := Nat.even_iff.mp hevenP
  have hpQ : trackLength (T a₃ a₁) % 2 = 0 := Nat.even_iff.mp hevenQ
  refine ⟨T a₂ a₄, T a₃ a₁, hBp, hBq, by omega, by omega, hevenP, hevenQ, ?_, ?_, ?_, ?_⟩
  · -- the two diagonal branches are vertex-disjoint
    intro x hx hx'
    rcases hendsP x hx with hint | hxw | hxw
    · exact hdisjint a₂ a₄ a₃ a₁ (top _ _ i24) (top _ _ i13.symm) hpairne x hint hx'
    · rcases hendsQ x hx' with hint' | hxw' | hxw'
      · exact hintQ x hint' (by rw [hxw]; simp)
      · exact d23 (hxw.symm.trans hxw')
      · exact d12 (hxw.symm.trans hxw').symm
    · rcases hendsQ x hx' with hint' | hxw' | hxw'
      · exact hintQ x hint' (by rw [hxw]; simp)
      · exact d34 (hxw.symm.trans hxw').symm
      · exact d14 (hxw.symm.trans hxw').symm
  · intro x hx
    rcases hendsP x hx with hint | hxw | hxw
    · exact ⟨fun h => hintP x hint (by rw [h]; simp), fun h => hintP x hint (by rw [h]; simp)⟩
    · exact ⟨fun h => d12 (hxw.symm.trans h).symm, fun h => d23 (hxw.symm.trans h)⟩
    · exact ⟨fun h => d14 (hxw.symm.trans h).symm, fun h => d34 (hxw.symm.trans h).symm⟩
  · intro x hx
    rcases hendsQ x hx with hint | hxw | hxw
    · exact ⟨fun h => hintQ x hint (by rw [h]; simp), fun h => hintQ x hint (by rw [h]; simp)⟩
    · exact ⟨fun h => d23 (hxw.symm.trans h).symm, fun h => d34 (hxw.symm.trans h)⟩
    · exact ⟨fun h => d12 (hxw.symm.trans h), fun h => d14 (hxw.symm.trans h)⟩
  · -- the edge-set decomposition
    have hE12 : trackEdges (T a₁ a₂) = ({s(w₁, w₂)} : Set (Sym2 (Fin n))) := by
      have := htrack a₁ a₂ (top _ _ i12)
      rw [ha₁, ha₂] at this
      exact trackEdges_of_len_two this hs12
    have hE23 : trackEdges (T a₂ a₃) = ({s(w₂, w₃)} : Set (Sym2 (Fin n))) := by
      have := htrack a₂ a₃ (top _ _ i23)
      rw [ha₂, ha₃] at this
      exact trackEdges_of_len_two this hs23
    have hE34 : trackEdges (T a₃ a₄) = ({s(w₃, w₄)} : Set (Sym2 (Fin n))) := by
      have := htrack a₃ a₄ (top _ _ i34)
      rw [ha₃, ha₄] at this
      exact trackEdges_of_len_two this hs34
    have hE41 : trackEdges (T a₄ a₁) = ({s(w₄, w₁)} : Set (Sym2 (Fin n))) := by
      have := htrack a₄ a₁ (top _ _ i14.symm)
      rw [ha₄, ha₁] at this
      exact trackEdges_of_len_two this hs41
    have hrevE : ∀ u v : Fin 4, u ≠ v → trackEdges (T v u) = trackEdges (T u v) := by
      intro u v huv
      rw [hrev u v (top _ _ huv), SubdivisionCounting.trackEdges_reverse]
    rw [hedges]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨u, v, huv, hmem⟩
      have huv' : u ≠ v := by simpa using huv
      rcases hall u with rfl | rfl | rfl | rfl <;> rcases hall v with rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl huv'
          | (rw [hE12] at hmem; simp at hmem; simp [hmem])
          | (rw [hE23] at hmem; simp at hmem; simp [hmem])
          | (rw [hE34] at hmem; simp at hmem; simp [hmem])
          | (rw [hE41] at hmem; simp at hmem; simp [hmem])
          | (rw [hrevE _ _ i12, hE12] at hmem; simp at hmem; simp [hmem])
          | (rw [hrevE _ _ i23, hE23] at hmem; simp at hmem; simp [hmem])
          | (rw [hrevE _ _ i34, hE34] at hmem; simp at hmem; simp [hmem])
          | (rw [hrevE _ _ i14.symm, hE41] at hmem; simp at hmem; simp [hmem])
          | (exact Or.inl (Or.inr hmem))
          | (rw [hrevE _ _ i24] at hmem; exact Or.inl (Or.inr hmem))
          | (exact Or.inr hmem)
          | (rw [hrevE _ _ i13.symm] at hmem; exact Or.inr hmem)
    · rintro ((he | he) | he)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact ⟨a₁, a₂, top _ _ i12, by rw [hE12]; simp⟩
        · exact ⟨a₂, a₃, top _ _ i23, by rw [hE23]; simp⟩
        · exact ⟨a₃, a₄, top _ _ i34, by rw [hE34]; simp⟩
        · exact ⟨a₄, a₁, top _ _ i14.symm, by rw [hE41]; simp⟩
      · exact ⟨a₂, a₄, top _ _ i24, he⟩
      · exact ⟨a₃, a₁, top _ _ i13.symm, he⟩

end Workspace.ProofLemmas.Thm61Claim1Helpers
