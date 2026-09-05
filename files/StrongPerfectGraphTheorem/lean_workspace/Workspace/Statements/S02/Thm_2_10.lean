/-  Proof attempt for statement 2.10 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 11).

    PRINTED PROOF (verbatim, `paper/proofs/2_10.md`):

      "Let the vertices of C be p1, ..., pn in order, where u = p1 and v = pn.  Let
       G1 = G|(V(C) u X), and let G2 = G1 \ e.  If G2 is Berge, then from 2.1 applied to the
       path C \ e in G2 it follows that X contains a leap for C at uv.  So we may assume that
       G2 is not Berge.  Consequently it has an odd hole or antihole D say, and since D is not
       an odd hole or antihole in G1 it must use both p1 and pn.  Suppose first that D is an odd
       hole.  Since every vertex in X is adjacent to both p1 and pn it follows that at most one
       vertex of X is in D; and since G2 \ X has no cycles, there is exactly one vertex of X in
       D, say x.  Hence D \ x is a path of G2 \ X between p1 and pn, and so D \ x = C \ e; and
       since D is a hole of G2 it follows that x has no neighbours in {p2, ..., p_{n-1}}, and
       therefore is a hat as required.  Next assume that D is an antihole.  Since it uses both
       p1 and pn, and they are nonadjacent in G2, it follows that they are consecutive in D, so
       the vertices of D can be numbered d1, ..., dm in order, where d1 = p1 and dm = pn, and
       therefore m >= 5.  Consequently, both d2 and d_{m-1} are not in X, since they are not
       complete to {p1, pn}, and therefore d1, d2, d_{m-1}, dm are vertices of C.  Yet
       d1 d_{m-1}, d_{m-1} d2, d2 dm are edges of G1, which is impossible since n >= 6.
       This proves 2.10."

    MAP ONTO THE LEAN PROOF.

    * `G1 = G|(V(C) u X)` is `bG1 = RestrictGraph.restrictTo G (bW c X)`: the vertex type is NOT
      changed, the discarded vertices are *isolated*.  `bG2 = bG1.deleteEdges {s(u,v)}` is
      `G2 = G1 \ e`.  `bG2_adj_of_mem` is the one transfer everything goes through: inside
      `V(C) u X`, `G2` has exactly the edges of `G \ e`.
    * `branch_berge` is *"If G2 is Berge, then from 2.1 applied to the path C \ e in G2 ..."*.
      `C \ e` is `PathGlue.isPathFrom_hole_deleteEdges`, which is precisely the path
      `IsLeapForHole` is defined by; 2.1's first outcome is killed because the only `X`-complete
      vertices of `C` are `u, v` and the deleted edge is exactly `uv`, and its third by `n >= 6`.
    * `no_odd_antihole` is the printed antihole paragraph.  `hole_no_short_chord` is the
      arithmetic content of *"which is impossible since n >= 6"*: on a hole of length >= 6 a
      neighbour of `s` other than `t` and a neighbour of `t` other than `s` are at cyclic
      distance 3.
    * `hole_gives_hat` is the printed odd-hole paragraph.  *"at most one vertex of X is in D"*
      is `two_common_nbrs` (two common neighbours of two distinct nonadjacent hole vertices force
      length 4); *"since G2 \ X has no cycles"* is `PathGlue.no_hole_in_path`; and
      *"D \ x = C \ e"* is `PathGlue.exists_pos_of_subpath` plus a pigeonhole: the position map
      of `D \ x` along `C \ e` is injective into `[0,n)` and moves the two ends from position
      `0` to position `n-1`, so it is a bijection and `D \ x` covers `V(C)`.
    * The paper's "u = p1, v = pn" fixes an orientation of the edge; the Lean statement allows
      either (`IsLeapForHole G c u v` or `IsLeapForHole G c v u`), and `core` is called once per
      orientation, with `hat_symm` converting the hat back.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.RestrictGraph
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.Statements.S02.Thm_2_1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

namespace SPGT

section Aux

variable {V : Type*}

/-- `V(C) ∪ X`, the paper's `G₁ = G|(V(C) ∪ X)` vertex set. -/
private def bW (c : List V) (X : Set V) : Set V := {w | w ∈ c} ∪ X

/-- `G₁ = G|(V(C) ∪ X)`, realised by isolating rather than deleting. -/
private def bG1 (G : SimpleGraph V) (c : List V) (X : Set V) : SimpleGraph V :=
  RestrictGraph.restrictTo G (bW c X)

/-- `G₂ = G₁ \ e`. -/
private def bG2 (G : SimpleGraph V) (c : List V) (X : Set V) (u v : V) : SimpleGraph V :=
  (bG1 G c X).deleteEdges {s(u, v)}

private theorem mem_bW {c : List V} {X : Set V} {a : V} : a ∈ bW c X ↔ (a ∈ c ∨ a ∈ X) := Iff.rfl

private theorem bG1_adj {G : SimpleGraph V} {c : List V} {X : Set V} (x y : V) :
    (bG1 G c X).Adj x y ↔ (G.Adj x y ∧ (x ∈ c ∨ x ∈ X) ∧ (y ∈ c ∨ y ∈ X)) := Iff.rfl

private theorem bG2_adj {G : SimpleGraph V} {c : List V} {X : Set V} {u v : V} (x y : V) :
    (bG2 G c X u v).Adj x y ↔
      ((G.Adj x y ∧ (x ∈ c ∨ x ∈ X) ∧ (y ∈ c ∨ y ∈ X)) ∧ s(x, y) ≠ s(u, v)) := by
  rw [bG2, SimpleGraph.deleteEdges_adj, bG1_adj, Set.mem_singleton_iff]

/-- Inside `V(C) ∪ X`, `G₂` has exactly the edges of `G \ e`. -/
private theorem bG2_adj_of_mem {G : SimpleGraph V} {c : List V} {X : Set V} {u v : V} {x y : V}
    (hx : x ∈ c ∨ x ∈ X) (hy : y ∈ c ∨ y ∈ X) :
    (bG2 G c X u v).Adj x y ↔ (G.deleteEdges {s(u, v)}).Adj x y := by
  rw [bG2_adj, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h, -, -⟩, hne⟩
    exact ⟨h, hne⟩
  · rintro ⟨h, hne⟩
    exact ⟨⟨h, hx, hy⟩, hne⟩

/-- Every vertex of a hole of `G₂` lies in `V(C) ∪ X`. -/
private theorem mem_bW_of_mem_hole {G : SimpleGraph V} {c : List V} {X : Set V} {u v : V}
    {D : List V} (hD : IsHoleList (bG2 G c X u v) D) : ∀ z ∈ D, (z ∈ c ∨ z ∈ X) := by
  obtain ⟨h4, hnd, hadj⟩ := hD
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hz
  have hpos : 0 < D.length := by omega
  have hj : (i + 1) % D.length < D.length := Nat.mod_lt _ hpos
  exact (((hadj i ((i + 1) % D.length) hi hj).mpr (Or.inl rfl))).1.2.1

/-- A vertex outside `V(C) ∪ X` is isolated in `G₂`. -/
private theorem bG2_isolated {G : SimpleGraph V} {c : List V} {X : Set V} {u v : V} {z : V}
    (hz : ¬ (z ∈ c ∨ z ∈ X)) : ∀ w, ¬ (bG2 G c X u v).Adj z w := by
  intro w hadj
  exact hz (bG2_adj z w |>.mp hadj).1.2.1

private theorem getElem_congr_idx' {α : Type*} (l : List α) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (h : a = b) : (l[a]'ha) = (l[b]'hb) := by subst h; rfl

/-- `IsHatForHole` is symmetric in the two ends of the deleted edge. -/
private theorem hat_symm {G : SimpleGraph V} {c : List V} {u v h : V}
    (hh : IsHatForHole G c u v h) : IsHatForHole G c v u h :=
  ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2.1.symm, hh.2.2.2.2.2.1, hh.2.2.2.2.1,
    fun x hx h1 h2 => hh.2.2.2.2.2.2 x hx h2 h1⟩

end Aux


section Branch1

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"If `G₂` is Berge, then from 2.1 applied to the path `C \ e` in `G₂` it follows that `X`
contains a leap for `C` at `uv`."* -/
private theorem branch_berge {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    (hX : AnticonnectedSet G X) {c : List V} (hc : IsHoleList G c)
    (hcX : ∀ w ∈ c, w ∉ X) (hn6 : 6 ≤ c.length)
    {u v : V} (hu : u ∈ c) (hv : v ∈ c) (huv : G.Adj u v)
    (hcu : VertexComplete G u X) (hcv : VertexComplete G v X)
    (honly : ∀ w ∈ c, VertexComplete G w X → w = u ∨ w = v)
    {l : ℕ} (hhead : (c.rotate l).head? = some v) (hlast : (c.rotate l).getLast? = some u)
    (hBerge : Berge (bG2 G c X u v)) :
    ∃ a ∈ X, ∃ b ∈ X, IsLeapForPath (G.deleteEdges {s(u, v)}) (c.rotate l) a b := by
  have hPmem : ∀ z, z ∈ c.rotate l ↔ z ∈ c := fun z => List.mem_rotate
  have hPlen : (c.rotate l).length = c.length := List.length_rotate ..
  have hPW : ∀ z ∈ c.rotate l, (z ∈ c ∨ z ∈ X) := fun z hz => Or.inl ((hPmem z).mp hz)
  have hPdel : IsPathFrom (G.deleteEdges {s(u, v)}) (c.rotate l) v u :=
    PathGlue.isPathFrom_hole_deleteEdges hc hhead hlast
  have hP2l : IsPathList (bG2 G c X u v) (c.rotate l) := by
    obtain ⟨hne, hnd, hadj⟩ := hPdel.1
    refine ⟨hne, hnd, fun i j hi hj => ?_⟩
    rw [bG2_adj_of_mem (hPW _ (List.getElem_mem hi)) (hPW _ (List.getElem_mem hj))]
    exact hadj i j hi hj
  have hP2 : IsPathFrom (bG2 G c X u v) (c.rotate l) v u := ⟨hP2l, hhead, hlast⟩
  have hPX : ∀ w ∈ c.rotate l, w ∉ X := fun w hw => hcX w ((hPmem w).mp hw)
  have hceven : c.length % 2 = 0 := by
    have := hG.1 c hc
    rw [Nat.even_iff] at this
    simpa only [holeLength] using this
  have hodd : Odd (pathLength (c.rotate l)) := by
    rw [Nat.odd_iff]
    simp only [pathLength, hPlen]
    omega
  have hcomp2 : ∀ (z : V), z ∈ c → VertexComplete G z X → VertexComplete (bG2 G c X u v) z X := by
    intro z hz hzc x hx
    rw [bG2_adj_of_mem (Or.inl hz) (Or.inr hx), SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff]
    refine ⟨hzc x hx, ?_⟩
    intro hs
    rcases Sym2.eq_iff.mp hs with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact hcX v hv (h2 ▸ hx)
    · exact hcX u hu (h2 ▸ hx)
  have hXanti2 : AnticonnectedSet (bG2 G c X u v) X := by
    have hEq : ((bG2 G c X u v)ᶜ).induce X = (Gᶜ).induce X := by
      ext a b
      constructor
      · rintro ⟨hne, hnadj⟩
        refine ⟨hne, fun hg => hnadj ?_⟩
        rw [bG2_adj]
        refine ⟨⟨hg, Or.inr a.2, Or.inr b.2⟩, ?_⟩
        intro hs
        rcases Sym2.eq_iff.mp hs with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hcX u hu (h1 ▸ a.2)
        · exact hcX v hv (h1 ▸ a.2)
      · rintro ⟨hne, hnadj⟩
        exact ⟨hne, fun hg => hnadj ((bG2_adj _ _).mp hg).1.1⟩
    show ((bG2 G c X u v)ᶜ.induce X).Preconnected
    rw [hEq]
    exact hX
  rcases thm_2_1 (bG2 G c X u v) hBerge X hXanti2 (c.rotate l) v u hP2 hPX hodd
      (hcomp2 v hv hcv) (hcomp2 u hu hcu) with h1 | ⟨-, a, ha, b, hb, hleap⟩ | ⟨h3, -⟩
  · exfalso
    obtain ⟨w, hw, w', hw', hadj, hwc, hw'c⟩ := h1
    have hends : ∀ z ∈ c.rotate l, VertexComplete (bG2 G c X u v) z X → z = u ∨ z = v := by
      intro z hz hzc
      refine honly z ((hPmem z).mp hz) ?_
      intro x hx
      exact ((bG2_adj_of_mem (Or.inl ((hPmem z).mp hz)) (Or.inr hx)).mp (hzc x hx)).1
    have hne := ((bG2_adj w w').mp hadj).2
    rcases hends w hw hwc with hw1 | hw1 <;> rcases hends w' hw' hw'c with hw2 | hw2
    · exact (bG2 G c X u v).ne_of_adj hadj (hw1.trans hw2.symm)
    · exact hne (by rw [hw1, hw2])
    · exact hne (by rw [hw1, hw2, Sym2.eq_swap])
    · exact (bG2 G c X u v).ne_of_adj hadj (hw1.trans hw2.symm)
  · refine ⟨a, ha, b, hb, ?_⟩
    obtain ⟨-, hlen2, hab, hnab, hAd, hBd⟩ := hleap
    have htr : ∀ (x : V), x ∈ X → ∀ (i : ℕ) (hi : i < (c.rotate l).length),
        ((bG2 G c X u v).Adj x ((c.rotate l)[i]'hi)) ↔
          (G.deleteEdges {s(u, v)}).Adj x ((c.rotate l)[i]'hi) :=
      fun x hx i hi => bG2_adj_of_mem (Or.inr hx) (hPW _ (List.getElem_mem hi))
    refine ⟨hPdel.1, hlen2, hab, ?_, ?_, ?_⟩
    · rw [← bG2_adj_of_mem (G := G) (c := c) (X := X) (u := u) (v := v) (Or.inr ha) (Or.inr hb)]
      exact hnab
    · intro i hi
      rw [← htr a ha i hi]
      exact hAd i hi
    · intro i hi
      rw [← htr b hb i hi]
      exact hBd i hi
  · exfalso
    simp only [pathLength, hPlen] at h3
    omega

end Branch1


section Branch2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- On a hole of length `≥ 6`: if `st` is an edge, `z` a neighbour of `s` other than `t`, and
`z'` a neighbour of `t` other than `s`, then `z` and `z'` are at cyclic distance `3`, hence
nonadjacent.  This is the arithmetic behind *"which is impossible since `n ≥ 6`"*. -/
private theorem hole_no_short_chord {n a b e f : ℕ} (hn6 : 6 ≤ n) (ha : a < n) (hb : b < n)
    (he : e < n) (hf : f < n)
    (hst : b = (a + 1) % n ∨ a = (b + 1) % n)
    (hsz : e = (a + 1) % n ∨ a = (e + 1) % n) (heb : e ≠ b)
    (htz : f = (b + 1) % n ∨ b = (f + 1) % n) (hfa : f ≠ a) :
    ¬ (f = (e + 1) % n ∨ e = (f + 1) % n) := by
  simp only [PathGlue.succ_mod_eq ha, PathGlue.succ_mod_eq hb, PathGlue.succ_mod_eq he,
    PathGlue.succ_mod_eq hf] at hst hsz htz ⊢
  split_ifs at hst hsz htz ⊢ <;> omega

/-- `(m - 1 + b) % m = a` when `b` is the cyclic successor of `a`. -/
private theorem rot_last {m a b : ℕ} (ha : a < m) (h : b = (a + 1) % m) : (m - 1 + b) % m = a := by
  rcases (by omega : a + 1 < m ∨ a + 1 = m) with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    subst h
    rw [show m - 1 + (a + 1) = m + a by omega, Nat.add_mod_left, Nat.mod_eq_of_lt ha]
  · rw [h1, Nat.mod_self] at h
    subst h
    rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    omega

/-- *"Next assume that `D` is an antihole … which is impossible since `n ≥ 6`."*  So `G₂` has no
odd antihole. -/
private theorem no_odd_antihole {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    {c : List V} (hc : IsHoleList G c) (hcX : ∀ w ∈ c, w ∉ X) (hn6 : 6 ≤ c.length)
    {u v : V} (hu : u ∈ c) (hv : v ∈ c) (huv : G.Adj u v)
    (hcu : VertexComplete G u X) (hcv : VertexComplete G v X)
    (D : List V) (hD : IsHoleList ((bG2 G c X u v)ᶜ) D) : Even (holeLength D) := by
  by_contra hnev
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hnev
  simp only [holeLength] at hnev
  have h4 : 4 ≤ D.length := hD.1
  have h5 : 5 ≤ D.length := by omega
  have hDW : ∀ z ∈ D, (z ∈ c ∨ z ∈ X) := by
    intro z hz
    by_contra hzz
    exact RestrictGraph.notMem_compl_hole_of_isolated hD (bG2_isolated hzz) hz
  have hagree : ∀ x y : V, s(x, y) ≠ s(u, v) →
      (((bG2 G c X u v)ᶜ).Adj x y ↔ ((bG1 G c X)ᶜ).Adj x y) := by
    intro x y hs
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun hg => h2 ((bG2_adj x y).mpr ⟨(bG1_adj x y).mp hg, hs⟩)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun hg => h2 ((bG1_adj x y).mpr ((bG2_adj x y).mp hg).1)⟩
  have hmiss : ∀ (w : V), w ∈ c → w ∉ D → (∀ x y : V, x ∈ D → y ∈ D → s(x, y) ≠ s(u, v)) →
      False := by
    intro w hw hwD hsne
    have h1 : IsHoleList ((bG1 G c X)ᶜ) D := by
      obtain ⟨ha, hnd, hadj⟩ := hD
      refine ⟨ha, hnd, fun i j hi hj => ?_⟩
      rw [← hagree _ _ (hsne _ _ (List.getElem_mem hi) (List.getElem_mem hj))]
      exact hadj i j hi hj
    have h2 := hG.2 D (RestrictGraph.isHoleList_compl_of_restrict h1)
    rw [Nat.even_iff] at h2
    simp only [holeLength] at h2
    omega
  have huD : u ∈ D := by
    by_contra huD
    exact hmiss u hu huD (by
      intro x y hx hy hs
      rcases Sym2.eq_iff.mp hs with ⟨he, -⟩ | ⟨-, he⟩
      · exact huD (he ▸ hx)
      · exact huD (he ▸ hy))
  have hvD : v ∈ D := by
    by_contra hvD
    exact hmiss v hv hvD (by
      intro x y hx hy hs
      rcases Sym2.eq_iff.mp hs with ⟨-, he⟩ | ⟨he, -⟩
      · exact hvD (he ▸ hy)
      · exact hvD (he ▸ hx))
  have huvc : ((bG2 G c X u v)ᶜ).Adj u v := by
    refine ⟨G.ne_of_adj huv, ?_⟩
    rw [bG2_adj]
    rintro ⟨-, hne⟩
    exact hne rfl
  -- the core: `D` rotated so that `s` is first and `t` last, `{s,t} = {u,v}`
  have key : ∀ (s t : V) (r : ℕ), s ∈ c → t ∈ c → G.Adj s t →
      VertexComplete G s X → VertexComplete G t X →
      (∀ (h : 0 < (D.rotate r).length), ((D.rotate r)[0]'h) = s) →
      (∀ (h : D.length - 1 < (D.rotate r).length), ((D.rotate r)[D.length - 1]'h) = t) →
      False := by
    intro s t r hsc htc hst hsX htX hE0 hEl
    have hE : IsHoleList ((bG2 G c X u v)ᶜ) (D.rotate r) := HoleBasics.isHoleList_rotate hD r
    have hElen : (D.rotate r).length = D.length := List.length_rotate ..
    have hEmem : ∀ z, z ∈ D.rotate r ↔ z ∈ D := fun z => List.mem_rotate
    have hEnd : (D.rotate r).Nodup := hE.2.1
    have h0 : ((D.rotate r)[0]'(by omega)) = s := hE0 (by omega)
    have hl : ((D.rotate r)[D.length - 1]'(by omega)) = t := hEl (by omega)
    -- `E[1]` and `E[m-2]` are old vertices of `C`
    have hnotX : ∀ (k : ℕ) (hk : k < (D.rotate r).length) (w : V),
        w ∈ c → VertexComplete G w X → (((bG2 G c X u v)ᶜ).Adj w ((D.rotate r)[k]'hk)) →
        ((D.rotate r)[k]'hk) ∉ X := by
      intro k hk w hwc hwX hadj hxX
      refine hadj.2 ?_
      rw [bG2_adj]
      refine ⟨⟨hwX _ hxX, Or.inl hwc, Or.inr hxX⟩, ?_⟩
      intro hs2
      rcases Sym2.eq_iff.mp hs2 with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact hcX v hv (h2 ▸ hxX)
      · exact hcX u hu (h2 ▸ hxX)
    have hE1lt : (1 : ℕ) < (D.rotate r).length := by omega
    have hE0lt : (0 : ℕ) < (D.rotate r).length := by omega
    have hEl1lt : D.length - 1 < (D.rotate r).length := by omega
    have hEl2lt : D.length - 2 < (D.rotate r).length := by omega
    have hif0 : ¬ ((0 : ℕ) + 1 = (D.rotate r).length) := by omega
    have hif1 : ¬ ((1 : ℕ) + 1 = (D.rotate r).length) := by omega
    have hifl2 : ¬ (D.length - 2 + 1 = (D.rotate r).length) := by omega
    have hifl1 : D.length - 1 + 1 = (D.rotate r).length := by omega
    have hmod1 : (1 : ℕ) = (0 + 1) % (D.rotate r).length := by
      rw [PathGlue.succ_mod_eq hE0lt, if_neg hif0]
    have hmodl : (D.length - 1 : ℕ) = (D.length - 2 + 1) % (D.rotate r).length := by
      rw [PathGlue.succ_mod_eq hEl2lt, if_neg hifl2]
      omega
    have hadj01 : ((bG2 G c X u v)ᶜ).Adj ((D.rotate r)[0]'hE0lt) ((D.rotate r)[1]'hE1lt) :=
      (HoleBasics.hole_adj_iff hE hE0lt hE1lt).mpr (Or.inl hmod1)
    have hadjl2 : ((bG2 G c X u v)ᶜ).Adj ((D.rotate r)[D.length - 1]'hEl1lt)
        ((D.rotate r)[D.length - 2]'hEl2lt) :=
      (HoleBasics.hole_adj_iff hE hEl1lt hEl2lt).mpr (Or.inr hmodl)
    have h1X : ((D.rotate r)[1]'hE1lt) ∉ X := by
      refine hnotX 1 hE1lt s hsc hsX ?_
      rw [← h0]
      exact hadj01
    have h2X : ((D.rotate r)[D.length - 2]'hEl2lt) ∉ X := by
      refine hnotX (D.length - 2) hEl2lt t htc htX ?_
      rw [← hl]
      exact hadjl2
    have h1c : ((D.rotate r)[1]'hE1lt) ∈ c := by
      rcases hDW _ ((hEmem _).mp (List.getElem_mem hE1lt)) with h | h
      · exact h
      · exact absurd h h1X
    have h2c : ((D.rotate r)[D.length - 2]'hEl2lt) ∈ c := by
      rcases hDW _ ((hEmem _).mp (List.getElem_mem hEl2lt)) with h | h
      · exact h
      · exact absurd h h2X
    -- the three `G` edges of the printed proof
    have hGedge : ∀ (i j : ℕ) (hi : i < (D.rotate r).length) (hj : j < (D.rotate r).length),
        ¬ (j = (i + 1) % (D.rotate r).length ∨ i = (j + 1) % (D.rotate r).length) → i ≠ j →
        G.Adj ((D.rotate r)[i]'hi) ((D.rotate r)[j]'hj) := by
      intro i j hi hj hnc hij
      have hnadj : ¬ ((bG2 G c X u v)ᶜ).Adj ((D.rotate r)[i]'hi) ((D.rotate r)[j]'hj) :=
        fun h => hnc ((HoleBasics.hole_adj_iff hE hi hj).mp h)
      have hne : ((D.rotate r)[i]'hi) ≠ ((D.rotate r)[j]'hj) :=
        fun h => hij (hEnd.getElem_inj_iff.mp h)
      by_contra hg
      exact hnadj ⟨hne, fun hb => hg ((bG2_adj _ _).mp hb).1.1⟩
    have hnc1 : ¬ ((D.length - 2 : ℕ) = (0 + 1) % (D.rotate r).length ∨
        (0 : ℕ) = (D.length - 2 + 1) % (D.rotate r).length) := by
      rw [PathGlue.succ_mod_eq hE0lt, PathGlue.succ_mod_eq hEl2lt, if_neg hif0, if_neg hifl2]
      omega
    have hnc2 : ¬ ((1 : ℕ) = (D.length - 1 + 1) % (D.rotate r).length ∨
        (D.length - 1 : ℕ) = (1 + 1) % (D.rotate r).length) := by
      rw [PathGlue.succ_mod_eq hEl1lt, PathGlue.succ_mod_eq hE1lt, if_pos hifl1, if_neg hif1]
      omega
    have hnc3 : ¬ ((1 : ℕ) = (D.length - 2 + 1) % (D.rotate r).length ∨
        (D.length - 2 : ℕ) = (1 + 1) % (D.rotate r).length) := by
      rw [PathGlue.succ_mod_eq hEl2lt, PathGlue.succ_mod_eq hE1lt, if_neg hifl2, if_neg hif1]
      omega
    have hsz : G.Adj s ((D.rotate r)[D.length - 2]'hEl2lt) := by
      rw [← h0]
      exact hGedge 0 (D.length - 2) hE0lt hEl2lt hnc1 (by omega)
    have htz : G.Adj t ((D.rotate r)[1]'hE1lt) := by
      rw [← hl]
      exact hGedge (D.length - 1) 1 hEl1lt hE1lt hnc2 (by omega)
    have hzz : G.Adj ((D.rotate r)[D.length - 2]'hEl2lt) ((D.rotate r)[1]'hE1lt) :=
      hGedge (D.length - 2) 1 hEl2lt hE1lt hnc3 (by omega)
    -- and now `n ≥ 6` on the hole `C` refutes them
    have hznet : ((D.rotate r)[D.length - 2]'hEl2lt) ≠ t := by
      rw [← hl]
      intro h
      have := hEnd.getElem_inj_iff.mp h
      omega
    have hz'nes : ((D.rotate r)[1]'hE1lt) ≠ s := by
      rw [← h0]
      intro h
      have := hEnd.getElem_inj_iff.mp h
      omega
    obtain ⟨ia, hia, hiaeq⟩ := List.getElem_of_mem hsc
    obtain ⟨ib, hib, hibeq⟩ := List.getElem_of_mem htc
    obtain ⟨ie, hie, hieeq⟩ := List.getElem_of_mem h2c
    obtain ⟨ifx, hif, hifeq⟩ := List.getElem_of_mem h1c
    refine hole_no_short_chord hn6 hia hib hie hif
      ((HoleBasics.hole_adj_iff hc hia hib).mp (by rw [hiaeq, hibeq]; exact hst))
      ((HoleBasics.hole_adj_iff hc hia hie).mp (by rw [hiaeq, hieeq]; exact hsz))
      (fun h => hznet (by rw [← hieeq, ← hibeq]; exact hc.2.1.getElem_inj_iff.mpr h))
      ((HoleBasics.hole_adj_iff hc hib hif).mp (by rw [hibeq, hifeq]; exact htz))
      (fun h => hz'nes (by rw [← hifeq, ← hiaeq]; exact hc.2.1.getElem_inj_iff.mpr h))
      ((HoleBasics.hole_adj_iff hc hie hif).mp (by rw [hieeq, hifeq]; exact hzz))
  -- pick the rotation
  obtain ⟨ia, hia, hiaeq⟩ := List.getElem_of_mem huD
  obtain ⟨ib, hib, hibeq⟩ := List.getElem_of_mem hvD
  have hcyc : ib = (ia + 1) % D.length ∨ ia = (ib + 1) % D.length := by
    refine (HoleBasics.hole_adj_iff hD hia hib).mp ?_
    rw [hiaeq, hibeq]
    exact huvc
  have hrot : ∀ (p q : ℕ) (hp : p < D.length) (hq : q < D.length),
      q = (p + 1) % D.length →
      (∀ (h : 0 < (D.rotate q).length), ((D.rotate q)[0]'h) = ((D)[q]'hq)) ∧
      (∀ (h : D.length - 1 < (D.rotate q).length),
        ((D.rotate q)[D.length - 1]'h) = ((D)[p]'hp)) := by
    intro p q hp hq hpq
    constructor
    · intro h
      have hlt : (0 + q) % D.length < D.length := Nat.mod_lt _ (by omega)
      have hg : ((D.rotate q)[0]'h) = ((D)[(0 + q) % D.length]'hlt) := by
        simp only [List.getElem_rotate, List.length_rotate]
      rw [hg]
      exact getElem_congr_idx' D hlt hq (by rw [Nat.zero_add, Nat.mod_eq_of_lt hq])
    · intro h
      have hlt : (D.length - 1 + q) % D.length < D.length := Nat.mod_lt _ (by omega)
      have hg : ((D.rotate q)[D.length - 1]'h) = ((D)[(D.length - 1 + q) % D.length]'hlt) := by
        simp only [List.getElem_rotate, List.length_rotate]
      rw [hg]
      exact getElem_congr_idx' D hlt hp (rot_last hp hpq)
  rcases hcyc with hcyc | hcyc
  · obtain ⟨e1, e2⟩ := hrot ia ib hia hib hcyc
    exact key v u ib hv hu huv.symm hcv hcu (fun h => (e1 h).trans hibeq)
      (fun h => (e2 h).trans hiaeq)
  · obtain ⟨e1, e2⟩ := hrot ib ia hib hia hcyc
    exact key u v ia hu hv huv hcu hcv (fun h => (e1 h).trans hiaeq)
      (fun h => (e2 h).trans hibeq)

end Branch2


section Branch3

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"Since every vertex in `X` is adjacent to both `p₁` and `pₙ` it follows that at most one
vertex of `X` is in `D`."*  Two common neighbours of two distinct non-adjacent hole vertices
force the hole to have length `4`. -/
private theorem two_common_nbrs {m a b e f : ℕ} (h5 : 5 ≤ m) (ha : a < m) (hb : b < m)
    (he : e < m) (hf : f < m) (hab : a ≠ b) (hef : e ≠ f)
    (h1 : e = (a + 1) % m ∨ a = (e + 1) % m) (h2 : e = (b + 1) % m ∨ b = (e + 1) % m)
    (h3 : f = (a + 1) % m ∨ a = (f + 1) % m) (h4 : f = (b + 1) % m ∨ b = (f + 1) % m) :
    False := by
  simp only [PathGlue.succ_mod_eq ha, PathGlue.succ_mod_eq hb, PathGlue.succ_mod_eq he,
    PathGlue.succ_mod_eq hf] at h1 h2 h3 h4
  split_ifs at h1 h2 h3 h4 <;> omega

/-- *"Suppose first that `D` is an odd hole … and therefore is a hat as required."* -/
private theorem hole_gives_hat {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    {c : List V} (hc : IsHoleList G c) (hcX : ∀ w ∈ c, w ∉ X) (hn6 : 6 ≤ c.length)
    {u v : V} (hu : u ∈ c) (hv : v ∈ c) (huv : G.Adj u v)
    (hcu : VertexComplete G u X) (hcv : VertexComplete G v X)
    {l : ℕ} (hhead : (c.rotate l).head? = some v) (hlast : (c.rotate l).getLast? = some u)
    (D : List V) (hD : IsHoleList (bG2 G c X u v) D) (hDodd : ¬ Even (holeLength D)) :
    ∃ h ∈ X, IsHatForHole G c u v h := by
  classical
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hDodd
  simp only [holeLength] at hDodd
  have h4 : 4 ≤ D.length := hD.1
  have h5 : 5 ≤ D.length := by omega
  have hDW : ∀ z ∈ D, (z ∈ c ∨ z ∈ X) := mem_bW_of_mem_hole hD
  have hDnd : D.Nodup := hD.2.1
  -- the path `C \ e` in `G₂`
  have hPmem : ∀ z, z ∈ c.rotate l ↔ z ∈ c := fun z => List.mem_rotate
  have hPlen : (c.rotate l).length = c.length := List.length_rotate ..
  have hPW : ∀ z ∈ c.rotate l, (z ∈ c ∨ z ∈ X) := fun z hz => Or.inl ((hPmem z).mp hz)
  have hPdel : IsPathFrom (G.deleteEdges {s(u, v)}) (c.rotate l) v u :=
    PathGlue.isPathFrom_hole_deleteEdges hc hhead hlast
  have hP2l : IsPathList (bG2 G c X u v) (c.rotate l) := by
    obtain ⟨hne, hnd, hadj⟩ := hPdel.1
    refine ⟨hne, hnd, fun i j hi hj => ?_⟩
    rw [bG2_adj_of_mem (hPW _ (List.getElem_mem hi)) (hPW _ (List.getElem_mem hj))]
    exact hadj i j hi hj
  have hP0 : ((c.rotate l)[0]'(by omega)) = v :=
    PathBasics.getElem_zero_of_head? hhead (by omega)
  have hPl : ((c.rotate l)[c.length - 1]'(by omega)) = u := by
    have h := PathBasics.getElem_last_of_getLast? hlast (show 0 < (c.rotate l).length by omega)
    exact (getElem_congr_idx' (c.rotate l) (by omega) (by omega) (by omega)).trans h
  -- `u`, `v` are `G₂`-adjacent to every vertex of `X`
  have hXadj : ∀ (w : V), w ∈ c → VertexComplete G w X → ∀ x ∈ X, (bG2 G c X u v).Adj w x := by
    intro w hw hwc x hx
    rw [bG2_adj_of_mem (Or.inl hw) (Or.inr hx), SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff]
    refine ⟨hwc x hx, ?_⟩
    intro hs
    rcases Sym2.eq_iff.mp hs with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact hcX v hv (h2 ▸ hx)
    · exact hcX u hu (h2 ▸ hx)
  have hagree : ∀ x y : V, s(x, y) ≠ s(u, v) →
      ((bG2 G c X u v).Adj x y ↔ (bG1 G c X).Adj x y) := by
    intro x y hs
    rw [bG2_adj, bG1_adj]
    exact ⟨fun h => h.1, fun h => ⟨h, hs⟩⟩
  have hmiss : ∀ (w : V), w ∉ D → (∀ x y : V, x ∈ D → y ∈ D → s(x, y) ≠ s(u, v)) → False := by
    intro w hwD hsne
    have h1 : IsHoleList (bG1 G c X) D := by
      obtain ⟨ha, hnd, hadj⟩ := hD
      refine ⟨ha, hnd, fun i j hi hj => ?_⟩
      rw [← hagree _ _ (hsne _ _ (List.getElem_mem hi) (List.getElem_mem hj))]
      exact hadj i j hi hj
    have h2 := hG.1 D (RestrictGraph.isHoleList_of_restrict h1)
    rw [Nat.even_iff] at h2
    simp only [holeLength] at h2
    omega
  have huD : u ∈ D := by
    by_contra huD
    exact hmiss u huD (by
      intro x y hx hy hs
      rcases Sym2.eq_iff.mp hs with ⟨he, -⟩ | ⟨-, he⟩
      · exact huD (he ▸ hx)
      · exact huD (he ▸ hy))
  have hvD : v ∈ D := by
    by_contra hvD
    exact hmiss v hvD (by
      intro x y hx hy hs
      rcases Sym2.eq_iff.mp hs with ⟨-, he⟩ | ⟨he, -⟩
      · exact hvD (he ▸ hy)
      · exact hvD (he ▸ hx))
  obtain ⟨ia, hia, hiaeq⟩ := List.getElem_of_mem huD
  obtain ⟨ib, hib, hibeq⟩ := List.getElem_of_mem hvD
  have hiab : ia ≠ ib := by
    intro h
    exact G.ne_of_adj huv (by rw [← hiaeq, ← hibeq]; exact hDnd.getElem_inj_iff.mpr h)
  -- at most one vertex of `X` lies on `D`
  have hXuniqD : ∀ x ∈ X, ∀ x' ∈ X, x ∈ D → x' ∈ D → x = x' := by
    intro x hx x' hx' hxD hx'D
    by_contra hne
    obtain ⟨ie, hie, hieeq⟩ := List.getElem_of_mem hxD
    obtain ⟨ifx, hif, hifeq⟩ := List.getElem_of_mem hx'D
    refine two_common_nbrs h5 hia hib hie hif hiab
      (fun h => hne (by rw [← hieeq, ← hifeq]; exact hDnd.getElem_inj_iff.mpr h)) ?_ ?_ ?_ ?_
    · exact (HoleBasics.hole_adj_iff hD hia hie).mp (by rw [hiaeq, hieeq]; exact hXadj u hu hcu x hx)
    · exact (HoleBasics.hole_adj_iff hD hib hie).mp (by rw [hibeq, hieeq]; exact hXadj v hv hcv x hx)
    · exact (HoleBasics.hole_adj_iff hD hia hif).mp
        (by rw [hiaeq, hifeq]; exact hXadj u hu hcu x' hx')
    · exact (HoleBasics.hole_adj_iff hD hib hif).mp
        (by rw [hibeq, hifeq]; exact hXadj v hv hcv x' hx')
  -- and at least one does, since `G₂ \ X` is a path
  have hXex : ∃ x ∈ X, x ∈ D := by
    by_contra hcon
    push Not at hcon
    have hDc : ∀ z ∈ D, z ∈ c.rotate l := by
      intro z hz
      rcases hDW z hz with h | h
      · exact (hPmem z).mpr h
      · exact absurd hz (hcon z h)
    exact PathGlue.no_hole_in_path hD hP2l hDc
  obtain ⟨x, hxX, hxD⟩ := hXex
  refine ⟨x, hxX, hc, hu, hv, huv, (hXadj u hu hcu x hxX).1.1.symm, (hXadj v hv hcv x hxX).1.1.symm, ?_⟩
  -- rotate `x` to the front of `D`
  obtain ⟨E, hE, hElen, hE0, hEmem⟩ :
      ∃ E : List V, IsHoleList (bG2 G c X u v) E ∧ E.length = D.length ∧
        (∀ (h : 0 < E.length), ((E)[0]'h) = x) ∧ (∀ z, z ∈ E ↔ z ∈ D) := by
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxD
    refine ⟨D.rotate j, HoleBasics.isHoleList_rotate hD j, List.length_rotate .., ?_,
      fun z => List.mem_rotate⟩
    intro h
    have hjlt : (0 + j) % D.length < D.length := Nat.mod_lt _ (by omega)
    have hg : ((D.rotate j)[0]'h) = ((D)[(0 + j) % D.length]'hjlt) := by
      simp only [List.getElem_rotate, List.length_rotate]
    rw [hg]
    exact (getElem_congr_idx' D hjlt hj (by rw [Nat.zero_add, Nat.mod_eq_of_lt hj])).trans hjx
  have hE5 : 5 ≤ E.length := by omega
  have hEx : ((E)[0]'(by omega)) = x := hE0 (by omega)
  have hEnd : E.Nodup := hE.2.1
  -- the neighbours of `x` on `D` are exactly `E[1]` and `E[m-1]`
  have hEnbr : ∀ (z : V), z ∈ E → (bG2 G c X u v).Adj x z →
      (z = ((E)[1]'(by omega)) ∨ z = ((E)[E.length - 1]'(by omega))) := by
    intro z hz hadj
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hz
    have := (HoleMinusVertexPath.adj_head_iff hE hE5 hk).mp (by rw [hEx, hkeq]; exact hadj)
    rcases this with h | h
    · exact Or.inl (by rw [← hkeq]; exact getElem_congr_idx' E hk (by omega) h)
    · exact Or.inr (by rw [← hkeq]; exact getElem_congr_idx' E hk (by omega) h)
  have huE : u ∈ E := (hEmem u).mpr huD
  have hvE : v ∈ E := (hEmem v).mpr hvD
  have huv' : ((E)[1]'(by omega)) ≠ ((E)[E.length - 1]'(by omega)) := by
    intro h
    have := hEnd.getElem_inj_iff.mp h
    omega
  -- `Q = D \ x` is a path of `G₂` inside `C`
  have hQ : IsPathFrom (bG2 G c X u v) E.tail ((E)[1]'(by omega))
      ((E)[E.length - 1]'(by omega)) := HoleMinusVertexPath.isPathFrom_tail hE hE5
  have hQlen : E.tail.length = E.length - 1 := by simp
  have hQsub : ∀ z ∈ E.tail, z ∈ c.rotate l := by
    intro z hz
    rw [HoleMinusVertexPath.mem_tail_iff hE hE5] at hz
    have hzD : z ∈ D := (hEmem z).mp hz.1
    rcases hDW z hzD with h | h
    · exact (hPmem z).mpr h
    · exact absurd (hXuniqD z h x hxX hzD hxD) (by rw [← hEx]; exact hz.2)
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := PathGlue.exists_pos_of_subpath hP2l hQ.1 hQsub
  have hfr : ∀ t, t < E.tail.length → f t < c.length := by
    intro t ht
    have := hf1 t ht
    omega
  -- the two ends of `Q` are `u` and `v`, at positions `n-1` and `0` of `P`
  have hQ0 : ((E.tail)[0]'(by omega)) = ((E)[1]'(by omega)) :=
    PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hQl : ((E.tail)[E.tail.length - 1]'(by omega)) = ((E)[E.length - 1]'(by omega)) :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
  have hends : ∀ (t : ℕ) (ht : t < E.tail.length), ((E.tail)[t]'ht) = u ∨
      ((E.tail)[t]'ht) = v → (f t = c.length - 1 ∨ f t = 0) := by
    intro t ht hor
    have heq := hf2 t ht (hf1 t ht)
    rcases hor with h | h
    · refine Or.inl ?_
      have hgoal : ((c.rotate l)[f t]'(hf1 t ht))
          = ((c.rotate l)[c.length - 1]'(by omega)) := by
        rw [heq, h, ← hPl]
      exact hP2l.2.1.getElem_inj_iff.mp hgoal
    · refine Or.inr ?_
      have hgoal : ((c.rotate l)[f t]'(hf1 t ht)) = ((c.rotate l)[0]'(by omega)) := by
        rw [heq, h, ← hP0]
      exact hP2l.2.1.getElem_inj_iff.mp hgoal
  have hQ0uv : ((E.tail)[0]'(by omega)) = u ∨ ((E.tail)[0]'(by omega)) = v := by
    rcases hEnbr u huE (hXadj u hu hcu x hxX).symm with h | h
    · exact Or.inl (by rw [hQ0, ← h])
    · rcases hEnbr v hvE (hXadj v hv hcv x hxX).symm with h' | h'
      · exact Or.inr (by rw [hQ0, ← h'])
      · exact absurd (h.trans h'.symm) (G.ne_of_adj huv)
  have hQluv : ((E.tail)[E.tail.length - 1]'(by omega)) = u ∨
      ((E.tail)[E.tail.length - 1]'(by omega)) = v := by
    rcases hEnbr u huE (hXadj u hu hcu x hxX).symm with h | h
    · rcases hEnbr v hvE (hXadj v hv hcv x hxX).symm with h' | h'
      · exact absurd (h.trans h'.symm) (G.ne_of_adj huv)
      · exact Or.inr (by rw [hQl, ← h'])
    · exact Or.inl (by rw [hQl, ← h])
  have hf0 : f 0 = c.length - 1 ∨ f 0 = 0 := hends 0 (by omega) hQ0uv
  have hfL : f (E.tail.length - 1) = c.length - 1 ∨ f (E.tail.length - 1) = 0 :=
    hends _ (by omega) hQluv
  have hfne : f 0 ≠ f (E.tail.length - 1) := by
    intro h
    have := hf3 0 (E.tail.length - 1) (by omega) (by omega) h
    omega
  have hlow : c.length ≤ E.tail.length := by
    obtain ⟨ha, hb⟩ := hf4 0 (E.tail.length - 1) (by omega) (by omega)
    omega
  have hhigh : E.tail.length ≤ c.length := by
    have hmaps : ∀ a ∈ Finset.range E.tail.length, f a ∈ Finset.range c.length := by
      intro a ha
      exact Finset.mem_range.mpr (hfr a (Finset.mem_range.mp ha))
    have hinj : Set.InjOn f (Finset.range E.tail.length) := by
      intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact hf3 a b ha hb hab
    have := Finset.card_le_card_of_injOn f hmaps hinj
    simpa using this
  have hcov : ∀ z ∈ c, z ∈ E.tail := by
    intro z hz
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem ((hPmem z).mpr hz)
    obtain ⟨a, ha, hae⟩ :=
      Finset.surj_on_of_inj_on_of_card_le (s := Finset.range E.tail.length)
        (t := Finset.range c.length) (fun a _ => f a)
        (fun a ha => Finset.mem_range.mpr (hfr a (Finset.mem_range.mp ha)))
        (fun a₁ a₂ ha₁ ha₂ h =>
          hf3 a₁ a₂ (Finset.mem_range.mp ha₁) (Finset.mem_range.mp ha₂) h)
        (by simp only [Finset.card_range]; omega) k (Finset.mem_range.mpr (by omega))
    have halt : a < E.tail.length := Finset.mem_range.mp ha
    have heq := hf2 a halt (hf1 a halt)
    rw [← hkeq]
    have hgg : ((c.rotate l)[k]'hk) = ((E.tail)[a]'halt) := by
      rw [← heq]
      exact getElem_congr_idx' (c.rotate l) hk (hf1 a halt) hae
    rw [hgg]
    exact List.getElem_mem halt
  -- and now the hat condition
  intro z hzc hzu hzv hadjz
  have hzE : z ∈ E.tail := hcov z hzc
  have hzD : z ∈ E := List.mem_of_mem_tail hzE
  have hb2 : (bG2 G c X u v).Adj x z := by
    rw [bG2_adj_of_mem (Or.inr hxX) (Or.inl hzc), SimpleGraph.deleteEdges_adj,
      Set.mem_singleton_iff]
    refine ⟨hadjz, ?_⟩
    intro hs
    rcases Sym2.eq_iff.mp hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hcX u hu (h1 ▸ hxX)
    · exact hcX v hv (h1 ▸ hxX)
  rcases hEnbr z hzD hb2 with h | h
  · rcases hQ0uv with h' | h'
    · exact hzu (by rw [h, ← hQ0, h'])
    · exact hzv (by rw [h, ← hQ0, h'])
  · rcases hQluv with h' | h'
    · exact hzu (by rw [h, ← hQl, h'])
    · exact hzv (by rw [h, ← hQl, h'])

end Branch3



section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem rot_head_last {α : Type*} (L : List α) {a b : ℕ} (ha : a < L.length)
    (hb : b < L.length) (h : b = (a + 1) % L.length) :
    (L.rotate b).head? = some ((L)[b]'hb) ∧ (L.rotate b).getLast? = some ((L)[a]'ha) := by
  have hlen : (L.rotate b).length = L.length := List.length_rotate ..
  have hpos : 0 < (L.rotate b).length := by omega
  constructor
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
    congr 1
    have hlt : (0 + b) % L.length < L.length := Nat.mod_lt _ (by omega)
    have hg : ((L.rotate b)[0]'hpos) = ((L)[(0 + b) % L.length]'hlt) := by
      simp only [List.getElem_rotate, List.length_rotate]
    rw [hg]
    exact getElem_congr_idx' L hlt hb (by rw [Nat.zero_add, Nat.mod_eq_of_lt hb])
  · rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show (L.rotate b).length - 1 < (L.rotate b).length by omega)]
    congr 1
    have hlt : (L.length - 1 + b) % L.length < L.length := Nat.mod_lt _ (by omega)
    have hg : ((L.rotate b)[(L.rotate b).length - 1]'(by omega))
        = ((L)[(L.length - 1 + b) % L.length]'hlt) := by
      simp only [List.getElem_rotate, List.length_rotate]
    rw [hg]
    exact getElem_congr_idx' L hlt ha (rot_last ha h)

/-- The whole argument for one orientation of the edge `uv`. -/
private theorem core {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    (hX : AnticonnectedSet G X) {c : List V} (hc : IsHoleList G c)
    (hcX : ∀ w ∈ c, w ∉ X) (hn6 : 6 ≤ c.length)
    {u v : V} (hu : u ∈ c) (hv : v ∈ c) (huv : G.Adj u v)
    (hcu : VertexComplete G u X) (hcv : VertexComplete G v X)
    (honly : ∀ w ∈ c, VertexComplete G w X → w = u ∨ w = v)
    {l : ℕ} (hhead : (c.rotate l).head? = some v) (hlast : (c.rotate l).getLast? = some u) :
    (∃ h ∈ X, IsHatForHole G c u v h) ∨
    (∃ a ∈ X, ∃ b ∈ X, IsLeapForHole G c u v a b) := by
  by_cases hB : Berge (bG2 G c X u v)
  · obtain ⟨a, ha, b, hb, hlp⟩ :=
      branch_berge hG hX hc hcX hn6 hu hv huv hcu hcv honly hhead hlast hB
    exact Or.inr ⟨a, ha, b, hb, hc, l, hhead, hlast, hlp⟩
  · have hanti : ∀ dd, IsHoleList ((bG2 G c X u v)ᶜ) dd → Even (holeLength dd) :=
      fun dd hdd => no_odd_antihole hG hc hcX hn6 hu hv huv hcu hcv dd hdd
    have hA : ¬ (∀ dd, IsHoleList (bG2 G c X u v) dd → Even (holeLength dd)) :=
      fun h => hB ⟨h, hanti⟩
    push Not at hA
    obtain ⟨D, hD, hDodd⟩ := hA
    exact Or.inl (hole_gives_hat hG hc hcX hn6 hu hv huv hcu hcv hhead hlast D hD hDodd)


/-- **2.10** (printed p. 11)

PAPER: *"Let `G` be Berge, let `X ⊆ V(G)` be anticonnected, let `C` be a hole in
`G \ X` with length `> 4`, and let `e = uv` be an edge of `C`.  Assume that `u,v`
are `X`-complete and no other vertex of `C` is `X`-complete.  Then either `X`
contains a hat for `C` at `uv`, or `X` contains a leap for `C` at `uv`."*

"`e = uv` is an edge of `C`" is `u, v ∈ V(C)` together with `G.Adj u v`; by
`IsHoleList` two vertices of the hole are adjacent exactly when they are
cyclically consecutive, so this says precisely that `uv` is an edge of `C`.  The
edge `e` is unordered, whereas `IsLeapForHole G c u v a b` cuts the cyclic list at
`e` in the direction "from `v` round to `u`"; the conclusion therefore allows
either direction, which is exactly "`X` contains a leap for `C` at `uv`". -/
theorem thm_2_10 (G : SimpleGraph V) (hG : Berge G) (X : Set V)
    (hX : AnticonnectedSet G X) (c : List V) (hc : IsHoleList G c)
    (hcX : ∀ w ∈ c, w ∉ X) (hlen : 4 < holeLength c)
    (u v : V) (hu : u ∈ c) (hv : v ∈ c) (huv : G.Adj u v)
    (hcu : VertexComplete G u X) (hcv : VertexComplete G v X)
    (honly : ∀ w ∈ c, VertexComplete G w X → w = u ∨ w = v) :
    (∃ h ∈ X, IsHatForHole G c u v h) ∨
    (∃ a ∈ X, ∃ b ∈ X, IsLeapForHole G c u v a b ∨ IsLeapForHole G c v u a b) := by
  have hceven : c.length % 2 = 0 := by
    have := hG.1 c hc
    rw [Nat.even_iff] at this
    simpa only [holeLength] using this
  have hn6 : 6 ≤ c.length := by
    simp only [holeLength] at hlen
    omega
  obtain ⟨a, ha, haeq⟩ := List.getElem_of_mem hu
  obtain ⟨b, hb, hbeq⟩ := List.getElem_of_mem hv
  have hcyc : b = (a + 1) % c.length ∨ a = (b + 1) % c.length :=
    (HoleBasics.hole_adj_iff hc ha hb).mp (by rw [haeq, hbeq]; exact huv)
  rcases hcyc with hcyc | hcyc
  · obtain ⟨e1, e2⟩ := rot_head_last c ha hb hcyc
    rw [hbeq] at e1
    rw [haeq] at e2
    rcases core hG hX hc hcX hn6 hu hv huv hcu hcv honly e1 e2 with h | ⟨p, hp, q, hq, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, q, hq, Or.inl hl⟩
  · obtain ⟨e1, e2⟩ := rot_head_last c hb ha hcyc
    rw [haeq] at e1
    rw [hbeq] at e2
    rcases core hG hX hc hcX hn6 hv hu huv.symm hcv hcu
      (fun w hw hwc => (honly w hw hwc).symm) e1 e2 with h | ⟨p, hp, q, hq, hl⟩
    · obtain ⟨hh, hhX, hhat⟩ := h
      exact Or.inl ⟨hh, hhX, hat_symm hhat⟩
    · exact Or.inr ⟨p, hp, q, hq, Or.inr hl⟩

end Main

end SPGT

end Workspace.Statements.S02
