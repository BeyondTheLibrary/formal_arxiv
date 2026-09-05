import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm101ThetaOfPrism
import Workspace.ProofLemmas.Thm101ThetaAddBranch
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose

/-!
# When the 10.1 case-1 appearance is degenerate

Fifth and last of the modules decomposing
`Workspace.ProofLemmas.Thm101CaseOneK4AppearanceWitness`.

## What it discharges

The final disjunct of the case-1 conclusion: the appearance built in case 1 is nondegenerate
**unless** the two rungs carrying the attachments both have length one.  In the target
statement this is

  `NondegenerateAppearance K₄ H ∨ (DegenerateAppearance K₄ H ∧ pathLength (R 0) = 1 ∧`
  `pathLength (R 1) = 1)`,

and since `NondegenerateAppearance J H` is by definition `¬ DegenerateAppearance J H`, the
disjunction below (which drops the redundant `DegenerateAppearance` conjunct) gives it by
`Classical.em`.

## The computation

`DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H` unfolds, via `DegenerateK4Appearance`, to
*"there are four distinct cyclically adjacent vertices of `H` containing every branch-vertex
of `H`"*.  By `hbranch` the four branch-vertices are `ρ x, ρ y, ρ z, ρ z'`, so the four
vertices of the cycle are exactly those, and the question is which of the three `4`-cycles on
`{x, y, z, z'}` `H` can realise.

`ρ x` and `ρ y` are **non-adjacent** in `H`: an edge joining them would have to be a single
edge of some `Q i` from `x` straight to `y`, forcing `(Q i).length = 2`, whereas
`(Q 0).length, (Q 1).length ≥ 3` (they have `z`, resp. `z'`, in their interior) and
`(Q 2).length = (R 2).length + 1 ≥ 3` by `hR`; and it cannot be an edge of the new track `p`,
whose vertices are `ρ z`, `ρ z'` and brand-new ones.  So `ρ x` and `ρ y` must be **diagonal**
in the cycle, leaving exactly one possibility,

  `ρ x - ρ z - ρ y - ρ z' - ρ x`.

Its four edges force `z` to be both the second and the second-to-last vertex of `Q 0`, hence
`(Q 0).length = 3`, hence `(R 0).length = 2`, hence `pathLength (R 0) = 1`; and symmetrically
`pathLength (R 1) = 1`.

Note that the length `trackLength p = f.length` of the new branch is entirely unconstrained by
degeneracy — the degenerate `4`-cycle does not use the `z z'` branch at all.

## Which `decide` in `NinePrismLineGraph` this generalises

**None.**  `NinePrismLineGraph` serves the escape clause of 10.6, which asks only for
`IsLineGraphOfBipartite`; degeneracy of an appearance never arises there, and its `theta` has
no attached branch and hence only two branch-vertices rather than four.  A future prover
should look at `Workspace.Types.Appearances.SPGT.DegenerateK4Appearance` and at
`Workspace.ProofLemmas.Thm101ThetaBranchVerticesAreK4` (which supplies `hbranch`), not at
`NinePrismLineGraph`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.ThetaData

private theorem mem_of_mem_trackEdges {W : Type*} {q : List W} {e : Sym2 W}
    (he : e ∈ trackEdges q) {w : W} (hw : w ∈ e) : w ∈ q := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

/-- An edge of a theta graph incident with an internal vertex of one constituent track lies
on that same track. -/
private theorem theta_edge_on_internal_track {m : ℕ} {Theta : SimpleGraph (Fin m)}
    {x y : Fin m} {Q : Fin 3 → List (Fin m)}
    (hTheta : IsThetaDatum Theta x y Q) {i : Fin 3} {w v : Fin m}
    (hw : w ∈ trackInterior (Q i)) (hvw : Theta.Adj v w) :
    s(v, w) ∈ trackEdges (Q i) := by
  have he : s(v, w) ∈ Theta.edgeSet := hvw
  rw [hTheta.2.2.2.2.2.2] at he
  simp only [Set.mem_iUnion] at he
  obtain ⟨j, hj⟩ := he
  by_cases hij : i = j
  · simpa [hij] using hj
  · have hwj : w ∈ Q j :=
      mem_of_mem_trackEdges hj (Sym2.mem_mk_right v w)
    exact False.elim (hTheta.2.2.2.1 i j hij w hw hwj)

/-- The only track edge incident with its first vertex is its first edge. -/
private theorem head_edge_unique {W : Type*} {D : SimpleGraph W} {q : List W}
    (hq : IsTrackList D q) (h2 : 2 ≤ q.length) {e : Sym2 W}
    (he : e ∈ trackEdges q) (hmem : q[0]'(by omega) ∈ e) :
    e = s(q[0]'(by omega), q[1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hmem with h | h
  · have h' : (0 : ℕ) = i := hq.2.1.getElem_inj_iff.mp h
    subst h'
    rfl
  · have h' : (0 : ℕ) = i + 1 := hq.2.1.getElem_inj_iff.mp h
    omega

/-- The only track edge incident with its last vertex is its last edge. -/
private theorem last_edge_unique {W : Type*} {D : SimpleGraph W} {q : List W}
    (hq : IsTrackList D q) (h2 : 2 ≤ q.length) {e : Sym2 W}
    (he : e ∈ trackEdges q) (hmem : q[q.length - 1]'(by omega) ∈ e) :
    e = s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hmem with h | h
  · have h' : q.length - 1 = i := hq.2.1.getElem_inj_iff.mp h
    omega
  · have h' : q.length - 1 = i + 1 := hq.2.1.getElem_inj_iff.mp h
    have hi0 : i = q.length - 2 := by omega
    subst hi0
    (congr 2; omega)

/-- In a theta datum, if an internal vertex of one track is adjacent to both common ends,
that track has exactly three vertices. -/
private theorem theta_track_len_three_of_adj_ends {m : ℕ}
    {Theta : SimpleGraph (Fin m)} {x y : Fin m} {Q : Fin 3 → List (Fin m)}
    (hTheta : IsThetaDatum Theta x y Q) {i : Fin 3} {w : Fin m}
    (hw : w ∈ trackInterior (Q i)) (hxw : Theta.Adj x w) (hwy : Theta.Adj w y) :
    (Q i).length = 3 := by
  let q := Q i
  have htrack : IsTrackFrom Theta q x y := hTheta.2.1 i
  have h2 : 2 ≤ q.length := hTheta.2.2.1 i
  obtain ⟨j, hj, -⟩ :=
    (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff q w).mp hw
  have h3 : 3 ≤ q.length := by omega
  have hxedge : s(x, w) ∈ trackEdges q :=
    theta_edge_on_internal_track hTheta (w := w) (v := x) hw hxw
  have hwedge : s(w, y) ∈ trackEdges q :=
    by simpa only [Sym2.eq_swap] using
      (theta_edge_on_internal_track hTheta (w := w) (v := y) hw hwy.symm)
  have hhead : q[0]'(by omega) = x :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head htrack (by omega)
  have hfirst := head_edge_unique htrack.1 h2 hxedge (by
    rw [hhead]
    exact Sym2.mem_mk_left x w)
  have hsecond : q[1]'(by omega) = w := by
    rcases Sym2.eq_iff.mp hfirst with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · exact h2'.symm
    · exact False.elim ((hTheta.2.2.2.2.1 i w hw).1 (h2'.trans hhead))
  have hlast : q[q.length - 1]'(by omega) = y := by
    have h := htrack.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have hfinal := last_edge_unique htrack.1 h2 hwedge (by
    rw [hlast]
    exact Sym2.mem_mk_right w y)
  have hpenult : q[q.length - 2]'(by omega) = w := by
    rcases Sym2.eq_iff.mp hfinal with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · exact h1.symm
    · exact False.elim ((hTheta.2.2.2.2.1 i w hw).2 (h1.trans hlast))
  have hpos : (1 : ℕ) = q.length - 2 :=
    htrack.1.2.1.getElem_inj_iff.mp (hsecond.trans hpenult.symm)
  change q.length = 3
  omega

/-- Four distinct named vertices contained in a four-cycle exhaust it.  If the first two are
not adjacent, they are opposite on the cycle, so the other two occur between them. -/
private theorem four_cycle_cross_adjacencies {W : Type*} {D : SimpleGraph W}
    {u v r s a b c d : W}
    (hnamed : [u, v, r, s].Nodup) (hcycle : [a, b, c, d].Nodup)
    (hab : D.Adj a b) (hbc : D.Adj b c) (hcd : D.Adj c d) (hda : D.Adj d a)
    (hsub : ({u, v, r, s} : Set W) ⊆ ({a, b, c, d} : Set W))
    (hnuv : ¬ D.Adj u v) :
    D.Adj u r ∧ D.Adj r v ∧ D.Adj v s ∧ D.Adj s u := by
  have hu := hsub (show u ∈ ({u, v, r, s} : Set W) by simp)
  have hv := hsub (show v ∈ ({u, v, r, s} : Set W) by simp)
  have hr := hsub (show r ∈ ({u, v, r, s} : Set W) by simp)
  have hs := hsub (show s ∈ ({u, v, r, s} : Set W) by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv hr hs
  simp at hnamed hcycle
  rcases hu with (rfl | rfl | rfl | rfl) <;>
    rcases hv with (rfl | rfl | rfl | rfl) <;>
    rcases hr with (rfl | rfl | rfl | rfl) <;>
    rcases hs with (rfl | rfl | rfl | rfl) <;>
    simp_all [SimpleGraph.adj_comm]

/-- **The case-1 appearance is nondegenerate unless both attachment rungs have length one.**

A pure length computation on top of the three preceding modules: `hΘ` and `hext` give the
shape of `H`, `hbranch` (the first conjunct of `Thm101ThetaBranchVerticesAreK4`'s conclusion)
names its four branch-vertices, and `hR` — supplied at the call site by the prism, whose rungs
have distinct ends — rules out a length-one `x`–`y` track.

Generalises no `decide` of `NinePrismLineGraph`; see the module docstring. -/
theorem Thm101ThetaNondegenerate {V : Type*} (R : Fin 3 → List V)
    (hR : ∀ i : Fin 3, 2 ≤ (R i).length)
    (m m' : ℕ) (Θ : SimpleGraph (Fin m)) (x y : Fin m) (Q : Fin 3 → List (Fin m))
    (hΘ : IsThetaDatum Θ x y Q)
    (hQR : ∀ i : Fin 3, (Q i).length = (R i).length + 1)
    (z z' : Fin m) (hz : z ∈ trackInterior (Q 0)) (hz' : z' ∈ trackInterior (Q 1))
    (H : SimpleGraph (Fin m')) (ρ : Fin m → Fin m') (p : List (Fin m'))
    (hext : IsThetaBranchExtension Θ z z' H ρ p)
    (hbranch : branchVertices H = ({ρ x, ρ y, ρ z, ρ z'} : Set (Fin m'))) :
    NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∨
      (pathLength (R 0) = 1 ∧ pathLength (R 1) = 1) := by
  classical
  have hxney : x ≠ y := hΘ.1
  have hz_ne_x : z ≠ x := (hΘ.2.2.2.2.1 0 z hz).1
  have hz_ne_y : z ≠ y := (hΘ.2.2.2.2.1 0 z hz).2
  have hz'_ne_x : z' ≠ x := (hΘ.2.2.2.2.1 1 z' hz').1
  have hz'_ne_y : z' ≠ y := (hΘ.2.2.2.2.1 1 z' hz').2
  have hz_ne_z' : z ≠ z' := by
    intro hzz'
    apply hΘ.2.2.2.1 0 1 (by decide) z hz
    rw [hzz']
    exact Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hz'
  have hxyTheta : ¬ Θ.Adj x y := by
    intro hxy
    have he : s(x, y) ∈ Θ.edgeSet := hxy
    rw [hΘ.2.2.2.2.2.2] at he
    simp only [Set.mem_iUnion] at he
    obtain ⟨i, hi⟩ := he
    obtain ⟨k, hk, heq⟩ := hi
    have hkxy : (Q i)[k]'(by omega) = x ∨ (Q i)[k]'(by omega) = y := by
      have hm : (Q i)[k]'(by omega) ∈ s(x, y) := by
        rw [heq]
        exact Sym2.mem_mk_left _ _
      exact Sym2.mem_iff.mp hm
    have hksxy : (Q i)[k + 1]'hk = x ∨ (Q i)[k + 1]'hk = y := by
      have hm : (Q i)[k + 1]'hk ∈ s(x, y) := by
        rw [heq]
        exact Sym2.mem_mk_right _ _
      exact Sym2.mem_iff.mp hm
    have hnotk : (Q i)[k]'(by omega) ∉ trackInterior (Q i) := by
      intro hint
      rcases hkxy with hkx | hky
      · exact (hΘ.2.2.2.2.1 i _ hint).1 hkx
      · exact (hΘ.2.2.2.2.1 i _ hint).2 hky
    have hnotks : (Q i)[k + 1]'hk ∉ trackInterior (Q i) := by
      intro hint
      rcases hksxy with hkx | hky
      · exact (hΘ.2.2.2.2.1 i _ hint).1 hkx
      · exact (hΘ.2.2.2.2.1 i _ hint).2 hky
    have hlen2 : (Q i).length = 2 :=
      Workspace.ProofLemmas.SubdivisionCounting.track_edge_len_two
        (Q i) k hk hnotk hnotks
    have hlen3 : 3 ≤ (Q i).length := by
      rw [hQR i]
      have := hR i
      omega
    omega
  have old_adj_of_adj : ∀ {c d : Fin m}, c ≠ z → c ≠ z' →
      H.Adj (ρ c) (ρ d) → Θ.Adj c d := by
    intro c d hcz hcz' hcd
    have hedge : s(ρ c, ρ d) ∈ H.edgeSet := hcd
    rw [hext.2.2.2.2.2.2] at hedge
    rcases hedge with hold | hp
    · obtain ⟨e, he, hemap⟩ := hold
      have heq : e = s(c, d) := by
        apply Sym2.map.injective hext.1
        rw [hemap, Sym2.map_mk]
      change s(c, d) ∈ Θ.edgeSet
      rwa [← heq]
    · have hcp : ρ c ∈ p :=
        mem_of_mem_trackEdges hp (Sym2.mem_mk_left (ρ c) (ρ d))
      have hcnot : ρ c ∉ trackInterior p := by
        intro hcint
        exact hext.2.2.2.2.1 (ρ c) hcint ⟨c, rfl⟩
      rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
          hext.2.2.1.2.1 hext.2.2.1.2.2 hcp hcnot with hc | hc
      · exact False.elim (hcz (hext.1 hc))
      · exact False.elim (hcz' (hext.1 hc))
  have hnxy : ¬ H.Adj (ρ x) (ρ y) := by
    intro hxy
    exact hxyTheta (old_adj_of_adj hz_ne_x.symm hz'_ne_x.symm hxy)
  by_cases hdeg : DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H
  · right
    have hdk4 : DegenerateK4Appearance H := by
      rcases hdeg with h | h
      · exact h.2
      · exact False.elim (h.1 ⟨SimpleGraph.Iso.refl⟩)
    obtain ⟨a, b, c, d, hcycle, hab, hbc, hcd, hda, hcover⟩ := hdk4
    have hnamed0 : [x, y, z, z'].Nodup := by
      simp [hxney, hz_ne_x.symm, hz'_ne_x.symm, hz_ne_y.symm,
        hz'_ne_y.symm, hz_ne_z']
    have hnamed : [ρ x, ρ y, ρ z, ρ z'].Nodup := by
      simpa using hnamed0.map hext.1
    have hsub : ({ρ x, ρ y, ρ z, ρ z'} : Set (Fin m')) ⊆
        ({a, b, c, d} : Set (Fin m')) := by
      rw [← hbranch]
      exact hcover
    have hadjs := four_cycle_cross_adjacencies hnamed hcycle hab hbc hcd hda hsub hnxy
    have hxz : Θ.Adj x z :=
      old_adj_of_adj hz_ne_x.symm hz'_ne_x.symm hadjs.1
    have hzy : Θ.Adj z y :=
      (old_adj_of_adj hz_ne_y.symm hz'_ne_y.symm hadjs.2.1.symm).symm
    have hxz' : Θ.Adj x z' :=
      old_adj_of_adj hz_ne_x.symm hz'_ne_x.symm hadjs.2.2.2.symm
    have hz'y : Θ.Adj z' y :=
      (old_adj_of_adj hz_ne_y.symm hz'_ne_y.symm hadjs.2.2.1).symm
    have hQ0 : (Q 0).length = 3 :=
      theta_track_len_three_of_adj_ends hΘ hz hxz hzy
    have hQ1 : (Q 1).length = 3 :=
      theta_track_len_three_of_adj_ends hΘ hz' hxz' hz'y
    constructor
    · have hR0 : (R 0).length = 2 := by
        have := hQR 0
        omega
      simp [pathLength, hR0]
    · have hR1 : (R 1).length = 2 := by
        have := hQR 1
        omega
      simp [pathLength, hR1]
  · left
    exact hdeg

end Workspace.ProofLemmas
