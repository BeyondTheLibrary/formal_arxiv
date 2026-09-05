import Workspace.ProofLemmas.Thm58StarStarGapBranchConn
import Workspace.ProofLemmas.Thm57EndgameEdgeDeletion

/-!
# Deleting the interior of a branch together with the two ends of an edge

PAPER, proof of 5.8 (4), printed p. 27, the premise *"for every edge `uv ∈ A₁ ∪ A₂`,
`H \ {u, v}` is connected"* of 5.6, read in the graph obtained from `H` by deleting the edges
and the internal vertices of the branch between `v₁` and `v₂`.

The edges of `A₁` are edges `v₁a` of `H` off the branch, so `a` is not on the branch.  Deleting
`v₁` and `a` from `H` leaves a connected graph (`Thm57EndgameEdgeDeletion.connected_compl_edge`,
which is where cyclic 3-connectivity is used).  What is left to see is that one may further
delete the internal vertices of the branch: every internal vertex of the branch has all its
neighbours on the branch, so inside `H \ {v₁, a}` the branch interior is a path hanging on the
single vertex `v₂`.  A walk that enters such a set must leave it again at `v₂`, the vertex where
it entered, so the walk can be shortcut.  That shortcut is `rchIn_diff` below.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapOffBranchConn

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ## Deleting a set all of whose edges to the outside end at one vertex -/

/-- If every edge of `H` from `D` to `X \ D` ends at the single vertex `b`, then deleting `D`
from a connected set `X` leaves the rest connected: a walk inside `X` that enters `D` must
enter and leave it at `b`, so the part of the walk inside `D` can be cut out. -/
theorem rchIn_diff {H : SimpleGraph W} {X D : Set W} {b : W}
    (hbX : b ∈ X) (hbD : b ∉ D)
    (hexit : ∀ z ∈ D, ∀ y ∈ X, y ∉ D → H.Adj z y → y = b)
    {u v : W} (hu : u ∉ D) (hv : v ∉ D) (h : RchIn H X u v) :
    RchIn H (X \ D) u v := by
  obtain ⟨huX, hvX, hreach⟩ := h
  obtain ⟨p⟩ := hreach
  have key : ∀ (k : ℕ) (x y : ↥X) (p : (H.induce X).Walk x y), p.length ≤ k →
      (y : W) ∉ D →
      (((x : W) ∈ D → RchIn H (X \ D) b (y : W)) ∧
        ((x : W) ∉ D → RchIn H (X \ D) (x : W) (y : W))) := by
    intro k
    induction k with
    | zero =>
      intro x y p hp hy
      cases p with
      | nil =>
        exact ⟨fun hc => absurd hc hy, fun _ => RchIn.refl (X := X \ D) ⟨x.2, hy⟩⟩
      | cons _ _ => simp at hp
    | succ k ih =>
      intro x y p hp hy
      cases p with
      | nil =>
        exact ⟨fun hc => absurd hc hy, fun _ => RchIn.refl (X := X \ D) ⟨x.2, hy⟩⟩
      | cons hxz p' =>
        rename_i z
        have hlen : p'.length ≤ k := by
          simp only [SimpleGraph.Walk.length_cons] at hp; omega
        have hadj : H.Adj (x : W) (z : W) := hxz
        refine ⟨fun hxD => ?_, fun hxD => ?_⟩
        · by_cases hzD : (z : W) ∈ D
          · exact (ih z y p' hlen hy).1 hzD
          · have hzb : (z : W) = b := hexit _ hxD _ z.2 hzD hadj
            have hres := (ih z y p' hlen hy).2 hzD
            rwa [hzb] at hres
        · by_cases hzD : (z : W) ∈ D
          · have hxb : (x : W) = b := hexit _ hzD _ x.2 hxD hadj.symm
            have hres := (ih z y p' hlen hy).1 hzD
            rwa [← hxb] at hres
          · exact (RchIn.of_adj (X := X \ D) ⟨x.2, hxD⟩ ⟨z.2, hzD⟩ hadj).trans
              ((ih z y p' hlen hy).2 hzD)
  exact (key p.length ⟨u, huX⟩ ⟨v, hvX⟩ p le_rfl hv).2 hu

/-- The set version of `rchIn_diff`. -/
theorem connectedSet_diff {H : SimpleGraph W} {X D : Set W} {b : W}
    (hbX : b ∈ X) (hbD : b ∉ D)
    (hexit : ∀ z ∈ D, ∀ y ∈ X, y ∉ D → H.Adj z y → y = b)
    (hX : ConnectedSet H X) : ConnectedSet H (X \ D) := by
  intro u v
  have hu : (u : W) ∈ X \ D := u.2
  have hv : (v : W) ∈ X \ D := v.2
  obtain ⟨h1, h2, hr⟩ :=
    rchIn_diff hbX hbD hexit hu.2 hv.2 ⟨hu.1, hv.1, hX ⟨(u : W), hu.1⟩ ⟨(v : W), hv.1⟩⟩
  exact hr

/-! ## The ends of a track are not internal vertices -/

theorem head_notMem_trackInterior {q : List W} (hnd : q.Nodup) {c : W}
    (hh : q.head? = some c) : c ∉ trackInterior q := by
  intro hc
  obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff q c).mp hc
  have h0 : q[0]'(by omega) = c := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have : (j + 1) = 0 := hnd.getElem_inj_iff.mp (hjc.trans h0.symm)
  omega

theorem getLast_notMem_trackInterior {q : List W} (hnd : q.Nodup) {c : W}
    (hl : q.getLast? = some c) : c ∉ trackInterior q := by
  intro hc
  obtain ⟨j, hj, hjc⟩ := (SubdivisionCounting.mem_trackInterior_iff q c).mp hc
  have h0 : q[q.length - 1]'(by omega) = c := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl
    exact Option.some_injective _ hl
  have : (j + 1) = q.length - 1 := hnd.getElem_inj_iff.mp (hjc.trans h0.symm)
  omega

/-- The two ends of a track with at least two vertices are distinct. -/
theorem ends_ne {H : SimpleGraph W} {q : List W} {c₁ c₂ : W} (hnd : q.Nodup)
    (hq2 : 2 ≤ q.length) (hfrom : IsTrackFrom H q c₁ c₂) : c₁ ≠ c₂ := by
  intro hcon
  have e1 : q[0]'(by omega) = c₁ := SubdivisionCounting.track_head hfrom (by omega)
  have e2 : q[q.length - 1]'(by omega) = c₂ := by
    have hl := hfrom.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hl
    exact Option.some_injective _ hl
  have : (0 : ℕ) = q.length - 1 := hnd.getElem_inj_iff.mp (e1.trans (hcon.trans e2.symm))
  omega

/-! ## Where the vertices and the edges of the branch sit -/

/-- A vertex of the branch is either internal or one of its two ends. -/
theorem mem_iff_interior_or_end {H : SimpleGraph W} {q : List W} {c₁ c₂ x : W}
    (hfrom : IsTrackFrom H q c₁ c₂) :
    x ∈ q ↔ (x ∈ trackInterior q ∨ x = c₁ ∨ x = c₂) := by
  constructor
  · intro hx
    by_cases hint : x ∈ trackInterior q
    · exact Or.inl hint
    · exact Or.inr (SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 hx hint)
  · rintro (hx | rfl | rfl)
    · exact SubdivisionCompose.mem_of_mem_trackInterior hx
    · exact List.mem_of_head? hfrom.2.1
    · exact List.mem_of_getLast? hfrom.2.2

/-- Every edge of the branch has an internal vertex as an end, unless the branch is the single
edge joining its two ends. -/
theorem trackEdge_endpoint {H : SimpleGraph W} {q : List W} {c₁ c₂ : W}
    (hfrom : IsTrackFrom H q c₁ c₂) {e : Sym2 W} (he : e ∈ trackEdges q) :
    (∃ z ∈ trackInterior q, z ∈ e) ∨ e = s(c₁, c₂) := by
  obtain ⟨i, hi, rfl⟩ := he
  by_cases h1 : q[i]'(by omega) ∈ trackInterior q
  · exact Or.inl ⟨_, h1, Sym2.mem_mk_left _ _⟩
  by_cases h2 : q[i + 1]'hi ∈ trackInterior q
  · exact Or.inl ⟨_, h2, Sym2.mem_mk_right _ _⟩
  have hlen : q.length = 2 := SubdivisionCounting.track_edge_len_two q i hi h1 h2
  have hi0 : i = 0 := by omega
  subst hi0
  have e1 : q[0]'(by omega) = c₁ := SubdivisionCounting.track_head hfrom (by omega)
  have e2 : q[0 + 1]'hi = c₂ := SubdivisionCounting.track_last hfrom hlen
  rw [e1, e2]
  exact Or.inr rfl

/-! ## The graph with the branch interior and the ends of an edge deleted -/

/-- PAPER, proof of 5.8 (4), printed p. 27: the premise *"for every edge `uv ∈ A₁ ∪ A₂`,
`H \ {u, v}` is connected"* of 5.6, applied to the graph obtained from `H` by deleting the
edges and internal vertices of the branch between `v₁` and `v₂`.

Here `c` is one of the two ends of the branch `q`, `d` is the other end, and `a` is a
neighbour of `c` off the branch (the far end of an edge of `Aᵢ`). -/
theorem interior_edge_complement_connected {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) {q : List W} {c₁ c₂ : W}
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    {c d a : W} (hc : c = c₁ ∨ c = c₂) (hd : d = c₁ ∨ d = c₂) (hcd : c ≠ d)
    (haq : a ∉ q) (hadj : H.Adj c a) :
    ConnectedSet H ((({c, a} : Set W)ᶜ) \ {x : W | x ∈ trackInterior q}) := by
  classical
  have hnd : q.Nodup := hq.1.2.1
  have hc₁int : c₁ ∉ trackInterior q := head_notMem_trackInterior hnd hfrom.2.1
  have hc₂int : c₂ ∉ trackInterior q := getLast_notMem_trackInterior hnd hfrom.2.2
  have hcint : c ∉ trackInterior q := by rcases hc with rfl | rfl <;> assumption
  have hdint : d ∉ trackInterior q := by rcases hd with rfl | rfl <;> assumption
  have hc₁q : c₁ ∈ q := List.mem_of_head? hfrom.2.1
  have hc₂q : c₂ ∈ q := List.mem_of_getLast? hfrom.2.2
  have hdq : d ∈ q := by rcases hd with rfl | rfl <;> assumption
  have hdX : d ∈ (({c, a} : Set W)ᶜ) := by
    rintro (h' | h')
    · exact hcd h'.symm
    · exact haq (h' ▸ hdq)
  refine connectedSet_diff (b := d) hdX hdint ?_
    (Thm57EndgameEdgeDeletion.connected_compl_edge H hc3 hadj)
  intro z hz y hy hyD hzy
  -- `z` is an internal vertex of the branch, so every edge at `z` is an edge of the branch
  obtain ⟨j, hj, hjz⟩ := (SubdivisionCounting.mem_trackInterior_iff q z).mp hz
  have hsub : incidentEdges H (q[j + 1]'(by omega)) ⊆ trackEdges q :=
    Thm57Claim2Structure.incidentEdges_internal_subset hq (by omega) (by omega)
  rw [hjz] at hsub
  have hmem : s(z, y) ∈ trackEdges q := hsub ⟨hzy, Sym2.mem_mk_left _ _⟩
  have hyq : y ∈ q := (BranchClassification.mem_of_mem_trackEdges hmem).2
  have hyne : y ≠ c := fun hcon => hy (Or.inl hcon)
  have hy12 : y = c₁ ∨ y = c₂ :=
    SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 hyq hyD
  rcases hc with hc' | hc' <;> rcases hd with hd' | hd' <;> rcases hy12 with hy' | hy' <;>
    simp_all

end Workspace.ProofLemmas.Thm58StarStarGapOffBranchConn
