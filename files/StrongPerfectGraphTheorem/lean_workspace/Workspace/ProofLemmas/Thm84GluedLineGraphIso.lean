import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.StripSystemBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84GluedLineGraphIso

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The presentation of the glued subdivision that the case analysis below consumes.** -/
structure GluedData {U Wt : Type*} (J : SimpleGraph U) (Hs : SimpleGraph Wt)
    (R : U → U → List V) (ι : U → Wt) (T : U → U → List Wt) (ρ : Sym2 Wt → V) : Prop where
  /-- the branch-vertices of `J` are embedded injectively -/
  inj : Function.Injective ι
  /-- each edge of `J` carries a track of `Hs` between the images of its ends -/
  track : ∀ u v : U, J.Adj u v → IsTrackFrom Hs (T u v) (ι u) (ι v)
  /-- each such track has at least one edge -/
  len : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v)
  /-- reversing the edge reverses the track -/
  rev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse
  /-- distinct edges of `J` give tracks meeting only in their ends -/
  disj : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
    ∀ w ∈ trackInterior (T u v), w ∉ T u' v'
  /-- the interior vertices of the tracks really are new -/
  new : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι
  /-- `Hs` has no other vertices -/
  cover : ∀ w : Wt, (∃ u : U, w = ι u) ∨ ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v)
  /-- `Hs` has no other edges -/
  edges : Hs.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v)
  /-- the track along `uv` has one vertex more than the rung `R u v` -/
  length : ∀ u v : U, J.Adj u v → (T u v).length = (R u v).length + 1
  /-- the `i`-th edge of the track along `uv` is the `i`-th vertex of the rung `R u v` -/
  dict : ∀ u v : U, J.Adj u v → ∀ (i : ℕ) (hi : i + 1 < (T u v).length),
    (R u v)[i]? = some (ρ s((T u v)[i]'(by omega), (T u v)[i + 1]'hi))

/-! ## Helper lemmas -/

section Helpers

variable {U Wt : Type*} {J : SimpleGraph U} {Hs : SimpleGraph Wt}
  {R : U → U → List V} {ι : U → Wt} {T : U → U → List Wt} {ρ : Sym2 Wt → V}

/-- The dictionary, in `getElem` form. -/
theorem dictGet (hD : GluedData J Hs R ι T ρ) {u v : U} (huv : J.Adj u v)
    (i : ℕ) (hi : i + 1 < (T u v).length) (hi' : i < (R u v).length) :
    ρ s((T u v)[i]'(by omega), (T u v)[i + 1]'hi) = (R u v)[i]'hi' := by
  have h := hD.dict u v huv i hi
  rw [List.getElem?_eq_getElem hi'] at h
  exact (Option.some_injective _ h).symm

/-- The `ρ`-image of a track edge is a vertex of the corresponding rung. -/
theorem rho_mem_rung (hD : GluedData J Hs R ι T ρ) {u v : U} (huv : J.Adj u v)
    {e : Sym2 Wt} (he : e ∈ trackEdges (T u v)) : ρ e ∈ R u v := by
  obtain ⟨i, hi, rfl⟩ := he
  exact List.mem_of_getElem? (hD.dict u v huv i hi)

/-- The last vertex of a track named by `IsTrackFrom`. -/
theorem track_getLast {W : Type*} {D : SimpleGraph W} {q : List W} {a b : W}
    (h : IsTrackFrom D q a b) (hlen : 0 < q.length) : q[q.length - 1]'(by omega) = b := by
  have h' := h.2.2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
  exact Option.some_injective _ h'

/-- A vertex of a track which is not internal is one of its two ends. -/
theorem track_mem_ends {W : Type*} {D : SimpleGraph W} {q : List W} {a b : W}
    (h : IsTrackFrom D q a b) {z : W} (hz : z ∈ q) (hz' : z ∉ trackInterior q) :
    z = a ∨ z = b := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact Or.inl (SubdivisionCounting.track_head h hk)
  · rcases Nat.lt_or_ge k (q.length - 1) with hlt | hge
    · exfalso
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact hz' (SubdivisionCounting.mem_trackInterior_getElem q j (by omega))
    · refine Or.inr ?_
      have hk' : k = q.length - 1 := by omega
      exact (SubdivisionCounting.getElem_eq_of_index_eq q hk' hk (by omega)).trans
        (track_getLast h (by omega))

/-- Reversing the edge of `J` does not change the edge set of the track. -/
theorem trackEdges_swap (hD : GluedData J Hs R ι T ρ) {u v : U} (huv : J.Adj u v) :
    trackEdges (T v u) = trackEdges (T u v) := by
  rw [hD.rev u v huv]
  exact SubdivisionCounting.trackEdges_reverse _

/-- Two edges of `J` meeting at `u` and differing elsewhere are distinct as `Sym2` elements. -/
theorem sym2_ne_of_branch {u v w : U} (huv : J.Adj u v) (hvw : v ≠ w) :
    s(u, v) ≠ s(u, w) := by
  intro h
  rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
  · exact hvw h2
  · exact hvw (h2.trans h1)

/-- Two tracks at a common branch-vertex `u` meet only at `ι u`. -/
theorem tracks_meet_branch (hD : GluedData J Hs R ι T ρ) {u v w : U}
    (huv : J.Adj u v) (huw : J.Adj u w) (hvw : v ≠ w)
    {z : Wt} (hz1 : z ∈ T u v) (hz2 : z ∈ T u w) : z = ι u := by
  have hne : s(u, v) ≠ s(u, w) := sym2_ne_of_branch huv hvw
  have h1 : z ∉ trackInterior (T u v) := fun hm => hD.disj u v u w huv huw hne z hm hz2
  have h2 : z ∉ trackInterior (T u w) := fun hm => hD.disj u w u v huw huv (Ne.symm hne) z hm hz1
  rcases track_mem_ends (hD.track u v huv) hz1 h1 with h3 | h3
  · exact h3
  · exfalso
    rcases track_mem_ends (hD.track u w huw) hz2 h2 with h4 | h4
    · rw [h3] at h4; exact huv.ne' (hD.inj h4)
    · rw [h3] at h4; exact hvw (hD.inj h4)

/-- Two tracks on disjoint edges of `J` are vertex-disjoint. -/
theorem tracks_disjoint4 (hD : GluedData J Hs R ι T ρ) {u v w x : U}
    (huv : J.Adj u v) (hwx : J.Adj w x) (hnd : [u, v, w, x].Nodup)
    {z : Wt} (hz1 : z ∈ T u v) (hz2 : z ∈ T w x) : False := by
  have huw' : u ≠ w := by rintro rfl; simp at hnd
  have hux' : u ≠ x := by rintro rfl; simp at hnd
  have hvw' : v ≠ w := by rintro rfl; simp at hnd
  have hvx' : v ≠ x := by rintro rfl; simp at hnd
  have hne : s(u, v) ≠ s(w, x) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact huw' h1
    · exact hux' h1
  have h1 : z ∉ trackInterior (T u v) := fun hm => hD.disj u v w x huv hwx hne z hm hz2
  have h2 : z ∉ trackInterior (T w x) := fun hm => hD.disj w x u v hwx huv (Ne.symm hne) z hm hz1
  rcases track_mem_ends (hD.track u v huv) hz1 h1 with h3 | h3 <;>
    rcases track_mem_ends (hD.track w x hwx) hz2 h2 with h4 | h4 <;>
      rw [h3] at h4
  · exact huw' (hD.inj h4)
  · exact hux' (hD.inj h4)
  · exact hvw' (hD.inj h4)
  · exact hvx' (hD.inj h4)

/-- The first vertex of a path named by `IsPathFrom`. -/
theorem path_head {W : Type*} {D : SimpleGraph W} {q : List W} {a b : W}
    (h : IsPathFrom D q a b) (hlen : 0 < q.length) : q[0]'hlen = a := by
  have h' := h.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h'
  exact Option.some_injective _ h'

/-- The branch-vertex `ι u` lies on the `k`-th edge of `T u v` exactly when `k = 0`. -/
theorem branch_mem_edge (hD : GluedData J Hs R ι T ρ) {u v : U} (huv : J.Adj u v)
    (k : ℕ) (hk : k + 1 < (T u v).length) :
    (ι u ∈ s((T u v)[k]'(by omega), (T u v)[k + 1]'hk)) ↔ k = 0 := by
  have htr := hD.track u v huv
  have hnd : (T u v).Nodup := htr.1.2.1
  have h0 : (T u v)[0]'(by omega) = ι u := SubdivisionCounting.track_head htr (by omega)
  rw [Sym2.mem_iff]
  constructor
  · rintro (h | h)
    · have := hnd.getElem_inj_iff.mp (h0.trans h)
      omega
    · have := hnd.getElem_inj_iff.mp (h0.trans h)
      omega
  · rintro rfl
    exact Or.inl h0.symm

/-- The `k`-th vertex of a `uv`-rung lies in `N u` exactly when `k = 0`. -/
theorem rung_mem_N_iff {U' : Type*} {G : SimpleGraph V} {J' : SimpleGraph U'}
    {S : U' → U' → Set V} {N : U' → Set V} {u v : U'} {Rl : List V}
    (hRung : IsUVRung G J' S N u v Rl) (k : ℕ) (hk : k < Rl.length) :
    (Rl[k]'hk ∈ N u) ↔ k = 0 := by
  obtain ⟨sv, tv, hp, hs, -⟩ := StripSystemBasics.rung_isPath hRung
  have hnd : Rl.Nodup := hp.1.2.1
  have h0 : Rl[0]'(by omega) = sv := path_head hp (by omega)
  rw [hs _ (List.getElem_mem hk)]
  constructor
  · intro h
    have := hnd.getElem_inj_iff.mp (h.trans h0.symm)
    omega
  · rintro rfl
    exact h0

end Helpers

/-- **The edge dictionary is a bijection from the edges of `Hs` onto the union of the rungs.** -/
theorem glued_edge_dictionary_bijOn {U Wt : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (Hs : SimpleGraph Wt) (ι : U → Wt) (T : U → U → List Wt) (ρ : Sym2 Wt → V)
    (hD : GluedData J Hs R ι T ρ) :
    Set.BijOn ρ Hs.edgeSet (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    intro e he
    rw [hD.edges] at he
    simp only [Set.mem_iUnion] at he
    obtain ⟨u, v, huv, hev⟩ := he
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨u, v, huv, rho_mem_rung hD huv hev⟩
  · -- InjOn
    intro e he f hf hef
    rw [hD.edges] at he hf
    simp only [Set.mem_iUnion] at he hf
    obtain ⟨u, v, huv, hev⟩ := he
    obtain ⟨u', v', hu'v', hfv⟩ := hf
    have hSe : ρ e ∈ S u v :=
      StripSystemBasics.rung_subset_strip (hR u v huv) _ (rho_mem_rung hD huv hev)
    have hSf : ρ e ∈ S u' v' := by
      rw [hef]
      exact StripSystemBasics.rung_subset_strip (hR u' v' hu'v') _ (rho_mem_rung hD hu'v' hfv)
    have hedge : s(u, v) = s(u', v') :=
      StripSystemBasics.edge_eq_of_mem_strips hSN huv hu'v' hSe hSf
    have hfv' : f ∈ trackEdges (T u v) := by
      rcases Sym2.eq_iff.mp hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hfv
      · rw [trackEdges_swap hD huv] at hfv; exact hfv
    clear hfv hu'v'
    obtain ⟨s0, t0, hpath, -, -⟩ := StripSystemBasics.rung_isPath (hR u v huv)
    have hnd : (R u v).Nodup := hpath.1.2.1
    have hlen := hD.length u v huv
    obtain ⟨i, hi, rfl⟩ := hev
    obtain ⟨j, hj, rfl⟩ := hfv'
    have hi' : i < (R u v).length := by omega
    have hj' : j < (R u v).length := by omega
    rw [dictGet hD huv i hi hi', dictGet hD huv j hj hj'] at hef
    have hij : i = j := (hnd.getElem_inj_iff).mp hef
    subst hij
    rfl
  · -- SurjOn
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨u, v, huv, hxR⟩ := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hxR
    have hlen := hD.length u v huv
    have hi2 : i + 1 < (T u v).length := by omega
    refine ⟨s((T u v)[i]'(by omega), (T u v)[i + 1]'hi2), ?_, ?_⟩
    · rw [hD.edges]
      simp only [Set.mem_iUnion]
      exact ⟨u, v, huv, ⟨i, hi2, rfl⟩⟩
    · exact dictGet hD huv i hi2 hi

/-- **Case 1 and half of case 3: two edges of one and the same track.** -/
theorem glued_sameTrack_adj_iff {U Wt : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (Hs : SimpleGraph Wt) (ι : U → Wt) (T : U → U → List Wt) (ρ : Sym2 Wt → V)
    (hD : GluedData J Hs R ι T ρ)
    (u v : U) (huv : J.Adj u v) (e f : Hs.edgeSet)
    (he : (e : Sym2 Wt) ∈ trackEdges (T u v)) (hf : (f : Sym2 Wt) ∈ trackEdges (T u v)) :
    Hs.lineGraph.Adj e f ↔ G.Adj (ρ ↑e) (ρ ↑f) := by
  obtain ⟨i, hi, hei⟩ := he
  obtain ⟨j, hj, hfj⟩ := hf
  have hlen := hD.length u v huv
  have hi' : i < (R u v).length := by omega
  have hj' : j < (R u v).length := by omega
  have htr := hD.track u v huv
  have hTnd : (T u v).Nodup := htr.1.2.1
  obtain ⟨s0, t0, hpath, -, -⟩ := StripSystemBasics.rung_isPath (hR u v huv)
  have hre : ρ ↑e = (R u v)[i]'hi' := by rw [hei]; exact dictGet hD huv i hi hi'
  have hrf : ρ ↑f = (R u v)[j]'hj' := by rw [hfj]; exact dictGet hD huv j hj hj'
  rw [hre, hrf, hpath.1.2.2 i j hi' hj']
  constructor
  · intro hadj
    rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
    obtain ⟨hne, z, hze, hzf⟩ := hadj
    have hij : i ≠ j := by
      rintro rfl
      exact hne (Subtype.ext (hei.trans hfj.symm))
    rw [hei, Sym2.mem_iff] at hze
    rw [hfj, Sym2.mem_iff] at hzf
    rcases hze with hze | hze <;> rcases hzf with hzf | hzf <;>
      (have hidx := hTnd.getElem_inj_iff.mp (hze.symm.trans hzf); omega)
  · intro hcase
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    refine ⟨?_, ?_⟩
    · intro heq
      have hsym : (↑e : Sym2 Wt) = ↑f := by rw [heq]
      rw [hei, hfj] at hsym
      rcases Sym2.eq_iff.mp hsym with ⟨h1, -⟩ | ⟨h1, h2⟩
      · have := hTnd.getElem_inj_iff.mp h1; omega
      · have hx1 := hTnd.getElem_inj_iff.mp h1
        have hx2 := hTnd.getElem_inj_iff.mp h2
        omega
    · rcases hcase with h | h
      · refine ⟨(T u v)[i + 1]'hi, ?_, ?_⟩
        · rw [hei, Sym2.mem_iff]; exact Or.inr rfl
        · rw [hfj, Sym2.mem_iff]
          exact Or.inl (SubdivisionCounting.getElem_eq_of_index_eq _ h hi (by omega))
      · refine ⟨(T u v)[i]'(by omega), ?_, ?_⟩
        · rw [hei, Sym2.mem_iff]; exact Or.inl rfl
        · rw [hfj, Sym2.mem_iff]
          exact Or.inr (SubdivisionCounting.getElem_eq_of_index_eq _ h.symm (by omega) hj)

/-- **Case 2 and the other half of case 3: two tracks meeting at a branch-vertex.** -/
theorem glued_branchMeet_adj_iff {U Wt : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (Hs : SimpleGraph Wt) (ι : U → Wt) (T : U → U → List Wt) (ρ : Sym2 Wt → V)
    (hD : GluedData J Hs R ι T ρ)
    (u v w : U) (huv : J.Adj u v) (huw : J.Adj u w) (hvw : v ≠ w) (e f : Hs.edgeSet)
    (he : (e : Sym2 Wt) ∈ trackEdges (T u v)) (hf : (f : Sym2 Wt) ∈ trackEdges (T u w)) :
    Hs.lineGraph.Adj e f ↔ G.Adj (ρ ↑e) (ρ ↑f) := by
  have hne : s(u, v) ≠ s(u, w) := sym2_ne_of_branch huv hvw
  have hefne : e ≠ f := by
    intro h
    refine hne (SubdivisionCounting.trackEdges_disjoint hD.inj hD.track hD.len hD.disj
      u v u w huv huw (↑e) he ?_)
    rw [h]; exact hf
  obtain ⟨i, hi, hei⟩ := he
  obtain ⟨j, hj, hfj⟩ := hf
  have hlenv := hD.length u v huv
  have hlenw := hD.length u w huw
  have hi' : i < (R u v).length := by omega
  have hj' : j < (R u w).length := by omega
  have hre : ρ ↑e = (R u v)[i]'hi' := by rw [hei]; exact dictGet hD huv i hi hi'
  have hrf : ρ ↑f = (R u w)[j]'hj' := by rw [hfj]; exact dictGet hD huw j hj hj'
  have hLHS : Hs.lineGraph.Adj e f ↔ (i = 0 ∧ j = 0) := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    constructor
    · rintro ⟨-, z, hze, hzf⟩
      rw [hei] at hze
      rw [hfj] at hzf
      have hz1 : z ∈ T u v := by
        rcases Sym2.mem_iff.mp hze with rfl | rfl <;> exact List.getElem_mem _
      have hz2 : z ∈ T u w := by
        rcases Sym2.mem_iff.mp hzf with rfl | rfl <;> exact List.getElem_mem _
      have hzu : z = ι u := tracks_meet_branch hD huv huw hvw hz1 hz2
      subst hzu
      exact ⟨(branch_mem_edge hD huv i hi).mp hze, (branch_mem_edge hD huw j hj).mp hzf⟩
    · rintro ⟨rfl, rfl⟩
      refine ⟨hefne, ι u, ?_, ?_⟩
      · rw [hei]; exact (branch_mem_edge hD huv 0 hi).mpr rfl
      · rw [hfj]; exact (branch_mem_edge hD huw 0 hj).mpr rfl
  rw [hre, hrf, hLHS]
  constructor
  · rintro ⟨rfl, rfl⟩
    have h1 : (R u v)[0]'hi' ∈ N u := (rung_mem_N_iff (hR u v huv) 0 hi').mpr rfl
    have h2 : (R u w)[0]'hj' ∈ N u := (rung_mem_N_iff (hR u w huw) 0 hj').mpr rfl
    have hs1 : (R u v)[0]'hi' ∈ S u v :=
      StripSystemBasics.rung_subset_strip (hR u v huv) _ (List.getElem_mem hi')
    have hs2 : (R u w)[0]'hj' ∈ S u w :=
      StripSystemBasics.rung_subset_strip (hR u w huw) _ (List.getElem_mem hj')
    exact StripSystemBasics.Nuv_complete hSN huv huw hvw _ ⟨h1, hs1⟩ _ ⟨h2, hs2⟩
  · intro hadj
    have hs1 : (R u v)[i]'hi' ∈ S u v :=
      StripSystemBasics.rung_subset_strip (hR u v huv) _ (List.getElem_mem hi')
    have hs2 : (R u w)[j]'hj' ∈ S u w :=
      StripSystemBasics.rung_subset_strip (hR u w huw) _ (List.getElem_mem hj')
    obtain ⟨hn1, hn2⟩ := StripSystemBasics.mem_N_of_adj hSN huv huw hvw hs1 hs2 hadj
    exact ⟨(rung_mem_N_iff (hR u v huv) i hi').mp hn1,
      (rung_mem_N_iff (hR u w huw) j hj').mp hn2⟩

/-- **Case 4: two tracks on disjoint edges of `J`.** -/
theorem glued_disjointEdges_not_adj {U Wt : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (Hs : SimpleGraph Wt) (ι : U → Wt) (T : U → U → List Wt) (ρ : Sym2 Wt → V)
    (hD : GluedData J Hs R ι T ρ)
    (u v w x : U) (huv : J.Adj u v) (hwx : J.Adj w x) (hnd : [u, v, w, x].Nodup)
    (e f : Hs.edgeSet)
    (he : (e : Sym2 Wt) ∈ trackEdges (T u v)) (hf : (f : Sym2 Wt) ∈ trackEdges (T w x)) :
    ¬ Hs.lineGraph.Adj e f ∧ ¬ G.Adj (ρ ↑e) (ρ ↑f) := by
  constructor
  · intro hadj
    rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
    obtain ⟨-, z, hze, hzf⟩ := hadj
    obtain ⟨i, hi, hei⟩ := he
    obtain ⟨j, hj, hfj⟩ := hf
    rw [hei] at hze
    rw [hfj] at hzf
    have hz1 : z ∈ T u v := by
      rcases Sym2.mem_iff.mp hze with rfl | rfl <;> exact List.getElem_mem _
    have hz2 : z ∈ T w x := by
      rcases Sym2.mem_iff.mp hzf with rfl | rfl <;> exact List.getElem_mem _
    exact tracks_disjoint4 hD huv hwx hnd hz1 hz2
  · intro hadj
    have h1 : ρ ↑e ∈ S u v :=
      StripSystemBasics.rung_subset_strip (hR u v huv) _ (rho_mem_rung hD huv he)
    have h2 : ρ ↑f ∈ S w x :=
      StripSystemBasics.rung_subset_strip (hR w x hwx) _ (rho_mem_rung hD hwx hf)
    exact StripSystemBasics.strip_anticomplete hSN huv hwx hnd _ h1 _ h2 hadj

/-- **The assembly.** -/
theorem glued_lineGraph_iso {U Wt : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (Hs : SimpleGraph Wt) (ι : U → Wt) (T : U → U → List Wt) (ρ : Sym2 Wt → V)
    (hD : GluedData J Hs R ι T ρ) :
    Nonempty (Hs.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v})) := by
  classical
  have hbij := glued_edge_dictionary_bijOn G hG J hJ S N hSN R hR hRsymm Hs ι T ρ hD
  have hmem : ∀ g : Hs.edgeSet, ∃ a b : U, J.Adj a b ∧ (↑g : Sym2 Wt) ∈ trackEdges (T a b) := by
    intro g
    have hg : (↑g : Sym2 Wt) ∈ ⋃ (a : U) (b : U) (_ : J.Adj a b), trackEdges (T a b) := by
      rw [← hD.edges]; exact g.2
    simp only [Set.mem_iUnion] at hg
    obtain ⟨a, b, hab, hgab⟩ := hg
    exact ⟨a, b, hab, hgab⟩
  have main : ∀ (a b c d : U), J.Adj a b → J.Adj c d → ∀ (e f : Hs.edgeSet),
      (↑e : Sym2 Wt) ∈ trackEdges (T a b) → (↑f : Sym2 Wt) ∈ trackEdges (T c d) →
      (Hs.lineGraph.Adj e f ↔ G.Adj (ρ ↑e) (ρ ↑f)) := by
    intro a b c d hab hcd e f he hf
    by_cases hsame : s(a, b) = s(c, d)
    · have hf' : (↑f : Sym2 Wt) ∈ trackEdges (T a b) := by
        rcases Sym2.eq_iff.mp hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hf
        · rw [trackEdges_swap hD hab] at hf; exact hf
      exact glued_sameTrack_adj_iff G hG J hJ S N hSN R hR hRsymm Hs ι T ρ hD a b hab e f he hf'
    · by_cases hac : a = c
      · subst hac
        have hbd : b ≠ d := by rintro rfl; exact hsame rfl
        exact glued_branchMeet_adj_iff G hG J hJ S N hSN R hR hRsymm Hs ι T ρ hD
          a b d hab hcd hbd e f he hf
      · by_cases had : a = d
        · subst had
          rw [trackEdges_swap hD hcd.symm] at hf
          have hbc : b ≠ c := by rintro rfl; exact hsame (Sym2.eq_swap)
          exact glued_branchMeet_adj_iff G hG J hJ S N hSN R hR hRsymm Hs ι T ρ hD
            a b c hab hcd.symm hbc e f he hf
        · by_cases hbc : b = c
          · subst hbc
            rw [← trackEdges_swap hD hab] at he
            exact glued_branchMeet_adj_iff G hG J hJ S N hSN R hR hRsymm Hs ι T ρ hD
              b a d hab.symm hcd had e f he hf
          · by_cases hbd : b = d
            · subst hbd
              rw [← trackEdges_swap hD hab] at he
              rw [trackEdges_swap hD hcd.symm] at hf
              exact glued_branchMeet_adj_iff G hG J hJ S N hSN R hR hRsymm Hs ι T ρ hD
                b a c hab.symm hcd.symm hac e f he hf
            · have hnd : [a, b, c, d].Nodup := by
                simp [hab.ne, hac, had, hbc, hbd, hcd.ne]
              obtain ⟨h1, h2⟩ := glued_disjointEdges_not_adj G hG J hJ S N hSN R hR hRsymm
                Hs ι T ρ hD a b c d hab hcd hnd e f he hf
              exact iff_of_false h1 h2
  refine ⟨⟨Set.BijOn.equiv ρ hbij, ?_⟩⟩
  intro e f
  show G.Adj (ρ ↑e) (ρ ↑f) ↔ Hs.lineGraph.Adj e f
  obtain ⟨a, b, hab, he⟩ := hmem e
  obtain ⟨c, d, hcd, hf⟩ := hmem f
  exact (main a b c d hab hcd e f he hf).symm

end Workspace.ProofLemmas.Thm84GluedLineGraphIso
