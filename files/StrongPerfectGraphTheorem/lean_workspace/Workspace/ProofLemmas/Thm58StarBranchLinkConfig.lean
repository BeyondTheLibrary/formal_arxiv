import Workspace.ProofLemmas.Thm58StarBranchStarTracks
import Workspace.ProofLemmas.Thm58StarBranchGeometry
import Workspace.ProofLemmas.Thm58StarBranchCycleData
import Workspace.ProofLemmas.Thm58StarBranchLinkTracks
import Workspace.ProofLemmas.Thm58StarBranchLinkSector
import Workspace.ProofLemmas.Thm58StarBranchLinkEnd
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.BipartiteClosedWalkEven

/-!
# The cycle and the minimal track of 5.8 (6)

PAPER (proof of 5.8 (6), printed p. 28): *"Choose a cycle `C₁` of `H` using the branch between
`v₁` and `v₂` and not using `u`, and choose a minimal track `S` in `H \ {v₁,v₂}` between `u`
and `V(C₁)`.  Let the ends of `S` be `u` and `w` say.  Hence in `L(H)` there are three
vertex-disjoint paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to `N_w`, and there are no
edges between them except in the triangle `T` formed by their ends in `N_w`."*

The three paths of that sentence are the two arcs of `C₁` out of `w` and the track `S`; each
is then extended, along the branch between `v₁` and `v₂` or through `F`, to reach the vertex
that is to be linked.  `Thm58StarBranchStarTracks.canBeLinked_of_star_tracks` proves that such
a configuration is a link onto the triangle at `w`; what remains, and is stated here as a gap,
is the existence of the cycle, of the minimal track, and of the three extensions.

`StarTrackLink G φ v w b S E T` below names that configuration once, so both applications of
2.4 in claim (6) (the one that links the unique neighbour `r`, and the one that links `pₙ`
itself) can quote the same construction.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchLinkConfig

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT
open Thm58StarBranchBasics ThreeTracksLineGraphPrism Thm58StarBranchStarTracks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- The configuration produced by the first two sentences of 5.8 (6).

`S i` are the three tracks of `H` out of `w` (the two arcs of the cycle `C₁` and the minimal
track back to `u`), `E i` is the region by which the `i`-th path is extended past the rung of
`S i`, and `T i` is the resulting path of `G`, which starts at the edge of `H` at `w` that
lies on `S i`.  The vertex `v` is the one to be linked: it has a neighbour on each `T i`. -/
structure StarTrackLink (G : SimpleGraph V) {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (v : V) (w : Fin n) (b : Fin 3 → Fin n)
    (S : Fin 3 → List (Fin n)) (Rg E : Fin 3 → Set V) (T : Fin 3 → List V) : Prop where
  track : ∀ i, IsTrackFrom H (S i) w (b i)
  len : ∀ i, 2 ≤ (S i).length
  meet : ∀ i j : Fin 3, i ≠ j → ∀ z ∈ S i, z ∈ S j → z = w
  rungSub : ∀ i, Rg i ⊆ edgeImage φ (trackEdges (S i))
  extDisj : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ E i, x ∉ E j
  extRung : ∀ i j : Fin 3, ∀ x ∈ E i, x ∉ Rg j
  extCross : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ E i, ∀ y ∈ E j, ¬ G.Adj x y
  extRungCross : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ E i, ∀ y ∈ Rg j, ¬ G.Adj x y
  path : ∀ i, IsPathList G (T i)
  head : ∀ i, (T i).head? = some (firstRungVertex φ (S i) (track i).1 (len i))
  sub : ∀ i, ∀ x ∈ T i, x ∈ Rg i ∪ E i
  nbr : ∀ i, ∃ x ∈ T i, G.Adj v x

/-- The triangle of `L(H)` formed by the three edges of `H` at `w`. -/
noncomputable def apex {v : V} {w : Fin n} {b : Fin 3 → Fin n} {S : Fin 3 → List (Fin n)}
    {Rg E : Fin 3 → Set V} {T : Fin 3 → List V}
    (hL : StarTrackLink G φ v w b S Rg E T) (i : Fin 3) : V :=
  firstRungVertex φ (S i) (hL.track i).1 (hL.len i)

/-- A `StarTrackLink` is exactly the hypothesis of 2.4. -/
theorem canBeLinked {v : V} {w : Fin n} {b : Fin 3 → Fin n} {S : Fin 3 → List (Fin n)}
    {Rg E : Fin 3 → Set V} {T : Fin 3 → List V} (hL : StarTrackLink G φ v w b S Rg E T) :
    VertexCanBeLinkedOntoTriangle G v (apex hL 0) (apex hL 1) (apex hL 2) :=
  canBeLinked_of_star_tracks v hL.track hL.len hL.meet hL.rungSub hL.extDisj hL.extRung
    hL.extCross hL.extRungCross hL.path hL.head hL.sub hL.nbr

/-- The apex vertices are edges of `H` at `w`, so they lie in the appearance. -/
theorem apex_mem_star {v : V} {w : Fin n} {b : Fin 3 → Fin n} {S : Fin 3 → List (Fin n)}
    {Rg E : Fin 3 → Set V} {T : Fin 3 → List V} (hL : StarTrackLink G φ v w b S Rg E T)
    (i : Fin 3) : apex hL i ∈ edgeImage φ (incidentEdges H w) := by
  refine ⟨firstTrackEdge (S i) (hL.len i),
    firstTrackEdge_mem (hL.track i).1 (hL.len i), ⟨?_, ?_⟩, rfl⟩
  · exact firstTrackEdge_mem (hL.track i).1 (hL.len i)
  · exact firstTrackEdge_contains (hL.track i) (hL.len i)

/-! ### Packaging three tracks and one extension into a `StarTrackLink` -/

open TrackToRungPath in
/-- **The `StarTrackLink` built from three tracks out of `w`, one of which is walked on.**

Sector `t` is the one that leaves the appearance: its path is the rung of `S t` followed by
`Q`, whose only edge to the rung joins its first vertex `z` to the last vertex of the rung.
The other two sectors are plain rungs.  This is the packaging step of the sentence *"there are
three vertex-disjoint paths … and there are no edges between them except in the triangle `T`
formed by their ends in `N_w`"*. -/
theorem link_of_tracks (t : Fin 3) {v : V} {w : Fin n} {b : Fin 3 → Fin n}
    {S : Fin 3 → List (Fin n)}
    (hS : ∀ i, IsTrackFrom H (S i) w (b i)) (hlen : ∀ i, 2 ≤ (S i).length)
    (hmeet : ∀ i j : Fin 3, i ≠ j → ∀ z ∈ S i, z ∈ S j → z = w)
    {Q : List V} {z y : V} (hQ : IsPathFrom G Q z y)
    (hQdisj : ∀ u ∈ Q, u ∉ trackRung φ (S t) (hS t).1)
    (hQcross : ∀ u ∈ Q, ∀ yy ∈ trackRung φ (S t) (hS t).1,
        (G.Adj yy u ↔ (yy = lastRungVertex φ (S t) (hS t).1 (hlen t) ∧ u = z)))
    (hQout : ∀ u ∈ Q, ∀ j : Fin 3, j ≠ t →
        ∀ yy ∈ trackRung φ (S j) (hS j).1, u ≠ yy ∧ ¬ G.Adj u yy)
    (hnbr : ∀ j : Fin 3, j ≠ t → ∃ u ∈ trackRung φ (S j) (hS j).1, G.Adj v u)
    (hnbrt : ∃ u ∈ Q, G.Adj v u) :
    ∃ (Rg E : Fin 3 → Set V) (T : Fin 3 → List V), StarTrackLink G φ v w b S Rg E T := by
  classical
  set E : Fin 3 → Set V := Function.update (fun _ => (∅ : Set V)) t {u : V | u ∈ Q} with hE
  set T : Fin 3 → List V :=
    Function.update (fun j => trackRung φ (S j) (hS j).1) t
      (trackRung φ (S t) (hS t).1 ++ Q) with hT
  have hEt : E t = {u : V | u ∈ Q} := Function.update_self _ _ _
  have hEn : ∀ j : Fin 3, j ≠ t → E j = ∅ := fun j hj => Function.update_of_ne hj _ _
  have hTt : T t = trackRung φ (S t) (hS t).1 ++ Q := Function.update_self _ _ _
  have hTn : ∀ j : Fin 3, j ≠ t → T j = trackRung φ (S j) (hS j).1 :=
    fun j hj => Function.update_of_ne hj _ _
  refine ⟨fun j => {u : V | u ∈ trackRung φ (S j) (hS j).1}, E, T,
    hS, hlen, hmeet, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `rungSub`
    intro j u hu
    obtain ⟨e, he, heS, rfl⟩ := (mem_trackRung_iff φ (hS j).1).mp hu
    exact ⟨e, he, heS, rfl⟩
  · -- `extDisj`
    intro i j hij u hu
    by_cases hit : i = t
    · have hjt : j ≠ t := fun hh => hij (hit.trans hh.symm)
      rw [hEn j hjt]
      exact fun hh => hh
    · rw [hEn i hit] at hu
      exact absurd hu (Set.notMem_empty u)
  · -- `extRung`
    intro i j u hu
    by_cases hit : i = t
    · rw [hit, hEt] at hu
      by_cases hjt : j = t
      · rw [hjt]
        exact hQdisj u hu
      · exact fun hh => (hQout u hu j hjt _ hh).1 rfl
    · rw [hEn i hit] at hu
      exact absurd hu (Set.notMem_empty u)
  · -- `extCross`
    intro i j hij u hu u' hu'
    by_cases hit : i = t
    · have hjt : j ≠ t := fun hh => hij (hit.trans hh.symm)
      rw [hEn j hjt] at hu'
      exact absurd hu' (Set.notMem_empty u')
    · rw [hEn i hit] at hu
      exact absurd hu (Set.notMem_empty u)
  · -- `extRungCross`
    intro i j hij u hu u' hu'
    by_cases hit : i = t
    · rw [hit, hEt] at hu
      have hjt : j ≠ t := fun hh => hij (hit.trans hh.symm)
      exact (hQout u hu j hjt u' hu').2
    · rw [hEn i hit] at hu
      exact absurd hu (Set.notMem_empty u)
  · -- `path`
    intro j
    by_cases hjt : j = t
    · rw [hjt, hTt]
      refine (PathGlue.glue_path (trackRung_isPathFrom_ends φ (hS t) (hlen t)) hQ ?_ ?_).1
      · intro u hu hu'
        exact hQdisj u hu' hu
      · intro u hu u' hu'
        exact hQcross u' hu' u hu
    · rw [hTn j hjt]
      exact trackRung_isPathList φ (S j) (hS j).1 (by
        have := hlen j; simp only [trackLength]; omega)
  · -- `head`
    intro j
    by_cases hjt : j = t
    · subst hjt
      rw [hTt, List.head?_append, (trackRung_isPathFrom_ends φ (hS j) (hlen j)).2.1]
      rfl
    · rw [hTn j hjt]
      exact (trackRung_isPathFrom_ends φ (hS j) (hlen j)).2.1
  · -- `sub`
    intro j u hu
    by_cases hjt : j = t
    · subst hjt
      rw [hTt] at hu
      rw [hEt]
      rcases List.mem_append.mp hu with hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
    · rw [hTn j hjt] at hu
      exact Or.inl hu
  · -- `nbr`
    intro j
    by_cases hjt : j = t
    · subst hjt
      rw [hTt]
      obtain ⟨u, hu, hadj⟩ := hnbrt
      exact ⟨u, List.mem_append.mpr (Or.inr hu), hadj⟩
    · rw [hTn j hjt]
      exact hnbr j hjt

/-- Relabelling the three sectors of a `StarTrackLink`. -/
theorem link_reorder {v : V} {w : Fin n} {b : Fin 3 → Fin n} {S : Fin 3 → List (Fin n)}
    {Rg E : Fin 3 → Set V} {T : Fin 3 → List V} (hL : StarTrackLink G φ v w b S Rg E T)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ (b' : Fin 3 → Fin n) (S' : Fin 3 → List (Fin n)) (Rg' E' : Fin 3 → Set V)
      (T' : Fin 3 → List V) (hL' : StarTrackLink G φ v w b' S' Rg' E' T'),
      ∀ i, apex hL' i = apex hL (σ i) :=
  ⟨b ∘ σ, S ∘ σ, Rg ∘ σ, E ∘ σ, T ∘ σ,
    { track := fun i => hL.track (σ i)
      len := fun i => hL.len (σ i)
      meet := fun i j hij => hL.meet (σ i) (σ j) fun hh => hij (σ.injective hh)
      rungSub := fun i => hL.rungSub (σ i)
      extDisj := fun i j hij => hL.extDisj (σ i) (σ j) fun hh => hij (σ.injective hh)
      extRung := fun i j => hL.extRung (σ i) (σ j)
      extCross := fun i j hij => hL.extCross (σ i) (σ j) fun hh => hij (σ.injective hh)
      extRungCross := fun i j hij =>
        hL.extRungCross (σ i) (σ j) fun hh => hij (σ.injective hh)
      path := fun i => hL.path (σ i)
      head := fun i => hL.head (σ i)
      sub := fun i => hL.sub (σ i)
      nbr := fun i => hL.nbr (σ i) }, fun _ => rfl⟩

open Thm58StarBranchLinkTracks Thm58StarBranchLinkSector TrackToRungPath in
/-- **The assembly of claim (6) when the star vertex used is off the cycle.**

`er` is the edge of the branch carrying the vertex `r` that is to be linked, and `x` is the
`H`-neighbour of the star vertex `c` used to reach `p₁`.  The hypothesis on `x` is what the
paper leaves implicit: the path out of the star must not run into the cycle. -/
theorem singleton_link_core
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k i : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ z ∈ Sm, z ∈ D → z = w) (hSmq : ∀ z ∈ Sm, z ∉ q)
    (hSmchord : ∀ y ∈ Sm, H.Adj c y → Sm[1]? = some y)
    (hi : i + 1 < q.length) {er : Sym2 (Fin n)} (her : er ∈ H.edgeSet)
    (herq : er = s(q[i]'(by omega), q[i + 1]'hi)) {r : V} (hrdef : r = (φ ⟨er, her⟩ : V))
    (hpr : G.Adj p₂ r)
    (hunique : ∀ z ∈ edgeImage φ (trackEdges q), G.Adj p₂ z → z = r)
    (x : Fin n) (hx : s(c, x) ∈ H.edgeSet) (hax : G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V))
    (hxcase : x ∈ Sm ∨ (x ∉ D ∧ x ∉ q)) :
    ∃ (w' : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (hL : StarTrackLink G φ r w' b S Rg E T),
      ¬ G.Adj r (apex hL 0) ∧ ¬ G.Adj r (apex hL 1) := by
  classical
  subst hrdef
  have hqlen : 2 ≤ q.length := by omega
  have hq0 : q[0]'(by omega) = v₁ := by
    have hh := hqe.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hql : q[q.length - 1]'(by omega) = v₂ := by
    have hh := hqe.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hDpos : 0 < D.length := by omega
  have hDk : D[k]'(by omega) = w := by
    rw [List.getElem?_eq_getElem (by omega : k < D.length)] at hkw
    exact Option.some_injective _ hkw
  have hD0 : D[0]'hDpos = v₁ := by
    have hh := hD.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hDpos] at hh
    exact Option.some_injective _ hh
  have hDl : D[D.length - 1]'(by omega) = v₂ := by
    have hh := hD.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hwq : w ∉ q := by
    intro hc
    have hwD : w ∈ D := by rw [← hDk]; exact List.getElem_mem _
    rcases hDq w hwD hc with hh | hh
    · have : k = 0 := hD.1.2.1.getElem_inj_iff.mp (by rw [hDk, hh, hD0])
      omega
    · have : k = D.length - 1 := hD.1.2.1.getElem_inj_iff.mp (by rw [hDk, hh, hDl])
      omega
  obtain ⟨bb, S, hS, hlen, hb0, hb1, hb2, hmeet, hsub0, hsub1, hsub2, hv2S0, hv1S1,
    ⟨z₀, hz₀D, hf0, hf0q⟩, ⟨z₁, hz₁D, hf1, hf1q⟩, ⟨z₂, hz₂Sm, hf2⟩, hl0, hl1, hS2eq⟩ :=
    exists_extended_tracks hD hqe hk0 hklt hkw hDq hSm hSm2 hSmD hSmq
      (show i < i + 1 by omega) hi
  -- where the vertices of the first two tracks live
  have hsub0' : ∀ z ∈ S 0, z ∈ D ∨ z ∈ q := fun z hz =>
    (hsub0 z hz).imp id (fun hh => TrackSlice.mem_of_mem_slice hh)
  have hsub1' : ∀ z ∈ S 1, z ∈ D ∨ z ∈ q := fun z hz =>
    (hsub1 z hz).imp id (fun hh => TrackSlice.mem_of_mem_slice hh)
  have hDq' : ∀ (j : Fin 3), j ≠ 2 → ∀ z ∈ S j, z ∈ D ∨ z ∈ q := by
    intro j hj
    fin_cases j
    · exact hsub0'
    · exact hsub1'
    · exact absurd rfl hj
  have hcSj : ∀ (j : Fin 3), j ≠ 2 → c ∉ S j := by
    intro j hj hc
    rcases hDq' j hj c hc with hh | hh
    · exact hcD hh
    · exact hcq hh
  -- the two branch pieces stop just before the edge `er`
  have hqi1S0 : (q[i + 1]'hi) ∉ S 0 := by
    intro hc
    rcases hsub0 _ hc with hh | hh
    · rcases hDq _ hh (List.getElem_mem _) with e | e
      · have : i + 1 = 0 := hqe.1.2.1.getElem_inj_iff.mp (by rw [e, hq0])
        omega
      · exact hv2S0 (by rw [← e]; exact hc)
    · obtain ⟨t, ht, -, hti, htv⟩ :=
        (TrackSlice.mem_slice_iff (show i < q.length by omega) (show 0 ≤ i by omega)).mp hh
      have : t = i + 1 := hqe.1.2.1.getElem_inj_iff.mp (by rw [htv])
      omega
  have hqiS1 : (q[i]'(by omega)) ∉ S 1 := by
    intro hc
    rcases hsub1 _ hc with hh | hh
    · rcases hDq _ hh (List.getElem_mem _) with e | e
      · exact hv1S1 (by rw [← e]; exact hc)
      · have : i = q.length - 1 := hqe.1.2.1.getElem_inj_iff.mp (by rw [e, hql])
        omega
    · obtain ⟨t, ht, hti, -, htv⟩ :=
        (TrackSlice.mem_slice_iff (show q.length - 1 < q.length by omega)
          (show i + 1 ≤ q.length - 1 by omega)).mp hh
      have : t = i := hqe.1.2.1.getElem_inj_iff.mp (by rw [htv])
      omega
  have hends : ∀ (j : Fin 3) (e : Sym2 (Fin n)), e ∈ trackEdges (S j) → ∀ z ∈ e, z ∈ S j := by
    intro j e he z hz
    obtain ⟨u, hu, rfl⟩ := he
    rcases Sym2.mem_iff.mp hz with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
  have herS : ∀ (j : Fin 3), j ≠ 2 → er ∉ trackEdges (S j) := by
    intro j hj hc
    fin_cases j
    · exact hqi1S0 (hends 0 er hc _ (by rw [herq]; exact Sym2.mem_mk_right _ _))
    · exact hqiS1 (hends 1 er hc _ (by rw [herq]; exact Sym2.mem_mk_left _ _))
    · exact absurd rfl hj
  -- the third track and its extension
  have hS₂ : IsTrackFrom H (S 2) w c := by rw [← hb2]; exact hS 2
  have hS₂q : ∀ z ∈ S 2, z ∉ q := fun z hz => hSmq z (hsub2 z hz)
  have hchord : ∀ y : Fin n, y ∈ S 2 → H.Adj c y → y = (S 2)[(S 2).length - 2]'(by
      have := hlen 2; omega) := by
    intro y hy hadj
    have hy' : Sm[1]? = some y := hSmchord y (hsub2 y hy) hadj
    have hy1 : Sm[1]'(by omega) = y := by
      rw [List.getElem?_eq_getElem (show 1 < Sm.length by omega)] at hy'
      exact Option.some_injective _ hy'
    have hlen2 : (S 2).length = Sm.length := by rw [hS2eq, List.length_reverse]
    have hkey : (S 2)[(S 2).length - 2]'(by have := hlen 2; omega) = Sm[1]'(by omega) := by
      rw [List.getElem_of_eq hS2eq, List.getElem_reverse]
      exact SubdivisionCounting.getElem_eq_of_index_eq Sm (by omega) _ _
    rw [hkey, hy1]
  have hA : c ∉ ({z : Fin n | z ∈ S 0 ∨ z ∈ S 1} : Set (Fin n)) := by
    rintro (hh | hh)
    · exact hcSj 0 (by decide) hh
    · exact hcSj 1 (by decide) hh
  obtain ⟨Q, zz, hQ, hQdisj, hQcross, hQmem, hQ₀sub⟩ :=
    exists_star_extension h hcq hS₂ (hlen 2) hS₂q hchord (path h) (fun u hu => hu)
      ({z : Fin n | z ∈ S 0 ∨ z ∈ S 1}) ⟨x, hx, hax, by
        intro hxS₂
        rcases hxcase with hh | hh
        · exact absurd (by rw [hS2eq]; exact List.mem_reverse.mpr hh) hxS₂
        · rintro (he | he)
          · rcases hsub0' x he with e | e
            · exact hh.1 e
            · exact hh.2 e
          · rcases hsub1' x he with e | e
            · exact hh.1 e
            · exact hh.2 e⟩
  -- the extension is anticomplete to the other two sectors
  have hQout : ∀ u ∈ Q, ∀ j : Fin 3, j ≠ 2 →
      ∀ yy ∈ trackRung φ (S j) (hS j).1, u ≠ yy ∧ ¬ G.Adj u yy := by
    intro u hu j hj yy hyy
    obtain ⟨e, he, heS, rfl⟩ := (mem_trackRung_iff φ (hS j).1).mp hyy
    have hyK : (φ ⟨e, he⟩ : V) ∈ K := (φ ⟨e, he⟩).2
    rcases hQmem u hu with hP | ⟨x', hx', hx'A, rfl⟩
    · refine ⟨fun hh => mem_P_not_mem_K h hP (hh ▸ hyK), fun hadj => ?_⟩
      rcases edges_of_disjoint h (star_disjoint_branch h hcq) u hP _ hyK hadj with hh | hh
      · have hstar : (φ ⟨e, he⟩ : V) ∈ edgeImage φ (incidentEdges H c) := by
          rw [← star_eq h c]; exact hh.2
        have hce : e ∈ incidentEdges H c := (image_mem_iff (φ := φ) he).mp hstar
        exact hcSj j hj (hends j e heS c hce.2)
      · have hun := hunique _ hh.2 (hh.1 ▸ hadj)
        have heer : e = er := congrArg Subtype.val (φ.injective (Subtype.ext hun))
        exact herS j hj (heer ▸ heS)
    · constructor
      · intro hh
        have heq : s(c, x') = e := congrArg Subtype.val (φ.injective (Subtype.ext hh))
        exact hcSj j hj (hends j e heS c (heq ▸ Sym2.mem_mk_left _ _))
      · intro hadj
        obtain ⟨-, zt, hzt1, hzt2⟩ :=
          SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hadj)
        have hztS : zt ∈ S j := hends j e heS zt hzt2
        have : zt = c ∨ zt = x' := by simpa using hzt1
        rcases this with rfl | rfl
        · exact hcSj j hj hztS
        · refine hx'A ?_
          fin_cases j
          · exact Or.inl hztS
          · exact Or.inr hztS
          · exact absurd rfl hj
  -- `r` has a neighbour on each of the first two sectors
  have hnbrmain : ∀ (j : Fin 3), j ≠ 2 → bb j ∈ er →
      ∃ u ∈ trackRung φ (S j) (hS j).1, G.Adj (φ ⟨er, her⟩ : V) u := by
    intro j hj hbj
    refine ⟨lastRungVertex φ (S j) (hS j).1 (hlen j),
      lastRungVertex_mem φ (hS j).1 (hlen j), ?_⟩
    apply φ.map_rel_iff.mpr
    refine ⟨fun hh => herS j hj ?_, bb j, hbj, lastTrackEdge_contains (hS j) (hlen j)⟩
    · have hee : er = lastTrackEdge (S j) (hlen j) := congrArg Subtype.val hh
      rw [hee]
      exact lastTrackEdge_mem_trackEdges (hlen j)
  have hnbr : ∀ j : Fin 3, j ≠ 2 →
      ∃ u ∈ trackRung φ (S j) (hS j).1, G.Adj (φ ⟨er, her⟩ : V) u := by
    intro j hj
    fin_cases j
    · exact hnbrmain 0 (by decide) (by rw [hb0, herq]; exact Sym2.mem_mk_left _ _)
    · exact hnbrmain 1 (by decide) (by rw [hb1, herq]; exact Sym2.mem_mk_right _ _)
    · exact absurd rfl hj
  have hnbrt : ∃ u ∈ Q, G.Adj (φ ⟨er, her⟩ : V) u := ⟨p₂, hQ₀sub p₂ (PathBasics.getLast_mem (path h).2.2), hpr.symm⟩
  obtain ⟨Rg, E, T, hL⟩ :=
    link_of_tracks (φ := φ) 2 hS hlen hmeet hQ hQdisj hQcross hQout hnbr hnbrt
  -- the apex of the third sector is never adjacent to `r`
  have hnot2 : ¬ G.Adj (φ ⟨er, her⟩ : V) (apex hL 2) := by
    intro hadj
    obtain ⟨-, zt, hzt1, hzt2⟩ :=
      SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hadj)
    have hzt2' : zt ∈ s(w, z₂) := by rw [← hf2]; exact hzt2
    have hztq : zt ∈ q := by
      have hzt1' : zt ∈ er := hzt1
      rw [herq] at hzt1'
      rcases Sym2.mem_iff.mp hzt1' with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
    rcases Sym2.mem_iff.mp hzt2' with hh | hh
    · exact hwq (hh ▸ hztq)
    · exact hSmq z₂ hz₂Sm (hh ▸ hztq)
  -- what adjacency to the first two apexes would mean
  have hbad : ∀ (j : Fin 3) (zj : Fin n), firstTrackEdge (S j) (hlen j) = s(w, zj) →
      G.Adj (φ ⟨er, her⟩ : V) (apex hL j) → zj ∈ q ∧ zj ∈ er := by
    intro j zj hfj hadj
    obtain ⟨-, zt, hzt1, hzt2⟩ :=
      SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hadj)
    have hzt2' : zt ∈ s(w, zj) := by rw [← hfj]; exact hzt2
    have hztq : zt ∈ q := by
      have hzt1' : zt ∈ er := hzt1
      rw [herq] at hzt1'
      rcases Sym2.mem_iff.mp hzt1' with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
    rcases Sym2.mem_iff.mp hzt2' with hh | hh
    · exact absurd (hh ▸ hztq) hwq
    · exact ⟨hh ▸ hztq, hh ▸ (hzt1 : zt ∈ er)⟩
  by_cases hc0 : G.Adj (φ ⟨er, her⟩ : V) (apex hL 0)
  · by_cases hc1 : G.Adj (φ ⟨er, her⟩ : V) (apex hL 1)
    · -- both would force a triangle in the bipartite graph `H`
      exfalso
      obtain ⟨hz₀q, hz₀er⟩ := hbad 0 z₀ hf0 hc0
      obtain ⟨hz₁q, hz₁er⟩ := hbad 1 z₁ hf1 hc1
      obtain ⟨hz₀v, hwv1⟩ := hf0q hz₀q
      obtain ⟨hz₁v, hwv2⟩ := hf1q hz₁q
      rw [hz₀v] at hz₀er
      rw [hz₁v] at hz₁er
      have hv1er : v₁ = q[i]'(by omega) ∨ v₁ = q[i + 1]'hi := by
        rw [herq] at hz₀er; simpa using hz₀er
      have hv2er : v₂ = q[i]'(by omega) ∨ v₂ = q[i + 1]'hi := by
        rw [herq] at hz₁er; simpa using hz₁er
      have hi0 : i = 0 := by
        rcases hv1er with hh | hh
        · exact (hqe.1.2.1.getElem_inj_iff.mp (hq0.trans hh)).symm
        · have : (0 : ℕ) = i + 1 := hqe.1.2.1.getElem_inj_iff.mp (hq0.trans hh)
          omega
      have hilast : i + 1 = q.length - 1 := by
        rcases hv2er with hh | hh
        · have : q.length - 1 = i := hqe.1.2.1.getElem_inj_iff.mp (hql.trans hh)
          omega
        · exact (hqe.1.2.1.getElem_inj_iff.mp (hql.trans hh)).symm
      have hq2 : q.length = 2 := by omega
      have hv1v2 : H.Adj v₁ v₂ := by
        have hadj := hqe.1.2.2 0 (by omega)
        rw [show q[0]'(by omega) = v₁ from hq0] at hadj
        rw [show q[0 + 1]'(by omega) = v₂ from by
          refine (SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _).trans hql] at hadj
        exact hadj
      obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite h.ready.2.2.1.2
      have e1 : col w ≠ col v₁ := col.valid hwv1
      have e2 : col w ≠ col v₂ := col.valid hwv2
      have e3 : col v₁ ≠ col v₂ := col.valid hv1v2
      rcases Bool.eq_false_or_eq_true (col w) with hw | hw <;>
        rcases Bool.eq_false_or_eq_true (col v₁) with ha | ha <;>
        rcases Bool.eq_false_or_eq_true (col v₂) with hb | hb <;>
        rw [hw] at e1 e2 <;> rw [ha] at e1 e3 <;> rw [hb] at e2 e3 <;>
        first
          | exact e1 rfl
          | exact e2 rfl
          | exact e3 rfl
    · -- move the offending sector to the last place
      obtain ⟨b', S', Rg', E', T', hL', hap⟩ := link_reorder hL (finRotate 3)
      refine ⟨_, b', S', Rg', E', T', hL', ?_, ?_⟩
      · rw [hap 0, show (finRotate 3) (0 : Fin 3) = 1 from by decide]
        exact hc1
      · rw [hap 1, show (finRotate 3) (1 : Fin 3) = 2 from by decide]
        exact hnot2
  · by_cases hc1 : G.Adj (φ ⟨er, her⟩ : V) (apex hL 1)
    · obtain ⟨b', S', Rg', E', T', hL', hap⟩ := link_reorder hL (Equiv.swap 1 2)
      refine ⟨_, b', S', Rg', E', T', hL', ?_, ?_⟩
      · rw [hap 0, show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide]
        exact hc0
      · rw [hap 1, show (Equiv.swap (1 : Fin 3) 2) 1 = 2 from by decide]
        exact hnot2
    · exact ⟨_, bb, S, Rg, E, T, hL, hc0, hc1⟩

/-- A path without its last vertex is a path, and it misses that last vertex. -/
theorem dropLast_isPathFrom {p : List V} {u v : V} (hp : IsPathFrom G p u v)
    (hlen : 2 ≤ p.length) :
    IsPathFrom G p.dropLast u (p[p.length - 2]'(by omega)) ∧ v ∉ p.dropLast ∧
      G.Adj (p[p.length - 2]'(by omega)) v ∧ ∀ z ∈ p.dropLast, z ∈ p := by
  have hnd : p.Nodup := hp.1.2.1
  have hne : p ≠ [] := hp.1.1
  have hlD : p.dropLast.length = p.length - 1 := List.length_dropLast
  have hv : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)
  have hu : p[0]'(by omega) = u := PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
  have hadj : G.Adj (p[p.length - 2]'(by omega)) v := by
    have hh := (hp.1.2.2 (p.length - 2) (p.length - 1) (by omega) (by omega)).mpr
      (Or.inl (by omega))
    rwa [hv] at hh
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, hadj, fun z hz => (List.dropLast_sublist p).mem hz⟩
  · intro hc
    have hz : p.dropLast.length = 0 := by rw [hc]; rfl
    omega
  · exact List.Nodup.sublist (List.dropLast_sublist p) hnd
  · intro t t' ht ht'
    simp only [List.getElem_dropLast]
    exact hp.1.2.2 t t' (by omega) (by omega)
  · rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < p.dropLast.length by omega)]
    simp only [List.getElem_dropLast]
    rw [hu]
  · rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show p.dropLast.length - 1 < p.dropLast.length by omega)]
    simp only [List.getElem_dropLast]
    exact congrArg some (SubdivisionCounting.getElem_eq_of_index_eq p (by omega) _ _)
  · intro hc
    obtain ⟨t, ht, htv⟩ := List.mem_iff_getElem.mp hc
    simp only [List.getElem_dropLast] at htv
    have hte : t = p.length - 1 := hnd.getElem_inj_iff.mp (by rw [htv, hv])
    omega

open Thm58StarBranchLinkTracks Thm58StarBranchLinkSector TrackToRungPath in
/-- **The assembly of claim (6) when `pₙ` itself is linked.**

`er` and `es` are the two edges of the branch carrying the two nonadjacent neighbours of `pₙ`,
and `x` is the `H`-neighbour of the star vertex `c` used to reach `p₁`.  The path out of the
star now stops one vertex before `pₙ`, so that `pₙ` sees the first two paths only at their far
ends, which are its two neighbours. -/
theorem separated_link_core
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k i j : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ z ∈ Sm, z ∈ D → z = w) (hSmq : ∀ z ∈ Sm, z ∉ q)
    (hSmchord : ∀ y ∈ Sm, H.Adj c y → Sm[1]? = some y)
    (hij : i + 1 < j) (hjq : j + 1 < q.length)
    {er es : Sym2 (Fin n)} (her : er ∈ H.edgeSet) (hes : es ∈ H.edgeSet)
    (herq : er = s(q[i]'(by omega), q[i + 1]'(by omega)))
    (hesq : es = s(q[j]'(by omega), q[j + 1]'hjq))
    (hpr : G.Adj p₂ (φ ⟨er, her⟩ : V)) (hps : G.Adj p₂ (φ ⟨es, hes⟩ : V))
    (x : Fin n) (hx : s(c, x) ∈ H.edgeSet) (hax : G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V))
    (hxcase : x ∈ Sm ∨ (x ∉ D ∧ x ∉ q)) :
    ∃ (w' : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (_ : StarTrackLink G φ p₂ w' b S Rg E T), w' ∉ q := by
  classical
  have hqlen : 2 ≤ q.length := by omega
  have hq0 : q[0]'(by omega) = v₁ := by
    have hh := hqe.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hql : q[q.length - 1]'(by omega) = v₂ := by
    have hh := hqe.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hDpos : 0 < D.length := by omega
  have hDk : D[k]'(by omega) = w := by
    rw [List.getElem?_eq_getElem (by omega : k < D.length)] at hkw
    exact Option.some_injective _ hkw
  have hD0 : D[0]'hDpos = v₁ := by
    have hh := hD.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hDpos] at hh
    exact Option.some_injective _ hh
  have hDl : D[D.length - 1]'(by omega) = v₂ := by
    have hh := hD.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some_injective _ hh
  have hwq : w ∉ q := by
    intro hc
    have hwD : w ∈ D := by rw [← hDk]; exact List.getElem_mem _
    rcases hDq w hwD hc with hh | hh
    · have : k = 0 := hD.1.2.1.getElem_inj_iff.mp (by rw [hDk, hh, hD0])
      omega
    · have : k = D.length - 1 := hD.1.2.1.getElem_inj_iff.mp (by rw [hDk, hh, hDl])
      omega
  obtain ⟨bb, S, hS, hlen, hb0, hb1, hb2, hmeet, hsub0, hsub1, hsub2, hv2S0, hv1S1,
    ⟨z₀, hz₀D, hf0, hf0q⟩, ⟨z₁, hz₁D, hf1, hf1q⟩, ⟨z₂, hz₂Sm, hf2⟩, hl0, hl1, hS2eq⟩ :=
    exists_extended_tracks hD hqe hk0 hklt hkw hDq hSm hSm2 hSmD hSmq
      (show i + 1 < j from hij) (show j < q.length by omega)
  have hsub0' : ∀ z ∈ S 0, z ∈ D ∨ z ∈ q := fun z hz =>
    (hsub0 z hz).imp id (fun hh => TrackSlice.mem_of_mem_slice hh)
  have hsub1' : ∀ z ∈ S 1, z ∈ D ∨ z ∈ q := fun z hz =>
    (hsub1 z hz).imp id (fun hh => TrackSlice.mem_of_mem_slice hh)
  have hDq' : ∀ (jj : Fin 3), jj ≠ 2 → ∀ z ∈ S jj, z ∈ D ∨ z ∈ q := by
    intro jj hjj
    fin_cases jj
    · exact hsub0'
    · exact hsub1'
    · exact absurd rfl hjj
  have hcSj : ∀ (jj : Fin 3), jj ≠ 2 → c ∉ S jj := by
    intro jj hjj hc
    rcases hDq' jj hjj c hc with hh | hh
    · exact hcD hh
    · exact hcq hh
  have hends : ∀ (jj : Fin 3) (e : Sym2 (Fin n)), e ∈ trackEdges (S jj) →
      ∀ z ∈ e, z ∈ S jj := by
    intro jj e he z hz
    obtain ⟨t, ht, rfl⟩ := he
    rcases Sym2.mem_iff.mp hz with hh | hh <;> rw [hh] <;> exact List.getElem_mem _
  -- the third track and its extension
  have hS₂ : IsTrackFrom H (S 2) w c := by rw [← hb2]; exact hS 2
  have hS₂q : ∀ z ∈ S 2, z ∉ q := fun z hz => hSmq z (hsub2 z hz)
  have hchord : ∀ y : Fin n, y ∈ S 2 → H.Adj c y → y = (S 2)[(S 2).length - 2]'(by
      have := hlen 2; omega) := by
    intro y hy hadj
    have hy' : Sm[1]? = some y := hSmchord y (hsub2 y hy) hadj
    have hy1 : Sm[1]'(by omega) = y := by
      rw [List.getElem?_eq_getElem (show 1 < Sm.length by omega)] at hy'
      exact Option.some_injective _ hy'
    have hlen2 : (S 2).length = Sm.length := by rw [hS2eq, List.length_reverse]
    have hkey : (S 2)[(S 2).length - 2]'(by have := hlen 2; omega) = Sm[1]'(by omega) := by
      rw [List.getElem_of_eq hS2eq, List.getElem_reverse]
      exact SubdivisionCounting.getElem_eq_of_index_eq Sm (by omega) _ _
    rw [hkey, hy1]
  have hA : c ∉ ({z : Fin n | z ∈ S 0 ∨ z ∈ S 1} : Set (Fin n)) := by
    rintro (hh | hh)
    · exact hcSj 0 (by decide) hh
    · exact hcSj 1 (by decide) hh
  -- the part of `P` that is walked on stops one vertex short of `pₙ`
  obtain ⟨hQ₀, hp₂out, hendadj, hQ₀P⟩ := dropLast_isPathFrom (path h) (two_le_length h)
  obtain ⟨Q, zz, hQ, hQdisj, hQcross, hQmem, hQ₀sub⟩ :=
    exists_star_extension_strong h hcq hS₂ (hlen 2) hS₂q hchord hQ₀ hQ₀P
      ({z : Fin n | z ∈ S 0 ∨ z ∈ S 1}) ⟨x, hx, hax, by
        intro hxS₂
        rcases hxcase with hh | hh
        · exact absurd (by rw [hS2eq]; exact List.mem_reverse.mpr hh) hxS₂
        · rintro (he | he)
          · rcases hsub0' x he with e | e
            · exact hh.1 e
            · exact hh.2 e
          · rcases hsub1' x he with e | e
            · exact hh.1 e
            · exact hh.2 e⟩
  -- the extension is anticomplete to the other two sectors
  have hQout : ∀ u ∈ Q, ∀ jj : Fin 3, jj ≠ 2 →
      ∀ yy ∈ trackRung φ (S jj) (hS jj).1, u ≠ yy ∧ ¬ G.Adj u yy := by
    intro u hu jj hjj yy hyy
    obtain ⟨e, he, heS, rfl⟩ := (mem_trackRung_iff φ (hS jj).1).mp hyy
    have hyK : (φ ⟨e, he⟩ : V) ∈ K := (φ ⟨e, he⟩).2
    rcases hQmem u hu with hP | ⟨x', hx', hx'A, rfl⟩
    · refine ⟨fun hh => mem_P_not_mem_K h (hQ₀P u hP) (hh ▸ hyK), fun hadj => ?_⟩
      rcases edges_of_disjoint h (star_disjoint_branch h hcq) u (hQ₀P u hP) _ hyK hadj
        with hh | hh
      · have hstar : (φ ⟨e, he⟩ : V) ∈ edgeImage φ (incidentEdges H c) := by
          rw [← star_eq h c]; exact hh.2
        have hce : e ∈ incidentEdges H c := (image_mem_iff (φ := φ) he).mp hstar
        exact hcSj jj hjj (hends jj e heS c hce.2)
      · exact hp₂out (hh.1 ▸ hP)
    · constructor
      · intro hh
        have heq : s(c, x') = e := congrArg Subtype.val (φ.injective (Subtype.ext hh))
        exact hcSj jj hjj (hends jj e heS c (heq ▸ Sym2.mem_mk_left _ _))
      · intro hadj
        obtain ⟨-, zt, hzt1, hzt2⟩ :=
          SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hadj)
        have hztS : zt ∈ S jj := hends jj e heS zt hzt2
        have hzt : zt = c ∨ zt = x' := by simpa using hzt1
        rcases hzt with rfl | rfl
        · exact hcSj jj hjj hztS
        · refine hx'A ?_
          fin_cases jj
          · exact Or.inl hztS
          · exact Or.inr hztS
          · exact absurd rfl hjj
  -- `pₙ` sees the far end of each of the first two sectors
  have hlast0 : lastRungVertex φ (S 0) (hS 0).1 (hlen 0) = (φ ⟨er, her⟩ : V) := by
    have he : lastTrackEdge (S 0) (hlen 0) = er := by
      rw [hl0 (by omega), herq,
        show q[i + 1 - 1]'(by omega) = q[i]'(by omega) from
          SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _]
    exact congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext he)
  have hlast1 : lastRungVertex φ (S 1) (hS 1).1 (hlen 1) = (φ ⟨es, hes⟩ : V) := by
    have he : lastTrackEdge (S 1) (hlen 1) = es := by
      rw [hl1 hjq, hesq]
      exact Sym2.eq_swap
    exact congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext he)
  have hnbr0 : ∃ u ∈ trackRung φ (S 0) (hS 0).1, G.Adj p₂ u :=
    ⟨_, lastRungVertex_mem φ (hS 0).1 (hlen 0), by rw [hlast0]; exact hpr⟩
  have hnbr1 : ∃ u ∈ trackRung φ (S 1) (hS 1).1, G.Adj p₂ u :=
    ⟨_, lastRungVertex_mem φ (hS 1).1 (hlen 1), by rw [hlast1]; exact hps⟩
  have hnbr : ∀ jj : Fin 3, jj ≠ 2 →
      ∃ u ∈ trackRung φ (S jj) (hS jj).1, G.Adj p₂ u := by
    intro jj hjj
    fin_cases jj
    · exact hnbr0
    · exact hnbr1
    · exact absurd rfl hjj
  have hnbrt : ∃ u ∈ Q, G.Adj p₂ u :=
    ⟨_, hQ₀sub _ (PathBasics.getLast_mem hQ₀.2.2), hendadj.symm⟩
  obtain ⟨Rg, E, T, hL⟩ :=
    link_of_tracks (φ := φ) 2 hS hlen hmeet hQ hQdisj hQcross hQout hnbr hnbrt
  exact ⟨_, bb, S, Rg, E, T, hL, hwq⟩

/-! ### The remaining gaps of claim (6)

The host-graph half of the first two sentences of claim (6) is proved:
`Thm58StarBranchCycleData.exists_host_data` supplies the cycle (the branch `q` together with a
return track `D` avoiding the star vertex `c`) and the minimal track from `c` to an internal
vertex `w` of `D`.  What is left is the assembly in `G`: read the three tracks out of `w` as
rungs, extend two of them along the branch and the third through the star at `c` and along `P`,
and check that the extensions are anticomplete to each other.  The two lemmas below are that
assembly step; both take the host data as hypotheses. -/

/-- GAP — PAPER, proof of 5.8 (6), printed p. 28: *"Hence in `L(H)` there are three
vertex-disjoint paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to `N_w`, and there are no
edges between them except in the triangle `T` formed by their ends in `N_w`.  If `pₙ` has a
unique neighbour (say `r`) in `R_{v₁v₂}`, then `r` can be linked onto the triangle `T`."*

This is the case the printed proof does not separate: every neighbour of `p₁` in the star at
`u = c` is an edge of `H` from `c` to a vertex of the branch, so the third path meets the first
two on the branch and the three paths above are not vertex-disjoint.  The link is then built at
`w := v₁` instead, from the branch truncated just before `r`, the one-edge track `c v₁`, and
the return track `D` continued along the branch past `r`; the triangle is listed so that its
first two vertices are the edge `c v₁` and the edge of `D` at `v₁`, neither of which meets `r`.
That construction needs `r` to be an internal edge of the branch; when `r` is the edge of the
branch at `v₁`, the whole attachment set of `F` lies in `N_{v₁}` and is local, contrary to the
hypothesis of 5.8. -/
theorem starTrackLink_singleton_star_at_branch_end
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hpr : G.Adj p₂ r)
    (hunique : ∀ x ∈ edgeImage φ (trackEdges q), G.Adj p₂ x → x = r)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hbv₁ : v₁ ∈ branchVertices H)
    (hbv₂ : v₂ ∈ branchVertices H) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hSmchord : ∀ y ∈ Sm, H.Adj c y → Sm[1]? = some y)
    (hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q) :
    ∃ (w' : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (hL : StarTrackLink G φ r w' b S Rg E T),
      ¬ G.Adj r (apex hL 0) ∧ ¬ G.Adj r (apex hL 1) :=
  (Thm58StarBranchLinkEnd.branch_end_absurd h hcq hqe hbv₁ hbv₂ hD hcD hDq hDe hk0 hklt hkw
    hSm hSm2 hSmD hSmq hbranchend hr hpr).elim

/-- GAP — PAPER, proof of 5.8 (6), printed p. 28: *"Hence in `L(H)` there are three
vertex-disjoint paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to `N_w`, and there are no
edges between them except in the triangle `T` formed by their ends in `N_w`.  If `pₙ` has a
unique neighbour (say `r`) in `R_{v₁v₂}`, then `r` can be linked onto the triangle `T`."*

The two arcs of the return track `D` out of `w` and the minimal track `S` back to `c` are the
three tracks; each is extended, along the branch towards `r` from either side, or through the
star at `c` and then along `P` to `pₙ`. -/
theorem starTrackLink_singleton_of_host
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hpr : G.Adj p₂ r)
    (hunique : ∀ x ∈ edgeImage φ (trackEdges q), G.Adj p₂ x → x = r)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hbv₁ : v₁ ∈ branchVertices H)
    (hbv₂ : v₂ ∈ branchVertices H) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hSmchord : ∀ y ∈ Sm, H.Adj c y → Sm[1]? = some y) :
    ∃ (w' : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (hL : StarTrackLink G φ r w' b S Rg E T),
      ¬ G.Adj r (apex hL 0) ∧ ¬ G.Adj r (apex hL 1) := by
  classical
  by_cases hgood : ∃ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
      G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) ∧ x ∉ q
  · obtain ⟨x, hx, hax, hxq⟩ := hgood
    obtain ⟨er, her, herq, hrdef⟩ := hr
    obtain ⟨i, hi, hereq⟩ := herq
    by_cases hxD : x ∈ D
    · -- the neighbour of `p₁` is reached by the one-edge track from `c` to `x`
      obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hxD
      have hqlen : 2 ≤ q.length := by omega
      have hDpos : 0 < D.length := by omega
      have hD0 : D[0]'hDpos = v₁ := by
        have hh := hD.2.1
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hDpos] at hh
        exact Option.some_injective _ hh
      have hDl : D[D.length - 1]'(by omega) = v₂ := by
        have hh := hD.2.2
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
        exact Option.some_injective _ hh
      have hq0 : q[0]'(by omega) = v₁ := by
        have hh := hqe.2.1
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
        exact Option.some_injective _ hh
      have hql : q[q.length - 1]'(by omega) = v₂ := by
        have hh := hqe.2.2
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
        exact Option.some_injective _ hh
      have hv₁q : v₁ ∈ q := by rw [← hq0]; exact List.getElem_mem _
      have hv₂q : v₂ ∈ q := by rw [← hql]; exact List.getElem_mem _
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hxq (by rw [← htx, hD0]; exact hv₁q)
      have htl : t ≠ D.length - 1 := by
        rintro rfl
        exact hxq (by rw [← htx, hDl]; exact hv₂q)
      have hcx : c ≠ x := fun hh => hcD (by rw [hh]; exact hxD)
      have hxadj : H.Adj c x := (SimpleGraph.mem_edgeSet H).mp hx
      have htrk : IsTrackFrom H [c, x] c x := by
        refine ⟨⟨by simp, by simp [hcx], ?_⟩, by simp, by simp⟩
        intro u hu
        have hu0 : u = 0 := by
          simp only [List.length_cons, List.length_nil] at hu
          omega
        subst hu0
        simpa using hxadj
      have hmemcx : ∀ z ∈ [c, x], z = c ∨ z = x := by
        intro z hz
        simpa using hz
      exact singleton_link_core h hcq hqe hD hcD hDq (show 0 < t by omega)
        (show t + 1 < D.length by omega)
        (by rw [List.getElem?_eq_getElem ht, htx])
        htrk (by simp)
        (fun z hz hzD => by
          rcases hmemcx z hz with rfl | rfl
          · exact absurd hzD hcD
          · rfl)
        (fun z hz => by
          rcases hmemcx z hz with rfl | rfl
          · exact hcq
          · exact hxq)
        (fun y hy hcy => by
          rcases hmemcx y hy with rfl | rfl
          · exact absurd hcy (H.irrefl)
          · rfl)
        hi her hereq hrdef hpr hunique x hx hax (Or.inl (by simp))
    · exact singleton_link_core h hcq hqe hD hcD hDq hk0 hklt hkw hSm hSm2 hSmD hSmq hSmchord
        hi her hereq hrdef hpr hunique x hx hax (Or.inr ⟨hxD, hxq⟩)
  · have hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q := by
      intro x hx hax
      by_contra hxq
      exact hgood ⟨x, hx, hax, hxq⟩
    exact starTrackLink_singleton_star_at_branch_end h hcq r hr hpr hunique hqe hbv₁ hbv₂
      hD hcD hDq hDe
      hk0 hklt hkw hSm hSm2 hSmD hSmq hSmchord hbranchend

/-- GAP — PAPER, proof of 5.8 (6), printed p. 28: *"If `pₙ` has two nonadjacent neighbours in
`R_{v₁v₂}`, then `pₙ` can be linked onto the triangle `T`, contrary to 2.4."*

This is the case the printed proof does not separate: every neighbour of `p₁` in the star at
`u = c` is an edge of `H` from `c` to a vertex of the branch, so the path *"from `N_u`"* meets
the other two on the branch and the three paths are not vertex-disjoint.  Rebuilding the link
at a branch vertex, as in `starTrackLink_singleton_star_at_branch_end`, is not available here,
because the conclusion asks for a `w` off the branch.  The escape is instead a parity count:
with `i < j` the two indices of the branch edges at the two neighbours of `pₙ`, the branch
together with `P` closes into three holes of `G` — through the two branch edges and through the
return track `D` — whose lengths force `i + j` to be odd and `j - i` to be even at the same
time, contrary to `Berge G`. -/
theorem starTrackLink_separated_star_at_branch_end
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r s : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : r ≠ s) (hnadj : ¬ G.Adj r s) (hpr : G.Adj p₂ r) (hps : G.Adj p₂ s)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hbv₁ : v₁ ∈ branchVertices H)
    (hbv₂ : v₂ ∈ branchVertices H) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hSmchord : ∀ y ∈ Sm, H.Adj c y → Sm[1]? = some y)
    (hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q) :
    ∃ (w' : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (_ : StarTrackLink G φ p₂ w' b S Rg E T), w' ∉ q :=
  (Thm58StarBranchLinkEnd.branch_end_absurd h hcq hqe hbv₁ hbv₂ hD hcD hDq hDe hk0 hklt hkw
    hSm hSm2 hSmD hSmq hbranchend hr hpr).elim

/-- GAP — PAPER, proof of 5.8 (6), printed p. 28: *"If `pₙ` has two nonadjacent neighbours in
`R_{v₁v₂}`, then `pₙ` can be linked onto the triangle `T`, contrary to 2.4."*

Same three tracks as `starTrackLink_singleton_of_host`; only the extensions change, because the
two branch directions are now attached to `pₙ` directly at its two nonadjacent neighbours `r`
and `s`. -/
theorem starTrackLink_separated_of_host
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r s : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : r ≠ s) (hnadj : ¬ G.Adj r s) (hpr : G.Adj p₂ r) (hps : G.Adj p₂ s)
    {v₁ v₂ w : Fin n} {D Sm : List (Fin n)} {k : ℕ}
    (hqe : IsTrackFrom H q v₁ v₂) (hbv₁ : v₁ ∈ branchVertices H)
    (hbv₂ : v₂ ∈ branchVertices H) (hD : IsTrackFrom H D v₁ v₂) (hcD : c ∉ D)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hDe : ∀ e ∈ trackEdges D, e ∉ trackEdges q)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hSmchord : ∀ y ∈ Sm, H.Adj c y → Sm[1]? = some y) :
    ∃ (w' : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (_ : StarTrackLink G φ p₂ w' b S Rg E T), w' ∉ q := by
  classical
  by_cases hgood : ∃ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
      G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) ∧ x ∉ q
  · obtain ⟨x, hx, hax, hxq⟩ := hgood
    obtain ⟨er, her, herq0, hrdef⟩ := hr
    obtain ⟨es, hes, hesq0, hsdef⟩ := hs
    obtain ⟨i, hi, hereq⟩ := herq0
    obtain ⟨j, hj, hesq⟩ := hesq0
    subst hrdef
    subst hsdef
    have hqlen : 2 ≤ q.length := by omega
    have hers : er ≠ es := by
      intro hh
      exact hrs (congrArg (fun t : H.edgeSet => (φ t : V)) (Subtype.ext hh))
    have hadjof : ∀ z : Fin n, z ∈ er → z ∈ es → False := by
      intro z hz1 hz2
      refine hnadj (φ.map_rel_iff.mpr (SimpleGraph.lineGraph_adj_iff_exists.mpr ?_))
      exact ⟨fun hh => hers (congrArg Subtype.val hh), z, hz1, hz2⟩
    have hne_ij : i ≠ j := by
      rintro rfl
      exact hers (hereq.trans hesq.symm)
    have hnij1 : j ≠ i + 1 := by
      rintro rfl
      exact hadjof (q[i + 1]'(by omega)) (by rw [hereq]; exact Sym2.mem_mk_right _ _)
        (by rw [hesq]; exact Sym2.mem_mk_left _ _)
    have hnji1 : i ≠ j + 1 := by
      rintro rfl
      exact hadjof (q[j + 1]'(by omega)) (by rw [hereq]; exact Sym2.mem_mk_left _ _)
        (by rw [hesq]; exact Sym2.mem_mk_right _ _)
    have hfar : i + 1 < j ∨ j + 1 < i := by omega
    -- when the neighbour of `p₁` lies on the cycle, use the one-edge track to it instead
    obtain ⟨w', Sm', k', hk0', hklt', hkw', hSm', hSm2', hSmD', hSmq', hSmchord', hxcase'⟩ :
        ∃ (w' : Fin n) (Sm' : List (Fin n)) (k' : ℕ), 0 < k' ∧ k' + 1 < D.length ∧
          D[k']? = some w' ∧ IsTrackFrom H Sm' c w' ∧ 2 ≤ Sm'.length ∧
          (∀ z ∈ Sm', z ∈ D → z = w') ∧ (∀ z ∈ Sm', z ∉ q) ∧
          (∀ y ∈ Sm', H.Adj c y → Sm'[1]? = some y) ∧ (x ∈ Sm' ∨ (x ∉ D ∧ x ∉ q)) := by
      by_cases hxD : x ∈ D
      · obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hxD
        have hDpos : 0 < D.length := by omega
        have hD0 : D[0]'hDpos = v₁ := by
          have hh := hD.2.1
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hDpos] at hh
          exact Option.some_injective _ hh
        have hDl : D[D.length - 1]'(by omega) = v₂ := by
          have hh := hD.2.2
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
          exact Option.some_injective _ hh
        have hq0 : q[0]'(by omega) = v₁ := by
          have hh := hqe.2.1
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
          exact Option.some_injective _ hh
        have hql : q[q.length - 1]'(by omega) = v₂ := by
          have hh := hqe.2.2
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
          exact Option.some_injective _ hh
        have hv₁q : v₁ ∈ q := by rw [← hq0]; exact List.getElem_mem _
        have hv₂q : v₂ ∈ q := by rw [← hql]; exact List.getElem_mem _
        have ht0 : t ≠ 0 := by
          rintro rfl
          exact hxq (by rw [← htx, hD0]; exact hv₁q)
        have htl : t ≠ D.length - 1 := by
          rintro rfl
          exact hxq (by rw [← htx, hDl]; exact hv₂q)
        have hcx : c ≠ x := fun hh => hcD (by rw [hh]; exact hxD)
        have hxadj : H.Adj c x := (SimpleGraph.mem_edgeSet H).mp hx
        have hmemcx : ∀ z ∈ [c, x], z = c ∨ z = x := by
          intro z hz
          simpa using hz
        refine ⟨x, [c, x], t, by omega, by omega,
          by rw [List.getElem?_eq_getElem ht, htx], ⟨⟨by simp, by simp [hcx], ?_⟩, by simp,
            by simp⟩, by simp, ?_, ?_, ?_, Or.inl (by simp)⟩
        · intro u hu
          have hu0 : u = 0 := by
            simp only [List.length_cons, List.length_nil] at hu
            omega
          subst hu0
          simpa using hxadj
        · intro z hz hzD
          rcases hmemcx z hz with rfl | rfl
          · exact absurd hzD hcD
          · rfl
        · intro z hz
          rcases hmemcx z hz with rfl | rfl
          · exact hcq
          · exact hxq
        · intro y hy hcy
          rcases hmemcx y hy with rfl | rfl
          · exact absurd hcy H.irrefl
          · rfl
      · exact ⟨w, Sm, k, hk0, hklt, hkw, hSm, hSm2, hSmD, hSmq, hSmchord,
          Or.inr ⟨hxD, hxq⟩⟩
    rcases hfar with hh | hh
    · exact separated_link_core h hcq hqe hD hcD hDq hk0' hklt' hkw' hSm' hSm2' hSmD' hSmq'
        hSmchord' hh hj her hes hereq hesq hpr hps x hx hax hxcase'
    · exact separated_link_core h hcq hqe hD hcD hDq hk0' hklt' hkw' hSm' hSm2' hSmD' hSmq'
        hSmchord' hh hi hes her hesq hereq hps hpr x hx hax hxcase'
  · have hbranchend : ∀ (x : Fin n) (hx : s(c, x) ∈ H.edgeSet),
        G.Adj p₁ (φ ⟨s(c, x), hx⟩ : V) → x ∈ q := by
      intro x hx hax
      by_contra hxq
      exact hgood ⟨x, hx, hax, hxq⟩
    exact starTrackLink_separated_star_at_branch_end h hcq r s hr hs hrs hnadj hpr hps hqe
      hbv₁ hbv₂ hD hcD hDq hDe hk0 hklt hkw hSm hSm2 hSmD hSmq hSmchord hbranchend

/-- GAP — PAPER, proof of 5.8 (6), printed p. 28: *"Choose a cycle `C₁` of `H` using the
branch between `v₁` and `v₂` and not using `u`, and choose a minimal track `S` in
`H \ {v₁,v₂}` between `u` and `V(C₁)`.  Let the ends of `S` be `u` and `w` say.  Hence in
`L(H)` there are three vertex-disjoint paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to
`N_w`, and there are no edges between them except in the triangle `T` formed by their ends in
`N_w`.  If `pₙ` has a unique neighbour (say `r`) in `R_{v₁v₂}`, then `r` can be linked onto the
triangle `T`."*

The two arcs of `C₁` out of `w` are extended along the branch towards `r` from either side,
and the track `S` is extended through the star at `c` and then along `P`, so that `r` — whose
neighbours are the two branch vertices next to it and `pₙ` — has a neighbour on each of the
three paths.  The last two conjuncts record that the triangle can be ordered so that its first
two vertices are nonneighbours of `r`; only the edge of the branch at a common end of the
branch and of an arc could be adjacent to a vertex of the triangle. -/
theorem exists_starTrackLink_singleton
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hpr : G.Adj p₂ r)
    (hunique : ∀ x ∈ edgeImage φ (trackEdges q), G.Adj p₂ x → x = r) :
    ∃ (w : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (hL : StarTrackLink G φ r w b S Rg E T),
      ¬ G.Adj r (apex hL 0) ∧ ¬ G.Adj r (apex hL 1) := by
  obtain ⟨v₁, v₂, w, D, Sm, k, hqe, hbv₁, hbv₂, hD, hcD, hDq, hDe, hk0, hklt, hkw,
    hSm, hSm2, hSmD, hSmq, hSmchord⟩ := Thm58StarBranchCycleData.exists_host_data h hcq
  exact starTrackLink_singleton_of_host h hcq r hr hpr hunique hqe hbv₁ hbv₂ hD hcD hDq hDe
    hk0 hklt hkw hSm hSm2 hSmD hSmq hSmchord

/-- GAP — PAPER, proof of 5.8 (6), printed p. 28: *"If `pₙ` has two nonadjacent neighbours in
`R_{v₁v₂}`, then `pₙ` can be linked onto the triangle `T`, contrary to 2.4."*

The cycle, the minimal track and the two arcs are the same as in
`exists_starTrackLink_singleton`; only the extensions change, because now the two branch
directions are attached to `pₙ` directly at its two nonadjacent neighbours `r` and `s`.
The vertex `w` is not on the branch between `v₁` and `v₂`, which is what
`starTrackLink_not_adj_apex` turns into the nonadjacency required by 2.4. -/
theorem exists_starTrackLink_separated
    (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r s : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : r ≠ s) (hnadj : ¬ G.Adj r s) (hpr : G.Adj p₂ r) (hps : G.Adj p₂ s) :
    ∃ (w : Fin n) (b : Fin 3 → Fin n) (S : Fin 3 → List (Fin n))
      (Rg E : Fin 3 → Set V) (T : Fin 3 → List V)
      (_ : StarTrackLink G φ p₂ w b S Rg E T), w ∉ q := by
  obtain ⟨v₁, v₂, w, D, Sm, k, hqe, hbv₁, hbv₂, hD, hcD, hDq, hDe, hk0, hklt, hkw,
    hSm, hSm2, hSmD, hSmq, hSmchord⟩ := Thm58StarBranchCycleData.exists_host_data h hcq
  exact starTrackLink_separated_of_host h hcq r s hr hs hrs hnadj hpr hps hqe hbv₁ hbv₂
    hD hcD hDq hDe hk0 hklt hkw hSm hSm2 hSmD hSmq hSmchord

/-- The last end of `P` sees nothing at a vertex of `H` off the branch: its attachments all
lie on the branch, and an edge of `H` at `w` is an edge of the branch only if `w` is a vertex
of the branch. -/
theorem last_not_adj_apex (h : Context G m J n H K φ N F P p₁ p₂ c q)
    {w : Fin n} {b : Fin 3 → Fin n} {S : Fin 3 → List (Fin n)}
    {Rg E : Fin 3 → Set V} {T : Fin 3 → List V} (hL : StarTrackLink G φ p₂ w b S Rg E T)
    (hw : w ∉ q) (i : Fin 3) : ¬ G.Adj p₂ (apex hL i) := by
  intro hadj
  obtain ⟨e, he, hew, hxe⟩ := apex_mem_star hL i
  have hK : apex hL i ∈ K := by rw [hxe]; exact (φ ⟨e, he⟩).2
  have hmem : apex hL i ∈ edgeImage φ (trackEdges q) := last_adj_mem h hK hadj
  rw [hxe] at hmem
  have heq : e ∈ trackEdges q := (image_mem_iff (φ := φ) he).mp hmem
  obtain ⟨j, hj, hje⟩ := heq
  apply hw
  rcases Sym2.mem_iff.mp (hje ▸ hew.2) with hh | hh <;> rw [hh] <;> exact List.getElem_mem _

end Workspace.ProofLemmas.Thm58StarBranchLinkConfig
