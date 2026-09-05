import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.Thm101ThetaOfPrism
import Workspace.ProofLemmas.Thm101ThetaAddBranch
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.TrackSlice

/-!
# A theta graph plus one extra branch is a subdivision of `K₄`

Third of the five modules decomposing
`Workspace.ProofLemmas.Thm101CaseOneK4AppearanceWitness`.

## What it discharges

The words *"bipartite subdivision of `K₄`"* in 10.1.1 (printed p. 56) — the **subdivision**
half; bipartiteness is `Workspace.ProofLemmas.Thm101ThetaBipartite`.

The graph `H` built by `Thm101ThetaAddBranch` has exactly four vertices of degree three,
namely `ρ x`, `ρ y` (the two branch-vertices of the theta graph) and `ρ z`, `ρ z'` (the two
internal theta-vertices where the new track is attached), and its six branches are

| `K₄`-edge | branch of `H` | edges |
|---|---|---|
| `x y` | the whole track `Q 2` | `(Q 2).length - 1` |
| `x z` | the initial segment of `Q 0` up to `z` | `≥ 1` |
| `z y` | the final segment of `Q 0` from `z` | `≥ 1` |
| `x z'` | the initial segment of `Q 1` up to `z'` | `≥ 1` |
| `z' y` | the final segment of `Q 1` from `z'` | `≥ 1` |
| `z z'` | the new track `p` | `p.length - 1 ≥ 1` |

Six branches, four branch-vertices, every pair of branch-vertices joined by exactly one — that
is precisely `IsSubdivision (⊤ : SimpleGraph (Fin 4)) H`.

## How to prove it

`Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices` and
`.branchVertices_subset_range` are stated in exactly the shape the six clauses of
`IsSubdivision` deliver, so once the six tracks above are exhibited (splitting `Q 0` at `z`
and `Q 1` at `z'` with `List.take` / `List.drop`, and using
`Workspace.ProofLemmas.SubdivisionCounting.k4_three_connected` together with
`.three_le_degree_of_three_connected` to supply `hdeg`), those two lemmas give the
branch-vertex identity in both directions.

## Which `decide` in `NinePrismLineGraph` this generalises

**None** — and that is worth recording.  `NinePrismLineGraph` never mentions `IsSubdivision`
at all: the escape clause of 10.6 that it serves only needs `IsLineGraphOfBipartite`, for
which a bipartite host graph and a line-graph isomorphism suffice.  10.1.1, by contrast, asks
for a bipartite subdivision **of `K₄`**, so the subdivision structure has to be produced here
from scratch.  A future prover should not go looking in `NinePrismLineGraph` for a template.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.ThetaData

private theorem mem_of_mem_trackInterior {W : Type*} {q : List W} {w : W}
    (h : w ∈ trackInterior q) : w ∈ q :=
  Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior h

private theorem member_eq_end_or_internal {W : Type*} {D : SimpleGraph W}
    {q : List W} {a b w : W} (hq : IsTrackFrom D q a b) (hw : w ∈ q) :
    w = a ∨ w = b ∨ w ∈ trackInterior q := by
  by_cases hint : w ∈ trackInterior q
  · exact Or.inr (Or.inr hint)
  · rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      hq.2.1 hq.2.2 hw hint with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

private theorem slice_interior_subset_interior {W : Type*} {q : List W}
    {a b : ℕ} (hb : b < q.length) (hab : a ≤ b)
    {w : W} (hw : w ∈ trackInterior (Workspace.ProofLemmas.TrackSlice.slice q a b)) :
    w ∈ trackInterior q := by
  obtain ⟨k, hk, hak, hkb, rfl⟩ :=
    (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff hb hab).mp hw
  rw [Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff]
  refine ⟨k - 1, by omega, ?_⟩
  exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _

private theorem slice_interiors_disjoint {W : Type*} {q : List W} {k : ℕ}
    (hnd : q.Nodup) (hk : k < q.length) (hkLast : k < q.length - 1) {w : W}
    (hpre : w ∈ trackInterior (Workspace.ProofLemmas.TrackSlice.slice q 0 k))
    (hsuf : w ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice q k (q.length - 1))) : False := by
  obtain ⟨i, hi, -, hik, hiw⟩ :=
    (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff hk (by omega)).mp hpre
  obtain ⟨j, hj, hkj, -, hjw⟩ :=
    (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff (by omega) (by omega)).mp hsuf
  have := hnd.getElem_inj_iff.mp (hiw.trans hjw.symm)
  omega

private theorem trackEdges_slice_subset {W : Type*} (q : List W) {a b : ℕ}
    (hb : b < q.length) (hab : a ≤ b) :
    trackEdges (Workspace.ProofLemmas.TrackSlice.slice q a b) ⊆ trackEdges q := by
  rintro e ⟨i, hi, rfl⟩
  have hlen := Workspace.ProofLemmas.TrackSlice.length_slice q hb hab
  have hia : a + i + 1 < q.length := by omega
  refine ⟨a + i, hia, ?_⟩
  rw [Workspace.ProofLemmas.TrackSlice.getElem_slice q (by omega) (by omega),
    Workspace.ProofLemmas.TrackSlice.getElem_slice q hi hia]
  congr 2

private theorem trackEdges_split {W : Type*} (q : List W) {k : ℕ}
    (hk : k < q.length) (hkLast : k < q.length - 1) :
    trackEdges q =
      trackEdges (Workspace.ProofLemmas.TrackSlice.slice q 0 k) ∪
      trackEdges (Workspace.ProofLemmas.TrackSlice.slice q k (q.length - 1)) := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hik : i < k
    · left
      have hlen := Workspace.ProofLemmas.TrackSlice.length_slice q
        (i := 0) (j := k) hk (by omega)
      have hip : i + 1 < (Workspace.ProofLemmas.TrackSlice.slice q 0 k).length := by
        rw [hlen]
        omega
      refine ⟨i, hip, ?_⟩
      rw [Workspace.ProofLemmas.TrackSlice.getElem_slice q (by omega) (by omega),
        Workspace.ProofLemmas.TrackSlice.getElem_slice q hip (by omega)]
      congr 2 <;> omega
    · right
      have hlen := Workspace.ProofLemmas.TrackSlice.length_slice q
        (i := k) (j := q.length - 1) (by omega) (by omega)
      have his : i - k + 1 <
          (Workspace.ProofLemmas.TrackSlice.slice q k (q.length - 1)).length := by
        rw [hlen]
        omega
      refine ⟨i - k, his, ?_⟩
      rw [Workspace.ProofLemmas.TrackSlice.getElem_slice q (by omega) (by omega),
        Workspace.ProofLemmas.TrackSlice.getElem_slice q his (by omega)]
      congr 2 <;> omega
  · rintro (h | h)
    · exact trackEdges_slice_subset q hk (by omega) h
    · exact trackEdges_slice_subset q (by omega) (by omega) h

private theorem map_interior_disjoint {X Y : Type*} {f : X → Y}
    (hf : Function.Injective f) {q r : List X}
    (hqr : ∀ w ∈ trackInterior q, w ∉ trackInterior r) {w : Y}
    (hwq : w ∈ trackInterior (q.map f)) (hwr : w ∈ trackInterior (r.map f)) : False := by
  rw [Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hwq hwr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hwq
  obtain ⟨v, hv, huv⟩ := List.mem_map.mp hwr
  exact hqr u hu (hf huv ▸ hv)

private theorem ne_getElem_of_mem_slice_interior {W : Type*} {q : List W}
    (hnd : q.Nodup) {a b t : ℕ} (hb : b < q.length) (hab : a ≤ b)
    (ht : t < q.length) (htout : ¬ (a < t ∧ t < b)) {w : W}
    (hw : w ∈ trackInterior (Workspace.ProofLemmas.TrackSlice.slice q a b)) :
    w ≠ q[t]'ht := by
  obtain ⟨j, hj, haj, hjb, hjw⟩ :=
    (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff hb hab).mp hw
  intro hwt
  have hjt : j = t := hnd.getElem_inj_iff.mp (hjw.trans hwt)
  exact htout ⟨hjt ▸ haj, hjt ▸ hjb⟩

private theorem map_interior_disjoint_of_cross {X Y : Type*} {f : X → Y}
    (hf : Function.Injective f) {q r a b : List X}
    (hcross : ∀ w ∈ trackInterior q, w ∉ r)
    (ha : ∀ w ∈ trackInterior a, w ∈ trackInterior q)
    (hb : ∀ w ∈ trackInterior b, w ∈ r) {w : Y}
    (hwa : w ∈ trackInterior (a.map f)) (hwb : w ∈ trackInterior (b.map f)) : False := by
  rw [Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hwa hwb
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hwa
  obtain ⟨v, hv, huv⟩ := List.mem_map.mp hwb
  exact hcross u (ha u hu) (hf huv ▸ hb v hv)

private theorem map_interior_disjoint_from_new {X Y : Type*} {f : X → Y}
    {q p : List Y} (hnew : ∀ w ∈ trackInterior p, w ∉ Set.range f)
    {w : Y} (hwq : w ∈ trackInterior q) (hwp : w ∈ trackInterior p)
    (hqrange : ∀ v ∈ trackInterior q, v ∈ Set.range f) : False :=
  hnew w hwp (hqrange w hwq)

private theorem map_interior_not_range_comp {X Y I : Type*} {f : X → Y} {g : I → X}
    (hf : Function.Injective f) {q : List X}
    (hnew : ∀ w ∈ trackInterior q, w ∉ Set.range g) {w : Y}
    (hw : w ∈ trackInterior (q.map f)) : w ∉ Set.range (f ∘ g) := by
  rw [Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  rintro ⟨i, hi⟩
  exact hnew v hv ⟨i, hf hi⟩

/-- **The theta graph with an extra `z`–`z'` branch is a subdivision of `K₄`.**

Its four branch-vertices are `ρ x, ρ y, ρ z, ρ z'`, the images of the two theta
branch-vertices and of the two attachment points, and its six branches are the three theta
tracks — with `Q 0` split at `z` and `Q 1` split at `z'` — together with the new track `p`.

The hypotheses `hz`, `hz'` (the attachment points are *internal* to `Q 0` and `Q 1`, hence lie
on **distinct** branches) are what make the four branch-vertices distinct and the six branches
pairwise internally disjoint.

Generalises no `decide` of `NinePrismLineGraph`: that module never needs any
subdivision structure at all.  See the module docstring. -/
theorem Thm101ThetaBranchVerticesAreK4 {m m' : ℕ}
    (Θ : SimpleGraph (Fin m)) (x y : Fin m) (Q : Fin 3 → List (Fin m))
    (hΘ : IsThetaDatum Θ x y Q)
    (z z' : Fin m) (hz : z ∈ trackInterior (Q 0)) (hz' : z' ∈ trackInterior (Q 1))
    (H : SimpleGraph (Fin m')) (ρ : Fin m → Fin m') (p : List (Fin m'))
    (hext : IsThetaBranchExtension Θ z z' H ρ p) :
    branchVertices H = ({ρ x, ρ y, ρ z, ρ z'} : Set (Fin m')) ∧
      IsSubdivision (⊤ : SimpleGraph (Fin 4)) H := by
  classical
  obtain ⟨j0, hj0, hzpos⟩ :=
    (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff (Q 0) z).mp hz
  obtain ⟨j1, hj1, hz'pos⟩ :=
    (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff (Q 1) z').mp hz'
  let k0 : ℕ := j0 + 1
  let k1 : ℕ := j1 + 1
  have hk0 : k0 < (Q 0).length := by dsimp [k0]; omega
  have hk0Last : k0 < (Q 0).length - 1 := by dsimp [k0]; omega
  have hk1 : k1 < (Q 1).length := by dsimp [k1]; omega
  have hk1Last : k1 < (Q 1).length - 1 := by dsimp [k1]; omega
  have hzpos' : (Q 0)[k0]'hk0 = z := by simpa [k0] using hzpos
  have hz'pos' : (Q 1)[k1]'hk1 = z' := by simpa [k1] using hz'pos
  have hQ0pos : 0 < (Q 0).length := by have := hΘ.2.2.1 0; omega
  have hQ1pos : 0 < (Q 1).length := by have := hΘ.2.2.1 1; omega
  have hhead0 : (Q 0)[0]'hQ0pos = x :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head (hΘ.2.1 0) hQ0pos
  have hhead1 : (Q 1)[0]'hQ1pos = x :=
    Workspace.ProofLemmas.SubdivisionCounting.track_head (hΘ.2.1 1) hQ1pos
  have hlast0 : (Q 0)[(Q 0).length - 1]'(by omega) = y := by
    have h := (hΘ.2.1 0).2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have hlast1 : (Q 1)[(Q 1).length - 1]'(by omega) = y := by
    have h := (hΘ.2.1 1).2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have hz_ne_x : z ≠ x := (hΘ.2.2.2.2.1 0 z hz).1
  have hz_ne_y : z ≠ y := (hΘ.2.2.2.2.1 0 z hz).2
  have hz'_ne_x : z' ≠ x := (hΘ.2.2.2.2.1 1 z' hz').1
  have hz'_ne_y : z' ≠ y := (hΘ.2.2.2.2.1 1 z' hz').2
  have hz_ne_z' : z ≠ z' := by
    intro hzz'
    apply hΘ.2.2.2.1 0 1 (by decide) z hz
    rw [hzz']
    exact mem_of_mem_trackInterior hz'
  let A0 : List (Fin m') :=
    (Workspace.ProofLemmas.TrackSlice.slice (Q 0) 0 k0).map ρ
  let B0 : List (Fin m') :=
    (Workspace.ProofLemmas.TrackSlice.slice (Q 0) k0 ((Q 0).length - 1)).map ρ
  let A1 : List (Fin m') :=
    (Workspace.ProofLemmas.TrackSlice.slice (Q 1) 0 k1).map ρ
  let B1 : List (Fin m') :=
    (Workspace.ProofLemmas.TrackSlice.slice (Q 1) k1 ((Q 1).length - 1)).map ρ
  let C : List (Fin m') := (Q 2).map ρ
  let κ : Fin 4 → Fin m := ![x, y, z, z']
  let ι : Fin 4 → Fin m' := ρ ∘ κ
  let T : Fin 4 → Fin 4 → List (Fin m') :=
    ![![[], C, A0, A1],
      ![C.reverse, [], B0.reverse, B1.reverse],
      ![A0.reverse, B0, [], p],
      ![A1.reverse, B1, p.reverse, []]]
  have mapTrack : ∀ {q : List (Fin m)} {a b : Fin m},
      IsTrackFrom Θ q a b → IsTrackFrom H (q.map ρ) (ρ a) (ρ b) := by
    intro q a b hq
    exact Workspace.ProofLemmas.SubdivisionDatum.isTrackFrom_of_injHom
      ρ hext.1 hext.2.1 hq
  have hA0 : IsTrackFrom H A0 (ρ x) (ρ z) := by
    have hs := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice
      (hΘ.2.1 0).1 (i := 0) (j := k0) hk0 (by omega)
    have hm := mapTrack hs
    simpa only [A0, hhead0, hzpos'] using hm
  have hB0 : IsTrackFrom H B0 (ρ z) (ρ y) := by
    have hs := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice
      (hΘ.2.1 0).1 (i := k0) (j := (Q 0).length - 1)
        (show (Q 0).length - 1 < (Q 0).length by omega) (by omega)
    have hm := mapTrack hs
    simpa only [B0, hzpos', hlast0] using hm
  have hA1 : IsTrackFrom H A1 (ρ x) (ρ z') := by
    have hs := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice
      (hΘ.2.1 1).1 (i := 0) (j := k1) hk1 (by omega)
    have hm := mapTrack hs
    simpa only [A1, hhead1, hz'pos'] using hm
  have hB1 : IsTrackFrom H B1 (ρ z') (ρ y) := by
    have hs := Workspace.ProofLemmas.TrackSlice.isTrackFrom_slice
      (hΘ.2.1 1).1 (i := k1) (j := (Q 1).length - 1)
        (show (Q 1).length - 1 < (Q 1).length by omega) (by omega)
    have hm := mapTrack hs
    simpa only [B1, hz'pos', hlast1] using hm
  have hC : IsTrackFrom H C (ρ x) (ρ y) := by
    exact mapTrack (hΘ.2.1 2)
  have hpTrack : IsTrackFrom H p (ρ z) (ρ z') := hext.2.2.1
  have hκ : Function.Injective κ := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [κ] at hab ⊢
    all_goals first
      | exact (hΘ.1 hab).elim | exact (hΘ.1 hab.symm).elim
      | exact (hz_ne_x hab).elim | exact (hz_ne_x hab.symm).elim
      | exact (hz_ne_y hab).elim | exact (hz_ne_y hab.symm).elim
      | exact (hz'_ne_x hab).elim | exact (hz'_ne_x hab.symm).elim
      | exact (hz'_ne_y hab).elim | exact (hz'_ne_y hab.symm).elim
      | exact (hz_ne_z' hab).elim | exact (hz_ne_z' hab.symm).elim
  have hι : Function.Injective ι := hext.1.comp hκ
  have htrack : ∀ u v : Fin 4, u ≠ v → IsTrackFrom H (T u v) (ι u) (ι v) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp [T, ι, κ] at huv ⊢
    all_goals first
      | exact (huv rfl).elim
      | exact hC | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hC
      | exact hA0 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hA0
      | exact hB0 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hB0
      | exact hA1 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hA1
      | exact hB1 | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hB1
      | exact hpTrack | exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hpTrack
  have hlen : ∀ u v : Fin 4, u ≠ v → 1 ≤ trackLength (T u v) := by
    intro u v huv
    have hA0len : 2 ≤ A0.length := by
      simp only [A0, List.length_map,
        Workspace.ProofLemmas.TrackSlice.length_slice (Q 0) (i := 0) (j := k0) hk0 (by omega)]
      omega
    have hB0len : 2 ≤ B0.length := by
      simp only [B0, List.length_map,
        Workspace.ProofLemmas.TrackSlice.length_slice (Q 0) (i := k0)
          (j := (Q 0).length - 1) (by omega) (by omega)]
      omega
    have hA1len : 2 ≤ A1.length := by
      simp only [A1, List.length_map,
        Workspace.ProofLemmas.TrackSlice.length_slice (Q 1) (i := 0) (j := k1) hk1 (by omega)]
      omega
    have hB1len : 2 ≤ B1.length := by
      simp only [B1, List.length_map,
        Workspace.ProofLemmas.TrackSlice.length_slice (Q 1) (i := k1)
          (j := (Q 1).length - 1) (by omega) (by omega)]
      omega
    have hClen : 2 ≤ C.length := by simpa [C] using hΘ.2.2.1 2
    have hplen : 2 ≤ p.length := hext.2.2.2.1
    fin_cases u <;> fin_cases v <;>
      simp [T, trackLength] at huv ⊢ <;> omega
  have hrev : ∀ u v : Fin 4, u ≠ v → T v u = (T u v).reverse := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp [T]
  have notκ_of_ne : ∀ {c : Fin m}, c ≠ x → c ≠ y → c ≠ z → c ≠ z' →
      c ∉ Set.range κ := by
    intro c hcx hcy hcz hcz' hc
    obtain ⟨u, hu⟩ := hc
    fin_cases u
    · exact hcx (by simpa [κ] using hu.symm)
    · exact hcy (by simpa [κ] using hu.symm)
    · exact hcz (by simpa [κ] using hu.symm)
    · exact hcz' (by simpa [κ] using hu.symm)
  have hA0srcNew : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 0) 0 k0), c ∉ Set.range κ := by
    intro c hc
    have hcwhole : c ∈ trackInterior (Q 0) :=
      slice_interior_subset_interior hk0 (by omega) hc
    apply notκ_of_ne (hΘ.2.2.2.2.1 0 c hcwhole).1 (hΘ.2.2.2.2.1 0 c hcwhole).2
    · intro hcz
      exact (ne_getElem_of_mem_slice_interior (hΘ.2.1 0).1.2.1 hk0 (by omega)
        hk0 (by simp) hc) (hcz.trans hzpos'.symm)
    · intro hcz'
      exact hΘ.2.2.2.1 1 0 (by decide) z' hz'
        (hcz'.symm ▸ mem_of_mem_trackInterior hcwhole)
  have hB0srcNew : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 0) k0 ((Q 0).length - 1)),
      c ∉ Set.range κ := by
    intro c hc
    have hcwhole : c ∈ trackInterior (Q 0) :=
      slice_interior_subset_interior (by omega) (by omega) hc
    apply notκ_of_ne (hΘ.2.2.2.2.1 0 c hcwhole).1 (hΘ.2.2.2.2.1 0 c hcwhole).2
    · intro hcz
      exact (ne_getElem_of_mem_slice_interior (hΘ.2.1 0).1.2.1 (by omega) (by omega)
        hk0 (by simp) hc) (hcz.trans hzpos'.symm)
    · intro hcz'
      exact hΘ.2.2.2.1 1 0 (by decide) z' hz'
        (hcz'.symm ▸ mem_of_mem_trackInterior hcwhole)
  have hA1srcNew : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 1) 0 k1), c ∉ Set.range κ := by
    intro c hc
    have hcwhole : c ∈ trackInterior (Q 1) :=
      slice_interior_subset_interior hk1 (by omega) hc
    apply notκ_of_ne (hΘ.2.2.2.2.1 1 c hcwhole).1 (hΘ.2.2.2.2.1 1 c hcwhole).2
    · intro hcz
      exact hΘ.2.2.2.1 0 1 (by decide) z hz
        (hcz.symm ▸ mem_of_mem_trackInterior hcwhole)
    · intro hcz'
      exact (ne_getElem_of_mem_slice_interior (hΘ.2.1 1).1.2.1 hk1 (by omega)
        hk1 (by simp) hc) (hcz'.trans hz'pos'.symm)
  have hB1srcNew : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 1) k1 ((Q 1).length - 1)),
      c ∉ Set.range κ := by
    intro c hc
    have hcwhole : c ∈ trackInterior (Q 1) :=
      slice_interior_subset_interior (by omega) (by omega) hc
    apply notκ_of_ne (hΘ.2.2.2.2.1 1 c hcwhole).1 (hΘ.2.2.2.2.1 1 c hcwhole).2
    · intro hcz
      exact hΘ.2.2.2.1 0 1 (by decide) z hz
        (hcz.symm ▸ mem_of_mem_trackInterior hcwhole)
    · intro hcz'
      exact (ne_getElem_of_mem_slice_interior (hΘ.2.1 1).1.2.1 (by omega) (by omega)
        hk1 (by simp) hc) (hcz'.trans hz'pos'.symm)
  have hCsrcNew : ∀ c ∈ trackInterior (Q 2), c ∉ Set.range κ := by
    intro c hc
    apply notκ_of_ne (hΘ.2.2.2.2.1 2 c hc).1 (hΘ.2.2.2.2.1 2 c hc).2
    · intro hcz
      exact hΘ.2.2.2.1 0 2 (by decide) z hz
        (hcz.symm ▸ mem_of_mem_trackInterior hc)
    · intro hcz'
      exact hΘ.2.2.2.1 1 2 (by decide) z' hz'
        (hcz'.symm ▸ mem_of_mem_trackInterior hc)
  have hA0new : ∀ w ∈ trackInterior A0, w ∉ Set.range ι := by
    intro w hw
    exact map_interior_not_range_comp hext.1 hA0srcNew (by simpa [A0] using hw)
  have hB0new : ∀ w ∈ trackInterior B0, w ∉ Set.range ι := by
    intro w hw
    exact map_interior_not_range_comp hext.1 hB0srcNew (by simpa [B0] using hw)
  have hA1new : ∀ w ∈ trackInterior A1, w ∉ Set.range ι := by
    intro w hw
    exact map_interior_not_range_comp hext.1 hA1srcNew (by simpa [A1] using hw)
  have hB1new : ∀ w ∈ trackInterior B1, w ∉ Set.range ι := by
    intro w hw
    exact map_interior_not_range_comp hext.1 hB1srcNew (by simpa [B1] using hw)
  have hCnew : ∀ w ∈ trackInterior C, w ∉ Set.range ι := by
    intro w hw
    exact map_interior_not_range_comp hext.1 hCsrcNew (by simpa [C] using hw)
  have hpNew : ∀ w ∈ trackInterior p, w ∉ Set.range ι := by
    intro w hw hr
    apply hext.2.2.2.2.1 w hw
    obtain ⟨u, hu⟩ := hr
    exact ⟨κ u, by simpa [ι] using hu⟩
  have hnew : ∀ u v : Fin 4, u ≠ v →
      ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι := by
    intro u v huv w hw
    fin_cases u <;> fin_cases v <;>
      simp [T, Workspace.ProofLemmas.TrackSlice.trackInterior_reverse] at huv hw
    all_goals first
      | exact hCnew w hw | exact hA0new w hw | exact hB0new w hw
      | exact hA1new w hw | exact hB1new w hw | exact hpNew w hw
  have sA0 : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 0) 0 k0), c ∈ trackInterior (Q 0) := by
    intro c hc; exact slice_interior_subset_interior hk0 (by omega) hc
  have sB0 : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 0) k0 ((Q 0).length - 1)),
      c ∈ trackInterior (Q 0) := by
    intro c hc; exact slice_interior_subset_interior (by omega) (by omega) hc
  have sA1 : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 1) 0 k1), c ∈ trackInterior (Q 1) := by
    intro c hc; exact slice_interior_subset_interior hk1 (by omega) hc
  have sB1 : ∀ c ∈ trackInterior
      (Workspace.ProofLemmas.TrackSlice.slice (Q 1) k1 ((Q 1).length - 1)),
      c ∈ trackInterior (Q 1) := by
    intro c hc; exact slice_interior_subset_interior (by omega) (by omega) hc
  have hCrange : ∀ w ∈ trackInterior C, w ∈ Set.range ρ := by
    intro w hw
    simp only [C, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hw
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hw
    exact ⟨c, rfl⟩
  have hA0range : ∀ w ∈ trackInterior A0, w ∈ Set.range ρ := by
    intro w hw
    simp only [A0, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hw
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hw
    exact ⟨c, rfl⟩
  have hB0range : ∀ w ∈ trackInterior B0, w ∈ Set.range ρ := by
    intro w hw
    simp only [B0, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hw
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hw
    exact ⟨c, rfl⟩
  have hA1range : ∀ w ∈ trackInterior A1, w ∈ Set.range ρ := by
    intro w hw
    simp only [A1, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hw
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hw
    exact ⟨c, rfl⟩
  have hB1range : ∀ w ∈ trackInterior B1, w ∈ Set.range ρ := by
    intro w hw
    simp only [B1, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hw
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hw
    exact ⟨c, rfl⟩
  have dCA0 : ∀ w, w ∈ trackInterior C → w ∈ trackInterior A0 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 2 0 (by decide))
      (fun c hc => hc) (fun c hc => mem_of_mem_trackInterior (sA0 c hc))
      (by simpa [C] using hw) (by simpa [A0] using hw')
  have dCB0 : ∀ w, w ∈ trackInterior C → w ∈ trackInterior B0 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 2 0 (by decide))
      (fun c hc => hc) (fun c hc => mem_of_mem_trackInterior (sB0 c hc))
      (by simpa [C] using hw) (by simpa [B0] using hw')
  have dCA1 : ∀ w, w ∈ trackInterior C → w ∈ trackInterior A1 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 2 1 (by decide))
      (fun c hc => hc) (fun c hc => mem_of_mem_trackInterior (sA1 c hc))
      (by simpa [C] using hw) (by simpa [A1] using hw')
  have dCB1 : ∀ w, w ∈ trackInterior C → w ∈ trackInterior B1 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 2 1 (by decide))
      (fun c hc => hc) (fun c hc => mem_of_mem_trackInterior (sB1 c hc))
      (by simpa [C] using hw) (by simpa [B1] using hw')
  have dA0B0 : ∀ w, w ∈ trackInterior A0 → w ∈ trackInterior B0 → False := by
    intro w hw hw'
    apply map_interior_disjoint hext.1
      (fun c hc hc' => slice_interiors_disjoint (hΘ.2.1 0).1.2.1 hk0 hk0Last hc hc')
      (by simpa [A0] using hw) (by simpa [B0] using hw')
  have dA1B1 : ∀ w, w ∈ trackInterior A1 → w ∈ trackInterior B1 → False := by
    intro w hw hw'
    apply map_interior_disjoint hext.1
      (fun c hc hc' => slice_interiors_disjoint (hΘ.2.1 1).1.2.1 hk1 hk1Last hc hc')
      (by simpa [A1] using hw) (by simpa [B1] using hw')
  have dA0A1 : ∀ w, w ∈ trackInterior A0 → w ∈ trackInterior A1 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 0 1 (by decide))
      sA0 (fun c hc => mem_of_mem_trackInterior (sA1 c hc))
      (by simpa [A0] using hw) (by simpa [A1] using hw')
  have dA0B1 : ∀ w, w ∈ trackInterior A0 → w ∈ trackInterior B1 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 0 1 (by decide))
      sA0 (fun c hc => mem_of_mem_trackInterior (sB1 c hc))
      (by simpa [A0] using hw) (by simpa [B1] using hw')
  have dB0A1 : ∀ w, w ∈ trackInterior B0 → w ∈ trackInterior A1 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 0 1 (by decide))
      sB0 (fun c hc => mem_of_mem_trackInterior (sA1 c hc))
      (by simpa [B0] using hw) (by simpa [A1] using hw')
  have dB0B1 : ∀ w, w ∈ trackInterior B0 → w ∈ trackInterior B1 → False := by
    intro w hw hw'
    exact map_interior_disjoint_of_cross hext.1 (hΘ.2.2.2.1 0 1 (by decide))
      sB0 (fun c hc => mem_of_mem_trackInterior (sB1 c hc))
      (by simpa [B0] using hw) (by simpa [B1] using hw')
  have dCp : ∀ w, w ∈ trackInterior C → w ∈ trackInterior p → False := by
    exact fun w hw hw' => map_interior_disjoint_from_new hext.2.2.2.2.1 hw hw' hCrange
  have dA0p : ∀ w, w ∈ trackInterior A0 → w ∈ trackInterior p → False := by
    exact fun w hw hw' => map_interior_disjoint_from_new hext.2.2.2.2.1 hw hw' hA0range
  have dB0p : ∀ w, w ∈ trackInterior B0 → w ∈ trackInterior p → False := by
    exact fun w hw hw' => map_interior_disjoint_from_new hext.2.2.2.2.1 hw hw' hB0range
  have dA1p : ∀ w, w ∈ trackInterior A1 → w ∈ trackInterior p → False := by
    exact fun w hw hw' => map_interior_disjoint_from_new hext.2.2.2.2.1 hw hw' hA1range
  have dB1p : ∀ w, w ∈ trackInterior B1 → w ∈ trackInterior p → False := by
    exact fun w hw hw' => map_interior_disjoint_from_new hext.2.2.2.2.1 hw hw' hB1range
  have hpairInt : ∀ u v u' v' : Fin 4, u < v → u' < v' →
      s(u, v) ≠ s(u', v') → ∀ w,
      w ∈ trackInterior (T u v) → w ∈ trackInterior (T u' v') → False := by
    intro u v u' v' huv huv' hs w hw hw'
    fin_cases u <;> fin_cases v <;> fin_cases u' <;> fin_cases v' <;>
      simp [T, Workspace.ProofLemmas.TrackSlice.trackInterior_reverse] at huv huv' hs hw hw'
    all_goals first
      | exact dCA0 w hw hw' | exact dCA0 w hw' hw
      | exact dCB0 w hw hw' | exact dCB0 w hw' hw
      | exact dCA1 w hw hw' | exact dCA1 w hw' hw
      | exact dCB1 w hw hw' | exact dCB1 w hw' hw
      | exact dA0B0 w hw hw' | exact dA0B0 w hw' hw
      | exact dA1B1 w hw hw' | exact dA1B1 w hw' hw
      | exact dA0A1 w hw hw' | exact dA0A1 w hw' hw
      | exact dA0B1 w hw hw' | exact dA0B1 w hw' hw
      | exact dB0A1 w hw hw' | exact dB0A1 w hw' hw
      | exact dB0B1 w hw hw' | exact dB0B1 w hw' hw
      | exact dCp w hw hw' | exact dCp w hw' hw
      | exact dA0p w hw hw' | exact dA0p w hw' hw
      | exact dB0p w hw hw' | exact dB0p w hw' hw
      | exact dA1p w hw hw' | exact dA1p w hw' hw
      | exact dB1p w hw hw' | exact dB1p w hw' hw
  have hswapInt : ∀ u v : Fin 4, u ≠ v → ∀ w,
      w ∈ trackInterior (T u v) → w ∈ trackInterior (T v u) := by
    intro u v huv w hw
    rw [hrev u v huv, Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse]
    exact hw
  have hdisj : ∀ u v u' v' : Fin 4, u ≠ v → u' ≠ v' →
      s(u, v) ≠ s(u', v') → ∀ w ∈ trackInterior (T u v), w ∉ T u' v' := by
    intro u v u' v' huv huv' hs w hw hmem
    rcases member_eq_end_or_internal (htrack u' v' huv') hmem with he | he | hint
    · exact hnew u v huv w hw ⟨u', he.symm⟩
    · exact hnew u v huv w hw ⟨v', he.symm⟩
    · rcases lt_or_gt_of_ne huv with huvlt | huvgt <;>
        rcases lt_or_gt_of_ne huv' with huv'lt | huv'gt
      · exact hpairInt u v u' v' huvlt huv'lt hs w hw hint
      · exact hpairInt u v v' u' huvlt huv'gt (by simpa [Sym2.eq_swap] using hs)
          w hw (hswapInt u' v' huv' w hint)
      · exact hpairInt v u u' v' huvgt huv'lt (by simpa [Sym2.eq_swap] using hs)
          w (hswapInt u v huv w hw) hint
      · exact hpairInt v u v' u' huvgt huv'gt (by simpa [Sym2.eq_swap] using hs)
          w (hswapInt u v huv w hw) (hswapInt u' v' huv' w hint)
  have hcover : ∀ w : Fin m', (∃ u : Fin 4, w = ι u) ∨
      ∃ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v ∧
        w ∈ trackInterior (T u v) := by
    intro w
    rcases hext.2.2.2.2.2.1 w with hwold | hwp
    · obtain ⟨c, rfl⟩ := hwold
      rcases hΘ.2.2.2.2.2.1 c with rfl | rfl | ⟨i, hi⟩
      · exact Or.inl ⟨0, by simp [ι, κ]⟩
      · exact Or.inl ⟨1, by simp [ι, κ]⟩
      · fin_cases i
        · obtain ⟨j, hj, hjc⟩ :=
            (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff (Q 0) c).mp hi
          by_cases hjk : j + 1 < k0
          · right
            refine ⟨0, 2, by simp, ?_⟩
            have hs : c ∈ trackInterior
                (Workspace.ProofLemmas.TrackSlice.slice (Q 0) 0 k0) := by
              rw [Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff hk0 (by omega)]
              exact ⟨j + 1, by omega, by omega, hjk, hjc⟩
            have hm : ρ c ∈ trackInterior A0 := by
              simp only [A0, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map]
              exact List.mem_map.mpr ⟨c, hs, rfl⟩
            simpa only [T] using hm
          · by_cases heq : j + 1 = k0
            · left
              refine ⟨2, ?_⟩
              have hcz : c = z := by
                exact hjc.symm.trans
                  ((Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
                    (Q 0) heq (by omega) hk0).trans hzpos')
              simp [ι, κ, hcz]
            · right
              refine ⟨2, 1, by simp, ?_⟩
              have hs : c ∈ trackInterior
                  (Workspace.ProofLemmas.TrackSlice.slice (Q 0) k0 ((Q 0).length - 1)) := by
                rw [Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff (by omega) (by omega)]
                exact ⟨j + 1, by omega, by omega, by omega, hjc⟩
              have hm : ρ c ∈ trackInterior B0 := by
                simp only [B0, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map]
                exact List.mem_map.mpr ⟨c, hs, rfl⟩
              simpa only [T] using hm
        · obtain ⟨j, hj, hjc⟩ :=
            (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff (Q 1) c).mp hi
          by_cases hjk : j + 1 < k1
          · right
            refine ⟨0, 3, by simp, ?_⟩
            have hs : c ∈ trackInterior
                (Workspace.ProofLemmas.TrackSlice.slice (Q 1) 0 k1) := by
              rw [Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff hk1 (by omega)]
              exact ⟨j + 1, by omega, by omega, hjk, hjc⟩
            have hm : ρ c ∈ trackInterior A1 := by
              simp only [A1, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map]
              exact List.mem_map.mpr ⟨c, hs, rfl⟩
            simpa only [T] using hm
          · by_cases heq : j + 1 = k1
            · left
              refine ⟨3, ?_⟩
              have hcz : c = z' := by
                exact hjc.symm.trans
                  ((Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
                    (Q 1) heq (by omega) hk1).trans hz'pos')
              simp [ι, κ, hcz]
            · right
              refine ⟨3, 1, by simp, ?_⟩
              have hs : c ∈ trackInterior
                  (Workspace.ProofLemmas.TrackSlice.slice (Q 1) k1 ((Q 1).length - 1)) := by
                rw [Workspace.ProofLemmas.TrackSlice.mem_trackInterior_slice_iff (by omega) (by omega)]
                exact ⟨j + 1, by omega, by omega, by omega, hjc⟩
              have hm : ρ c ∈ trackInterior B1 := by
                simp only [B1, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map]
                exact List.mem_map.mpr ⟨c, hs, rfl⟩
              simpa only [T] using hm
        · right
          refine ⟨0, 1, by simp, ?_⟩
          have hm : ρ c ∈ trackInterior C := by
            simp only [C, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map]
            exact List.mem_map.mpr ⟨c, hi, rfl⟩
          simpa only [T] using hm
    · right
      exact ⟨2, 3, by simp, by simpa [T] using hwp⟩
  let sixEdges : Set (Sym2 (Fin m')) :=
    trackEdges C ∪
      (trackEdges A0 ∪
        (trackEdges B0 ∪
          (trackEdges A1 ∪
            (trackEdges B1 ∪ trackEdges p))))
  have hRhsSix :
      (⋃ (u : Fin 4) (v : Fin 4) (_ : (⊤ : SimpleGraph (Fin 4)).Adj u v),
        trackEdges (T u v)) = sixEdges := by
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, v, huv, he⟩
      have huv' : u ≠ v := by simpa only [SimpleGraph.top_adj] using huv
      fin_cases u
      · fin_cases v
        · exact (huv' rfl).elim
        · exact Or.inl (by simpa only [T] using he)
        · exact Or.inr (Or.inl (by simpa only [T] using he))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [T] using he))))
      · fin_cases v
        · exact Or.inl (by
            have he' := he
            rw [hrev _ _ huv'.symm,
              Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at he'
            simpa only [T] using he')
        · exact (huv' rfl).elim
        · exact Or.inr (Or.inr (Or.inl (by
            have he' := he
            rw [hrev _ _ huv'.symm,
              Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at he'
            simpa only [T] using he')))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
            have he' := he
            rw [hrev _ _ huv'.symm,
              Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at he'
            simpa only [T] using he')))))
      · fin_cases v
        · exact Or.inr (Or.inl (by
            have he' := he
            rw [hrev _ _ huv'.symm,
              Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at he'
            simpa only [T] using he'))
        · exact Or.inr (Or.inr (Or.inl (by simpa only [T] using he)))
        · exact (huv' rfl).elim
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [T] using he)))))
      · fin_cases v
        · exact Or.inr (Or.inr (Or.inr (Or.inl (by
            have he' := he
            rw [hrev _ _ huv'.symm,
              Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at he'
            simpa only [T] using he'))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [T] using he)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
            have he' := he
            rw [hrev _ _ huv'.symm,
              Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at he'
            simpa only [T] using he')))))
        · exact (huv' rfl).elim
    · intro he
      rcases he with h | h | h | h | h | h
      · exact ⟨0, 1, by simp, by simpa only [T] using h⟩
      · exact ⟨0, 2, by simp, by simpa only [T] using h⟩
      · exact ⟨2, 1, by simp, by simpa only [T] using h⟩
      · exact ⟨0, 3, by simp, by simpa only [T] using h⟩
      · exact ⟨3, 1, by simp, by simpa only [T] using h⟩
      · exact ⟨2, 3, by simp, by simpa only [T] using h⟩
  have hHsix : H.edgeSet = sixEdges := by
    ext e
    constructor
    · intro he
      rw [hext.2.2.2.2.2.2] at he
      rcases he with ⟨e0, he0, rfl⟩ | hpedge
      · rw [hΘ.2.2.2.2.2.2] at he0
        simp only [Set.mem_iUnion] at he0
        obtain ⟨i, hi⟩ := he0
        fin_cases i
        · change e0 ∈ trackEdges (Q 0) at hi
          rw [trackEdges_split (Q 0) hk0 hk0Last] at hi
          rcases hi with hi | hi
          · have hm : Sym2.map ρ e0 ∈ trackEdges A0 := by
              simp only [A0, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
              exact ⟨e0, hi, rfl⟩
            exact Or.inr (Or.inl hm)
          · have hm : Sym2.map ρ e0 ∈ trackEdges B0 := by
              simp only [B0, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
              exact ⟨e0, hi, rfl⟩
            exact Or.inr (Or.inr (Or.inl hm))
        · change e0 ∈ trackEdges (Q 1) at hi
          rw [trackEdges_split (Q 1) hk1 hk1Last] at hi
          rcases hi with hi | hi
          · have hm : Sym2.map ρ e0 ∈ trackEdges A1 := by
              simp only [A1, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
              exact ⟨e0, hi, rfl⟩
            exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
          · have hm : Sym2.map ρ e0 ∈ trackEdges B1 := by
              simp only [B1, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
              exact ⟨e0, hi, rfl⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
        · have hm : Sym2.map ρ e0 ∈ trackEdges C := by
            change e0 ∈ trackEdges (Q 2) at hi
            simp only [C, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
            exact ⟨e0, hi, rfl⟩
          exact Or.inl hm
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hpedge))))
    · intro he
      rw [hext.2.2.2.2.2.2]
      rcases he with h | h | h | h | h | h
      · simp only [C, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at h
        obtain ⟨e0, he0, rfl⟩ := h
        left
        refine ⟨e0, ?_, rfl⟩
        rw [hΘ.2.2.2.2.2.2]
        simp only [Set.mem_iUnion]
        exact ⟨2, he0⟩
      · simp only [A0, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at h
        obtain ⟨e0, he0, rfl⟩ := h
        left
        refine ⟨e0, ?_, rfl⟩
        rw [hΘ.2.2.2.2.2.2]
        simp only [Set.mem_iUnion]
        exact ⟨0, trackEdges_slice_subset (Q 0) hk0 (by omega) he0⟩
      · simp only [B0, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at h
        obtain ⟨e0, he0, rfl⟩ := h
        left
        refine ⟨e0, ?_, rfl⟩
        rw [hΘ.2.2.2.2.2.2]
        simp only [Set.mem_iUnion]
        exact ⟨0, trackEdges_slice_subset (Q 0) (by omega) (by omega) he0⟩
      · simp only [A1, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at h
        obtain ⟨e0, he0, rfl⟩ := h
        left
        refine ⟨e0, ?_, rfl⟩
        rw [hΘ.2.2.2.2.2.2]
        simp only [Set.mem_iUnion]
        exact ⟨1, trackEdges_slice_subset (Q 1) hk1 (by omega) he0⟩
      · simp only [B1, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at h
        obtain ⟨e0, he0, rfl⟩ := h
        left
        refine ⟨e0, ?_, rfl⟩
        rw [hΘ.2.2.2.2.2.2]
        simp only [Set.mem_iUnion]
        exact ⟨1, trackEdges_slice_subset (Q 1) (by omega) (by omega) he0⟩
      · exact Or.inr h
  have hedges : H.edgeSet =
      ⋃ (u : Fin 4) (v : Fin 4) (_ : (⊤ : SimpleGraph (Fin 4)).Adj u v),
        trackEdges (T u v) := hHsix.trans hRhsSix.symm
  have topAdj : ∀ {u v : Fin 4}, (⊤ : SimpleGraph (Fin 4)).Adj u v → u ≠ v := by
    intro u v huv
    simpa only [SimpleGraph.top_adj] using huv
  have hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H :=
    ⟨ι, T, hι,
      fun u v h => htrack u v (topAdj h),
      fun u v h => hlen u v (topAdj h),
      fun u v h => hrev u v (topAdj h),
      fun u v u' v' h h' => hdisj u v u' v' (topAdj h) (topAdj h'),
      fun u v h => hnew u v (topAdj h), hcover, hedges⟩
  have hdeg : ∀ u : Fin 4,
      3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    fun u => Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected
      (⊤ : SimpleGraph (Fin 4))
      Workspace.ProofLemmas.SubdivisionCounting.k4_three_connected u
  have hbLower : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices hι
      (fun u v h => htrack u v (topAdj h))
      (fun u v h => hlen u v (topAdj h))
      (fun u v u' v' h h' => hdisj u v u' v' (topAdj h) (topAdj h'))
      (fun u v h => hnew u v (topAdj h)) hdeg
  have hbUpper : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      (fun u v h => htrack u v (topAdj h))
      (fun u v h => hrev u v (topAdj h))
      (fun u v u' v' h h' => hdisj u v u' v' (topAdj h) (topAdj h'))
      hcover hedges
  have hb : branchVertices H = Set.range ι := Set.Subset.antisymm hbUpper hbLower
  have hrange : Set.range ι = ({ρ x, ρ y, ρ z, ρ z'} : Set (Fin m')) := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      fin_cases u <;> simp [ι, κ]
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [ι, κ]⟩
      · exact ⟨1, by simp [ι, κ]⟩
      · exact ⟨2, by simp [ι, κ]⟩
      · exact ⟨3, by simp [ι, κ]⟩
  exact ⟨hb.trans hrange, hsub⟩

end Workspace.ProofLemmas
