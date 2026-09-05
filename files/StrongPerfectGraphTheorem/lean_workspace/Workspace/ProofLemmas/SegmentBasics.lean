import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.ExtremalChoice

/-!
# `Y`-segments of a hole

`Workspace.Types.Wheels.SPGT.IsSegment G H Y S` transcribes the paper's *"maximal path in `H`
all of whose vertices are `Y`-complete"* (printed p. 96) literally: `S` is a path, it is a
cyclically consecutive block of `H` in one of its two orientations, its vertices are `Y`-complete,
and it is maximal among all such blocks.  Section 16 then uses segments as if they were
*maximal runs of consecutive `Y`-complete positions* — it counts them, it says two of them are
distinct, it says an odd number of edges of one of them lies in some other hole.

This module supplies that reading.  Writing `n = C.length` and `CycVert m` for *"the vertex at
cyclic position `m` of `C` is `Y`-complete"*, the content is:

* `isSegment_of_run` — the **constructor**: a run `k, …, k+L-1` of `Y`-complete positions whose
  two cyclic neighbours `k-1` and `k+L` are not `Y`-complete gives a genuine `IsSegment`
  witness, maximality clause and all (that clause quantifies over *every* block of `C` in *both*
  orientations, which is the part that has to be done by hand);
* `isSegment_run` — the **decoder**: every segment is such a run;
* `isSegment_onArc_unique` — two segments meeting in a vertex have the same vertex set, so
  distinct segments are disjoint;
* `exists_isSegment_of_cycVert` — every `Y`-complete vertex of `C` lies in a segment, provided
  some vertex of `C` is not `Y`-complete;
* `odd_pathLength_iff_even_length` — *"an odd segment"* means an **even** number of vertices.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.SegmentBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.WheelParity

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### Cyclic positions -/

/-- The vertex at cyclic position `m` of `C` is `Y`-complete.  Stated with `getElem?` so that it
is total in `m`. -/
def CycVert (G : SimpleGraph V) (Y : Set V) (C : List V) (m : ℕ) : Prop :=
  ∃ u : V, C[m % C.length]? = some u ∧ VertexComplete G u Y

/-- `x` occupies one of the cyclic positions `k, k+1, …, k+L-1` of `C`. -/
def OnArc (C : List V) (k L : ℕ) (x : V) : Prop :=
  ∃ t, t < L ∧ C[(k + t) % C.length]? = some x

theorem add_mod_congr {n a b : ℕ} (h : a % n = b % n) (t : ℕ) :
    (a + t) % n = (b + t) % n := by
  rw [← Nat.mod_add_mod, h, Nat.mod_add_mod]

theorem cycVert_congr {a b : ℕ} (h : a % C.length = b % C.length) :
    CycVert G Y C a ↔ CycVert G Y C b := by
  simp only [CycVert, h]

theorem onArc_congr {k k' L : ℕ} (h : k % C.length = k' % C.length) {x : V} :
    OnArc C k L x ↔ OnArc C k' L x := by
  constructor
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, by rwa [← add_mod_congr h t]⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨t, ht, by rwa [add_mod_congr h t]⟩

/-- The position of a vertex of a hole is determined. -/
theorem pos_unique (hC : IsHoleList G C) {a b : ℕ} {x : V}
    (ha : C[a % C.length]? = some x) (hb : C[b % C.length]? = some x) :
    a % C.length = b % C.length := by
  have hn : 0 < C.length := by have := hC.1; omega
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at ha hb
  exact (List.Nodup.getElem_inj_iff hC.2.1).mp
    ((Option.some_injective _ ha).trans (Option.some_injective _ hb).symm)

/-- Every cyclic position is occupied. -/
theorem exists_at_pos (hn : 0 < C.length) (m : ℕ) : ∃ u : V, C[m % C.length]? = some u := by
  refine ⟨C[m % C.length]'(Nat.mod_lt _ hn), ?_⟩
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)]

theorem mem_of_pos (hn : 0 < C.length) {m : ℕ} {u : V} (h : C[m % C.length]? = some u) :
    u ∈ C := by
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at h
  rw [← Option.some_injective _ h]
  exact List.getElem_mem _

/-! ### Arcs of the hole -/

theorem arc_getElem (hn : 0 < C.length) {k L t : ℕ} (ht : t < ((C.rotate k).take L).length) :
    ((C.rotate k).take L)[t]'ht = C[(k + t) % C.length]'(Nat.mod_lt _ hn) := by
  have h1 : t < (C.rotate k).length := by
    simp only [List.length_take] at ht; omega
  have e : ((C.rotate k).take L)[t]'ht = ((C.rotate k)[t]'h1) := by simp only [List.getElem_take]
  rw [e, getElem_rotate_eq hn]
  simp only [show t + k = k + t by omega]

theorem mem_arc_iff (hn : 0 < C.length) {k L : ℕ} (hL : L ≤ C.length) {x : V} :
    x ∈ (C.rotate k).take L ↔ OnArc C k L x := by
  constructor
  · intro hx
    obtain ⟨t, ht, htx⟩ := List.getElem_of_mem hx
    have ht' : t < L := by
      simp only [List.length_take, List.length_rotate] at ht; omega
    refine ⟨t, ht', ?_⟩
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn), ← arc_getElem hn ht, htx]
  · rintro ⟨t, ht, hx⟩
    have ht2 : t < ((C.rotate k).take L).length := by
      simp only [List.length_take, List.length_rotate]; omega
    have hval : ((C.rotate k).take L)[t]'ht2 = x := by
      rw [arc_getElem hn ht2]
      rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hx
      exact Option.some_injective _ hx
    rw [← hval]
    exact List.getElem_mem _

/-- The vertices of an arc are all `Y`-complete as soon as its positions are. -/
theorem arc_vertexComplete (hn : 0 < C.length) {k L : ℕ} (hL : L ≤ C.length)
    (hall : ∀ t < L, CycVert G Y C (k + t)) :
    ∀ w ∈ (C.rotate k).take L, w ∈ C ∧ VertexComplete G w Y := by
  intro w hw
  obtain ⟨t, ht, htw⟩ := (mem_arc_iff hn hL).mp hw
  obtain ⟨u, hu, huY⟩ := hall t ht
  have huw : u = w := Option.some_injective _ (hu.symm.trans htw)
  subst huw
  exact ⟨mem_of_pos hn hu, huY⟩

/-- A path of `G` occupying consecutive positions of a hole cannot use every vertex of it. -/
theorem length_le_of_path_prefix (hC : IsHoleList G C) {T : List V} {k : ℕ}
    (hT : IsPathList G T) (hpre : T <+: C.rotate k) : T.length + 1 ≤ C.length := by
  have hn4 : 4 ≤ C.length := hC.1
  have hpos : 0 < T.length := PathBasics.path_length_pos hT
  have hlenr : (C.rotate k).length = C.length := by simp
  have hle : T.length ≤ C.length := by have := hpre.length_le; omega
  rcases Nat.lt_or_ge T.length C.length with h | h
  · omega
  exfalso
  have h1 : T.length - 1 < T.length := by omega
  have hCr : IsHoleList G (C.rotate k) := HoleBasics.isHoleList_rotate hC k
  have i0 : (0 : ℕ) < (C.rotate k).length := by omega
  have i1 : T.length - 1 < (C.rotate k).length := by omega
  have hadjC : G.Adj ((C.rotate k)[0]'i0) ((C.rotate k)[T.length - 1]'i1) :=
    (HoleBasics.hole_adj_iff hCr i0 i1).mpr (Or.inr (by
      rw [show T.length - 1 + 1 = (C.rotate k).length by omega, Nat.mod_self]))
  have hadj : G.Adj (T[0]'hpos) (T[T.length - 1]'h1) := by
    rw [hpre.getElem hpos, hpre.getElem h1]
    exact hadjC
  have := (PathBasics.path_adj_iff hT hpos h1).mp hadj
  omega

/-- Positions of the vertices of a prefix of a rotation. -/
theorem prefix_pos (hn : 0 < C.length) {T : List V} {k : ℕ} (hpre : T <+: C.rotate k)
    {s : ℕ} (hs : s < T.length) : C[(k + s) % C.length]? = some (T[s]'hs) := by
  have hs' : s < (C.rotate k).length := by have := hpre.length_le; omega
  have e1 : (T[s]'hs) = ((C.rotate k)[s]'hs') := hpre.getElem hs
  have e2 : ((C.rotate k)[s]'hs') = C[(k + s) % C.length]'(Nat.mod_lt _ hn) := by
    rw [getElem_rotate_eq hn hs']
    simp only [show s + k = k + s by omega]
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn), e1.trans e2]

/-! ### The constructor -/

/-- **A maximal run of `Y`-complete positions is a `Y`-segment.**  The hard part is the
maximality clause of `IsSegment`, which ranges over every consecutive block of `C` in either
orientation. -/
theorem isSegment_of_run (hC : IsHoleList G C) {k L : ℕ}
    (h1 : 1 ≤ L) (h2 : L + 1 ≤ C.length)
    (hall : ∀ t < L, CycVert G Y C (k + t))
    (hnext : ¬ CycVert G Y C (k + L))
    (hprev : ¬ CycVert G Y C (k + (C.length - 1))) :
    IsSegment G C Y ((C.rotate k).take L) := by
  have hn : 0 < C.length := by have := hC.1; omega
  have hn4 : 4 ≤ C.length := hC.1
  refine ⟨⟨isPathList_rotate_take hC h1 h2, ⟨k, Or.inl (List.take_prefix _ _)⟩,
    arc_vertexComplete hn (by omega) hall⟩, ?_⟩
  intro T hT harc hTY hsub
  obtain ⟨k', hk'⟩ := harc
  obtain ⟨T', hT'pre, hT'mem, hT'len⟩ : ∃ T' : List V, T' <+: C.rotate k' ∧
      (∀ x, x ∈ T' ↔ x ∈ T) ∧ T'.length = T.length := by
    rcases hk' with h | h
    · exact ⟨T, h, fun _ => Iff.rfl, rfl⟩
    · exact ⟨T.reverse, h, fun x => List.mem_reverse, by simp⟩
  have hMle : T'.length ≤ C.length := by
    have := hT'pre.length_le
    have hlenr : (C.rotate k').length = C.length := by simp
    omega
  have hTcyc : ∀ s (hs : s < T'.length), CycVert G Y C (k' + s) := fun s hs =>
    ⟨T'[s]'hs, prefix_pos hn hT'pre hs, (hTY _ ((hT'mem _).mp (List.getElem_mem hs))).2⟩
  -- the first vertex of the run lies on `T`
  obtain ⟨u₀, hu₀⟩ := exists_at_pos (C := C) hn (k + 0)
  have hu₀S : u₀ ∈ (C.rotate k).take L := (mem_arc_iff hn (by omega)).mpr ⟨0, by omega, hu₀⟩
  obtain ⟨d, hd, hdpos⟩ : ∃ d, ∃ hd : d < T'.length, C[(k' + d) % C.length]? = some u₀ := by
    obtain ⟨d, hd, hdv⟩ := List.getElem_of_mem ((hT'mem u₀).mpr (hsub u₀ hu₀S))
    exact ⟨d, hd, by rw [prefix_pos hn hT'pre hd, hdv]⟩
  have hshift : ∀ t : ℕ, (k + t) % C.length = (k' + d + t) % C.length := by
    intro t
    exact add_mod_congr (by simpa using pos_unique hC hu₀ hdpos) t
  -- `d = 0`
  have hd0 : d = 0 := by
    by_contra hcon
    refine hprev ((cycVert_congr ?_).mpr (hTcyc (d - 1) (by omega)))
    rw [hshift (C.length - 1),
      show k' + d + (C.length - 1) = (k' + (d - 1)) + C.length by omega, Nat.add_mod_right]
  have hshift0 : ∀ t : ℕ, (k + t) % C.length = (k' + t) % C.length := by
    intro t; rw [hshift t, hd0, Nat.add_zero]
  have hML : T'.length ≤ L := by
    by_contra hcon
    exact hnext ((cycVert_congr (hshift0 L)).mpr (hTcyc L (by omega)))
  intro w hw
  obtain ⟨s, hs, hsw⟩ := List.getElem_of_mem ((hT'mem w).mpr hw)
  refine (mem_arc_iff hn (by omega)).mpr ⟨s, by omega, ?_⟩
  rw [hshift0 s, prefix_pos hn hT'pre hs, hsw]

/-! ### The decoder -/

/-- **Every `Y`-segment is a maximal run of `Y`-complete positions.** -/
theorem isSegment_run (hC : IsHoleList G C) {S : List V} (hS : IsSegment G C Y S)
    (hlen : S.length + 2 ≤ C.length) :
    ∃ k : ℕ, 1 ≤ S.length ∧
      (∀ t < S.length, CycVert G Y C (k + t)) ∧
      ¬ CycVert G Y C (k + S.length) ∧
      ¬ CycVert G Y C (k + (C.length - 1)) ∧
      (∀ x : V, x ∈ S ↔ OnArc C k S.length x) := by
  have hn : 0 < C.length := by have := hC.1; omega
  have hn4 : 4 ≤ C.length := hC.1
  obtain ⟨⟨hpath, ⟨k, hk⟩, hSY⟩, hmax⟩ := hS
  have hpos : 1 ≤ S.length := PathBasics.path_length_pos hpath
  obtain ⟨S', hS'pre, hS'mem, hS'len⟩ : ∃ S' : List V, S' <+: C.rotate k ∧
      (∀ x, x ∈ S' ↔ x ∈ S) ∧ S'.length = S.length := by
    rcases hk with h | h
    · exact ⟨S, h, fun _ => Iff.rfl, rfl⟩
    · exact ⟨S.reverse, h, fun x => List.mem_reverse, by simp⟩
  have hS'take : S' = (C.rotate k).take S.length := by
    rw [← hS'len]; exact List.prefix_iff_eq_take.mp hS'pre
  have hmem : ∀ x : V, x ∈ S ↔ OnArc C k S.length x := by
    intro x
    rw [← hS'mem, hS'take, mem_arc_iff hn (by omega)]
  have hall : ∀ t < S.length, CycVert G Y C (k + t) := by
    intro t ht
    obtain ⟨u, hu⟩ := exists_at_pos (C := C) hn (k + t)
    exact ⟨u, hu, (hSY u ((hmem u).mpr ⟨t, ht, hu⟩)).2⟩
  -- every position of a one-step extension of `S` is already a position of `S`
  have key : ∀ m : ℕ, (∀ t < S.length + 1, CycVert G Y C (m + t)) →
      (∀ t < S.length, ∃ s < S.length + 1, (m + s) % C.length = (k + t) % C.length) →
      ∀ e < S.length + 1, ∃ t < S.length, (k + t) % C.length = (m + e) % C.length := by
    intro m hmall hmsub e he
    have hsub : ∀ w ∈ S, w ∈ (C.rotate m).take (S.length + 1) := by
      intro w hw
      obtain ⟨t, ht, htw⟩ := (hmem w).mp hw
      obtain ⟨s, hs, hst⟩ := hmsub t ht
      exact (mem_arc_iff hn (by omega)).mpr ⟨s, hs, by rw [hst]; exact htw⟩
    have hback := hmax ((C.rotate m).take (S.length + 1))
      (isPathList_rotate_take hC (by omega) (by omega))
      ⟨m, Or.inl (List.take_prefix _ _)⟩
      (arc_vertexComplete hn (by omega) hmall) hsub
    obtain ⟨u, hu⟩ := exists_at_pos (C := C) hn (m + e)
    have huS : u ∈ S := hback u ((mem_arc_iff hn (by omega)).mpr ⟨e, he, hu⟩)
    obtain ⟨t, ht, htu⟩ := (hmem u).mp huS
    exact ⟨t, ht, pos_unique hC htu hu⟩
  refine ⟨k, hpos, hall, ?_, ?_, hmem⟩
  · -- `k + |S|` is not `Y`-complete
    intro hcon
    obtain ⟨t, ht, hteq⟩ := key k
      (by
        intro t ht
        rcases Nat.lt_or_ge t S.length with h | h
        · exact hall t h
        · exact (cycVert_congr (by congr 1; omega)).mpr hcon)
      (fun t ht => ⟨t, by omega, rfl⟩) S.length (by omega)
    have hcancel : t % C.length = S.length % C.length := Nat.ModEq.add_left_cancel' k hteq
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcancel
    omega
  · -- `k - 1` is not `Y`-complete
    intro hcon
    obtain ⟨t, ht, hteq⟩ := key (k + (C.length - 1))
      (by
        intro t ht
        rcases Nat.eq_zero_or_pos t with rfl | hpos'
        · simpa using hcon
        · refine (cycVert_congr ?_).mpr (hall (t - 1) (by omega))
          rw [show k + (C.length - 1) + t = (k + (t - 1)) + C.length by omega, Nat.add_mod_right])
      (by
        intro t ht
        refine ⟨t + 1, by omega, ?_⟩
        rw [show k + (C.length - 1) + (t + 1) = (k + t) + C.length by omega, Nat.add_mod_right])
      0 (by omega)
    have hteq' : (k + t) % C.length = (k + (C.length - 1)) % C.length := by simpa using hteq
    have hcancel : t % C.length = (C.length - 1) % C.length :=
      Nat.ModEq.add_left_cancel' k hteq'
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hcancel
    omega

/-! ### Uniqueness, disjointness, and existence -/

/-- Two segments that meet have the same vertex set; so distinct segments are disjoint. -/
theorem isSegment_onArc_unique (hC : IsHoleList G C) {S₁ S₂ : List V}
    (h₁ : IsSegment G C Y S₁) (h₂ : IsSegment G C Y S₂)
    (hlen₁ : S₁.length + 2 ≤ C.length) (hlen₂ : S₂.length + 2 ≤ C.length)
    {x : V} (hx₁ : x ∈ S₁) (hx₂ : x ∈ S₂) : ∀ w : V, w ∈ S₁ ↔ w ∈ S₂ := by
  have hn : 0 < C.length := by have := hC.1; omega
  obtain ⟨k₁, hpos₁, hall₁, hnext₁, hprev₁, hmem₁⟩ := isSegment_run hC h₁ hlen₁
  obtain ⟨k₂, hpos₂, hall₂, hnext₂, hprev₂, hmem₂⟩ := isSegment_run hC h₂ hlen₂
  obtain ⟨t₁, ht₁, hp₁⟩ := (hmem₁ x).mp hx₁
  obtain ⟨t₂, ht₂, hp₂⟩ := (hmem₂ x).mp hx₂
  have hshare : (k₁ + t₁) % C.length = (k₂ + t₂) % C.length := pos_unique hC hp₁ hp₂
  have hF : S₁.length - t₁ = S₂.length - t₂ := by
    by_contra hcon
    rcases Nat.lt_or_ge (S₁.length - t₁) (S₂.length - t₂) with h | h
    · refine hnext₁ ((cycVert_congr ?_).mpr (hall₂ (t₂ + (S₁.length - t₁)) (by omega)))
      have e := add_mod_congr hshare (S₁.length - t₁)
      rw [show k₁ + t₁ + (S₁.length - t₁) = k₁ + S₁.length by omega,
        show k₂ + t₂ + (S₁.length - t₁) = k₂ + (t₂ + (S₁.length - t₁)) by omega] at e
      exact e
    · have h' : S₂.length - t₂ < S₁.length - t₁ := by omega
      refine hnext₂ ((cycVert_congr ?_).mpr (hall₁ (t₁ + (S₂.length - t₂)) (by omega)))
      have e := add_mod_congr hshare.symm (S₂.length - t₂)
      rw [show k₂ + t₂ + (S₂.length - t₂) = k₂ + S₂.length by omega,
        show k₁ + t₁ + (S₂.length - t₂) = k₁ + (t₁ + (S₂.length - t₂)) by omega] at e
      exact e
  have hB : t₁ = t₂ := by
    by_contra hcon
    rcases Nat.lt_or_ge t₁ t₂ with h | h
    · refine hprev₁ ((cycVert_congr ?_).mpr (hall₂ (t₂ - (t₁ + 1)) (by omega)))
      have e := add_mod_congr hshare (C.length - (t₁ + 1))
      rw [show k₁ + t₁ + (C.length - (t₁ + 1)) = k₁ + (C.length - 1) by omega,
        show k₂ + t₂ + (C.length - (t₁ + 1)) = (k₂ + (t₂ - (t₁ + 1))) + C.length by omega,
        Nat.add_mod_right] at e
      exact e
    · have h' : t₂ < t₁ := by omega
      refine hprev₂ ((cycVert_congr ?_).mpr (hall₁ (t₁ - (t₂ + 1)) (by omega)))
      have e := add_mod_congr hshare.symm (C.length - (t₂ + 1))
      rw [show k₂ + t₂ + (C.length - (t₂ + 1)) = k₂ + (C.length - 1) by omega,
        show k₁ + t₁ + (C.length - (t₂ + 1)) = (k₁ + (t₁ - (t₂ + 1))) + C.length by omega,
        Nat.add_mod_right] at e
      exact e
  subst hB
  have hLen : S₁.length = S₂.length := by omega
  have hk : k₁ % C.length = k₂ % C.length := Nat.ModEq.add_right_cancel' t₁ hshare
  intro w
  rw [hmem₁ w, hmem₂ w, hLen, onArc_congr hk]

/-- Every `Y`-complete vertex of `C` lies in a maximal run, as soon as some vertex of `C` is not
`Y`-complete. -/
theorem exists_run_of_cycVert (hC : IsHoleList G C) {i j : ℕ}
    (hi : CycVert G Y C i) (hj : ¬ CycVert G Y C j) :
    ∃ (k L : ℕ), 1 ≤ L ∧ L + 1 ≤ C.length ∧
      (∀ t < L, CycVert G Y C (k + t)) ∧
      ¬ CycVert G Y C (k + L) ∧ ¬ CycVert G Y C (k + (C.length - 1)) ∧
      (∃ t < L, (k + t) % C.length = i % C.length) := by
  have hn : 0 < C.length := by have := hC.1; omega
  have hn4 : 4 ≤ C.length := hC.1
  obtain ⟨⟨k, L⟩, ⟨hLle, hrun, hcov⟩, hmax⟩ :=
    ExtremalChoice.exists_max_nat
      (fun p : ℕ × ℕ => p.2 ≤ C.length ∧ (∀ t < p.2, CycVert G Y C (p.1 + t)) ∧
        ∃ t < p.2, (p.1 + t) % C.length = i % C.length)
      (fun p => p.2) C.length (fun p hp => hp.1)
      ⟨⟨i, 1⟩, by omega, by
        intro t ht
        have h0 : t = 0 := by omega
        subst h0
        simpa using hi, ⟨0, by omega, by simp⟩⟩
  simp only at hLle hrun hcov hmax
  have hL1 : 1 ≤ L := by obtain ⟨t, ht, -⟩ := hcov; omega
  have hLlt : L + 1 ≤ C.length := by
    rcases Nat.lt_or_ge L C.length with h | h
    · omega
    exfalso
    have hLeq : L = C.length := by omega
    have hkm : k % C.length < C.length := Nat.mod_lt _ hn
    have e : (k + (j + C.length - k % C.length) % C.length) % C.length = j % C.length := by
      have s1 : (k + (j + C.length - k % C.length) % C.length) % C.length
          = (k % C.length + (j + C.length - k % C.length) % C.length) % C.length :=
        (Nat.mod_add_mod k C.length _).symm
      have s2 : (k % C.length + (j + C.length - k % C.length) % C.length) % C.length
          = (k % C.length + (j + C.length - k % C.length)) % C.length :=
        Nat.add_mod_mod _ _ _
      have s3 : k % C.length + (j + C.length - k % C.length) = j + C.length := by omega
      rw [s1, s2, s3, Nat.add_mod_right]
    exact hj ((cycVert_congr e.symm).mpr
      (hrun ((j + C.length - k % C.length) % C.length) (by rw [hLeq]; exact Nat.mod_lt _ hn)))
  refine ⟨k, L, hL1, hLlt, hrun, ?_, ?_, hcov⟩
  · intro hcon
    have hbig := hmax ⟨k, L + 1⟩ ⟨by omega, ?_, ?_⟩
    · simp only at hbig; omega
    · intro t ht
      rcases Nat.lt_or_ge t L with h | h
      · exact hrun t h
      · exact (cycVert_congr (by congr 1; omega)).mpr hcon
    · obtain ⟨t, ht, hteq⟩ := hcov
      exact ⟨t, by omega, hteq⟩
  · intro hcon
    have hbig := hmax ⟨k + (C.length - 1), L + 1⟩ ⟨by omega, ?_, ?_⟩
    · simp only at hbig; omega
    · intro t ht
      rcases Nat.eq_zero_or_pos t with rfl | hpos'
      · simpa using hcon
      · refine (cycVert_congr ?_).mpr (hrun (t - 1) (by omega))
        rw [show k + (C.length - 1) + t = (k + (t - 1)) + C.length by omega, Nat.add_mod_right]
    · obtain ⟨t, ht, hteq⟩ := hcov
      refine ⟨t + 1, by omega, ?_⟩
      rw [show k + (C.length - 1) + (t + 1) = (k + t) + C.length by omega, Nat.add_mod_right]
      exact hteq

/-- Every `Y`-complete vertex of `C` lies in a `Y`-segment, as soon as some vertex of `C` is not
`Y`-complete. -/
theorem exists_isSegment_of_cycVert (hC : IsHoleList G C) {i j : ℕ}
    (hi : CycVert G Y C i) (hj : ¬ CycVert G Y C j) :
    ∃ (S : List V), IsSegment G C Y S ∧ (∀ x : V, C[i % C.length]? = some x → x ∈ S) := by
  have hn : 0 < C.length := by have := hC.1; omega
  obtain ⟨k, L, hL1, hLlt, hrun, hnext, hprev, t, ht, hteq⟩ :=
    exists_run_of_cycVert hC hi hj
  refine ⟨(C.rotate k).take L, isSegment_of_run hC hL1 hLlt hrun hnext hprev, ?_⟩
  intro x hx
  exact (mem_arc_iff hn (by omega)).mpr ⟨t, ht, by rw [hteq]; exact hx⟩

/-! ### Parity bookkeeping -/

/-- *"An odd segment"* has an **even** number of vertices. -/
theorem odd_pathLength_iff_even_length {S : List V} (h : 1 ≤ S.length) :
    Odd (pathLength S) ↔ Even S.length := by
  rw [pathLength, Nat.odd_iff, Nat.even_iff]
  omega

end Workspace.ProofLemmas.SegmentBasics
