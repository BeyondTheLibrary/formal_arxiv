import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# Splitting the tracks of a subdivision at prescribed internal vertices

The proofs of 7.5 and 8.5 (printed pp. 36–37 and 42) say

> *"Then there is an appearance `L(H')` in `G` of some `J`-enlargement `J'`, with `L(H)` an
> induced subgraph of `L(H')`."*

Before the new branch can be added, the two attachment vertices have to become vertices of the
skeleton.  That is pure bookkeeping: if an attachment vertex is an internal vertex of one of the
tracks of the subdivision, cut that track in two at the attachment vertex and declare the
attachment vertex a new skeleton vertex.  The refined skeleton is again subdivided by the same
host graph, and it is itself a subdivision of the old skeleton, each cut edge having become a
track of length two.

This file carries out that cutting for any finite family of marked internal vertices lying on
pairwise different tracks.  `SplitData` is the family, `SplitData.graph` the refined skeleton,
`SplitData.tracks` its tracks inside the host and `SplitData.skelTracks` its tracks over the
old skeleton.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.EnlargementFromNonlocalSplitCore

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {U W : Type*}

/-! ### Reading membership in a prefix or a suffix off indices -/

theorem mem_take_iff {l : List W} {m : ℕ} {w : W} :
    w ∈ l.take m ↔ ∃ (i : ℕ) (h : i < l.length), i < m ∧ l[i] = w := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.length_take] at hj
    exact ⟨j, by omega, by omega, List.getElem_take.symm⟩
  · rintro ⟨i, hi, him, rfl⟩
    exact ⟨i, by rw [List.length_take]; omega, List.getElem_take⟩

theorem mem_drop_iff {l : List W} {m : ℕ} {w : W} :
    w ∈ l.drop m ↔ ∃ (i : ℕ) (h : i < l.length), m ≤ i ∧ l[i] = w := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [List.length_drop] at hj
    exact ⟨m + j, by omega, by omega, List.getElem_drop.symm⟩
  · rintro ⟨i, hi, him, rfl⟩
    refine ⟨i - m, by rw [List.length_drop]; omega, ?_⟩
    rw [List.getElem_drop]
    exact getElem_eq_of_index_eq l (by omega) _ _

theorem mem_interior_iff {l : List W} {w : W} :
    w ∈ trackInterior l ↔ ∃ (i : ℕ) (h : i < l.length), 1 ≤ i ∧ i + 1 < l.length ∧ l[i] = w := by
  rw [mem_trackInterior_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j + 1, by omega, by omega, by omega, rfl⟩
  · rintro ⟨i, hi, h1, h2, rfl⟩
    refine ⟨i - 1, by omega, ?_⟩
    exact getElem_eq_of_index_eq l (by omega) _ _

theorem mem_interior_take_iff {l : List W} {m : ℕ} (hm : m ≤ l.length) {w : W} :
    w ∈ trackInterior (l.take m) ↔
      ∃ (i : ℕ) (h : i < l.length), 1 ≤ i ∧ i + 1 < m ∧ l[i] = w := by
  rw [mem_interior_iff]
  simp only [List.length_take, min_eq_left hm]
  constructor
  · rintro ⟨i, hi, h1, h2, rfl⟩
    exact ⟨i, by omega, h1, h2, List.getElem_take.symm⟩
  · rintro ⟨i, hi, h1, h2, rfl⟩
    exact ⟨i, by omega, h1, h2, List.getElem_take⟩

theorem mem_interior_drop_iff {l : List W} {m : ℕ} (hm : m ≤ l.length) {w : W} :
    w ∈ trackInterior (l.drop m) ↔
      ∃ (i : ℕ) (h : i < l.length), m < i ∧ i + 1 < l.length ∧ l[i] = w := by
  rw [mem_interior_iff]
  simp only [List.length_drop]
  constructor
  · rintro ⟨i, hi, h1, h2, rfl⟩
    refine ⟨m + i, by omega, by omega, by omega, List.getElem_drop.symm⟩
  · rintro ⟨i, hi, h1, h2, rfl⟩
    refine ⟨i - m, by omega, by omega, by omega, ?_⟩
    rw [List.getElem_drop]
    exact getElem_eq_of_index_eq l (by omega) _ _


/-! ### The data of a family of marked internal vertices -/

/-- A finite family of marked vertices, the mark `t` lying strictly inside the track that the
subdivision attaches to the edge `(fst t, snd t)` of the skeleton `J`, with different marks on
different edges.  The mark is named by its position `pos t` along the track. -/
structure SplitData (J : SimpleGraph U) (T : U → U → List W) (k : ℕ) where
  /-- one end of the skeleton edge whose track carries the mark -/
  fst : Fin k → U
  /-- the other end of that skeleton edge -/
  snd : Fin k → U
  /-- the position of the mark along that track -/
  pos : Fin k → ℕ
  /-- the marked track really is a track of the subdivision -/
  adj : ∀ t, J.Adj (fst t) (snd t)
  /-- the mark is not the first vertex of the track -/
  pos_pos : ∀ t, 0 < pos t
  /-- the mark is not the last vertex of the track -/
  pos_lt : ∀ t, pos t + 1 < (T (fst t) (snd t)).length
  /-- different marks lie on different tracks -/
  edge_inj : ∀ t t', s(fst t, snd t) = s(fst t', snd t') → t = t'

namespace SplitData

variable {J : SimpleGraph U} {T : U → U → List W} {k : ℕ} (D : SplitData J T k)

/-- The track that the mark `t` cuts in two. -/
def line (t : Fin k) : List W := T (D.fst t) (D.snd t)

theorem pos_lt_line (t : Fin k) : D.pos t + 1 < (D.line t).length := D.pos_lt t

/-- The marked vertex itself. -/
def mark (t : Fin k) : W := (D.line t)[D.pos t]'(by have := D.pos_lt_line t; omega)

theorem mark_eq (t : Fin k) (h : D.pos t < (D.line t).length) :
    (D.line t)[D.pos t]'h = D.mark t := rfl

/-- The first half of the cut track: from the end `fst t` up to the mark. -/
def pre (t : Fin k) : List W := (D.line t).take (D.pos t + 1)

/-- The second half of the cut track: from the mark to the end `snd t`. -/
def post (t : Fin k) : List W := (D.line t).drop (D.pos t)

/-! ### The refined skeleton -/

/-- Adjacency of the refined skeleton: the unmarked skeleton edges survive, and a marked
skeleton edge is replaced by the two edges joining its ends to the mark. -/
def Adjacent : U ⊕ Fin k → U ⊕ Fin k → Prop
  | Sum.inl i, Sum.inl j => J.Adj i j ∧ ∀ t, s(i, j) ≠ s(D.fst t, D.snd t)
  | Sum.inl i, Sum.inr t => i = D.fst t ∨ i = D.snd t
  | Sum.inr t, Sum.inl i => i = D.fst t ∨ i = D.snd t
  | Sum.inr _, Sum.inr _ => False

/-- The refined skeleton. -/
def graph : SimpleGraph (U ⊕ Fin k) where
  Adj := D.Adjacent
  symm := by
    rintro (i | s) (j | t) h
    · exact ⟨h.1.symm, fun t hc => h.2 t (Sym2.eq_swap.trans hc)⟩
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    rintro (i | t) h
    · exact J.loopless.irrefl i h.1
    · exact h

@[simp] theorem adj_inl_inl {i j : U} :
    D.graph.Adj (Sum.inl i) (Sum.inl j) ↔ J.Adj i j ∧ ∀ t, s(i, j) ≠ s(D.fst t, D.snd t) :=
  Iff.rfl

@[simp] theorem adj_inl_inr {i : U} {t : Fin k} :
    D.graph.Adj (Sum.inl i) (Sum.inr t) ↔ i = D.fst t ∨ i = D.snd t := Iff.rfl

@[simp] theorem adj_inr_inl {i : U} {t : Fin k} :
    D.graph.Adj (Sum.inr t) (Sum.inl i) ↔ i = D.fst t ∨ i = D.snd t := Iff.rfl

@[simp] theorem not_adj_inr_inr {s t : Fin k} : ¬ D.graph.Adj (Sum.inr s) (Sum.inr t) := id

/-! ### The tracks of the refined skeleton inside the host graph -/

open scoped Classical in
/-- The tracks of the host graph over the refined skeleton. -/
noncomputable def tracks : U ⊕ Fin k → U ⊕ Fin k → List W
  | Sum.inl i, Sum.inl j => T i j
  | Sum.inl i, Sum.inr t => if i = D.fst t then D.pre t else (D.post t).reverse
  | Sum.inr t, Sum.inl i => if i = D.fst t then (D.pre t).reverse else D.post t
  | Sum.inr _, Sum.inr _ => []

@[simp] theorem tracks_inl_inl (i j : U) : D.tracks (Sum.inl i) (Sum.inl j) = T i j := rfl

@[simp] theorem tracks_inr_inr (s t : Fin k) : D.tracks (Sum.inr s) (Sum.inr t) = [] := rfl

theorem tracks_fst_mark (t : Fin k) :
    D.tracks (Sum.inl (D.fst t)) (Sum.inr t) = D.pre t := by
  simp [tracks]

theorem tracks_mark_fst (t : Fin k) :
    D.tracks (Sum.inr t) (Sum.inl (D.fst t)) = (D.pre t).reverse := by
  simp [tracks]

theorem tracks_snd_mark (t : Fin k) (h : D.snd t ≠ D.fst t) :
    D.tracks (Sum.inl (D.snd t)) (Sum.inr t) = (D.post t).reverse := by
  simp [tracks, h]

theorem tracks_mark_snd (t : Fin k) (h : D.snd t ≠ D.fst t) :
    D.tracks (Sum.inr t) (Sum.inl (D.snd t)) = D.post t := by
  simp [tracks, h]

/-- The embedding of the refined skeleton into the host graph. -/
def emb (ι : U → W) : U ⊕ Fin k → W := Sum.elim ι D.mark

@[simp] theorem emb_inl (ι : U → W) (i : U) : D.emb ι (Sum.inl i) = ι i := rfl

@[simp] theorem emb_inr (ι : U → W) (t : Fin k) : D.emb ι (Sum.inr t) = D.mark t := rfl

/-! ### The tracks of the refined skeleton over the old skeleton -/

open scoped Classical in
/-- The mark sitting on a given skeleton edge, if any. -/
noncomputable def splitIdx (x : Sym2 U) : Option (Fin k) :=
  if h : ∃ t, x = s(D.fst t, D.snd t) then some h.choose else none

theorem splitIdx_eq_some_iff {x : Sym2 U} {t : Fin k} :
    D.splitIdx x = some t ↔ x = s(D.fst t, D.snd t) := by
  classical
  unfold splitIdx
  split_ifs with h
  · constructor
    · intro hs
      have : h.choose = t := Option.some_injective _ hs
      rw [← this]; exact h.choose_spec
    · intro hx
      exact congrArg some (D.edge_inj t h.choose (hx.symm.trans h.choose_spec)).symm
  · constructor
    · intro hs; simp at hs
    · intro hx; exact absurd ⟨t, hx⟩ h

theorem splitIdx_eq_none_iff {x : Sym2 U} :
    D.splitIdx x = none ↔ ∀ t, x ≠ s(D.fst t, D.snd t) := by
  classical
  constructor
  · intro hs t hx
    rw [(D.splitIdx_eq_some_iff).mpr hx] at hs
    simp at hs
  · intro h
    cases hc : D.splitIdx x with
    | none => rfl
    | some t => exact absurd ((D.splitIdx_eq_some_iff).mp hc) (h t)

/-- The tracks of the refined skeleton over the old skeleton: an unmarked edge stays an edge,
a marked edge becomes a track of length two through the mark. -/
noncomputable def skelTracks (i j : U) : List (U ⊕ Fin k) :=
  match D.splitIdx s(i, j) with
  | some t => [Sum.inl i, Sum.inr t, Sum.inl j]
  | none => [Sum.inl i, Sum.inl j]

theorem skelTracks_of_some {i j : U} {t : Fin k} (h : D.splitIdx s(i, j) = some t) :
    D.skelTracks i j = [Sum.inl i, Sum.inr t, Sum.inl j] := by
  unfold skelTracks; rw [h]

theorem skelTracks_of_none {i j : U} (h : D.splitIdx s(i, j) = none) :
    D.skelTracks i j = [Sum.inl i, Sum.inl j] := by
  unfold skelTracks; rw [h]

end SplitData


/-! ### Prefixes and suffixes of a track are tracks -/

theorem head?_getElem {l : List W} (h : 0 < l.length) : l.head? = some (l[0]'h) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h]

theorem getLast?_getElem {l : List W} (h : 0 < l.length) :
    l.getLast? = some (l[l.length - 1]'(by omega)) := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]

theorem isTrackList_take {H : SimpleGraph W} {l : List W} (hl : IsTrackList H l) {m : ℕ}
    (hm : 0 < m) : IsTrackList H (l.take m) := by
  have hlen : 0 < l.length := List.length_pos_iff.mpr hl.1
  refine ⟨?_, hl.2.1.sublist (List.take_sublist _ _), ?_⟩
  · exact List.length_pos_iff.mp (by rw [List.length_take]; omega)
  · intro i hi
    rw [List.length_take] at hi
    have h1 : i + 1 < l.length := by omega
    have e1 : (l.take m)[i]'(by rw [List.length_take]; omega) = l[i]'(by omega) :=
      List.getElem_take
    have e2 : (l.take m)[i + 1]'(by rw [List.length_take]; omega) = l[i + 1]'h1 :=
      List.getElem_take
    rw [e1, e2]
    exact hl.2.2 i h1

theorem isTrackList_drop {H : SimpleGraph W} {l : List W} (hl : IsTrackList H l) {m : ℕ}
    (hm : m < l.length) : IsTrackList H (l.drop m) := by
  refine ⟨?_, hl.2.1.sublist (List.drop_sublist _ _), ?_⟩
  · exact List.length_pos_iff.mp (by rw [List.length_drop]; omega)
  · intro i hi
    rw [List.length_drop] at hi
    have h1 : m + i + 1 < l.length := by omega
    have e1 : (l.drop m)[i]'(by rw [List.length_drop]; omega) = l[m + i]'(by omega) :=
      List.getElem_drop
    have e2 : (l.drop m)[i + 1]'(by rw [List.length_drop]; omega) = l[m + (i + 1)]'(by omega) :=
      List.getElem_drop
    have e3 : l[m + i + 1]'h1 = l[m + (i + 1)]'(by omega) :=
      getElem_eq_of_index_eq l (by omega) _ _
    rw [e1, e2, ← e3]
    exact hl.2.2 (m + i) h1

/-! ### The eight clauses of a subdivision, on an arbitrary vertex type -/

/-- All eight clauses of `IsSubdivision J H` for a fixed witness pair `(ι, T)`. -/
structure FullWitness (J : SimpleGraph U) (H : SimpleGraph W) (ι : U → W)
    (T : U → U → List W) : Prop extends SubdivisionCompose.SubdivWitness J H ι T where
  /-- every vertex of the host is an old vertex or an internal vertex of a track -/
  cover : ∀ w : W, (∃ u : U, w = ι u) ∨ ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v)
  /-- every edge of the host is an edge of a track -/
  edges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v)

theorem exists_fullWitness {J : SimpleGraph U} {H : SimpleGraph W} (h : IsSubdivision J H) :
    ∃ (ι : U → W) (T : U → U → List W), FullWitness J H ι T := by
  obtain ⟨ι, T, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨ι, T, ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8⟩⟩

theorem isSubdivision_of_fullWitness {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W}
    {T : U → U → List W} (h : FullWitness J H ι T) : IsSubdivision J H :=
  ⟨ι, T, h.inj, h.track, h.len, h.rev, h.disj, h.new, h.cover, h.edges⟩

theorem mem_trackEdges_iff {l : List W} {e : Sym2 W} :
    e ∈ trackEdges l ↔ ∃ (i : ℕ) (h : i + 1 < l.length), e = s(l[i]'(by omega), l[i + 1]'h) :=
  Iff.rfl

theorem trackEdges_subset_edgeSet {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q) :
    trackEdges q ⊆ H.edgeSet := by
  rintro e ⟨i, hi, rfl⟩
  exact hq.2.2 i hi

/-! ### The two halves of a cut track -/

section Split

variable {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W} {k : ℕ}
  (hS : FullWitness J H ι T) (D : SplitData J T k)

theorem pre_length (t : Fin k) : (D.pre t).length = D.pos t + 1 := by
  have := D.pos_lt_line t
  simp only [SplitData.pre, List.length_take]
  omega

theorem post_length (t : Fin k) : (D.post t).length = (D.line t).length - D.pos t := by
  simp only [SplitData.post, List.length_drop]

theorem pre_getElem (t : Fin k) {i : ℕ} (h : i < (D.pre t).length) :
    (D.pre t)[i] = (D.line t)[i]'(by rw [pre_length] at h; have := D.pos_lt_line t; omega) :=
  List.getElem_take

theorem post_getElem (t : Fin k) {i : ℕ} (h : i < (D.post t).length) :
    (D.post t)[i] = (D.line t)[D.pos t + i]'(by rw [post_length] at h; omega) :=
  List.getElem_drop

theorem mem_pre_iff (t : Fin k) {w : W} : w ∈ D.pre t ↔
    ∃ (i : ℕ) (_ : i < (D.line t).length), i ≤ D.pos t ∧ (D.line t)[i] = w := by
  simp only [SplitData.pre, mem_take_iff]
  constructor
  · rintro ⟨i, hi, h1, h2⟩; exact ⟨i, hi, by omega, h2⟩
  · rintro ⟨i, hi, h1, h2⟩; exact ⟨i, hi, by omega, h2⟩

theorem mem_post_iff (t : Fin k) {w : W} : w ∈ D.post t ↔
    ∃ (i : ℕ) (_ : i < (D.line t).length), D.pos t ≤ i ∧ (D.line t)[i] = w :=
  mem_drop_iff

theorem mem_line_interior_iff (t : Fin k) {w : W} : w ∈ trackInterior (D.line t) ↔
    ∃ (i : ℕ) (_ : i < (D.line t).length), 1 ≤ i ∧ i + 1 < (D.line t).length ∧
      (D.line t)[i] = w := mem_interior_iff

theorem mem_pre_interior_iff (t : Fin k) {w : W} : w ∈ trackInterior (D.pre t) ↔
    ∃ (i : ℕ) (_ : i < (D.line t).length), 1 ≤ i ∧ i < D.pos t ∧ (D.line t)[i] = w := by
  have hp := D.pos_lt_line t
  simp only [SplitData.pre, mem_interior_take_iff (by omega : D.pos t + 1 ≤ (D.line t).length)]
  constructor
  · rintro ⟨i, hi, h1, h2, h3⟩; exact ⟨i, hi, h1, by omega, h3⟩
  · rintro ⟨i, hi, h1, h2, h3⟩; exact ⟨i, hi, h1, by omega, h3⟩

theorem mem_post_interior_iff (t : Fin k) {w : W} : w ∈ trackInterior (D.post t) ↔
    ∃ (i : ℕ) (_ : i < (D.line t).length), D.pos t < i ∧ i + 1 < (D.line t).length ∧
      (D.line t)[i] = w := by
  have hp := D.pos_lt_line t
  exact mem_interior_drop_iff (by omega : D.pos t ≤ (D.line t).length)

theorem mark_mem_line_interior (t : Fin k) : D.mark t ∈ trackInterior (D.line t) := by
  have hp := D.pos_lt_line t
  exact (mem_line_interior_iff D t).mpr ⟨D.pos t, by omega, D.pos_pos t, hp, rfl⟩

theorem pre_subset_line (t : Fin k) {w : W} (h : w ∈ D.pre t) : w ∈ D.line t := by
  obtain ⟨i, hi, -, rfl⟩ := (mem_pre_iff D t).mp h
  exact List.getElem_mem hi

theorem post_subset_line (t : Fin k) {w : W} (h : w ∈ D.post t) : w ∈ D.line t := by
  obtain ⟨i, hi, -, rfl⟩ := (mem_post_iff D t).mp h
  exact List.getElem_mem hi

theorem pre_interior_subset_line_interior (t : Fin k) {w : W}
    (h : w ∈ trackInterior (D.pre t)) : w ∈ trackInterior (D.line t) := by
  obtain ⟨i, hi, h1, h2, rfl⟩ := (mem_pre_interior_iff D t).mp h
  have hp := D.pos_lt_line t
  exact (mem_line_interior_iff D t).mpr ⟨i, hi, h1, by omega, rfl⟩

theorem post_interior_subset_line_interior (t : Fin k) {w : W}
    (h : w ∈ trackInterior (D.post t)) : w ∈ trackInterior (D.line t) := by
  obtain ⟨i, hi, h1, h2, rfl⟩ := (mem_post_interior_iff D t).mp h
  have hp := D.pos_pos t
  exact (mem_line_interior_iff D t).mpr ⟨i, hi, by omega, h2, rfl⟩

theorem trackEdges_line_subset (t : Fin k) :
    trackEdges (D.line t) ⊆ trackEdges (D.pre t) ∪ trackEdges (D.post t) := by
  have hp := D.pos_lt_line t
  rintro e ⟨i, hi, rfl⟩
  by_cases hle : i + 1 ≤ D.pos t
  · refine Or.inl ⟨i, ?_, ?_⟩
    · rw [pre_length D t]; omega
    · rw [pre_getElem D t (by rw [pre_length D t]; omega),
        pre_getElem D t (by rw [pre_length D t]; omega)]
  · refine Or.inr ⟨i - D.pos t, ?_, ?_⟩
    · rw [post_length D t]; omega
    · rw [post_getElem D t (by rw [post_length D t]; omega),
        post_getElem D t (by rw [post_length D t]; omega)]
      rw [getElem_eq_of_index_eq (D.line t) (show D.pos t + (i - D.pos t) = i by omega)
          (by omega) (by omega),
        getElem_eq_of_index_eq (D.line t) (show D.pos t + (i - D.pos t + 1) = i + 1 by omega)
          (by omega) (by omega)]

include hS

theorem line_isTrackFrom (t : Fin k) :
    IsTrackFrom H (D.line t) (ι (D.fst t)) (ι (D.snd t)) := hS.track _ _ (D.adj t)

theorem line_nodup (t : Fin k) : (D.line t).Nodup := (line_isTrackFrom hS D t).1.2.1

theorem line_index_inj {t : Fin k} {i j : ℕ} (hi : i < (D.line t).length)
    (hj : j < (D.line t).length) (h : (D.line t)[i] = (D.line t)[j]) : i = j :=
  (List.Nodup.getElem_inj_iff (line_nodup hS D t)).mp h

theorem line_head (t : Fin k) :
    (D.line t)[0]'(by have := D.pos_lt_line t; omega) = ι (D.fst t) :=
  track_head (line_isTrackFrom hS D t) _

theorem line_getLast (t : Fin k) :
    (D.line t)[(D.line t).length - 1]'(by have := D.pos_lt_line t; omega) = ι (D.snd t) :=
  Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast (line_isTrackFrom hS D t)
    (by have := D.pos_lt_line t; omega)

theorem pre_interior_notMem_post (t : Fin k) {w : W}
    (h : w ∈ trackInterior (D.pre t)) : w ∉ D.post t := by
  intro hpost
  obtain ⟨i, hi, h1, h2, hw⟩ := (mem_pre_interior_iff D t).mp h
  obtain ⟨j, hj, h3, hw2⟩ := (mem_post_iff D t).mp hpost
  have := line_index_inj hS D hi hj (hw.trans hw2.symm)
  omega

theorem post_interior_notMem_pre (t : Fin k) {w : W}
    (h : w ∈ trackInterior (D.post t)) : w ∉ D.pre t := by
  intro hpre
  obtain ⟨i, hi, h1, h2, hw⟩ := (mem_post_interior_iff D t).mp h
  obtain ⟨j, hj, h3, hw2⟩ := (mem_pre_iff D t).mp hpre
  have := line_index_inj hS D hi hj (hw.trans hw2.symm)
  omega

theorem mark_notMem_pre_interior (t : Fin k) : D.mark t ∉ trackInterior (D.pre t) := by
  intro h
  obtain ⟨i, hi, h1, h2, hw⟩ := (mem_pre_interior_iff D t).mp h
  have hp := D.pos_lt_line t
  have := line_index_inj hS D hi (show D.pos t < (D.line t).length by omega) hw
  omega

theorem mark_notMem_post_interior (t : Fin k) : D.mark t ∉ trackInterior (D.post t) := by
  intro h
  obtain ⟨i, hi, h1, h2, hw⟩ := (mem_post_interior_iff D t).mp h
  have hp := D.pos_lt_line t
  have := line_index_inj hS D hi (show D.pos t < (D.line t).length by omega) hw
  omega

theorem pre_isTrackFrom (t : Fin k) :
    IsTrackFrom H (D.pre t) (ι (D.fst t)) (D.mark t) := by
  have hp := D.pos_lt_line t
  have hlen : (D.pre t).length = D.pos t + 1 := pre_length D t
  refine ⟨isTrackList_take (line_isTrackFrom hS D t).1 (by omega), ?_, ?_⟩
  · rw [head?_getElem (by omega), pre_getElem D t (by omega)]
    exact congrArg some (line_head hS D t)
  · rw [getLast?_getElem (by omega)]
    refine congrArg some ?_
    rw [pre_getElem D t (by omega)]
    exact getElem_eq_of_index_eq (D.line t) (by omega) _ _

theorem post_isTrackFrom (t : Fin k) :
    IsTrackFrom H (D.post t) (D.mark t) (ι (D.snd t)) := by
  have hp := D.pos_lt_line t
  have hlen : (D.post t).length = (D.line t).length - D.pos t := post_length D t
  refine ⟨isTrackList_drop (line_isTrackFrom hS D t).1 (by omega), ?_, ?_⟩
  · rw [head?_getElem (by omega), post_getElem D t (by omega)]
    exact congrArg some (getElem_eq_of_index_eq (D.line t) (by omega) _ _)
  · rw [getLast?_getElem (by omega)]
    refine congrArg some ?_
    rw [post_getElem D t (by omega)]
    rw [getElem_eq_of_index_eq (D.line t) (show D.pos t + ((D.post t).length - 1)
      = (D.line t).length - 1 by omega) (by omega) (by omega)]
    exact line_getLast hS D t


end Split

/-! ### Two- and three-vertex tracks -/

theorem trackEdges_pair {A : Type*} (a b : A) : trackEdges [a, b] = {s(a, b)} := by
  ext e
  rw [mem_trackEdges_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    simp
  · rintro rfl
    exact ⟨0, by simp, by simp⟩

theorem trackEdges_triple {A : Type*} (a b c : A) :
    trackEdges [a, b, c] = {s(a, b), s(b, c)} := by
  ext e
  rw [mem_trackEdges_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_cons, List.length_nil] at hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨1, by simp, by simp⟩

theorem trackInterior_pair {A : Type*} (a b : A) : trackInterior [a, b] = [] := by
  simp [trackInterior]

theorem trackInterior_triple {A : Type*} (a b c : A) : trackInterior [a, b, c] = [b] := by
  simp [trackInterior]

theorem isTrackFrom_pair {A : Type*} {G : SimpleGraph A} {a b : A} (h : G.Adj a b) :
    IsTrackFrom G [a, b] a b := by
  refine ⟨⟨by simp, by simp [h.ne], ?_⟩, by simp, by simp⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  obtain rfl : i = 0 := by omega
  simpa using h

theorem isTrackFrom_triple {A : Type*} {G : SimpleGraph A} {a b c : A} (h1 : G.Adj a b)
    (h2 : G.Adj b c) (hac : a ≠ c) : IsTrackFrom G [a, b, c] a c := by
  refine ⟨⟨by simp, by simp [h1.ne, h2.ne, hac], ?_⟩, by simp, by simp⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · simpa using h1
  · simpa using h2

/-! ### The refined skeleton is a subdivision of the old skeleton

Every unmarked edge survives, and every marked edge becomes a track of length two through its
mark. -/

section Skel

variable {J : SimpleGraph U} {T : U → U → List W} {k : ℕ} (D : SplitData J T k)

theorem splitIdx_self (t : Fin k) : D.splitIdx s(D.fst t, D.snd t) = some t :=
  (D.splitIdx_eq_some_iff).mpr rfl

theorem ends_of_splitIdx {i j : U} {t : Fin k} (h : D.splitIdx s(i, j) = some t) :
    (i = D.fst t ∧ j = D.snd t) ∨ (i = D.snd t ∧ j = D.fst t) :=
  Sym2.eq_iff.mp ((D.splitIdx_eq_some_iff).mp h)

theorem skelTracks_isTrackFrom {i j : U} (hij : J.Adj i j) :
    IsTrackFrom D.graph (D.skelTracks i j) (Sum.inl i) (Sum.inl j) := by
  cases hc : D.splitIdx s(i, j) with
  | none =>
    rw [D.skelTracks_of_none hc]
    exact isTrackFrom_pair ⟨hij, (D.splitIdx_eq_none_iff).mp hc⟩
  | some t =>
    rw [D.skelTracks_of_some hc]
    refine isTrackFrom_triple ?_ ?_ (by simpa using hij.ne)
    · rcases ends_of_splitIdx D hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rcases ends_of_splitIdx D hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl rfl

theorem mem_skelTracks_interior {i j : U} {y : U ⊕ Fin k}
    (hy : y ∈ trackInterior (D.skelTracks i j)) :
    ∃ t, y = Sum.inr t ∧ D.splitIdx s(i, j) = some t := by
  cases hc : D.splitIdx s(i, j) with
  | none =>
    rw [D.skelTracks_of_none hc, trackInterior_pair] at hy
    exact absurd hy (by simp)
  | some t =>
    rw [D.skelTracks_of_some hc, trackInterior_triple] at hy
    exact ⟨t, by simpa using hy, rfl⟩

theorem skelWitness : FullWitness J D.graph Sum.inl D.skelTracks := by
  refine ⟨⟨Sum.inl_injective, fun i j hij => skelTracks_isTrackFrom D hij, ?_, ?_, ?_, ?_⟩,
    ?_, ?_⟩
  · intro i j hij
    cases hc : D.splitIdx s(i, j) with
    | none => rw [D.skelTracks_of_none hc]; simp [trackLength]
    | some t => rw [D.skelTracks_of_some hc]; simp [trackLength]
  · intro i j hij
    have hsw : s(j, i) = s(i, j) := Sym2.eq_swap
    cases hc : D.splitIdx s(i, j) with
    | none =>
      rw [D.skelTracks_of_none hc, D.skelTracks_of_none (by rw [hsw]; exact hc)]
      simp
    | some t =>
      rw [D.skelTracks_of_some hc, D.skelTracks_of_some (by rw [hsw]; exact hc)]
      simp
  · intro i j i' j' hij hi'j' hne y hy hmem
    obtain ⟨t, rfl, hc⟩ := mem_skelTracks_interior D hy
    cases hc' : D.splitIdx s(i', j') with
    | none => rw [D.skelTracks_of_none hc'] at hmem; simp at hmem
    | some t' =>
      rw [D.skelTracks_of_some hc'] at hmem
      have htt : t = t' := by simpa using hmem
      subst htt
      exact hne (((D.splitIdx_eq_some_iff).mp hc).trans
        ((D.splitIdx_eq_some_iff).mp hc').symm)
  · intro i j hij y hy
    obtain ⟨t, rfl, -⟩ := mem_skelTracks_interior D hy
    rintro ⟨i', hi'⟩
    simp at hi'
  · rintro (i | t)
    · exact Or.inl ⟨i, rfl⟩
    · refine Or.inr ⟨D.fst t, D.snd t, D.adj t, ?_⟩
      rw [D.skelTracks_of_some (splitIdx_self D t), trackInterior_triple]
      simp
  · ext e
    induction e using Sym2.ind with
    | _ y z =>
      constructor
      · intro he
        have hadj : D.graph.Adj y z := he
        simp only [Set.mem_iUnion]
        match y, z, hadj with
        | Sum.inl i, Sum.inl j, hadj =>
          refine ⟨i, j, hadj.1, ?_⟩
          rw [D.skelTracks_of_none ((D.splitIdx_eq_none_iff).mpr hadj.2), trackEdges_pair]
          rfl
        | Sum.inl i, Sum.inr t, hadj =>
          refine ⟨D.fst t, D.snd t, D.adj t, ?_⟩
          rw [D.skelTracks_of_some (splitIdx_self D t), trackEdges_triple]
          rcases hadj with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Sym2.eq_swap)
        | Sum.inr t, Sum.inl i, hadj =>
          refine ⟨D.fst t, D.snd t, D.adj t, ?_⟩
          rw [D.skelTracks_of_some (splitIdx_self D t), trackEdges_triple]
          rcases hadj with rfl | rfl
          · exact Or.inl (Sym2.eq_swap)
          · exact Or.inr rfl
        | Sum.inr t, Sum.inr t', hadj => exact absurd hadj (D.not_adj_inr_inr)
      · intro he
        simp only [Set.mem_iUnion] at he
        obtain ⟨i, j, hij, hmem⟩ := he
        exact trackEdges_subset_edgeSet (skelTracks_isTrackFrom D hij).1 hmem

end Skel

/-! ### The host graph subdivides the refined skeleton -/

section Refine

variable {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W} {k : ℕ}
  (hS : FullWitness J H ι T) (D : SplitData J T k)

theorem mem_of_eq_or_reverse {L M : List W} (h : M = L ∨ M = L.reverse) {w : W} :
    w ∈ M ↔ w ∈ L := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact List.mem_reverse

theorem interior_mem_of_eq_or_reverse {L M : List W} (h : M = L ∨ M = L.reverse) {w : W} :
    w ∈ trackInterior M ↔ w ∈ trackInterior L := by
  rcases h with rfl | rfl
  · exact Iff.rfl
  · exact Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse

theorem half_subset_line {t : Fin k} {w : W} (h : w ∈ D.pre t ∨ w ∈ D.post t) :
    w ∈ D.line t := by
  rcases h with h | h
  · exact pre_subset_line D t h
  · exact post_subset_line D t h

theorem half_interior_subset_line_interior {t : Fin k} {w : W}
    (h : w ∈ trackInterior (D.pre t) ∨ w ∈ trackInterior (D.post t)) :
    w ∈ trackInterior (D.line t) := by
  rcases h with h | h
  · exact pre_interior_subset_line_interior D t h
  · exact post_interior_subset_line_interior D t h

theorem tracks_classify {y z : U ⊕ Fin k} (h : D.graph.Adj y z) :
    (∃ i j : U, J.Adj i j ∧ (∀ t, s(i, j) ≠ s(D.fst t, D.snd t)) ∧
        s(y, z) = s(Sum.inl i, Sum.inl j) ∧ D.tracks y z = T i j) ∨
    (∃ t : Fin k, s(y, z) = s(Sum.inl (D.fst t), Sum.inr t) ∧
        (D.tracks y z = D.pre t ∨ D.tracks y z = (D.pre t).reverse)) ∨
    (∃ t : Fin k, s(y, z) = s(Sum.inl (D.snd t), Sum.inr t) ∧
        (D.tracks y z = D.post t ∨ D.tracks y z = (D.post t).reverse)) := by
  match y, z, h with
  | Sum.inl i, Sum.inl j, h => exact Or.inl ⟨i, j, h.1, h.2, rfl, rfl⟩
  | Sum.inl i, Sum.inr t, h =>
    rcases h with rfl | rfl
    · exact Or.inr (Or.inl ⟨t, rfl, Or.inl (D.tracks_fst_mark t)⟩)
    · exact Or.inr (Or.inr ⟨t, rfl, Or.inr (D.tracks_snd_mark t (D.adj t).ne')⟩)
  | Sum.inr t, Sum.inl i, h =>
    rcases h with rfl | rfl
    · exact Or.inr (Or.inl ⟨t, Sym2.eq_swap, Or.inr (D.tracks_mark_fst t)⟩)
    · exact Or.inr (Or.inr ⟨t, Sym2.eq_swap, Or.inl (D.tracks_mark_snd t (D.adj t).ne')⟩)
  | Sum.inr t, Sum.inr t', h => exact absurd h (D.not_adj_inr_inr)

include hS

theorem mark_notMem_range (t : Fin k) : D.mark t ∉ Set.range ι :=
  hS.new _ _ (D.adj t) _ (mark_mem_line_interior D t)

theorem line_interior_notMem_unsplit {i j : U} (hij : J.Adj i j)
    (hns : ∀ t, s(i, j) ≠ s(D.fst t, D.snd t)) (t : Fin k) {w : W}
    (hw : w ∈ trackInterior (D.line t)) : w ∉ T i j :=
  hS.disj _ _ i j (D.adj t) hij (fun h => hns t h.symm) w hw

theorem unsplit_interior_notMem_line {i j : U} (hij : J.Adj i j)
    (hns : ∀ t, s(i, j) ≠ s(D.fst t, D.snd t)) (t : Fin k) {w : W}
    (hw : w ∈ trackInterior (T i j)) : w ∉ D.line t :=
  hS.disj i j _ _ hij (D.adj t) (hns t) w hw

theorem line_interior_notMem_line {a b : Fin k} (hab : a ≠ b) {w : W}
    (hw : w ∈ trackInterior (D.line a)) : w ∉ D.line b :=
  hS.disj _ _ _ _ (D.adj a) (D.adj b) (fun h => hab (D.edge_inj a b h)) w hw

theorem mark_injective : Function.Injective D.mark := by
  intro a b hab
  by_contra hne
  refine line_interior_notMem_line hS D hne (mark_mem_line_interior D a) ?_
  rw [hab]
  exact Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior
    (mark_mem_line_interior D b)

theorem emb_injective : Function.Injective (D.emb ι) := by
  rintro (i | a) (j | b) h
  · exact congrArg Sum.inl (hS.inj h)
  · exact absurd ⟨i, h⟩ (mark_notMem_range hS D b)
  · exact absurd ⟨j, h.symm⟩ (mark_notMem_range hS D a)
  · exact congrArg Sum.inr (mark_injective hS D h)

theorem tracks_isTrackFrom {y z : U ⊕ Fin k} (h : D.graph.Adj y z) :
    IsTrackFrom H (D.tracks y z) (D.emb ι y) (D.emb ι z) := by
  match y, z, h with
  | Sum.inl i, Sum.inl j, h => exact hS.track i j h.1
  | Sum.inl i, Sum.inr t, h =>
    rcases h with rfl | rfl
    · rw [D.tracks_fst_mark t]; exact pre_isTrackFrom hS D t
    · rw [D.tracks_snd_mark t (D.adj t).ne']
      exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse (post_isTrackFrom hS D t)
  | Sum.inr t, Sum.inl i, h =>
    rcases h with rfl | rfl
    · rw [D.tracks_mark_fst t]
      exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse (pre_isTrackFrom hS D t)
    · rw [D.tracks_mark_snd t (D.adj t).ne']; exact post_isTrackFrom hS D t
  | Sum.inr t, Sum.inr t', h => exact absurd h (D.not_adj_inr_inr)

omit hS in
theorem sym2_inl_eq {i j i' j' : U} (h : s(i, j) = s(i', j')) :
    s(Sum.inl i, Sum.inl j) = (s(Sum.inl i', Sum.inl j') : Sym2 (U ⊕ Fin k)) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact Sym2.eq_swap

theorem tracks_len (y z : U ⊕ Fin k) (h : D.graph.Adj y z) :
    1 ≤ trackLength (D.tracks y z) := by
  have hpp := D.pos_pos
  match y, z, h with
  | Sum.inl i, Sum.inl j, h => exact hS.len i j h.1
  | Sum.inl i, Sum.inr t, h =>
    rcases h with rfl | rfl
    · rw [D.tracks_fst_mark t]
      simp only [trackLength, pre_length D t]
      have := hpp t; omega
    · rw [D.tracks_snd_mark t (D.adj t).ne']
      simp only [trackLength, List.length_reverse, post_length D t]
      have := D.pos_lt_line t; omega
  | Sum.inr t, Sum.inl i, h =>
    rcases h with rfl | rfl
    · rw [D.tracks_mark_fst t]
      simp only [trackLength, List.length_reverse, pre_length D t]
      have := hpp t; omega
    · rw [D.tracks_mark_snd t (D.adj t).ne']
      simp only [trackLength, post_length D t]
      have := D.pos_lt_line t; omega
  | Sum.inr t, Sum.inr t', h => exact absurd h (D.not_adj_inr_inr)

theorem tracks_rev (y z : U ⊕ Fin k) (h : D.graph.Adj y z) :
    D.tracks z y = (D.tracks y z).reverse := by
  match y, z, h with
  | Sum.inl i, Sum.inl j, h => exact hS.rev i j h.1
  | Sum.inl i, Sum.inr t, h =>
    rcases h with rfl | rfl
    · rw [D.tracks_fst_mark t, D.tracks_mark_fst t]
    · rw [D.tracks_snd_mark t (D.adj t).ne', D.tracks_mark_snd t (D.adj t).ne',
        List.reverse_reverse]
  | Sum.inr t, Sum.inl i, h =>
    rcases h with rfl | rfl
    · rw [D.tracks_fst_mark t, D.tracks_mark_fst t, List.reverse_reverse]
    · rw [D.tracks_snd_mark t (D.adj t).ne', D.tracks_mark_snd t (D.adj t).ne']
  | Sum.inr t, Sum.inr t', h => exact absurd h (D.not_adj_inr_inr)

theorem tracks_disj (y z y' z' : U ⊕ Fin k) (h : D.graph.Adj y z) (h' : D.graph.Adj y' z')
    (hne : s(y, z) ≠ s(y', z')) (w : W) (hw : w ∈ trackInterior (D.tracks y z)) :
    w ∉ D.tracks y' z' := by
  intro hmem
  rcases tracks_classify D h with ⟨i, j, hij, hns, hs, ht⟩ | ⟨t, hs, ht⟩ | ⟨t, hs, ht⟩ <;>
    rcases tracks_classify D h' with ⟨i', j', hij', hns', hs', ht'⟩ | ⟨t', hs', ht'⟩ |
      ⟨t', hs', ht'⟩
  -- unmarked against unmarked
  · rw [ht] at hw
    rw [ht'] at hmem
    exact hS.disj i j i' j' hij hij'
      (fun hq => hne (hs.trans ((sym2_inl_eq hq).trans hs'.symm))) w hw hmem
  -- unmarked against a first half
  · exact unsplit_interior_notMem_line hS D hij hns t' (ht ▸ hw)
      (half_subset_line D (Or.inl ((mem_of_eq_or_reverse ht').mp hmem)))
  -- unmarked against a second half
  · exact unsplit_interior_notMem_line hS D hij hns t' (ht ▸ hw)
      (half_subset_line D (Or.inr ((mem_of_eq_or_reverse ht').mp hmem)))
  -- a first half against unmarked
  · exact line_interior_notMem_unsplit hS D hij' hns' t
      (half_interior_subset_line_interior D
        (Or.inl ((interior_mem_of_eq_or_reverse ht).mp hw))) (ht' ▸ hmem)
  -- a first half against a first half
  · by_cases htt : t = t'
    · subst htt
      exact hne (hs.trans hs'.symm)
    · exact line_interior_notMem_line hS D htt
        (half_interior_subset_line_interior D
          (Or.inl ((interior_mem_of_eq_or_reverse ht).mp hw)))
        (half_subset_line D (Or.inl ((mem_of_eq_or_reverse ht').mp hmem)))
  -- a first half against a second half
  · by_cases htt : t = t'
    · subst htt
      exact pre_interior_notMem_post hS D t ((interior_mem_of_eq_or_reverse ht).mp hw)
        ((mem_of_eq_or_reverse ht').mp hmem)
    · exact line_interior_notMem_line hS D htt
        (half_interior_subset_line_interior D
          (Or.inl ((interior_mem_of_eq_or_reverse ht).mp hw)))
        (half_subset_line D (Or.inr ((mem_of_eq_or_reverse ht').mp hmem)))
  -- a second half against unmarked
  · exact line_interior_notMem_unsplit hS D hij' hns' t
      (half_interior_subset_line_interior D
        (Or.inr ((interior_mem_of_eq_or_reverse ht).mp hw))) (ht' ▸ hmem)
  -- a second half against a first half
  · by_cases htt : t = t'
    · subst htt
      exact post_interior_notMem_pre hS D t ((interior_mem_of_eq_or_reverse ht).mp hw)
        ((mem_of_eq_or_reverse ht').mp hmem)
    · exact line_interior_notMem_line hS D htt
        (half_interior_subset_line_interior D
          (Or.inr ((interior_mem_of_eq_or_reverse ht).mp hw)))
        (half_subset_line D (Or.inl ((mem_of_eq_or_reverse ht').mp hmem)))
  -- a second half against a second half
  · by_cases htt : t = t'
    · subst htt
      exact hne (hs.trans hs'.symm)
    · exact line_interior_notMem_line hS D htt
        (half_interior_subset_line_interior D
          (Or.inr ((interior_mem_of_eq_or_reverse ht).mp hw)))
        (half_subset_line D (Or.inr ((mem_of_eq_or_reverse ht').mp hmem)))

theorem tracks_new (y z : U ⊕ Fin k) (h : D.graph.Adj y z) (w : W)
    (hw : w ∈ trackInterior (D.tracks y z)) : w ∉ Set.range (D.emb ι) := by
  rintro ⟨x, hx⟩
  have hmarkmem : ∀ a : Fin k, D.mark a ∈ D.line a := fun a =>
    Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior
      (mark_mem_line_interior D a)
  rcases tracks_classify D h with ⟨i, j, hij, hns, hs, ht⟩ | ⟨t, hs, ht⟩ | ⟨t, hs, ht⟩
  · rw [ht] at hw
    match x, hx with
    | Sum.inl i', hx => exact hS.new i j hij w hw ⟨i', hx⟩
    | Sum.inr a, hx =>
      exact unsplit_interior_notMem_line hS D hij hns a hw (hx ▸ hmarkmem a)
  · have hw' : w ∈ trackInterior (D.line t) :=
      half_interior_subset_line_interior D (Or.inl ((interior_mem_of_eq_or_reverse ht).mp hw))
    match x, hx with
    | Sum.inl i', hx => exact hS.new _ _ (D.adj t) w hw' ⟨i', hx⟩
    | Sum.inr a, hx =>
      by_cases hat : a = t
      · subst hat
        refine mark_notMem_pre_interior hS D a ?_
        have hx' : D.mark a = w := hx
        rw [hx']
        exact (interior_mem_of_eq_or_reverse ht).mp hw
      · exact line_interior_notMem_line hS D (fun hq => hat hq.symm) hw' (hx ▸ hmarkmem a)
  · have hw' : w ∈ trackInterior (D.line t) :=
      half_interior_subset_line_interior D (Or.inr ((interior_mem_of_eq_or_reverse ht).mp hw))
    match x, hx with
    | Sum.inl i', hx => exact hS.new _ _ (D.adj t) w hw' ⟨i', hx⟩
    | Sum.inr a, hx =>
      by_cases hat : a = t
      · subst hat
        refine mark_notMem_post_interior hS D a ?_
        have hx' : D.mark a = w := hx
        rw [hx']
        exact (interior_mem_of_eq_or_reverse ht).mp hw
      · exact line_interior_notMem_line hS D (fun hq => hat hq.symm) hw' (hx ▸ hmarkmem a)

theorem split_edge_interior {i j : U} {t : Fin k} (h : s(i, j) = s(D.fst t, D.snd t))
    {w : W} (hw : w ∈ trackInterior (T i j)) : w ∈ trackInterior (D.line t) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hw
  · rw [hS.rev _ _ (D.adj t)] at hw
    exact Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse.mp hw

theorem split_edge_edges {i j : U} {t : Fin k} (h : s(i, j) = s(D.fst t, D.snd t)) :
    trackEdges (T i j) ⊆ trackEdges (D.line t) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact le_rfl
  · rw [hS.rev _ _ (D.adj t), trackEdges_reverse]
    exact subset_rfl

theorem tracks_cover (w : W) : (∃ y, w = D.emb ι y) ∨
    ∃ y z, D.graph.Adj y z ∧ w ∈ trackInterior (D.tracks y z) := by
  rcases hS.cover w with ⟨i, rfl⟩ | ⟨i, j, hij, hw⟩
  · exact Or.inl ⟨Sum.inl i, rfl⟩
  · by_cases hns : ∀ t, s(i, j) ≠ s(D.fst t, D.snd t)
    · exact Or.inr ⟨Sum.inl i, Sum.inl j, ⟨hij, hns⟩, hw⟩
    · push_neg at hns
      obtain ⟨t, ht⟩ := hns
      have hw' : w ∈ trackInterior (D.line t) := split_edge_interior hS D ht hw
      obtain ⟨m, hm, h1, h2, hmw⟩ := (mem_line_interior_iff D t).mp hw'
      rcases lt_trichotomy m (D.pos t) with hlt | heq | hgt
      · refine Or.inr ⟨Sum.inl (D.fst t), Sum.inr t, Or.inl rfl, ?_⟩
        rw [D.tracks_fst_mark t]
        exact (mem_pre_interior_iff D t).mpr ⟨m, hm, h1, hlt, hmw⟩
      · subst heq
        exact Or.inl ⟨Sum.inr t, hmw.symm⟩
      · refine Or.inr ⟨Sum.inr t, Sum.inl (D.snd t), Or.inr rfl, ?_⟩
        rw [D.tracks_mark_snd t (D.adj t).ne']
        exact (mem_post_interior_iff D t).mpr ⟨m, hm, hgt, h2, hmw⟩

theorem tracks_edgeSet : H.edgeSet =
    ⋃ (y : U ⊕ Fin k) (z : U ⊕ Fin k) (_ : D.graph.Adj y z), trackEdges (D.tracks y z) := by
  ext e
  constructor
  · intro he
    rw [hS.edges] at he
    simp only [Set.mem_iUnion] at he ⊢
    obtain ⟨i, j, hij, hme⟩ := he
    by_cases hns : ∀ t, s(i, j) ≠ s(D.fst t, D.snd t)
    · exact ⟨Sum.inl i, Sum.inl j, ⟨hij, hns⟩, hme⟩
    · push_neg at hns
      obtain ⟨t, ht⟩ := hns
      rcases trackEdges_line_subset D t (split_edge_edges hS D ht hme) with hh | hh
      · exact ⟨Sum.inl (D.fst t), Sum.inr t, Or.inl rfl,
          by rw [D.tracks_fst_mark t]; exact hh⟩
      · exact ⟨Sum.inr t, Sum.inl (D.snd t), Or.inr rfl,
          by rw [D.tracks_mark_snd t (D.adj t).ne']; exact hh⟩
  · intro he
    simp only [Set.mem_iUnion] at he
    obtain ⟨y, z, hyz, hme⟩ := he
    exact trackEdges_subset_edgeSet (tracks_isTrackFrom hS D hyz).1 hme

/-- **The host graph is a subdivision of the refined skeleton.** -/
theorem splitWitness : FullWitness D.graph H (D.emb ι) D.tracks :=
  ⟨⟨emb_injective hS D, fun y z h => tracks_isTrackFrom hS D h, tracks_len hS D,
      tracks_rev hS D, tracks_disj hS D, tracks_new hS D⟩,
    tracks_cover hS D, tracks_edgeSet hS D⟩

end Refine


end Workspace.ProofLemmas.EnlargementFromNonlocalSplitCore



