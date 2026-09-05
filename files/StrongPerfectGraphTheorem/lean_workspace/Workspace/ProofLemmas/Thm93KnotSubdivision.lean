import Workspace.ProofLemmas.Thm93KnotChains
import Workspace.ProofLemmas.Thm93KnotHost
import Workspace.ProofLemmas.Thm82BranchDelta

/-!
# The host graph is a bipartite subdivision of `K₄`

PAPER (9.3, printed p. 48): *"Then `K` is a degenerate appearance of `K₄` in `G`."*

The host graph of `Thm93KnotHost` is the four-cycle `c₁c₂c₃c₄` together with two extra tracks,
one from `c₁` to `c₃` with `m` edges and one from `c₂` to `c₄` with `n` edges.  So it is the
subdivision of `K₄` in which the four edges `c₁c₂`, `c₂c₃`, `c₃c₄`, `c₄c₁` are not subdivided
and the two remaining edges `c₁c₃`, `c₂c₄` are subdivided into those tracks.  It is bipartite
because `m` and `n` are even.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93KnotSubdivision

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm93KnotModel
open Workspace.ProofLemmas.Thm93KnotHost
open Workspace.ProofLemmas.Thm93KnotChains

variable {m n : ℕ}

/-! ### Generalities on tracks -/

theorem trackEdges_pair {α : Type*} (x y : α) : trackEdges [x, y] = {s(x, y)} := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_cons, List.length_nil] at hi
    obtain rfl : i = 0 := by omega
    simp
  · rintro rfl
    exact ⟨0, by simp, rfl⟩

theorem trackEdges_subset_edgeSet {α : Type*} {G : SimpleGraph α} {q : List α}
    (hq : IsTrackList G q) : trackEdges q ⊆ G.edgeSet := by
  rintro e ⟨i, hi, rfl⟩
  exact hq.2.2 i hi

/-! ### The two chains -/

theorem chainA_isTrackList : IsTrackList (host m n) (chainA m n) := by
  refine ofFn_isTrackList _ (fun a b h => by simpa using h) ?_
  intro i
  simp [Fin.val_succ]

theorem chainB_isTrackList : IsTrackList (host m n) (chainB m n) := by
  refine ofFn_isTrackList _ (fun a b h => by simpa using h) ?_
  intro i
  simp [Fin.val_succ]

theorem chainA_isTrackFrom : IsTrackFrom (host m n) (chainA m n) (c1 m n) (c3 m n) :=
  ⟨chainA_isTrackList, ofFn_head? _, ofFn_getLast? _⟩

theorem chainB_isTrackFrom : IsTrackFrom (host m n) (chainB m n) (c2 m n) (c4 m n) :=
  ⟨chainB_isTrackList, ofFn_head? _, ofFn_getLast? _⟩

theorem mem_chainA {w : Host m n} : w ∈ chainA m n ↔ ∃ i : Fin (m + 1), Sum.inl i = w :=
  mem_ofFn

theorem mem_chainB {w : Host m n} : w ∈ chainB m n ↔ ∃ i : Fin (n + 1), Sum.inr i = w :=
  mem_ofFn

theorem mem_trackEdges_chainA {e : Sym2 (Host m n)} :
    e ∈ trackEdges (chainA m n) ↔
      ∃ i : Fin m, e = s((Sum.inl i.castSucc : Host m n), Sum.inl i.succ) :=
  mem_trackEdges_ofFn

theorem mem_trackEdges_chainB {e : Sym2 (Host m n)} :
    e ∈ trackEdges (chainB m n) ↔
      ∃ i : Fin n, e = s((Sum.inr i.castSucc : Host m n), Sum.inr i.succ) :=
  mem_trackEdges_ofFn

theorem mem_trackInterior_chainA {w : Host m n} :
    w ∈ trackInterior (chainA m n) ↔
      ∃ i : Fin (m + 1), 0 < i.val ∧ i.val < m ∧ w = Sum.inl i :=
  mem_trackInterior_ofFn

theorem mem_trackInterior_chainB {w : Host m n} :
    w ∈ trackInterior (chainB m n) ↔
      ∃ i : Fin (n + 1), 0 < i.val ∧ i.val < n ∧ w = Sum.inr i :=
  mem_trackInterior_ofFn


/-! ### The subdivision data -/

/-- The four vertices of `K₄`, placed at the four corners of the four-cycle. -/
def corner (m n : ℕ) : Fin 4 → Host m n := ![c1 m n, c2 m n, c3 m n, c4 m n]

/-- The track of the host graph subdividing an edge of `K₄`.  The edges `c₁c₃` and `c₂c₄` are
subdivided into the two chains; the other four edges are not subdivided. -/
def track (m n : ℕ) (u v : Fin 4) : List (Host m n) :=
  if u.val = 0 ∧ v.val = 2 then chainA m n
  else if u.val = 2 ∧ v.val = 0 then (chainA m n).reverse
  else if u.val = 1 ∧ v.val = 3 then chainB m n
  else if u.val = 3 ∧ v.val = 1 then (chainB m n).reverse
  else [corner m n u, corner m n v]

theorem isTrackFrom_pair {α : Type*} {G : SimpleGraph α} {x y : α} (h : G.Adj x y) :
    IsTrackFrom G [x, y] x y := by
  refine ⟨⟨by simp, by simp [h.ne], ?_⟩, rfl, rfl⟩
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  obtain rfl : i = 0 := by omega
  simpa using h

theorem corner_injective (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Function.Injective (corner m n) := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp_all [corner, c1, c2, c3, c4, Fin.ext_iff] <;> omega

theorem corner_adj (hm : 2 ≤ m) (hn : 2 ≤ n) (u v : Fin 4)
    (h : ¬ (u.val = 0 ∧ v.val = 2)) (h2 : ¬ (u.val = 2 ∧ v.val = 0))
    (h3 : ¬ (u.val = 1 ∧ v.val = 3)) (h4 : ¬ (u.val = 3 ∧ v.val = 1)) (huv : u ≠ v) :
    (host m n).Adj (corner m n u) (corner m n v) := by
  fin_cases u <;> fin_cases v <;>
    simp_all [corner, c1, c2, c3, c4, Fin.ext_iff]


@[simp] theorem track_02 (m n : ℕ) : track m n 0 2 = chainA m n := by simp [track]

@[simp] theorem track_20 (m n : ℕ) : track m n 2 0 = (chainA m n).reverse := by
  simp [track]

@[simp] theorem track_13 (m n : ℕ) : track m n 1 3 = chainB m n := by simp [track]

@[simp] theorem track_31 (m n : ℕ) : track m n 3 1 = (chainB m n).reverse := by
  simp [track]

theorem track_cross (m n : ℕ) (u v : Fin 4)
    (h : ¬ (u.val = 0 ∧ v.val = 2)) (h2 : ¬ (u.val = 2 ∧ v.val = 0))
    (h3 : ¬ (u.val = 1 ∧ v.val = 3)) (h4 : ¬ (u.val = 3 ∧ v.val = 1)) :
    track m n u v = [corner m n u, corner m n v] := by
  simp only [track]
  rw [if_neg h, if_neg h2, if_neg h3, if_neg h4]


@[simp] theorem chainA_length (m n : ℕ) : (chainA m n).length = m + 1 := by simp [chainA]

@[simp] theorem chainB_length (m n : ℕ) : (chainB m n).length = n + 1 := by simp [chainB]

@[simp] theorem corner_zero (m n : ℕ) : corner m n 0 = c1 m n := rfl
@[simp] theorem corner_one (m n : ℕ) : corner m n 1 = c2 m n := rfl
@[simp] theorem corner_two (m n : ℕ) : corner m n 2 = c3 m n := rfl
@[simp] theorem corner_three (m n : ℕ) : corner m n 3 = c4 m n := rfl

/-- Either the pair of `K₄`-vertices is one of the two subdivided edges, or its track is the
single edge joining the two corners. -/
theorem track_cases (hm : 2 ≤ m) (hn : 2 ≤ n) (u v : Fin 4) :
    (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) ∨
      (track m n u v = [corner m n u, corner m n v] ∧
        track m n v u = [corner m n v, corner m n u] ∧
        (u ≠ v → (host m n).Adj (corner m n u) (corner m n v))) := by
  by_cases h1 : u.val = 0 ∧ v.val = 2
  · exact Or.inl ⟨Fin.ext (by simpa using h1.1), Fin.ext (by simpa using h1.2)⟩
  by_cases h2 : u.val = 2 ∧ v.val = 0
  · exact Or.inr (Or.inl ⟨Fin.ext (by simpa using h2.1), Fin.ext (by simpa using h2.2)⟩)
  by_cases h3 : u.val = 1 ∧ v.val = 3
  · exact Or.inr (Or.inr (Or.inl ⟨Fin.ext (by simpa using h3.1), Fin.ext (by simpa using h3.2)⟩))
  by_cases h4 : u.val = 3 ∧ v.val = 1
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Fin.ext (by simpa using h4.1), Fin.ext (by simpa using h4.2)⟩)))
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨track_cross m n u v h1 h2 h3 h4,
    track_cross m n v u (fun h => h2 ⟨h.2, h.1⟩) (fun h => h1 ⟨h.2, h.1⟩)
      (fun h => h4 ⟨h.2, h.1⟩) (fun h => h3 ⟨h.2, h.1⟩), ?_⟩)))
  intro huv
  exact corner_adj hm hn u v h1 h2 h3 h4 huv

theorem track_isTrackFrom (hm : 2 ≤ m) (hn : 2 ≤ n) (u v : Fin 4) (huv : u ≠ v) :
    IsTrackFrom (host m n) (track m n u v) (corner m n u) (corner m n v) := by
  rcases track_cases hm hn u v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨he, -, hadj⟩
  · rw [track_02, corner_zero, corner_two]; exact chainA_isTrackFrom
  · rw [track_20, corner_zero, corner_two]
    exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse chainA_isTrackFrom
  · rw [track_13, corner_one, corner_three]; exact chainB_isTrackFrom
  · rw [track_31, corner_one, corner_three]
    exact Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse chainB_isTrackFrom
  · rw [he]; exact isTrackFrom_pair (hadj huv)

/-! ### What can lie on a track other than a given one -/

theorem mem_track_of_ne_A (hm : 2 ≤ m) (hn : 2 ≤ n) {u v : Fin 4}
    (hne : s(u, v) ≠ s((0 : Fin 4), 2)) {w : Host m n} (hw : w ∈ track m n u v) :
    w ∈ chainB m n ∨ w ∈ Set.range (corner m n) := by
  rcases track_cases hm hn u v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨he, -, -⟩
  · exact absurd rfl hne
  · exact absurd (Sym2.eq_swap) hne
  · rw [track_13] at hw; exact Or.inl hw
  · rw [track_31, List.mem_reverse] at hw; exact Or.inl hw
  · rw [he] at hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact Or.inr ⟨u, rfl⟩
    · rcases List.mem_cons.mp hw' with rfl | hw'' 
      · exact Or.inr ⟨v, rfl⟩
      · exact absurd hw'' (by simp)

theorem mem_track_of_ne_B (hm : 2 ≤ m) (hn : 2 ≤ n) {u v : Fin 4}
    (hne : s(u, v) ≠ s((1 : Fin 4), 3)) {w : Host m n} (hw : w ∈ track m n u v) :
    w ∈ chainA m n ∨ w ∈ Set.range (corner m n) := by
  rcases track_cases hm hn u v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨he, -, -⟩
  · rw [track_02] at hw; exact Or.inl hw
  · rw [track_20, List.mem_reverse] at hw; exact Or.inl hw
  · exact absurd rfl hne
  · exact absurd (Sym2.eq_swap) hne
  · rw [he] at hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact Or.inr ⟨u, rfl⟩
    · rcases List.mem_cons.mp hw' with rfl | hw''
      · exact Or.inr ⟨v, rfl⟩
      · exact absurd hw'' (by simp)

theorem inl_interior_not_corner (hm : 2 ≤ m) (hn : 2 ≤ n) {i : Fin (m + 1)}
    (h0 : 0 < i.val) (hi : i.val < m) :
    (Sum.inl i : Host m n) ∉ Set.range (corner m n) := by
  rintro ⟨k, hk⟩
  fin_cases k <;>
    simp_all [corner, c1, c2, c3, c4, Fin.ext_iff] <;> omega

theorem inr_interior_not_corner (hm : 2 ≤ m) (hn : 2 ≤ n) {i : Fin (n + 1)}
    (h0 : 0 < i.val) (hi : i.val < n) :
    (Sum.inr i : Host m n) ∉ Set.range (corner m n) := by
  rintro ⟨k, hk⟩
  fin_cases k <;>
    simp_all [corner, c1, c2, c3, c4, Fin.ext_iff] <;> omega


/-! ### The subdivision -/

theorem host_isSubdivision (hm : 2 ≤ m) (hn : 2 ≤ n) :
    IsSubdivision (⊤ : SimpleGraph (Fin 4)) (host m n) := by
  refine ⟨corner m n, track m n, corner_injective hm hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    exact track_isTrackFrom hm hn u v (SimpleGraph.top_adj .. |>.mp huv)
  · intro u v huv
    rcases track_cases hm hn u v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨he, -, -⟩
    · rw [track_02]; simp [trackLength]; omega
    · rw [track_20]; simp [trackLength]; omega
    · rw [track_13]; simp [trackLength]; omega
    · rw [track_31]; simp [trackLength]; omega
    · rw [he]; simp [trackLength]
  · intro u v huv
    rcases track_cases hm hn u v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨he, he', -⟩
    · rw [track_02, track_20]
    · rw [track_02, track_20, List.reverse_reverse]
    · rw [track_13, track_31]
    · rw [track_13, track_31, List.reverse_reverse]
    · rw [he, he']; rfl
  · intro u v u' v' huv hu'v' hne w hw hmem
    rcases track_cases hm hn u v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨he, -, -⟩
    · rw [track_02] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainA.mp hw
      rcases mem_track_of_ne_A hm hn (Ne.symm hne) hmem with hB | hR
      · obtain ⟨j, hj⟩ := mem_chainB.mp hB; exact absurd hj (by simp)
      · exact inl_interior_not_corner hm hn h0 hi hR
    · rw [track_20, Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainA.mp hw
      rcases mem_track_of_ne_A hm hn (Ne.symm (Sym2.eq_swap ▸ hne)) hmem with hB | hR
      · obtain ⟨j, hj⟩ := mem_chainB.mp hB; exact absurd hj (by simp)
      · exact inl_interior_not_corner hm hn h0 hi hR
    · rw [track_13] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainB.mp hw
      rcases mem_track_of_ne_B hm hn (Ne.symm hne) hmem with hA | hR
      · obtain ⟨j, hj⟩ := mem_chainA.mp hA; exact absurd hj (by simp)
      · exact inr_interior_not_corner hm hn h0 hi hR
    · rw [track_31, Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainB.mp hw
      rcases mem_track_of_ne_B hm hn (Ne.symm (Sym2.eq_swap ▸ hne)) hmem with hA | hR
      · obtain ⟨j, hj⟩ := mem_chainA.mp hA; exact absurd hj (by simp)
      · exact inr_interior_not_corner hm hn h0 hi hR
    · rw [he] at hw; simp [trackInterior] at hw
  · intro u v huv w hw
    rcases track_cases hm hn u v with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨he, -, -⟩
    · rw [track_02] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainA.mp hw
      exact inl_interior_not_corner hm hn h0 hi
    · rw [track_20, Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainA.mp hw
      exact inl_interior_not_corner hm hn h0 hi
    · rw [track_13] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainB.mp hw
      exact inr_interior_not_corner hm hn h0 hi
    · rw [track_31, Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse] at hw
      obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainB.mp hw
      exact inr_interior_not_corner hm hn h0 hi
    · rw [he] at hw; simp [trackInterior] at hw
  · rintro (i | i)
    · by_cases h0 : i.val = 0
      · exact Or.inl ⟨0, by rw [corner_zero]; exact congrArg Sum.inl (Fin.ext (by simpa using h0))⟩
      by_cases hM : i.val = m
      · exact Or.inl ⟨2, by rw [corner_two]; exact congrArg Sum.inl (Fin.ext (by simpa using hM))⟩
      refine Or.inr ⟨0, 2, by simp, ?_⟩
      rw [track_02]
      exact mem_trackInterior_chainA.mpr ⟨i, by omega, by have := i.isLt; omega, rfl⟩
    · by_cases h0 : i.val = 0
      · exact Or.inl ⟨1, by rw [corner_one]; exact congrArg Sum.inr (Fin.ext (by simpa using h0))⟩
      by_cases hM : i.val = n
      · exact Or.inl ⟨3, by rw [corner_three]; exact congrArg Sum.inr (Fin.ext (by simpa using hM))⟩
      refine Or.inr ⟨1, 3, by simp, ?_⟩
      rw [track_13]
      exact mem_trackInterior_chainB.mpr ⟨i, by omega, by have := i.isLt; omega, rfl⟩
  · ext e
    simp only [Set.mem_iUnion]
    constructor
    · intro he
      obtain ⟨u, rfl⟩ := edgeOf_surjective e he
      rcases u with i | j | k
      · exact ⟨0, 2, by simp, by rw [track_02]; exact mem_trackEdges_chainA.mpr ⟨i, rfl⟩⟩
      · exact ⟨1, 3, by simp, by rw [track_13]; exact mem_trackEdges_chainB.mpr ⟨j, rfl⟩⟩
      · fin_cases k
        · refine ⟨0, 1, by simp, ?_⟩
          rw [track_cross m n 0 1 (by decide) (by decide) (by decide) (by decide),
            corner_zero, corner_one, trackEdges_pair]
          rfl
        · refine ⟨0, 3, by simp, ?_⟩
          rw [track_cross m n 0 3 (by decide) (by decide) (by decide) (by decide),
            corner_zero, corner_three, trackEdges_pair]
          rfl
        · refine ⟨2, 3, by simp, ?_⟩
          rw [track_cross m n 2 3 (by decide) (by decide) (by decide) (by decide),
            corner_two, corner_three, trackEdges_pair]
          rfl
        · refine ⟨2, 1, by simp, ?_⟩
          rw [track_cross m n 2 1 (by decide) (by decide) (by decide) (by decide),
            corner_two, corner_one, trackEdges_pair]
          rfl
    · rintro ⟨u, v, huv, hmem⟩
      exact trackEdges_subset_edgeSet
        (track_isTrackFrom hm hn u v (SimpleGraph.top_adj .. |>.mp huv)).1 hmem


/-! ### Bipartiteness -/

theorem host_bipartite (hem : Even m) (hen : Even n) : (host m n).IsBipartite := by
  have hm2 : m % 2 = 0 := Nat.even_iff.mp hem
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hen
  refine ⟨SimpleGraph.Coloring.mk
    (fun w => match w with
      | .inl i => (⟨i.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)
      | .inr j => (⟨(j.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2)) ?_⟩
  rintro (i | i) (j | j) hadj <;>
    simp only [host_adj_ll, host_adj_rr, host_adj_lr, host_adj_rl] at hadj <;>
    simp only [ne_eq, Fin.mk.injEq] <;> omega

/-! ### The degenerate four-cycle and the two branches -/

theorem corners_nodup (hm : 2 ≤ m) (hn : 2 ≤ n) :
    [c1 m n, c2 m n, c3 m n, c4 m n].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, and_true,
    or_false, List.mem_singleton, not_or]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
    simp [c1, c2, c3, c4, Fin.ext_iff] <;> omega

theorem host_degenerate (hm : 2 ≤ m) (hn : 2 ≤ n) :
    DegenerateK4Appearance (host m n) := by
  refine ⟨c1 m n, c2 m n, c3 m n, c4 m n, corners_nodup hm hn, ?_, ?_, ?_, ?_, ?_⟩
  · simp [c1, c2]
  · simp [c2, c3, Fin.val_last]
  · simp [c3, c4, Fin.val_last]
  · simp [c4, c1, Fin.val_last]
  · rw [branchVertices_eq hm hn]

theorem c1_ne_c3 (hm : 2 ≤ m) : (c1 m n) ≠ c3 m n := by
  simp [c1, c3, Fin.ext_iff]; omega

theorem c2_ne_c4 (hn : 2 ≤ n) : (c2 m n) ≠ c4 m n := by
  simp [c2, c4, Fin.ext_iff]; omega

theorem chainA_isBranch (hm : 2 ≤ m) (hn : 2 ≤ n) : IsBranch (host m n) (chainA m n) := by
  refine Thm82BranchDelta.isBranch_of_ends_branch chainA_isTrackFrom (c1_ne_c3 hm) ?_ ?_ ?_
  · intro w hw
    obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainA.mp hw
    rw [branchVertices_eq hm hn]
    intro hmem
    exact inl_interior_not_corner hm hn h0 hi
      (by rcases hmem with h | h | h | h <;> [exact ⟨0, h.symm⟩; exact ⟨1, h.symm⟩;
        exact ⟨2, h.symm⟩; exact ⟨3, h.symm⟩])
  · rw [branchVertices_eq hm hn]; simp
  · rw [branchVertices_eq hm hn]; simp

theorem chainB_isBranch (hm : 2 ≤ m) (hn : 2 ≤ n) : IsBranch (host m n) (chainB m n) := by
  refine Thm82BranchDelta.isBranch_of_ends_branch chainB_isTrackFrom (c2_ne_c4 hn) ?_ ?_ ?_
  · intro w hw
    obtain ⟨i, h0, hi, rfl⟩ := mem_trackInterior_chainB.mp hw
    rw [branchVertices_eq hm hn]
    intro hmem
    exact inr_interior_not_corner hm hn h0 hi
      (by rcases hmem with h | h | h | h <;> [exact ⟨0, h.symm⟩; exact ⟨1, h.symm⟩;
        exact ⟨2, h.symm⟩; exact ⟨3, h.symm⟩])
  · rw [branchVertices_eq hm hn]; simp
  · rw [branchVertices_eq hm hn]; simp

end Workspace.ProofLemmas.Thm93KnotSubdivision



