import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Prisms
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HyperprismFromPrism

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm101ThetaOfPrismAux

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismFromPrism

abbrev RawVertex (n : Fin 3 → ℕ) := Fin 2 ⊕ Σ i : Fin 3, Fin (n i)

def x (n : Fin 3 → ℕ) : RawVertex n := Sum.inl 0
def y (n : Fin 3 → ℕ) : RawVertex n := Sum.inl 1
def mid (n : Fin 3 → ℕ) (i : Fin 3) (k : Fin (n i)) : RawVertex n :=
  Sum.inr ⟨i, k⟩

def q (n : Fin 3 → ℕ) (i : Fin 3) : List (RawVertex n) :=
  [x n] ++ (List.finRange (n i)).map (mid n i) ++ [y n]

theorem card_rawVertex (n : Fin 3 → ℕ) :
    Fintype.card (RawVertex n) = n 0 + n 1 + n 2 + 2 := by
  simp [RawVertex, Fintype.card_sigma, Fin.sum_univ_succ]
  omega

theorem q_length (n : Fin 3 → ℕ) (i : Fin 3) : (q n i).length = n i + 2 := by
  simp [q]

theorem q_interior (n : Fin 3 → ℕ) (i : Fin 3) : trackInterior (q n i) =
    (List.finRange (n i)).map (mid n i) := by
  simp [q, trackInterior]

theorem q_nodup (n : Fin 3 → ℕ) (i : Fin 3) : (q n i).Nodup := by
  have hmid : Function.Injective (mid n i) := by
    intro k l h
    apply Fin.ext
    have hv := congrArg (fun z : RawVertex n =>
      match z with
      | Sum.inl _ => 0
      | Sum.inr z => z.2.val + 1) h
    simpa [mid] using hv
  have hm : ((List.finRange (n i)).map (mid n i)).Nodup :=
    (List.nodup_finRange _).map hmid
  simpa [q, x, y, mid, List.nodup_append] using hm

theorem q_head (n : Fin 3 → ℕ) (i : Fin 3) : (q n i).head? = some (x n) := by
  simp [q]

theorem q_last (n : Fin 3 → ℕ) (i : Fin 3) : (q n i).getLast? = some (y n) := by
  change ((x n :: (List.finRange (n i)).map (mid n i)) ++ [y n]).getLast? = some (y n)
  exact List.getLast?_concat

def edges (n : Fin 3 → ℕ) : Set (Sym2 (RawVertex n)) :=
  ⋃ i : Fin 3, trackEdges (q n i)

def H (n : Fin 3 → ℕ) : SimpleGraph (RawVertex n) :=
  SimpleGraph.fromEdgeSet (edges n)

theorem edges_disjoint_diag (n : Fin 3 → ℕ) :
    Disjoint (edges n) (Sym2.diagSet : Set (Sym2 (RawVertex n))) := by
  rw [Set.disjoint_left]
  intro e he hd
  simp only [edges, Set.mem_iUnion] at he
  obtain ⟨i, k, hk, rfl⟩ := he
  rw [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at hd
  have hidx := (q_nodup n i).getElem_inj_iff.mp hd
  omega

theorem H_edgeSet (n : Fin 3 → ℕ) : (H n).edgeSet = edges n := by
  rw [H, SimpleGraph.edgeSet_fromEdgeSet]
  exact sdiff_eq_left.mpr (edges_disjoint_diag n)

theorem q_track (n : Fin 3 → ℕ) (i : Fin 3) :
    IsTrackFrom (H n) (q n i) (x n) (y n) := by
  refine ⟨⟨by simp [q], q_nodup n i, ?_⟩, q_head n i, q_last n i⟩
  intro k hk
  rw [H, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, ?_⟩
  · simp only [edges, Set.mem_iUnion]
    exact ⟨i, k, hk, rfl⟩
  · intro heq
    have hidx := (q_nodup n i).getElem_inj_iff.mp heq
    omega

theorem q_interior_disjoint (n : Fin 3 → ℕ) {i j : Fin 3} (hij : i ≠ j) :
    ∀ v ∈ trackInterior (q n i), v ∉ q n j := by
  intro v hv hvj
  rw [q_interior] at hv
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hv
  simp [q, x, y, mid] at hvj
  exact hij hvj.1.symm

theorem q_interior_ne_ends (n : Fin 3 → ℕ) (i : Fin 3) :
    ∀ v ∈ trackInterior (q n i), v ≠ x n ∧ v ≠ y n := by
  intro v hv
  rw [q_interior] at hv
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hv
  simp [mid, x, y]

theorem q_cover (n : Fin 3 → ℕ) (v : RawVertex n) :
    v = x n ∨ v = y n ∨ ∃ i : Fin 3, v ∈ trackInterior (q n i) := by
  rcases v with v | v
  · fin_cases v
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rcases v with ⟨i, k⟩
    refine Or.inr (Or.inr ⟨i, ?_⟩)
    rw [q_interior]
    exact List.mem_map.mpr ⟨k, List.mem_finRange _, rfl⟩

abbrev EdgeIndex (n : Fin 3 → ℕ) := Σ i : Fin 3, Fin (n i + 1)

def edgeAt (n : Fin 3 → ℕ) (p : EdgeIndex n) : Sym2 (RawVertex n) :=
  s((q n p.1)[p.2.val]'(by rw [q_length]; omega),
    (q n p.1)[p.2.val + 1]'(by rw [q_length]; omega))

theorem edgeAt_mem (n : Fin 3 → ℕ) (p : EdgeIndex n) : edgeAt n p ∈ edges n := by
  simp only [edges, Set.mem_iUnion]
  exact ⟨p.1, p.2.val, by rw [q_length]; omega, rfl⟩

theorem exists_edgeIndex_of_mem_edges (n : Fin 3 → ℕ) {e : Sym2 (RawVertex n)}
    (he : e ∈ edges n) : ∃ p : EdgeIndex n, edgeAt n p = e := by
  simp only [edges, Set.mem_iUnion] at he
  obtain ⟨i, k, hk, rfl⟩ := he
  have hk' : k < n i + 1 := by rw [q_length] at hk; omega
  exact ⟨⟨i, ⟨k, hk'⟩⟩, rfl⟩

theorem edgeAt_same_eq_iff (n : Fin 3 → ℕ) (i : Fin 3)
    (k l : Fin (n i + 1)) :
    edgeAt n ⟨i, k⟩ = edgeAt n ⟨i, l⟩ ↔ k = l := by
  constructor
  · intro h
    rw [edgeAt, edgeAt, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply Fin.ext
      exact (q_nodup n i).getElem_inj_iff.mp h1
    · have hi1 := (q_nodup n i).getElem_inj_iff.mp h1
      have hi2 := (q_nodup n i).getElem_inj_iff.mp h2
      omega
  · rintro rfl
    rfl

theorem edgeAt_same_meet_iff (n : Fin 3 → ℕ) (i : Fin 3)
    (k l : Fin (n i + 1)) :
    (edgeAt n ⟨i, k⟩ ≠ edgeAt n ⟨i, l⟩ ∧
      ∃ v, v ∈ edgeAt n ⟨i, k⟩ ∧ v ∈ edgeAt n ⟨i, l⟩) ↔
      (k.val + 1 = l.val ∨ l.val + 1 = k.val) := by
  constructor
  · rintro ⟨hne, v, hvk, hvl⟩
    have hkl : k.val ≠ l.val := by
      intro h
      exact hne ((edgeAt_same_eq_iff n i k l).mpr (Fin.ext h))
    simp only [edgeAt, Sym2.mem_iff] at hvk hvl
    rcases hvk with h1 | h1 <;> rcases hvl with h2 | h2
    · have he := (q_nodup n i).getElem_inj_iff.mp (h1.symm.trans h2)
      exact False.elim (hkl he)
    · have he := (q_nodup n i).getElem_inj_iff.mp (h1.symm.trans h2)
      exact Or.inr (by omega)
    · have he := (q_nodup n i).getElem_inj_iff.mp (h1.symm.trans h2)
      exact Or.inl (by omega)
    · have he := (q_nodup n i).getElem_inj_iff.mp (h1.symm.trans h2)
      exact False.elim (hkl (by omega))
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      have he := (edgeAt_same_eq_iff n i k l).mp heq
      rcases h with h | h <;> omega
    · rcases h with h | h
      · refine ⟨(q n i)[k.val + 1]'(by rw [q_length]; omega), ?_, ?_⟩
        · rw [edgeAt, Sym2.mem_iff]
          exact Or.inr rfl
        · rw [edgeAt, Sym2.mem_iff]
          exact Or.inl (by congr)
      · refine ⟨(q n i)[l.val + 1]'(by rw [q_length]; omega), ?_, ?_⟩
        · rw [edgeAt, Sym2.mem_iff]
          exact Or.inl (by congr)
        · rw [edgeAt, Sym2.mem_iff]
          exact Or.inr rfl

theorem q_intersection (n : Fin 3 → ℕ) {i j : Fin 3} (hij : i ≠ j)
    {v : RawVertex n} (hi : v ∈ q n i) (hj : v ∈ q n j) :
    v = x n ∨ v = y n := by
  rcases v with v | v
  · fin_cases v
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rcases v with ⟨t, k⟩
    simp [q, x, y, mid] at hi hj
    exact False.elim (hij (hi.1.trans hj.1.symm))

theorem q_get_eq_x_iff (n : Fin 3 → ℕ) (i : Fin 3) (k : ℕ)
    (hk : k < (q n i).length) :
    (q n i)[k]'hk = x n ↔ k = 0 := by
  have h0 : (q n i)[0]'(by simp [q]) = x n := by simp [q]
  constructor
  · intro h
    exact (q_nodup n i).getElem_inj_iff.mp (h.trans h0.symm)
  · rintro rfl
    simpa using h0

theorem q_get_eq_y_iff (n : Fin 3 → ℕ) (i : Fin 3) (k : ℕ)
    (hk : k < (q n i).length) :
    (q n i)[k]'hk = y n ↔ k = n i + 1 := by
  have hlast : (q n i)[n i + 1]'(by rw [q_length]; omega) = y n := by
    have h := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
      (q_last n i) (by simp [q])
    have heq : (q n i).length - 1 = n i + 1 := by rw [q_length]; omega
    simpa [heq] using h
  constructor
  · intro h
    exact (q_nodup n i).getElem_inj_iff.mp (h.trans hlast.symm)
  · intro h
    have he := Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
      (q n i) h hk (by rw [q_length]; omega)
    exact he.trans hlast

theorem edgeAt_has_interior_endpoint (n : Fin 3 → ℕ) (i : Fin 3)
    (hn : 1 ≤ n i) (k : Fin (n i + 1)) :
    ∃ v, v ∈ edgeAt n ⟨i, k⟩ ∧ v ∈ trackInterior (q n i) := by
  by_cases hk : k.val < n i
  · refine ⟨(q n i)[k.val + 1]'(by rw [q_length]; omega), ?_, ?_⟩
    · rw [edgeAt, Sym2.mem_iff]
      exact Or.inr rfl
    · exact Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem
        (q n i) k.val (by rw [q_length]; omega)
  · have hkeq : k.val = n i := by omega
    refine ⟨(q n i)[k.val]'(by rw [q_length]; omega), ?_, ?_⟩
    · rw [edgeAt, Sym2.mem_iff]
      exact Or.inl rfl
    · have hm := Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem
        (q n i) (k.val - 1) (by rw [q_length]; omega)
      have he := Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
        (q n i) (show k.val - 1 + 1 = k.val by omega)
        (by rw [q_length]; omega) (by rw [q_length]; omega)
      rwa [he] at hm

theorem edgeAt_cross_ne (n : Fin 3 → ℕ) {i j : Fin 3} (hij : i ≠ j)
    (hni : 1 ≤ n i) (k : Fin (n i + 1)) (l : Fin (n j + 1)) :
    edgeAt n ⟨i, k⟩ ≠ edgeAt n ⟨j, l⟩ := by
  intro heq
  obtain ⟨v, hve, hvint⟩ := edgeAt_has_interior_endpoint n i hni k
  have hve' : v ∈ edgeAt n ⟨j, l⟩ := by rwa [← heq]
  have hvqj : v ∈ q n j := by
    rw [edgeAt, Sym2.mem_iff] at hve'
    rcases hve' with h | h
    · rw [h]
      exact List.getElem_mem _
    · rw [h]
      exact List.getElem_mem _
  exact q_interior_disjoint n hij v hvint hvqj

theorem edgeAt_cross_meet_iff (n : Fin 3 → ℕ) {i j : Fin 3} (hij : i ≠ j)
    (hni : 1 ≤ n i) (k : Fin (n i + 1)) (l : Fin (n j + 1)) :
    (edgeAt n ⟨i, k⟩ ≠ edgeAt n ⟨j, l⟩ ∧
      ∃ v, v ∈ edgeAt n ⟨i, k⟩ ∧ v ∈ edgeAt n ⟨j, l⟩) ↔
      ((k.val = 0 ∧ l.val = 0) ∨ (k.val = n i ∧ l.val = n j)) := by
  constructor
  · rintro ⟨-, v, hvk, hvl⟩
    have hvqi : v ∈ q n i := by
      rw [edgeAt, Sym2.mem_iff] at hvk
      rcases hvk with h | h <;> rw [h] <;> exact List.getElem_mem _
    have hvqj : v ∈ q n j := by
      rw [edgeAt, Sym2.mem_iff] at hvl
      rcases hvl with h | h <;> rw [h] <;> exact List.getElem_mem _
    rcases q_intersection n hij hvqi hvqj with hxv | hyv
    · left
      constructor
      · rw [edgeAt, Sym2.mem_iff] at hvk
        rcases hvk with h | h
        · exact (q_get_eq_x_iff n i k.val _).mp (h.symm.trans hxv)
        · have he := (q_get_eq_x_iff n i (k.val + 1) _).mp (h.symm.trans hxv)
          omega
      · rw [edgeAt, Sym2.mem_iff] at hvl
        rcases hvl with h | h
        · exact (q_get_eq_x_iff n j l.val _).mp (h.symm.trans hxv)
        · have he := (q_get_eq_x_iff n j (l.val + 1) _).mp (h.symm.trans hxv)
          omega
    · right
      constructor
      · rw [edgeAt, Sym2.mem_iff] at hvk
        rcases hvk with h | h
        · have he := (q_get_eq_y_iff n i k.val _).mp (h.symm.trans hyv)
          omega
        · have he := (q_get_eq_y_iff n i (k.val + 1) _).mp (h.symm.trans hyv)
          omega
      · rw [edgeAt, Sym2.mem_iff] at hvl
        rcases hvl with h | h
        · have he := (q_get_eq_y_iff n j l.val _).mp (h.symm.trans hyv)
          omega
        · have he := (q_get_eq_y_iff n j (l.val + 1) _).mp (h.symm.trans hyv)
          omega
  · intro h
    refine ⟨edgeAt_cross_ne n hij hni k l, ?_⟩
    rcases h with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · refine ⟨x n, ?_, ?_⟩
      · rw [edgeAt, Sym2.mem_iff]
        exact Or.inl ((q_get_eq_x_iff n i k.val _).mpr hk).symm
      · rw [edgeAt, Sym2.mem_iff]
        exact Or.inl ((q_get_eq_x_iff n j l.val _).mpr hl).symm
    · refine ⟨y n, ?_, ?_⟩
      · rw [edgeAt, Sym2.mem_iff]
        exact Or.inr ((q_get_eq_y_iff n i (k.val + 1) _).mpr (by omega)).symm
      · rw [edgeAt, Sym2.mem_iff]
        exact Or.inr ((q_get_eq_y_iff n j (l.val + 1) _).mpr (by omega)).symm

def indexedEdge (n : Fin 3 → ℕ) (p : EdgeIndex n) : (H n).edgeSet :=
  ⟨edgeAt n p, by rw [H_edgeSet]; exact edgeAt_mem n p⟩

theorem indexedEdge_bijective (n : Fin 3 → ℕ) (hn : ∀ i, 1 ≤ n i) :
    Function.Bijective (indexedEdge n) := by
  constructor
  · rintro ⟨i, k⟩ ⟨j, l⟩ h
    have he : edgeAt n ⟨i, k⟩ = edgeAt n ⟨j, l⟩ := Subtype.mk.inj h
    by_cases hij : i = j
    · subst j
      have hkl := (edgeAt_same_eq_iff n i k l).mp he
      subst l
      rfl
    · exact False.elim (edgeAt_cross_ne n hij (hn i) k l he)
  · intro e
    have he : (e : Sym2 (RawVertex n)) ∈ edges n := by
      rw [← H_edgeSet]
      exact e.2
    obtain ⟨p, hp⟩ := exists_edgeIndex_of_mem_edges n he
    exact ⟨p, Subtype.ext hp⟩

noncomputable def edgeEquiv (n : Fin 3 → ℕ) (hn : ∀ i, 1 ≤ n i) :
    EdgeIndex n ≃ (H n).edgeSet :=
  Equiv.ofBijective (indexedEdge n) (indexedEdge_bijective n hn)

@[simp] theorem edgeEquiv_apply (n : Fin 3 → ℕ) (hn : ∀ i, 1 ≤ n i)
    (p : EdgeIndex n) : edgeEquiv n hn p = indexedEdge n p := rfl

def rungSize {V : Type*} (R : Fin 3 → List V) (i : Fin 3) : ℕ :=
  pathLength (R i)

theorem rungSize_add_one {V : Type*} {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (i : Fin 3) : rungSize R i + 1 = (R i).length := by
  have h2 := formPrism_two_le_length hprism i
  rw [rungSize, Workspace.ProofLemmas.PathBasics.pathLength_eq]
  omega

theorem one_le_rungSize {V : Type*} {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hprism : FormPrism G a b (R 0) (R 1) (R 2)) :
    ∀ i, 1 ≤ rungSize R i := by
  intro i
  have h2 := formPrism_two_le_length hprism i
  rw [rungSize, Workspace.ProofLemmas.PathBasics.pathLength_eq]
  omega

def rungVertex {V : Type*} (R : Fin 3 → List V)
    (h2 : ∀ i, 2 ≤ (R i).length) (p : EdgeIndex (rungSize R)) : V :=
  (R p.1)[p.2.val]'(by
    have hp := p.2.isLt
    change p.2.val < pathLength (R p.1) + 1 at hp
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hp
    have hi := h2 p.1
    omega)

theorem rungVertex_mem {V : Type*} (R : Fin 3 → List V)
    (h2 : ∀ i, 2 ≤ (R i).length) (p : EdgeIndex (rungSize R)) :
    rungVertex R h2 p ∈ R p.1 := by
  exact List.getElem_mem _

theorem rungVertex_eq_a_iff {V : Type*} {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (i : Fin 3) (k : Fin (rungSize R i + 1)) :
    rungVertex R (formPrism_two_le_length hprism) ⟨i, k⟩ = a i ↔ k.val = 0 := by
  have h0 : (R i)[0]'(by have := formPrism_two_le_length hprism i; omega) = a i :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head?
      (formPrism_path hprism i).2.1 (by have := formPrism_two_le_length hprism i; omega)
  constructor
  · intro h
    exact (formPrism_path hprism i).1.2.1.getElem_inj_iff.mp (h.trans h0.symm)
  · intro hk
    have he := Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
      (R i) hk (by rw [← rungSize_add_one hprism i]; exact k.isLt)
      (by have := formPrism_two_le_length hprism i; omega)
    exact he.trans h0

theorem rungVertex_eq_b_iff {V : Type*} {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (i : Fin 3) (k : Fin (rungSize R i + 1)) :
    rungVertex R (formPrism_two_le_length hprism) ⟨i, k⟩ = b i ↔
      k.val = rungSize R i := by
  have hlast :
      (R i)[rungSize R i]'(by rw [← rungSize_add_one hprism i]; omega) = b i := by
    have h := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
      (formPrism_path hprism i).2.2 (by have := formPrism_two_le_length hprism i; omega)
    have heq : (R i).length - 1 = rungSize R i := by
      rw [rungSize, Workspace.ProofLemmas.PathBasics.pathLength_eq]
    simpa [heq] using h
  constructor
  · intro h
    exact (formPrism_path hprism i).1.2.1.getElem_inj_iff.mp (h.trans hlast.symm)
  · intro hk
    have he := Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
      (R i) hk (by rw [← rungSize_add_one hprism i]; exact k.isLt)
      (by rw [← rungSize_add_one hprism i]; omega)
    exact he.trans hlast

def rungInK {V : Type*} {G : SimpleGraph V} (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (p : EdgeIndex (rungSize R)) : K :=
  ⟨rungVertex R (formPrism_two_le_length hprism) p, by
    rw [hK]
    rcases p with ⟨i, k⟩
    fin_cases i
    · exact Or.inl (Or.inl (rungVertex_mem R _ ⟨0, k⟩))
    · exact Or.inl (Or.inr (rungVertex_mem R _ ⟨1, k⟩))
    · exact Or.inr (rungVertex_mem R _ ⟨2, k⟩)⟩

theorem rungInK_bijective {V : Type*} {G : SimpleGraph V} (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}) :
    Function.Bijective (rungInK a b R K hprism hK) := by
  constructor
  · rintro ⟨i, k⟩ ⟨j, l⟩ h
    have he :
        rungVertex R (formPrism_two_le_length hprism) ⟨i, k⟩ =
          rungVertex R (formPrism_two_le_length hprism) ⟨j, l⟩ := Subtype.mk.inj h
    by_cases hij : i = j
    · subst j
      have hidx := (formPrism_path hprism i).1.2.1.getElem_inj_iff.mp he
      have hkl : k = l := Fin.ext hidx
      subst l
      rfl
    · have hmi := rungVertex_mem R (formPrism_two_le_length hprism) ⟨i, k⟩
      have hmj := rungVertex_mem R (formPrism_two_le_length hprism) ⟨j, l⟩
      rw [he] at hmi
      exact False.elim (formPrism_disjoint hprism hij _ hmi hmj)
  · intro v
    have hv : (v : V) ∈
        ({v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}) := by
      rw [← hK]
      exact v.2
    rcases hv with (hv | hv) | hv
    · obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
      have hk' : k < rungSize R 0 + 1 := by rw [rungSize_add_one hprism]; exact hk
      refine ⟨⟨0, ⟨k, hk'⟩⟩, Subtype.ext ?_⟩
      exact hkv
    · obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
      have hk' : k < rungSize R 1 + 1 := by rw [rungSize_add_one hprism]; exact hk
      refine ⟨⟨1, ⟨k, hk'⟩⟩, Subtype.ext ?_⟩
      exact hkv
    · obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
      have hk' : k < rungSize R 2 + 1 := by rw [rungSize_add_one hprism]; exact hk
      refine ⟨⟨2, ⟨k, hk'⟩⟩, Subtype.ext ?_⟩
      exact hkv

noncomputable def rungEquiv {V : Type*} {G : SimpleGraph V} (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}) :
    EdgeIndex (rungSize R) ≃ K :=
  Equiv.ofBijective (rungInK a b R K hprism hK)
    (rungInK_bijective a b R K hprism hK)

@[simp] theorem rungEquiv_apply {V : Type*} {G : SimpleGraph V} (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (p : EdgeIndex (rungSize R)) :
    rungEquiv a b R K hprism hK p = rungInK a b R K hprism hK p := rfl

noncomputable def rawPrismIso {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}) :
    (H (rungSize R)).lineGraph ≃g G.induce K := by
  let hn : ∀ i, 1 ≤ rungSize R i := one_le_rungSize hprism
  let ee := edgeEquiv (rungSize R) hn
  let re := rungEquiv a b R K hprism hK
  refine { toEquiv := ee.symm.trans re, map_rel_iff' := ?_ }
  intro e f
  obtain ⟨⟨i, k⟩, rfl⟩ := ee.surjective e
  obtain ⟨⟨j, l⟩, rfl⟩ := ee.surjective f
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  simp only [ee, re, edgeEquiv_apply, rungEquiv_apply]
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  simp only [rungInK, indexedEdge]
  change G.Adj
      (rungVertex R (formPrism_two_le_length hprism) ⟨i, k⟩)
      (rungVertex R (formPrism_two_le_length hprism) ⟨j, l⟩) ↔
    (indexedEdge (rungSize R) ⟨i, k⟩ ≠ indexedEdge (rungSize R) ⟨j, l⟩ ∧
      ∃ v, v ∈ edgeAt (rungSize R) ⟨i, k⟩ ∧
        v ∈ edgeAt (rungSize R) ⟨j, l⟩)
  have hne :
      indexedEdge (rungSize R) ⟨i, k⟩ ≠ indexedEdge (rungSize R) ⟨j, l⟩ ↔
        edgeAt (rungSize R) ⟨i, k⟩ ≠ edgeAt (rungSize R) ⟨j, l⟩ := by
    constructor
    · intro h hval
      exact h (Subtype.ext hval)
    · intro h hsub
      exact h (congrArg Subtype.val hsub)
  rw [hne]
  by_cases hij : i = j
  · subst j
    rw [edgeAt_same_meet_iff]
    simpa [rungVertex] using
      (Workspace.ProofLemmas.PathBasics.path_adj_iff (formPrism_path hprism i).1
        (by rw [← rungSize_add_one hprism i]; exact k.isLt)
        (by rw [← rungSize_add_one hprism i]; exact l.isLt))
  · rw [edgeAt_cross_meet_iff (hij := hij) (hni := hn i)]
    rw [formPrism_cross hprism hij
      _ (rungVertex_mem R (formPrism_two_le_length hprism) ⟨i, k⟩)
      _ (rungVertex_mem R (formPrism_two_le_length hprism) ⟨j, l⟩),
      rungVertex_eq_a_iff hprism, rungVertex_eq_a_iff hprism,
      rungVertex_eq_b_iff hprism, rungVertex_eq_b_iff hprism]

@[simp] theorem rawPrismIso_indexedEdge {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (a b : Fin 3 → V) (R : Fin 3 → List V) (K : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (p : EdgeIndex (rungSize R)) :
    rawPrismIso G a b R K hprism hK (indexedEdge (rungSize R) p) =
      rungInK a b R K hprism hK p := by
  change (rungEquiv a b R K hprism hK)
      ((edgeEquiv (rungSize R) (one_le_rungSize hprism)).symm
        (edgeEquiv (rungSize R) (one_le_rungSize hprism) p)) = _
  rw [Equiv.symm_apply_apply, rungEquiv_apply]

noncomputable def finEquiv (n : Fin 3 → ℕ) :
    RawVertex n ≃ Fin (n 0 + n 1 + n 2 + 2) :=
  Fintype.equivFinOfCardEq (card_rawVertex n)

noncomputable def theta (n : Fin 3 → ℕ) :
    SimpleGraph (Fin (n 0 + n 1 + n 2 + 2)) :=
  (H n).map (finEquiv n).toEmbedding

noncomputable def fx (n : Fin 3 → ℕ) : Fin (n 0 + n 1 + n 2 + 2) :=
  finEquiv n (x n)

noncomputable def fy (n : Fin 3 → ℕ) : Fin (n 0 + n 1 + n 2 + 2) :=
  finEquiv n (y n)

noncomputable def fq (n : Fin 3 → ℕ) (i : Fin 3) :
    List (Fin (n 0 + n 1 + n 2 + 2)) :=
  (q n i).map (finEquiv n)

/-- The vertex/edge clauses of a theta presentation, before tying its edges to a prism. -/
def IsRawThetaDatum {W : Type*} (Theta : SimpleGraph W) (xx yy : W)
    (Q : Fin 3 → List W) : Prop :=
  xx ≠ yy ∧
  (∀ i : Fin 3, IsTrackFrom Theta (Q i) xx yy) ∧
  (∀ i : Fin 3, 2 ≤ (Q i).length) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ v ∈ trackInterior (Q i), v ∉ Q j) ∧
  (∀ i : Fin 3, ∀ v ∈ trackInterior (Q i), v ≠ xx ∧ v ≠ yy) ∧
  (∀ v : W, v = xx ∨ v = yy ∨ ∃ i : Fin 3, v ∈ trackInterior (Q i)) ∧
  Theta.edgeSet = ⋃ i : Fin 3, trackEdges (Q i)

theorem fin_isTheta (n : Fin 3 → ℕ) :
    IsRawThetaDatum (theta n) (fx n) (fy n) (fq n) := by
  let psi : H n ≃g theta n := SimpleGraph.Iso.map (finEquiv n) (H n)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : x n = y n := (finEquiv n).injective (by simpa [fx, fy] using h)
    simpa [x, y] using h'
  · intro i
    simpa [psi, theta, fq, fx, fy] using
      Workspace.ProofLemmas.SubdivisionCounting.isTrackFrom_map psi (q_track n i)
  · intro i
    simp [fq, q_length]
  · intro i j hij v hv hvj
    rw [fq, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hv
    rw [fq] at hvj
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
    obtain ⟨w0, hw0, heq⟩ := List.mem_map.mp hvj
    exact q_interior_disjoint n hij v0 hv0
      ((finEquiv n).injective heq ▸ hw0)
  · intro i v hv
    rw [fq, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map] at hv
    obtain ⟨v0, hv0, rfl⟩ := List.mem_map.mp hv
    obtain ⟨hx0, hy0⟩ := q_interior_ne_ends n i v0 hv0
    exact ⟨fun h => hx0 ((finEquiv n).injective h),
      fun h => hy0 ((finEquiv n).injective h)⟩
  · intro v
    rcases q_cover n ((finEquiv n).symm v) with hx0 | hy0 | ⟨i, hi⟩
    · exact Or.inl (by simpa [fx] using congrArg (finEquiv n) hx0)
    · exact Or.inr (Or.inl (by simpa [fy] using congrArg (finEquiv n) hy0))
    · refine Or.inr (Or.inr ⟨i, ?_⟩)
      rw [fq, Workspace.ProofLemmas.SubdivisionCounting.trackInterior_map]
      exact List.mem_map.mpr ⟨(finEquiv n).symm v, hi, by simp⟩
  · rw [← Workspace.ProofLemmas.SubdivisionCounting.edgeSet_image_of_iso psi,
      H_edgeSet]
    ext e
    constructor
    · rintro ⟨d, hd, rfl⟩
      simp only [edges, Set.mem_iUnion] at hd
      obtain ⟨i, hi⟩ := hd
      simp only [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [fq, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map]
      exact ⟨d, hi, rfl⟩
    · simp only [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      rw [fq, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_map] at hi
      obtain ⟨d, hd, rfl⟩ := hi
      refine ⟨d, ?_, rfl⟩
      simp only [edges, Set.mem_iUnion]
      exact ⟨i, hd⟩

end Workspace.ProofLemmas.Thm101ThetaOfPrismAux
