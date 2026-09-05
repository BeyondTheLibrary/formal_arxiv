import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
import Workspace.ProofLemmas.Thm58NoEvenTrackThroughAttachments
import Workspace.Statements.S05.Thm_5_7

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58SingletonCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

section Helpers

variable {W : Type*} {H : SimpleGraph W}

/-- The only edge of a track incident with its first vertex is its first edge. -/
theorem head_edge_unique {q : List W} (hq : IsTrackList H q) (h2 : 2 ≤ q.length)
    {e : Sym2 W} (he : e ∈ trackEdges q) (hmem : q[0]'(by omega) ∈ e) :
    e = s(q[0]'(by omega), q[0 + 1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  have hnd := hq.2.1
  rcases Sym2.mem_iff.mp hmem with h | h
  · have h' : (0 : ℕ) = i := hnd.getElem_inj_iff.mp h
    subst h'
    rfl
  · have h' : (0 : ℕ) = i + 1 := hnd.getElem_inj_iff.mp h
    omega

/-- The only edge of a track incident with its last vertex is its last edge. -/
theorem last_edge_unique {q : List W} (hq : IsTrackList H q) (h2 : 2 ≤ q.length)
    {e : Sym2 W} (he : e ∈ trackEdges q) (hmem : q[q.length - 1]'(by omega) ∈ e) :
    e = s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  have hnd := hq.2.1
  rcases Sym2.mem_iff.mp hmem with h | h
  · have h' : q.length - 1 = i := hnd.getElem_inj_iff.mp h
    omega
  · have h' : q.length - 1 = i + 1 := hnd.getElem_inj_iff.mp h
    have hi0 : i = q.length - 2 := by omega
    subst hi0
    rfl

/-- An internal vertex of a track lies on two distinct edges of it. -/
theorem two_edges_at_interior {q : List W} (hq : IsTrackList H q) {w : W}
    (hw : w ∈ trackInterior q) :
    ∃ e f : Sym2 W, e ∈ trackEdges q ∧ f ∈ trackEdges q ∧ e ≠ f ∧ w ∈ e ∧ w ∈ f := by
  obtain ⟨j, hj, rfl⟩ := (SubdivisionCounting.mem_trackInterior_iff q w).mp hw
  refine ⟨s(q[j]'(by omega), q[j + 1]'(by omega)),
    s(q[j + 1]'(by omega), q[j + 1 + 1]'(by omega)),
    ⟨j, by omega, rfl⟩, ⟨j + 1, by omega, rfl⟩, ?_, ?_, ?_⟩
  · intro hc
    rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := hq.2.1.getElem_inj_iff.mp h1; omega
    · have := hq.2.1.getElem_inj_iff.mp h1; omega
  · exact Sym2.mem_mk_right _ _
  · exact Sym2.mem_mk_left _ _

end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm58SingletonCase (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (y : V) (hyK : y ∉ K)
    (hnotlocal : ¬ LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G {y} K})
    (hnomajor : ¬ MajorForLineGraph G H K φ y) :
    ∃ (P : List V) (p₁ p₂ : V), IsPathFrom G P p₁ p₂ ∧ (∀ x ∈ P, x ∈ ({y} : Set V)) ∧
      ((∃ c₁ c₂ : Fin n,
          (¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
          (∀ x ∈ N c₁, G.Adj p₁ x) ∧ (∀ x ∈ N c₂, G.Adj p₂ x) ∧
          (∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ N c₁) ∨ (x = p₂ ∧ y ∈ N c₂))) ∨
       (∃ (b₁ b₂ : Fin n) (q : List (Fin n)) (R : List V) (r₁ r₂ : V),
          b₁ ∈ branchVertices H ∧ b₂ ∈ branchVertices H ∧
          IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
          IsPathList G R ∧
          {x : V | x ∈ R} =
            {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
              e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)} ∧
          N b₁ ∩ {x : V | x ∈ R} = {r₁} ∧ N b₂ ∩ {x : V | x ∈ R} = {r₂} ∧
          (((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧
            (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
           ((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂}) ∨
              (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
            (Even (pathLength P) ↔ Even (pathLength R))) ∨
           (p₁ = p₂ ∧ (∀ x ∈ (N b₁ ∪ N b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
            (∀ y ∈ K, G.Adj p₁ y → y ∈ N b₁ ∪ N b₂ ∪ {z : V | z ∈ R}) ∧
            Even (pathLength R)) ∨
           (r₁ = r₂ ∧ (∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂})) ∧
            Even (pathLength P))))) := by
  classical
  ------------------------------------------------------------------
  -- 0.  The attachment set `X`, and the basic dictionary
  ------------------------------------------------------------------
  set X : Set (Sym2 (Fin n)) := {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
    (↑(φ ⟨e, he⟩) : V) ∈ attachments G {y} K} with hXdef
  have hattach : ∀ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      (↑(φ ⟨e, he⟩) : V) ∈ attachments G {y} K ↔ G.Adj y (↑(φ ⟨e, he⟩) : V) := by
    intro e he
    constructor
    · rintro ⟨-, z, hz, hadj⟩
      have hzy : z = y := hz
      rw [hzy] at hadj
      exact hadj.symm
    · intro h
      exact ⟨Subtype.coe_prop _, y, rfl, h.symm⟩
  have hXE : X ⊆ H.edgeSet := by
    rw [hXdef]; rintro e ⟨he, -⟩; exact he
  have hφinj : ∀ a b : ↥H.edgeSet, (↑(φ a) : V) = (↑(φ b) : V) → a = b := fun a b h =>
    φ.injective (Subtype.ext h)
  have hKimg : ∀ z ∈ K, ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), z = (↑(φ ⟨e, he⟩) : V) := by
    intro z hz
    refine ⟨(φ.symm ⟨z, hz⟩ : ↥H.edgeSet).1, (φ.symm ⟨z, hz⟩ : ↥H.edgeSet).2, ?_⟩
    have h1 : (⟨(φ.symm ⟨z, hz⟩ : ↥H.edgeSet).1, (φ.symm ⟨z, hz⟩ : ↥H.edgeSet).2⟩ :
        ↥H.edgeSet) = φ.symm ⟨z, hz⟩ := rfl
    rw [h1, φ.apply_symm_apply]
  -- the path `P = [y]`
  have hPfrom : IsPathFrom G [y] y y := by
    refine ⟨⟨by simp, by simp, ?_⟩, rfl, rfl⟩
    intro i j hi hj
    simp only [List.length_singleton] at hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    simp
  ------------------------------------------------------------------
  -- 1.  Subdivision bookkeeping
  ------------------------------------------------------------------
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub.1
  have hdeg : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard := fun u =>
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hbv₁ : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlenT hdisjint hnew hdeg
  -- every vertex of `H` has a neighbour
  have hnbr : ∀ w : Fin n, ∃ x : Fin n, H.Adj w x := by
    intro w
    rcases hcover w with ⟨a, rfl⟩ | ⟨a, b, hab, hwint⟩
    · have h3 := hdeg a
      obtain ⟨v0, hv0⟩ : (J.neighborSet a).Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by omega)
      have ht := htrack a v0 hv0
      have hl := hlenT a v0 hv0
      have h2 : 2 ≤ (T a v0).length := by simp only [trackLength] at hl; omega
      refine ⟨(T a v0)[1]'(by omega), ?_⟩
      have h0 := SubdivisionCounting.track_head ht (by omega)
      have hadj := ht.1.2.2 0 (by omega)
      rw [h0] at hadj
      exact hadj
    · obtain ⟨j, hj, rfl⟩ := (SubdivisionCounting.mem_trackInterior_iff _ _).mp hwint
      exact ⟨(T a b)[j + 1 + 1]'(by omega), (htrack a b hab).1.2.2 (j + 1) (by omega)⟩
  have h2le : ∀ q : List (Fin n), IsBranch H q → 2 ≤ q.length := fun q hq =>
    Thm84BranchRungDictionaryAt.two_le_length_of_isBranch hnbr hq
  -- the ends of a branch are branch-vertices
  have hEndBV : ∀ (q : List (Fin n)) (c₁ c₂ : Fin n), IsBranch H q → IsTrackFrom H q c₁ c₂ →
      c₁ ∈ branchVertices H ∧ c₂ ∈ branchVertices H := by
    intro q c₁ c₂ hbranch hfrom
    have hq2 := h2le q hbranch
    have hqt : IsTrackList H q := hbranch.1
    obtain ⟨u, v, huv, heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
      hι htrack hlenT hrev hdisjint hnew hcover hedges hdeg hbranch hq2
    have hc₁ : q[0]'(by omega) = c₁ := SubdivisionCounting.track_head hfrom (by omega)
    have hc₂ : q[q.length - 1]'(by omega) = c₂ := by
      have h' := hfrom.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
      exact Option.some_injective _ h'
    have hfirst : s(q[0]'(by omega), q[0 + 1]'(by omega)) ∈ trackEdges q := ⟨0, by omega, rfl⟩
    have hlast : s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)) ∈ trackEdges q :=
      ⟨q.length - 2, by omega, rfl⟩
    have key : ∀ (w : Fin n), (∃ e ∈ trackEdges q, w ∈ e) →
        (∀ e f : Sym2 (Fin n), e ∈ trackEdges q → f ∈ trackEdges q → w ∈ e → w ∈ f → e = f) →
        w ∈ branchVertices H := by
      intro w ⟨e0, he0, hwe0⟩ huniq
      have hmemT : w ∈ T u v := by
        obtain ⟨d, rfl⟩ := Sym2.mem_iff_exists.mp hwe0
        exact (BranchClassification.mem_of_mem_trackEdges (heq ▸ he0)).1
      have hnotint : w ∉ trackInterior (T u v) := by
        intro hc
        obtain ⟨e, f, he, hf, hef, hme, hmf⟩ := two_edges_at_interior (htrack u v huv).1 hc
        rw [← heq] at he hf
        exact hef (huniq e f he hf hme hmf)
      rcases SubdivisionCompose.mem_ends_of_mem (htrack u v huv).2.1 (htrack u v huv).2.2
        hmemT hnotint with h | h
      · exact hbv₁ ⟨u, h.symm⟩
      · exact hbv₁ ⟨v, h.symm⟩
    constructor
    · rw [← hc₁]
      refine key _ ⟨_, hfirst, Sym2.mem_mk_left _ _⟩ ?_
      intro e f he hf hme hmf
      exact (head_edge_unique hqt hq2 he hme).trans (head_edge_unique hqt hq2 hf hmf).symm
    · rw [← hc₂]
      refine key _ ⟨_, hlast, ?_⟩ ?_
      · have hidx : q[q.length - 2 + 1]'(by omega) = q[q.length - 1]'(by omega) :=
          SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
        rw [← hidx]
        exact Sym2.mem_mk_right _ _
      · intro e f he hf hme hmf
        exact (last_edge_unique hqt hq2 he hme).trans (last_edge_unique hqt hq2 hf hmf).symm
  ------------------------------------------------------------------
  -- 2.  Apply 5.7
  ------------------------------------------------------------------
  have hnotrack := Thm58NoEvenTrackThroughAttachments.thm58NoEvenTrackThroughAttachments
    G hG n H K φ y hyK
  obtain ⟨hsix, -⟩ := _root_.Workspace.Statements.S05.SPGT.thm_5_7 H hsub.2
    ⟨m, J, hJ, ⟨ι, T, hι, htrack, hlenT, hrev, hdisjint, hnew, hcover, hedges⟩⟩ X hXE hnotrack
  refine ⟨[y], y, y, hPfrom, by simp, ?_⟩
  rcases hsix with hsat | hloc1 | hloc2 | hfour | hfive | hsix6
  ------------------------------------------------------------------
  -- 5.7.1 : `X` saturates `L(H)` — `y` would be major
  ------------------------------------------------------------------
  · exfalso
    apply hnomajor
    refine ⟨hyK, ?_⟩
    have hXeq : X = {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj y (↑(φ ⟨e, he⟩) : V)} := by
      rw [hXdef]
      ext e
      constructor
      · rintro ⟨he, hm⟩; exact ⟨he, (hattach e he).mp hm⟩
      · rintro ⟨he, hm⟩; exact ⟨he, (hattach e he).mpr hm⟩
    rw [← hXeq]
    exact hsat
  ------------------------------------------------------------------
  -- 5.7.2, 5.7.3 : `X` would be local
  ------------------------------------------------------------------
  · exact absurd (Or.inl hloc1) hnotlocal
  · exact absurd (Or.inr hloc2) hnotlocal
  ------------------------------------------------------------------
  -- 5.7.4  →  alternative 2(a)
  ------------------------------------------------------------------
  · obtain ⟨q, b₁, b₂, hbranch, hfrom, hXdiff⟩ := hfour
    have hq2 : 2 ≤ q.length := h2le q hbranch
    have hqt : IsTrackList H q := hbranch.1
    obtain ⟨hb₁bv, hb₂bv⟩ := hEndBV q b₁ b₂ hbranch hfrom
    have hb₁q : q[0]'(by omega) = b₁ := SubdivisionCounting.track_head hfrom (by omega)
    have hE0 : s(q[0]'(by omega), q[0 + 1]'(by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hqt 0 (by omega)
    have hEl : s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hqt (q.length - 2) (by omega)
    have hRpath : IsPathList G (TrackToRungPath.trackRung φ q hqt) :=
      TrackToRungPath.trackRung_isPathList φ q hqt (by simp only [trackLength]; omega)
    have hRset : ∀ x : V, x ∈ TrackToRungPath.trackRung φ q hqt ↔
        ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges q ∧
          x = (↑(φ ⟨e, he⟩) : V) := by
      intro x
      constructor
      · intro hx
        obtain ⟨k, hklen, hke⟩ := List.mem_iff_getElem.mp hx
        have hk : k < trackLength q := by
          rwa [TrackToRungPath.trackRung_length] at hklen
        have hk1 : k + 1 < q.length := by simp only [trackLength] at hk; omega
        have hE : s(q[k]'(by omega), q[k + 1]'hk1) ∈ H.edgeSet :=
          TrackToRungPath.trackEdge_mem_edgeSet hqt k hk1
        refine ⟨_, hE, ⟨k, hk1, rfl⟩, ?_⟩
        rw [← hke, TrackToRungPath.trackRung_getElem φ q hqt k hklen hk1 hE]
      · rintro ⟨e, he, ⟨k, hk1, hke⟩, rfl⟩
        have hklen : k < (TrackToRungPath.trackRung φ q hqt).length := by
          rw [TrackToRungPath.trackRung_length]; simp only [trackLength]; omega
        have hE : s(q[k]'(by omega), q[k + 1]'hk1) ∈ H.edgeSet :=
          TrackToRungPath.trackEdge_mem_edgeSet hqt k hk1
        have hval : (TrackToRungPath.trackRung φ q hqt)[k]'hklen = (↑(φ ⟨e, he⟩) : V) := by
          rw [TrackToRungPath.trackRung_getElem φ q hqt k hklen hk1 hE]
          exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V)) (Subtype.ext hke.symm)
        rw [← hval]
        exact List.getElem_mem hklen
    have hRsetEq : {x : V | x ∈ TrackToRungPath.trackRung φ q hqt} =
        {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges q ∧
          x = (↑(φ ⟨e, he⟩) : V)} := Set.ext hRset
    have hNb₁ : N b₁ ∩ {x : V | x ∈ TrackToRungPath.trackRung φ q hqt} =
        {(↑(φ ⟨s(q[0]'(by omega), q[0 + 1]'(by omega)), hE0⟩) : V)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx1, hx2⟩
        rw [hN b₁] at hx1
        obtain ⟨e, he, hein, rfl⟩ := hx1
        obtain ⟨e', he', hetr, hxe⟩ := (hRset _).mp hx2
        have hee : e = e' := congrArg Subtype.val (hφinj ⟨e, he⟩ ⟨e', he'⟩ hxe)
        have hetr' : e ∈ trackEdges q := by rw [hee]; exact hetr
        have hq0 : q[0]'(by omega) ∈ e := by rw [hb₁q]; exact hein.2
        exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V))
          (Subtype.ext (head_edge_unique hqt hq2 hetr' hq0))
      · rintro rfl
        refine ⟨?_, (hRset _).mpr ⟨_, hE0, ⟨0, by omega, rfl⟩, rfl⟩⟩
        rw [hN b₁]
        exact ⟨_, hE0, ⟨hE0, by rw [← hb₁q]; exact Sym2.mem_mk_left _ _⟩, rfl⟩
    have hNb₂ : N b₂ ∩ {x : V | x ∈ TrackToRungPath.trackRung φ q hqt} =
        {(↑(φ ⟨s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)), hEl⟩) : V)} := by
      have hb₂q : q[q.length - 1]'(by omega) = b₂ := by
        have h' := hfrom.2.2
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
        exact Option.some_injective _ h'
      have hidx : q[q.length - 2 + 1]'(by omega) = q[q.length - 1]'(by omega) :=
        SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx1, hx2⟩
        rw [hN b₂] at hx1
        obtain ⟨e, he, hein, rfl⟩ := hx1
        obtain ⟨e', he', hetr, hxe⟩ := (hRset _).mp hx2
        have hee : e = e' := congrArg Subtype.val (hφinj ⟨e, he⟩ ⟨e', he'⟩ hxe)
        have hetr' : e ∈ trackEdges q := by rw [hee]; exact hetr
        have hqL : q[q.length - 1]'(by omega) ∈ e := by rw [hb₂q]; exact hein.2
        exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V))
          (Subtype.ext (last_edge_unique hqt hq2 hetr' hqL))
      · rintro rfl
        refine ⟨?_, (hRset _).mpr ⟨_, hEl, ⟨q.length - 2, by omega, rfl⟩, rfl⟩⟩
        rw [hN b₂]
        refine ⟨_, hEl, ⟨hEl, ?_⟩, rfl⟩
        rw [← hb₂q, ← hidx]
        exact Sym2.mem_mk_right _ _
    refine Or.inr ⟨b₁, b₂, q, TrackToRungPath.trackRung φ q hqt, _, _,
      hb₁bv, hb₂bv, hbranch, hfrom, hRpath, hRsetEq, hNb₁, hNb₂, Or.inl ⟨?_, ?_, ?_⟩⟩
    · -- `y` is complete to `N b₁ \ {r₁}`
      rintro x ⟨hx1, hx2⟩
      rw [hN b₁] at hx1
      obtain ⟨e, he, hein, rfl⟩ := hx1
      have heX : e ∈ X := by
        by_cases hetr : e ∈ trackEdges q
        · exfalso
          apply hx2
          have hq0 : q[0]'(by omega) ∈ e := by rw [hb₁q]; exact hein.2
          exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V))
            (Subtype.ext (head_edge_unique hqt hq2 hetr hq0))
        · have : e ∈ X \ trackEdges q := by
            rw [hXdiff]; exact ⟨hein, hetr⟩
          exact this.1
      rw [hXdef] at heX
      obtain ⟨he', hm⟩ := heX
      exact (hattach e he').mp hm
    · -- `y` has a neighbour on the rung other than `r₁`
      by_contra hcon
      apply hnotlocal
      refine Or.inl ⟨b₁, hb₁bv, ?_⟩
      intro e heX
      by_cases hetr : e ∈ trackEdges q
      · have he : e ∈ H.edgeSet := hXE heX
        have hadj : G.Adj y (↑(φ ⟨e, he⟩) : V) := by
          rw [hXdef] at heX
          obtain ⟨he'', hm⟩ := heX
          exact (hattach e he'').mp hm
        have hmemR : (↑(φ ⟨e, he⟩) : V) ∈ TrackToRungPath.trackRung φ q hqt :=
          (hRset _).mpr ⟨e, he, hetr, rfl⟩
        have hEq : (↑(φ ⟨e, he⟩) : V) =
            (↑(φ ⟨s(q[0]'(by omega), q[0 + 1]'(by omega)), hE0⟩) : V) := by
          by_contra hne
          exact hcon ⟨_, ⟨hmemR, hne⟩, hadj⟩
        have hee : e = s(q[0]'(by omega), q[0 + 1]'(by omega)) :=
          congrArg Subtype.val (hφinj ⟨e, he⟩ ⟨_, hE0⟩ hEq)
        refine ⟨he, ?_⟩
        rw [hee, ← hb₁q]
        exact Sym2.mem_mk_left _ _
      · have : e ∈ X \ trackEdges q := ⟨heX, hetr⟩
        rw [hXdiff] at this
        exact this.1
    · -- there are no other edges
      intro x hx z hz hzr hadj
      have hxy : x = y := by simpa using hx
      rw [hxy] at hadj
      obtain ⟨e, he, rfl⟩ := hKimg z hz
      have heX : e ∈ X := by rw [hXdef]; exact ⟨he, (hattach e he).mpr hadj⟩
      by_cases hetr : e ∈ trackEdges q
      · exact Or.inr ⟨hxy, ⟨(hRset _).mpr ⟨e, he, hetr, rfl⟩, hzr⟩⟩
      · have hin : e ∈ incidentEdges H b₁ := by
          have : e ∈ X \ trackEdges q := ⟨heX, hetr⟩
          rw [hXdiff] at this
          exact this.1
        exact Or.inl ⟨hxy, ⟨by rw [hN b₁]; exact ⟨e, he, hin, rfl⟩, hzr⟩⟩
  ------------------------------------------------------------------
  -- 5.7.5  →  alternative 2(c)
  ------------------------------------------------------------------
  · obtain ⟨q, b₁, b₂, hbranch, hfrom, hodd, hXdiff⟩ := hfive
    have hq2 : 2 ≤ q.length := h2le q hbranch
    have hqt : IsTrackList H q := hbranch.1
    obtain ⟨hb₁bv, hb₂bv⟩ := hEndBV q b₁ b₂ hbranch hfrom
    have hb₁q : q[0]'(by omega) = b₁ := SubdivisionCounting.track_head hfrom (by omega)
    have hb₂q : q[q.length - 1]'(by omega) = b₂ := by
      have h' := hfrom.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
      exact Option.some_injective _ h'
    have hidx : q[q.length - 2 + 1]'(by omega) = q[q.length - 1]'(by omega) :=
      SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
    have hE0 : s(q[0]'(by omega), q[0 + 1]'(by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hqt 0 (by omega)
    have hEl : s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)) ∈ H.edgeSet :=
      TrackToRungPath.trackEdge_mem_edgeSet hqt (q.length - 2) (by omega)
    have hRpath : IsPathList G (TrackToRungPath.trackRung φ q hqt) :=
      TrackToRungPath.trackRung_isPathList φ q hqt (by simp only [trackLength]; omega)
    have hRset : ∀ x : V, x ∈ TrackToRungPath.trackRung φ q hqt ↔
        ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges q ∧
          x = (↑(φ ⟨e, he⟩) : V) := by
      intro x
      constructor
      · intro hx
        obtain ⟨k, hklen, hke⟩ := List.mem_iff_getElem.mp hx
        have hk : k < trackLength q := by
          rwa [TrackToRungPath.trackRung_length] at hklen
        have hk1 : k + 1 < q.length := by simp only [trackLength] at hk; omega
        have hE : s(q[k]'(by omega), q[k + 1]'hk1) ∈ H.edgeSet :=
          TrackToRungPath.trackEdge_mem_edgeSet hqt k hk1
        refine ⟨_, hE, ⟨k, hk1, rfl⟩, ?_⟩
        rw [← hke, TrackToRungPath.trackRung_getElem φ q hqt k hklen hk1 hE]
      · rintro ⟨e, he, ⟨k, hk1, hke⟩, rfl⟩
        have hklen : k < (TrackToRungPath.trackRung φ q hqt).length := by
          rw [TrackToRungPath.trackRung_length]; simp only [trackLength]; omega
        have hE : s(q[k]'(by omega), q[k + 1]'hk1) ∈ H.edgeSet :=
          TrackToRungPath.trackEdge_mem_edgeSet hqt k hk1
        have hval : (TrackToRungPath.trackRung φ q hqt)[k]'hklen = (↑(φ ⟨e, he⟩) : V) := by
          rw [TrackToRungPath.trackRung_getElem φ q hqt k hklen hk1 hE]
          exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V)) (Subtype.ext hke.symm)
        rw [← hval]
        exact List.getElem_mem hklen
    have hRsetEq : {x : V | x ∈ TrackToRungPath.trackRung φ q hqt} =
        {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet), e ∈ trackEdges q ∧
          x = (↑(φ ⟨e, he⟩) : V)} := Set.ext hRset
    have hNb₁ : N b₁ ∩ {x : V | x ∈ TrackToRungPath.trackRung φ q hqt} =
        {(↑(φ ⟨s(q[0]'(by omega), q[0 + 1]'(by omega)), hE0⟩) : V)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx1, hx2⟩
        rw [hN b₁] at hx1
        obtain ⟨e, he, hein, rfl⟩ := hx1
        obtain ⟨e', he', hetr, hxe⟩ := (hRset _).mp hx2
        have hee : e = e' := congrArg Subtype.val (hφinj ⟨e, he⟩ ⟨e', he'⟩ hxe)
        have hetr' : e ∈ trackEdges q := by rw [hee]; exact hetr
        have hq0 : q[0]'(by omega) ∈ e := by rw [hb₁q]; exact hein.2
        exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V))
          (Subtype.ext (head_edge_unique hqt hq2 hetr' hq0))
      · rintro rfl
        refine ⟨?_, (hRset _).mpr ⟨_, hE0, ⟨0, by omega, rfl⟩, rfl⟩⟩
        rw [hN b₁]
        exact ⟨_, hE0, ⟨hE0, by rw [← hb₁q]; exact Sym2.mem_mk_left _ _⟩, rfl⟩
    have hNb₂ : N b₂ ∩ {x : V | x ∈ TrackToRungPath.trackRung φ q hqt} =
        {(↑(φ ⟨s(q[q.length - 2]'(by omega), q[q.length - 2 + 1]'(by omega)), hEl⟩) : V)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx1, hx2⟩
        rw [hN b₂] at hx1
        obtain ⟨e, he, hein, rfl⟩ := hx1
        obtain ⟨e', he', hetr, hxe⟩ := (hRset _).mp hx2
        have hee : e = e' := congrArg Subtype.val (hφinj ⟨e, he⟩ ⟨e', he'⟩ hxe)
        have hetr' : e ∈ trackEdges q := by rw [hee]; exact hetr
        have hqL : q[q.length - 1]'(by omega) ∈ e := by rw [hb₂q]; exact hein.2
        exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V))
          (Subtype.ext (last_edge_unique hqt hq2 hetr' hqL))
      · rintro rfl
        refine ⟨?_, (hRset _).mpr ⟨_, hEl, ⟨q.length - 2, by omega, rfl⟩, rfl⟩⟩
        rw [hN b₂]
        refine ⟨_, hEl, ⟨hEl, ?_⟩, rfl⟩
        rw [← hb₂q, ← hidx]
        exact Sym2.mem_mk_right _ _
    refine Or.inr ⟨b₁, b₂, q, TrackToRungPath.trackRung φ q hqt, _, _,
      hb₁bv, hb₂bv, hbranch, hfrom, hRpath, hRsetEq, hNb₁, hNb₂,
      Or.inr (Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩))⟩
    · -- `y` is complete to `(N b₁ ∪ N b₂) \ {r₁, r₂}`
      rintro x ⟨hx1, hx2⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx2
      have heX : ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
          e ∈ X ∧ x = (↑(φ ⟨e, he⟩) : V) := by
        rcases hx1 with h | h
        · rw [hN b₁] at h
          obtain ⟨e, he, hein, rfl⟩ := h
          refine ⟨e, he, ?_, rfl⟩
          by_cases hetr : e ∈ trackEdges q
          · exfalso
            apply hx2.1
            have hq0 : q[0]'(by omega) ∈ e := by rw [hb₁q]; exact hein.2
            exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V))
              (Subtype.ext (head_edge_unique hqt hq2 hetr hq0))
          · have : e ∈ X \ trackEdges q := by
              rw [hXdiff]; exact ⟨Or.inl hein, hetr⟩
            exact this.1
        · rw [hN b₂] at h
          obtain ⟨e, he, hein, rfl⟩ := h
          refine ⟨e, he, ?_, rfl⟩
          by_cases hetr : e ∈ trackEdges q
          · exfalso
            apply hx2.2
            have hqL : q[q.length - 1]'(by omega) ∈ e := by rw [hb₂q]; exact hein.2
            exact congrArg (fun t : ↥H.edgeSet => (↑(φ t) : V))
              (Subtype.ext (last_edge_unique hqt hq2 hetr hqL))
          · have : e ∈ X \ trackEdges q := by
              rw [hXdiff]; exact ⟨Or.inr hein, hetr⟩
            exact this.1
      obtain ⟨e, he, hmem, rfl⟩ := heX
      rw [hXdef] at hmem
      obtain ⟨he', hm⟩ := hmem
      exact (hattach e he').mp hm
    · -- every neighbour of `y` in `K` lies in `N b₁ ∪ N b₂ ∪ V(R)`
      intro z hz hadj
      obtain ⟨e, he, rfl⟩ := hKimg z hz
      have heX : e ∈ X := by rw [hXdef]; exact ⟨he, (hattach e he).mpr hadj⟩
      by_cases hetr : e ∈ trackEdges q
      · exact Or.inr ((hRset _).mpr ⟨e, he, hetr, rfl⟩)
      · have hin : e ∈ incidentEdges H b₁ ∪ incidentEdges H b₂ := by
          have : e ∈ X \ trackEdges q := ⟨heX, hetr⟩
          rw [hXdiff] at this
          exact this.1
        rcases hin with h | h
        · exact Or.inl (Or.inl (by rw [hN b₁]; exact ⟨e, he, h, rfl⟩))
        · exact Or.inl (Or.inr (by rw [hN b₂]; exact ⟨e, he, h, rfl⟩))
    · -- the rung is even
      rw [TrackToRungPath.trackRung_pathLength]
      obtain ⟨k, hk⟩ := hodd
      rw [hk]
      exact ⟨k, by omega⟩
  ------------------------------------------------------------------
  -- 5.7.6  →  alternative 1
  ------------------------------------------------------------------
  · obtain ⟨c₁, c₂, -, hnb, hXeq6⟩ := hsix6
    refine Or.inl ⟨c₁, c₂, hnb, ?_, ?_, ?_⟩
    · intro x hx
      rw [hN c₁] at hx
      obtain ⟨e, he, hein, rfl⟩ := hx
      have heX : e ∈ X := by rw [hXeq6]; exact Or.inl hein
      rw [hXdef] at heX
      obtain ⟨he', hm⟩ := heX
      exact (hattach e he').mp hm
    · intro x hx
      rw [hN c₂] at hx
      obtain ⟨e, he, hein, rfl⟩ := hx
      have heX : e ∈ X := by rw [hXeq6]; exact Or.inr hein
      rw [hXdef] at heX
      obtain ⟨he', hm⟩ := heX
      exact (hattach e he').mp hm
    · intro x hx z hz hadj
      have hxy : x = y := by simpa using hx
      rw [hxy] at hadj
      obtain ⟨e, he, rfl⟩ := hKimg z hz
      have heX : e ∈ X := by rw [hXdef]; exact ⟨he, (hattach e he).mpr hadj⟩
      rw [hXeq6] at heX
      rcases heX with h | h
      · exact Or.inl ⟨hxy, by rw [hN c₁]; exact ⟨e, he, h, rfl⟩⟩
      · exact Or.inr ⟨hxy, by rw [hN c₂]; exact ⟨e, he, h, rfl⟩⟩

end Workspace.ProofLemmas.Thm58SingletonCase
