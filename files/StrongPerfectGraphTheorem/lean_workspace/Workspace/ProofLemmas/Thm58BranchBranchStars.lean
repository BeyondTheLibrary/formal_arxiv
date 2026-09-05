import Workspace.ProofLemmas.Thm58BranchBranchBasics

/-!
# The conclusion when each end has two adjacent neighbors

PAPER (5.8 (7), printed p. 28): "If `p₁` has exactly two neighbours in
`R_{u₁v₁}` and they are adjacent, and also `pₙ` has exactly two neighbours in
`R_{u₂v₂}` and they are adjacent, then statement 1 of the theorem holds."

The common endpoint in `H` of each pair is internal to its branch. Its degree is
two, so the pair is its whole star. The two internal vertices cannot lie in a
common branch, because the original branches have different edge sets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- The endpoint's neighbors in the appearance are exactly one adjacent pair. -/
def TwoAdjacentNeighbors (G : SimpleGraph V) (K : Set V) (p : V) : Prop :=
  ∃ a b : V, a ∈ K ∧ b ∈ K ∧ G.Adj a b ∧
    ∀ y ∈ K, G.Adj p y ↔ y = a ∨ y = b

/-- A common endpoint of two distinct edges of a track is internal to it. -/
theorem internal_of_two_edges {q : List (Fin n)} (hnd : q.Nodup)
    {e f : Sym2 (Fin n)} (he : e ∈ trackEdges q) (hf : f ∈ trackEdges q)
    (hef : e ≠ f) {c : Fin n} (hce : c ∈ e) (hcf : c ∈ f) :
    c ∈ trackInterior q := by
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hf
  rw [SubdivisionCounting.mem_trackInterior_iff]
  rcases Sym2.mem_iff.mp hce with h₁ | h₁ <;>
    rcases Sym2.mem_iff.mp hcf with h₂ | h₂
  · have hij : i = j := hnd.getElem_inj_iff.mp (h₁.symm.trans h₂)
    subst j
    exact (hef rfl).elim
  · have hij : i = j + 1 := hnd.getElem_inj_iff.mp (h₁.symm.trans h₂)
    exact ⟨j, by omega, h₂.symm⟩
  · have hij : i + 1 = j := hnd.getElem_inj_iff.mp (h₁.symm.trans h₂)
    exact ⟨i, by omega, h₁.symm⟩
  · have hij : i + 1 = j + 1 := hnd.getElem_inj_iff.mp (h₁.symm.trans h₂)
    have hij' : i = j := by omega
    subst j
    exact (hef rfl).elim

/-- The adjacent pair of neighbors is exactly the star of an internal vertex. -/
theorem pair_is_internal_star
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q : List (Fin n)} (hq : IsBranch H q)
    (hX : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q)
    (hpair : TwoAdjacentNeighbors G K p₁) :
    ∃ c ∈ trackInterior q, ∀ y ∈ K, G.Adj p₁ y ↔ y ∈ N c := by
  obtain ⟨a, b, haK, hbK, hab, hp⟩ := hpair
  let e := φ.symm ⟨a, haK⟩
  let f := φ.symm ⟨b, hbK⟩
  have hea : (↑(φ e) : V) = a := congrArg Subtype.val (φ.apply_symm_apply ⟨a, haK⟩)
  have hfb : (↑(φ f) : V) = b := congrArg Subtype.val (φ.apply_symm_apply ⟨b, hbK⟩)
  have hpF : p₁ ∈ F := by
    rw [← h.2.2.2.2.2.2.2.1]
    exact PathBasics.head_mem h.2.2.2.2.2.2.1.2.1
  have hpa : G.Adj p₁ a := (hp a haK).mpr (Or.inl rfl)
  have hpb : G.Adj p₁ b := (hp b hbK).mpr (Or.inr rfl)
  have heq : e.1 ∈ trackEdges q := hX
    ⟨e.2, hea.symm ▸ haK, p₁, ⟨hpF, ends_ne h⟩, hea.symm ▸ hpa.symm⟩
  have hfq : f.1 ∈ trackEdges q := hX
    ⟨f.2, hfb.symm ▸ hbK, p₁, ⟨hpF, ends_ne h⟩, hfb.symm ▸ hpb.symm⟩
  have hefadj : H.lineGraph.Adj e f := by
    apply φ.map_rel_iff.mp
    change G.Adj (↑(φ e) : V) (↑(φ f) : V)
    rwa [hea, hfb]
  obtain ⟨hef, c, hce, hcf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hefadj
  have hef' : e.1 ≠ f.1 := fun hval => hef (Subtype.ext hval)
  have hcint := internal_of_two_edges hq.1.2.1 heq hfq hef' hce hcf
  have hpairsub : ({e.1, f.1} : Set (Sym2 (Fin n))) ⊆ incidentEdges H c := by
    rintro d (rfl | rfl)
    · exact ⟨e.2, hce⟩
    · exact ⟨f.2, hcf⟩
  have hstar : incidentEdges H c = {e.1, f.1} := by
    apply (Set.eq_of_subset_of_ncard_le hpairsub ?_ (Set.toFinite _)).symm
    rw [Thm84RungEndDictionary.incidentEdges_ncard, Set.ncard_pair hef']
    have hnot := hq.2.1 c hcint
    change ¬ 3 ≤ (H.neighborSet c).ncard at hnot
    omega
  have hN : N c = {a, b} := by
    rw [h.2.2.2.1 c]
    ext y
    constructor
    · rintro ⟨g, hg, hgc, rfl⟩
      rw [hstar] at hgc
      rcases hgc with hge | hgf
      · left
        exact (congrArg (fun d : H.edgeSet => (↑(φ d) : V)) (Subtype.ext hge)).trans hea
      · right
        exact (congrArg (fun d : H.edgeSet => (↑(φ d) : V))
          (Subtype.ext (show g = f.1 from hgf))).trans hfb
    · rintro (rfl | rfl)
      · exact ⟨e.1, e.2, ⟨e.2, hce⟩, hea.symm⟩
      · exact ⟨f.1, f.2, ⟨f.2, hcf⟩, hfb.symm⟩
  refine ⟨c, hcint, ?_⟩
  intro y hyK
  rw [hN]
  exact hp y hyK

/-- The first alternative follows from the two adjacent neighbor pairs. -/
theorem outcome_of_two_pairs
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    (hpair₁ : TwoAdjacentNeighbors G K p₁) (hpair₂ : TwoAdjacentNeighbors G K p₂) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  obtain ⟨c₁, hc₁, hstar₁⟩ := pair_is_internal_star h hq₁ hX₁ hpair₁
  obtain ⟨c₂, hc₂, hstar₂⟩ := pair_is_internal_star (ready_reverse h) hq₂ hX₂ hpair₂
  have hNK : ∀ c, N c ⊆ K := by
    intro c y hy
    rw [h.2.2.2.1 c] at hy
    obtain ⟨e, he, _, rfl⟩ := hy
    exact (φ ⟨e, he⟩).2
  refine Or.inl ⟨c₁, c₂, ?_, ?_, ?_, ?_⟩
  · rintro ⟨r, hr, hc₁r, hc₂r⟩
    have he₁ := branch_edges_eq_of_internal h.2.1 h.2.2.1.1 hq₁ hr hc₁ hc₁r
    have he₂ := branch_edges_eq_of_internal h.2.1 h.2.2.1.1 hq₂ hr hc₂ hc₂r
    exact branches_ne h hq₁ hX₁ hX₂ (he₁.trans he₂.symm)
  · intro y hy
    exact (hstar₁ y (hNK c₁ hy)).mpr hy
  · intro y hy
    exact (hstar₂ y (hNK c₂ hy)).mpr hy
  · intro x hx y hy hxy
    have hxF : x ∈ F := h.2.2.2.2.2.2.2.1 ▸ hx
    rcases adjacent_vertex_is_end h hq₁ hq₂ hX₁ hX₂ hxF hy hxy with rfl | rfl
    · exact Or.inl ⟨rfl, (hstar₁ y hy).mp hxy⟩
    · exact Or.inr ⟨rfl, (hstar₂ y hy).mp hxy⟩

end Workspace.ProofLemmas.Thm58BranchBranch
