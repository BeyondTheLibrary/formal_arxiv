import Workspace.ProofLemmas.Thm58StarStarGaps
import Workspace.ProofLemmas.Thm58StarBranch

/-!
# The star-star case of 5.8, claims (3) and (4)

Both attachment sets sit in vertex stars.  The two star vertices are either nonadjacent in `J`
(claim (3)) or adjacent (claim (4)).  In claim (4) the paper reduces two of the subcases to
claim (2), once with the ends of the outside path exchanged, so the conclusion is stated for
one of the two orientations of `P`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStar

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ : Fin n}

/-- Two holes of different parity contradict Bergeness. -/
theorem no_parity_pair (hG : Berge G)
    (hCD : ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2) :
    False := by
  obtain ⟨C, D, hC, hD, hne⟩ := hCD
  obtain ⟨u, hu⟩ := hG.1 C hC
  obtain ⟨v, hv⟩ := hG.1 D hD
  simp only [holeLength] at hu hv
  omega

variable (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

/-- PAPER claim (3), printed p. 26: nonadjacent star vertices give alternative 1. -/
theorem nonadjacent (hnb : ¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ := by
  classical
  have hdisj : Disjoint (N c₁) (N c₂) := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact hnb ⟨[c₁, c₂], isBranch_pair h (star_inter_adj h ⟨hx₁, hx₂⟩), by simp, by simp⟩
  have key : ¬ ((∃ x ∈ N c₁, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂, ¬ G.Adj p₂ x)) := fun hB =>
    no_parity_pair (berge h) (Thm58StarStarGaps.nonadjacent_parity_gap h hnb hB)
  push Not at key
  refine Or.inl ⟨c₁, c₂, hnb, key.1, key.2, ?_⟩
  intro x hx y hy ha
  by_cases hx₁ : x = p₁
  · exact Or.inl ⟨hx₁, first_adj_mem h hy (hx₁ ▸ ha)⟩
  by_cases hx₂ : x = p₂
  · exact Or.inr ⟨hx₂, last_adj_mem h hy (hx₂ ▸ ha)⟩
  · have hm := mid_adj_mem h hx hx₁ hx₂ hy ha
    exact absurd hm.2 (Set.disjoint_left.mp hdisj hm.1)

/-- PAPER claim (4), printed p. 27: adjacent star vertices.  Two of the subcases are the paper's
appeal to claim (2), the second one with the ends exchanged. -/
theorem adjacent {q : List (Fin n)}
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ ∨
      Thm58Setup.Outcome G n H K φ N P.reverse p₂ p₁ := by
  classical
  obtain ⟨R, r₁, r₂, hR, hRset, hi₁, hi₂⟩ :=
    Thm58StarStarGeometry.rung_intersections (N := N) h.ready.2.2.2.1 hfrom hq2
  have hinterR : N c₁ ∩ N c₂ ⊆ {x : V | x ∈ R} := by
    rw [hRset]
    exact Thm58StarStarGeometry.stars_inter_subset_rung h hq hfrom hq2
  have hinter₁ : ∀ x ∈ N c₁ ∩ N c₂, x = r₁ := by
    intro x hx
    have : x ∈ N c₁ ∩ {y : V | y ∈ R} := ⟨hx.1, hinterR hx⟩
    rw [hi₁] at this
    exact this
  have hinter₂ : ∀ x ∈ N c₁ ∩ N c₂, x = r₂ := by
    intro x hx
    have : x ∈ N c₂ ∩ {y : V | y ∈ R} := ⟨hx.2, hinterR hx⟩
    rw [hi₂] at this
    exact this
  have hr₁R : r₁ ∈ {x : V | x ∈ R} := by
    have : r₁ ∈ N c₁ ∩ {y : V | y ∈ R} := by rw [hi₁]; rfl
    exact this.2
  have hr₂R : r₂ ∈ {x : V | x ∈ R} := by
    have : r₂ ∈ N c₂ ∩ {y : V | y ∈ R} := by rw [hi₂]; rfl
    exact this.2
  -- the two exits from the star--branch case
  by_cases hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x
  · by_cases hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x
    · by_cases hB : (∃ x ∈ N c₁ \ {r₁}, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂ \ {r₂}, ¬ G.Adj p₂ x)
      · exact absurd (Thm58StarStarGaps.adjacent_parity_gap h hq hfrom hq2 hR hRset hi₁ hi₂
          hA₁ hA₂ hB) (fun hh => no_parity_pair (berge h) hh)
      · push Not at hB
        obtain ⟨hB₁, hB₂⟩ := hB
        have hpar := Thm58StarStarGaps.adjacent_both_complete_parity_gap h hq hfrom hq2 hR
          hRset hi₁ hi₂ hA₁ hA₂ hB₁ hB₂
        refine Or.inl (Or.inr ⟨c₁, c₂, q, R, r₁, r₂, h.star₁, h.star₂, hq, hfrom, hR.1,
          hRset, hi₁, hi₂, ?_⟩)
        by_cases hrr : r₁ = r₂
        · -- alternative 2(d): the branch is a single vertex of `L(H)`
          have hlen : pathLength R = 0 := by
            by_contra hlen
            exact (PathBasics.isPathFrom_ends_ne hR (by omega)) hrr
          refine Or.inr (Or.inr (Or.inr ⟨hrr, hB₁, hB₂, ?_, ?_⟩))
          · intro x hx y hy hyr ha
            by_cases hx₁ : x = p₁
            · exact Or.inl ⟨hx₁, first_adj_mem h hy (hx₁ ▸ ha), hyr⟩
            by_cases hx₂ : x = p₂
            · exact Or.inr ⟨hx₂, last_adj_mem h hy (hx₂ ▸ ha),
                fun hcon => hyr (hcon.trans hrr.symm)⟩
            · exact absurd (hinter₁ y (mid_adj_mem h hx hx₁ hx₂ hy ha)) hyr
          · rw [hpar, hlen]
            simp
        · -- alternative 2(b): the two stars are disjoint
          refine Or.inr (Or.inl ⟨hB₁, hB₂, ?_, hpar⟩)
          intro x hx y hy ha
          by_cases hx₁ : x = p₁
          · have hyN := first_adj_mem h hy (hx₁ ▸ ha)
            by_cases hyr : y = r₁
            · exact Or.inr (Or.inr (Or.inl ⟨hx₁, hyr⟩))
            · exact Or.inl ⟨hx₁, hyN, hyr⟩
          by_cases hx₂ : x = p₂
          · have hyN := last_adj_mem h hy (hx₂ ▸ ha)
            by_cases hyr : y = r₂
            · exact Or.inr (Or.inr (Or.inr ⟨hx₂, hyr⟩))
            · exact Or.inr (Or.inl ⟨hx₂, hyN, hyr⟩)
          · have hm := mid_adj_mem h hx hx₁ hx₂ hy ha
            exact absurd ((hinter₁ y hm).symm.trans (hinter₂ y hm)) hrr
    · -- `A₂` is empty: the second attachment set lies in the branch, so claim (2) applies
      push Not at hA₂
      have hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (φ ⟨e, he⟩ : V) ∈ attachments G (F \ {p₂}) K} ⊆ incidentEdges H c₁ := by
        rintro e ⟨he, hatt⟩
        apply (image_mem_iff (φ := φ) he).mp
        rw [← star_eq h c₁]
        exact h.first hatt
      have hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          (φ ⟨e, he⟩ : V) ∈ attachments G (F \ {p₁}) K} ⊆ trackEdges q := by
        rintro e ⟨he, hatt⟩
        have hmem : (φ ⟨e, he⟩ : V) = r₂ := by
          obtain ⟨hxK, z, ⟨hzF, hz₁⟩, hza⟩ := hatt
          by_cases hz₂ : z = p₂
          · by_contra hne
            exact hA₂ _ ⟨h.last ⟨hxK, z, ⟨hzF, hz₁⟩, hza⟩, hne⟩ (hz₂ ▸ hza.symm)
          · exact hinter₂ _ (mid_adj_mem h (mem_path h hzF) hz₁ hz₂ hxK hza.symm)
        apply (image_mem_iff (φ := φ) he).mp
        rw [hmem, ← hRset]
        exact hr₂R
      exact Or.inl (Thm58StarBranch.starBranch h.ready h.star₁ hq hX₁ hX₂)
  · -- `A₁` is empty: the first attachment set lies in the branch, so claim (2) applies
    -- to the reversed path
    push Not at hA₁
    have hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (φ ⟨e, he⟩ : V) ∈ attachments G (F \ {p₁}) K} ⊆ incidentEdges H c₂ := by
      rintro e ⟨he, hatt⟩
      apply (image_mem_iff (φ := φ) he).mp
      rw [← star_eq h c₂]
      exact h.last hatt
    have hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (φ ⟨e, he⟩ : V) ∈ attachments G (F \ {p₂}) K} ⊆ trackEdges q := by
      rintro e ⟨he, hatt⟩
      have hmem : (φ ⟨e, he⟩ : V) = r₁ := by
        obtain ⟨hxK, z, ⟨hzF, hz₂⟩, hza⟩ := hatt
        by_cases hz₁ : z = p₁
        · by_contra hne
          exact hA₁ _ ⟨h.first ⟨hxK, z, ⟨hzF, hz₂⟩, hza⟩, hne⟩ (hz₁ ▸ hza.symm)
        · exact hinter₁ _ (mid_adj_mem h (mem_path h hzF) hz₁ hz₂ hxK hza.symm)
      apply (image_mem_iff (φ := φ) he).mp
      rw [hmem, ← hRset]
      exact hr₁R
    exact Or.inr (Thm58StarBranch.starBranch (Thm58BranchBranch.ready_reverse h.ready)
      h.star₂ hq hX₁ hX₂)

omit h in
/-- PAPER claims (3) and (4), printed pp. 26--27.  The orientation of `P` is the paper's
*"possibly after exchanging `v₁` and `v₂`"*. -/
theorem starStar
    (hready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    (hc₁ : c₁ ∈ branchVertices H) (hc₂ : c₂ ∈ branchVertices H)
    (hX₁ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₂}) K} ⊆ incidentEdges H c₁)
    (hX₂ : {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₁}) K} ⊆ incidentEdges H c₂) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ ∨
      Thm58Setup.Outcome G n H K φ N P.reverse p₂ p₁ := by
  classical
  have hfirst : attachments G (F \ {p₂}) K ⊆ N c₁ := by
    rw [hready.2.2.2.1 c₁]
    exact attachments_subset_image hX₁
  have hlast : attachments G (F \ {p₁}) K ⊆ N c₂ := by
    rw [hready.2.2.2.1 c₂]
    exact attachments_subset_image hX₂
  have h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂ := ⟨hready, hc₁, hc₂, hfirst, hlast⟩
  by_cases hbr : ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q
  · obtain ⟨q, hq, hq₁, hq₂⟩ := hbr
    obtain ⟨Q, hQ, hQfrom, -⟩ := Thm58StarStarGeometry.orient_branch h hq hq₁ hq₂
    have hQ2 : 2 ≤ Q.length := by
      have h0 : 0 < Q.length := List.length_pos_of_ne_nil hQfrom.1.1
      by_contra hcon
      have hone : Q.length = 1 := by omega
      obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hone
      subst hz
      have e₁ : z = c₁ := by simpa using hQfrom.2.1
      have e₂ : z = c₂ := by simpa using hQfrom.2.2
      exact stars_ne h (e₁ ▸ e₂ ▸ rfl)
    exact adjacent h hQ hQfrom hQ2
  · exact Or.inl (nonadjacent h hbr)

end Workspace.ProofLemmas.Thm58StarStar
