import Workspace.ProofLemmas.Thm58StarStarGeometry
import Workspace.ProofLemmas.Thm58StarStarHoles
import Workspace.ProofLemmas.Thm58StarStarNonadjacentGap
import Workspace.ProofLemmas.Thm58StarStarAdjacentGap

/-!
# The three remaining constructions in 5.8 (3) and (4)

Each lemma below is one sentence of the printed proof: a pair of paths of `L(H)` built from
tracks of `H`, completed through `F` into two holes.  Everything else in claims (3) and (4) is
proved in `Thm58StarStar.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58StarStarGaps

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ : Fin n}

variable (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)

include h

/-- GAP — PAPER, proof of 5.8 claim (3), printed p. 26: *"Certainly `A₁` and `A₂` are both
nonempty, so there is a track in `H` from `v₁` to `v₂` with end-edges in `A₁` and `A₂`
respectively.  Hence there is a path `S₁` in `L(H)` from `A₁` to `A₂`, vertex-disjoint from
`N_{v₁} ∪ N_{v₂}` except for its ends. ...  Hence we can apply 5.6, and we deduce (possibly
after exchanging `v₁` and `v₂`) that there is a path `S₂` in `L(H)` with first vertex in `A₁`,
second vertex in `B₁`, last vertex in `A₂`, and otherwise disjoint from `N_{v₁} ∪ N_{v₂}`.
Since `H` is bipartite, `S₁` and `S₂` have opposite parity; but they can both be completed via
`F`, a contradiction."*

The hypothesis is that at least one of `B₁`, `B₂` is nonempty; the conclusion is the pair of
holes of different parity that the last sentence produces. -/
theorem nonadjacent_parity_gap
    (hnb : ¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (hB : (∃ x ∈ N c₁, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂, ¬ G.Adj p₂ x)) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  exact Thm58StarStarNonadjacentGap.holes h hnb hB

variable {q : List (Fin n)} {R : List V} {r₁ r₂ : V}

/-- GAP — PAPER, proof of 5.8 claim (4), printed p. 27: *"Suppose that both `B₁` and `B₂` are
empty.  There is a cycle in `J` of length ≥ 4 using the edge `v₁v₂`, and so there is a path in
`L(H)` of length ≥ 2 from `A₁` to `A₂` with no internal vertex in
`N_{v₁} ∪ V(R_{v₁v₂}) ∪ N_{v₂}`.  The union of this path with `R_{v₁v₂}` induces a hole, and so
does its union with `F`, and therefore these two paths have lengths of the same parity."* -/
theorem adjacent_both_complete_parity_gap
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB₁ : ∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hB₂ : ∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x) :
    (Even (pathLength P) ↔ Even (pathLength R)) := by
  classical
  obtain ⟨T, a₁, a₂, hT, hTK, hT3, ha₁, hp₁, ha₂, hp₂, hint⟩ :=
    Thm58StarStarAdjacentGap.exists_crossPath h hq hfrom hq2 hR hRset hi₁ hi₂ hA₁ hA₂ hB₁ hB₂
  have hinterR := Thm58StarStarAdjacentGap.inter_subset_rung h hq hfrom hq2 hRset
  have ha₁ne : a₁ ≠ r₁ := by simpa using ha₁.2
  have ha₂ne : a₂ ≠ r₂ := by simpa using ha₂.2
  have ha₁R : a₁ ∉ R := Thm58StarStarAdjacentGap.not_mem_rung₁ h hi₁ ha₁.1 ha₁ne
  have ha₂R : a₂ ∉ R := Thm58StarStarAdjacentGap.not_mem_rung₂ h hi₂ ha₂.1 ha₂ne
  have ha₂not₁ : a₂ ∉ N c₁ := fun hc => ha₂R (hinterR ⟨hc, ha₂.1⟩)
  have ha₁not₂ : a₁ ∉ N c₂ := fun hc => ha₁R (hinterR ⟨ha₁.1, hc⟩)
  have hTR : ∀ x ∈ T, x ∉ R := by
    intro x hx
    by_cases hx₁ : x = a₁
    · exact hx₁ ▸ ha₁R
    by_cases hx₂ : x = a₂
    · exact hx₂ ▸ ha₂R
    · exact (hint x hx hx₁ hx₂).2.2
  have hTedge : ∀ x ∈ T, x ∉ edgeImage φ (trackEdges q) := by
    intro x hx hmem
    have hxR : x ∈ {y : V | y ∈ R} := by rw [hRset]; exact hmem
    exact hTR x hx hxR
  have hr₁ := Thm58StarStarAdjacentGap.mem_rung₁ h hi₁
  have hr₂ := Thm58StarStarAdjacentGap.mem_rung₂ h hi₂
  have hcross : ∀ x ∈ T, ∀ y ∈ R, (G.Adj x y ↔ (x = a₂ ∧ y = r₂) ∨ (x = a₁ ∧ y = r₁)) := by
    intro x hx y hy
    constructor
    · intro hadj
      have hyE : y ∈ edgeImage φ (trackEdges q) := by rw [← hRset]; exact hy
      rcases adj_rung_imp (star_eq h) hq hfrom (hTK x hx) (hTedge x hx) hyE hadj with
        ⟨hx₁, hy₁⟩ | ⟨hx₂, hy₂⟩
      · have hyr : y = r₁ := by
          have hmem : y ∈ N c₁ ∩ {z : V | z ∈ R} := ⟨hy₁, hy⟩
          rw [hi₁] at hmem
          exact hmem
        by_cases hxa₁ : x = a₁
        · exact Or.inr ⟨hxa₁, hyr⟩
        by_cases hxa₂ : x = a₂
        · exact absurd (hxa₂ ▸ hx₁) ha₂not₁
        · exact absurd hx₁ (hint x hx hxa₁ hxa₂).1
      · have hyr : y = r₂ := by
          have hmem : y ∈ N c₂ ∩ {z : V | z ∈ R} := ⟨hy₂, hy⟩
          rw [hi₂] at hmem
          exact hmem
        by_cases hxa₂ : x = a₂
        · exact Or.inl ⟨hxa₂, hyr⟩
        by_cases hxa₁ : x = a₁
        · exact absurd (hxa₁ ▸ hx₂) ha₁not₂
        · exact absurd hx₂ (hint x hx hxa₁ hxa₂).2.1
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact star_adj (star_eq h) c₂ ha₂.1 hr₂.1 ha₂ne
      · exact star_adj (star_eq h) c₁ ha₁.1 hr₁.1 ha₁ne
  have hRpos : 0 < R.length := PathBasics.path_length_pos hR.1
  have hC : IsHoleList G (T ++ R.reverse) :=
    hole_of_two_paths hT hR hTR hcross (by omega)
  have hcompl : Completion G K (N c₁ ∩ N c₂) p₁ p₂ T a₁ a₂ := by
    refine ⟨hT, hTK, hp₁, hp₂, ?_, ?_, ?_, ?_⟩
    · intro x hx hadj
      have hxN : x ∈ N c₁ := first_adj_mem h (hTK x hx) hadj
      by_cases hxa₁ : x = a₁
      · exact hxa₁
      by_cases hxa₂ : x = a₂
      · exact absurd (hxa₂ ▸ hxN) ha₂not₁
      · exact absurd hxN (hint x hx hxa₁ hxa₂).1
    · intro x hx hadj
      have hxN : x ∈ N c₂ := last_adj_mem h (hTK x hx) hadj
      by_cases hxa₂ : x = a₂
      · exact hxa₂
      by_cases hxa₁ : x = a₁
      · exact absurd (hxa₁ ▸ hxN) ha₁not₂
      · exact absurd hxN (hint x hx hxa₁ hxa₂).2.1
    · intro x hx hmem
      exact hTR x hx (hinterR hmem)
    · intro hcon
      exact ha₁R (hinterR ⟨ha₁.1, hcon ▸ ha₂.1⟩)
  have hD : IsHoleList G (T ++ P.reverse) := hole_of_completion h hcompl
  have hCe := (berge h).1 _ hC
  have hDe := (berge h).1 _ hD
  have hP2 := two_le_length h
  simp only [holeLength, List.length_append, List.length_reverse, Nat.even_iff] at hCe hDe
  simp only [pathLength, Nat.even_iff]
  omega

/-- GAP — PAPER, proof of 5.8 claim (4), printed p. 27: *"So we may assume that at least one of
`B₁`, `B₂` is nonempty. ...  Since `H` is bipartite, `S₁` and `S₂` have opposite parity; but
they can both be completed via `F`, a contradiction.  Consequently there is a vertex
`w ∈ V(J)` with `A₁ ∪ A₂ ⊆ N_w`. ...  But `T` can be completed to a hole via
`r₁-R_{v₁v₂}-r₂-a₂-a₃` and via `r₁-p₁-⋯-pₙ-a₂-a₃`, and these two completions have different
parity, a contradiction."*

Both branches of that argument end in two holes of different parity, which is the conclusion
below. -/
theorem adjacent_parity_gap
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB : (∃ x ∈ N c₁ \ {r₁}, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂ \ {r₂}, ¬ G.Adj p₂ x)) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  classical
  by_cases hw : ∃ w : Fin n, (∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x → x ∈ N w) ∧
      (∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x → x ∈ N w)
  · exact Thm58StarStarAdjacentGap.covered_holes h hq hfrom hq2 hR hRset hi₁ hi₂ hA₁ hA₂ hB hw
  · exact Thm58StarStarAdjacentGap.holes_of_not_covered h hq hfrom hq2 hR hRset hi₁ hi₂
      hA₁ hA₂ hB hw

end Workspace.ProofLemmas.Thm58StarStarGaps
