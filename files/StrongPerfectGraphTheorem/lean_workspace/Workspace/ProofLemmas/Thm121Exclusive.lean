import Mathlib
import Workspace.Types.Core
import Workspace.Types.Staircases

/-!
# The "exactly one" half of 12.1

PAPER (printed p. 69): *"… and let `v ∈ V(G) \ V(K)`.  Then **exactly one** of the following
holds: …"*

The printed proof of 12.1 establishes only that at least one of the three alternatives holds
(its cases (1)–(4), formalized in `Workspace.ProofLemmas.Thm121Cases`); that no two of them can
hold simultaneously is left implicit by the authors, and is the content of this module.  It is a
direct consequence of the definitions, and needs nothing beyond the staircase axioms:

* a **minor** vertex has a local neighbourhood, i.e. its neighbours in `V(K)` lie inside one of
  `V(S)`, `V(R₀)`, `A ∪ {a₀}`, `B ∪ {b₀}`, whereas a **major** vertex has neighbours in each of
  `A`, `B` and `V(R₀)` — and `V(R₀)` is disjoint from `V(S) = A ∪ B ∪ C`, since `R₀` is a
  banister; so no vertex is both;
* a **left-star** is complete to `A` and, if alternative 3 holds for it, has a neighbour in
  `R₀ \ a₀`; those two neighbours already escape every one of the four local sets, so no
  left-star of alternative 3 is minor (and symmetrically for a right-star);
* a **left-star** is anticomplete to `B ∪ C`, so it has no neighbour in `B` and is therefore not
  major (and symmetrically a right-star is anticomplete to `A ∪ C`).

Also proved here is the bookkeeping lemma turning "one of three, no two of three" into the
`∃! i : Fin 3` form in which 12.1 is stated.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm121Exclusive

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT

/-- *"Exactly one of the following holds"*, for three alternatives listed in order: it is
equivalent to the disjunction together with the three pairwise exclusions. -/
theorem existsUnique_fin3 {P₁ P₂ P₃ : Prop} (h : P₁ ∨ P₂ ∨ P₃)
    (h12 : ¬ (P₁ ∧ P₂)) (h13 : ¬ (P₁ ∧ P₃)) (h23 : ¬ (P₂ ∧ P₃)) :
    ∃! i : Fin 3, ![P₁, P₂, P₃] i := by
  rcases h with h | h | h
  · refine ⟨0, by simpa using h, ?_⟩
    intro j hj; fin_cases j <;> simp_all
  · refine ⟨1, by simpa using h, ?_⟩
    intro j hj; fin_cases j <;> simp_all
  · refine ⟨2, by simpa using h, ?_⟩
    intro j hj; fin_cases j <;> simp_all

/-- **No two of the three alternatives of 12.1 hold at once.** -/
theorem thm121Exclusive {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : IsStaircase G A C B a₀ R₀ b₀) (v : V) :
    ¬ ((MinorForStaircase G A C B a₀ R₀ b₀ v ∧
          (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
          (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∧
        (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
          (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
            CentralForStaircase G A C B a₀ R₀ b₀ v))) ∧
      ¬ ((MinorForStaircase G A C B a₀ R₀ b₀ v ∧
          (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
          (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∧
        ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
          (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x))) ∧
      ¬ ((MajorForStaircase G A C B a₀ R₀ b₀ v ∧
          (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
            CentralForStaircase G A C B a₀ R₀ b₀ v)) ∧
        ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
          (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x))) := by
  obtain ⟨hSC, hban, -⟩ := hK
  obtain ⟨⟨hAB, -, -⟩, ⟨hAne, hBne⟩, -⟩ := hSC
  -- `R₀` is a banister, so none of its vertices lies in `V(S) = A ∪ B ∪ C`.
  have hR₀S : ∀ w ∈ R₀, w ∉ A ∪ B ∪ C := hban.2.1
  have ha₀R : a₀ ∈ R₀ := List.mem_of_mem_head? (by rw [hban.1.2.1]; rfl)
  have hb₀R : b₀ ∈ R₀ := List.mem_of_mem_getLast? (by rw [hban.1.2.2]; rfl)
  have hnbA : ∀ x, x ∈ A → G.Adj v x →
      x ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ := by
    intro x hx hadj; exact ⟨hadj, Or.inr (Or.inl (Or.inl hx))⟩
  have hnbB : ∀ x, x ∈ B → G.Adj v x →
      x ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ := by
    intro x hx hadj; exact ⟨hadj, Or.inr (Or.inl (Or.inr hx))⟩
  have hnbR : ∀ x, x ∈ R₀ → G.Adj v x →
      x ∈ G.neighborSet v ∩ staircaseVertices A C B R₀ := by
    intro x hx hadj; exact ⟨hadj, Or.inl hx⟩
  refine ⟨?_, ?_, ?_⟩
  · -- minor and major are incompatible
    rintro ⟨⟨⟨-, hloc⟩, -, -⟩, ⟨-, ⟨x, hxA, hvx⟩, ⟨y, hyB, hvy⟩, z, hzR, hvz⟩, -⟩
    rcases hloc with h | h | h | h
    · exact hR₀S z hzR (h (hnbR z hzR hvz))
    · exact hR₀S x (h (hnbA x hxA hvx)) (Or.inl (Or.inl hxA))
    · rcases h (hnbB y hyB hvy) with hy' | hy'
      · exact (Set.disjoint_left.mp hAB hy') hyB
      · exact hR₀S a₀ ha₀R (Or.inl (Or.inr (hy' ▸ hyB)))
    · rcases h (hnbA x hxA hvx) with hx' | hx'
      · exact (Set.disjoint_left.mp hAB hxA) hx'
      · exact hR₀S b₀ hb₀R (Or.inl (Or.inl (hx' ▸ hxA)))
  · -- minor and alternative 3 are incompatible
    rintro ⟨⟨⟨-, hloc⟩, -, -⟩, hP3⟩
    obtain ⟨a, haA⟩ := hAne
    obtain ⟨b, hbB⟩ := hBne
    rcases hP3 with ⟨hls, x, hxR, hxa, hvx⟩ | ⟨hrs, x, hxR, hxb, hvx⟩
    · have hva : G.Adj v a := hls.2.1 a haA
      rcases hloc with h | h | h | h
      · exact hR₀S x hxR (h (hnbR x hxR hvx))
      · exact hR₀S a (h (hnbA a haA hva)) (Or.inl (Or.inl haA))
      · rcases h (hnbR x hxR hvx) with hx' | hx'
        · exact hR₀S x hxR (Or.inl (Or.inl hx'))
        · exact hxa hx'
      · rcases h (hnbA a haA hva) with ha' | ha'
        · exact (Set.disjoint_left.mp hAB haA) ha'
        · exact hR₀S b₀ hb₀R (Or.inl (Or.inl (ha' ▸ haA)))
    · have hvb : G.Adj v b := hrs.2.1 b hbB
      rcases hloc with h | h | h | h
      · exact hR₀S x hxR (h (hnbR x hxR hvx))
      · exact hR₀S b (h (hnbB b hbB hvb)) (Or.inl (Or.inr hbB))
      · rcases h (hnbB b hbB hvb) with hb' | hb'
        · exact (Set.disjoint_left.mp hAB hb') hbB
        · exact hR₀S a₀ ha₀R (Or.inl (Or.inr (hb' ▸ hbB)))
      · rcases h (hnbR x hxR hvx) with hx' | hx'
        · exact hR₀S x hxR (Or.inl (Or.inr hx'))
        · exact hxb hx'
  · -- major and alternative 3 are incompatible
    rintro ⟨⟨⟨-, ⟨x, hxA, hvx⟩, ⟨y, hyB, hvy⟩, -⟩, -⟩, hP3⟩
    rcases hP3 with ⟨hls, -⟩ | ⟨hrs, -⟩
    · exact hls.2.2 y (Or.inl hyB) hvy
    · exact hrs.2.2 x (Or.inl hxA) hvx

end Workspace.ProofLemmas.Thm121Exclusive
