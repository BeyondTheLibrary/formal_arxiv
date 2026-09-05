import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Appearances
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry
import Workspace.ProofLemmas.PathBasics
import Workspace.Statements.S12.Thm_12_1

set_option autoImplicit false

/-!
# The classification paragraph of the proof of 13.4

PAPER (§13, printed p. 84, the paragraph immediately preceding claim (1) of the
proof of 13.4): *"… there is a strongly maximal staircase
`K = (S = (A, C, B), a₀-R₀-b₀)` say in `G`.  Let `A₀` be the set of all
left-stars, `B₀` the set of all right-stars, and `N` the set of all vertices
that are `A ∪ B`-complete.  By 12.1, every non-major `A`-complete vertex is in
`A₀`, and since there is no 3-breaker, every major `A`-complete vertex is in
`N`, so every `A`-complete vertex is in `A₀ ∪ N`; and similarly every
`B`-complete vertex is in `B₀ ∪ N`.  Let `H = G \ (V(S) ∪ A₀ ∪ B₀ ∪ N)`."*

The proof below follows that sentence literally.

* `12.1` (`Workspace.Statements.S12.SPGT.thm_12_1`) splits a vertex outside
  `V(K)` into three kinds.  In its first alternative, an `A`-complete vertex is
  forced to be a left-star; in its third, it is a left-star (a right-star is
  `A`-anticomplete, so cannot be `A`-complete).
* In the second alternative the vertex is *major*.  If such a vertex `v` is
  `A`-complete but not `A ∪ B`-complete, then `v` is not `B`-complete, and — `v`
  being major — has a neighbour in `B`, so is not `B`-anticomplete; hence
  `(K', v)` is a 3-breaker, where `K'` is the same staircase read backwards,
  `(S' = (B, C, A), b₀-R₀ʳ-a₀)`.  That is the paper's *"since there is no
  3-breaker"*, and the left–right transport is
  `Workspace.ProofLemmas.StaircaseLeftRightSymmetry`.  The `B`-complete half of
  the sentence uses the 3-breaker for `K` itself.

Everything else in the conclusion is bookkeeping about the six classes: they are
pairwise disjoint and disjoint from `V(S)`, no vertex of `H = H₀` is
`A`-complete, `B`-complete, a star or major, and the interior of the banister
`R₀` lies in `H₀` (it is anticomplete to `V(S)`).

The only fact needed about the strip itself is that no vertex of `V(S)` outside
`A` is `A`-complete: every vertex of `V(S)` lies in a step, and the two rungs of
a step carry no edges beyond `a₁a₂` and `b₁b₂`.
-/

namespace Workspace.ProofLemmas.StrongStaircaseVertexClassification

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances.SPGT

theorem strongStaircaseVertexClassification
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hBerge : Berge H)
    (hK4 : ¬ Appears H (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism H s t R₁ R₂ R₃)
    (h1breaker : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker H A' C' B' F Q)
    (h3breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' x : V),
      IsThreeBreaker H A' C' B' a₀' R₀' b₀' x)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hstairs : StronglyMaximalStaircase H A C B a₀ R₀ b₀) :
    let VS : Set V := A ∪ B ∪ C
    let A₀ : Set V := {v : V | IsLeftStar H A C B v}
    let B₀ : Set V := {v : V | IsRightStar H A C B v}
    let N : Set V := {v : V | VertexComplete H v (A ∪ B)}
    let H₀ : Set V := Set.univ \ (VS ∪ A₀ ∪ B₀ ∪ N)
    (Disjoint A₀ B₀ ∧ Disjoint A₀ N ∧ Disjoint B₀ N) ∧
    (Disjoint A₀ VS ∧ Disjoint B₀ VS ∧ Disjoint N VS) ∧
    (∀ v : V, VertexComplete H v A → v ∈ A₀ ∪ N) ∧
    (∀ v : V, VertexComplete H v B → v ∈ B₀ ∪ N) ∧
    (∀ v : V, v ∉ VS → MajorForStaircase H A C B a₀ R₀ b₀ v →
      VertexComplete H v A ∨ VertexComplete H v B) ∧
    (∀ v ∈ H₀, ¬ VertexComplete H v A ∧ ¬ VertexComplete H v B ∧
      ¬ IsLeftStar H A C B v ∧ ¬ IsRightStar H A C B v ∧
      ¬ MajorForStaircase H A C B a₀ R₀ b₀ v) ∧
    {v : V | v ∈ interior R₀} ⊆ H₀ := by
  intro VS A₀ B₀ N H₀
  -- the staircase data
  have hmaxst : MaximalStaircase H A C B a₀ R₀ b₀ := hstairs.1
  have hsc : StepConnected H A C B := hstairs.1.1.1
  have hban : IsBanister H A C B a₀ R₀ b₀ := hstairs.1.1.2.1
  have hpath : IsPathFrom H R₀ a₀ b₀ := hban.1
  have hls : IsLeftStar H A C B a₀ := hban.2.2.1
  have hrs : IsRightStar H A C B b₀ := hban.2.2.2.1
  obtain ⟨⟨hAB, _hAC, _hBC⟩, ⟨hAne, hBne⟩, _hrung, hstep, _hpart⟩ := hsc
  obtain ⟨aw, haw⟩ := hAne
  obtain ⟨bw, hbw⟩ := hBne
  have hnAB : ∀ x : V, x ∈ A → x ∈ B → False := fun x hx hx' =>
    (Set.disjoint_left.mp hAB hx) hx'
  ---------------------------------------------------------------------------
  -- Stars are never complete to the far side of the strip.
  ---------------------------------------------------------------------------
  have hRightStarNotA : ∀ v : V, IsRightStar H A C B v → ¬ VertexComplete H v A :=
    fun v h hc => h.2.2 aw (Or.inl haw) (hc aw haw)
  have hLeftStarNotB : ∀ v : V, IsLeftStar H A C B v → ¬ VertexComplete H v B :=
    fun v h hc => h.2.2 bw (Or.inl hbw) (hc bw hbw)
  ---------------------------------------------------------------------------
  -- No vertex of `V(S)` outside `A` is `A`-complete (and symmetrically).
  ---------------------------------------------------------------------------
  have hstepNotA : ∀ v : V, v ∈ A ∪ B ∪ C → v ∉ A → ¬ VertexComplete H v A := by
    intro v hv hvA hcomp
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hmem⟩ := hstep v hv
    obtain ⟨hr1, hr2, -, hadj⟩ := hs
    have ha₁A : a₁ ∈ A := hr1.2.1
    have hb₁B : b₁ ∈ B := hr1.2.2.1
    have ha₂A : a₂ ∈ A := hr2.2.1
    have hb₂B : b₂ ∈ B := hr2.2.2.1
    have ha₁mem : a₁ ∈ R₁ := PathBasics.head_mem hr1.1.2.1
    have ha₂mem : a₂ ∈ R₂ := PathBasics.head_mem hr2.1.2.1
    rcases hmem with h | h
    · rcases (hadj v h a₂ ha₂mem).mp (hcomp a₂ ha₂A) with ⟨he, -⟩ | ⟨-, he⟩
      · exact hvA (by rw [he]; exact ha₁A)
      · exact hnAB a₂ ha₂A (by rw [he]; exact hb₂B)
    · rcases (hadj a₁ ha₁mem v h).mp (hcomp a₁ ha₁A).symm with ⟨-, he⟩ | ⟨he, -⟩
      · exact hvA (by rw [he]; exact ha₂A)
      · exact hnAB a₁ ha₁A (by rw [he]; exact hb₁B)
  have hstepNotB : ∀ v : V, v ∈ A ∪ B ∪ C → v ∉ B → ¬ VertexComplete H v B := by
    intro v hv hvB hcomp
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hmem⟩ := hstep v hv
    obtain ⟨hr1, hr2, -, hadj⟩ := hs
    have ha₁A : a₁ ∈ A := hr1.2.1
    have hb₁B : b₁ ∈ B := hr1.2.2.1
    have ha₂A : a₂ ∈ A := hr2.2.1
    have hb₂B : b₂ ∈ B := hr2.2.2.1
    have hb₁mem : b₁ ∈ R₁ := PathBasics.getLast_mem hr1.1.2.2
    have hb₂mem : b₂ ∈ R₂ := PathBasics.getLast_mem hr2.1.2.2
    rcases hmem with h | h
    · rcases (hadj v h b₂ hb₂mem).mp (hcomp b₂ hb₂B) with ⟨-, he⟩ | ⟨he, -⟩
      · exact hnAB a₂ ha₂A (by rw [← he]; exact hb₂B)
      · exact hvB (by rw [he]; exact hb₁B)
    · rcases (hadj b₁ hb₁mem v h).mp (hcomp b₁ hb₁B).symm with ⟨he, -⟩ | ⟨-, he⟩
      · exact hnAB a₁ ha₁A (by rw [← he]; exact hb₁B)
      · exact hvB (by rw [he]; exact hb₂B)
  have hVSnotA : ∀ v : V, v ∈ A ∪ B ∪ C → ¬ VertexComplete H v A := by
    intro v hv hcomp
    by_cases hvA : v ∈ A
    · exact H.irrefl (hcomp v hvA)
    · exact hstepNotA v hv hvA hcomp
  have hVSnotB : ∀ v : V, v ∈ A ∪ B ∪ C → ¬ VertexComplete H v B := by
    intro v hv hcomp
    by_cases hvB : v ∈ B
    · exact H.irrefl (hcomp v hvB)
    · exact hstepNotB v hv hvB hcomp
  ---------------------------------------------------------------------------
  -- No vertex of `R₀` other than `a₀` is `A`-complete (and symmetrically).
  ---------------------------------------------------------------------------
  have hRnotA : ∀ v : V, v ∈ R₀ → v ≠ a₀ → ¬ VertexComplete H v A := by
    intro v hv hne hcomp
    by_cases hb : v = b₀
    · subst hb
      exact hrs.2.2 aw (Or.inl haw) (hcomp aw haw)
    · have hint : v ∈ interior R₀ :=
        (PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hne, hb⟩
      exact hban.2.2.2.2 v hint aw (Or.inl (Or.inl haw)) (hcomp aw haw)
  have hRnotB : ∀ v : V, v ∈ R₀ → v ≠ b₀ → ¬ VertexComplete H v B := by
    intro v hv hne hcomp
    by_cases ha : v = a₀
    · subst ha
      exact hls.2.2 bw (Or.inl hbw) (hcomp bw hbw)
    · have hint : v ∈ interior R₀ :=
        (PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, ha, hne⟩
      exact hban.2.2.2.2 v hint bw (Or.inl (Or.inr hbw)) (hcomp bw hbw)
  have hAcompNotInK : ∀ v : V, VertexComplete H v A → v ≠ a₀ →
      v ∉ staircaseVertices A C B R₀ := by
    intro v hcomp hne hmem
    rcases hmem with hR | hV
    · exact hRnotA v hR hne hcomp
    · exact hVSnotA v hV hcomp
  have hBcompNotInK : ∀ v : V, VertexComplete H v B → v ≠ b₀ →
      v ∉ staircaseVertices A C B R₀ := by
    intro v hcomp hne hmem
    rcases hmem with hR | hV
    · exact hRnotB v hR hne hcomp
    · exact hVSnotB v hV hcomp
  ---------------------------------------------------------------------------
  -- 12.1, in disjunctive form.
  ---------------------------------------------------------------------------
  have hclass : ∀ v : V, v ∉ staircaseVertices A C B R₀ →
      (MinorForStaircase H A C B a₀ R₀ b₀ v ∧
        (IsLeftStar H A C B v ∨ ¬ VertexComplete H v A) ∧
        (IsRightStar H A C B v ∨ ¬ VertexComplete H v B)) ∨
      (MajorForStaircase H A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal H A C B a₀ R₀ b₀ v ∨ RightDiagonal H A C B a₀ R₀ b₀ v ∨
          CentralForStaircase H A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar H A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ H.Adj v x) ∨
        (IsRightStar H A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ H.Adj v x)) := by
    intro v hv
    obtain ⟨i, hi, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1 H hBerge hK4 heven
      h1breaker A C B a₀ b₀ R₀ hmaxst v hv
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  ---------------------------------------------------------------------------
  -- A major vertex is never minor.
  ---------------------------------------------------------------------------
  have hmajor_not_minor : ∀ v : V, MajorForStaircase H A C B a₀ R₀ b₀ v →
      ¬ MinorForStaircase H A C B a₀ R₀ b₀ v := by
    intro v hmaj hmin
    obtain ⟨-, ⟨x, hxA, hax⟩, ⟨y, hyB, hay⟩, ⟨z, hzR, haz⟩⟩ := hmaj
    have hxnb : x ∈ H.neighborSet v ∩ staircaseVertices A C B R₀ :=
      ⟨hax, Or.inr (Or.inl (Or.inl hxA))⟩
    have hynb : y ∈ H.neighborSet v ∩ staircaseVertices A C B R₀ :=
      ⟨hay, Or.inr (Or.inl (Or.inr hyB))⟩
    have hznb : z ∈ H.neighborSet v ∩ staircaseVertices A C B R₀ :=
      ⟨haz, Or.inl hzR⟩
    rcases hmin.2 with h | h | h | h
    · exact hban.2.1 z hzR (h hznb)
    · exact hban.2.1 x (h hxnb) (Or.inl (Or.inl hxA))
    · rcases h hynb with hyA | hya0
      · exact hnAB y hyA hyB
      · exact hls.1 (Or.inl (Or.inr ((Set.mem_singleton_iff.mp hya0) ▸ hyB)))
    · rcases h hxnb with hxB | hxb0
      · exact hnAB x hxA hxB
      · exact hrs.1 (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hxb0) ▸ hxA)))
  ---------------------------------------------------------------------------
  -- The staircase read backwards, for the 3-breaker of the `A`-complete half.
  ---------------------------------------------------------------------------
  have svrev : staircaseVertices B C A R₀.reverse = staircaseVertices A C B R₀ := by
    ext w
    simp only [staircaseVertices, Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
    tauto
  have hstairsRev : StronglyMaximalStaircase H B C A b₀ R₀.reverse a₀ :=
    StaircaseLeftRightSymmetry.stronglyMaximalStaircase_swap.mp hstairs
  ---------------------------------------------------------------------------
  -- "every `A`-complete vertex is in `A₀ ∪ N`"
  ---------------------------------------------------------------------------
  have hAcomp : ∀ v : V, VertexComplete H v A → v ∈ A₀ ∪ N := by
    intro v hcomp
    by_cases hva : v = a₀
    · subst hva
      exact Or.inl hls
    · have hvK := hAcompNotInK v hcomp hva
      rcases hclass v hvK with ⟨-, hs1, -⟩ | ⟨hmaj, -⟩ | (⟨hstar, -⟩ | ⟨hstar, -⟩)
      · rcases hs1 with hstar | hnc
        · exact Or.inl hstar
        · exact absurd hcomp hnc
      · right
        by_contra hnN
        have hnB : ¬ VertexComplete H v B := by
          intro hB
          refine hnN ?_
          intro x hx
          rcases hx with h | h
          · exact hcomp x h
          · exact hB x h
        have hnBanti : ¬ VertexAnticomplete H v B := by
          intro hanti
          obtain ⟨y, hyB, hadjy⟩ := hmaj.2.2.1
          exact hanti y hyB hadjy
        exact h3breaker ⟨B, C, A, b₀, R₀.reverse, a₀, v, hstairsRev,
          (by rw [svrev]; exact hvK), hcomp, hnB, hnBanti⟩
      · exact Or.inl hstar
      · exact absurd hcomp (hRightStarNotA v hstar)
  ---------------------------------------------------------------------------
  -- "and similarly every `B`-complete vertex is in `B₀ ∪ N`"
  ---------------------------------------------------------------------------
  have hBcomp : ∀ v : V, VertexComplete H v B → v ∈ B₀ ∪ N := by
    intro v hcomp
    by_cases hvb : v = b₀
    · subst hvb
      exact Or.inl hrs
    · have hvK := hBcompNotInK v hcomp hvb
      rcases hclass v hvK with ⟨-, -, hs2⟩ | ⟨hmaj, -⟩ | (⟨hstar, -⟩ | ⟨hstar, -⟩)
      · rcases hs2 with hstar | hnc
        · exact Or.inl hstar
        · exact absurd hcomp hnc
      · right
        by_contra hnN
        have hnA : ¬ VertexComplete H v A := by
          intro hA
          refine hnN ?_
          intro x hx
          rcases hx with h | h
          · exact hA x h
          · exact hcomp x h
        have hnAanti : ¬ VertexAnticomplete H v A := by
          intro hanti
          obtain ⟨y, hyA, hadjy⟩ := hmaj.2.1
          exact hanti y hyA hadjy
        exact h3breaker ⟨A, C, B, a₀, R₀, b₀, v, hstairs, hvK, hcomp, hnA, hnAanti⟩
      · exact absurd hcomp (hLeftStarNotB v hstar)
      · exact Or.inl hstar
  ---------------------------------------------------------------------------
  -- major vertices outside `V(S)` are `A`- or `B`-complete
  ---------------------------------------------------------------------------
  have hmajorComplete : ∀ v : V, v ∉ VS → MajorForStaircase H A C B a₀ R₀ b₀ v →
      VertexComplete H v A ∨ VertexComplete H v B := by
    intro v _ hmaj
    rcases hclass v hmaj.1 with ⟨hmin, -⟩ | ⟨-, hd⟩ | (⟨hstar, -⟩ | ⟨hstar, -⟩)
    · exact absurd hmin (hmajor_not_minor v hmaj)
    · rcases hd with hL | hR | hCn
      · exact Or.inl fun x hx => hL.2 x (Or.inl hx)
      · exact Or.inr fun x hx => hR.2 x (Or.inl hx)
      · exact Or.inl fun x hx => hCn.2.1 x (Or.inl hx)
    · exact Or.inl hstar.2.1
    · exact Or.inr hstar.2.1
  ---------------------------------------------------------------------------
  -- assembling the seven conclusions
  ---------------------------------------------------------------------------
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hAcomp, hBcomp, hmajorComplete, ?_, ?_⟩
  · -- `A₀` and `B₀` are disjoint
    refine Set.disjoint_left.mpr ?_
    intro v hvA₀ hvB₀
    exact hRightStarNotA v hvB₀ hvA₀.2.1
  · -- `A₀` and `N` are disjoint
    refine Set.disjoint_left.mpr ?_
    intro v hvA₀ hvN
    exact hLeftStarNotB v hvA₀ (fun x hx => hvN x (Or.inr hx))
  · -- `B₀` and `N` are disjoint
    refine Set.disjoint_left.mpr ?_
    intro v hvB₀ hvN
    exact hRightStarNotA v hvB₀ (fun x hx => hvN x (Or.inl hx))
  · exact Set.disjoint_left.mpr fun v hv => hv.1
  · exact Set.disjoint_left.mpr fun v hv => hv.1
  · refine Set.disjoint_left.mpr ?_
    intro v hvN hvVS
    exact hVSnotA v hvVS (fun x hx => hvN x (Or.inl hx))
  · -- nothing in `H₀` is complete to `A` or to `B`, a star, or major
    intro v hv
    have hv2 : v ∉ VS ∪ A₀ ∪ B₀ ∪ N := hv.2
    have hvVS : v ∉ VS := fun h => hv2 (Or.inl (Or.inl (Or.inl h)))
    have hvA₀ : v ∉ A₀ := fun h => hv2 (Or.inl (Or.inl (Or.inr h)))
    have hvB₀ : v ∉ B₀ := fun h => hv2 (Or.inl (Or.inr h))
    have hvN : v ∉ N := fun h => hv2 (Or.inr h)
    refine ⟨?_, ?_, hvA₀, hvB₀, ?_⟩
    · intro hc
      rcases hAcomp v hc with h | h
      · exact hvA₀ h
      · exact hvN h
    · intro hc
      rcases hBcomp v hc with h | h
      · exact hvB₀ h
      · exact hvN h
    · intro hmaj
      rcases hmajorComplete v hvVS hmaj with hc | hc
      · rcases hAcomp v hc with h | h
        · exact hvA₀ h
        · exact hvN h
      · rcases hBcomp v hc with h | h
        · exact hvB₀ h
        · exact hvN h
  · -- the interior of the banister lies in `H₀`
    intro v hv
    have hvR : v ∈ R₀ := PathBasics.interior_subset hv
    have hanti : VertexAnticomplete H v (A ∪ B ∪ C) := hban.2.2.2.2 v hv
    refine ⟨trivial, ?_⟩
    rintro (((hc | hc) | hc) | hc)
    · exact hban.2.1 v hvR hc
    · exact hanti aw (Or.inl (Or.inl haw)) (hc.2.1 aw haw)
    · exact hanti bw (Or.inl (Or.inr hbw)) (hc.2.1 bw hbw)
    · exact hanti aw (Or.inl (Or.inl haw)) (hc aw (Or.inl haw))

end Workspace.ProofLemmas.StrongStaircaseVertexClassification
