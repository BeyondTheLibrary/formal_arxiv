import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Knots
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.Statements.S05.Thm_5_8
import Workspace.Statements.S09.Thm_9_2

/-!
# 9.3, case (1): the appeal to 5.8

PAPER (proof of 9.3, printed p. 48, inside claim (1)):

> *"So we assume there is no such `f`, and hence we may apply 5.8."*

This module discharges the three non-trivial hypotheses of 5.8 in that situation and returns
5.8's conclusion verbatim.  The knot `(P₁,P₂,Q₁,Q₂)` with `Q₁,Q₂` of length `1` induces a
degenerate appearance `K = L(H)` of `K₄` (`Workspace.ProofLemmas.AppearanceFromKnot`), whose
data is taken here as hypotheses so that this module stays free of that construction; the
three hypotheses of 5.8 are then obtained as follows.

* *`J` is 3-connected*: `J = K₄`, `SubdivisionCounting.k4_three_connected`.
* *the set of attachments is not local for `L(H)`*: this is **9.2**, first bullet — *"`X` is
  local with respect to the knot if and only if it is local with respect to `L(H)`"* — applied
  to `X = attachments G F K`, together with the hypothesis of 9.3 that that set is not local
  with respect to the knot.
* *no member of `F` is major*: *"major"* is `SaturatesLineGraph` of the neighbour set, i.e.
  *"at most one edge of `δ_H(v)` is missed, for each branch-vertex `v`"*; with the four
  branch-vertices `c₁,…,c₄` of the degenerate appearance carrying the four triangles

  ```
  N c₁ = {x₁, x₂, a₁}      N c₂ = {x₁, y₂, a₂}
  N c₃ = {y₁, y₂, b₁}      N c₄ = {y₁, x₂, b₂}
  ```

  this is exactly the paper's own gloss *"it has two neighbours in every triangle of `K`"*,
  which is the form in which `Workspace.ProofLemmas.Thm93Case1Major` leaves claim (1).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm93Case1FiveEight

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every attachment of `F` in `K` lies in `K`. -/
theorem attachments_subset (G : SimpleGraph V) (F K : Set V) : attachments G F K ⊆ K :=
  fun _ hv => hv.1

/-- **The triangle form of `SaturatesLineGraph` at a branch-vertex.**

`N c` is the `φ`-image of `δ_H(c)`, and `φ` is injective, so *"at most one edge of `δ_H(c)` is
not a neighbour of `x`"* is *"at most one vertex of the triangle `N c` is not a neighbour of
`x`"* — the paper's *"`x` has two neighbours in every triangle of `K`"*. -/
theorem subsingleton_triangle_of_subsingleton_incident
    {n : ℕ} {G : SimpleGraph V} {H : SimpleGraph (Fin n)} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ v = (↑(φ ⟨e, he⟩) : V)})
    (x : V) (c : Fin n)
    (h : (incidentEdges H c \
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj x (↑(φ ⟨e, he⟩) : V)}).Subsingleton) :
    (N c \ G.neighborSet x).Subsingleton := by
  intro u hu v hv
  obtain ⟨hu₁, hu₂⟩ := hu
  obtain ⟨hv₁, hv₂⟩ := hv
  rw [hN c] at hu₁ hv₁
  obtain ⟨e, he, hec, rfl⟩ := hu₁
  obtain ⟨e', he', hec', rfl⟩ := hv₁
  have hmem : e ∈ incidentEdges H c \
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj x (↑(φ ⟨e, he⟩) : V)} := by
    refine ⟨hec, ?_⟩
    rintro ⟨he₂, hadj⟩
    exact hu₂ hadj
  have hmem' : e' ∈ incidentEdges H c \
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, G.Adj x (↑(φ ⟨e, he⟩) : V)} := by
    refine ⟨hec', ?_⟩
    rintro ⟨he₂, hadj⟩
    exact hv₂ hadj
  have : e = e' := h hmem hmem'
  subst this
  rfl

/-- **The appeal to 5.8 inside claim (1) of the proof of 9.3.**

PAPER: *"So we assume there is no such `f`, and hence we may apply 5.8."*

The hypotheses `hbv`, `hNc₁`–`hNc₄` and `hN` are the part of the output of
`Workspace.ProofLemmas.AppearanceFromKnot.appearanceFromKnot` that is used; `hnomaj` is the
second alternative of `Workspace.ProofLemmas.Thm93Case1Major.case1_saturating_dichotomy`. -/
theorem five_eight_in_case_one
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hQ1len : pathLength Q₁ = 1) (hQ2len : pathLength Q₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (n : ℕ) (H : SimpleGraph (Fin n)) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ v = (↑(φ ⟨e, he⟩) : V)})
    (c₁ c₂ c₃ c₄ : Fin n)
    (hbv : branchVertices H = ({c₁, c₂, c₃, c₄} : Set (Fin n)))
    (hNc₁ : N c₁ = ({x₁, x₂, a₁} : Set V)) (hNc₂ : N c₂ = ({x₁, y₂, a₂} : Set V))
    (hNc₃ : N c₃ = ({y₁, y₂, b₁} : Set V)) (hNc₄ : N c₄ = ({y₁, x₂, b₂} : Set V))
    (F : Set V) (hFsub : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G F K))
    (hnomaj : ∀ f ∈ F, ¬ ((({x₁, x₂, a₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({x₁, y₂, a₂} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, y₂, b₁} : Set V) \ G.neighborSet f).Subsingleton ∧
      (({y₁, x₂, b₂} : Set V) \ G.neighborSet f).Subsingleton)) :
    ∃ (P : List V) (p₁ p₂ : V), IsPathFrom G P p₁ p₂ ∧ (∀ x ∈ P, x ∈ F) ∧
      ((∃ c₁' c₂' : Fin n,
          (¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁' ∈ q ∧ c₂' ∈ q) ∧
          (∀ x ∈ N c₁', G.Adj p₁ x) ∧ (∀ x ∈ N c₂', G.Adj p₂ x) ∧
          (∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ N c₁') ∨ (x = p₂ ∧ y ∈ N c₂'))) ∨
       (∃ (d₁ d₂ : Fin n) (q : List (Fin n)) (R : List V) (r₁ r₂ : V),
          d₁ ∈ branchVertices H ∧ d₂ ∈ branchVertices H ∧
          IsBranch H q ∧ IsTrackFrom H q d₁ d₂ ∧
          IsPathList G R ∧
          {x : V | x ∈ R} =
            {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
              e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)} ∧
          N d₁ ∩ {x : V | x ∈ R} = {r₁} ∧ N d₂ ∩ {x : V | x ∈ R} = {r₂} ∧
          (((∀ x ∈ N d₁ \ {r₁}, G.Adj p₁ x) ∧
            (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
           ((∀ x ∈ N d₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N d₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
              (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N d₂ \ {r₂}) ∨
              (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
            (Even (pathLength P) ↔ Even (pathLength R))) ∨
           (p₁ = p₂ ∧ (∀ x ∈ (N d₁ ∪ N d₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
            (∀ y ∈ K, G.Adj p₁ y → y ∈ N d₁ ∪ N d₂ ∪ {z : V | z ∈ R}) ∧
            Even (pathLength R)) ∨
           (r₁ = r₂ ∧ (∀ x ∈ N d₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N d₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N d₂ \ {r₂})) ∧
            Even (pathLength P))))) := by
  -- PAPER: *"we may apply 5.8"*.
  refine _root_.Workspace.Statements.S05.SPGT.thm_5_8 G hG 4 (⊤ : SimpleGraph (Fin 4))
    SubdivisionCounting.k4_three_connected n H K happ.1 φ N hN F hFsub hFconn ?_ ?_
  · -- *"the set of attachments of `F` in `L(H)` is not local"* — this is **9.2**, first bullet.
    intro hloc
    refine hFattach ?_
    exact ((_root_.Workspace.Statements.S09.SPGT.thm_9_2 G P₁ P₂ Q₁ Q₂ hknot K hK
      hQ1len hQ2len n H φ happ (attachments G F K)
      (attachments_subset G F K)).1).mpr hloc
  · -- *"no member of `F` is major"* — the four triangles of `K`.
    intro f hf hmaj
    refine hnomaj f hf ⟨?_, ?_, ?_, ?_⟩
    · rw [← hNc₁]
      exact subsingleton_triangle_of_subsingleton_incident φ N hN f c₁
        (hmaj.2 c₁ (by rw [hbv]; simp))
    · rw [← hNc₂]
      exact subsingleton_triangle_of_subsingleton_incident φ N hN f c₂
        (hmaj.2 c₂ (by rw [hbv]; simp))
    · rw [← hNc₃]
      exact subsingleton_triangle_of_subsingleton_incident φ N hN f c₃
        (hmaj.2 c₃ (by rw [hbv]; simp))
    · rw [← hNc₄]
      exact subsingleton_triangle_of_subsingleton_incident φ N hN f c₄
        (hmaj.2 c₄ (by rw [hbv]; simp))

end Workspace.ProofLemmas.Thm93Case1FiveEight
