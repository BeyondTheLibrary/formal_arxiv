import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.FiveHoleBasics
import Workspace.Statements.S17.Thm_17_1

/-!
# The two applications of 17.1 in the first paragraph of claim (8) of 19.2

PAPER (printed p. 121):

> *"For assume `x₂` is nonadjacent to `y` and adjacent to `x₀` say.  Now `A ∪ {x₁}` catches
> the triangle `{z,x₀,x₂}`; it contains no reflection of this triangle, since `x₀,x₁` have
> no common neighbour in `A`; and the unique neighbour of `z` in this set is nonadjacent to
> both `x₀,x₂`.  So by 17.1 it follows that there is a vertex in `A` adjacent to both
> `x₀,x₂`.  Also, `A ∪ x₂` catches the triangle `{z,x₁,y}`.  Suppose that `A ∪ {x₂}`
> contains a reflection of this triangle; then there exists `f ∈ A` adjacent to `x₁,x₂` and
> not to `y`.  Since `f ∈ A` it follows that `f` is nonadjacent to `x₀`; but then
> `f-x₂-x₀-y-x₁-f` is an odd hole, a contradiction.  Hence by 17.1 there is a vertex in `A`
> adjacent to both `x₁,y`."*

Both applications have the same shape: the partner of `z` in a reflection has to be the one
vertex of `F` adjacent to `z` (all of `A` misses `z`), and then the partner of a second
triangle vertex lies in `A` and is adjacent to that first partner.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim8Triangles

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem triple_distinct {a b c : V} (h : ({a, b, c} : Set V).ncard = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have pair_le : ∀ p q : V, ({p, q} : Set V).ncard ≤ 2 := by
    intro p q
    have hh := Set.ncard_insert_le p ({q} : Set V)
    simpa using hh
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have he : ({a, a, c} : Set V) = {a, c} := by ext; simp
    rw [he] at h
    exact (by have := pair_le a c; omega)
  · have he : ({a, b, a} : Set V) = {a, b} := by ext; simp; tauto
    rw [he] at h
    exact (by have := pair_le a b; omega)
  · have he : ({a, b, b} : Set V) = {a, b} := by ext; simp
    rw [he] at h
    exact (by have := pair_le a b; omega)

/-- Every vertex of the first triangle of a reflection has a matched partner in the second,
and no other vertex of the first triangle is adjacent to that partner. -/
private theorem reflection_partner {G : SimpleGraph V} {a₀ a₁ a₂ b₀ b₁ b₂ u : V}
    (h : IsReflectionOfTriangle G a₀ a₁ a₂ b₀ b₁ b₂)
    (hu : u ∈ ({a₀, a₁, a₂} : Set V)) :
    ∃ v ∈ ({b₀, b₁, b₂} : Set V), G.Adj u v ∧
      ∀ w ∈ ({a₀, a₁, a₂} : Set V), w ≠ u → ¬ G.Adj w v := by
  obtain ⟨hb₀₁, hb₀₂, hb₁₂⟩ := triple_distinct h.2.1.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨b₀, by simp, (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₀ (by simp)).mp hadj with hw | hw | hw
    · exact hne hw.1
    · exact hb₀₁ hw.2
    · exact hb₀₂ hw.2
  · refine ⟨b₁, by simp,
      (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₁ (by simp)).mp hadj with hw | hw | hw
    · exact hb₀₁ hw.2.symm
    · exact hne hw.1
    · exact hb₁₂ hw.2
  · refine ⟨b₂, by simp,
      (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₂ (by simp)).mp hadj with hw | hw | hw
    · exact hb₀₂ hw.2.symm
    · exact hb₁₂ hw.2.symm
    · exact hne hw.1

/-- The two partners of a reflection: `z`'s partner is the attached vertex `s`, and the
partner of a second triangle vertex `p` lies in `A` and is adjacent to `s`. -/
private theorem two_partners (G : SimpleGraph V) (hG : InF7 G) (z p q s : V) (A : Set V)
    (hzp : G.Adj z p) (hzq : G.Adj z q) (hpq : G.Adj p q)
    (hzs : G.Adj z s) (hsA : s ∉ A)
    (hznep : z ≠ p) (hzneq : z ≠ q) (hpneq : p ≠ q)
    (hAconn : ConnectedSet G A) (hzA : ∀ g ∈ A, ¬ G.Adj z g)
    (hzAmem : z ∉ A) (hpA : p ∉ A) (hqA : q ∉ A)
    (hsnep : s ≠ p) (hsneq : s ≠ q)
    (hsp : ¬ G.Adj s p) (hsq : ¬ G.Adj s q)
    (hsnb : ∃ g ∈ A, G.Adj s g)
    (hpnb : ∃ g ∈ A, G.Adj p g) (hqnb : ∃ g ∈ A, G.Adj q g)
    (hnorefl : ∀ g ∈ A, ¬ (G.Adj p g ∧ G.Adj s g ∧ ¬ G.Adj q g)) :
    ∃ g ∈ A, G.Adj p g ∧ G.Adj q g := by
  classical
  let T : Set V := {z, p, q}
  let F : Set V := A ∪ {s}
  have htri : IsTriangle G T := by
    refine ⟨Set.ncard_eq_three.mpr ⟨z, p, q, hznep, hzneq, hpneq, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact hzp
    · exact hzq
    · exact hzp.symm
    · exact (huv rfl).elim
    · exact hpq
    · exact hzq.symm
    · exact hpq.symm
    · exact (huv rfl).elim
  have hFT : F ⊆ Tᶜ := by
    rintro g (hg | hg) hgT <;>
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hgT
    · rcases hgT with h | h | h
      · exact hzAmem (h ▸ hg)
      · exact hpA (h ▸ hg)
      · exact hqA (h ▸ hg)
    · have hgs : g = s := by simpa using hg
      subst g
      rcases hgT with h | h | h
      · exact hzs.ne h.symm
      · exact hsnep h
      · exact hsneq h
  have hFconn : ConnectedSet G F :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hAconn hsnb
  have hcatch : Catches G F T := by
    refine ⟨htri, hFconn, Set.disjoint_left.mpr hFT, ?_⟩
    intro u hu
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨s, Or.inr rfl, hzs⟩
    · obtain ⟨g, hgA, hg⟩ := hpnb
      exact ⟨g, Or.inl hgA, hg⟩
    · obtain ⟨g, hgA, hg⟩ := hqnb
      exact ⟨g, Or.inl hgA, hg⟩
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T htri F hFT hcatch with
    href | ⟨g, hgF, hcard⟩
  · exfalso
    obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, hTeq, hBsub, hreff⟩ := href
    have hzmem : z ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    have hpmem : p ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    obtain ⟨v, hvB, hzv, -⟩ := reflection_partner hreff hzmem
    obtain ⟨v', hv'B, hpv', hother'⟩ := reflection_partner hreff hpmem
    have hvs : v = s := by
      rcases hBsub hvB with h | h
      · exact absurd hzv (hzA v h)
      · simpa using h
    subst hvs
    have hv'ne : v' ≠ v := by
      intro he
      exact hother' z hzmem (fun hc => hznep hc) (he ▸ hzv)
    have hv'A : v' ∈ A := by
      rcases hBsub hv'B with h | h
      · exact h
      · exact absurd (show v' = v from by simpa using h) hv'ne
    have hadj : G.Adj v' v := by
      obtain ⟨-, htriB, -, -⟩ := hreff
      exact htriB.2 v' hv'B v hvB hv'ne
    have hqmem : q ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    exact hnorefl v' hv'A ⟨hpv', hadj.symm, hother' q hqmem (fun hc => hpneq hc.symm)⟩
  · -- some vertex of `F` has two neighbours in the triangle
    have hgA : g ∈ A := by
      rcases hgF with h | h
      · exact h
      · exfalso
        have hgs : g = s := by simpa using h
        rw [hgs] at hcard
        have hsub : (G.neighborSet s ∩ T).Subsingleton := by
          have hkey : ∀ w : V, w ∈ G.neighborSet s ∩ T → w = z := by
            intro w hw
            have hw1 : G.Adj s w := hw.1
            have hw2 := hw.2
            simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hw2
            rcases hw2 with h | h | h
            · exact h
            · exact absurd (h ▸ hw1) hsp
            · exact absurd (h ▸ hw1) hsq
          intro a ha b hb
          exact (hkey a ha).trans (hkey b hb).symm
        have := (Set.ncard_le_one (Set.toFinite _)).mpr hsub
        omega
    have hnz : ¬ (z ∈ G.neighborSet g ∩ T) := by
      rintro ⟨h, -⟩
      exact hzA g hgA h.symm
    obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp hcard
    have hmem : ∀ w : V, w ∈ G.neighborSet g ∩ T → w = p ∨ w = q := by
      intro w hw
      have hw2 := hw.2
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hw2
      rcases hw2 with h | h | h
      · exact absurd (h ▸ hw) hnz
      · exact Or.inl h
      · exact Or.inr h
    have hga : G.Adj g a := ha.1
    have hgb : G.Adj g b := hb.1
    rcases hmem a ha with h | h <;> rcases hmem b hb with h' | h'
    · exact absurd (h.trans h'.symm) hab
    · exact ⟨g, hgA, (h ▸ hga).symm, (h' ▸ hgb).symm⟩
    · exact ⟨g, hgA, (h' ▸ hgb).symm, (h ▸ hga).symm⟩
    · exact absurd (h.trans h'.symm) hab


/-- **Claim (8), first application of 17.1.**  *"Now `A ∪ {x₁}` catches the triangle
`{z,x₀,x₂}`; it contains no reflection of this triangle, since `x₀,x₁` have no common
neighbour in `A`; … So by 17.1 it follows that there is a vertex in `A` adjacent to both
`x₀,x₂`."* -/
theorem catch_x0x2 (G : SimpleGraph V) (hG : InF7 G) (z x₀ x₁ x₂ : V) (A : Set V)
    (hzx0 : G.Adj z x₀) (hzx1 : G.Adj z x₁) (hzx2 : G.Adj z x₂)
    (hx20 : G.Adj x₂ x₀) (hx21 : ¬ G.Adj x₂ x₁) (hx01 : ¬ G.Adj x₀ x₁)
    (hx01ne : x₀ ≠ x₁) (hx12ne : x₁ ≠ x₂)
    (hAconn : ConnectedSet G A) (hzA : ∀ g ∈ A, ¬ G.Adj z g)
    (hzAmem : z ∉ A) (hx0A : x₀ ∉ A) (hx1A : x₁ ∉ A) (hx2A : x₂ ∉ A)
    (hnoc : ∀ g ∈ A, ¬ (G.Adj x₀ g ∧ G.Adj x₁ g))
    (h0nb : ∃ g ∈ A, G.Adj x₀ g) (h1nb : ∃ g ∈ A, G.Adj x₁ g)
    (h2nb : ∃ g ∈ A, G.Adj x₂ g) :
    ∃ g ∈ A, G.Adj x₀ g ∧ G.Adj x₂ g :=
  two_partners G hG z x₀ x₂ x₁ A hzx0 hzx2 hx20.symm hzx1 hx1A hzx0.ne hzx2.ne hx20.ne'
    hAconn hzA hzAmem hx0A hx2A (Ne.symm hx01ne) hx12ne
    (fun h => hx01 h.symm) (fun h => hx21 h.symm) h1nb h0nb h2nb
    (fun g hg h => hnoc g hg ⟨h.1, h.2.1⟩)

/-- **Claim (8), second application of 17.1.**  *"Also, `A ∪ x₂` catches the triangle
`{z,x₁,y}`.  Suppose that `A ∪ {x₂}` contains a reflection of this triangle; then there
exists `f ∈ A` adjacent to `x₁,x₂` and not to `y`.  Since `f ∈ A` it follows that `f` is
nonadjacent to `x₀`; but then `f-x₂-x₀-y-x₁-f` is an odd hole, a contradiction.  Hence by
17.1 there is a vertex in `A` adjacent to both `x₁,y`."* -/
theorem catch_x1y (G : SimpleGraph V) (hG : InF7 G) (z x₀ x₁ x₂ y : V) (A : Set V)
    (hzx0 : G.Adj z x₀) (hzx1 : G.Adj z x₁) (hzx2 : G.Adj z x₂) (hzy : G.Adj z y)
    (hy0 : G.Adj y x₀) (hy1 : G.Adj y x₁)
    (hx20 : G.Adj x₂ x₀) (hx21 : ¬ G.Adj x₂ x₁) (hx01 : ¬ G.Adj x₀ x₁)
    (h2y : ¬ G.Adj x₂ y) (hx2yne : x₂ ≠ y) (hx12ne : x₁ ≠ x₂) (hx01ne : x₀ ≠ x₁)
    (hAconn : ConnectedSet G A) (hzA : ∀ g ∈ A, ¬ G.Adj z g)
    (hzAmem : z ∉ A) (hx0A : x₀ ∉ A) (hx1A : x₁ ∉ A) (hx2A : x₂ ∉ A) (hyA : y ∉ A)
    (hnoc : ∀ g ∈ A, ¬ (G.Adj x₀ g ∧ G.Adj x₁ g))
    (h1nb : ∃ g ∈ A, G.Adj x₁ g) (hynb : ∃ g ∈ A, G.Adj y g)
    (h2nb : ∃ g ∈ A, G.Adj x₂ g) :
    ∃ g ∈ A, G.Adj x₁ g ∧ G.Adj y g := by
  refine two_partners G hG z x₁ y x₂ A hzx1 hzy hy1.symm hzx2 hx2A hzx1.ne hzy.ne hy1.ne'
    hAconn hzA hzAmem hx1A hyA (Ne.symm hx12ne) hx2yne hx21 h2y h2nb h1nb hynb ?_
  rintro f hf ⟨hf1, hf2, hfy⟩
  have hf0 : ¬ G.Adj x₀ f := fun h => hnoc f hf ⟨h, hf1⟩
  have hfne0 : f ≠ x₀ := fun h => hx0A (h ▸ hf)
  have hfne1 : f ≠ x₁ := fun h => hx1A (h ▸ hf)
  have hfne2 : f ≠ x₂ := fun h => hx2A (h ▸ hf)
  have hfney : f ≠ y := fun h => hyA (h ▸ hf)
  refine FiveHoleBasics.five_hole_absurd (G := G) hG.1.1.1.1
    (x := f) (y := x₂) (z := x₀) (w := y) (t := x₁) ?_
    hf2.symm hx20 hy0.symm hy1 hf1
    (fun h => hf0 h.symm) (fun h => hfy h.symm) h2y hx21 hx01
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    List.nodup_nil, and_true, not_or, not_false_eq_true, List.not_mem_nil, or_false]
  exact ⟨⟨hfne2, hfne0, hfney, hfne1⟩, ⟨hx20.ne, hx2yne, hx12ne.symm⟩,
    ⟨hy0.ne', hx01ne⟩, hy1.ne⟩

end Workspace.ProofLemmas.Thm192Claim8Triangles
