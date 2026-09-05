import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# 23.2, claim (4): the odd antipath between `y` and `v₁`

PAPER (23.2, claim (4), printed p. 140):

> *"Since `y, v₁` are not `Y`-complete, there is an antipath joining them with interior in `Y`,
> and it is odd since it can be completed to an antihole via `v₁-z-v₂-y`.  Hence every
> `Y`-complete vertex is adjacent to one of `y, v₁`."*

`every_complete_adj` is that whole passage.  The antipath comes from
`InducedPathExtraction.exists_antipath_interior_in`; the antihole `y-Q-v₁-z-v₂-y` is
`Q ++ [z, v₂]` read in `Gᶜ`, and Berge makes it even, so `Q` is odd.  A `Y`-complete vertex
adjacent to neither end would close `Q` into an antihole with one extra vertex
(`AntiholeCompletion.even_pathLength_of_witness`), forcing `Q` even instead.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232Claim4Antipath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **PAPER (23.2, claim (4)):** *"Since `y, v₁` are not `Y`-complete, there is an antipath
joining them with interior in `Y`, and it is odd since it can be completed to an antihole via
`v₁-z-v₂-y`."*

Here `u` is the paper's `v₂`, the `Y`-complete neighbour of `v₁` in `A₀`. -/
theorem exists_odd_antipath (hBerge : Berge G) (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (y v₁ z u : V)
    (hyv : G.Adj y v₁) (hzy : G.Adj z y) (hvu : G.Adj v₁ u)
    (hzv : ¬ G.Adj z v₁) (hzu : ¬ G.Adj z u) (huy : ¬ G.Adj u y)
    (hzune : z ≠ u) (hzvne : z ≠ v₁) (huyne : u ≠ y) (huvne : u ≠ v₁)
    (hyY : y ∉ Y) (hvY : v₁ ∉ Y) (hzYm : z ∉ Y) (huYm : u ∉ Y)
    (hyNC : ¬ VertexComplete G y Y) (hvNC : ¬ VertexComplete G v₁ Y)
    (hzC : VertexComplete G z Y) (huC : VertexComplete G u Y) :
    ∃ Q : List V, IsAntipathFrom G Q y v₁ ∧ (∀ w ∈ SPGT.interior Q, w ∈ Y) ∧
      ¬ Even (pathLength Q) := by
  have hy' : ∃ x ∈ Y, ¬ G.Adj y x := by
    by_contra h
    push_neg at h
    exact hyNC h
  have hv' : ∃ x ∈ Y, ¬ G.Adj v₁ x := by
    by_contra h
    push_neg at h
    exact hvNC h
  obtain ⟨Q, hQ, hQint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hYanti hyY hvY hy' hv'
  refine ⟨Q, hQ, hQint, ?_⟩
  have hQ3 : 3 ≤ Q.length := AntiholeCompletion.three_le_length_of_antipath hQ hyv
  -- every vertex of `Q` is an end or lies in `Y`
  have hQmem : ∀ x ∈ Q, x = y ∨ x = v₁ ∨ x ∈ Y := by
    intro x hx
    by_cases h1 : x = y
    · exact Or.inl h1
    by_cases h2 : x = v₁
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (hQint x ((mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, h1, h2⟩)))
  have hzQ : z ∉ Q := by
    intro hz
    rcases hQmem z hz with h | h | h
    · exact hzy.ne h
    · exact hzvne h
    · exact hzYm h
  have huQ : u ∉ Q := by
    intro hu
    rcases hQmem u hu with h | h | h
    · exact huyne h
    · exact huvne h
    · exact huYm h
  -- the antihole `y-Q-v₁-z-u-y`
  have hpair : IsPathFrom Gᶜ [z, u] z u :=
    ⟨isPathList_pair (G := Gᶜ) ⟨hzune, hzu⟩, rfl, rfl⟩
  have hdisj : ∀ x ∈ Q, x ∉ ([z, u] : List V) := by
    intro x hx hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact hzQ hx
    · exact huQ hx
  have hcross : ∀ x ∈ Q, ∀ w ∈ ([z, u] : List V),
      (Gᶜ.Adj x w ↔ (x = v₁ ∧ w = z) ∨ (x = y ∧ w = u)) := by
    intro x hx w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · constructor
      · intro hadj
        refine Or.inl ⟨?_, rfl⟩
        rcases hQmem x hx with h | h | h
        · exact absurd (h ▸ hzy.symm) hadj.2
        · exact h
        · exact absurd (hzC x h).symm hadj.2
      · rintro (⟨rfl, -⟩ | ⟨-, h⟩)
        · exact ⟨fun hh => hzvne hh.symm, fun hh => hzv hh.symm⟩
        · exact absurd h hzune
    · constructor
      · intro hadj
        refine Or.inr ⟨?_, rfl⟩
        rcases hQmem x hx with h | h | h
        · exact h
        · exact absurd (h ▸ hvu) hadj.2
        · exact absurd (huC x h).symm hadj.2
      · rintro (⟨-, h⟩ | ⟨rfl, -⟩)
        · exact absurd h.symm hzune
        · exact ⟨fun hh => huyne hh.symm, fun hh => huy hh.symm⟩
  have hhole : IsHoleList Gᶜ (Q ++ [z, u]) :=
    PathGlue.glue_hole hQ hpair hdisj hcross (by simp; omega)
  have heven := hBerge.2 _ hhole
  simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at heven
  have hple := pathLength_eq Q
  rw [Nat.even_iff] at heven
  rw [Nat.even_iff]
  omega

/-- **PAPER (23.2, claim (4)):** *"Hence every `Y`-complete vertex is adjacent to one of
`y, v₁`."* -/
theorem every_complete_adj (hBerge : Berge G) (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (y v₁ z u : V)
    (hyv : G.Adj y v₁) (hzy : G.Adj z y) (hvu : G.Adj v₁ u)
    (hzv : ¬ G.Adj z v₁) (hzu : ¬ G.Adj z u) (huy : ¬ G.Adj u y)
    (hzune : z ≠ u) (hzvne : z ≠ v₁) (huyne : u ≠ y) (huvne : u ≠ v₁)
    (hyY : y ∉ Y) (hvY : v₁ ∉ Y) (hzYm : z ∉ Y) (huYm : u ∉ Y)
    (hyNC : ¬ VertexComplete G y Y) (hvNC : ¬ VertexComplete G v₁ Y)
    (hzC : VertexComplete G z Y) (huC : VertexComplete G u Y)
    (t : V) (htC : VertexComplete G t Y) :
    G.Adj t y ∨ G.Adj t v₁ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hty, htv⟩ := hcon
  obtain ⟨Q, hQ, hQint, hodd⟩ :=
    exists_odd_antipath hBerge Y hYanti y v₁ z u hyv hzy hvu hzv hzu huy hzune hzvne
      huyne huvne hyY hvY hzYm huYm hyNC hvNC hzC huC
  exact hodd (AntiholeCompletion.even_pathLength_of_witness hBerge hyv htC hty htv
    (fun h => hyNC (h ▸ htC)) (fun h => hvNC (h ▸ htC)) hQ hQint)

end Workspace.ProofLemmas.Thm232Claim4Antipath
