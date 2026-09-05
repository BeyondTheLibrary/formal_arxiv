import Workspace.Types.Classes
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm232ClosingCompletePair

/-!
# The special case at `c₂` in claim (3) of 23.2, in one orientation

PAPER (23.2, claim (3), printed pp. 139–140):

> *"Next suppose that `y` is adjacent to `c₂`.  From the symmetry we may assume that
> `x₀ ≠ c₃`.  Let `Q` be the path of `C \ z` between `x₀, c₃`; so `Q` has length `> 0`, and
> even length by 2.3.  Since `x₀-Q-c₃-c₂-y-x₀` is not an odd hole, it follows that `y` is not
> adjacent to `x₀`.  But then the hole `x₀-Q-c₃-c₂-y-z-x₀` is the rim of an odd wheel with
> hub `Y`, contrary to `G ∈ F₈`."*

The two sentences are separated here, and both are stated for an abstract arc `Q`, so that the
symmetry *"we may assume that `x₀ ≠ c₃`"* can be discharged by applying them twice: once to the
arc of `C \ z` from `c₃` to `x₀`, and once to the arc from `c₁` to `x₁`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232Claim3C2Core

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **PAPER (23.2, claim (3)):** *"Since `x₀-Q-c₃-c₂-y-x₀` is not an odd hole, it follows that
`y` is not adjacent to `x₀`."*

`Q` runs from `c₃` to `x₀`; the cycle of the printed sentence is `Q ++ [y, c₂]`, of length
`pathLength Q + 3`. -/
theorem no_adj_far_end (hBerge : Berge G) (Q : List V) (c₃ x₀ y c₂ : V)
    (hQ : IsPathFrom G Q c₃ x₀)
    (hQeven : Even (pathLength Q)) (hQ2 : 2 ≤ pathLength Q)
    (hyQ : y ∉ Q) (hc2Q : c₂ ∉ Q)
    (hyc2 : G.Adj y c₂)
    (hyadj : ∀ v ∈ Q, v ≠ x₀ → ¬ G.Adj y v)
    (hc2adj : ∀ v ∈ Q, (G.Adj c₂ v ↔ v = c₃)) :
    ¬ G.Adj y x₀ := by
  intro hadj
  have hlen : 3 ≤ Q.length := by
    have := length_eq_pathLength_add_one hQ.1
    omega
  have hyc : y ≠ c₂ := hyc2.ne
  have hpair : IsPathFrom G [y, c₂] y c₂ := ⟨isPathList_pair hyc2, rfl, rfl⟩
  have hhole : IsHoleList G (Q ++ [y, c₂]) := by
    refine PathGlue.glue_hole hQ hpair ?_ ?_ (by simp; omega)
    · intro x hx hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      · exact hyQ hx
      · exact hc2Q hx
    · intro x hx w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with hw | hw
      · rw [hw]
        constructor
        · intro h
          refine Or.inl ⟨?_, rfl⟩
          by_contra hne
          exact hyadj x hx hne h.symm
        · rintro (⟨rfl, -⟩ | ⟨-, h⟩)
          · exact hadj.symm
          · exact absurd h hyc
      · rw [hw]
        constructor
        · intro h
          exact Or.inr ⟨(hc2adj x hx).mp h.symm, rfl⟩
        · rintro (⟨-, h⟩ | ⟨rfl, -⟩)
          · exact absurd h.symm hyc
          · exact ((hc2adj _ hx).mpr rfl).symm
  have hlen2 : (Q ++ [y, c₂]).length = pathLength Q + 3 := by
    have := length_eq_pathLength_add_one hQ.1
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have hev := hBerge.1 _ hhole
  rw [holeLength, hlen2] at hev
  obtain ⟨r, hr⟩ := hQeven
  obtain ⟨s, hs⟩ := hev
  omega


/-- **PAPER (23.2, claim (3)):** *"But then the hole `x₀-Q-c₃-c₂-y-z-x₀` is the rim of an odd
wheel with hub `Y`, contrary to `G ∈ F₈`."*

The rim is `[x₀, z, y, c₂] ++ Q.dropLast`, and the odd segment is the single `Y`-complete edge
`x₀z`: its two rim neighbours are `y`, which is not `Y`-complete, and the neighbour of `x₀` on
`Q`, which is not `Y`-complete because `x₀` is and `C` carries only the four listed
`Y`-complete edges. -/
theorem odd_wheel_absurd (hG : InF8 G) (Y : Set V)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (Q : List V) (c₃ x₀ z y c₂ : V)
    (hQ : IsPathFrom G Q c₃ x₀)
    (hQ2 : 2 ≤ pathLength Q)
    (hQY : ∀ v ∈ Q, v ∉ Y)
    (hzQ : z ∉ Q) (hyQ : y ∉ Q) (hc2Q : c₂ ∉ Q)
    (hyY : y ∉ Y) (hzYm : z ∉ Y) (hc2Ym : c₂ ∉ Y)
    (hx0z : G.Adj x₀ z) (hzy : G.Adj z y) (hyc2 : G.Adj y c₂)
    (hnx0y : ¬ G.Adj x₀ y) (hnx0c2 : ¬ G.Adj x₀ c₂) (hnzc2 : ¬ G.Adj z c₂)
    (hzc2ne : z ≠ c₂)
    (hzadj : ∀ v ∈ Q, (G.Adj z v ↔ v = x₀))
    (hc2adj : ∀ v ∈ Q, (G.Adj c₂ v ↔ v = c₃))
    (hyadj : ∀ v ∈ Q, ¬ G.Adj y v)
    (hx0C : VertexComplete G x₀ Y) (hzC : VertexComplete G z Y)
    (hc2C : VertexComplete G c₂ Y) (hc3C : VertexComplete G c₃ Y)
    (hyNC : ¬ VertexComplete G y Y)
    (hnbrNC : ∀ v ∈ Q, G.Adj x₀ v → ¬ VertexComplete G v Y) :
    False := by
  classical
  have hQlen : 3 ≤ Q.length := by
    have := length_eq_pathLength_add_one hQ.1
    omega
  have hQ0 : Q[0]'(by omega) = c₃ := getElem_zero_of_head? hQ.2.1 (by omega)
  have hQlast : Q[Q.length - 1]'(by omega) = x₀ :=
    getElem_last_of_getLast? hQ.2.2 (by omega)
  set s : V := Q[Q.length - 2]'(by omega) with hsdef
  -- the arc with its far end `x₀` removed
  have hslice0 := isPathFrom_slice hQ.1 (i := 0) (j := Q.length - 2) (by omega) (by omega)
  rw [show Q.length - 2 - 0 + 1 = Q.length - 1 by omega, List.drop_zero, hQ0,
    ← List.dropLast_eq_take] at hslice0
  set Q₂ : List V := Q.dropLast with hQ₂def
  have hslice : IsPathFrom G Q₂ c₃ s := hslice0
  have hQ₂len : Q₂.length = Q.length - 1 := List.length_dropLast
  have hQ₂sub : ∀ v ∈ Q₂, v ∈ Q := fun v hv => List.dropLast_subset _ hv
  have hcat : Q₂ ++ [x₀] = Q := by
    have hne : Q ≠ [] := path_ne_nil hQ.1
    have hgl : Q.getLast hne = x₀ := by
      have := hQ.2.2
      rw [List.getLast?_eq_some_getLast hne] at this
      exact Option.some_injective _ this
    rw [hQ₂def, ← hgl]
    exact List.dropLast_append_getLast hne
  have hx0Q₂ : x₀ ∉ Q₂ := by
    intro hmem
    have hnd : (Q₂ ++ [x₀]).Nodup := hcat ▸ hQ.1.2.1
    rw [List.nodup_append] at hnd
    exact hnd.2.2 x₀ hmem x₀ (by simp) rfl
  have hsQ : s ∈ Q := List.getElem_mem _
  have hx0s : G.Adj x₀ s := by
    have h := path_adj_succ hQ.1 (i := Q.length - 2) (by omega)
    have e : Q[Q.length - 2 + 1]'(by omega) = x₀ :=
      (hQ.1.2.1.getElem_inj_iff.mpr
        (show Q.length - 2 + 1 = Q.length - 1 by omega)).trans hQlast
    rw [e] at h
    exact h.symm
  have hx0Q₂adj : ∀ w ∈ Q₂, (G.Adj x₀ w ↔ w = s) := by
    intro w hw
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem (hQ₂sub w hw)
    have hine : i ≠ Q.length - 1 := by
      intro he
      apply hx0Q₂
      have hex : Q[i]'hi = x₀ := (hQ.1.2.1.getElem_inj_iff.mpr he).trans hQlast
      exact (hiv.symm.trans hex) ▸ hw
    have hws : w = s ↔ i = Q.length - 2 := by
      rw [← hiv, hsdef]
      exact hQ.1.2.1.getElem_inj_iff
    rw [hws, ← hiv, ← hQlast]
    rw [path_adj_iff hQ.1 (show Q.length - 1 < Q.length by omega) hi]
    omega
  -- the four-vertex path `x₀-z-y-c₂`
  have hx0y : x₀ ≠ y := fun h => hyQ (h ▸ (getLast_mem hQ.2.2))
  have hx0c2 : x₀ ≠ c₂ := fun h => hc2Q (h ▸ (getLast_mem hQ.2.2))
  have hnd : ([x₀, z, y, c₂] : List V).Nodup := by
    have e1 : x₀ ≠ z := hx0z.ne
    have e2 : z ≠ y := hzy.ne
    have e3 : y ≠ c₂ := hyc2.ne
    simp [e1, e2, e3, hx0y, hx0c2, hzc2ne]
  have hP : IsPathFrom G [x₀, z, y, c₂] x₀ c₂ :=
    ⟨PathGlue.isPathList_four hnd hx0z hzy hyc2 hnx0y hnx0c2 hnzc2, rfl, rfl⟩
  have hcross : ∀ x ∈ ([x₀, z, y, c₂] : List V), ∀ w ∈ Q₂,
      (G.Adj x w ↔ (x = c₂ ∧ w = c₃) ∨ (x = x₀ ∧ w = s)) := by
    intro x hx w hw
    have hwQ : w ∈ Q := hQ₂sub w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · rw [hx0Q₂adj w hw]
      constructor
      · intro h; exact Or.inr ⟨rfl, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h hx0c2
        · exact h
    · rw [hzadj w hwQ]
      constructor
      · rintro rfl; exact absurd hw hx0Q₂
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact absurd h hzc2ne
        · exact absurd h.symm hx0z.ne
    · constructor
      · intro h; exact absurd h (hyadj w hwQ)
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact absurd h hyc2.ne
        · exact absurd h.symm hx0y
    · rw [hc2adj w hwQ]
      constructor
      · intro h; exact Or.inl ⟨rfl, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · exact absurd h.symm hx0c2
  have hdisj : ∀ x ∈ ([x₀, z, y, c₂] : List V), x ∉ Q₂ := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact hx0Q₂
    · exact fun h => hzQ (hQ₂sub _ h)
    · exact fun h => hyQ (hQ₂sub _ h)
    · exact fun h => hc2Q (hQ₂sub _ h)
  have hhole : IsHoleList G ([x₀, z, y, c₂] ++ Q₂) :=
    PathGlue.glue_hole hP hslice hdisj hcross (by simp)
  -- the tail `y-c₂-Q₂` of the new rim
  have hSpath : IsPathFrom G ([y, c₂] ++ Q₂) y s := by
    refine PathGlue.glue_path ⟨isPathList_pair hyc2, rfl, rfl⟩ hslice ?_ ?_
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx <;> rw [hx]
      · exact fun h => hyQ (hQ₂sub _ h)
      · exact fun h => hc2Q (hQ₂sub _ h)
    · intro x hx w hw
      have hwQ : w ∈ Q := hQ₂sub w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx <;> rw [hx]
      · constructor
        · intro h; exact absurd h (hyadj w hwQ)
        · rintro ⟨h, -⟩; exact absurd h hyc2.ne
      · rw [hc2adj w hwQ]
        exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  have hDeq : ([x₀, z, y, c₂] ++ Q₂) = x₀ :: z :: ([y, c₂] ++ Q₂) := rfl
  have hD6 : 6 ≤ (x₀ :: z :: ([y, c₂] ++ Q₂)).length := by
    simp only [List.length_cons, List.length_append, List.length_nil]
    omega
  have hsNC : ¬ VertexComplete G s Y := hnbrNC s hsQ hx0s
  have hseg : IsSegment G (x₀ :: z :: ([y, c₂] ++ Q₂)) Y [x₀, z] :=
    Thm232ClosingCompletePair.pair_segment (hDeq ▸ hhole) hD6 hSpath hx0C hzC hyNC hsNC
  have hc3Q₂ : c₃ ∈ Q₂ := head_mem hslice.2.1
  have hc2c3 : G.Adj c₂ c₃ := (hc2adj c₃ (head_mem hQ.2.1)).mpr rfl
  have hnotY : ∀ v ∈ x₀ :: z :: ([y, c₂] ++ Q₂), v ∉ Y := by
    intro v hv
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv | (hv | hv) | hv
    · exact hv ▸ hQY x₀ (getLast_mem hQ.2.2)
    · exact hv ▸ hzYm
    · exact hv ▸ hyY
    · exact hv ▸ hc2Ym
    · exact hQY v (hQ₂sub v hv)
  have hwheel : IsWheel G (x₀ :: z :: ([y, c₂] ++ Q₂)) Y := by
    refine ⟨⟨hDeq ▸ hhole, by rw [holeLength]; exact hD6⟩, ⟨hYne, hYanti, hnotY⟩,
      x₀, z, c₂, c₃, by simp, by simp, by simp, by simp [hc3Q₂],
      ⟨hx0z, hx0C, hzC⟩, ⟨hc2c3, hc2C, hc3C⟩, hx0c2, ?_, hzc2ne, ?_⟩
    · exact fun h => hx0Q₂ (h ▸ hc3Q₂)
    · exact fun h => hzQ (hQ₂sub _ (h ▸ hc3Q₂))
  exact hG.1.2.1 ⟨_, Y, hwheel, [x₀, z], hseg, ⟨0, rfl⟩⟩

end Workspace.ProofLemmas.Thm232Claim3C2Core
