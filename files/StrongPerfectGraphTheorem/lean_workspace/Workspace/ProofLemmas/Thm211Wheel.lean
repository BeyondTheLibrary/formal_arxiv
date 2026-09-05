import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleYEdgeParity

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm211Wheel

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (21.1, printed p. 131): "In the third case, 2.3 implies that
`(C, Y)` is a wheel." The third complete vertex excludes the exceptional
outcome of 2.3. Thus there is a second complete edge. The first edge has no
other complete neighbor at either end, so the two edges are disjoint. -/
theorem wheel_of_isolated_complete_edge {G : SimpleGraph V} (hG : Berge G)
    {C : List V} (hC : IsHoleList G C) (hlen : 6 ≤ holeLength C)
    {Y : Set V} (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hCY : ∀ w ∈ C, w ∉ Y) {u v z : V}
    (hu : u ∈ C) (hv : v ∈ C) (hz : z ∈ C)
    (huv : EdgeComplete G Y u v) (hzY : VertexComplete G z Y)
    (hzu : z ≠ u) (hzv : z ≠ v)
    (hsole : ∀ w ∈ C, VertexComplete G w Y →
      (G.Adj u w → w = v) ∧ (G.Adj v w → w = u)) :
    IsWheel G C Y := by
  classical
  have heven : Even (HoleYEdgeParity.yEdges G Y C).ncard := by
    rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hG Y hYanti C
      (Or.inr hC) hCY).2 hC with he | ⟨a, b, hset, _, _⟩
    · exact he
    · have hm : ∀ w ∈ C, VertexComplete G w Y → w = a ∨ w = b := by
        intro w hw hwY
        have hwab : w ∈ ({a, b} : Set V) := by rw [← hset]; exact ⟨hw, hwY⟩
        exact hwab
      have hmu := hm u hu huv.2.1
      have hmv := hm v hv huv.2.2
      have hmz := hm z hz hzY
      have hune := huv.1.ne
      rcases hmu with hmu | hmu <;> rcases hmv with hmv | hmv <;>
        rcases hmz with hmz | hmz
      all_goals first
        | exact (hune (hmu.trans hmv.symm)).elim
        | exact (hzu (hmz.trans hmu.symm)).elim
        | exact (hzv (hmz.trans hmv.symm)).elim
  have he : s(u, v) ∈ HoleYEdgeParity.yEdges G Y C := ⟨u, hu, v, hv, rfl, huv⟩
  have hpos : 0 < (HoleYEdgeParity.yEdges G Y C).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨s(u, v), he⟩
  have htwo : 1 < (HoleYEdgeParity.yEdges G Y C).ncard := by
    rw [Nat.even_iff] at heven
    omega
  obtain ⟨e, heC, hene⟩ := Set.exists_ne_of_one_lt_ncard htwo s(u, v)
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := heC
  have hcross : ∀ c ∈ C, ∀ d ∈ C, EdgeComplete G Y c d →
      s(c, d) ≠ s(u, v) → c ≠ u ∧ c ≠ v := by
    intro c hc d hd hcd hne
    constructor
    · intro hcu
      subst c
      have hdv := (hsole d hd hcd.2.2).1 hcd.1
      exact hne (by rw [hdv])
    · intro hcv
      subst c
      have hdu := (hsole d hd hcd.2.2).2 hcd.1
      exact hne (by rw [hdu]; exact Sym2.eq_swap)
  have haends := hcross a ha b hb hab hene
  have hbends := hcross b hb a ha ⟨hab.1.symm, hab.2.2, hab.2.1⟩ (by
    intro heq
    apply hene
    exact Sym2.eq_swap.trans heq)
  exact ⟨⟨hC, hlen⟩, ⟨hYne, hYanti, hCY⟩, u, v, a, b,
    hu, hv, ha, hb, huv, hab, haends.1.symm, hbends.1.symm,
    haends.2.symm, hbends.2.symm⟩

end Workspace.ProofLemmas.Thm211Wheel
