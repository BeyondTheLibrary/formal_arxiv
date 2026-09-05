import Workspace.ProofLemmas.Thm74Holes
import Workspace.Statements.S07.Thm_7_2

/-!
# The proof of rung replacement, 7.4

First assume that the unchanged top neighbour is `a₂`. We follow the two
linkages and two odd holes in the printed proof. Exchanging `a₂` and `a₃`
then handles the other possible neighbour.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm74Proof

open Workspace.Types.Core.SPGT Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas
open Thm74Linkage Thm74Holes

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Translate the neighbour count on a triangle into its three possible pairs. -/
theorem two_neighbors_iff {G : SimpleGraph V} {x z w y : V}
    (hxz : x ≠ z) (hxw : x ≠ w) (hzw : z ≠ w) :
    2 ≤ (({x, z, w} : Set V) ∩ G.neighborSet y).ncard ↔
      (G.Adj y x ∧ G.Adj y z) ∨ (G.Adj y x ∧ G.Adj y w) ∨
        (G.Adj y z ∧ G.Adj y w) := by
  constructor
  · intro hc
    obtain ⟨u, ⟨hu, huy⟩, v, ⟨hv, hvy⟩, huv⟩ :=
      (Set.one_lt_ncard (Set.toFinite _)).mp hc
    change G.Adj y u at huy
    change G.Adj y v at hvy
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> tauto
  · intro hh
    apply (Set.one_lt_ncard (Set.toFinite _)).mpr
    rcases hh with ⟨hyx, hyz⟩ | ⟨hyx, hyw⟩ | ⟨hyz, hyw⟩
    · exact ⟨x, ⟨by simp, hyx⟩, z, ⟨by simp, hyz⟩, hxz⟩
    · exact ⟨x, ⟨by simp, hyx⟩, w, ⟨by simp, hyw⟩, hxw⟩
    · exact ⟨z, ⟨by simp, hyz⟩, w, ⟨by simp, hyw⟩, hzw⟩

/-- PAPER (7.4, printed p. 35): "Then a₁′ ∉ X, and a₁ ∈ X, and
exactly one of a₂, a₃ ∈ X, say a₂ ∈ X."

This is the rest of the printed proof in that orientation. The hypotheses
record the four top adjacencies after this choice. -/
theorem oriented_contradiction {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2))
    (heven1 : Even (pathLength (R 1))) (heven2 : Even (pathLength (R 2)))
    (hlen1 : 2 ≤ pathLength (R 1)) (hlen2 : 2 ≤ pathLength (R 2))
    {a' : V} {P' : List V}
    (h' : FormPrism G ![a', a 1, a 2] b P' (R 1) (R 2))
    {y : V} (hya : G.Adj y (a 0)) (hy1 : G.Adj y (a 1))
    (hy2 : ¬ G.Adj y (a 2)) (hy' : ¬ G.Adj y a')
    (hyB : (G.Adj y (b 0) ∧ G.Adj y (b 1)) ∨
      (G.Adj y (b 0) ∧ G.Adj y (b 2)) ∨ (G.Adj y (b 1) ∧ G.Adj y (b 2))) :
    False := by
  let R' : Fin 3 → List V := ![P', R 1, R 2]
  have hnew : FormPrism G ![a', a 1, a 2] b (R' 0) (R' 1) (R' 2) := h'
  have hlen1' : 3 ≤ (R' 1).length := by
    change 3 ≤ (R 1).length
    dsimp [pathLength] at hlen1
    omega
  -- By 7.2 the replacement rung is even, and its distinct ends make it nonzero.
  have heven' : Even (pathLength P') :=
    (Workspace.Statements.S07.SPGT.thm_7_2 G hG _ b P' (R 1) (R 2) h').1.mpr heven1
  have hlen' : 2 ≤ pathLength P' := by
    have hh := Thm101ClaimOne.two_le_length hnew 0
    change 2 ≤ P'.length at hh
    rw [Nat.even_iff] at heven'
    dsimp [pathLength] at *
    omega
  -- The first linkage excludes every neighbour before the end of the new rung.
  have hbottom : G.Adj y (b 1) ∨ G.Adj y (b 2) := by tauto
  have htrim' : ∀ x ∈ P'.dropLast, ¬ G.Adj y x := by
    apply no_neighbor_before_end hG hnew hlen1' hy' hy1 hy2
    rcases hbottom with hb1 | hb2
    · exact Or.inr hb1
    · exact Or.inl ⟨b 2, PathBasics.getLast_mem h'.2.2.2.2.2.1.2.2, hb2⟩
  -- Otherwise y-a₂-a₁′-P₁′-b₁-y is an odd hole.
  have hnotb0 : ¬ G.Adj y (b 0) := by
    intro hyb0
    have ht := top_adj_rung hnew (i := 1) (j := 0) (by decide)
    exact even_rung_hole_absurd hG h'.2.2.2.1 heven' hlen'
      ht.1 ht.2 hy1 hyb0 htrim'
  have hyb1 : G.Adj y (b 1) := by tauto
  have hyb2 : G.Adj y (b 2) := by tauto
  -- The old prism supplies y-a₁-a₃-P₃-b₃-y, so P₃ minus b₃ has a neighbour.
  have hneighbor : ∃ x ∈ (R 2).dropLast, G.Adj y x := by
    by_contra hnone
    have ht := top_adj_rung h (i := 0) (j := 2) (by decide)
    apply even_rung_hole_absurd hG h.2.2.2.2.2.1 heven2 hlen2
      ht.1 ht.2 hya hyb2
    intro x hx hyx
    exact hnone ⟨x, hx, hyx⟩
  -- The final linkage uses a₃-P₃, the vertex a₂, and a₁′-P₁′-b₁-b₂.
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  have hswap := PrismSymmetry.formPrism_perm hnew σ
  have hforbid : ∀ x ∈ (R 2).dropLast, ¬ G.Adj y x := by
    apply no_neighbor_before_end (R := fun i => R' (σ i))
      (a := fun i => (![a', a 1, a 2] : Fin 3 → V) (σ i))
      (b := fun i => b (σ i)) hG hswap hlen1' hy2 hy1 hy'
    exact Or.inr hyb1
  obtain ⟨x, hx, hyx⟩ := hneighbor
  exact hforbid x hx hyx

/-- The two orientations of the printed proof give the new triangle's two neighbours. -/
theorem replacement_neighbors {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2))
    (heven1 : Even (pathLength (R 1))) (heven2 : Even (pathLength (R 2)))
    (hlen1 : 2 ≤ pathLength (R 1)) (hlen2 : 2 ≤ pathLength (R 2))
    {a' : V} {P' : List V}
    (h' : FormPrism G ![a', a 1, a 2] b P' (R 1) (R 2))
    {y : V} (hy : MajorForPrism G a b y) :
    2 ≤ (({a', a 1, a 2} : Set V) ∩ G.neighborSet y).ncard := by
  have hA := (two_neighbors_iff (h.1 0 1 (by decide)).ne
    (h.1 0 2 (by decide)).ne (h.1 1 2 (by decide)).ne).mp hy.1
  have hB := (two_neighbors_iff (h.2.1 0 1 (by decide)).ne
    (h.2.1 0 2 (by decide)).ne (h.2.1 1 2 (by decide)).ne).mp hy.2
  apply (two_neighbors_iff (h'.1 0 1 (by decide)).ne
    (h'.1 0 2 (by decide)).ne (h'.1 1 2 (by decide)).ne).mpr
  by_contra hno
  have hya : G.Adj y (a 0) := by tauto
  have hy' : ¬ G.Adj y a' := by tauto
  by_cases hy1 : G.Adj y (a 1)
  · have hy2 : ¬ G.Adj y (a 2) := by tauto
    exact oriented_contradiction hG h heven1 heven2 hlen1 hlen2 h' hya hy1 hy2 hy' hB
  · have hy2 : G.Adj y (a 2) := by tauto
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    have hs := PrismSymmetry.formPrism_perm h σ
    have hs' := PrismSymmetry.formPrism_perm
      (R := ![P', R 1, R 2]) h' σ
    have heq : (fun i => (![a', a 1, a 2] : Fin 3 → V) (σ i)) =
        ![a', a (σ 1), a (σ 2)] := by
      funext i
      fin_cases i <;> rfl
    rw [heq] at hs'
    have hBs : (G.Adj y (b (σ 0)) ∧ G.Adj y (b (σ 1))) ∨
        (G.Adj y (b (σ 0)) ∧ G.Adj y (b (σ 2))) ∨
          (G.Adj y (b (σ 1)) ∧ G.Adj y (b (σ 2))) := by
      change (G.Adj y (b 0) ∧ G.Adj y (b 2)) ∨
        (G.Adj y (b 0) ∧ G.Adj y (b 1)) ∨ (G.Adj y (b 2) ∧ G.Adj y (b 1))
      tauto
    exact oriented_contradiction (R := fun i => R (σ i))
      (a := fun i => a (σ i)) (b := fun i => b (σ i))
      hG hs heven2 heven1 hlen2 hlen1 hs'
      hya hy2 hy1 hy' hBs

end Workspace.ProofLemmas.Thm74Proof
