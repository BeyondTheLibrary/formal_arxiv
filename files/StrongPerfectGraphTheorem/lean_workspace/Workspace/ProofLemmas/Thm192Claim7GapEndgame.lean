import Workspace.ProofLemmas.Thm192Claim7GapCatch
import Workspace.ProofLemmas.Thm192Claim7GapPrism
import Workspace.ProofLemmas.ClassLemmas

/-! Both final contradictions of claim (7), once its endpoint facts have been proved. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim7GapEndgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The four end-to-interior incidences of `x₀-p₁-⋯-pₙ-x₁`. -/
theorem endpoint_facts {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hP5 : 5 ≤ P.length) :
    G.Adj (P[1]'(by omega)) a ∧ G.Adj (P[P.length - 2]'(by omega)) b ∧
    ¬ G.Adj (P[1]'(by omega)) b ∧ ¬ G.Adj (P[P.length - 2]'(by omega)) a ∧
    (P[1]'(by omega)) ≠ (P[P.length - 2]'(by omega)) := by
  have h0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hN := PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0]
    exact (PathBasics.path_adj_iff hP.1 (by omega) (by omega)).mpr (by omega)
  · rw [← hN]
    exact (PathBasics.path_adj_iff hP.1 (by omega) (by omega)).mpr (by omega)
  · rw [← hN]
    exact PathBasics.path_not_adj_of_gap hP.1 (by omega) (by omega) (by omega) (by omega)
  · rw [← h0]
    exact PathBasics.path_not_adj_of_gap hP.1 (by omega) (by omega) (by omega) (by omega)
  · exact PathBasics.path_ne_of_ne_index hP.1 (by omega) (by omega) (by omega)

/-- PAPER (claim (7)): "So in [the complement], the connected set
`Y ∪ {p₁,pₙ}` catches the triangle `{x₀,x₁,x₂}` ... contrary to 17.1." -/
theorem complete_endpoints_absurd {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y A : Set V} (hHyp : Hyp192 G z A₀ x Y) (hA : A ⊆ wheelSystemA G z A₀ x 1)
    {y : V} (hyY : y ∈ Y) {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ A) (hP5 : 5 ≤ P.length)
    (hx2c : VertexComplete G (x 2) (Y \ {y})) (hx2y : ¬ G.Adj (x 2) y)
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hp1x : G.Adj (P[1]'(by omega)) (x 2))
    (hpnx : G.Adj (P[P.length - 2]'(by omega)) (x 2))
    (hp1y : G.Adj (P[1]'(by omega)) y)
    (hpny : G.Adj (P[P.length - 2]'(by omega)) y)
    (hp1nc : ¬ VertexComplete G (P[1]'(by omega)) Y)
    (hpnnc : ¬ VertexComplete G (P[P.length - 2]'(by omega)) Y) : False := by
  let p := P[1]'(by omega)
  let q := P[P.length - 2]'(by omega)
  have hpI : p ∈ SPGT.interior P := PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)
  have hqI : q ∈ SPGT.interior P := PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)
  obtain ⟨hp0, hq1, hpn1, hqn0, hpq⟩ := endpoint_facts hP hP5
  change G.Adj p (x 0) at hp0
  change G.Adj q (x 1) at hq1
  change ¬ G.Adj p (x 1) at hpn1
  change ¬ G.Adj q (x 0) at hqn0
  change p ≠ q at hpq
  have hYout := Thm192Claim6Basics.Y_disjoint_path hHyp hA hP hPI
  have hpY : p ∉ Y := hYout p (PathBasics.interior_subset hpI)
  have hqY : q ∉ Y := hYout q (PathBasics.interior_subset hqI)
  have hpy : p ≠ y := fun he => hpY (he ▸ hyY)
  have hqy : q ≠ y := fun he => hqY (he ▸ hyY)
  have hpends := ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hpI).2
  have hqends := ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hqI).2
  let F : Set V := (Y ∪ {p}) ∪ {q}
  have hFconn : AnticonnectedSet G F :=
    KiteTailBasics.anticonnectedSet_union_singleton
      (KiteTailBasics.anticonnectedSet_union_singleton hHyp.2.1 hp1nc)
      (fun h => hpnnc (fun v hv => h v (Or.inl hv)))
  have hdisj : Disjoint F ({x 0, x 1, x 2} : Set V) := by
    apply Set.disjoint_left.mpr
    intro v hv hvT
    have hv' : v ∈ Y ∨ v = p ∨ v = q := by simpa only [F, Set.mem_union, Set.mem_singleton_iff, or_assoc] using hv
    rcases hv' with hvY | hv | hv
    · have hs := hHyp.1 v hvY
      rcases hvT with hv0 | hv1 | hv2
      · exact hs.2.1 hv0
      · exact hs.2.2.1 hv1
      · exact hs.2.2.2 hv2
    · rw [hv] at hvT
      rcases hvT with hv0 | hv1 | hv2
      · exact hpends.1 hv0
      · exact hpends.2 hv1
      · exact hp1x.ne hv2
    · rw [hv] at hvT
      rcases hvT with hv0 | hv1 | hv2
      · exact hqends.1 hv0
      · exact hqends.2 hv1
      · exact hpnx.ne hv2
  have hxne : ∀ i ≤ 2, ∀ j ≤ 2, i ≠ j → x i ≠ x j := by
    intro i hi j hj hij heq
    exact hij (hws.2.1 i hi j hj heq)
  have hqycomp : Gᶜ.Adj q y := Thm192Claim7GapCatch.unique_neighbours_adjacent
    (ClassLemmas.inF7_compl.mpr hG)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hxne 0 (by omega) 1 (by omega) (by omega), x0_not_adj_x1 hws⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hxne 0 (by omega) 2 le_rfl (by omega), fun h => hx20 h.symm⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hxne 1 (by omega) 2 le_rfl (by omega), fun h => hx21 h.symm⟩)
    hFconn hdisj (Or.inr rfl) (Or.inl (Or.inr rfl)) (Or.inl (Or.inl hyY))
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hqends.1.symm, fun h => hqn0 h.symm⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hpends.2.symm, fun h => hpn1 h.symm⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨(hHyp.1 y hyY).2.2.2.symm, hx2y⟩)
    (by
      intro v hv hadj
      have hn := ((SimpleGraph.compl_adj G _ _).mp hadj).2
      have hv' : v ∈ Y ∨ v = p ∨ v = q := by simpa only [F, Set.mem_union, Set.mem_singleton_iff, or_assoc] using hv
      rcases hv' with hv | hv | hv
      · exact (hn (hHyp.2.2.1 v hv)).elim
      · exact (hn (hv ▸ hp0.symm)).elim
      · exact hv)
    (by
      intro v hv hadj
      have hn := ((SimpleGraph.compl_adj G _ _).mp hadj).2
      have hv' : v ∈ Y ∨ v = p ∨ v = q := by simpa only [F, Set.mem_union, Set.mem_singleton_iff, or_assoc] using hv
      rcases hv' with hv | hv | hv
      · exact (hn (hHyp.2.2.2.1 v hv)).elim
      · exact hv
      · exact (hn (hv ▸ hq1.symm)).elim)
    (by
      intro v hv hadj
      have hn := ((SimpleGraph.compl_adj G _ _).mp hadj).2
      have hv' : v ∈ Y ∨ v = p ∨ v = q := by simpa only [F, Set.mem_union, Set.mem_singleton_iff, or_assoc] using hv
      rcases hv' with hv | hv | hv
      · by_contra hvy
        exact hn (hx2c v ⟨hv, hvy⟩)
      · exact (hn (hv ▸ hp1x.symm)).elim
      · exact (hn (hv ▸ hpnx.symm)).elim)
    hpq.symm hqy hpy
  exact ((SimpleGraph.compl_adj G q y).mp hqycomp).2 hpny

/-- The two endpoint conclusions in the first case of (7) give the three
antipaths named in the paper's long-prism contradiction. -/
theorem noncomplete_endpoints_absurd {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1)) (hP5 : 5 ≤ P.length)
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}))
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hp1x : G.Adj (P[1]'(by omega)) (x 2))
    (hpnx : G.Adj (P[P.length - 2]'(by omega)) (x 2))
    (hp1y : ¬ G.Adj (P[1]'(by omega)) y)
    (hpny : ¬ G.Adj (P[P.length - 2]'(by omega)) y)
    (hp1c : VertexComplete G (P[1]'(by omega)) (Y \ {y}))
    (hpnc : VertexComplete G (P[P.length - 2]'(by omega)) (Y \ {y}))
    (hyx : G.Adj y (x 2)) : False := by
  have hx2Y : x 2 ∉ Y := fun h => (hHyp.1 _ h).2.2.2 rfl
  obtain ⟨Q, hQ, hQI⟩ := Thm192Claim6Basics.antipath_to_y hHyp.2.1 hyY hx2Y hx2nc
  obtain ⟨hp0, hq1, hpn1, hqn0, hpq⟩ := endpoint_facts hP hP5
  have hpI := PathBasics.getElem_mem_interior hP.1 (by omega : 1 < P.length) (by omega) (by omega)
  have hqI := PathBasics.getElem_mem_interior hP.1
    (by omega : P.length - 2 < P.length) (by omega) (by omega)
  have hpends := ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hpI).2
  have hqends := ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hqI).2
  have hpqna : ¬ G.Adj (P[1]'(by omega)) (P[P.length - 2]'(by omega)) :=
    PathBasics.path_not_adj_of_gap hP.1 (by omega) (by omega) (by omega) (by omega)
  have hpyne : (P[1]'(by omega)) ≠ y := by
    intro he
    have hh : G.Adj (P[1]'(by omega)) (x 1) := he ▸ (hHyp.2.2.2.1 y hyY).symm
    exact hpn1 hh
  have hqyne : (P[P.length - 2]'(by omega)) ≠ y := by
    intro he
    have hh : G.Adj (P[P.length - 2]'(by omega)) (x 0) := he ▸ (hHyp.2.2.1 y hyY).symm
    exact hqn0 hh
  have hxne : ∀ i ≤ 2, ∀ j ≤ 2, i ≠ j → x i ≠ x j := by
    intro i hi j hj hij heq
    exact hij (hws.2.1 i hi j hj heq)
  exact Thm192Claim7GapPrism.prism_absurd hG (PathBasics.isPathFrom_reverse hQ)
    (fun v hv => hQI v (PathBasics.mem_interior_reverse.mp hv)) hp1c hpnc
    (fun v hv => hHyp.2.2.1 v hv.1) (fun v hv => hHyp.2.2.2.1 v hv.1)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hpq, hpqna⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hpyne, hp1y⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hqyne, hpny⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hxne 1 (by omega) 0 (by omega) (by omega),
      fun h => x0_not_adj_x1 hws h.symm⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hxne 1 (by omega) 2 le_rfl (by omega), fun h => hx21 h.symm⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hxne 0 (by omega) 2 le_rfl (by omega), fun h => hx20 h.symm⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hpends.2, hpn1⟩)
    ((SimpleGraph.compl_adj G _ _).mpr ⟨hqends.1, hqn0⟩)
    hp0 hp1x hq1 hpnx (hHyp.2.2.2.1 y hyY) (hHyp.2.2.1 y hyY) hyx

end Workspace.ProofLemmas.Thm192Claim7GapEndgame
