import Workspace.ProofLemmas.Thm192Claim7GapParity
import Workspace.ProofLemmas.Thm192Claim7GapUniqueEdge
import Workspace.ProofLemmas.Thm192Claim6Antihole

/-! Last-neighbour selection and the antihole reduction in claim (7) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim7GapEndpoint

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (claim (7)): "Choose `i` with `1 ≤ i ≤ n` maximum such that `x₂`
is adjacent to `pᵢ`." -/
theorem last_neighbour {G : SimpleGraph V} {P : List V} {a b u : V}
    (hP : IsPathFrom G P a b) (hub : ¬ G.Adj u b)
    (hnb : ∃ w ∈ SPGT.interior P, G.Adj u w) :
    ∃ (i : ℕ) (hi : i + 1 < P.length), 0 < i ∧ G.Adj u (P[i]'(by omega)) ∧
      ∀ k (hk : k < P.length), i ≤ k → (G.Adj u (P[k]'hk) ↔ k = i) := by
  classical
  obtain ⟨w, hw, huw⟩ := hnb
  obtain ⟨j, hj, hj1, hjn, hjw⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hw
  let pred := fun k => ∃ hk : k + 1 < P.length, 0 < k ∧ G.Adj u (P[k]'(by omega))
  have hpred : pred j := ⟨by omega, by omega, by rwa [hjw]⟩
  have hspec := Nat.findGreatest_spec (P := pred) (by omega : j ≤ P.length - 2) hpred
  obtain ⟨hi, hi0, hiadj⟩ := hspec
  refine ⟨Nat.findGreatest pred (P.length - 2), hi, hi0, hiadj, ?_⟩
  intro k hk hik
  constructor
  · intro hadj
    by_cases hki : k = Nat.findGreatest pred (P.length - 2)
    · exact hki
    by_cases hkl : k = P.length - 1
    · have hlast := PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
      subst k
      rw [hlast] at hadj
      exact (hub hadj).elim
    · exact (Nat.findGreatest_is_greatest (P := pred) (n := P.length - 2)
        (by omega) (by omega) ⟨by omega, by omega, hadj⟩).elim
  · rintro rfl
    exact hiadj

/-- After the parity step has shown that `y` meets `pᵢ`, the paper proves:
"Suppose that `i < n`. If `pᵢ` is not `Y`-complete then an antipath ... can be
extended ... contrary to 15.7. So `pᵢ` is `Y`-complete, and therefore so is `z`,
by (4). ... So `i = n`." -/
theorem complete_right_endpoint {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    (hyz : G.Adj y z) (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length)
    (hx2c : VertexComplete G (x 2) (Y \ {y})) (hx2y : ¬ G.Adj (x 2) y)
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hfirst : (∃ w ∈ SPGT.interior P, VertexComplete G w (Y ∪ {x 2})) → VertexComplete G z Y)
    (hno : VertexComplete G z Y → ∀ k (hk : k + 1 < P.length),
      ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    (hend : ¬ VertexComplete G (P[P.length - 2]'(by omega)) (Y ∪ {x 2}))
    (hboth : (∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧
      (∃ w ∈ SPGT.interior P, G.Adj y w)) :
    G.Adj (P[P.length - 2]'(by omega)) (x 2) ∧ G.Adj (P[P.length - 2]'(by omega)) y := by
  obtain ⟨i, hin, hi, hxI, hlast⟩ := last_neighbour hP hx21 hboth.1
  have hyI := Thm192Claim7GapParity.complete_last_neighbour_contact hG hws hHyp hyY hyz
    hY0 hP hPI hP5 hx2c hx2y hx20 hx21 hfirst hno hend hboth.2 hi hin hxI hlast
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hzP, hx2P, _, _⟩ := Thm192Claim6Basics.path_facts hBerge hws Set.Subset.rfl
    hP hPI (by omega)
  have hYout := Thm192Claim6Basics.Y_disjoint_path hHyp Set.Subset.rfl hP hPI
  have hpiI := PathBasics.getElem_mem_interior hP.1 (by omega : i < P.length) hi hin
  have hpiP := PathBasics.interior_subset hpiI
  have hC1 : IsHoleList G (z :: x 2 :: P.drop i) :=
    Thm192Infra.holeFromCut hP hPI (fun w hw => wheelSystemA_no_z w hw)
      (hws.2.2.2.2.2.2 0 (by omega)) (hws.2.2.2.2.2.2 1 (by omega))
      (hws.2.2.2.2.2.2 2 le_rfl) hzP hx2P hi (by omega) hlast
  have hpiC : (P[i]'(by omega)) ∈ z :: x 2 :: P.drop i := by
    simp only [List.mem_cons]
    right; right
    rw [List.mem_iff_getElem]
    exact ⟨0, by simp; omega, by simp⟩
  have hbC : x 1 ∈ z :: x 2 :: P.drop i := by
    simp only [List.mem_cons]
    right; right
    rw [List.mem_iff_getElem]
    refine ⟨P.length - 1 - i, by simp; omega, ?_⟩
    rw [List.getElem_drop]
    have he : i + (P.length - 1 - i) = P.length - 1 := by omega
    simpa only [he] using PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hinend : i = P.length - 2 := by
    by_contra hine
    have hClen : 4 < holeLength (z :: x 2 :: P.drop i) := by
      simp only [holeLength, List.length_cons, List.length_drop]
      omega
    have hpic : VertexComplete G (P[i]'(by omega)) Y := by
      by_contra hpinc
      have hpinc0 : ¬ VertexComplete G (P[i]'(by omega)) (Y \ {y}) := by
        intro hc
        apply hpinc
        intro v hv
        by_cases hvy : v = y
        · simpa only [hvy] using hyI.symm
        · exact hc v ⟨hv, hvy⟩
      obtain ⟨Q, hQ, hQI⟩ := Thm192Claim6Basics.antipath_to_y hHyp.2.1 hyY
        (hYout _ hpiP) hpinc0
      have hpib : ¬ G.Adj (P[i]'(by omega)) (x 1) := by
        rw [← PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
        exact PathBasics.path_not_adj_of_gap hP.1 (by omega) (by omega) (by omega) (by omega)
      exact Thm192Claim6Antihole.antihole_absurd hG.1 hQ hQI hyI.symm hxI.symm
        (hHyp.2.2.2.1 y hyY).symm (fun h => hx2y h.symm) hx21 hpib
        (hHyp.1 y hyY).2.2.2
        (fun h => by have := hws.2.1 2 le_rfl 1 (by omega) h; omega)
        ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hpiI).2.2 hx2c
        (fun v hv => hHyp.2.2.2.1 v hv.1) hC1 hClen hpiC (by simp) hbC
    have hzY : VertexComplete G z Y := hfirst ⟨_, hpiI, by
      intro v hv
      rcases hv with hv | rfl
      · exact hpic v hv
      · exact hxI.symm⟩
    have hCY : ∀ w ∈ z :: x 2 :: P.drop i, w ∉ Y := by
      intro w hw hwY
      rcases List.mem_cons.mp hw with hw | hw
      · exact (hHyp.1 w hwY).1 hw
      rcases List.mem_cons.mp hw with hw | hw
      · exact (hHyp.1 w hwY).2.2.2 hw
      · exact hYout w (List.mem_of_mem_drop hw) hwY
    have hclass := Thm192Claim7GapUniqueEdge.cut_only_complete hBerge hHyp.2.1 hP hi hin
      hC1 hCY hzY hHyp.2.2.2.1 hHyp.2.2.2.2.1 (hws.2.2.2.2.2.2 1 (by omega))
      (fun w hw => wheelSystemA_no_z w (hPI w hw)) (hno hzY) _ hpiC hpic
    rcases hclass with hpiz | hpib
    · exact hzP (hpiz ▸ hpiP)
    · exact ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hpiI).2.2 hpib
  subst i
  exact ⟨hxI.symm, hyI.symm⟩

/-- The right endpoint conclusions in the noncomplete case, including the
application of (4) that excludes its edge to `y`. -/
theorem noncomplete_right_endpoint {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    (hyz : G.Adj y z) {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length) (hW : IsWheel G (z :: P) (Y \ {y}))
    (hx2nc : ¬ VertexComplete G (x 2) (Y \ {y}))
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hzY : VertexComplete G z Y)
    (hno : ∀ k (hk : k + 1 < P.length), ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    (hboth : (∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧
      (∃ w ∈ SPGT.interior P, G.Adj y w)) :
    G.Adj (P[P.length - 2]'(by omega)) (x 2) ∧
    VertexComplete G (P[P.length - 2]'(by omega)) (Y \ {y}) ∧
    ¬ G.Adj (P[P.length - 2]'(by omega)) y ∧ G.Adj y (x 2) := by
  obtain ⟨i, hin, hi, hxI, hlast⟩ := last_neighbour hP hx21 hboth.1
  obtain ⟨hiend, hpc, hyx⟩ := Thm192Claim7GapParity.noncomplete_short_cut hG hws hHyp hyY
    hyz hP hPI hP5 hW hx2nc hx20 hx21 hzY hno hboth.2 hi hin hxI hlast
  subst i
  refine ⟨hxI.symm, hpc, ?_, hyx⟩
  intro hpny
  apply hno (P.length - 2) (by omega)
  refine ⟨PathBasics.path_adj_succ hP.1 (by omega), ?_, ?_⟩
  · intro v hv
    by_cases hvy : v = y
    · simpa only [hvy] using hpny
    · exact hpc v ⟨hv, hvy⟩
  · have hidx : (P.length - 2) + 1 = P.length - 1 := by omega
    have he : (P[(P.length - 2) + 1]'(by omega)) = x 1 := by
      simpa only [hidx] using PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
    rw [he]
    exact hHyp.2.2.2.1

theorem penultimate_reverse (P : List V) (hP : 3 ≤ P.length) :
    (P.reverse[P.reverse.length - 2]'(by simp; omega)) = (P[1]'(by omega)) := by
  simp only [List.getElem_reverse, List.length_reverse]
  congr 1
  omega

theorem no_edge_reverse {G : SimpleGraph V} {Y : Set V} {P : List V}
    (hP : IsPathList G P)
    (hno : ∀ k (hk : k + 1 < P.length), ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk)) :
    ∀ k (hk : k + 1 < P.reverse.length),
      ¬ EdgeComplete G Y (P.reverse[k]'(by omega)) (P.reverse[k+1]'hk) := by
  intro k hk hE
  exact Thm192Claim7GapUniqueEdge.no_edge_any hP hno _
    (List.mem_reverse.mp (List.getElem_mem (by omega))) _
    (List.mem_reverse.mp (List.getElem_mem hk)) hE

end Workspace.ProofLemmas.Thm192Claim7GapEndpoint
