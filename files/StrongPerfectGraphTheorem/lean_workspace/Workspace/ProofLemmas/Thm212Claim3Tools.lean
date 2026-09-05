import Workspace.ProofLemmas.Thm203AntipathTools
import Workspace.Statements.S17.Thm_17_1
import Workspace.Statements.S20.Thm_20_3

/-! The two applications of 2.2 in 21.2(3), followed by its reflection obstruction. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm212Claim3Tools

open Workspace.Types.Core Workspace.Types.Core.SPGT Workspace.Types.Classes.SPGT
open Workspace.Types.TriangleCatching.SPGT Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (21.2(3), p. 132): "Let `Q` be an antipath between `f,x_{t+1}`
with interior in `X_t`. ... it follows that `Q` is even. ... By 2.2 applied in
the complement, it follows that `f` has a neighbour in `A_{t-1} ∪ {p₁,…,p_m}`."
Here `A` is `A_{t-1}` and `B` is that larger connected set. -/
theorem neighbor_of_two_antipaths {G : SimpleGraph V} (hG : Berge G)
    {A B X : Set V} {z y u f : V}
    (hA : ConnectedSet G A) (hB : ConnectedSet G B) (hAB : A ⊆ B)
    (hX : AnticonnectedSet G X)
    (hzB : z ∉ B) (hzanti : VertexAnticomplete G z B)
    (hzX : VertexComplete G z X) (hyX : VertexComplete G y X)
    (hzU : G.Adj z u) (huB : u ∉ B) (hfB : f ∉ B)
    (huX : u ∉ X) (hfX : f ∉ X)
    (hunc : ¬ VertexComplete G u X) (hfnc : ¬ VertexComplete G f X)
    (huf : G.Adj u f) (hyf : G.Adj y f) (hyu : ¬ G.Adj y u)
    (hyNotB : y ∉ B) (hyB : VertexAnticomplete G y B)
    (huA : VertexAnticomplete G u A) (hfA : VertexAnticomplete G f A)
    (huNbr : ∃ b ∈ B, G.Adj u b)
    (hXNbr : ∀ w ∈ X, ∃ a ∈ A, G.Adj w a) :
    ∃ b ∈ B, G.Adj f b := by
  classical
  have hunc' : ∃ w ∈ X, ¬ G.Adj u w := by
    simpa only [VertexComplete, not_forall, exists_prop] using hunc
  have hfnc' : ∃ w ∈ X, ¬ G.Adj f w := by
    simpa only [VertexComplete, not_forall, exists_prop] using hfnc
  obtain ⟨Q, hQ, hQI⟩ := InducedPathExtraction.exists_antipath_interior_in
    hX hfX huX hfnc' hunc'
  have hQB : ∀ w ∈ Q, w ∉ B := by
    intro w hw hwB
    by_cases hwf : w = f
    · exact hfB (hwf ▸ hwB)
    by_cases hwu : w = u
    · exact huB (hwu ▸ hwB)
    exact hzanti w hwB (hzX w (hQI w
      ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hw, hwf, hwu⟩)))
  have hQeven : Even (pathLength Q) := by
    apply Nat.not_odd_iff_even.mp
    intro hodd
    rcases Thm203AntipathTools.exists_end_nbr_of_odd_antipath hG hA
        (fun hzA => hzB (hAB hzA)) (fun a ha => hzanti a (hAB ha))
        hQ hodd huf.symm (fun w hw hwA => hQB w hw (hAB hwA))
        (fun w hw => hXNbr w (hQI w hw)) (fun w hw => hzX w (hQI w hw)) with
      ⟨a, ha, hfa⟩ | ⟨a, ha, hua⟩
    · exact hfA a ha hfa
    · exact huA a ha hua
  have hyQ : ∀ w ∈ Q, w ≠ u → G.Adj y w := by
    intro w hw hwu
    by_cases hwf : w = f
    · simpa only [hwf] using hyf
    · exact hyX w (hQI w
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hw, hwf, hwu⟩))
  have hyne : y ≠ u := by
    intro he
    obtain ⟨b, hb, hub⟩ := huNbr
    exact hyB b hb (he ▸ hub)
  have hyNotQ : y ∉ Q := fun hyQmem => G.irrefl (hyQ y hyQmem hyne)
  have hR : IsAntipathFrom G (y :: Q.reverse) y f :=
    PathAttach.isPathFrom_cons (PathBasics.isAntipathFrom_reverse hQ)
      ((SimpleGraph.compl_adj G y u).mpr ⟨hyne, hyu⟩)
      (by simpa using hyNotQ)
      (fun w hw hwu hc => ((SimpleGraph.compl_adj G y w).mp hc).2
        (hyQ w (by simpa using hw) hwu))
  have hRodd : Odd (pathLength (y :: Q.reverse)) := by
    obtain ⟨d, hd⟩ := hQeven
    refine ⟨d, ?_⟩
    have hpos := PathBasics.path_length_pos hQ.1
    simp only [pathLength, List.length_cons, List.length_reverse] at *
    omega
  have hRint : ∀ w ∈ SPGT.interior (y :: Q.reverse),
      w = u ∨ w ∈ X := by
    intro w hw
    have hw' := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hw
    have hwQ : w ∈ Q := by
      rcases List.mem_cons.mp hw'.1 with hwy | hwQ
      · exact (hw'.2.1 hwy).elim
      · simpa using hwQ
    by_cases hwu : w = u
    · exact Or.inl hwu
    · exact Or.inr (hQI w
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hwQ, hw'.2.2, hwu⟩))
  have hRB : ∀ w ∈ y :: Q.reverse, w ∉ B := by
    intro w hw hwB
    rcases List.mem_cons.mp hw with rfl | hwQ
    · exact hyNotB hwB
    · exact hQB w (by simpa using hwQ) hwB
  have hRnbr : ∀ w ∈ SPGT.interior (y :: Q.reverse), ∃ b ∈ B, G.Adj w b := by
    intro w hw
    rcases hRint w hw with rfl | hwX
    · exact huNbr
    · obtain ⟨a, ha, hwa⟩ := hXNbr w hwX
      exact ⟨a, hAB ha, hwa⟩
  have hRz : ∀ w ∈ SPGT.interior (y :: Q.reverse), G.Adj z w := by
    intro w hw
    rcases hRint w hw with rfl | hwX
    · exact hzU
    · exact hzX w hwX
  rcases Thm203AntipathTools.exists_end_nbr_of_odd_antipath hG hB hzB hzanti
      hR hRodd hyf hRB hRnbr hRz with ⟨b, hb, hyb⟩ | hf
  · exact (hyB b hb hyb).elim
  · exact hf

/-- PAPER (21.2(3), pp. 132–133): "By 17.1, `F'` contains a reflection of
the triangle, and hence there is a vertex in `F'` adjacent to both of `z,p₁`."
The unique neighbour of `u` is `z`, and no vertex of the catching set meets
both `z` and `v`. -/
theorem catch_obstruction {G : SimpleGraph V} (hG : InF7 G)
    {F T : Set V} {u v z : V} (hc : Catches G F T)
    (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v)
    (hunique : ∀ w ∈ F, G.Adj u w → w = z)
    (hcommon : ∀ w ∈ F, G.Adj z w → ¬ G.Adj v w)
    (hone : ∀ w ∈ F, (G.neighborSet w ∩ T).ncard ≤ 1) : False := by
  rcases Workspace.Statements.S17.SPGT.thm_17_1 G hG T hc.1 F
      (fun w hw hwT => Set.disjoint_left.mp hc.2.2.1 hw hwT) hc with href | htwo
  · obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, heq, hbF, href⟩ := href
    obtain ⟨bu, hbu, bv, hbv, hubu, hvbv, hbb⟩ :=
      Scratch203.reflection_pair href (by rwa [← heq]) (by rwa [← heq]) huv
    have he : bu = z := hunique bu (hbF hbu) hubu
    exact hcommon bv (hbF hbv) (by rwa [← he]) hvbv
  · obtain ⟨w, hw, htwo⟩ := htwo
    have := hone w hw
    omega

end Workspace.ProofLemmas.Thm212Claim3Tools
