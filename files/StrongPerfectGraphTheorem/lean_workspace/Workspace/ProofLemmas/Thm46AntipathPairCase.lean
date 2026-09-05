import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Statements.S04.Thm_4_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm46AntipathPairCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-  The antipath-pair case of the proof of **4.6**: if `(A₁, B₂)` is an antipath pair
    while `A₁` is balanced with respect to the kernel `W` and contains no `W`-complete
    vertex, a contradiction follows.  -/
theorem antipath_pair_case {G : SimpleGraph V} (hG : Berge G) {A B W A₁ B₂ : Set V}
    (hAB : IsSkewPartition G A B) (hWB : W ⊆ B) (hWanti : AnticonnectedSet G W)
    (hA₁ : IsComponent G A A₁)
    (hnoWcomp : ∀ v ∈ A₁, ¬ VertexComplete G v W)
    (hbal1 : SPGT.Balanced G A₁ W)
    (hpair : IsAntipathPair G A B A₁ B₂)
    (hcon : ¬ AdmitsBalancedSkewPartition G) :
    False := by
  classical
  obtain ⟨-, -, hB₂, q₁, u, v, hu, hv, huv, hq₁, hq₁int, hq₁odd⟩ := hpair
  have huW : u ∉ W := by
    intro hu'
    exact Set.disjoint_left.mp hAB.2.1 (hA₁.1 hu) (hWB hu')
  have hvW : v ∉ W := by
    intro hv'
    exact Set.disjoint_left.mp hAB.2.1 (hA₁.1 hv) (hWB hv')
  have hunon : ∃ w ∈ W, ¬ G.Adj u w := by
    have hn := hnoWcomp u hu
    simp only [VertexComplete, not_forall] at hn
    obtain ⟨w, hw, hnw⟩ := hn
    exact ⟨w, hw, hnw⟩
  have hvnon : ∃ w ∈ W, ¬ G.Adj v w := by
    have hn := hnoWcomp v hv
    simp only [VertexComplete, not_forall] at hn
    obtain ⟨w, hw, hnw⟩ := hn
    exact ⟨w, hw, hnw⟩
  obtain ⟨q₂, hq₂, hq₂int⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_antipath_interior_in
      hWanti huW hvW hunon hvnon
  rcases Nat.even_or_odd (pathLength q₂) with hq₂even | hq₂odd
  · exact hcon (Workspace.Statements.S04.SPGT.thm_4_3 G hG A B hAB
      (Or.inr ⟨u, v, q₁, q₂, hA₁.1 hu, hA₁.1 hv, hq₁,
        (fun x hx => hB₂.1 (hq₁int x hx)), hq₁odd, hq₂,
        (fun x hx => hWB (hq₂int x hx)), hq₂even⟩)).2
  · exact hbal1.2 u v q₂ hu hv huv hq₂ hq₂int hq₂odd

end Workspace.ProofLemmas.Thm46AntipathPairCase
