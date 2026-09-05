import Workspace.ProofLemmas.Thm192Claim6Basics
import Workspace.ProofLemmas.PathAttach

/-! The antihole contradiction used in claims (6) and (7) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim6Antihole

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (claim (6)): "an antipath between `p₁` and `y` with interior in `Y₀`
can be extended to an antihole via `y-x₂-x₁-p₁`, and this antihole shares the
vertices `p₁,x₁,x₂` with the hole ... contrary to 15.7."
The same argument is used with `pᵢ` in claim (7). -/
theorem antihole_absurd {G : SimpleGraph V} (hG : InF6 G)
    {W : Set V} {p y u b : V} {Q C : List V}
    (hQ : IsAntipathFrom G Q p y) (hQI : ∀ w ∈ SPGT.interior Q, w ∈ W)
    (hpy : G.Adj p y) (hpu : G.Adj p u) (hyb : G.Adj y b)
    (hyu : ¬ G.Adj y u) (hub : ¬ G.Adj u b) (hpb : ¬ G.Adj p b)
    (hyune : y ≠ u) (hubne : u ≠ b) (hpbne : p ≠ b)
    (huW : VertexComplete G u W) (hbW : VertexComplete G b W)
    (hC : IsHoleList G C) (hClen : 4 < holeLength C)
    (hpC : p ∈ C) (huC : u ∈ C) (hbC : b ∈ C) : False := by
  have hub' : Gᶜ.Adj u b := (SimpleGraph.compl_adj G u b).mpr ⟨hubne, hub⟩
  have hR : IsAntipathFrom G [y, u, b, p] y p := by
    apply PathAttach.isPathFrom_cons_concat
      (show IsPathFrom Gᶜ [u, b] u b from ⟨PathBasics.isPathList_pair hub', rfl, rfl⟩)
      ((SimpleGraph.compl_adj G y u).mpr ⟨hyune, hyu⟩)
      ((SimpleGraph.compl_adj G p b).mpr ⟨hpbne, hpb⟩)
      (fun h => ((SimpleGraph.compl_adj G y p).mp h).2 hpy.symm) hpy.ne.symm
    · simp [hyune, hyb.ne]
    · simp [hpu.ne, hpbne]
    · intro v hv hvu hcon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hv | hv
      · exact hvu hv
      · rw [hv] at hcon
        exact ((SimpleGraph.compl_adj G y b).mp hcon).2 hyb
    · intro v hv hvb hcon
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with hv | hv
      · rw [hv] at hcon
        exact ((SimpleGraph.compl_adj G p u).mp hcon).2 hpu
      · exact hvb hv
  apply Thm192Infra.antipathExtendToAntihole hG hpy hQ hQI hR (by simp)
    (by intro w hw; simp only [SPGT.interior, List.tail_cons, List.dropLast_cons_cons,
      List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw
        ; rcases hw with rfl | rfl; exact huW; exact hbW)
    hC hClen hpu.ne hpbne hubne hpC huC hbC
  · exact List.mem_append_left _ (PathBasics.head_mem hQ.2.1)
  · simp [SPGT.interior]
  · simp [SPGT.interior]

end Workspace.ProofLemmas.Thm192Claim6Antihole
