import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.KiteTailBasics

/-! Truncate `T` when it first reaches the rim, as in the minimum-path choice in 23.2. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper chooses `T` of minimum length.  For the attachment argument it suffices
to take a path inside the given `T` that first reaches `C \ {z}`.  Its interior is
outside the rim and is a subset of the original interior. -/
theorem first_rim_path {G : SimpleGraph V} {C T : List V} {z w x₀ x₁ : V}
    (hC : IsHoleList G C) (hzC : z ∈ C) (hnb : IsRimNeighbours G C z x₀ x₁)
    (hT : IsPathFrom G T z w) (hwC : w ∈ C) (hwz : w ≠ z)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁) :
    ∃ P : List V, ∃ b : V, IsPathFrom G P z b ∧ 3 ≤ P.length ∧
      b ∈ C ∧ b ≠ z ∧ ¬ G.Adj z b ∧
      (∀ v ∈ SPGT.interior P, v ∈ SPGT.interior T) ∧
      (∀ v ∈ SPGT.interior P, v ∉ C) := by
  have hzT := PathBasics.head_mem hT.2.1
  have hwT := PathBasics.getLast_mem hT.2.2
  have hpos := PathBasics.path_length_pos hT.1
  have htwo : 2 ≤ T.length := by
    by_contra hn
    have hlast := PathBasics.getElem_last_of_getLast? hT.2.2 hpos
    have hfirst := PathBasics.getElem_zero_of_head? hT.2.1 hpos
    have he : T.length - 1 = 0 := by omega
    exact hwz (hlast.symm.trans ((hT.1.2.1.getElem_inj_iff.mpr he).trans hfirst))
  have hza : ∃ a ∈ ({v : V | v ∈ T} : Set V), G.Adj z a := by
    refine ⟨T[1]'(by omega), List.getElem_mem _, ?_⟩
    have hadj := PathBasics.path_adj_succ hT.1 (i := 0) (by omega)
    rwa [PathBasics.getElem_zero_of_head? hT.2.1 hpos] at hadj
  obtain ⟨b, hb, P, hP, hPlen, hPT, hPB⟩ :=
    FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet G
      {v : V | v ∈ T} ({v : V | v ∈ C} \ {z}) z
      (connectedSet_of_isPathList hT.1) hza ⟨w, hwT, hwC, hwz⟩ (by simp)
  have hbC : b ∈ C := hb.2.1
  have hbz : b ≠ z := hb.2.2
  have hnbz : ¬ G.Adj z b := by
    intro hadj
    exact (hnb.2.2.2.2.2 b hbC hadj).elim (havoid b hb.1).1 (havoid b hb.1).2
  have hthree : 3 ≤ P.length := by
    have hlen : 2 ≤ P.length := by change 0 < P.length - 1 at hPlen; omega
    by_contra hn
    exact hnbz (PathBasics.isPathFrom_ends_adj_of_length_one hP
      (by change P.length - 1 = 1; omega))
  refine ⟨P, b, hP, hthree, hbC, hbz, hnbz, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvP, hvz, hvb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hv
    refine (PathBasics.mem_interior_iff_of_pathFrom hT).mpr ⟨hPT v hvP hvz, hvz, ?_⟩
    intro he
    exact hvb ((hPB v hvP).mp ⟨he ▸ hwC, hvz⟩)
  · intro v hv hvC
    obtain ⟨hvP, hvz, hvb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hv
    exact hvb ((hPB v hvP).mp ⟨hvC, hvz⟩)

/-- Each end of a path with at least three vertices attaches to its interior. -/
theorem end_attaches {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hlen : 3 ≤ P.length) :
    ∃ f ∈ SPGT.interior P, G.Adj a f := by
  refine ⟨P[1]'(by omega), PathBasics.getElem_mem_interior hP.1 (by omega)
    (by omega) (by omega), ?_⟩
  have hadj := PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
  rwa [PathBasics.getElem_zero_of_head? hP.2.1 (by omega)] at hadj

end Workspace.ProofLemmas.Thm232ClosingPath
