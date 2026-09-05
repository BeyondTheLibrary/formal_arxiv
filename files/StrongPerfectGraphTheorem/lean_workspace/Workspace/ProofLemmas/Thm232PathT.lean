import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.SkewPartitionFromSeparator
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.YEdgeFourConfig
import Workspace.ProofLemmas.Thm232FourYEdges
import Workspace.Statements.S15.Thm_15_1

/-!
# 23.2 — the path `T` from `z` to `A₀`

PAPER (23.2, printed p. 139):

> *"Let `A₀ = V(C) \ {z, x₀, x₁}`.  Since `G` does not admit a skew partition, there is a path
> `T` of `G \ {x₀,x₁}` from `z` to `A₀`, such that no vertex in its interior is in `Y` or
> `Y`-complete.  Let `y` be the neighbour of `z` in `T`."*

The conclusion below packages the path together with the shape `T = z :: y :: R` that names
its second vertex `y` — the paper's *"the neighbour of `z` in `T`"*.  `T` has at least two
vertices because its last vertex lies in `A₀`, which does not contain `z`.

The move *"since `G` does not admit a skew partition, there is a path …"* is the standard one
isolated in `Workspace.ProofLemmas.SkewPartitionFromSeparator`: the `Y`-complete vertices
together with `Y` separate `G`, so if the rest of `G` were disconnected `G` would have a skew
partition.

## Implementation notes

Two real obstacles, both recorded here so they are not rediscovered:

1. **The hypothesis is `¬ AdmitsBalancedSkewPartition G`, but the printed sentence says
   *"since `G` does not admit a skew partition"*.**  The ready-made tool
   `SkewPartitionFromSeparator.exists_path_interior_avoiding_of_no_skew_partition` wants the
   stronger `¬ AdmitsSkewPartition G`.  The printed proof of **23.4** makes the same step and
   there says *"Since `G` admits no skew partition **by 15.1**"*; the appeal in 23.2 is
   presumably the same one, so the discharge should route through
   `Workspace.Statements.S15.SPGT.thm_15_1` (or through the observation that the separation
   produced here is balanced) rather than assume the stronger hypothesis.
2. **Two different separators.**  *"a path `T` of `G \ {x₀,x₁}`"* asks every vertex of `T` to
   avoid `{x₀,x₁}`, while *"no vertex in its interior is in `Y` or `Y`-complete"* asks the
   **interior** to avoid `Y` and the `Y`-complete vertices.  So the separator to feed the
   machinery is `X := Y` with the extra deletion of `{x₀,x₁}` handled separately: `x₀, x₁` are
   themselves `Y`-complete, hence lie in the separator `Y ∪ {v | v is Y-complete}`, so a path
   whose interior avoids that separator automatically avoids `x₀, x₁` internally, and its two
   ends are `z` and a vertex of `A₀`, neither of which is `x₀` or `x₁`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232PathT

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (23.2, printed p. 139):** *"Since `G` does not admit a skew partition, there is a
path `T` of `G \ {x₀,x₁}` from `z` to `A₀`, such that no vertex in its interior is in `Y` or
`Y`-complete.  Let `y` be the neighbour of `z` in `T`."*

The statement carries **the three `Y`-completeness facts and the minimality clause that the
printed proof has in hand at this point** — the printed sentence is the second half of a
paragraph whose first half says *"the `Y`-complete edges in `C` are `x₀z, zx₁, c₁c₂, c₂c₃`"*
(so `x₀`, `z`, `x₁` are `Y`-complete, by `EdgeComplete`), and the minimality of the number of
`Y`-complete rim edges is the second half of the opening sentence of the proof.  Without them
the statement is not the paper's: nothing would force `T` to avoid `x₀, x₁`, and nothing would
supply a vertex outside the separator `Y ∪ {Y`-complete`}`.

The bridge *"`G` does not admit a skew partition"* is **15.1** (`thm_15_1`: a graph in `F₆`
admitting a skew partition admits a balanced one), exactly as the printed proof of 23.4 spells
out for the identical step. -/
theorem exists_clean_path (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (hmin : ∀ C' : List V, IsWheel G C' Y →
      OptimalWheelChoice.yEdgeCount G Y C ≤ OptimalWheelChoice.yEdgeCount G Y C')
    (z x₀ x₁ : V) (hz : z ∈ C) (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) :
    ∃ (T R : List V) (y w : V),
      T = z :: y :: R ∧
      IsPathFrom G T z w ∧ w ∈ C ∧ w ≠ z ∧ w ≠ x₀ ∧ w ≠ x₁ ∧
      (∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁) ∧
      (∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y) := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hCY : ∀ v ∈ C, v ∉ Y := hw.2.1.2.2
  have hYne : Y.Nonempty := hw.2.1.1
  -- **"Since `G` does not admit a skew partition"** — by 15.1, as 23.4 spells out.
  have hno : ¬ AdmitsSkewPartition G := fun h =>
    hbsp (_root_.Workspace.Statements.S15.SPGT.thm_15_1 G hG.1.1 h)
  have hNne : {q : V | VertexComplete G q Y}.Nonempty := ⟨z, hzY⟩
  have hB := SkewPartitionFromSeparator.not_anticonnectedSet_separator_of_nonempty
    (G := G) hYne hNne
  -- `A` is nonempty: by step (1) the rim carries only four `Y`-complete edges, so some rim
  -- position is not `Y`-complete, and no rim vertex lies in `Y`.
  have hAne : ((Y ∪ {q : V | VertexComplete G q Y})ᶜ).Nonempty := by
    have h4 : OptimalWheelChoice.yEdgeCount G Y C = 4 :=
      Thm232FourYEdges.exactly_four_yEdges G hG hbsp C Y hopt hmin
    obtain ⟨j, hj⟩ := YEdgeFourConfig.exists_not_cycVert hC hn6 h4
    exact ⟨C[j % C.length]'(Nat.mod_lt _ hn),
      SkewPartitionFromSeparator.mem_compl_separator_iff.mpr
        ⟨hCY _ (List.getElem_mem _),
          fun hcc => hj ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hn), hcc⟩⟩⟩
  -- the far end of `T`: any rim vertex outside `{z, x₀, x₁}`, i.e. any vertex of `A₀`
  obtain ⟨w, hwC, hwz, hw0, hw1⟩ : ∃ w : V, w ∈ C ∧ w ≠ z ∧ w ≠ x₀ ∧ w ≠ x₁ := by
    by_contra hcon
    push_neg at hcon
    have hsub : C.toFinset ⊆ ({z, x₀, x₁} : Finset V) := by
      intro v hv
      rw [List.mem_toFinset] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases e1 : v = z
      · exact Or.inl e1
      · by_cases e2 : v = x₀
        · exact Or.inr (Or.inl e2)
        · exact Or.inr (Or.inr (hcon v hv e1 e2))
    have hcard : C.toFinset.card = C.length := by
      rw [List.card_toFinset, List.Nodup.dedup hC.2.1]
    have hle := Finset.card_le_card hsub
    have a1 := Finset.card_insert_le z ({x₀, x₁} : Finset V)
    have a2 := Finset.card_insert_le x₀ ({x₁} : Finset V)
    have a3 : ({x₁} : Finset V).card = 1 := Finset.card_singleton _
    omega
  -- both ends are attached to `A` (an end that is `Y`-complete gets its neighbour in `A`
  -- from the absence of a skew partition)
  have hattach : ∀ u : V, u ∈ C →
      (u ∈ (Y ∪ {q : V | VertexComplete G q Y})ᶜ ∨
        ∃ a ∈ (Y ∪ {q : V | VertexComplete G q Y})ᶜ, G.Adj u a) := by
    intro u huC
    by_cases hcc : VertexComplete G u Y
    · refine Or.inr (SkewPartitionFromSeparator.exists_adj_compl_separator_of_no_skew_partition
        hno hYne hcc ?_ hAne)
      obtain ⟨-, -, a, b, c, e, haC, hbC, hcC, heC, hab, hce, hac, hae, hbc, hbe⟩ := hw
      by_cases hua : u = a
      · exact ⟨c, hce.2.1, by rw [hua]; exact Ne.symm hac⟩
      · exact ⟨a, hab.2.1, fun h => hua h.symm⟩
    · exact Or.inl (SkewPartitionFromSeparator.mem_compl_separator_iff.mpr ⟨hCY u huC, hcc⟩)
  obtain ⟨P, hP, hPY, hPint⟩ :=
    SkewPartitionFromSeparator.exists_path_interior_avoiding_of_no_skew_partition
      hno hB (hCY z hz) (hCY w hwC) (hattach z hz) (hattach w hwC)
  -- **"Let `y` be the neighbour of `z` in `T`"**: `P` has at least two vertices.
  obtain ⟨a, y, R, hPr⟩ : ∃ (a y : V) (R : List V), P = a :: y :: R := by
    rcases hPcase : P with _ | ⟨a, tl⟩
    · exact absurd hP.2.1 (by rw [hPcase]; simp)
    · rcases tl with _ | ⟨y, R⟩
      · exfalso
        have e1 : a = z := by have h := hP.2.1; rw [hPcase] at h; simpa using h
        have e2 : a = w := by have h := hP.2.2; rw [hPcase] at h; simpa using h
        exact hwz (e2.symm.trans e1)
      · exact ⟨a, y, R, rfl⟩
  have haz : a = z := by have h := hP.2.1; rw [hPr] at h; simpa using h
  rw [haz] at hPr
  -- an interior vertex is not `Y`-complete, so neither `x₀` nor `x₁` lies on `T`
  have key : ∀ u : V, VertexComplete G u Y → u ≠ z → u ≠ w → u ∉ P := by
    intro u huY huz huw hup
    exact hPint u ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hup, huz, huw⟩) huY
  refine ⟨P, R, y, w, hPr, hP, hwC, hwz, hw0, hw1, ?_, ?_⟩
  · intro v hv
    refine ⟨fun he => ?_, fun he => ?_⟩
    · exact key x₀ h0Y (hnb.2.2.2.1).ne' (fun h => hw0 h.symm) (he ▸ hv)
    · exact key x₁ h1Y (hnb.2.2.2.2.1).ne' (fun h => hw1 h.symm) (he ▸ hv)
  · intro v hv
    exact ⟨hPY v (PathBasics.interior_subset hv), hPint v hv⟩

end Workspace.ProofLemmas.Thm232PathT
