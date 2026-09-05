import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.YDiamondTruncation
import Workspace.ProofLemmas.Thm203Prelim

/-!
# The two antipath arguments §20.3 repeats, and the `Y`-square truncation

Sections 19–20 apply 2.2 and 13.6 **in `Ḡ`** to an antipath whose internal vertices all
have neighbours in some connected set `T` while its ends do not.  The proof of 20.3 does
this five times, in three different paragraphs, always with the same bookkeeping:

* `exists_end_nbr_of_odd_antipath` is *"since all internal vertices of `Q` have neighbours
  in `A_{t−3}`, and `z` is complete to its interior and anticomplete to `A_{t−3}`, it
  follows from 2.2 applied in `Ḡ` that one end of `Q` has a neighbour in `A_{t−3}`"*
  (printed pp. 126, 127).

* `antipath_length_three_of_odd` is *"all its internal vertices have neighbours in the
  connected set `T` and its ends do not, so by 13.6 this antipath has length 3"*
  (printed pp. 126, 127).  Its contrapositive is the *"so by 13.6 it has even length"* of
  the final paragraph.

In both, the hypothesis `huvadj : G.Adj u v` is what rules out 13.6's / 2.2's
`T`-complete-edge alternative: the only vertices of the antipath that can be `Ḡ`-complete
to `T` are its two ends, and they are `G`-adjacent, hence not `Ḡ`-adjacent.

`ysquare_truncate_union` is the `Y`-square counterpart of
`YDiamondTruncation.ydiamond_truncate_union`: *"But then `x₀,…,x_{t−1}` is a
`Y ∪ {x_t}`-square of height `t − 1`"* (printed pp. 126, 127, used twice inside step (3)).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm203AntipathTools

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Ḡ`-anticonnectedness is `G`-connectedness. -/
theorem anticonnected_compl {G : SimpleGraph V} {S : Set V} (h : ConnectedSet G S) :
    AnticonnectedSet Gᶜ S := by
  show ConnectedSet Gᶜᶜ S
  rwa [compl_compl]

/-- Being `Ḡ`-complete to `S` means being distinct from and nonadjacent to every vertex
of `S`. -/
theorem vertexComplete_compl_iff {G : SimpleGraph V} {v : V} {S : Set V} :
    VertexComplete Gᶜ v S ↔ ∀ s ∈ S, v ≠ s ∧ ¬ G.Adj v s := by
  constructor
  · intro h s hs
    have h2 := h s hs
    rw [SimpleGraph.compl_adj] at h2
    exact h2
  · intro h s hs
    rw [SimpleGraph.compl_adj]
    exact h s hs

/-- Only the ends of the antipath can be `Ḡ`-complete to `T`, and they are `G`-adjacent, so
there is no `T`-complete edge of `Ḡ` inside the antipath. -/
private theorem noedge {G : SimpleGraph V} {T : Set V} {Q : List V} {u v : V}
    (hQ : IsAntipathFrom G Q u v) (huvadj : G.Adj u v)
    (hintT : ∀ w ∈ SPGT.interior Q, ∃ a ∈ T, G.Adj w a) :
    ¬ ∃ a ∈ Q, ∃ b ∈ Q, EdgeComplete Gᶜ T a b := by
  have hQp : IsPathFrom Gᶜ Q u v := hQ
  have hends : ∀ w ∈ Q, VertexComplete Gᶜ w T → w = u ∨ w = v := by
    intro w hw hwC
    by_cases h1 : w = u
    · exact Or.inl h1
    by_cases h2 : w = v
    · exact Or.inr h2
    exfalso
    obtain ⟨a, ha, hadj⟩ := hintT w
      ((PathBasics.mem_interior_iff_of_pathFrom hQp).mpr ⟨hw, h1, h2⟩)
    exact (vertexComplete_compl_iff.mp hwC a ha).2 hadj
  rintro ⟨a, ha, b, hb, hadj, haC, hbC⟩
  rcases hends a ha haC with rfl | rfl <;> rcases hends b hb hbC with hb' | hb'
  · exact Gᶜ.irrefl (hb' ▸ hadj)
  · rw [hb', SimpleGraph.compl_adj] at hadj
    exact hadj.2 huvadj
  · rw [hb', SimpleGraph.compl_adj] at hadj
    exact hadj.2 huvadj.symm
  · exact Gᶜ.irrefl (hb' ▸ hadj)

/-- **2.2 applied in `Ḡ`.**  An odd antipath whose internal vertices all have neighbours in
the connected set `T`, and to whose interior `z` is complete while being anticomplete to
`T`, must have an end with a neighbour in `T`. -/
theorem exists_end_nbr_of_odd_antipath {G : SimpleGraph V} (hBerge : Berge G)
    {z : V} {T : Set V} (hTcon : ConnectedSet G T) (hzT : z ∉ T)
    (hzTnadj : ∀ a ∈ T, ¬ G.Adj z a)
    {Q : List V} {u v : V} (hQ : IsAntipathFrom G Q u v) (hodd : Odd (pathLength Q))
    (huvadj : G.Adj u v) (hQT : ∀ w ∈ Q, w ∉ T)
    (hintT : ∀ w ∈ SPGT.interior Q, ∃ a ∈ T, G.Adj w a)
    (hintz : ∀ w ∈ SPGT.interior Q, G.Adj z w) :
    (∃ a ∈ T, G.Adj u a) ∨ (∃ a ∈ T, G.Adj v a) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hu, hv⟩ := hcon
  have hQp : IsPathFrom Gᶜ Q u v := hQ
  obtain ⟨humem, hvmem⟩ := PathBasics.isPathFrom_ends_mem hQp
  have huC : VertexComplete Gᶜ u T :=
    vertexComplete_compl_iff.mpr fun a ha => ⟨fun h => hQT u humem (h ▸ ha), hu a ha⟩
  have hvC : VertexComplete Gᶜ v T :=
    vertexComplete_compl_iff.mpr fun a ha => ⟨fun h => hQT v hvmem (h ▸ ha), hv a ha⟩
  have hzC : VertexComplete Gᶜ z T :=
    vertexComplete_compl_iff.mpr fun a ha => ⟨fun h => hzT (h ▸ ha), hzTnadj a ha⟩
  obtain ⟨w, hwint, hzw⟩ :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_2 Gᶜ (HoleBasics.berge_compl.mpr hBerge)
      T (anticonnected_compl hTcon) Q u v hQp hQT hodd huC hvC
      (noedge hQ huvadj hintT) z hzC
  rw [SimpleGraph.compl_adj] at hzw
  exact hzw.2 (hintz w hwint)

/-- **13.6 applied in `Ḡ`.**  An odd antipath whose ends have no neighbours in the
connected set `T` while all its internal vertices do has length exactly `3`, and its two
internal vertices are joined by an **odd path of `G`** with interior in `T` — that is
13.6's second alternative read in `Ḡ`, and it is the *"and there is an odd path `P` between
`q, x_i` with interior in `A_{t−3} ∪ V(R \ q)`"* of printed p. 127. -/
theorem antipath_middle_of_odd {G : SimpleGraph V} (hF5 : InF5 G)
    {T : Set V} (hTcon : ConnectedSet G T)
    {Q : List V} {u v : V} (hQ : IsAntipathFrom G Q u v) (hodd : Odd (pathLength Q))
    (huvadj : G.Adj u v) (hQT : ∀ w ∈ Q, w ∉ T)
    (huT : ∀ a ∈ T, ¬ G.Adj u a) (hvT : ∀ a ∈ T, ¬ G.Adj v a)
    (hintT : ∀ w ∈ SPGT.interior Q, ∃ a ∈ T, G.Adj w a) :
    pathLength Q = 3 ∧ ∃ c d : V, SPGT.interior Q = [c, d] ∧
      ∃ P : List V, IsPathFrom G P c d ∧ Odd (pathLength P) ∧
        ∀ y ∈ SPGT.interior P, y ∈ T := by
  have hQp : IsPathFrom Gᶜ Q u v := hQ
  obtain ⟨humem, hvmem⟩ := PathBasics.isPathFrom_ends_mem hQp
  have huC : VertexComplete Gᶜ u T :=
    vertexComplete_compl_iff.mpr fun a ha => ⟨fun h => hQT u humem (h ▸ ha), huT a ha⟩
  have hvC : VertexComplete Gᶜ v T :=
    vertexComplete_compl_iff.mpr fun a ha => ⟨fun h => hQT v hvmem (h ▸ ha), hvT a ha⟩
  have hXP : T ⊆ {w : V | w ∈ Q}ᶜ := fun a ha hmem => hQT a hmem ha
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 Gᶜ
      (ClassLemmas.inF5_compl.mpr hF5) Q u v hQp hodd T hXP
      (anticonnected_compl hTcon) huC hvC with h1 | h2
  · exact absurd h1 (noedge hQ huvadj hintT)
  · obtain ⟨hlen, c, d, hcd, P, hP, hPodd, hPint⟩ := h2
    exact ⟨hlen, c, d, hcd, P, PathBasics.isAntipathFrom_compl.mp hP, hPodd, hPint⟩

/-- The length-only form. -/
theorem antipath_length_three_of_odd {G : SimpleGraph V} (hF5 : InF5 G)
    {T : Set V} (hTcon : ConnectedSet G T)
    {Q : List V} {u v : V} (hQ : IsAntipathFrom G Q u v) (hodd : Odd (pathLength Q))
    (huvadj : G.Adj u v) (hQT : ∀ w ∈ Q, w ∉ T)
    (huT : ∀ a ∈ T, ¬ G.Adj u a) (hvT : ∀ a ∈ T, ¬ G.Adj v a)
    (hintT : ∀ w ∈ SPGT.interior Q, ∃ a ∈ T, G.Adj w a) :
    pathLength Q = 3 :=
  (antipath_middle_of_odd hF5 hTcon hQ hodd huvadj hQT huT hvT hintT).1

/-- **The `Y`-square truncation** (printed pp. 126, 127): *"But then `x₀,…,x_{t−1}` is a
`Y ∪ {x_t}`-square of height `t − 1`."* -/
theorem ysquare_truncate_union {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} {Y : Set V} (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hadj : G.Adj (x (t - 1)) (x (t - 2)))
    (hno : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a)
    (hq : ∃ a ∈ wheelSystemA G z A₀ x (t - 2), G.Adj a (x (t - 1)) ∧
      ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj a b) :
    IsYSquare G z A₀ x (t - 1) (Y ∪ {x t}) := by
  have hnonadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hA⟩ := hd
  obtain ⟨-, hinj, hout, -, -, -, -⟩ := id hws
  have h1 : t - 1 - 1 = t - 2 := by omega
  have h2 : t - 1 - 2 = t - 3 := by omega
  refine ⟨YDiamondTruncation.wheelSystem_truncate hws (by omega) (by omega), ?_, ?_,
    ⟨?_, ?_⟩, ?_, ?_, by omega, ?_, ?_, ?_⟩
  · exact hYne.mono Set.subset_union_left
  · exact YDiamondTruncation.anticonnected_union_singleton hYanti (hxY t le_rfl) hnVC
  · rintro (hz | hz)
    · exact hzY hz
    · rw [Set.mem_singleton_iff] at hz
      exact (hout t le_rfl).2 hz.symm
  · rintro i hi (hy | hy)
    · exact hxY i (by omega) hy
    · rw [Set.mem_singleton_iff] at hy
      have := hinj i (by omega) t le_rfl hy
      omega
  · intro i hi y hy
    rcases hy with hy | hy
    · exact hVC i (by omega) y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hXc (x i) (WheelSystemBasics.mem_wheelSystemX.2 ⟨i, by omega, rfl⟩)).symm
  · intro hcon
    exact hnonadj (hcon (x t) (Or.inr rfl)).symm
  · rw [h1]; exact hadj
  · rw [h2]; exact hno
  · rw [h1, h2]; exact hq

end Workspace.ProofLemmas.Thm203AntipathTools
