import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.YEdgeFourConfig

/-!
# 23.2 — the layout of the four `Y`-complete rim edges

PAPER (23.2, printed p. 139), the sentence immediately after step (1):

> *"Since `(C,Y)` is not an odd wheel, there are vertices `x₀, z, x₁, c₁, c₂, c₃` of `C`, in
> order, and all distinct except possibly `x₁ = c₁` or `c₃ = x₀`, such that the `Y`-complete
> edges in `C` are `x₀z, zx₁, c₁c₂, c₂c₃`."*

`exists_yEdge_layout` is that sentence, phrased on cyclic **positions** of the rim: there is a
base position `k` and an offset `d` with `2 ≤ d` and `d + 2 ≤ |C|` such that the `Y`-complete
cyclic edges of `C` are exactly those at the positions `k, k+1, k+d, k+d+1`.  Reading the six
vertices off, `x₀, z, x₁` sit at positions `k, k+1, k+2` and `c₁, c₂, c₃` at `k+d, k+d+1,
k+d+2`; the two degenerate coincidences the paper allows are precisely `d = 2` (then
`x₁ = c₁`) and `d + 2 = |C|` (then `c₃ = x₀`), and they cannot both occur because `|C| ≥ 6`.

## How the printed sentence is proved

Every maximal run of `Y`-complete rim positions has **odd** length — that is
`YEdgeConfiguration.run_odd_of_not_isOddWheel`, the working form of *"`(C,Y)` is not an odd
wheel"* — and a run of `L` positions carries exactly `L − 1` `Y`-complete edges.  So the
`Y`-complete edges of the rim break into maximal blocks of **even** size, and step (1) says
the blocks have four elements in total.  Hence either one block of four (one run of five
vertices: the degenerate case `x₁ = c₁`) or two blocks of two (two runs of three).  The proof
below chooses the run through some `Y`-complete edge, splits on `L = 3` or `L = 5`
(`YEdgeFourConfig.run_length_eq_three_or_five`), and in the `L = 3` case locates the *next*
`Y`-complete edge position `d` and shows the edge at `d + 1` is `Y`-complete too — otherwise
the run through `d` would have the even length `2`.

The running count is handled by the partial sums `g j = #{t < j | e_{k+t} is Y-complete}`,
for which `WheelParity.cycCount_add` and `WheelParity.cycCount_add_length` give `g |C| = 4`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232YEdgeLayout

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.WheelParity
open Workspace.ProofLemmas.SegmentBasics
open Workspace.ProofLemmas.YEdgeConfiguration
open Workspace.ProofLemmas.OptimalWheelChoice

attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-- **PAPER (23.2, printed p. 139):** *"Since `(C,Y)` is not an odd wheel, there are vertices
`x₀, z, x₁, c₁, c₂, c₃` of `C`, in order, and all distinct except possibly `x₁ = c₁` or
`c₃ = x₀`, such that the `Y`-complete edges in `C` are `x₀z, zx₁, c₁c₂, c₂c₃`."*

On cyclic positions: the `Y`-complete edges of the rim are exactly the ones at positions
`k, k+1, k+d, k+d+1`, with `2 ≤ d` and `d + 2 ≤ |C|`. -/
theorem exists_yEdge_layout (hC : IsHoleList G C) (hn6 : 6 ≤ C.length)
    (hw : IsWheel G C Y) (hno : ¬ IsOddWheel G C Y)
    (h4 : yEdgeCount G Y C = 4) :
    ∃ k d : ℕ, 2 ≤ d ∧ d + 2 ≤ C.length ∧
      ∀ i : ℕ, i < C.length →
        (CycEdge G Y C (k + i) ↔ (i = 0 ∨ i = 1 ∨ i = d ∨ i = d + 1)) := by
  classical
  have hn : 0 < C.length := by omega
  -- a rim position that is not `Y`-complete, and a `Y`-complete rim edge
  obtain ⟨j, hj⟩ := YEdgeFourConfig.exists_not_cycVert hC hn6 h4
  obtain ⟨m, hmlt, hme⟩ :=
    YEdgeFourConfig.exists_cycEdge (Y := Y) hC (by rw [h4]; norm_num)
  have hmv : CycVert G Y C m := cycVert_of_cycEdge hC hme
  obtain ⟨k, L, hL1, hL2, hLodd, hall, hnext, hprev, t, htL, hteq⟩ :=
    exists_odd_run hC hw hno hmv hj
  have hedge : CycEdge G Y C (k + t) := (YEdgeFourConfig.cycEdge_congr hn hteq).mpr hme
  have hL35 : L = 3 ∨ L = 5 :=
    YEdgeFourConfig.run_length_eq_three_or_five hC h4 hL2 hLodd hall hnext htL hedge
  ------------------------------------------------------------------
  -- the running count of `Y`-complete edges from position `k`
  ------------------------------------------------------------------
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℕ, g = fun j =>
      ∑ x ∈ Finset.range j, (if CycEdge G Y C (k + x) then 1 else 0) := ⟨_, rfl⟩
  have hg0 : g 0 = 0 := by simp only [hgdef]; simp
  have hgsucc : ∀ j : ℕ, g (j + 1) = g j + (if CycEdge G Y C (k + j) then 1 else 0) := by
    intro j; simp only [hgdef]; exact Finset.sum_range_succ _ _
  have hgmono : ∀ a b : ℕ, a ≤ b → g a ≤ g b := by
    intro a b hab
    simp only [hgdef]
    refine Finset.sum_le_sum_of_subset ?_
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hab)
  have hgn : g C.length = 4 := by
    have h1 := cycCount_add (G := G) (Y := Y) (C := C) k C.length
    have h2 := cycCount_add_length (G := G) (Y := Y) (C := C) k
    have h3 : cycCount G Y C C.length = 4 := by
      rw [← YEdgeFourConfig.yEdgeCount_eq_card hC]; exact h4
    simp only [hgdef]
    omega
  rcases hL35 with rfl | rfl
  ------------------------------------------------------------------
  -- generic case: two runs of three, i.e. two blocks of two edges
  ------------------------------------------------------------------
  · have he0 : CycEdge G Y C (k + 0) := cycEdge_of_run hC hall (t := 0) (by omega)
    have he1 : CycEdge G Y C (k + 1) := cycEdge_of_run hC hall (t := 1) (by omega)
    have hne2 : ¬ CycEdge G Y C (k + 2) := by
      intro h
      have hv := cycVert_succ_of_cycEdge hC h
      rw [show k + 2 + 1 = k + 3 from by omega] at hv
      exact hnext hv
    have hnelast : ¬ CycEdge G Y C (k + (C.length - 1)) :=
      fun h => hprev (cycVert_of_cycEdge hC h)
    have hg3 : g 3 = 2 := by
      have e0 : g 1 = g 0 + 1 := by
        have h := hgsucc 0; rw [if_pos he0] at h; simpa using h
      have e1 : g 2 = g 1 + 1 := by
        have h := hgsucc 1; rw [if_pos he1] at h; simpa using h
      have e2 : g 3 = g 2 := by
        have h := hgsucc 2; rw [if_neg hne2] at h; simpa using h
      omega
    have hgn1 : g (C.length - 1) = 4 := by
      have e := hgsucc (C.length - 1)
      rw [if_neg hnelast, show C.length - 1 + 1 = C.length from by omega] at e
      omega
    -- the next `Y`-complete edge position after `k + 1`
    have hex : ∃ i : ℕ, 3 ≤ i ∧ i < C.length - 1 ∧ CycEdge G Y C (k + i) := by
      by_contra hcon
      push_neg at hcon
      have hconst : ∀ p : ℕ, 3 + p ≤ C.length - 1 → g (3 + p) = 2 := by
        intro p
        induction p with
        | zero => intro _; simpa using hg3
        | succ q ih =>
            intro hle
            have hqe : ¬ CycEdge G Y C (k + (3 + q)) := hcon (3 + q) (by omega) (by omega)
            rw [show 3 + (q + 1) = (3 + q) + 1 from by omega, hgsucc, if_neg hqe,
              ih (by omega)]
      have hcc := hconst (C.length - 1 - 3) (by omega)
      rw [show 3 + (C.length - 1 - 3) = C.length - 1 from by omega] at hcc
      omega
    obtain ⟨d, ⟨hd3, hdn, hde⟩, hdmin⟩ :
        ∃ d : ℕ, (3 ≤ d ∧ d < C.length - 1 ∧ CycEdge G Y C (k + d)) ∧
          ∀ i, i < d → ¬ (3 ≤ i ∧ i < C.length - 1 ∧ CycEdge G Y C (k + i)) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
    have hlow : ∀ i : ℕ, 2 ≤ i → i < d → ¬ CycEdge G Y C (k + i) := by
      intro i h2 hid
      rcases Nat.eq_or_lt_of_le h2 with h | h
      · rw [← h]; exact hne2
      · exact fun hce => hdmin i hid ⟨by omega, by omega, hce⟩
    have hgconst : ∀ p : ℕ, 3 + p ≤ d → g (3 + p) = 2 := by
      intro p
      induction p with
      | zero => intro _; simpa using hg3
      | succ q ih =>
          intro hle
          have hqe : ¬ CycEdge G Y C (k + (3 + q)) := hlow (3 + q) (by omega) (by omega)
          rw [show 3 + (q + 1) = (3 + q) + 1 from by omega, hgsucc, if_neg hqe, ih (by omega)]
    have hgd : g d = 2 := by
      have h := hgconst (d - 3) (by omega)
      rwa [show 3 + (d - 3) = d from by omega] at h
    have hvd : CycVert G Y C (k + d) := cycVert_of_cycEdge hC hde
    have hvd1 : CycVert G Y C (k + d + 1) := cycVert_succ_of_cycEdge hC hde
    -- the second block has size two: otherwise the run through `k + d` would have length `2`
    have hed1 : CycEdge G Y C (k + (d + 1)) := by
      by_contra hcon
      have hnv2 : ¬ CycVert G Y C (k + d + 2) := by
        intro h
        refine hcon ((cycEdge_iff hC).mpr ⟨?_, ?_⟩)
        · rw [show k + (d + 1) = k + d + 1 from by omega]; exact hvd1
        · rw [show k + (d + 1) + 1 = k + d + 2 from by omega]; exact h
      have hnvprev : ¬ CycVert G Y C (k + d + (C.length - 1)) := by
        intro h
        have h' : CycVert G Y C (k + (d - 1)) := by
          refine (cycVert_congr ?_).mp h
          rw [show k + d + (C.length - 1) = (k + (d - 1)) + C.length from by omega,
            Nat.add_mod_right]
        refine hlow (d - 1) (by omega) (by omega) ((cycEdge_iff hC).mpr ⟨h', ?_⟩)
        rw [show k + (d - 1) + 1 = k + d from by omega]; exact hvd
      have hallD : ∀ s : ℕ, s < 2 → CycVert G Y C (k + d + s) := by
        intro s hs
        interval_cases s
        · simpa using hvd
        · exact hvd1
      have hodd2 := run_odd' hC hw hno (k := k + d) (L := 2) (by omega) (by omega) hallD
        hnv2 hnvprev
      omega
    have hgd2 : g (d + 2) = 4 := by
      have e0 : g (d + 1) = g d + 1 := by
        have h := hgsucc d; rwa [if_pos hde] at h
      have e1 : g (d + 2) = g (d + 1) + 1 := by
        have h := hgsucc (d + 1); rw [if_pos hed1] at h
        rwa [show d + 1 + 1 = d + 2 from by omega] at h
      omega
    refine ⟨k, d, by omega, by omega, ?_⟩
    intro i hi
    constructor
    · intro hce
      by_contra hcon
      push_neg at hcon
      obtain ⟨c0, c1, c2, c3⟩ := hcon
      rcases Nat.lt_or_ge i d with hid | hid
      · exact hlow i (by omega) hid hce
      · have hi2 : d + 2 ≤ i := by omega
        have h1 : g (i + 1) = g i + 1 := by rw [hgsucc i, if_pos hce]
        have h2 : g (d + 2) ≤ g i := hgmono (d + 2) i hi2
        have h3 : g (i + 1) ≤ g C.length := hgmono (i + 1) C.length (by omega)
        omega
    · rintro (rfl | rfl | rfl | rfl)
      · exact he0
      · exact he1
      · exact hde
      · exact hed1
  ------------------------------------------------------------------
  -- degenerate case: one run of five, i.e. one block of four edges
  ------------------------------------------------------------------
  · have he0 : CycEdge G Y C (k + 0) := cycEdge_of_run hC hall (t := 0) (by omega)
    have he1 : CycEdge G Y C (k + 1) := cycEdge_of_run hC hall (t := 1) (by omega)
    have he2 : CycEdge G Y C (k + 2) := cycEdge_of_run hC hall (t := 2) (by omega)
    have he3 : CycEdge G Y C (k + 3) := cycEdge_of_run hC hall (t := 3) (by omega)
    have hg4 : g 4 = 4 := by
      have e0 : g 1 = g 0 + 1 := by
        have h := hgsucc 0; rw [if_pos he0] at h; simpa using h
      have e1 : g 2 = g 1 + 1 := by
        have h := hgsucc 1; rw [if_pos he1] at h; simpa using h
      have e2 : g 3 = g 2 + 1 := by
        have h := hgsucc 2; rw [if_pos he2] at h; simpa using h
      have e3 : g 4 = g 3 + 1 := by
        have h := hgsucc 3; rw [if_pos he3] at h; simpa using h
      omega
    refine ⟨k, 2, le_rfl, by omega, ?_⟩
    intro i hi
    constructor
    · intro hce
      by_contra hcon
      push_neg at hcon
      obtain ⟨c0, c1, c2, c3⟩ := hcon
      have hi4 : 4 ≤ i := by omega
      have h1 : g (i + 1) = g i + 1 := by rw [hgsucc i, if_pos hce]
      have h2 : g 4 ≤ g i := hgmono 4 i hi4
      have h3 : g (i + 1) ≤ g C.length := hgmono (i + 1) C.length (by omega)
      omega
    · rintro (rfl | rfl | rfl | rfl)
      · exact he0
      · exact he1
      · exact he2
      · exact he3

end Workspace.ProofLemmas.Thm232YEdgeLayout
