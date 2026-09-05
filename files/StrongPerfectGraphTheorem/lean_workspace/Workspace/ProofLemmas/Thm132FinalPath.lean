import Workspace.ProofLemmas.Thm132Claim5
import Workspace.ProofLemmas.Thm132Claim5Long
import Workspace.ProofLemmas.PathGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # The final odd path supplied by Roussel--Rubio in 13.2. -/

namespace Workspace.ProofLemmas.Thm132FinalPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm132Setup
open Workspace.ProofLemmas.Thm132Claim5Long

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem adj_of_not_compl_adj {G : SimpleGraph V} {u v : V}
    (hne : u ≠ v) (h : ¬ Gᶜ.Adj u v) : G.Adj u v := by
  by_contra hn
  exact h (by rw [SimpleGraph.compl_adj]; exact ⟨hne, hn⟩)

/-- The four-vertex antipath in the short Roussel--Rubio alternative can be
read in the complementary order as a path through the two old interior
vertices. -/
private theorem path_of_short_antipath
    {G : SimpleGraph V} {q : List V} {c e r w : V}
    (hq : IsAntipathFrom G q c e) (hqodd : Odd (pathLength q))
    (hqinner : ∀ z ∈ interior q, z = r ∨ z = w)
    (hce : G.Adj c e) (hrw : ¬ G.Adj r w) :
    ∃ P : List V, IsPathFrom G P r w ∧ Odd (pathLength P) ∧
      ∀ z, z ∈ interior P ↔ z ∈ [c, e] := by
  classical
  have hqne : c ≠ e := hce.ne
  have hqnotone : pathLength q ≠ 1 := by
    intro hone
    have hc := PathBasics.isPathFrom_ends_adj_of_length_one hq hone
    rw [SimpleGraph.compl_adj] at hc
    exact hc.2 hce
  have hqlt : q.length < 5 := by
    by_contra hn
    have h5 : 5 ≤ q.length := by omega
    have hm1 : q[1] ∈ interior q :=
      PathBasics.getElem_mem_interior hq.1 (by omega) (by omega) (by omega)
    have hm2 : q[2] ∈ interior q :=
      PathBasics.getElem_mem_interior hq.1 (by omega) (by omega) (by omega)
    have hm3 : q[3] ∈ interior q :=
      PathBasics.getElem_mem_interior hq.1 (by omega) (by omega) (by omega)
    rcases hqinner q[1] hm1 with h1 | h1 <;>
      rcases hqinner q[2] hm2 with h2 | h2 <;>
      rcases hqinner q[3] hm3 with h3 | h3
    all_goals
      first
      | exact (PathBasics.path_ne_of_ne_index hq.1 (by omega) (by omega) (by omega))
          (h1.trans h2.symm)
      | exact (PathBasics.path_ne_of_ne_index hq.1 (by omega) (by omega) (by omega))
          (h1.trans h3.symm)
      | exact (PathBasics.path_ne_of_ne_index hq.1 (by omega) (by omega) (by omega))
          (h2.trans h3.symm)
  have hqlen : q.length = 4 := by
    obtain ⟨k, hk⟩ := hqodd
    rw [PathBasics.pathLength_eq] at hk
    have hpos := PathBasics.path_length_pos hq.1
    rw [PathBasics.pathLength_eq] at hqnotone
    omega
  obtain ⟨q₀, q₁, q₂, q₃, rfl⟩ := Workspace.ProofLemmas.PathGlue.length_eq_four hqlen
  have hq₀ : q₀ = c := by simpa using hq.2.1
  have hq₃ : q₃ = e := by simpa using hq.2.2
  subst q₀
  subst q₃
  have h1 : q₁ = r ∨ q₁ = w := by
    apply hqinner q₁
    simp [SPGT.interior]
  have h2 : q₂ = r ∨ q₂ = w := by
    apply hqinner q₂
    simp [SPGT.interior]
  have h12 : q₁ ≠ q₂ := by
    exact PathBasics.path_ne_of_ne_index hq.1 (i := 1) (j := 2)
      (by norm_num) (by norm_num) (by omega)
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact absurd rfl h12
  · -- the antipath is `c-r-w-e`; use the complementary order `r-e-c-w`
    have hre : G.Adj q₁ e := adj_of_not_compl_adj
      (PathBasics.path_ne_of_ne_index hq.1 (i := 1) (j := 3)
        (by norm_num) (by norm_num) (by omega))
      (by intro h; rcases (PathBasics.path_adj_iff hq.1 (i := 1) (j := 3)
          (by norm_num) (by norm_num)).mp h
          with h | h <;> omega)
    have hcw : G.Adj c q₂ := adj_of_not_compl_adj
      (PathBasics.path_ne_of_ne_index hq.1 (i := 0) (j := 2)
        (by norm_num) (by norm_num) (by omega))
      (by intro h; rcases (PathBasics.path_adj_iff hq.1 (i := 0) (j := 2)
          (by norm_num) (by norm_num)).mp h
          with h | h <;> omega)
    have hrc : ¬ G.Adj q₁ c := by
      have hc := (PathBasics.path_adj_iff hq.1 (i := 1) (j := 0)
        (by norm_num) (by norm_num)).mpr (Or.inr (by omega))
      rw [SimpleGraph.compl_adj] at hc
      intro h
      exact hc.2 (by simpa using h)
    have hew : ¬ G.Adj e q₂ := by
      have hc := (PathBasics.path_adj_iff hq.1 (i := 2) (j := 3)
        (by norm_num) (by norm_num)).mpr (Or.inl (by omega))
      rw [SimpleGraph.compl_adj] at hc
      exact fun h => hc.2 h.symm
    have hnd : ([q₁, e, c, q₂] : List V).Nodup := by
      have hndq := hq.1.2.1
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
        List.not_mem_nil, not_false_eq_true, and_true] at hndq ⊢
      aesop
    refine ⟨[q₁, e, c, q₂], ⟨?_, by simp, by simp⟩,
      ⟨1, by norm_num [pathLength]⟩, ?_⟩
    · exact Workspace.ProofLemmas.PathGlue.isPathList_four hnd hre hce.symm hcw
        hrc hrw hew
    · intro z
      simp [SPGT.interior, or_comm]
  · -- the antipath is `c-w-r-e`; use the complementary order `r-c-e-w`
    have hrc : G.Adj q₂ c := adj_of_not_compl_adj
      (PathBasics.path_ne_of_ne_index hq.1 (i := 2) (j := 0)
        (by norm_num) (by norm_num) (by omega))
      (by intro h; rcases (PathBasics.path_adj_iff hq.1 (i := 2) (j := 0)
          (by norm_num) (by norm_num)).mp h
          with h | h <;> omega)
    have hew : G.Adj e q₁ := adj_of_not_compl_adj
      (PathBasics.path_ne_of_ne_index hq.1 (i := 3) (j := 1)
        (by norm_num) (by norm_num) (by omega))
      (by intro h; rcases (PathBasics.path_adj_iff hq.1 (i := 3) (j := 1)
          (by norm_num) (by norm_num)).mp h
          with h | h <;> omega)
    have hre : ¬ G.Adj q₂ e := by
      have hc := (PathBasics.path_adj_iff hq.1 (i := 2) (j := 3)
        (by norm_num) (by norm_num)).mpr (Or.inl (by omega))
      rw [SimpleGraph.compl_adj] at hc
      intro h
      exact hc.2 (by simpa using h)
    have hcw : ¬ G.Adj c q₁ := by
      have hc := (PathBasics.path_adj_iff hq.1 (i := 0) (j := 1)
        (by norm_num) (by norm_num)).mpr (Or.inl (by omega))
      rw [SimpleGraph.compl_adj] at hc
      exact hc.2
    have hnd : ([q₂, c, e, q₁] : List V).Nodup := by
      have hndq := hq.1.2.1
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
        List.not_mem_nil, not_false_eq_true, and_true] at hndq ⊢
      aesop
    refine ⟨[q₂, c, e, q₁], ⟨?_, by simp, by simp⟩,
      ⟨1, by norm_num [pathLength]⟩, ?_⟩
    · exact Workspace.ProofLemmas.PathGlue.isPathList_four hnd hrc hce hew
        hre hrw hcw
    · intro z
      simp [SPGT.interior]
  · exact absurd rfl h12

/-- After Claim (5), 2.1 gives an odd path between the two trajectory
vertices, with precisely the interior of the distinguished banister inside. -/
theorem exists_final_odd_path
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V} {i : ℕ}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hbW : VertexComplete G b₀ {z : V | z ∈ d.w})
    (hra : G.Adj a₀ d.r)
    (hlast : IsRightStar G A C B d.last)
    (hwone : d.w.length = 1) :
    ∃ P : List V, IsPathFrom G P d.r d.last ∧ Odd (pathLength P) ∧
      ∀ z, z ∈ interior P ↔ z ∈ interior R₀ := by
  classical
  have hban₀ : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have hrb₀ : G.Adj d.r b₀ :=
    PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
  have hrout : d.r ∉ staircaseVertices A C B R₀ :=
    Workspace.ProofLemmas.Thm132Claim2.leftStar_adj_rightEnd_outside
      hK.1.1 d.optimal.1.2.2.1 hra.ne' hrb₀
  have hwne : d.w ≠ [] := by rw [List.ne_nil_iff_length_pos, hwone]; omega
  have hlastMem : d.last ∈ d.w := by
    have hc' : d.w.getLast? = some d.last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using d.trajectory_antipath.2.2
    exact PathBasics.getLast_mem hc'
  have hrw : ¬ G.Adj d.r d.last := by
    have hc := PathBasics.isPathFrom_ends_adj_of_length_one d.trajectory_antipath (by
      rw [PathBasics.pathLength_eq]
      simp [hwone])
    rw [SimpleGraph.compl_adj] at hc
    exact hc.2
  have hwshape : d.w = [d.last] := by
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hwone
    have hc := d.trajectory_antipath.2.2
    rw [hz] at hc
    simp only [List.getLast?_cons_of_ne_nil (by simp : [z] ≠ []), List.getLast?_singleton,
      Option.some.injEq] at hc
    simpa [hz, hc]
  let T : Set V := {z : V | z ∈ d.r :: d.w}
  have hTanti : AnticonnectedSet G T :=
    Workspace.ProofLemmas.InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      d.trajectory_antipath.1
  have hTout : ∀ z ∈ T, z ∉ staircaseVertices A C B R₀ := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    simp [hwshape] at hz
    rcases hz with rfl | rfl
    · exact hrout
    · exact Workspace.ProofLemmas.Thm132Infrastructure.bComplete_adj_left_not_mem_staircase
        hK.1.1 (d.w_B_complete d.last hlastMem)
          (d.a₀_complete_w d.last hlastMem).symm
  have hR₀T : ∀ z ∈ R₀, z ∉ T := by
    intro z hzR hzT
    exact hTout z hzT (Or.inl hzR)
  have ha₀T : VertexComplete G a₀ T := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    simp [hwshape] at hz
    rcases hz with rfl | rfl
    · exact hra
    · exact d.a₀_complete_w d.last hlastMem
  have hb₀T : VertexComplete G b₀ T := by
    intro z hz
    change z ∈ d.r :: d.w at hz
    simp [hwshape] at hz
    rcases hz with rfl | rfl
    · exact hrb₀.symm
    · exact hbW d.last hlastMem
  have hRodd : Odd (pathLength R₀) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
      a₀ b₀ R₀ hban₀).2
  have ha₀b₀ : ¬ G.Adj a₀ b₀ := by
    have hlen : 3 ≤ R₀.length := by
      have hlong := hK.1.1.2.2
      rw [PathBasics.pathLength_eq] at hlong
      omega
    have hn := PathBasics.path_ends_not_adj hban₀.1.1 hlen
    have h0 : R₀[0]'(by omega) = a₀ :=
      PathBasics.getElem_zero_of_head? hban₀.1.2.1 (by omega)
    have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
      PathBasics.getElem_last_of_getLast? hban₀.1.2.2 (by omega)
    simpa [h0, hl] using hn
  have hcompleteEnds : ∀ z ∈ R₀, VertexComplete G z T → z = a₀ ∨ z = b₀ := by
    intro z hz hzT
    by_cases hza : z = a₀
    · exact Or.inl hza
    by_cases hzb : z = b₀
    · exact Or.inr hzb
    have hzint : z ∈ interior R₀ :=
      (PathBasics.mem_interior_iff_of_pathFrom hban₀.1).mpr ⟨hz, hza, hzb⟩
    exact absurd ⟨z, hzint, hzT⟩
      (Workspace.ProofLemmas.Thm132Claim4.no_trajectory_complete_interior
        hG heven hK d hbW hra hlast)
  have hnoedge : ¬ ∃ u ∈ R₀, ∃ v ∈ R₀, EdgeComplete G T u v := by
    rintro ⟨u, hu, v, hv, huv, huT, hvT⟩
    rcases hcompleteEnds u hu huT with rfl | rfl <;>
      rcases hcompleteEnds v hv hvT with rfl | rfl
    · exact G.irrefl huv
    · exact ha₀b₀ huv
    · exact ha₀b₀ huv.symm
    · exact G.irrefl huv
  rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG T hTanti R₀ a₀ b₀
      hban₀.1 hR₀T hRodd ha₀T hb₀T with hedge | hleap | hshort
  · exact absurd hedge hnoedge
  · obtain ⟨hR5, u, huT, v, hvT, huv⟩ := hleap
    obtain ⟨hP, hlen⟩ := leap_path hban₀.1 hR5 hR₀T huT hvT huv
    have hu : u = d.r ∨ u = d.last := by
      change u ∈ d.r :: d.w at huT
      simpa [hwshape] using huT
    have hv : v = d.r ∨ v = d.last := by
      change v ∈ d.r :: d.w at hvT
      simpa [hwshape] using hvT
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv.2.2.1
    · refine ⟨_, hP, ?_, ?_⟩
      · simpa [hlen] using hRodd
      · intro z
        simp [SPGT.interior]
    · refine ⟨_, PathBasics.isPathFrom_reverse hP, ?_, ?_⟩
      · rw [PathBasics.pathLength_reverse, hlen]
        exact hRodd
      · intro z
        rw [PathBasics.interior_reverse, List.mem_reverse]
        simp [SPGT.interior]
    · exact absurd rfl huv.2.2.1
  · obtain ⟨hR3, c, e, hinterior, q, hq, hqodd, hqinner⟩ := hshort
    have hce : G.Adj c e := by
      have hlen : 3 ≤ R₀.length := by rw [PathBasics.pathLength_eq] at hR3; omega
      have hi := Workspace.ProofLemmas.PathGlue.isPathFrom_interior hban₀.1.1 hlen
      rw [hinterior] at hi
      have hc : c = R₀[1]'(by omega) := by simpa using hi.2.1
      have he : e = R₀[R₀.length - 2]'(by omega) := by simpa using hi.2.2
      have hadj := PathBasics.isPathFrom_ends_adj_of_length_one hi (by norm_num [pathLength])
      simpa [hc, he] using hadj
    obtain ⟨P, hP, hPodd, hPint⟩ := path_of_short_antipath hq hqodd
      (by
        intro z hz
        have hm := hqinner z hz
        change z ∈ d.r :: d.w at hm
        simpa [hwshape] using hm) hce hrw
    exact ⟨P, hP, hPodd, fun z => by simpa [hinterior] using hPint z⟩

end Workspace.ProofLemmas.Thm132FinalPath
