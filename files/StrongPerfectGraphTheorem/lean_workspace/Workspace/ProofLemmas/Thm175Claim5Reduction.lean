import Workspace.ProofLemmas.Thm175Claim4Miss
import Workspace.ProofLemmas.Thm175Claim5Antipath
import Workspace.Statements.S15.Thm_15_7

/-! The last complete vertex and the four-vertex antihole in 17.5 (5). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim5Reduction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

theorem path_length_four (c : Counterexample G z) : 4 ≤ c.core.p.length := by
  have ho := c.core.hodd
  have hl := c.core.hlong
  rw [Nat.odd_iff, pathLength] at ho
  rw [pathLength] at hl
  omega

/-- The conclusion `j=2` in the paper, including its maximality clause. -/
theorem last_complete_is_second (hG : InF7 G) (s : Setup c) (hopt : IsOptimal c)
    (hxonly : ∀ v ∈ c.core.p, G.Adj s.x₁ v → v = c.core.p₁) :
    ∃ h1 : 1 < c.core.p.length,
      VertexComplete G (c.core.p[1]'h1) (wSet s) ∧
      ∀ k (hk : k < c.core.p.length),
        VertexComplete G (c.core.p[k]'hk) (wSet s) → k ≤ 1 := by
  classical
  have hlen := path_length_four c
  have hp0 : c.core.p[0]'(by omega) = c.core.p₁ :=
    PathBasics.getElem_zero_of_head? c.core.hp.2.1 (by omega)
  obtain ⟨j, hj, hjC, hjmax⟩ := Thm182MaxIndex.exists_max_complete_index
    G (wSet s) c.core.p (by omega) (by rw [hp0]; exact p₁_complete_wSet s)
  have hjpos : 0 < j := by
    by_contra hn
    have hj0 : j = 0 := by omega
    have ho := odd_edges_wSet s hopt
    have hpos : 0 < (edges G (wSet s) c.core.p).ncard := by
      rw [Nat.odd_iff] at ho
      omega
    obtain ⟨e, u, hu, v, hv, he, hE⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hi0 : i = 0 := by have := hjmax i hi hE.2.1; omega
    have hk0 : k = 0 := by have := hjmax k hk hE.2.2; omega
    subst i
    subst k
    exact G.irrefl hE.1
  let S := antiPrefix s ++ [c.core.p₁]
  have hS := first_miss_antipath s
  have hSl : 4 ≤ S.length := by
    dsimp [S, antiPrefix]
    simp only [List.length_append, List.length_singleton, List.length_take]
    have := s.hXlong
    have := s.ht₀
    omega
  have hSP : ∀ v ∈ S, v ∈ c.core.p → v = c.core.p₁ := by
    intro v hv hvP
    rcases List.mem_append.mp hv with hv | hv
    · rcases prefix_subset s v hv with hx | hy
      · exact (c.core.houtX v hvP hx).elim
      · exact (c.core.houtY v hvP hy).elim
    · simpa using hv
  have hzS : z ∉ S := by
    intro hz
    rcases List.mem_append.mp hz with hz | hz
    · exact c.hz (prefix_subset s z hz)
    · apply c.core.hzP
      have he : z = c.core.p₁ := by simpa using hz
      exact (congrArg (fun v => v ∈ c.core.p) he).mpr
        (PathBasics.head_mem c.core.hp.2.1)
  have hzcomp : ∀ v ∈ S, v ≠ c.core.p₁ → G.Adj z v := by
    intro v hv hne
    rcases List.mem_append.mp hv with hv | hv
    · exact c.hzXY v (prefix_subset s v hv)
    · exact (hne (by simpa using hv)).elim
  have hint : ∀ v ∈ SPGT.interior S,
      G.Adj v (c.core.p[j]'hj) ∨ G.Adj v c.core.pₙ := by
    intro v hv
    have hparts := (PathBasics.mem_interior_iff_of_pathFrom hS).mp hv
    have hvR : v ∈ antiPrefix s := by
      rcases List.mem_append.mp hparts.1 with hv | hv
      · exact hv
      · exact (hparts.2.2 (by simpa using hv)).elim
    rcases prefix_subset s v hvR with hx | hy
    · exact Or.inl (hjC v (Or.inl ⟨hx, hparts.2.1⟩)).symm
    · exact Or.inr (((c.core.hYuniq c.core.pₙ
        (PathBasics.getLast_mem c.core.hp.2.2)).mpr rfl) v hy).symm
  have hj1 := Thm175Claim5Antipath.complete_index_eq_one G hG.1.1 c.core.p
    c.core.p₁ c.core.pₙ s.x₁ z c.core.hp hlen (x₁_notMem_p s) c.core.hzP
    hxonly c.core.hzanti S hS hSl hSP hzS hzcomp j hj hjpos hint
  subst j
  exact ⟨hj, hjC, hjmax⟩

/-- The interior of `x₁-⋯-x_s-y₁-⋯-y_{t₀}` is contained in `W`. -/
theorem prefix_interior_wSet (s : Setup c) :
    ∀ v ∈ SPGT.interior (antiPrefix s), v ∈ wSet s := by
  intro v hv
  have hparts := (PathBasics.mem_interior_iff_of_pathFrom (prefix_from s)).mp hv
  rcases List.mem_append.mp hparts.1 with hx | hy
  · exact Or.inl ⟨(s.hXverts v).mp hx, hparts.2.1⟩
  · right
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    have hit : i < s.t₀ + 1 := lt_of_lt_of_le hi (List.length_take_le _ _)
    have hine : i ≠ s.t₀ := by
      intro he
      apply hparts.2.2
      simp only [List.getElem_take]
      subst i
      rfl
    have hi' : i < (s.qY.take s.t₀).length := by
      simp only [List.length_take]
      have := s.ht₀
      omega
    simpa using (List.getElem_mem hi' : (s.qY.take s.t₀)[i]'hi' ∈ s.qY.take s.t₀)

/-- PAPER: "Therefore `p₂-x₁-⋯-x_s-y₁-⋯-y_{t₀}-p₂` is an antihole `D`." -/
theorem second_prefix_antihole (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (hxonly : ∀ v ∈ c.core.p, G.Adj s.x₁ v → v = c.core.p₁)
    (h1 : 1 < c.core.p.length)
    (hp₂W : VertexComplete G (c.core.p[1]'h1) (wSet s)) :
    IsAntiholeList G ((c.core.p[1]'h1) :: antiPrefix s) := by
  have hp₂mem : c.core.p[1]'h1 ∈ c.core.p := List.getElem_mem h1
  have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (show 0 < c.core.p.length by omega)
  have hx : ¬ G.Adj (c.core.p[1]'h1) s.x₁ := by
    intro ha
    have he := hxonly _ hp₂mem ha.symm
    have := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hp0.symm)
    omega
  have hout : c.core.p[1]'h1 ∉ antiPrefix s := by
    intro hm
    rcases prefix_subset s _ hm with hX | hY
    · exact c.core.houtX _ hp₂mem hX
    · exact c.core.houtY _ hp₂mem hY
  apply PrismBasics.isAntiholeList_of_antipath_add_vertex (prefix_from s)
  · simp only [pathLength, antiPrefix, List.length_append, List.length_take]
    have := s.hXlong
    have := s.ht₀
    omega
  · exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun he => c.core.houtX _ hp₂mem (he ▸ x₁_mem s), hx⟩
  · exact (SimpleGraph.compl_adj G _ _).mpr
      ⟨fun he => c.core.houtY _ hp₂mem (he ▸
        ((s.hYverts _).mp (List.getElem_mem s.ht₀))),
       Thm175Claim4Miss.second_misses hG s hfirst h1⟩
  · exact hout
  · intro v hv hanti
    exact ((SimpleGraph.compl_adj G _ _).mp hanti).2 (hp₂W v (prefix_interior_wSet s v hv))

end Workspace.ProofLemmas.Thm175Claim5Reduction
