import Workspace.ProofLemmas.Thm175Claim4Miss
import Workspace.Statements.S15.Thm_15_7

/-! The hole meeting the antihole in three vertices in the proof of 17.5 (5). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim5Hole

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

/-- The first neighbour of `y_{t₀}` on `P` is at or after `p₃`. -/
theorem exists_first_neighbor (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁)) :
    ∃ d, ∃ hd : d < c.core.p.length, 2 ≤ d ∧
      G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[d]'hd) ∧
      ∀ i (hi : i < c.core.p.length), i < d →
        ¬ G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[i]'hi) := by
  classical
  have hpₙY := (c.core.hYuniq c.core.pₙ (PathBasics.getLast_mem c.core.hp.2.2)).mpr rfl
  have hyY : s.qY[s.t₀]'s.ht₀ ∈ c.Y := (s.hYverts _).mp (List.getElem_mem s.ht₀)
  have hpos := PathBasics.path_length_pos c.core.hp.1
  have hlast := PathBasics.getElem_last_of_getLast? c.core.hp.2.2 hpos
  let Good : ℕ → Prop := fun i => ∃ hi : i < c.core.p.length,
    G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[i]'hi)
  have hex : ∃ i, Good i :=
    ⟨c.core.p.length - 1, by omega, by rw [hlast]; exact (hpₙY _ hyY).symm⟩
  obtain ⟨hd, hda⟩ := Nat.find_spec hex
  have hbefore : ∀ i (hi : i < c.core.p.length), i < Nat.find hex →
      ¬ G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[i]'hi) := by
    intro i hi him ha
    exact Nat.find_min hex him ⟨hi, ha⟩
  refine ⟨Nat.find hex, hd, ?_, hda, hbefore⟩
  have hne0 : Nat.find hex ≠ 0 := by
    intro he
    have h0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1 hpos
    have ha : G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[0]'hpos) := by simpa [he] using hda
    rw [h0] at ha
    exact s.hmiss ha.symm
  have hne1 : Nat.find hex ≠ 1 := by
    intro he
    have h1 : 1 < c.core.p.length := by omega
    have ha : G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[1]'h1) := by simpa [he] using hda
    exact Thm175Claim4Miss.second_misses hG s hfirst h1 ha.symm
  omega

theorem x₁_adj_missed_vertex (s : Setup c) : G.Adj s.x₁ (s.qY[s.t₀]'s.ht₀) := by
  have hlen : 3 ≤ (antiPrefix s).length := by
    simp only [antiPrefix, List.length_append, List.length_take]
    have := s.hXlong
    have := s.ht₀
    omega
  have hp := prefix_from s
  have hnon := PathBasics.path_ends_not_adj hp.1 hlen
  rw [PathBasics.getElem_zero_of_head? hp.2.1 (by omega),
    PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)] at hnon
  by_contra ha
  apply hnon
  exact (SimpleGraph.compl_adj G _ _).mpr
    ⟨fun he => Set.disjoint_left.mp (blocks_disjoint s) (x₁_mem s)
      (he ▸ (s.hYverts _).mp (List.getElem_mem s.ht₀)), ha⟩

/-- PAPER: "`x₁-p₁-⋯-p_d-y_{t₀}-x₁` is a hole of length at least 6." -/
theorem first_neighbor_hole (s : Setup c)
    (hxonly : ∀ v ∈ c.core.p, G.Adj s.x₁ v → v = c.core.p₁)
    (d : ℕ) (hd : d < c.core.p.length) (hd2 : 2 ≤ d)
    (hda : G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[d]'hd))
    (hbefore : ∀ i (hi : i < c.core.p.length), i < d →
      ¬ G.Adj (s.qY[s.t₀]'s.ht₀) (c.core.p[i]'hi)) :
    IsHoleList G (s.x₁ :: (c.core.p.take (d + 1) ++ [s.qY[s.t₀]'s.ht₀])) := by
  let y := s.qY[s.t₀]'s.ht₀
  have hyY : y ∈ c.Y := (s.hYverts _).mp (List.getElem_mem s.ht₀)
  have hyP : y ∉ c.core.p := fun hy => c.core.houtY y hy hyY
  have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (show 0 < c.core.p.length by omega)
  have hpre : IsPathFrom G (c.core.p.take (d + 1)) c.core.p₁ (c.core.p[d]'hd) := by
    simpa only [List.drop_zero, Nat.sub_zero, hp0] using
      PathBasics.isPathFrom_slice c.core.hp.1 (show 0 < d by omega) hd
  have hyonly : ∀ v ∈ c.core.p.take (d + 1), v ≠ c.core.p[d]'hd → ¬ G.Adj y v := by
    intro v hv hne ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
    have hid : i ≤ d := by have := List.length_take_le (d + 1) c.core.p; omega
    have hip : i < c.core.p.length := by omega
    have hine : i ≠ d := by intro he; apply hne; simp [he]
    exact hbefore i hip (by omega) (by simpa using ha)
  have hprey : IsPathFrom G (c.core.p.take (d + 1) ++ [y]) c.core.p₁ y :=
    PathAttach.isPathFrom_concat hpre hda
      (fun hy => hyP (List.take_subset _ _ hy)) hyonly
  have hxout : s.x₁ ∉ c.core.p.take (d + 1) ++ [y] := by
    intro hx
    rcases List.mem_append.mp hx with hx | hx
    · exact x₁_notMem_p s (List.take_subset _ _ hx)
    · exact (x₁_adj_missed_vertex s).ne (by simpa using hx)
  apply PrismBasics.isHoleList_of_path_add_vertex hprey
  · simp only [pathLength, List.length_append, List.length_take, List.length_singleton]
    omega
  · exact (c.core.hp₁X s.x₁ (x₁_mem s)).symm
  · exact x₁_adj_missed_vertex s
  · exact hxout
  · intro v hv ha
    have hparts := (PathBasics.mem_interior_iff_of_pathFrom hprey).mp hv
    rcases List.mem_append.mp hparts.1 with hv | hv
    · exact hparts.2.1 (hxonly v (List.take_subset _ _ hv) ha)
    · exact hparts.2.2 (by simpa using hv)

/-- The three shared vertices force the antihole to have length four, by 15.7. -/
theorem four_of_three_shared (hG : InF6 G) (C D : List V)
    (hC : IsHoleList G C) (hCl : 4 < C.length) (hD : IsAntiholeList G D)
    (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huC : u ∈ C) (hvC : v ∈ C) (hwC : w ∈ C)
    (huD : u ∈ D) (hvD : v ∈ D) (hwD : w ∈ D) : D.length = 4 := by
  have hD4 : 4 ≤ D.length := hD.1
  by_contra hne
  have hle := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hG C D hC hCl hD
    (show 4 < D.length by omega)
  have hsub : ({u, v, w} : Set V) ⊆ {x | x ∈ C} ∩ {x | x ∈ D} := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨huC, huD⟩
    · exact ⟨hvC, hvD⟩
    · exact ⟨hwC, hwD⟩
  have hcard : ({u, v, w} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [huv, huw]),
      Set.ncard_pair hvw]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

end Workspace.ProofLemmas.Thm175Claim5Hole
