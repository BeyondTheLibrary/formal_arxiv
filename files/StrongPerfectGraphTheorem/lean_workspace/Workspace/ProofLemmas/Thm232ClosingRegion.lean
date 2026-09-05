import Workspace.ProofLemmas.Thm232ClosingPath
import Workspace.Types.Wheels

/-! The connected set `F ∪ A₀` used to catch the closing triangle in 23.2. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingRegion

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The region used in the closing proof.  Its two prescribed neighbours are `y`
at `z`, and the next rim vertex `s` at the inactive rim neighbour `p`. -/
structure Region (G : SimpleGraph V) (C : List V) (Y : Set V) (z p u y : V) where
  s : V
  B : Set V
  sC : s ∈ C
  pnb : IsRimNeighbours G C p z s
  connected : ConnectedSet G B
  avoid : ∀ a ∈ B, a ≠ z ∧ a ≠ p ∧ a ≠ u ∧ a ∉ Y
  ymem : y ∈ B
  smem : s ∈ B
  ys : y ≠ s
  not_adj_ys : ¬ G.Adj y s
  zy : G.Adj z y
  zunique : ∀ a ∈ B, G.Adj z a → a = y
  punique : ∀ a ∈ B, G.Adj p a → a = s
  hub_attach : ∀ h ∈ Y, ∃ a ∈ B, G.Adj h a
  pair_incomplete : ∀ a ∈ B, ¬ VertexComplete G a ({p,u} : Set V)
  y_incomplete : ¬ VertexComplete G y Y

/-- PAPER (23.2, printed p. 141): “Let `F = {y,v₁,…,v_n}`. ... Let `S` be a path
from `y` to `x₀` with interior in `F ∪ A₀`.”  The original path attaches `F` to
the connected arc `A₀`; inducedness gives the unique neighbour of `z`. -/
theorem region {G : SimpleGraph V} {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    {z p u y w : V} (hzC : z ∈ C) (hnb : IsRimNeighbours G C z p u)
    {T R : List V} (hTeq : T = z :: y :: R) (hT : IsPathFrom G T z w)
    (hwC : w ∈ C) (hwz : w ≠ z) (havoid : ∀ a ∈ T, a ≠ p ∧ a ≠ u)
    (hint : ∀ a ∈ SPGT.interior T, a ∉ Y ∧ ¬ VertexComplete G a Y)
    (hyA : VertexAnticomplete G y ({a : V | a ∈ C} \ ({z,p,u} : Set V)))
    (hpF : VertexAnticomplete G p {a : V | a ∈ SPGT.interior T}) :
    Nonempty (Region G C Y z p u y) := by
  have hC := hw.1.1
  have hC6 : 6 ≤ C.length := hw.1.2
  let A : Set V := {a : V | a ∈ C} \ ({z,p,u} : Set V)
  let F : Set V := {a : V | a ∈ SPGT.interior T}
  let B := F ∪ A
  have hyT : y ∈ T := by rw [hTeq]; simp
  have hzT : z ∈ T := PathBasics.head_mem hT.2.1
  have hwT : w ∈ T := PathBasics.getLast_mem hT.2.2
  have hT2 : 2 ≤ T.length := by rw [hTeq]; simp
  have hfirst : T[0]'(by omega) = z := PathBasics.getElem_zero_of_head? hT.2.1 (by omega)
  have hsecond : T[1]'(by omega) = y := by
    have hh : T[1]? = some y := by rw [hTeq]; rfl
    exact Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hh)
  have hzy : G.Adj z y := by
    have hh := PathBasics.path_adj_succ hT.1 (i := 0) (by omega)
    rwa [hfirst, hsecond] at hh
  have hyC : y ∉ C := by
    intro hy
    exact (hnb.2.2.2.2.2 y hy hzy).elim (havoid y hyT).1 (havoid y hyT).2
  have hyF : y ∈ F := (PathBasics.mem_interior_iff_of_pathFrom hT).mpr
    ⟨hyT, hzy.ne', fun he => hyC (he ▸ hwC)⟩
  have hwA : w ∈ A := mem_rim_minus.mpr ⟨hwC, hwz, (havoid w hwT).1, (havoid w hwT).2⟩
  have hT3 : 3 ≤ T.length := by
    have hh := PathBasics.interior_length T
    have hn : 0 < (SPGT.interior T).length := List.length_pos_of_mem hyF
    omega
  have hFconn : ConnectedSet G F := by
    change ConnectedSet G {a : V | a ∈ SPGT.interior T}
    rw [PathBasics.interior_eq_drop_take]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain
      (((InducedPathExtraction.isChain_of_isPathList hT.1).drop 1).take (T.length - 2))
  have hconn : ConnectedSet G B := by
    obtain ⟨a, ha, hwa⟩ := Thm232ClosingPath.end_attaches
      (PathBasics.isPathFrom_reverse hT) (by simpa using hT3)
    exact ConnectedSetUnionAttach.connectedSet_union hFconn (connectedSet_rim_minus hC hzC hnb)
      (Or.inr ⟨a, PathBasics.mem_interior_reverse.mp ha, w, hwA, hwa.symm⟩)
  obtain ⟨s, hnps⟩ : ∃ s : V, IsRimNeighbours G C p z s := by
    obtain ⟨a, b, r, k, hr⟩ := exists_rim_normal_form hC hnb.2.1
    have hpre : [a,p,b] <+: C.rotate k := ⟨r, hr.symm⟩
    have hn := (hole_triple hC ⟨k,hpre⟩).2.2.2
    rcases hn.2.2.2.2.2 z hzC hnb.2.2.2.1.symm with he | he
    · exact ⟨b, he ▸ hn⟩
    · exact ⟨a, he ▸ isRimNeighbours_symm hn⟩
  have hsC : s ∈ C := hnps.2.2.1
  have hps : G.Adj p s := hnps.2.2.2.2.1
  have hsA : s ∈ A := by
    refine mem_rim_minus.mpr ⟨hsC, hnps.1.symm, hps.ne', ?_⟩
    intro he
    exact rimNeighbours_not_adj hC hzC hnb (he ▸ hps)
  have hBavoid : ∀ a ∈ B, a ≠ z ∧ a ≠ p ∧ a ≠ u ∧ a ∉ Y := by
    intro a ha
    rcases ha with ha | ha
    · have haT := PathBasics.interior_subset ha
      exact ⟨((PathBasics.mem_interior_iff_of_pathFrom hT).mp ha).2.1,
        (havoid a haT).1, (havoid a haT).2, (hint a ha).1⟩
    · obtain ⟨haC, haz, hap, hau⟩ := mem_rim_minus.mp ha
      exact ⟨haz, hap, hau, hw.2.1.2.2 a haC⟩
  refine ⟨{
    s := s, B := B, sC := hsC, pnb := hnps, connected := hconn
    avoid := hBavoid, ymem := Or.inl hyF, smem := Or.inr hsA
    ys := fun he => hyC (he ▸ hsC), not_adj_ys := hyA s hsA, zy := hzy
    zunique := ?_, punique := ?_, hub_attach := ?_, pair_incomplete := ?_
    y_incomplete := (hint y hyF).2 }⟩
  · intro a ha hza
    rcases ha with ha | ha
    · obtain ⟨j, hj, hj1, hj2, hja⟩ := PathBasics.exists_getElem_of_mem_interior hT.1 ha
      have hh : G.Adj (T[0]'(by omega)) (T[j]'hj) := by rwa [hfirst, hja]
      have hjone : j = 1 := by
        have := (PathBasics.path_adj_iff hT.1 (by omega) hj).mp hh
        omega
      exact hja.symm.trans ((hT.1.2.1.getElem_inj_iff.mpr hjone).trans hsecond)
    · obtain ⟨haC, _, hap, hau⟩ := mem_rim_minus.mp ha
      exact ((hnb.2.2.2.2.2 a haC hza).elim hap hau).elim
  · intro a ha hpa
    rcases ha with ha | ha
    · exact (hpF a ha hpa).elim
    · obtain ⟨haC, haz, _, _⟩ := mem_rim_minus.mp ha
      exact (hnps.2.2.2.2.2 a haC hpa).resolve_left haz
  · intro h hh
    obtain ⟨a, ha, hha⟩ := hub_exists_nbr_rim_minus (z := z) (x₀ := p) (x₁ := u) hw hh
    exact ⟨a, Or.inr ha, hha⟩
  · intro a ha hcomplete
    rcases ha with ha | ha
    · exact hpF a ha (hcomplete p (by simp)).symm
    · exact no_pair_complete_rim_minus hC (by omega) hzC hnb a ha hcomplete

end Workspace.ProofLemmas.Thm232ClosingRegion
