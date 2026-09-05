import Workspace.ProofLemmas.Thm175FinalBlocks

/-! The complete vertex after the last neighbour, in the closing argument of 17.5. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175FinalParity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm175Minimal Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claims Workspace.ProofLemmas.Thm175FinalBlocks

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "From the optimality of `P,X,Y`, it follows that `P,W,Y` is not a
counterexample ... and so there are an odd number of `W`-complete edges in `P`." -/
theorem odd_W_edges {G : SimpleGraph V} {z : V} (c : Counterexample G z)
    (hopt : IsOptimal c) (b : AntipathBlocks G c.X c.Y)
    (t : FirstMissContext c.core.p₁ b) :
    Odd (completePathEdges G (W b t) c.core.p).ncard := by
  classical
  have hWsub : W b t ⊆ c.X ∪ c.Y := by
    rintro v (hv | hv)
    · exact Or.inl hv.1
    · exact Or.inr ((b.hYverts v).mp (List.take_subset _ _ hv))
  have hpW : VertexComplete G c.core.p₁ (W b t) := by
    rintro v (hv | hv)
    · exact c.core.hp₁X v hv.1
    · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hv
      have hit : i < t.t₀ := by have := hi; simp only [List.length_take] at this; omega
      have hiv : b.qY[i]'(lt_trans hit t.ht₀) = v := by
        simpa only [List.getElem_take] using he
      exact hiv ▸ t.hbefore i hit
  have hxX : b.x₁ ∈ c.X := (b.hXverts _).mp (PathBasics.head_mem b.hxhead)
  have hxY : b.x₁ ∉ c.Y := fun hy => Set.disjoint_left.mp (blocks_disjoint b) hxX hy
  have hxW : b.x₁ ∉ W b t := by
    rintro (hx | hx)
    · exact hx.2 rfl
    · exact hxY ((b.hYverts _).mp (List.take_subset _ _ hx))
  obtain ⟨hWa, hWYa⟩ := W_anticonnected b t
  by_contra hnot
  let d : Counterexample G z :=
    { X := W b t
      Y := c.Y
      core :=
        { p := c.core.p
          p₁ := c.core.p₁
          pₙ := c.core.pₙ
          hp := c.core.hp
          hodd := c.core.hodd
          hlong := c.core.hlong
          houtX := by
            intro v hv hW
            rcases hWsub hW with hx | hy
            · exact c.core.houtX v hv hx
            · exact c.core.houtY v hv hy
          houtY := c.core.houtY
          hp₁X := hpW
          hYuniq := c.core.hYuniq
          hzP := c.core.hzP
          hzanti := c.core.hzanti
          heven := Nat.not_odd_iff_even.mp hnot }
      hXa := hWa
      hYa := c.hYa
      hXYa := hWYa
      hz := by
        rintro (hW | hy)
        · exact c.hz (hWsub hW)
        · exact c.hz (Or.inr hy)
      hzXY := by
        rintro v (hW | hy)
        · exact c.hzXY v (hWsub hW)
        · exact c.hzXY v (Or.inr hy) }
  apply hopt.2.1 d rfl
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · rintro v (hW | hy)
    · exact hWsub hW
    · exact Or.inr hy
  · intro he
    have hx : b.x₁ ∈ d.X ∪ d.Y := he.symm ▸ (Or.inl hxX : b.x₁ ∈ c.X ∪ c.Y)
    exact hx.elim hxW hxY

/-- PAPER: "From (5), since `p_h` is adjacent to `x₁`, it follows that `p_h`
is not complete to `X\{x₁}`." -/
theorem last_not_complete {G : SimpleGraph V} {z : V} (c : Counterexample G z)
    (hfirst : ∀ w ∈ c.core.p, VertexComplete G w c.X ↔ w = c.core.p₁)
    (b : AntipathBlocks G c.X c.Y) (last : LastNeighborContext c b)
    (h5 : 0 < last.h) :
    ¬ VertexComplete G (c.core.p[last.h]'last.hlt) (c.X \ {b.x₁}) := by
  intro hc
  have hcomp : VertexComplete G (c.core.p[last.h]'last.hlt) c.X := by
    intro x hx
    by_cases he : x = b.x₁
    · exact he ▸ last.hadj.symm
    · exact hc x ⟨hx, he⟩
  have he := (hfirst _ (List.getElem_mem _) ).mp hcomp
  have h0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (PathBasics.path_length_pos c.core.hp.1)
  have hi := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans h0.symm)
  omega

/-- PAPER: "There are an odd number [of `W`-complete edges] in the path
`p_h-...-p_n` ... Choose `i,j` ... Hence `j>i`."  Only the later complete
vertex is needed below. Since `p_h` is not complete, its index exceeds `h+1`. -/
theorem later_complete {G : SimpleGraph V} {z : V} (c : Counterexample G z)
    (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p, VertexComplete G w c.X ↔ w = c.core.p₁)
    (b : AntipathBlocks G c.X c.Y) (t : FirstMissContext c.core.p₁ b)
    (h4 : Claim4Conclusion c b t) (last : LastNeighborContext c b)
    (h5 : 0 < last.h) :
    ∃ j, ∃ hj : j < c.core.p.length,
      last.h + 1 < j ∧ VertexComplete G (c.core.p[j]'hj) (W b t) := by
  classical
  have hodd := odd_W_edges c hopt b t
  have hnot := last_not_complete c hfirst b last h5
  have hnotW : ¬ VertexComplete G (c.core.p[last.h]'last.hlt) (W b t) :=
    fun h => hnot (fun v hv => h v (Or.inl hv))
  have hxX : b.x₁ ∈ c.X := (b.hXverts _).mp (PathBasics.head_mem b.hxhead)
  have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (PathBasics.path_length_pos c.core.hp.1)
  have heven : Even (completePathEdges G (W b t)
      (c.core.p.take (last.h + 1))).ncard := by
    have hh := h4 0 last.h h5 last.hlt
      (by simpa only [hp0] using (c.core.hp₁X b.x₁ hxX).symm) last.hadj
    simpa only [List.drop_zero, Nat.sub_zero] using hh
  by_contra hn
  have hbound (i : ℕ) (hi : i < c.core.p.length)
      (hc : VertexComplete G (c.core.p[i]'hi) (W b t)) : i ≤ last.h + 1 := by
    by_contra hle
    exact hn ⟨i, hi, by omega, hc⟩
  have heq : completePathEdges G (W b t) c.core.p =
      completePathEdges G (W b t) (c.core.p.take (last.h + 1)) := by
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hE⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      have hbi := hbound i hi hE.2.1
      have hbj := hbound j hj hE.2.2
      have hni : i ≠ last.h := by intro he; subst i; exact hnotW hE.2.1
      have hnj : j ≠ last.h := by intro he; subst j; exact hnotW hE.2.2
      have hadj := (PathBasics.path_adj_iff c.core.hp.1 hi hj).mp hE.1
      have hil : i ≤ last.h := by omega
      have hjl : j ≤ last.h := by omega
      exact ⟨_, Thm182EdgeSetTake.getElem_mem_take _ hi hil,
        _, Thm182EdgeSetTake.getElem_mem_take _ hj hjl, rfl, hE⟩
    · rintro ⟨u, hu, v, hv, rfl, hE⟩
      exact ⟨u, List.take_subset _ _ hu, v, List.take_subset _ _ hv, rfl, hE⟩
  rw [heq] at hodd
  exact (Nat.not_odd_iff_even.mpr heven) hodd

end Workspace.ProofLemmas.Thm175FinalParity
