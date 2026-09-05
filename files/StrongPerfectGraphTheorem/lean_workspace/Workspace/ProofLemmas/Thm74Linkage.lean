import Workspace.ProofLemmas.Thm101ClaimOne
import Workspace.ProofLemmas.PathAttach

/-!
# The two triangle linkages in 7.4

We use the paths `R₁` minus its last vertex, the single vertex `a₂`, and
`a₃-R₃-b₃-b₂`. The last path can catch a neighbour at either `b₂` or `b₃`.
Exchanging the first and third rungs gives the linkage at the end of the proof.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm74Linkage

open Workspace.Types.Core.SPGT Workspace.Types.Prisms.SPGT
open Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_dropLast {G : SimpleGraph V} {P : List V} {a b x : V}
    (hP : IsPathFrom G P a b) : x ∈ P.dropLast ↔ x ∈ P ∧ x ≠ b := by
  have he : P.getLast hP.1.1 = b := Option.some.inj
    ((List.getLast?_eq_some_getLast hP.1.1).symm.trans hP.2.2)
  rw [PathBasics.mem_dropLast_iff hP.1.2.1 hP.1.1, he]

theorem ends_nonadj {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (hlen : 3 ≤ P.length) : ¬ G.Adj a b := by
  have h := PathBasics.path_ends_not_adj hP.1 hlen
  rwa [PathBasics.getElem_zero_of_head? hP.2.1 (by omega),
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)] at h

/-- PAPER (7.4, printed p. 35): "Also, y cannot be linked onto the triangle
A′, by 2.4, and since one of b₂, b₃ ∈ X it follows that no internal vertex
of P₁′ is in X."

This constructs the linkage from a neighbour before the last vertex of the
first rung. The third path is extended by the bottom vertex of the middle rung.
The same construction, with the first and third rungs exchanged, is used in the
last sentence of the printed proof. -/
theorem link_extended {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2))
    (hlen : 3 ≤ (R 1).length) (y : V) (hya : G.Adj y (a 1))
    (hy0 : ∃ x ∈ (R 0).dropLast, G.Adj y x)
    (hy2 : (∃ x ∈ R 2, G.Adj y x) ∨ G.Adj y (b 1)) :
    VertexCanBeLinkedOntoTriangle G y (a 0) (a 1) (a 2) := by
  obtain ⟨hA, hB, hAB, hp, hc⟩ := PrismSymmetry.formPrism_family.mp h
  have ha (i : Fin 3) : a i ∈ R i := PathBasics.head_mem (hp i).2.1
  have hb (i : Fin 3) : b i ∈ R i := PathBasics.getLast_mem (hp i).2.2
  have hd (i j : Fin 3) (hij : i ≠ j) {x : V} (hi : x ∈ R i) (hj : x ∈ R j) :
      False := Thm101ClaimOne.paths_disjoint h hij hi hj
  have htrim (x : V) (hx : x ∈ (R 0).dropLast) : x ∈ R 0 ∧ x ≠ b 0 :=
    (mem_dropLast (hp 0)).mp hx
  have hlen0 := Thm101ClaimOne.two_le_length h 0
  have hpath0 : IsPathList G (R 0).dropLast := by
    rw [List.dropLast_eq_take]
    exact PathBasics.isPathList_take (hp 0).1 (by omega)
  have hhead0 : (R 0).dropLast.head? = some (a 0) := by
    rw [List.head?_dropLast, if_pos (by omega)]
    exact (hp 0).2.1
  have hpath2 : IsPathFrom G (R 2 ++ [b 1]) (a 2) (b 1) := by
    refine PathAttach.isPathFrom_concat (hp 2) (hB 1 2 (by decide)) ?_ ?_
    · exact fun hx => hd 1 2 (by decide) (hb 1) hx
    · intro x hx hxb hbx
      rcases (hc 1 2 (by decide) _ (hb 1) x hx).mp hbx with hh | hh
      · exact hAB 1 1 hh.1.symm
      · exact hxb hh.2
  have hmid : ¬ G.Adj (a 1) (b 1) := ends_nonadj (hp 1) hlen
  refine ⟨(R 0).dropLast, [a 1], R 2 ++ [b 1],
    ⟨hpath0, PathBasics.isPathList_singleton G _, hpath2.1⟩,
    ⟨?_, ?_, ?_⟩, ⟨Or.inl hhead0, Or.inl rfl, Or.inl hpath2.2.1⟩,
    ⟨?_, ?_, ?_⟩, hy0, ⟨a 1, by simp, hya⟩, ?_⟩
  · intro x hx hx1
    have he : x = a 1 := by simpa using hx1
    exact hd 0 1 (by decide) (htrim x hx).1 (he ▸ ha 1)
  · intro x hx hx2
    rcases List.mem_append.mp hx2 with hx2 | hx2
    · exact hd 0 2 (by decide) (htrim x hx).1 hx2
    · have he : x = b 1 := by simpa using hx2
      exact hd 0 1 (by decide) (htrim x hx).1 (he ▸ hb 1)
  · intro x hx hx2
    have he : x = a 1 := by simpa using hx
    subst x
    rcases List.mem_append.mp hx2 with hx2 | hx2
    · exact hd 1 2 (by decide) (ha 1) hx2
    · exact hAB 1 1 (by simpa using hx2)
  · intro x hx z hz
    have he : z = a 1 := by simpa using hz
    subst z
    rw [hc 0 1 (by decide) x (htrim x hx).1 _ (ha 1)]
    simp [(htrim x hx).2]
  · intro x hx z hz
    rcases List.mem_append.mp hz with hz | hz
    · rw [hc 0 2 (by decide) x (htrim x hx).1 z hz]
      simp [(htrim x hx).2]
    · have he : z = b 1 := by simpa using hz
      subst z
      rw [hc 0 1 (by decide) x (htrim x hx).1 _ (hb 1)]
      simp [(htrim x hx).2, (hAB 1 1).symm, (hAB 2 1).symm]
  · intro x hx z hz
    have he : x = a 1 := by simpa using hx
    subst x
    rcases List.mem_append.mp hz with hz | hz
    · rw [hc 1 2 (by decide) _ (ha 1) z hz]
      simp [hAB 1 1]
    · have he : z = b 1 := by simpa using hz
      subst z
      simp [hmid, (hAB 2 1).symm]
  · rcases hy2 with ⟨x, hx, hyx⟩ | hyb
    · exact ⟨x, List.mem_append_left _ hx, hyx⟩
    · exact ⟨b 1, by simp, hyb⟩

/-- The first application of 2.4 in the proof of 7.4: a vertex missing the
first and third top vertices cannot have both a neighbour before the end of
the first rung and a neighbour in the extended third rung. -/
theorem no_neighbor_before_end {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) (hlen : 3 ≤ (R 1).length)
    {y : V} (hy0 : ¬ G.Adj y (a 0)) (hy1 : G.Adj y (a 1))
    (hy2 : ¬ G.Adj y (a 2))
    (hyb : (∃ x ∈ R 2, G.Adj y x) ∨ G.Adj y (b 1)) :
    ∀ x ∈ (R 0).dropLast, ¬ G.Adj y x := by
  intro x hx hyx
  have hlink := link_extended h hlen y hy1 ⟨x, hx, hyx⟩ hyb
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG y _ _ _ hlink with hh | hh | hh
  · exact hy0 hh.1
  · exact hy0 hh.1
  · exact hy2 hh.2

end Workspace.ProofLemmas.Thm74Linkage
