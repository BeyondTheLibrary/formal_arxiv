import Workspace.ProofLemmas.Thm74Linkage
import Workspace.ProofLemmas.PrismBasics

/-!
# The two odd holes in 7.4

An even rung together with two adjacent extra vertices forms an odd hole
when those vertices attach only at opposite ends of the rung.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm74Holes

open Workspace.Types.Core.SPGT Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas
open Thm74Linkage

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A top triangle vertex meets another rung only at its top end. -/
theorem top_adj_rung {G : SimpleGraph V} {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    a i ∉ R j ∧ ∀ x ∈ R j, (G.Adj (a i) x ↔ x = a j) := by
  obtain ⟨hA, hB, hAB, hp, hc⟩ := PrismSymmetry.formPrism_family.mp h
  have hai : a i ∈ R i := PathBasics.head_mem (hp i).2.1
  refine ⟨fun hx => Thm101ClaimOne.paths_disjoint h hij hai hx, ?_⟩
  intro x hx
  rw [hc i j hij _ hai x hx]
  simp [hAB i i]

/-- PAPER (7.4, printed p. 35): "Hence b₁ ∉ X, for otherwise
y-a₂-a₁′-P₁′-b₁- would be an odd hole." Also: "Since
y-a₁-a₃-P₃-b₃-y is not an odd hole, there is a member of X in P₃ ∖ b₃."

Both sentences use the same hole: an even path closed through two adjacent
vertices, each with only one neighbour on that path. -/
theorem even_rung_hole_absurd {G : SimpleGraph V} (hG : Berge G)
    {P : List V} {a b x y : V} (hP : IsPathFrom G P a b)
    (heven : Even (pathLength P)) (hlen : 2 ≤ pathLength P)
    (hx : x ∉ P) (hxadj : ∀ z ∈ P, G.Adj x z ↔ z = a)
    (hyx : G.Adj y x) (hyb : G.Adj y b)
    (hytrim : ∀ z ∈ P.dropLast, ¬ G.Adj y z) : False := by
  have hlen' : 3 ≤ P.length := by dsimp [pathLength] at hlen; omega
  have hab : a ≠ b := by
    intro he
    have hpos : 0 < P.length := by omega
    have h0 := PathBasics.getElem_zero_of_head? hP.2.1 hpos
    have hn := PathBasics.getElem_last_of_getLast? hP.2.2 hpos
    have hind := hP.1.2.1.getElem_inj_iff.mp (h0.trans (he.trans hn.symm))
    omega
  have ha : a ∈ P := PathBasics.head_mem hP.2.1
  have hb : b ∈ P := PathBasics.getLast_mem hP.2.2
  have hy : y ∉ P := by
    intro hyp
    have he : y = a := (hxadj y hyp).mp hyx.symm
    exact ends_nonadj hP hlen' (he ▸ hyb)
  have hhole : IsHoleList G (y :: x :: P) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hP (by omega)
      ((hxadj a ha).mpr rfl) hyb hyx.symm hx hy ?_ ?_ ?_ ?_
    · exact fun hxb => hab ((hxadj b hb).mp hxb).symm
    · exact hytrim a ((mem_dropLast hP).mpr ⟨ha, hab⟩)
    · intro z hz hxz
      have hz' := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hz
      exact hz'.2.1 ((hxadj z hz'.1).mp hxz)
    · intro z hz
      have hz' := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hz
      exact hytrim z ((mem_dropLast hP).mpr ⟨hz'.1, hz'.2.2⟩)
  have he := hG.1 _ hhole
  simp only [holeLength, List.length_cons, Nat.even_iff] at he
  simp only [pathLength, Nat.even_iff] at heven
  omega

end Workspace.ProofLemmas.Thm74Holes
