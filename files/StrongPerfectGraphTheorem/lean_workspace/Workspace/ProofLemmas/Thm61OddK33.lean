import Workspace.ProofLemmas.Thm61OddTriads
import Workspace.ProofLemmas.CyclicThreeConnectedAttachments

/-! Recovering `J = H = K₃,₃` in the last paragraph of 6.1(7). -/
set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61OddK33

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.SubdivisionCounting

/-- Paper, 6.1(7): "Since `H` is a subdivision of a 3-connected graph,
`J = K₃,₃`." A connected graph containing a `K₃,₃` whose six vertices
all have degree three has no other vertices. -/
theorem cubic_six_exhaust
    {W : Type*} [Finite W] {H : SimpleGraph W} (hconn : H.Preconnected)
    (a b : Fin 3 → W) (ha : Function.Injective a) (hb : Function.Injective b)
    (hcross : ∀ i j, H.Adj (a i) (b j))
    (hda : ∀ i, (H.neighborSet (a i)).ncard = 3)
    (hdb : ∀ i, (H.neighborSet (b i)).ncard = 3) :
    ∀ w : W, (∃ i, w = a i) ∨ ∃ j, w = b j := by
  have nb : ∀ i w, H.Adj (a i) w → ∃ j, w = b j := by
    intro i w hw
    rcases neighbor_of_degree_three (hda i) (hb.ne (by decide : (0 : Fin 3) ≠ 1))
        (hb.ne (by decide : (0 : Fin 3) ≠ 2)) (hb.ne (by decide : (1 : Fin 3) ≠ 2))
        (hcross i 0) (hcross i 1) (hcross i 2) hw with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have na : ∀ j w, H.Adj (b j) w → ∃ i, w = a i := by
    intro j w hw
    rcases neighbor_of_degree_three (hdb j) (ha.ne (by decide : (0 : Fin 3) ≠ 1))
        (ha.ne (by decide : (0 : Fin 3) ≠ 2)) (ha.ne (by decide : (1 : Fin 3) ≠ 2))
        (hcross 0 j).symm (hcross 1 j).symm (hcross 2 j).symm hw with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have stay : ∀ {u v : W}, H.Walk u v →
      ((∃ i, u = a i) ∨ ∃ j, u = b j) → ((∃ i, v = a i) ∨ ∃ j, v = b j) := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      intro hu
      apply ih
      rcases hu with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · exact Or.inr (nb i v huv)
      · exact Or.inl (na j v huv)
  intro w
  obtain ⟨p⟩ := hconn (a 0) w
  exact stay p (Or.inl ⟨0, rfl⟩)

/-- A subdivision with no internal vertices is isomorphic to its original graph.
This supplies the `J = H` part of the last sentence of 6.1(7). -/
theorem iso_of_all_branch_vertices
    {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    (hsub : IsSubdivision J H) (hall : ∀ w, w ∈ branchVertices H) : Nonempty (J ≃g H) := by
  classical
  obtain ⟨ι, T, hι, ht, hl, hr, hd, hn, hc, he⟩ := hsub
  have hs : Function.Surjective ι := fun w =>
    branchVertices_subset_range ht hr hd hc he (hall w)
  let e : U ≃ W := Equiv.ofBijective ι ⟨hι, hs⟩
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  intro u v
  change H.Adj (ι u) (ι v) ↔ J.Adj u v
  refine ⟨original_adj_of_subdivision_adj hι ht hn he, ?_⟩
  intro huv
  have hlen : (T u v).length = 2 := by
    have hp := hl u v huv
    simp only [trackLength] at hp
    by_contra h
    have hi : (T u v)[1]'(by omega) ∈ trackInterior (T u v) :=
      mem_trackInterior_getElem _ 0 (by omega)
    exact hn u v huv _ hi (hs _)
  have hadj := (ht u v huv).1.2.2 0 (by omega)
  rw [track_head (ht u v huv) (by omega), track_last (ht u v huv) hlen] at hadj
  exact hadj

/-- Paper, 6.1(7): "`J = K₃,₃`, and `L(H)` is a degenerate appearance of `J`."
The six labelled vertices form the complete bipartition and have degree three. -/
theorem degenerate_of_cubic_bipartition
    {m n : ℕ} (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (H : SimpleGraph (Fin n)) (hsub : IsBipartiteSubdivision J H)
    (a b : Fin 3 → Fin n) (ha : Function.Injective a) (hb : Function.Injective b)
    (hcross : ∀ i j, H.Adj (a i) (b j))
    (hda : ∀ i, (H.neighborSet (a i)).ncard = 3)
    (hdb : ∀ i, (H.neighborSet (b i)).ncard = 3) :
    Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
    DegenerateAppearance J H := by
  have hconn := CyclicThreeConnectedAttachments.preconnected_of_cyclicallyThreeConnected
    (H := H) ⟨m, J, hJ, hsub.1⟩
  have hall := cubic_six_exhaust hconn a b ha hb hcross hda hdb
  have hleft : ∀ i j, ¬ H.Adj (a i) (a j) := by
    intro i j hij
    exact Thm84RungEndDictionary.no_triangle_of_bipartite hsub.2
      hij (hcross j 0) (hcross i 0)
  have hright : ∀ i j, ¬ H.Adj (b i) (b j) := by
    intro i j hij
    exact Thm84RungEndDictionary.no_triangle_of_bipartite hsub.2
      hij (hcross 0 j).symm (hcross 0 i).symm
  obtain ⟨hiso⟩ := iso_completeBipartite_three_three a b ha hb
    (fun i j => (hcross i j).ne) hall hcross hleft hright
  obtain ⟨jiso⟩ := iso_of_all_branch_vertices hsub.1 (by
    intro w
    rcases hall w with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · change 3 ≤ (H.neighborSet (a i)).ncard
      rw [hda]
    · change 3 ≤ (H.neighborSet (b j)).ncard
      rw [hdb])
  have hj33 := jiso.trans hiso
  refine ⟨⟨hj33⟩, Or.inr ⟨?_, ⟨hj33⟩, ⟨hiso⟩⟩⟩
  rintro ⟨hj4⟩
  have hcard := Fintype.card_congr (hj4.symm.trans hj33).toEquiv
  norm_num at hcard

end Workspace.ProofLemmas.Thm61OddK33
