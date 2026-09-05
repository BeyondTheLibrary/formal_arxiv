import Workspace.ProofLemmas.CyclicThreeConnectedAttachments
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.Thm55Connectivity

/-!
# 5.5 — branch vertices survive a separator of size two

In a subdivision, deleting an internal vertex blocks just the original edge whose track contains
it.  Thus two internal deleted vertices block at most two original edges.  If one deleted vertex
is a branch vertex, the other blocks at most one edge after that original vertex is deleted.
The connectivity lemmas in `Thm55Connectivity` then lift paths in the original graph through the
unblocked tracks of the subdivision.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm55BranchReach

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments

variable {W : Type*} [Fintype W] [DecidableEq W]

private theorem track_rchIn_of_avoids {H : SimpleGraph W} {n : ℕ}
    {J : SimpleGraph (Fin n)} {S : Set W} {ι : Fin n → W}
    {T : Fin n → Fin n → List W}
    (hD : Workspace.ProofLemmas.NoCrossTrackBranch.SubData J H ι T)
    {a b : Fin n} (hab : J.Adj a b) (havoid : ∀ z ∈ T a b, z ∉ S) :
    RchIn H Sᶜ (ι a) (ι b) := by
  refine rchIn_of_chain (T a b)
    (List.isChain_iff_getElem.mpr (hD.track a b hab).1.2.2) ?_
    (List.mem_of_head? (hD.track a b hab).2.1)
    (List.mem_of_getLast? (hD.track a b hab).2.2)
  intro z hz hzS
  exact havoid z hz hzS

private theorem track_avoids_two_internal {H : SimpleGraph W} {n : ℕ}
    {J : SimpleGraph (Fin n)} {ι : Fin n → W} {T : Fin n → Fin n → List W}
    (hD : Workspace.ProofLemmas.NoCrossTrackBranch.SubData J H ι T)
    {a b c d z w : Fin n} (hab : J.Adj a b) (hcd : J.Adj c d) (hzw : J.Adj z w)
    {x y : W} (hx : x ∈ trackInterior (T a b)) (hy : y ∈ trackInterior (T c d))
    (hza : s(z, w) ≠ s(a, b)) (hzc : s(z, w) ≠ s(c, d)) :
    ∀ t ∈ T z w, t ∉ ({x, y} : Set W) := by
  intro t ht htxy
  rcases htxy with htx | hty
  · exact hD.disj a b z w hab hzw (Ne.symm hza) x hx (htx ▸ ht)
  · exact hD.disj c d z w hcd hzw (Ne.symm hzc) y hy (hty ▸ ht)

private theorem track_avoids_branch_internal {H : SimpleGraph W} {n : ℕ}
    {J : SimpleGraph (Fin n)} {ι : Fin n → W} {T : Fin n → Fin n → List W}
    (hD : Workspace.ProofLemmas.NoCrossTrackBranch.SubData J H ι T)
    {r a b z w : Fin n} (hab : J.Adj a b) (hzw : J.Adj z w)
    {y : W} (hy : y ∈ trackInterior (T a b))
    (hzr : z ≠ r) (hwr : w ≠ r) (hze : s(z, w) ≠ s(a, b)) :
    ∀ t ∈ T z w, t ∉ ({ι r, y} : Set W) := by
  intro t ht htxy
  rcases htxy with htr | hty
  · by_cases htint : t ∈ trackInterior (T z w)
    · exact hD.new z w hzw t htint ⟨r, htr.symm⟩
    · rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
          (hD.track z w hzw).2.1 (hD.track z w hzw).2.2 ht htint with h | h
      · exact hzr (hD.inj (h.symm.trans htr))
      · exact hwr (hD.inj (h.symm.trans htr))
  · exact hD.disj a b z w hab hzw (Ne.symm hze) y hy (hty ▸ ht)

private theorem subtype_edge_ne {U : Type*} {S : Set U} {z w a b : ↑S}
    (h : s(z, w) ≠ s(a, b)) : s((z : U), (w : U)) ≠ s((a : U), (b : U)) := by
  intro he
  apply h
  rcases Sym2.eq_iff.mp he with ⟨hza, hwb⟩ | ⟨hzb, hwa⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext hza, Subtype.ext hwb⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext hzb, Subtype.ext hwa⟩)

/-- Any two surviving branch vertices of a cyclically 3-connected graph remain joined after
deleting two specified vertices. -/
theorem branch_rchIn_compl_pair {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) {x y u v : W}
    (hub : u ∈ branchVertices H) (hvb : v ∈ branchVertices H)
    (hu : u ∈ ({x, y} : Set W)ᶜ) (hv : v ∈ ({x, y} : Set W)ᶜ) :
    RchIn H ({x, y} : Set W)ᶜ u v := by
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  have hc3' : CyclicallyThreeConnected H := ⟨n, J, hJ, hsub⟩
  obtain ⟨ι, T, hD⟩ := Workspace.ProofLemmas.NoCrossTrackBranch.exists_subData hsub
  have hbr : branchVertices H = Set.range ι :=
    Workspace.ProofLemmas.NoCrossTrackBranch.branch_eq_range hJ hD
  rw [hbr] at hub hvb
  obtain ⟨p, rfl⟩ := hub
  obtain ⟨q, rfl⟩ := hvb
  rcases hD.cover x with ⟨r, hx⟩ | ⟨a, b, hab, hx⟩
  · rcases hD.cover y with ⟨s, hy⟩ | ⟨a, b, hab, hy⟩
    · subst x
      subst y
      have hrb : ι r ∈ branchVertices H := by rw [hbr]; exact ⟨r, rfl⟩
      have hsb : ι s ∈ branchVertices H := by rw [hbr]; exact ⟨s, rfl⟩
      have hpb : ι p ∈ branchVertices H := by rw [hbr]; exact ⟨p, rfl⟩
      have hqb : ι q ∈ branchVertices H := by rw [hbr]; exact ⟨q, rfl⟩
      exact Workspace.ProofLemmas.NoCrossTrackBranch.branch_rchIn_of_two hc3' hrb hsb
        hpb hqb hu hv
    · subst x
      have hpr : p ≠ r := by
        intro h
        apply hu
        left
        exact congrArg ι h
      have hqr : q ≠ r := by
        intro h
        apply hv
        left
        exact congrArg ι h
      let p' : ↑(({r} : Set (Fin n))ᶜ) := ⟨p, by simpa⟩
      let q' : ↑(({r} : Set (Fin n))ᶜ) := ⟨q, by simpa⟩
      by_cases hrab : r = a ∨ r = b
      · have hconn := hJ.2 ({r} : Set (Fin n)) (by simp)
        obtain ⟨walk⟩ := hconn.preconnected p' q'
        refine rchIn_of_walk (H := H) (X := ({ι r, y} : Set W)ᶜ)
          (fun z : ↑(({r} : Set (Fin n))ᶜ) => ι (z : Fin n)) ?_ ?_ walk
        · intro z hzbad
          rcases hzbad with hz | hz
          · exact z.2 (hD.inj hz)
          · exact hD.new a b hab y hy ⟨z, hz⟩
        · intro z w hzw
          have hne : s((z : Fin n), (w : Fin n)) ≠ s(a, b) := by
            intro he
            have hrmem : r ∈ s((z : Fin n), (w : Fin n)) := by
              rw [he]
              rcases hrab with h | h
              · simp [h]
              · simp [h]
            rcases Sym2.mem_iff.mp hrmem with h | h
            · exact z.2 (by simpa using h.symm)
            · exact w.2 (by simpa using h.symm)
          exact track_rchIn_of_avoids hD hzw
            (track_avoids_branch_internal hD hab hzw hy z.2 w.2 hne)
      · have har : a ≠ r := fun h => hrab (Or.inl h.symm)
        have hbr' : b ≠ r := fun h => hrab (Or.inr h.symm)
        let a' : ↑(({r} : Set (Fin n))ᶜ) := ⟨a, by simpa⟩
        let b' : ↑(({r} : Set (Fin n))ᶜ) := ⟨b, by simpa⟩
        have hconn :=
          Thm55Connectivity.connected_induce_compl_singleton_delete_edge hJ r a' b'
        obtain ⟨walk⟩ := hconn.preconnected p' q'
        refine rchIn_of_walk (H := H) (X := ({ι r, y} : Set W)ᶜ)
          (fun z : ↑(({r} : Set (Fin n))ᶜ) => ι (z : Fin n)) ?_ ?_ walk
        · intro z hzbad
          rcases hzbad with hz | hz
          · exact z.2 (hD.inj hz)
          · exact hD.new a b hab y hy ⟨z, hz⟩
        · intro z w hzw
          rw [SimpleGraph.deleteEdges_adj] at hzw
          have hne : s((z : Fin n), (w : Fin n)) ≠ s(a, b) := by
            simpa [a', b'] using subtype_edge_ne hzw.2
          exact track_rchIn_of_avoids hD hzw.1
            (track_avoids_branch_internal hD hab hzw.1 hy z.2 w.2 hne)
  · rcases hD.cover y with ⟨r, hy⟩ | ⟨c, d, hcd, hy⟩
    · subst y
      have hswap : ({x, ι r} : Set W) = {ι r, x} := by ext z; simp [or_comm]
      rw [hswap] at hu hv ⊢
      have hpr : p ≠ r := by
        intro h
        apply hu
        left
        exact congrArg ι h
      have hqr : q ≠ r := by
        intro h
        apply hv
        left
        exact congrArg ι h
      let p' : ↑(({r} : Set (Fin n))ᶜ) := ⟨p, by simpa⟩
      let q' : ↑(({r} : Set (Fin n))ᶜ) := ⟨q, by simpa⟩
      by_cases hrab : r = a ∨ r = b
      · have hconn := hJ.2 ({r} : Set (Fin n)) (by simp)
        obtain ⟨walk⟩ := hconn.preconnected p' q'
        refine rchIn_of_walk (H := H) (X := ({ι r, x} : Set W)ᶜ)
          (fun z : ↑(({r} : Set (Fin n))ᶜ) => ι (z : Fin n)) ?_ ?_ walk
        · intro z hzbad
          rcases hzbad with hz | hz
          · exact z.2 (hD.inj hz)
          · exact hD.new a b hab x hx ⟨z, hz⟩
        · intro z w hzw
          have hne : s((z : Fin n), (w : Fin n)) ≠ s(a, b) := by
            intro he
            have hrmem : r ∈ s((z : Fin n), (w : Fin n)) := by
              rw [he]
              rcases hrab with h | h
              · simp [h]
              · simp [h]
            rcases Sym2.mem_iff.mp hrmem with h | h
            · exact z.2 (by simpa using h.symm)
            · exact w.2 (by simpa using h.symm)
          exact track_rchIn_of_avoids hD hzw
            (track_avoids_branch_internal hD hab hzw hx z.2 w.2 hne)
      · have har : a ≠ r := fun h => hrab (Or.inl h.symm)
        have hbr' : b ≠ r := fun h => hrab (Or.inr h.symm)
        let a' : ↑(({r} : Set (Fin n))ᶜ) := ⟨a, by simpa⟩
        let b' : ↑(({r} : Set (Fin n))ᶜ) := ⟨b, by simpa⟩
        have hconn :=
          Thm55Connectivity.connected_induce_compl_singleton_delete_edge hJ r a' b'
        obtain ⟨walk⟩ := hconn.preconnected p' q'
        refine rchIn_of_walk (H := H) (X := ({ι r, x} : Set W)ᶜ)
          (fun z : ↑(({r} : Set (Fin n))ᶜ) => ι (z : Fin n)) ?_ ?_ walk
        · intro z hzbad
          rcases hzbad with hz | hz
          · exact z.2 (hD.inj hz)
          · exact hD.new a b hab x hx ⟨z, hz⟩
        · intro z w hzw
          rw [SimpleGraph.deleteEdges_adj] at hzw
          have hne : s((z : Fin n), (w : Fin n)) ≠ s(a, b) := by
            simpa [a', b'] using subtype_edge_ne hzw.2
          exact track_rchIn_of_avoids hD hzw.1
            (track_avoids_branch_internal hD hab hzw.1 hx z.2 w.2 hne)
    · by_cases hedge : s(a, b) = s(c, d)
      · have hconn := Thm55Connectivity.connected_delete_edge hJ a b
        obtain ⟨walk⟩ := hconn.preconnected p q
        refine rchIn_of_walk (H := H) (X := ({x, y} : Set W)ᶜ) ι ?_ ?_ walk
        · intro z hzbad
          rcases hzbad with hz | hz
          · exact hD.new a b hab x hx ⟨z, hz⟩
          · exact hD.new c d hcd y hy ⟨z, hz⟩
        · intro z w hzw
          rw [SimpleGraph.deleteEdges_adj] at hzw
          exact track_rchIn_of_avoids hD hzw.1
            (track_avoids_two_internal hD hab hcd hzw.1 hx hy hzw.2
              (fun h => hzw.2 (h.trans hedge.symm)))
      · have hconn := Thm55Connectivity.connected_delete_two_edges hJ a b c d
        obtain ⟨walk⟩ := hconn.preconnected p q
        refine rchIn_of_walk (H := H) (X := ({x, y} : Set W)ᶜ) ι ?_ ?_ walk
        · intro z hzbad
          rcases hzbad with hz | hz
          · exact hD.new a b hab x hx ⟨z, hz⟩
          · exact hD.new c d hcd y hy ⟨z, hz⟩
        · intro z w hzw
          rw [SimpleGraph.deleteEdges_adj, SimpleGraph.deleteEdges_adj] at hzw
          exact track_rchIn_of_avoids hD hzw.1.1
            (track_avoids_two_internal hD hab hcd hzw.1.1 hx hy hzw.1.2 hzw.2)

/-- A separator of at most two vertices leaves all surviving branch vertices mutually
reachable. -/
theorem branch_rchIn_compl_of_ncard_le_two {H : SimpleGraph W}
    (hc3 : CyclicallyThreeConnected H) (S : Set W) (hcard : S.ncard ≤ 2)
    {u v : W} (hub : u ∈ branchVertices H) (hvb : v ∈ branchVertices H)
    (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ) : RchIn H Sᶜ u v := by
  by_cases hsmall : S.ncard ≤ 1
  · have hconn := connectedSet_compl_of_ncard_le_one hc3 hsmall
    exact ⟨hu, hv, hconn ⟨u, hu⟩ ⟨v, hv⟩⟩
  · have heq : S.ncard = 2 := by omega
    obtain ⟨x, y, -, rfl⟩ := Set.ncard_eq_two.mp heq
    exact branch_rchIn_compl_pair hc3 hub hvb hu hv

end Workspace.ProofLemmas.Thm55BranchReach
