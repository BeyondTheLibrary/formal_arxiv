import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# The strict size decrease in 7.5 claim (2)

PAPER (printed p. 37): *"Since there is a proper subset F' of F with attachments in S and
in the new set T' ... it follows that we may apply the inductive hypothesis."*

A new rung puts a vertex of `F` in one of the two new sides. Join that vertex to an attachment
of the other side by a path in `F`, then delete the first vertex. Anticompleteness ensures
that the path has an edge, so its remaining vertices still attach to both sides.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim2Five82SmallerSet

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.InducedPathExtraction

/-- PAPER: *"there is a proper subset F' of F with attachments in S and in the new set T'"*.
This is the set argument, with the side meeting `F` named `A`. -/
theorem smaller_connected_of_meets_left {V : Type*} (G : SimpleGraph V)
    (A B F : Set V) (hconn : ConnectedSet G F) (hanti : Anticomplete G A B)
    (hmeet : (F ∩ A).Nonempty) (hattach : ∃ b ∈ B, ∃ f ∈ F, G.Adj b f) :
    ∃ F' : Set V, F' ⊂ F ∧ ConnectedSet G F' ∧
      (∃ a ∈ A, ∃ f ∈ F', G.Adj a f) ∧ (∃ b ∈ B, ∃ f ∈ F', G.Adj b f) := by
  classical
  obtain ⟨x, hxF, hxA⟩ := hmeet
  obtain ⟨b, hbB, f, hfF, hbf⟩ := hattach
  have hxf : x ≠ f := by
    intro h
    exact hanti x hxA b hbB (h ▸ hbf.symm)
  obtain ⟨p, hp, hpF⟩ := exists_isPathFrom_of_connected hconn hxF hfF
  have hpos := path_length_pos hp.1
  have hzero : p[0]'hpos = x := getElem_zero_of_head? hp.2.1 hpos
  have hlast : p[p.length - 1]'(by omega) = f :=
    getElem_last_of_getLast? hp.2.2 hpos
  have hlen : 2 ≤ p.length := by
    by_contra hnot
    apply hxf
    rw [← hzero, ← hlast]
    exact hp.1.2.1.getElem_inj_iff.mpr (by omega)
  have htail : IsPathList G p.tail := by
    rw [← List.drop_one]
    exact isPathList_drop hp.1 (by omega)
  let F' : Set V := {z | z ∈ p.tail}
  have hsub : F' ⊆ F := fun z hz => hpF z (List.mem_of_mem_tail hz)
  have hcons : x :: p.tail = p := List.cons_head?_tail hp.2.1
  have hxTail : x ∉ p.tail := by
    have hnd := hp.1.2.1
    rw [← hcons, List.nodup_cons] at hnd
    exact hnd.1
  have hproper : F' ⊂ F := hsub.ssubset_of_ne (by
    intro heq
    exact hxTail (show x ∈ F' from heq ▸ hxF))
  have hp₁Tail : p[1]'(by omega) ∈ p.tail := by
    have htpos : 0 < p.tail.length := by simp; omega
    have heq : p.tail[0]'htpos = p[1]'(by omega) := by simp
    rw [← heq]
    exact List.getElem_mem _
  have hxp₁ : G.Adj x (p[1]'(by omega)) := by
    have hadj := path_adj_succ hp.1 (show 0 + 1 < p.length by omega)
    rwa [hzero] at hadj
  have hfTail : f ∈ p.tail := by
    have hfp := (isPathFrom_ends_mem hp).2
    rw [← hcons, List.mem_cons] at hfp
    exact hfp.resolve_left hxf.symm
  exact ⟨F', hproper, connectedSet_setOf_mem_of_isPathList htail,
    ⟨x, hxA, p[1]'(by omega), hp₁Tail, hxp₁⟩, ⟨b, hbB, f, hfTail, hbf⟩⟩

/-- The two orientations of the printed size decrease. In the different-branch case `F`
meets the new `T`. In the same-branch case it meets the new `S`. -/
theorem smaller_connected_of_meets_either {V : Type*} (G : SimpleGraph V)
    (S T F : Set V) (hconn : ConnectedSet G F) (hanti : Anticomplete G S T)
    (hbridge : ((F ∩ S).Nonempty ∧ ∃ t ∈ T, ∃ f ∈ F, G.Adj t f) ∨
      ((F ∩ T).Nonempty ∧ ∃ s ∈ S, ∃ f ∈ F, G.Adj s f)) :
    ∃ F' : Set V, F' ⊂ F ∧ ConnectedSet G F' ∧
      (∃ s ∈ S, ∃ f ∈ F', G.Adj s f) ∧ (∃ t ∈ T, ∃ f ∈ F', G.Adj t f) := by
  rcases hbridge with ⟨hmeet, hattach⟩ | ⟨hmeet, hattach⟩
  · exact smaller_connected_of_meets_left G S T F hconn hanti hmeet hattach
  · have hanti' : Anticomplete G T S := fun t ht s hs hts => hanti s hs t ht hts.symm
    obtain ⟨F', hproper, hconn', hTF', hSF'⟩ :=
      smaller_connected_of_meets_left G T S F hconn hanti' hmeet hattach
    exact ⟨F', hproper, hconn', hSF', hTF'⟩

/-- A proper subset of a finite set of size `n + 1` has size at most `n`. -/
theorem ncard_le_of_ssubset {V : Type*} [Finite V] {F F' : Set V} {n : ℕ}
    (hcard : F.ncard = n + 1) (hproper : F' ⊂ F) : F'.ncard ≤ n := by
  have hlt := Set.ncard_lt_ncard hproper (Set.toFinite F)
  omega

end Workspace.ProofLemmas.Thm75Claim2Five82SmallerSet
