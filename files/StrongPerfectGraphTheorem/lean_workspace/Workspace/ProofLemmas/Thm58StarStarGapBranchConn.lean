import Workspace.ProofLemmas.Thm58StarStarGapTracks
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm57Claim2ConnCore

/-!
# Deleting a branch from a subdivision of a 3-connected graph

PAPER, proof of 5.8 (4), printed p. 27, implicit in *"There is a path `S₁` from `A₁` to `A₂`
with no vertex in `N_{v₁} ∪ N_{v₂} ∪ V(R_{v₁v₂})` except for its ends"*: the graph obtained
from `H` by deleting the branch `R_{v₁v₂}` — its two ends and its internal vertices — is
connected.

The branch is the subdividing track `T a b` of an edge `ab` of `J`.  Deleting it leaves, for
every other vertex `c` of `J`, the branch-vertex `ι c`; any two of these are joined because
`J \ {a, b}` is connected (`J` is 3-connected), and every subdividing track between two
surviving vertices of `J` avoids `T a b` altogether.  Every other surviving vertex is internal
to some track `T c d` with `s(c,d) ≠ s(a,b)`, and at least one end of that track survives, so
the part of the track between the vertex and that end reaches a surviving branch-vertex.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapBranchConn

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.NoCrossTrackBranch

variable {W : Type*} [Fintype W] [DecidableEq W]

private theorem mem_interior_of_index {l : List W} {j : ℕ} (hj : j + 1 < l.length)
    (h0 : 0 < j) : l[j]'(by omega) ∈ trackInterior l := by
  refine (SubdivisionCounting.mem_trackInterior_iff l _).mpr ⟨j - 1, by omega, ?_⟩
  exact SubdivisionCounting.getElem_eq_of_index_eq l (by omega) (by omega) (by omega)

/-- PAPER, proof of 5.8 (4), printed p. 27: the graph obtained from `H` by deleting the branch
between `v₁` and `v₂` is connected. -/
theorem branch_complement_connected {H : SimpleGraph W} (hc3 : CyclicallyThreeConnected H)
    {q : List W} (hq : IsBranch H q) (hq2 : 2 ≤ q.length) :
    ConnectedSet H ({x : W | x ∈ q}ᶜ) := by
  classical
  obtain ⟨M, J, hJ, hsub⟩ := hc3
  obtain ⟨ι, T, hS⟩ := exists_subData hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  obtain ⟨a, b, hab, hEq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
    hS.inj hS.track hS.len hS.rev hS.disj hS.new hS.cover hS.edges hdeg hq hq2
  set X : Set W := {x : W | x ∈ q}ᶜ with hXdef
  have hTlen : 2 ≤ (T a b).length := by
    have := hS.len a b hab
    simp only [trackLength] at this
    omega
  have hmemq : ∀ z : W, z ∈ q ↔ z ∈ T a b := by
    intro z
    exact ⟨fun h => Thm57Claim2ConnCore.mem_of_trackEdges_eq hq2 hEq h,
      fun h => Thm57Claim2ConnCore.mem_of_trackEdges_eq hTlen hEq.symm h⟩
  have hXiff : ∀ z : W, z ∈ X ↔ z ∉ T a b := by
    intro z
    simp only [hXdef, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact not_congr (hmemq z)
  have hTa : ι a ∈ T a b := List.mem_of_head? (hS.track a b hab).2.1
  have hTb : ι b ∈ T a b := List.mem_of_getLast? (hS.track a b hab).2.2
  -- images of vertices other than `a`, `b` survive
  have hbase : ∀ c : Fin M, c ≠ a → c ≠ b → ι c ∈ X := by
    intro c hca hcb
    rw [hXiff]
    intro hc
    by_cases hint : ι c ∈ trackInterior (T a b)
    · exact hS.new a b hab _ hint ⟨c, rfl⟩
    · rcases SubdivisionCompose.mem_ends_of_mem (hS.track a b hab).2.1
        (hS.track a b hab).2.2 hc hint with h | h
      · exact hca (hS.inj h)
      · exact hcb (hS.inj h)
  -- a whole subdividing track other than the branch, both of whose ends survive, lies in `X`
  have hinner : ∀ c d : Fin M, J.Adj c d → s(c, d) ≠ s(a, b) →
      ∀ (j : ℕ) (hj : j + 1 < (T c d).length), 0 < j → (T c d)[j]'(by omega) ∈ X := by
    intro c d hcd hne j hj h0
    rw [hXiff]
    exact hS.disj c d a b hcd hab hne _ (mem_interior_of_index hj h0)
  have hedge : ∀ c d : Fin M, J.Adj c d → c ≠ a → c ≠ b → d ≠ a → d ≠ b →
      RchIn H X (ι c) (ι d) := by
    intro c d hcd hca hcb hda hdb
    have hne : s(c, d) ≠ s(a, b) := by
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact hca h1
      · exact hcb h1
    refine rchIn_of_chain (T c d)
      (List.isChain_iff_getElem.mpr (hS.track c d hcd).1.2.2) ?_
      (List.mem_of_head? (hS.track c d hcd).2.1)
      (List.mem_of_getLast? (hS.track c d hcd).2.2)
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    by_cases h0 : j = 0
    · subst h0
      have : (T c d)[0]'hj = ι c :=
        SubdivisionCounting.track_head (hS.track c d hcd) hj
      rw [this]; exact hbase c hca hcb
    by_cases hlast : j + 1 = (T c d).length
    · have : (T c d)[j]'hj = ι d := by
        rw [SubdivisionCounting.getElem_eq_of_index_eq (T c d)
          (show j = (T c d).length - 1 by omega) hj (by omega)]
        exact DegenerateK4Tracks.track_getLast (hS.track c d hcd) (by omega)
      rw [this]; exact hbase d hda hdb
    · exact hinner c d hcd hne j (by omega) (by omega)
  -- any two surviving images are joined inside `X`
  have hall : ∀ p r : Fin M, p ≠ a → p ≠ b → r ≠ a → r ≠ b → RchIn H X (ι p) (ι r) := by
    intro p r hpa hpb hra hrb
    have hcard : ({a, b} : Set (Fin M)).ncard < 3 := by
      have h1 := Set.ncard_insert_le a ({b} : Set (Fin M))
      have h2 : ({b} : Set (Fin M)).ncard = 1 := Set.ncard_singleton b
      omega
    have hc := hJ.2 _ hcard
    have hpm : p ∈ ((({a, b} : Set (Fin M)))ᶜ) := by
      rintro (h | h)
      · exact hpa h
      · exact hpb h
    have hrm : r ∈ ((({a, b} : Set (Fin M)))ᶜ) := by
      rintro (h | h)
      · exact hra h
      · exact hrb h
    obtain ⟨wk⟩ := hc.preconnected ⟨p, hpm⟩ ⟨r, hrm⟩
    exact rchIn_of_walk (H := H) (X := X)
      (fun c : ↥((({a, b} : Set (Fin M)))ᶜ) => ι (c : Fin M))
      (fun c => hbase _ (fun h => c.2 (Or.inl h)) (fun h => c.2 (Or.inr h)))
      (fun c d hcd => hedge c.1 d.1 hcd (fun h => c.2 (Or.inl h)) (fun h => c.2 (Or.inr h))
        (fun h => d.2 (Or.inl h)) (fun h => d.2 (Or.inr h))) wk
  -- every surviving vertex reaches a surviving image
  have hreach : ∀ z ∈ X, ∃ c : Fin M, c ≠ a ∧ c ≠ b ∧ RchIn H X z (ι c) := by
    intro z hz
    rcases hS.cover z with ⟨c, rfl⟩ | ⟨c, d, hcd, hint⟩
    · have hca : c ≠ a := by rintro rfl; exact (hXiff _).mp hz hTa
      have hcb : c ≠ b := by rintro rfl; exact (hXiff _).mp hz hTb
      exact ⟨c, hca, hcb, RchIn.refl hz⟩
    · have hzT : z ∈ T c d := SubdivisionCompose.mem_of_mem_trackInterior hint
      have hne : s(c, d) ≠ s(a, b) := by
        intro hc
        refine (hXiff z).mp hz ?_
        rcases Sym2.eq_iff.mp hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at hzT
          exact hzT
        · rw [h1, h2, hS.rev a b hab] at hzT
          exact List.mem_reverse.mp hzT
      obtain ⟨k, hk2, hkz⟩ := (SubdivisionCounting.mem_trackInterior_iff (T c d) z).mp hint
      have hchain : List.IsChain H.Adj (T c d) :=
        List.isChain_iff_getElem.mpr (hS.track c d hcd).1.2.2
      by_cases hcok : c ≠ a ∧ c ≠ b
      · refine ⟨c, hcok.1, hcok.2, ?_⟩
        refine rchIn_of_chain ((T c d).take (k + 2)) (hchain.take _) ?_ ?_ ?_
        · intro y hy
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
          rw [List.length_take] at hj
          rw [List.getElem_take]
          by_cases h0 : j = 0
          · subst h0
            have hc0 : (T c d)[0]'(by omega) = ι c :=
              SubdivisionCounting.track_head (hS.track c d hcd) (by omega)
            rw [hc0]; exact hbase c hcok.1 hcok.2
          · exact hinner c d hcd hne j (by omega) (by omega)
        · have hlen : k + 1 < ((T c d).take (k + 2)).length := by
            rw [List.length_take]; omega
          have h0 : ((T c d).take (k + 2))[k + 1]'hlen = (T c d)[k + 1]'(by omega) := by
            rw [List.getElem_take]
          rw [← hkz, ← h0]
          exact List.getElem_mem _
        · have hlen0 : 0 < ((T c d).take (k + 2)).length := by
            rw [List.length_take]; omega
          have h0 : ((T c d).take (k + 2))[0]'hlen0 = (T c d)[0]'(by omega) := by
            rw [List.getElem_take]
          have hc0 : (T c d)[0]'(by omega) = ι c :=
            SubdivisionCounting.track_head (hS.track c d hcd) (by omega)
          rw [← hc0, ← h0]
          exact List.getElem_mem _
      · have hc' : c = a ∨ c = b := by
          by_contra hcon
          push_neg at hcon
          exact hcok ⟨hcon.1, hcon.2⟩
        have hda : d ≠ a := by
          intro hda
          rcases hc' with h | h
          · exact hcd.ne (h.trans hda.symm)
          · exact hne (by rw [h, hda, Sym2.eq_swap])
        have hdb : d ≠ b := by
          intro hdb
          rcases hc' with h | h
          · exact hne (by rw [h, hdb])
          · exact hcd.ne (h.trans hdb.symm)
        refine ⟨d, hda, hdb, ?_⟩
        refine rchIn_of_chain ((T c d).drop (k + 1)) (hchain.drop _) ?_ ?_ ?_
        · intro y hy
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
          rw [List.length_drop] at hj
          rw [List.getElem_drop]
          by_cases hlast : (k + 1 + j) + 1 = (T c d).length
          · have hdl : (T c d)[k + 1 + j]'(by omega) = ι d := by
              rw [SubdivisionCounting.getElem_eq_of_index_eq (T c d)
                (show k + 1 + j = (T c d).length - 1 by omega) (by omega) (by omega)]
              exact DegenerateK4Tracks.track_getLast (hS.track c d hcd) (by omega)
            rw [hdl]; exact hbase d hda hdb
          · exact hinner c d hcd hne (k + 1 + j) (by omega) (by omega)
        · have hlen0 : 0 < ((T c d).drop (k + 1)).length := by
            rw [List.length_drop]; omega
          have h0 : ((T c d).drop (k + 1))[0]'hlen0 = (T c d)[k + 1 + 0]'(by omega) := by
            rw [List.getElem_drop]
          have h1 : (T c d)[k + 1 + 0]'(by omega) = (T c d)[k + 1]'(by omega) :=
            SubdivisionCounting.getElem_eq_of_index_eq (T c d) (by omega) (by omega) (by omega)
          rw [← hkz, ← h1, ← h0]
          exact List.getElem_mem _
        · have hlen : (T c d).length - 1 - (k + 1) < ((T c d).drop (k + 1)).length := by
            rw [List.length_drop]; omega
          have h0 : ((T c d).drop (k + 1))[(T c d).length - 1 - (k + 1)]'hlen
              = (T c d)[k + 1 + ((T c d).length - 1 - (k + 1))]'(by omega) := by
            rw [List.getElem_drop]
          have h1 : (T c d)[k + 1 + ((T c d).length - 1 - (k + 1))]'(by omega)
              = (T c d)[(T c d).length - 1]'(by omega) :=
            SubdivisionCounting.getElem_eq_of_index_eq (T c d) (by omega) (by omega) (by omega)
          have hdl : (T c d)[(T c d).length - 1]'(by omega) = ι d :=
            DegenerateK4Tracks.track_getLast (hS.track c d hcd) (by omega)
          rw [← hdl, ← h1, ← h0]
          exact List.getElem_mem _
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  obtain ⟨c, hca, hcb, hrc⟩ := hreach u hu
  obtain ⟨d, hda, hdb, hrd⟩ := hreach v hv
  obtain ⟨h1, h2, hr⟩ :=
    (hrc.trans (hall c d hca hcb hda hdb)).trans hrd.symm
  exact hr

end Workspace.ProofLemmas.Thm58StarStarGapBranchConn
