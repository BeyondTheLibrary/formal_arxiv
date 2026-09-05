import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm75BranchEnds

/-!
# Helpers for the final sentence of 5.7

The paper derives the final sentence by counting the branch-vertices incident with two edges
of `X` in each of alternatives 2--5.  This module supplies that count.  The elementary facts
about edges of a track are kept here so the frozen theorem file only needs the final assembly.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57FinalHelpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

private theorem mem_of_mem_trackEdges {q : List W} {e : Sym2 W}
    (he : e ∈ trackEdges q) {w : W} (hw : w ∈ e) : w ∈ q := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

private theorem sym2_eq_of_mem_of_mem {a b : W} {e : Sym2 W}
    (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) : e = s(a, b) := by
  exact (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩

private theorem mem_trackInterior_of_two_edges {q : List W} (hnd : q.Nodup)
    {e f : Sym2 W} (hef : e ≠ f) (he : e ∈ trackEdges q) (hf : f ∈ trackEdges q)
    {b : W} (hbe : b ∈ e) (hbf : b ∈ f) : b ∈ trackInterior q := by
  obtain ⟨i, hi, rfl⟩ := he
  obtain ⟨j, hj, rfl⟩ := hf
  rw [Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff]
  rcases Sym2.mem_iff.mp hbe with h1 | h1 <;> rcases Sym2.mem_iff.mp hbf with h2 | h2
  · exfalso
    have hij : i = j := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    subst hij
    exact hef rfl
  · have hij : i = j + 1 := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    exact ⟨j, by omega, h2.symm⟩
  · have hij : i + 1 = j := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    exact ⟨i, by omega, h1.symm⟩
  · exfalso
    have hij : i + 1 = j + 1 := (hnd.getElem_inj_iff).mp (h1.symm.trans h2)
    have : i = j := by omega
    subst this
    exact hef rfl

private theorem branch_vertex_on_edge_is_end {H : SimpleGraph W} {q : List W} {b₁ b₂ b : W}
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q b₁ b₂)
    (hb : b ∈ branchVertices H) {e : Sym2 W} (he : e ∈ trackEdges q) (hbe : b ∈ e) :
    b = b₁ ∨ b = b₂ := by
  have hbq : b ∈ q := mem_of_mem_trackEdges he hbe
  have hbnot : b ∉ trackInterior q := fun hbin => hq.2.1 b hbin hb
  exact Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
    hfrom.2.1 hfrom.2.2 hbq hbnot

private theorem trackEdges_of_length_two {q : List W} (h2 : q.length = 2) {e : Sym2 W}
    (he : e ∈ trackEdges q) : e = s(q[0]'(by omega), q[1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  rw [h2] at hi
  have : i = 0 := by omega
  subst this
  rfl

private theorem head_getElem {l : List W} {a : W} (h : l.head? = some a)
    (h0 : 0 < l.length) : l[0]'h0 = a := by
  cases l with
  | nil => simp at h0
  | cons x t => simp only [List.head?_cons, Option.some.injEq] at h; simpa using h

private theorem last_getElem {l : List W} {b : W} (h : l.getLast? = some b)
    (h0 : 0 < l.length) : l[l.length - 1]'(by omega) = b := by
  have hne : l ≠ [] := by intro hc; subst hc; simp at h0
  have h1 := List.getLast?_eq_some_getLast hne
  rw [h] at h1
  have h2 : b = l.getLast hne := Option.some_injective _ h1
  rw [h2]
  exact (List.getLast_eq_getElem hne).symm

private theorem big_subset_of_stmt2 (H : SimpleGraph W) (X : Set (Sym2 W))
    {b : W} (hX : X ⊆ incidentEdges H b) : BigBranchVertices H X ⊆ {b} := by
  intro c hc
  by_contra hcb
  have hcb' : c ≠ b := by simpa using hcb
  obtain ⟨e, he, f, hf, hef⟩ := hc.2
  have heq : e = s(c, b) := sym2_eq_of_mem_of_mem he.1.2 (hX he.2).2 hcb'
  have hfq : f = s(c, b) := sym2_eq_of_mem_of_mem hf.1.2 (hX hf.2).2 hcb'
  exact hef (heq.trans hfq.symm)

private theorem big_subset_of_stmt3 (H : SimpleGraph W) (X : Set (Sym2 W))
    {q : List W} (hq : IsBranch H q) (hX : X ⊆ trackEdges q) :
    BigBranchVertices H X ⊆ ∅ := by
  intro c hc
  obtain ⟨e, he, f, hf, hef⟩ := hc.2
  have hcint := mem_trackInterior_of_two_edges hq.1.2.1 hef
    (hX he.2) (hX hf.2) he.1.2 hf.1.2
  exact (hq.2.1 c hcint) hc.1

private theorem edge_category_stmt4 (H : SimpleGraph W) (X : Set (Sym2 W))
    {q : List W} {b₁ : W}
    (hEq : X \ trackEdges q = incidentEdges H b₁ \ trackEdges q)
    {e : Sym2 W} (heX : e ∈ X) :
    e ∈ trackEdges q ∨ (e ∈ incidentEdges H b₁ ∧ e ∉ trackEdges q) := by
  by_cases heq : e ∈ trackEdges q
  · exact Or.inl heq
  · right
    have he : e ∈ X \ trackEdges q := ⟨heX, heq⟩
    rw [hEq] at he
    exact he

private theorem big_subset_of_stmt4 (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    {q : List W} {b₁ b₂ : W} (hq : IsBranch H q) (hfrom : IsTrackFrom H q b₁ b₂)
    (hEq : X \ trackEdges q = incidentEdges H b₁ \ trackEdges q) :
    BigBranchVertices H X ⊆ {b₁} := by
  intro c hc
  by_contra hcb
  have hcb' : c ≠ b₁ := by simpa using hcb
  obtain ⟨e, he, f, hf, hef⟩ := hc.2
  have hecat := edge_category_stmt4 H X hEq he.2
  have hfcat := edge_category_stmt4 H X hEq hf.2
  have honoff : ∃ eon eoff : Sym2 W,
      eon ∈ trackEdges q ∧ c ∈ eon ∧ eoff ∈ X ∧
      c ∈ eoff ∧ eoff ∈ incidentEdges H b₁ ∧ eoff ∉ trackEdges q := by
    rcases hecat with heB | heO <;> rcases hfcat with hfB | hfO
    · exact False.elim ((hq.2.1 c
        (mem_trackInterior_of_two_edges hq.1.2.1 hef heB hfB he.1.2 hf.1.2)) hc.1)
    · exact ⟨e, f, heB, he.1.2, hf.2, hf.1.2, hfO.1, hfO.2⟩
    · exact ⟨f, e, hfB, hf.1.2, he.2, he.1.2, heO.1, heO.2⟩
    · have heq : e = s(c, b₁) :=
        sym2_eq_of_mem_of_mem he.1.2 heO.1.2 hcb'
      have hfq : f = s(c, b₁) :=
        sym2_eq_of_mem_of_mem hf.1.2 hfO.1.2 hcb'
      exact False.elim (hef (heq.trans hfq.symm))
  obtain ⟨eon, eoff, heon, hceon, heoffX, hceoff, heoff, heoffnot⟩ := honoff
  have hcend := branch_vertex_on_edge_is_end hq hfrom hc.1 heon hceon
  have hcb2 : c = b₂ := hcend.resolve_left hcb'
  have heoffEq : eoff = s(b₁, b₂) := by
    apply sym2_eq_of_mem_of_mem heoff.2
    · rw [← hcb2]
      exact hceoff
    · intro h
      exact hcb' (hcb2.trans h.symm)
  have hadj : H.Adj b₁ b₂ := by
    apply H.mem_edgeSet.mp
    rw [← heoffEq]
    exact hXE heoffX
  by_cases hlen : 2 ≤ trackLength q
  · obtain ⟨n, J, hJ, hsub⟩ := hc3
    exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
      J hJ H hsub q b₁ b₂ hq hfrom hlen).2.2.2 hadj
  · have hqedge : 2 ≤ q.length := by
      obtain ⟨i, hi, -⟩ := heon
      omega
    have hq2 : q.length = 2 := by
      simp only [trackLength] at hlen
      omega
    have heonEq := trackEdges_of_length_two hq2 heon
    have h0 : q[0]'(by omega) = b₁ := head_getElem hfrom.2.1 (by omega)
    have h1 : q[1]'(by omega) = b₂ := by
      have hl := last_getElem hfrom.2.2 (by omega)
      exact (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
        (show 1 = q.length - 1 by omega) (by omega) (by omega)).trans hl
    rw [h0, h1, ← heoffEq] at heonEq
    exact heoffnot (heonEq ▸ heon)

private theorem edge_category_stmt5 (H : SimpleGraph W) (X : Set (Sym2 W))
    {q : List W} {b₁ b₂ : W}
    (hEq : X \ trackEdges q =
      (incidentEdges H b₁ ∪ incidentEdges H b₂) \ trackEdges q)
    {e : Sym2 W} (heX : e ∈ X) :
    e ∈ trackEdges q ∨
      ((e ∈ incidentEdges H b₁ ∨ e ∈ incidentEdges H b₂) ∧ e ∉ trackEdges q) := by
  by_cases heq : e ∈ trackEdges q
  · exact Or.inl heq
  · right
    have he : e ∈ X \ trackEdges q := ⟨heX, heq⟩
    rw [hEq] at he
    exact he

private theorem big_subset_of_stmt5 (H : SimpleGraph W) (hbip : H.IsBipartite)
    (X : Set (Sym2 W)) {q : List W} {b₁ b₂ : W}
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q b₁ b₂)
    (hodd : Odd (trackLength q))
    (hEq : X \ trackEdges q =
      (incidentEdges H b₁ ∪ incidentEdges H b₂) \ trackEdges q) :
    BigBranchVertices H X ⊆ {b₁, b₂} := by
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
  have hnotEven : ¬ Even (trackLength q) := Nat.not_even_iff_odd.mpr hodd
  have hcolne : col b₁ ≠ col b₂ := by
    intro hsame
    exact hnotEven
      ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom).mpr hsame)
  intro c hc
  by_contra hcends
  have hcne : c ≠ b₁ ∧ c ≠ b₂ := by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hcends
  obtain ⟨e, he, f, hf, hef⟩ := hc.2
  have hecat := edge_category_stmt5 H X hEq he.2
  have hfcat := edge_category_stmt5 H X hEq hf.2
  have heoff : (e ∈ incidentEdges H b₁ ∨ e ∈ incidentEdges H b₂) := by
    rcases hecat with heB | heO
    · rcases branch_vertex_on_edge_is_end hq hfrom hc.1 heB he.1.2 with h | h
      · exact False.elim (hcne.1 h)
      · exact False.elim (hcne.2 h)
    · exact heO.1
  have hfoff : (f ∈ incidentEdges H b₁ ∨ f ∈ incidentEdges H b₂) := by
    rcases hfcat with hfB | hfO
    · rcases branch_vertex_on_edge_is_end hq hfrom hc.1 hfB hf.1.2 with h | h
      · exact False.elim (hcne.1 h)
      · exact False.elim (hcne.2 h)
    · exact hfO.1
  have hadj1 : H.Adj c b₁ := by
    rcases heoff with he1 | he2
    · apply H.mem_edgeSet.mp
      have heq := sym2_eq_of_mem_of_mem he.1.2 he1.2 hcne.1
      rw [← heq]
      exact he.1.1
    · rcases hfoff with hf1 | hf2
      · apply H.mem_edgeSet.mp
        have hfq := sym2_eq_of_mem_of_mem hf.1.2 hf1.2 hcne.1
        rw [← hfq]
        exact hf.1.1
      · have heq := sym2_eq_of_mem_of_mem he.1.2 he2.2 hcne.2
        have hfq := sym2_eq_of_mem_of_mem hf.1.2 hf2.2 hcne.2
        exact False.elim (hef (heq.trans hfq.symm))
  have hadj2 : H.Adj c b₂ := by
    rcases heoff with he1 | he2
    · rcases hfoff with hf1 | hf2
      · have heq := sym2_eq_of_mem_of_mem he.1.2 he1.2 hcne.1
        have hfq := sym2_eq_of_mem_of_mem hf.1.2 hf1.2 hcne.1
        exact False.elim (hef (heq.trans hfq.symm))
      · apply H.mem_edgeSet.mp
        have hfq := sym2_eq_of_mem_of_mem hf.1.2 hf2.2 hcne.2
        rw [← hfq]
        exact hf.1.1
    · apply H.mem_edgeSet.mp
      have heq := sym2_eq_of_mem_of_mem he.1.2 he2.2 hcne.2
      rw [← heq]
      exact he.1.1
  have hkey : ∀ x y z : Bool, x ≠ y → x ≠ z → y = z := by decide
  exact hcolne (hkey (col c) (col b₁) (col b₂) (col.valid hadj1) (col.valid hadj2))

/-- The paper's final sentence follows from the six alternatives of 5.7. -/
theorem final_from_alternatives (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (h : Concl57 H X) : Concl57Final H X := by
  rcases h with h1 | h2 | h3 | h4 | h5 | h6
  · exact Or.inl (Or.inl h1)
  · right
    obtain ⟨b, hb, hX⟩ := h2
    have hsub := big_subset_of_stmt2 H X hX
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hcard
    refine ⟨by omega, ?_⟩
    intro htwo
    exfalso
    omega
  · right
    obtain ⟨q, hq, hX⟩ := h3
    have hsub := big_subset_of_stmt3 H X hq hX
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_empty] at hcard
    refine ⟨by omega, ?_⟩
    intro htwo
    exfalso
    omega
  · right
    obtain ⟨q, b₁, b₂, hq, hfrom, hEq⟩ := h4
    have hsub := big_subset_of_stmt4 H hc3 X hXE hq hfrom hEq
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_singleton] at hcard
    refine ⟨by omega, ?_⟩
    intro htwo
    exfalso
    omega
  · right
    obtain ⟨q, b₁, b₂, hq, hfrom, hodd, hEq⟩ := h5
    have hsub := big_subset_of_stmt5 H hbip X hq hfrom hodd hEq
    have hbne : b₁ ≠ b₂ := by
      obtain ⟨col⟩ :=
        Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
      have hnotEven : ¬ Even (trackLength q) := Nat.not_even_iff_odd.mpr hodd
      have hcolne : col b₁ ≠ col b₂ := fun hsame => hnotEven
        ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom).mpr hsame)
      exact fun heq => hcolne (congrArg col heq)
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hbne] at hcard
    exact ⟨hcard, fun _ => ⟨q, b₁, b₂, hq, hfrom, hodd, hEq⟩⟩
  · exact Or.inl (Or.inr h6)

end Workspace.ProofLemmas.Thm57FinalHelpers
