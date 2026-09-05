import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- Positional `T`-complete path edges and unordered `T`-complete path edges
are counted by the same finite set. -/
theorem PathCompleteEdgeIndexEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (T : Set V) (P : List V) (r s : V)
    (hP : IsPathFrom G P r s) :
    let completeEdgeIndices : Set ℕ :=
      {i | i + 1 < P.length ∧
        ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
          EdgeComplete G T u v}
    let completeEdges : Set (Sym2 V) :=
      {e | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G T u v}
    (∃ f : {i : ℕ // i ∈ completeEdgeIndices} ≃
        {e : Sym2 V // e ∈ completeEdges},
        ∀ i : {i : ℕ // i ∈ completeEdgeIndices},
          (f i).1 =
            s(P[i.1]'(by
              have hi : i.1 + 1 < P.length := by
                simpa only [Set.mem_setOf_eq] using i.2.1
              omega),
              P[i.1 + 1]'(by
                simpa only [Set.mem_setOf_eq] using i.2.1))) ∧
      completeEdgeIndices.ncard = completeEdges.ncard ∧
      (0 < completeEdgeIndices.ncard →
        ∃ u ∈ P, ∃ v ∈ P, EdgeComplete G T u v) := by
  classical
  intro CEI CE
  have hmemCEI : ∀ i : ℕ, i ∈ CEI ↔ (i + 1 < P.length ∧
      ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
        EdgeComplete G T u v) := fun _ => Iff.rfl
  have hmemCE : ∀ e : Sym2 V, e ∈ CE ↔
      ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G T u v := fun _ => Iff.rfl
  obtain ⟨hpath, hhead, hlast⟩ := hP
  have hnd : P.Nodup := hpath.2.1
  have hadj := hpath.2.2
  -- The total map on `ℕ` sending `i` to the unordered pair `{P i, P (i+1)}`.
  set F : ℕ → Sym2 V := fun i => s(P.getD i r, P.getD (i + 1) r) with hFdef
  have hFval : ∀ (i : ℕ) (h : i + 1 < P.length),
      F i = s(P[i]'(by omega), P[i + 1]'h) := by
    intro i h
    simp only [hFdef]
    rw [List.getD_eq_getElem P r (show i < P.length by omega),
      List.getD_eq_getElem P r h]
  have hBij : Set.BijOn F CEI CE := by
    refine ⟨?_, ?_, ?_⟩
    · -- maps to
      intro i hi
      obtain ⟨hi1, u, v, hu, hv, hE⟩ := (hmemCEI i).mp hi
      have hui : i < P.length := by omega
      have hu' : u = P[i]'hui := by
        rw [List.getElem?_eq_getElem hui] at hu
        exact (Option.some_injective _ hu).symm
      have hv' : v = P[i + 1]'hi1 := by
        rw [List.getElem?_eq_getElem hi1] at hv
        exact (Option.some_injective _ hv).symm
      refine (hmemCE _).mpr ⟨u, ?_, v, ?_, ?_, hE⟩
      · rw [hu']; exact List.getElem_mem hui
      · rw [hv']; exact List.getElem_mem hi1
      · rw [hFval i hi1, hu', hv']
    · -- injective on
      intro i hi j hj hij
      obtain ⟨hi1, -⟩ := (hmemCEI i).mp hi
      obtain ⟨hj1, -⟩ := (hmemCEI j).mp hj
      rw [hFval i hi1, hFval j hj1] at hij
      rcases Sym2.eq_iff.mp hij with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact (List.Nodup.getElem_inj_iff hnd).mp h1
      · have e1 : i = j + 1 := (List.Nodup.getElem_inj_iff hnd).mp h1
        have e2 : i + 1 = j := (List.Nodup.getElem_inj_iff hnd).mp h2
        omega
    · -- surjective on
      intro e he
      obtain ⟨u, hu, v, hv, rfl, hE⟩ := (hmemCE e).mp he
      obtain ⟨a, ha, hau⟩ := List.mem_iff_getElem.mp hu
      obtain ⟨b, hb, hbv⟩ := List.mem_iff_getElem.mp hv
      have hAdj : G.Adj (P[a]'ha) (P[b]'hb) := by rw [hau, hbv]; exact hE.1
      rcases (hadj a b ha hb).mp hAdj with hab | hab
      · -- b = a + 1
        subst hab
        refine ⟨a, ?_, ?_⟩
        · refine (hmemCEI a).mpr ⟨hb, u, v, ?_, ?_, hE⟩
          · rw [List.getElem?_eq_getElem ha, hau]
          · rw [List.getElem?_eq_getElem hb, hbv]
        · rw [hFval a hb, hau, hbv]
      · -- a = b + 1
        subst hab
        refine ⟨b, ?_, ?_⟩
        · refine (hmemCEI b).mpr ⟨ha, v, u, ?_, ?_, ?_⟩
          · rw [List.getElem?_eq_getElem hb, hbv]
          · rw [List.getElem?_eq_getElem ha, hau]
          · exact ⟨hE.1.symm, hE.2.2, hE.2.1⟩
        · rw [hFval b ha, hau, hbv, Sym2.eq_swap]
  refine ⟨⟨Set.BijOn.equiv F hBij, ?_⟩, ?_, ?_⟩
  · intro i
    have hi1 : i.1 + 1 < P.length := ((hmemCEI i.1).mp i.2).1
    show F i.1 = _
    rw [hFval i.1 hi1]
  · have himg : F '' CEI = CE := hBij.image_eq
    rw [← himg, Set.ncard_image_of_injOn hBij.injOn]
  · intro hpos
    have hne : CEI.Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      rw [hcon] at hpos
      simp at hpos
    obtain ⟨i, hi⟩ := hne
    obtain ⟨hi1, u, v, hu, hv, hE⟩ := (hmemCEI i).mp hi
    have hui : i < P.length := by omega
    have hu' : u = P[i]'hui := by
      rw [List.getElem?_eq_getElem hui] at hu
      exact (Option.some_injective _ hu).symm
    have hv' : v = P[i + 1]'hi1 := by
      rw [List.getElem?_eq_getElem hi1] at hv
      exact (Option.some_injective _ hv).symm
    refine ⟨u, ?_, v, ?_, hE⟩
    · rw [hu']; exact List.getElem_mem hui
    · rw [hv']; exact List.getElem_mem hi1

end Workspace.ProofLemmas
