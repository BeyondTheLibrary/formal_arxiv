import Workspace.ProofLemmas.Connectivity58ThreeTracks
import Workspace.ProofLemmas.TrackGlueAtCommonEndpoint
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism

/-!
# The three extended tracks of 5.8 (6)

PAPER (proof of 5.8 (6), printed p. 28): *"Hence in `L(H)` there are three vertex-disjoint
paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to `N_w`, and there are no edges between
them except in the triangle `T` formed by their ends in `N_w`."*

`Connectivity58ThreeTracks.exists_three_tracks` gives the three tracks of `H` out of `w`: the
two arcs of the return track `D` and the minimal track back to the star vertex `c`.  The paper
then walks the first two paths further, along the branch between `v₁` and `v₂`, until they
reach the neighbours of the vertex that is to be linked.  This file glues the corresponding
pieces of the branch onto the two arcs, so that the three *paths* of the sentence above are
again plain rungs of three tracks of `H` meeting only at `w`.

`α` and `β` below are the two places where the branch is cut: the first extended track ends at
`q[α]`, the second at `q[β]`, and `α < β` is what keeps the two extensions apart.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchLinkTracks

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism

variable {W : Type*} [DecidableEq W] {H : SimpleGraph W}

/-! ### Gluing two tracks at a common end -/

/-- Every edge of a glued track is an edge of one of the two pieces. -/
theorem trackEdges_append_tail_subset {A B : List W} (hA : A ≠ [])
    (hglue : A.getLast? = B.head?) :
    trackEdges (A ++ B.tail) ⊆ trackEdges A ∪ trackEdges B := by
  rintro e ⟨t, ht, rfl⟩
  have hAlen : 0 < A.length := List.length_pos_of_ne_nil hA
  have hlen : (A ++ B.tail).length = A.length + B.length - 1 := by
    cases B with
    | nil => simp at hglue; exact absurd hglue hA
    | cons b bs => simp
  by_cases h1 : t + 1 < A.length
  · left
    refine ⟨t, h1, ?_⟩
    rw [List.getElem_append_left (by omega), List.getElem_append_left h1]
  · right
    -- `B` has at least two entries here
    have hBlen : 2 ≤ B.length := by rw [hlen] at ht; omega
    have hB0 : B[0]'(by omega) = A[A.length - 1]'(by omega) := by
      have h1 : A.getLast? = some (A[A.length - 1]'(by omega)) := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      have h2 : B.head? = some (B[0]'(by omega)) := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      rw [h1, h2] at hglue
      exact (Option.some_injective _ hglue).symm
    have hBtail : ∀ (j : ℕ) (hj : j < B.tail.length),
        B.tail[j]'hj = B[j + 1]'(by simp at hj; omega) := by
      intro j hj
      simp only [List.getElem_tail]
    by_cases h2 : t < A.length
    · -- the junction edge
      have htA : t = A.length - 1 := by omega
      refine ⟨0, by omega, ?_⟩
      have e1 : (A ++ B.tail)[t]'(by omega) = B[0]'(by omega) := by
        rw [List.getElem_append_left h2, hB0]
        congr 1
      have e2 : (A ++ B.tail)[t + 1]'ht = B[1]'(by omega) := by
        rw [List.getElem_append_right (by omega)]
        rw [hBtail _ (by simp; omega)]
        congr 1
        omega
      rw [e1, e2]
    · push_neg at h2
      refine ⟨t - A.length + 1, by rw [hlen] at ht; omega, ?_⟩
      have e1 : (A ++ B.tail)[t]'(by omega) = B[t - A.length + 1]'(by rw [hlen] at ht; omega) := by
        rw [List.getElem_append_right h2, hBtail _ (by simp; omega)]
      have e2 : (A ++ B.tail)[t + 1]'ht
          = B[t - A.length + 1 + 1]'(by rw [hlen] at ht; omega) := by
        rw [List.getElem_append_right (by omega), hBtail _ (by simp; omega)]
        congr 1
        omega
      rw [e1, e2]

/-- The first edge of a glued track is the first edge of the first piece. -/
theorem firstTrackEdge_append_tail {A B : List W} (h2 : 2 ≤ A.length)
    (h2' : 2 ≤ (A ++ B.tail).length) :
    firstTrackEdge (A ++ B.tail) h2' = firstTrackEdge A h2 := by
  simp only [firstTrackEdge]
  rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]

/-! ### The three extended tracks -/

open Workspace.ProofLemmas.TrackSlice in
/-- **The three tracks of the first two sentences of 5.8 (6), walked out along the branch.**

`S 0` runs from `w` along the return track `D` to `v₁` and then along the branch to `q[α]`;
`S 1` runs from `w` along `D` to `v₂` and then back along the branch to `q[β]`; `S 2` is the
minimal track from `w` to the star vertex `c`.  Since `α < β`, the two branch pieces are
disjoint, so the three tracks still meet only at `w`. -/
theorem exists_extended_tracks
    {D q Sm : List W} {v₁ v₂ c w : W} {k α β : ℕ}
    (hD : IsTrackFrom H D v₁ v₂) (hq : IsTrackFrom H q v₁ v₂)
    (hk0 : 0 < k) (hklt : k + 1 < D.length) (hkw : D[k]? = some w)
    (hDq : ∀ z ∈ D, z ∈ q → z = v₁ ∨ z = v₂)
    (hSm : IsTrackFrom H Sm c w) (hSm2 : 2 ≤ Sm.length)
    (hSmD : ∀ x ∈ Sm, x ∈ D → x = w) (hSmq : ∀ x ∈ Sm, x ∉ q)
    (hαβ : α < β) (hβ : β < q.length) :
    ∃ (b : Fin 3 → W) (S : Fin 3 → List W) (hS : ∀ i, IsTrackFrom H (S i) w (b i))
      (hlen : ∀ i, 2 ≤ (S i).length),
      b 0 = q[α]'(by omega) ∧ b 1 = q[β]'hβ ∧ b 2 = c ∧
      (∀ i j : Fin 3, i ≠ j → ∀ z ∈ S i, z ∈ S j → z = w) ∧
      (∀ z ∈ S 0, z ∈ D ∨ z ∈ slice q 0 α) ∧
      (∀ z ∈ S 1, z ∈ D ∨ z ∈ slice q β (q.length - 1)) ∧
      (∀ z ∈ S 2, z ∈ Sm) ∧ v₂ ∉ S 0 ∧ v₁ ∉ S 1 ∧
      (∃ z₀ ∈ D, firstTrackEdge (S 0) (hlen 0) = s(w, z₀) ∧ (z₀ ∈ q → z₀ = v₁ ∧ H.Adj w v₁)) ∧
      (∃ z₁ ∈ D, firstTrackEdge (S 1) (hlen 1) = s(w, z₁) ∧ (z₁ ∈ q → z₁ = v₂ ∧ H.Adj w v₂)) ∧
      (∃ z₂ ∈ Sm, firstTrackEdge (S 2) (hlen 2) = s(w, z₂)) ∧
      (∀ h1 : 1 ≤ α, lastTrackEdge (S 0) (hlen 0)
          = s(q[α - 1]'(by omega), q[α]'(by omega))) ∧
      (∀ h1 : β + 1 < q.length, lastTrackEdge (S 1) (hlen 1)
          = s(q[β + 1]'h1, q[β]'hβ)) ∧ S 2 = Sm.reverse := by
  classical
  have hqlen : 2 ≤ q.length := by omega
  have hDpos : 0 < D.length := by omega
  have hDk : D[k]'(by omega) = w := by
    rw [List.getElem?_eq_getElem (by omega : k < D.length)] at hkw
    exact Option.some_injective _ hkw
  have hD0 : D[0]'hDpos = v₁ := by
    have h := hD.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hDpos] at h
    exact Option.some_injective _ h
  have hDl : D[D.length - 1]'(by omega) = v₂ := by
    have h := hD.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have hq0 : q[0]'(by omega) = v₁ := by
    have h := hq.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have hql : q[q.length - 1]'(by omega) = v₂ := by
    have h := hq.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have hwv1 : w ≠ v₁ := by
    intro hc
    have : k = 0 := hD.1.2.1.getElem_inj_iff.mp (by rw [hDk, hc, hD0])
    omega
  have hwv2 : w ≠ v₂ := by
    intro hc
    have : k = D.length - 1 := hD.1.2.1.getElem_inj_iff.mp (by rw [hDk, hc, hDl])
    omega
  have hwD : w ∈ D := by rw [← hDk]; exact List.getElem_mem _
  have hwq : w ∉ q := by
    intro hc
    rcases hDq w hwD hc with h | h
    · exact hwv1 h
    · exact hwv2 h
  obtain ⟨bb, SS, hbb0, hbb1, hbb2, htr, hln, hmt, hsub0, hsub1, hSS2⟩ :=
    Connectivity58ThreeTracks.exists_three_tracks hD hk0 hklt hkw hSm hSm2 hSmD
  have hend : ∀ i : Fin 3, bb i ∈ SS i := fun i =>
    List.mem_of_mem_getLast? (htr i).2.2
  have hSSm : ∀ z ∈ SS 2, z ∈ Sm := by
    intro z hz
    rw [hSS2] at hz
    exact List.mem_reverse.mp hz
  have hv2S0 : v₂ ∉ SS 0 := by
    intro hc
    exact hwv2 (hmt 0 1 (by decide) v₂ hc (hbb1 ▸ hend 1)).symm
  have hv1S1 : v₁ ∉ SS 1 := by
    intro hc
    exact hwv1 (hmt 1 0 (by decide) v₁ hc (hbb0 ▸ hend 0)).symm
  have hB0 : IsTrackFrom H (TrackSlice.slice q 0 α) v₁ (q[α]'(by omega)) := by
    have h := TrackSlice.isTrackFrom_slice hq.1 (show α < q.length by omega)
      (show 0 ≤ α by omega)
    rwa [hq0] at h
  have hB1' : IsTrackFrom H (TrackSlice.slice q β (q.length - 1)) (q[β]'hβ) v₂ := by
    have h := TrackSlice.isTrackFrom_slice hq.1 (show q.length - 1 < q.length by omega)
      (show β ≤ q.length - 1 by omega)
    rwa [hql] at h
  have hB1 : IsTrackFrom H (TrackSlice.slice q β (q.length - 1)).reverse v₂ (q[β]'hβ) :=
    TrackSlice.isTrackFrom_reverse hB1'
  have hB0mem : ∀ z ∈ TrackSlice.slice q 0 α, z ∈ q := fun z hz => TrackSlice.mem_of_mem_slice hz
  have hB1mem : ∀ z ∈ (TrackSlice.slice q β (q.length - 1)).reverse, z ∈ q := fun z hz =>
    TrackSlice.mem_of_mem_slice (List.mem_reverse.mp hz)
  have hv2B0 : v₂ ∉ TrackSlice.slice q 0 α := by
    intro hc
    obtain ⟨t, ht, -, htα, htv⟩ :=
      (TrackSlice.mem_slice_iff (show α < q.length by omega) (show 0 ≤ α by omega)).mp hc
    have : t = q.length - 1 := hq.1.2.1.getElem_inj_iff.mp (by rw [htv, hql])
    omega
  have hv1B1 : v₁ ∉ (TrackSlice.slice q β (q.length - 1)).reverse := by
    intro hc
    obtain ⟨t, ht, hβt, -, htv⟩ :=
      (TrackSlice.mem_slice_iff (show q.length - 1 < q.length by omega)
        (show β ≤ q.length - 1 by omega)).mp (List.mem_reverse.mp hc)
    have : t = 0 := hq.1.2.1.getElem_inj_iff.mp (by rw [htv, hq0])
    omega
  have hB0B1 : ∀ z ∈ TrackSlice.slice q 0 α,
      z ∉ (TrackSlice.slice q β (q.length - 1)).reverse := by
    intro z hz hz'
    obtain ⟨t, ht, -, htα, htv⟩ :=
      (TrackSlice.mem_slice_iff (show α < q.length by omega) (show 0 ≤ α by omega)).mp hz
    obtain ⟨u, hu, hβu, -, huv⟩ :=
      (TrackSlice.mem_slice_iff (show q.length - 1 < q.length by omega)
        (show β ≤ q.length - 1 by omega)).mp (List.mem_reverse.mp hz')
    have : t = u := hq.1.2.1.getElem_inj_iff.mp (by rw [htv, huv])
    omega
  have hc0 : ∀ z : W, z ∈ SS 0 → z ∈ TrackSlice.slice q 0 α → z = v₁ := by
    intro z hz hz'
    rcases hDq z (hsub0 z hz) (hB0mem z hz') with h | h
    · exact h
    · exact absurd (h ▸ hz) hv2S0
  have hc1 : ∀ z : W, z ∈ SS 1 → z ∈ (TrackSlice.slice q β (q.length - 1)).reverse → z = v₂ := by
    intro z hz hz'
    rcases hDq z (hsub1 z hz) (hB1mem z hz') with h | h
    · exact absurd (h ▸ hz) hv1S1
    · exact h
  obtain ⟨hg0, hm0⟩ := TrackGlueAtCommonEndpoint H (SS 0) (TrackSlice.slice q 0 α) w v₁
    (q[α]'(by omega)) (hbb0 ▸ htr 0) hB0 hc0
  obtain ⟨hg1, hm1⟩ := TrackGlueAtCommonEndpoint H (SS 1)
    (TrackSlice.slice q β (q.length - 1)).reverse w v₂ (q[β]'hβ) (hbb1 ▸ htr 1) hB1 hc1
  refine ⟨![q[α]'(by omega), q[β]'hβ, c],
    ![SS 0 ++ (TrackSlice.slice q 0 α).tail,
      SS 1 ++ (TrackSlice.slice q β (q.length - 1)).reverse.tail, SS 2],
    ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hSS2⟩
  · intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hbb2 ▸ htr 2
  · intro i
    fin_cases i
    · show 2 ≤ (SS 0 ++ _).length
      rw [List.length_append]
      have := hln 0
      omega
    · show 2 ≤ (SS 1 ++ _).length
      rw [List.length_append]
      have := hln 1
      omega
    · exact hln 2
  · have key : ∀ z : W, z ∈ SS 0 ++ (TrackSlice.slice q 0 α).tail →
        z ∈ SS 1 ++ (TrackSlice.slice q β (q.length - 1)).reverse.tail → z = w := by
      intro z hz hz'
      rcases hm0 z hz with h | h <;> rcases hm1 z hz' with h' | h'
      · exact hmt 0 1 (by decide) z h h'
      · rcases hDq z (hsub0 z h) (hB1mem z h') with e | e
        · exact absurd (e ▸ h') hv1B1
        · exact absurd (e ▸ h) hv2S0
      · rcases hDq z (hsub1 z h') (hB0mem z h) with e | e
        · exact absurd (e ▸ h') hv1S1
        · exact absurd (e ▸ h) hv2B0
      · exact absurd h' (hB0B1 z h)
    have key2 : ∀ z : W, z ∈ SS 0 ++ (TrackSlice.slice q 0 α).tail → z ∈ SS 2 → z = w := by
      intro z hz hz'
      rcases hm0 z hz with h | h
      · exact hmt 0 2 (by decide) z h hz'
      · exact absurd (hB0mem z h) (hSmq z (hSSm z hz'))
    have key3 : ∀ z : W, z ∈ SS 1 ++ (TrackSlice.slice q β (q.length - 1)).reverse.tail →
        z ∈ SS 2 → z = w := by
      intro z hz hz'
      rcases hm1 z hz with h | h
      · exact hmt 1 2 (by decide) z h hz'
      · exact absurd (hB1mem z h) (hSmq z (hSSm z hz'))
    intro i j hij z hz hz'
    fin_cases i <;> fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hz hz' ⊢
    · exact absurd rfl hij
    · exact key z hz hz'
    · exact key2 z hz hz'
    · exact key z hz' hz
    · exact absurd rfl hij
    · exact key3 z hz hz'
    · exact key2 z hz' hz
    · exact key3 z hz' hz
    · exact absurd rfl hij
  · intro z hz
    exact (hm0 z hz).imp (fun h => hsub0 z h) id
  · intro z hz
    exact (hm1 z hz).imp (fun h => hsub1 z h) (fun h => List.mem_reverse.mp h)
  · intro z hz
    exact hSSm z hz
  · intro hc
    rcases hm0 v₂ hc with h | h
    · exact hv2S0 h
    · exact hv2B0 h
  · intro hc
    rcases hm1 v₁ hc with h | h
    · exact hv1S1 h
    · exact hv1B1 h
  · have h0 : (SS 0)[0]'(by have := hln 0; omega) = w := by
      have h := (htr 0).2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by have := hln 0; omega)] at h
      exact Option.some_injective _ h
    refine ⟨(SS 0)[1]'(by have := hln 0; omega), hsub0 _ (List.getElem_mem _), ?_, ?_⟩
    · show firstTrackEdge (SS 0 ++ (TrackSlice.slice q 0 α).tail) _ = _
      rw [firstTrackEdge_append_tail (by have := hln 0; omega)]
      simp only [firstTrackEdge]
      rw [h0]
    · intro hz
      rcases hDq _ (hsub0 _ (List.getElem_mem _)) hz with e | e
      · refine ⟨e, ?_⟩
        have hadj := (htr 0).1.2.2 0 (by have := hln 0; omega)
        rw [h0, e] at hadj
        exact hadj
      · exact absurd (show v₂ ∈ SS 0 by rw [← e]; exact List.getElem_mem _) hv2S0
  · have h0 : (SS 1)[0]'(by have := hln 1; omega) = w := by
      have h := (htr 1).2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by have := hln 1; omega)] at h
      exact Option.some_injective _ h
    refine ⟨(SS 1)[1]'(by have := hln 1; omega), hsub1 _ (List.getElem_mem _), ?_, ?_⟩
    · show firstTrackEdge (SS 1 ++ (TrackSlice.slice q β (q.length - 1)).reverse.tail) _ = _
      rw [firstTrackEdge_append_tail (by have := hln 1; omega)]
      simp only [firstTrackEdge]
      rw [h0]
    · intro hz
      rcases hDq _ (hsub1 _ (List.getElem_mem _)) hz with e | e
      · exact absurd (show v₁ ∈ SS 1 by rw [← e]; exact List.getElem_mem _) hv1S1
      · refine ⟨e, ?_⟩
        have hadj := (htr 1).1.2.2 0 (by have := hln 1; omega)
        rw [h0, e] at hadj
        exact hadj
  · have h0 : (SS 2)[0]'(by have := hln 2; omega) = w := by
      have h := (htr 2).2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by have := hln 2; omega)] at h
      exact Option.some_injective _ h
    refine ⟨(SS 2)[1]'(by have := hln 2; omega), ?_, ?_⟩
    · exact hSSm _ (List.getElem_mem _)
    · show firstTrackEdge (SS 2) _ = _
      simp only [firstTrackEdge]
      rw [h0]
  · intro h1
    have hsl : (TrackSlice.slice q 0 α).length = α - 0 + 1 :=
      TrackSlice.length_slice q (show α < q.length by omega) (show 0 ≤ α by omega)
    have hB0len : 2 ≤ (TrackSlice.slice q 0 α).length := by omega
    have hlen0 : 2 ≤ (SS 0 ++ (TrackSlice.slice q 0 α).tail).length := by
      rw [List.length_append]; have := hln 0; omega
    have hqα_notD : (q[α]'(by omega)) ∉ D := by
      intro hm
      rcases hDq _ hm (List.getElem_mem _) with e | e
      · have : α = 0 := hq.1.2.1.getElem_inj_iff.mp (by rw [e, hq0])
        omega
      · have : α = q.length - 1 := hq.1.2.1.getElem_inj_iff.mp (by rw [e, hql])
        omega
    have hglue : (SS 0).getLast? = (TrackSlice.slice q 0 α).head? := by
      have ht0 : IsTrackFrom H (SS 0) w v₁ := hbb0 ▸ htr 0
      rw [ht0.2.2, hB0.2.1]
    have hcontains : (q[α]'(by omega))
        ∈ lastTrackEdge (SS 0 ++ (TrackSlice.slice q 0 α).tail) hlen0 :=
      lastTrackEdge_contains hg0 hlen0
    show lastTrackEdge (SS 0 ++ (TrackSlice.slice q 0 α).tail) _ = _
    rcases trackEdges_append_tail_subset (A := SS 0) (B := TrackSlice.slice q 0 α)
        (htr 0).1.1 hglue (lastTrackEdge_mem_trackEdges hlen0) with hin | hin
    · exfalso
      obtain ⟨t, ht, het⟩ := hin
      apply hqα_notD
      rw [het] at hcontains
      rcases Sym2.mem_iff.mp hcontains with e | e
      · exact hsub0 _ (show (q[α]'(by omega)) ∈ SS 0 by rw [e]; exact List.getElem_mem _)
      · exact hsub0 _ (show (q[α]'(by omega)) ∈ SS 0 by rw [e]; exact List.getElem_mem _)
    · rw [edge_eq_lastTrackEdge hB0 hB0len hin hcontains]
      simp only [lastTrackEdge]
      have e1 : (TrackSlice.slice q 0 α)[(TrackSlice.slice q 0 α).length - 2]'(by omega)
          = q[α - 1]'(by omega) := by
        rw [TrackSlice.getElem_slice q (show (TrackSlice.slice q 0 α).length - 2 <
          (TrackSlice.slice q 0 α).length by omega)
          (show 0 + ((TrackSlice.slice q 0 α).length - 2) < q.length by omega)]
        exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
      have e2 : (TrackSlice.slice q 0 α)[(TrackSlice.slice q 0 α).length - 1]'(by omega)
          = q[α]'(by omega) := by
        rw [TrackSlice.getElem_slice q (show (TrackSlice.slice q 0 α).length - 1 <
          (TrackSlice.slice q 0 α).length by omega)
          (show 0 + ((TrackSlice.slice q 0 α).length - 1) < q.length by omega)]
        exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
      rw [e1, e2]
  · intro h1
    have hsl : (TrackSlice.slice q β (q.length - 1)).length = q.length - 1 - β + 1 :=
      TrackSlice.length_slice q (show q.length - 1 < q.length by omega)
        (show β ≤ q.length - 1 by omega)
    have hslr : (TrackSlice.slice q β (q.length - 1)).reverse.length = q.length - 1 - β + 1 := by
      rw [List.length_reverse]; exact hsl
    have hB1len : 2 ≤ (TrackSlice.slice q β (q.length - 1)).reverse.length := by omega
    have hlen1 : 2 ≤ (SS 1 ++ (TrackSlice.slice q β (q.length - 1)).reverse.tail).length := by
      rw [List.length_append]; have := hln 1; omega
    have hqβ_notD : (q[β]'hβ) ∉ D := by
      intro hm
      rcases hDq _ hm (List.getElem_mem _) with e | e
      · have : β = 0 := hq.1.2.1.getElem_inj_iff.mp (by rw [e, hq0])
        omega
      · have : β = q.length - 1 := hq.1.2.1.getElem_inj_iff.mp (by rw [e, hql])
        omega
    have hglue : (SS 1).getLast? = (TrackSlice.slice q β (q.length - 1)).reverse.head? := by
      have ht1 : IsTrackFrom H (SS 1) w v₂ := hbb1 ▸ htr 1
      rw [ht1.2.2, hB1.2.1]
    have hcontains : (q[β]'hβ)
        ∈ lastTrackEdge (SS 1 ++ (TrackSlice.slice q β (q.length - 1)).reverse.tail) hlen1 :=
      lastTrackEdge_contains hg1 hlen1
    show lastTrackEdge (SS 1 ++ (TrackSlice.slice q β (q.length - 1)).reverse.tail) _ = _
    rcases trackEdges_append_tail_subset (A := SS 1)
        (B := (TrackSlice.slice q β (q.length - 1)).reverse)
        (htr 1).1.1 hglue (lastTrackEdge_mem_trackEdges hlen1) with hin | hin
    · exfalso
      obtain ⟨t, ht, het⟩ := hin
      apply hqβ_notD
      rw [het] at hcontains
      rcases Sym2.mem_iff.mp hcontains with e | e
      · exact hsub1 _ (show (q[β]'hβ) ∈ SS 1 by rw [e]; exact List.getElem_mem _)
      · exact hsub1 _ (show (q[β]'hβ) ∈ SS 1 by rw [e]; exact List.getElem_mem _)
    · rw [edge_eq_lastTrackEdge hB1 hB1len hin hcontains]
      simp only [lastTrackEdge]
      have key : ∀ (t : ℕ) (ht : t < (TrackSlice.slice q β (q.length - 1)).reverse.length)
          (ht' : β + (q.length - β - 1 - t) < q.length),
          (TrackSlice.slice q β (q.length - 1)).reverse[t]'ht
            = q[β + (q.length - β - 1 - t)]'ht' := by
        intro t ht ht'
        rw [List.getElem_reverse]
        rw [TrackSlice.getElem_slice q (show (TrackSlice.slice q β (q.length - 1)).length - 1 - t
          < (TrackSlice.slice q β (q.length - 1)).length by omega)
          (show β + ((TrackSlice.slice q β (q.length - 1)).length - 1 - t) < q.length by omega)]
        exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
      have e1 := key ((TrackSlice.slice q β (q.length - 1)).reverse.length - 2) (by omega)
        (by omega)
      have e2 := key ((TrackSlice.slice q β (q.length - 1)).reverse.length - 1) (by omega)
        (by omega)
      rw [e1, e2]
      congr 1
      · exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _
      · exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _

end Workspace.ProofLemmas.Thm58StarBranchLinkTracks
