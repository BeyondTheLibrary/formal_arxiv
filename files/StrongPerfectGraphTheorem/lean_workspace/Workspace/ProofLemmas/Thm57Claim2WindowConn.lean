import Workspace.ProofLemmas.Thm57Claim2ConnCore

/-! # Deleting the window in 5.7 (2)

PAPER (printed p. 23): *"Since `c₁,c₂` belong to the same branch of `H` and `H` is cyclically
3-connected, it follows that there is a track in `H \ {c₁,c₂}` from `a₁` to `a₂`"*, and *"Let
`H'` be the graph obtained from `H` by deleting the internal vertices and edges of `C`"*.

Both statements have the same shape: the window `C` is a stretch of one branch `B`, so the
only vertices of `H` that see the inside of the window are its two ends.  Once at least one
of those two ends is deleted, an excursion into the window enters and leaves through the same
vertex and can be collapsed away (`window_transport`).  What remains is a statement about `H`
with two vertices deleted, which is 5.5.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2WindowConn

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.TrackSlice
open Workspace.ProofLemmas.Thm57Claim2DeletedWindow
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.Thm57Claim2ConnCore
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ### Reading the window off the branch -/

/-- A vertex of the window which is not internal to it is one of its two ends. -/
theorem end_of_mem_slice {B : List W} (hnd : B.Nodup) {i j : ℕ} (hij : i < j)
    (hj : j < B.length) {w : W} (hw : w ∈ slice B i j)
    (hint : w ∉ trackInterior (slice B i j)) : w = B[i]'(by omega) ∨ w = B[j]'hj := by
  obtain ⟨k, hk, hik, hkj, rfl⟩ := (mem_slice_iff hj (by omega)).mp hw
  rcases Nat.lt_or_ge i k with hlt | hle
  · rcases Nat.lt_or_ge k j with hlt' | hge
    · exact absurd ((mem_trackInterior_slice_iff hj (by omega)).mpr
        ⟨k, hk, hlt, hlt', rfl⟩) hint
    · exact Or.inr (getElem_eq_of_index_eq B (by omega) _ _)
  · exact Or.inl (getElem_eq_of_index_eq B (by omega) _ _)

/-- Both ends of an edge of the window lie on the window. -/
theorem mem_slice_of_mem_trackEdges {B : List W} {i j : ℕ} {e : Sym2 W}
    (he : e ∈ trackEdges (slice B i j)) {w : W} (hw : w ∈ e) : w ∈ slice B i j := by
  obtain ⟨k, hk, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

/-! ### Collapsing an excursion into the window -/

/-- **Transporting a connection past the window.**

If every end of the window that survives the deletion of `P` is the same vertex `w₀`, then a
walk of `H` avoiding `P` collapses to a walk avoiding the whole window, in the graph with the
window's edges deleted. -/
theorem window_transport (H : SimpleGraph W) {B : List W} (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length) (P : Set W) (w₀ : W)
    (hw₀ : w₀ ∈ Outside (slice B i j) \ P)
    (hends : ∀ t : W, (t = B[i]'(by omega) ∨ t = B[j]'hj) → t ∉ P → t = w₀)
    {a b : W} (ha : a ∈ Outside (slice B i j) \ P) (hb : b ∈ Outside (slice B i j) \ P)
    (h : RchIn H Pᶜ a b) :
    RchIn (H.deleteEdges (trackEdges (slice B i j))) (Outside (slice B i j) \ P) a b := by
  classical
  set C := slice B i j with hC
  set π : W → W := fun t => if t ∈ trackInterior C then w₀ else t with hπ
  have hmem : ∀ t ∈ Pᶜ, π t ∈ Outside C \ P := by
    intro t ht
    by_cases hti : t ∈ trackInterior C
    · simpa only [hπ, if_pos hti] using hw₀
    · exact ⟨by simpa only [hπ, if_neg hti, Outside, Set.mem_setOf_eq] using hti,
        by simpa only [hπ, if_neg hti] using ht⟩
  have hstep : ∀ c ∈ Pᶜ, ∀ t ∈ Pᶜ, H.Adj c t →
      π c = π t ∨ (H.deleteEdges (trackEdges C)).Adj (π c) (π t) := by
    intro c hc t ht hadj
    by_cases hci : c ∈ trackInterior C
    · -- an edge at an internal vertex of the window is an edge of the window
      have hsub := internal_incident_subset hB hij hj hci
      have hedge : s(c, t) ∈ trackEdges C := hsub ⟨hadj, Sym2.mem_mk_left _ _⟩
      have htC : t ∈ C := mem_slice_of_mem_trackEdges hedge (Sym2.mem_mk_right _ _)
      by_cases hti : t ∈ trackInterior C
      · left; simp only [hπ, if_pos hci, if_pos hti]
      · left
        have hte := hends t (end_of_mem_slice hB.1.2.1 hij hj htC hti) ht
        simp only [hπ, if_pos hci, if_neg hti]
        exact hte.symm
    · by_cases hti : t ∈ trackInterior C
      · have hsub := internal_incident_subset hB hij hj hti
        have hedge : s(c, t) ∈ trackEdges C := hsub ⟨hadj, Sym2.mem_mk_right _ _⟩
        have hcC : c ∈ C := mem_slice_of_mem_trackEdges hedge (Sym2.mem_mk_left _ _)
        left
        have hce := hends c (end_of_mem_slice hB.1.2.1 hij hj hcC hci) hc
        simp only [hπ, if_neg hci, if_pos hti]
        exact hce
      · right
        simp only [hπ, if_neg hci, if_neg hti]
        refine SimpleGraph.deleteEdges_adj.mpr ⟨hadj, ?_⟩
        intro hedge
        have hcC : c ∈ C := mem_slice_of_mem_trackEdges hedge (Sym2.mem_mk_left _ _)
        have htC : t ∈ C := mem_slice_of_mem_trackEdges hedge (Sym2.mem_mk_right _ _)
        have h1 := hends c (end_of_mem_slice hB.1.2.1 hij hj hcC hci) hc
        have h2 := hends t (end_of_mem_slice hB.1.2.1 hij hj htC hti) ht
        exact hadj.ne (h1.trans h2.symm)
  have hrun := rchIn_map (H := H) (G := H.deleteEdges (trackEdges C)) π hmem hstep h
  have hai : a ∉ trackInterior C := ha.1
  have hbi : b ∉ trackInterior C := hb.1
  simpa only [hπ, if_neg hai, if_neg hbi] using hrun

/-! ### The exceptional piece lies inside the window -/

/-- The piece that 5.5 leaves out lies strictly inside the window.

If a branch-free piece survives the deletion of the two ends of the window, then it lies on
the branch `B` (there is only one branch through those two vertices) and, walking along `B`
away from the window, it would reach an end of `B`, which is a branch-vertex. -/
theorem exceptional_subset (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {B : List W} (hB : IsBranch H B) {i j : ℕ} (hij : i < j) (hj : j < B.length)
    {E : Set W}
    (hEsub : E ⊆ ({B[i]'(by omega), B[j]'hj} : Set W)ᶜ)
    (hEcl : ∀ e ∈ E, ∀ w ∈ ({B[i]'(by omega), B[j]'hj} : Set W)ᶜ, H.Adj e w → w ∈ E)
    (hEnb : ∀ e ∈ E, e ∉ branchVertices H)
    (hEq : E.Nonempty → ∃ q : List W, IsBranch H q ∧
      E ∪ ({B[i]'(by omega), B[j]'hj} : Set W) ⊆ {v : W | v ∈ q}) :
    ∀ w ∈ E, w ∈ trackInterior (slice B i j) := by
  classical
  have hB2 : 2 ≤ B.length := by omega
  have hnd := hB.1.2.1
  have hBne : B[i]'(by omega) ≠ B[j]'hj := by
    intro h
    exact absurd (hnd.getElem_inj_iff.mp h) (by omega)
  -- the two ends of `B` are branch-vertices
  obtain ⟨n, J, hJ, hsubdiv⟩ := hc3
  have hc3' : CyclicallyThreeConnected H := ⟨n, J, hJ, hsubdiv⟩
  have hbv := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsubdiv B (B[0]'(by omega)) (B[B.length - 1]'(by omega)) hB
    (Workspace.ProofLemmas.Thm57Claim2Structure.branch_from_ends hB hB2)
    (by unfold trackLength; omega)
  intro w hw
  obtain ⟨q, hqb, hsub⟩ := hEq ⟨w, hw⟩
  have hiq : B[i]'(by omega) ∈ q := hsub (Or.inr (by left; rfl))
  have hjq : B[j]'hj ∈ q := hsub (Or.inr (by right; rfl))
  have hq2 : 2 ≤ q.length := by
    by_contra hcon
    interval_cases h : q.length
    · simp only [List.length_eq_zero_iff] at h
      rw [h] at hiq; simp at hiq
    · obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp h
      rw [hz] at hiq hjq
      simp only [List.mem_singleton] at hiq hjq
      exact hBne (hiq.trans hjq.symm)
  have hEqE : trackEdges B = trackEdges q :=
    trackEdges_eq_of_two_common hc3' hB hqb hB2 hq2 hBne
      (List.getElem_mem _) (List.getElem_mem _) hiq hjq
  have hwB : w ∈ B := mem_of_trackEdges_eq hq2 hEqE.symm (hsub (Or.inl hw))
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hwB
  have hki : k ≠ i := by
    intro h
    refine hEsub hw ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inl (by rw [← hkw, getElem_eq_of_index_eq B h _ _])
  have hkj : k ≠ j := by
    intro h
    refine hEsub hw ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr (by rw [← hkw, getElem_eq_of_index_eq B h _ _])
  -- membership of `B[m]` in the complement of the deleted pair, for `m` outside `[i, j]`
  have hcompl : ∀ (m : ℕ) (hm : m < B.length), m ≠ i → m ≠ j →
      B[m]'hm ∈ ({B[i]'(by omega), B[j]'hj} : Set W)ᶜ := by
    intro m hm hmi hmj hbad
    rcases hbad with h | h
    · exact hmi (hnd.getElem_inj_iff.mp h)
    · exact hmj (hnd.getElem_inj_iff.mp h)
  rcases Nat.lt_trichotomy k i with hlt | heq | hgt
  · exfalso
    have key : ∀ (d m : ℕ) (hm : m < B.length), m + d = k → B[m]'hm ∈ E := by
      intro d
      induction d with
      | zero =>
          intro m hm hmk
          rw [getElem_eq_of_index_eq B (show m = k by omega) hm hk, hkw]
          exact hw
      | succ e ih =>
          intro m hm hmk
          have hm1 : m + 1 < B.length := by omega
          have hprev : B[m + 1]'hm1 ∈ E := ih (m + 1) hm1 (by omega)
          exact hEcl _ hprev _ (hcompl m hm (by omega) (by omega)) (hB.1.2.2 m hm1).symm
    exact hEnb _ (key k 0 (by omega) (by omega)) hbv.1
  · exact absurd heq hki
  · rcases Nat.lt_or_ge j k with hgt' | hle
    · exfalso
      have key : ∀ (d m : ℕ) (hm : m < B.length), k + d = m → B[m]'hm ∈ E := by
        intro d
        induction d with
        | zero =>
            intro m hm hmk
            rw [getElem_eq_of_index_eq B (show m = k by omega) hm hk, hkw]
            exact hw
        | succ e ih =>
            intro m hm hmk
            have hm1 : m - 1 < B.length := by omega
            have hprev : B[m - 1]'hm1 ∈ E := ih (m - 1) hm1 (by omega)
            have hadj := hB.1.2.2 (m - 1) (show m - 1 + 1 < B.length by omega)
            rw [getElem_eq_of_index_eq B (show m - 1 + 1 = m by omega)
              (show m - 1 + 1 < B.length by omega) hm] at hadj
            exact hEcl _ hprev _ (hcompl m hm (by omega) (by omega)) hadj
      exact hEnb _ (key (B.length - 1 - k) (B.length - 1) (by omega) (by omega)) hbv.2
    · exact (mem_trackInterior_slice_iff hj (by omega)).mpr ⟨k, hk, hgt, by omega, hkw⟩

/-! ### The two connectivity statements -/

/-- **The window's complement is connected.**  PAPER (printed p. 23): *"there is a track in
`H \ {c₁,c₂}` from `a₁` to `a₂`"*. -/
theorem complement_connected (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {B : List W} (hB : IsBranch H B) {i j : ℕ} (hij : i < j) (hj : j < B.length) :
    ConnectedSet (H.deleteEdges (trackEdges (slice B i j)))
      (Outside (slice B i j) \ {B[i]'(by omega), B[j]'hj}) := by
  classical
  intro a b
  obtain ⟨E, hEsub, hEcl, hEnb, hEconn, hEbranch⟩ :=
    exists_exceptional hc3 (B[i]'(by omega)) (B[j]'hj)
  have hEint := exceptional_subset H hc3 hB hij hj hEsub hEcl hEnb hEbranch
  have hmem : ∀ z : W, z ∈ Outside (slice B i j) \ ({B[i]'(by omega), B[j]'hj} : Set W) →
      z ∈ ({B[i]'(by omega), B[j]'hj} : Set W)ᶜ \ E := by
    intro z hz
    exact ⟨hz.2, fun hzE => hz.1 (hEint z hzE)⟩
  have hrch : RchIn H (({B[i]'(by omega), B[j]'hj} : Set W)ᶜ) (a : W) (b : W) :=
    hEconn _ (hmem _ a.2) _ (hmem _ b.2)
  have := window_transport H hB hij hj ({B[i]'(by omega), B[j]'hj} : Set W) (a : W)
    a.2
    (by
      intro t ht htP
      exact absurd (show t ∈ ({B[i]'(by omega), B[j]'hj} : Set W) by
        rcases ht with h | h
        · exact Or.inl h
        · exact Or.inr h) htP)
    a.2 b.2 hrch
  exact this.choose_spec.choose_spec


/-- Neither end of the window is internal to it. -/
theorem ends_outside_slice {B : List W} (hnd : B.Nodup) {i j : ℕ} (hij : i < j)
    (hj : j < B.length) :
    B[i]'(by omega) ∈ Outside (slice B i j) ∧ B[j]'hj ∈ Outside (slice B i j) := by
  constructor
  · intro hc
    obtain ⟨k, hk, hik, hkj, hkb⟩ := (mem_trackInterior_slice_iff hj (by omega)).mp hc
    exact absurd (hnd.getElem_inj_iff.mp hkb) (by omega)
  · intro hc
    obtain ⟨k, hk, hik, hkj, hkb⟩ := (mem_trackInterior_slice_iff hj (by omega)).mp hc
    exact absurd (hnd.getElem_inj_iff.mp hkb) (by omega)

/-- **Deleting the ends of an edge outside the window.**  PAPER (printed p. 23): the second
connectivity premise in the application of 5.6 to `H'`. -/
theorem complement_delete_incident_connected (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) {B : List W} (hB : IsBranch H B)
    {i j : ℕ} (hij : i < j) (hj : j < B.length) {u v : W}
    (hedge : s(u, v) ∈ incidentEdges H (B[i]'(by omega)) ∪ incidentEdges H (B[j]'hj))
    (hout : s(u, v) ∉ trackEdges (slice B i j)) :
    ConnectedSet (H.deleteEdges (trackEdges (slice B i j)))
      (Outside (slice B i j) \ {u, v}) := by
  classical
  have hadj : H.Adj u v := by
    rcases hedge with h | h <;> exact h.1
  have hone : B[i]'(by omega) ∈ ({u, v} : Set W) ∨ B[j]'hj ∈ ({u, v} : Set W) := by
    rcases hedge with h | h
    · refine Or.inl ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Sym2.mem_iff.mp h.2
    · refine Or.inr ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Sym2.mem_iff.mp h.2
  have hconn := Workspace.ProofLemmas.Thm57EndgameEdgeDeletion.connected_compl_edge H hc3 hadj
  have houts := ends_outside_slice (B := B) hB.1.2.1 hij hj
  intro a b
  have hrch : RchIn H (({u, v} : Set W)ᶜ) (a : W) (b : W) :=
    ⟨a.2.2, b.2.2, hconn ⟨a, a.2.2⟩ ⟨b, b.2.2⟩⟩
  -- choose the surviving end of the window, if there is one
  have hchoice : ∃ w₀ : W, w₀ ∈ Outside (slice B i j) \ ({u, v} : Set W) ∧
      ∀ t : W, (t = B[i]'(by omega) ∨ t = B[j]'hj) → t ∉ ({u, v} : Set W) → t = w₀ := by
    by_cases hi : B[i]'(by omega) ∈ ({u, v} : Set W)
    · by_cases hj' : B[j]'hj ∈ ({u, v} : Set W)
      · refine ⟨(a : W), a.2, ?_⟩
        rintro t (rfl | rfl) ht
        · exact absurd hi ht
        · exact absurd hj' ht
      · refine ⟨B[j]'hj, ⟨houts.2, hj'⟩, ?_⟩
        rintro t (rfl | rfl) ht
        · exact absurd hi ht
        · rfl
    · refine ⟨B[i]'(by omega), ⟨houts.1, hi⟩, ?_⟩
      rintro t (rfl | rfl) ht
      · rfl
      · rcases hone with h | h
        · exact absurd h hi
        · exact absurd h ht
  obtain ⟨w₀, hw₀, hends⟩ := hchoice
  exact (window_transport H hB hij hj ({u, v} : Set W) w₀ hw₀ hends a.2 b.2
    hrch).choose_spec.choose_spec

end Workspace.ProofLemmas.Thm57Claim2WindowConn
