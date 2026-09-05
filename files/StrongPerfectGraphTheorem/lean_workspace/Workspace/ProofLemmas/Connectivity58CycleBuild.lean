import Workspace.ProofLemmas.Thm58BranchBranchCycleRung
import Workspace.ProofLemmas.Connectivity58Minimal

/-!
# Closing a branch into a cycle, and reading the cycle from any of its vertices

PAPER (5.8 (7), printed p. 28): *"There is a cycle in `H` using the branch between `u₁` and
`v₁` …"*

`Connectivity58Cycle.exists_return_track` produces the second track `D` joining the two ends of
the branch `q`.  This file glues `q` and `D` into an `IsCycleList` and rotates the result, so
that the cycle can be listed starting at any prescribed vertex of the branch.  The rotation is
what lets the caller decide which edge of the cycle becomes the first vertex of the hole of `G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Connectivity58CycleBuild

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm58BranchBranchCycleRung

variable {W : Type*} [DecidableEq W] {H : SimpleGraph W}

/-- The last vertex of a track with named ends. -/
theorem track_last {q : List W} {u v : W} (hq : IsTrackFrom H q u v)
    (h : 0 < q.length) : q[q.length - 1]'(by omega) = v := by
  have h' := hq.2.2
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega : q.length - 1 < q.length)] at h'
  exact Option.some_injective _ h'

theorem track_first {q : List W} {u v : W} (hq : IsTrackFrom H q u v)
    (h : 0 < q.length) : q[0]'h = u := by
  have h' := hq.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h] at h'
  exact Option.some_injective _ h'

/-! ### The interior of a track, by index -/

theorem trackInterior_length (D : List W) : (trackInterior D).length = D.length - 2 := by
  simp only [trackInterior, List.length_dropLast, List.length_tail]
  omega

theorem trackInterior_getElem (D : List W) (t : ℕ) (h : t < (trackInterior D).length) :
    (trackInterior D)[t] = D[t + 1]'(by rw [trackInterior_length] at h; omega) := by
  simp only [trackInterior] at h ⊢
  rw [List.getElem_dropLast, List.getElem_tail]

theorem mem_trackInterior_of_getElem (D : List W) (t : ℕ) (h : t < (trackInterior D).length) :
    D[t + 1]'(by rw [trackInterior_length] at h; omega) ∈ trackInterior D := by
  rw [← trackInterior_getElem D t h]; exact List.getElem_mem h

/-! ### The cycle -/

/-- The cycle of `H` formed by a branch `q` and a return track `D` with the same ends. -/
def baseCycle (q D : List W) : List W := q ++ (trackInterior D).reverse

theorem baseCycle_length (q D : List W) :
    (baseCycle q D).length = q.length + (D.length - 2) := by
  simp only [baseCycle, List.length_append, List.length_reverse, trackInterior_length]

theorem baseCycle_getElem_left (q D : List W) (j : ℕ) (hj : j < q.length)
    (h : j < (baseCycle q D).length) : (baseCycle q D)[j] = q[j] :=
  List.getElem_append_left hj

theorem baseCycle_getElem_right (q D : List W) (j : ℕ) (hj : q.length ≤ j)
    (h : j < (baseCycle q D).length) :
    (baseCycle q D)[j] = D[D.length - 2 - (j - q.length)]'(by
      rw [baseCycle_length] at h; omega) := by
  have h' : j < q.length + (D.length - 2) := by rw [baseCycle_length] at h; exact h
  have hlen : (trackInterior D).reverse.length = D.length - 2 := by
    rw [List.length_reverse, trackInterior_length]
  have h1 : (baseCycle q D)[j] =
      (trackInterior D).reverse[j - q.length]'(by rw [hlen]; omega) :=
    List.getElem_append_right hj
  rw [h1, List.getElem_reverse, trackInterior_getElem]
  exact SubdivisionCounting.getElem_eq_of_index_eq D
    (by rw [trackInterior_length]; omega) _ _

theorem mem_baseCycle {q D : List W} {x : W} :
    x ∈ baseCycle q D ↔ x ∈ q ∨ x ∈ trackInterior D := by
  simp only [baseCycle, List.mem_append, List.mem_reverse]

/-- **The branch and the return track form a cycle.** -/
theorem isCycleList_baseCycle {q D : List W} {v₁ v₂ : W}
    (hq : IsTrackFrom H q v₁ v₂) (hD : IsTrackFrom H D v₁ v₂)
    (hq2 : 2 ≤ q.length) (hD3 : 3 ≤ D.length)
    (hdisj : ∀ x ∈ trackInterior D, x ∉ q) :
    IsCycleList H (baseCycle q D) := by
  classical
  have hlen := baseCycle_length q D
  have hqlen : 0 < q.length := by omega
  have hq0 : q[0]'hqlen = v₁ := track_first hq hqlen
  have hql : q[q.length - 1]'(by omega) = v₂ := track_last hq hqlen
  have hD0 : D[0]'(by omega) = v₁ := track_first hD (by omega)
  have hDl : D[D.length - 1]'(by omega) = v₂ := track_last hD (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · rw [baseCycle, List.nodup_append]
    refine ⟨hq.1.2.1, (List.nodup_reverse).mpr ?_, ?_⟩
    · exact List.Nodup.sublist (List.dropLast_sublist _ |>.trans (List.tail_sublist _)) hD.1.2.1
    · intro a ha b hb
      rw [List.mem_reverse] at hb
      intro hab
      exact hdisj b hb (hab ▸ ha)
  · intro j hj h2
    have hjlen : j < q.length + (D.length - 2) := by rw [hlen] at hj; exact hj
    rcases Nat.lt_or_ge (j + 1) q.length with hcase | hcase
    · -- inside the branch
      have hnxt : nxt (baseCycle q D) j = j + 1 := by
        rw [nxt, hlen]; exact Nat.mod_eq_of_lt (by omega)
      rw [SubdivisionCounting.getElem_eq_of_index_eq (baseCycle q D) hnxt h2
        (show j + 1 < (baseCycle q D).length by rw [hlen]; omega)]
      rw [baseCycle_getElem_left q D j (by omega) hj,
        baseCycle_getElem_left q D (j + 1) hcase (by rw [hlen]; omega)]
      exact hq.1.2.2 j hcase
    rcases Nat.lt_or_ge j (q.length - 1) with hcase2 | hcase2
    · omega
    rcases Nat.eq_or_lt_of_le hcase2 with hcase3 | hcase3
    · -- the junction at `v₂`
      have hjq : j = q.length - 1 := hcase3.symm
      have hnxt : nxt (baseCycle q D) j = j + 1 := by
        rw [nxt, hlen]; exact Nat.mod_eq_of_lt (by omega)
      rw [SubdivisionCounting.getElem_eq_of_index_eq (baseCycle q D) hnxt h2
        (show j + 1 < (baseCycle q D).length by rw [hlen]; omega)]
      rw [baseCycle_getElem_left q D j (by omega) hj,
        baseCycle_getElem_right q D (j + 1) (by omega) (by rw [hlen]; omega)]
      have e1 : q[j]'(by omega : j < q.length) = v₂ := by
        rw [SubdivisionCounting.getElem_eq_of_index_eq q hjq (by omega) (by omega)]; exact hql
      have e2 : D[D.length - 2 - (j + 1 - q.length)]'(by omega) = D[D.length - 2]'(by omega) :=
        SubdivisionCounting.getElem_eq_of_index_eq D (by omega) (by omega) (by omega)
      rw [e1, e2]
      have := hD.1.2.2 (D.length - 2) (by omega)
      have e3 : D[D.length - 2 + 1]'(by omega) = D[D.length - 1]'(by omega) :=
        SubdivisionCounting.getElem_eq_of_index_eq D (by omega) (by omega) (by omega)
      rw [e3, hDl] at this
      exact this.symm
    rcases Nat.lt_or_ge (j + 1) ((baseCycle q D).length) with hcase4 | hcase4
    · -- inside the return track
      have hnxt : nxt (baseCycle q D) j = j + 1 := by
        rw [nxt]; exact Nat.mod_eq_of_lt hcase4
      rw [SubdivisionCounting.getElem_eq_of_index_eq (baseCycle q D) hnxt h2 hcase4]
      rw [baseCycle_getElem_right q D j (by omega) hj,
        baseCycle_getElem_right q D (j + 1) (by omega) (by rw [hlen]; omega)]
      rw [hlen] at hcase4
      have := hD.1.2.2 (D.length - 2 - (j + 1 - q.length)) (by omega)
      have e3 : D[D.length - 2 - (j + 1 - q.length) + 1]'(by omega)
          = D[D.length - 2 - (j - q.length)]'(by omega) :=
        SubdivisionCounting.getElem_eq_of_index_eq D (by omega) (by omega) (by omega)
      rw [e3] at this
      exact this.symm
    · -- back to `v₁`
      have hjl : j = (baseCycle q D).length - 1 := by omega
      have hnxt : nxt (baseCycle q D) j = 0 := by
        rw [nxt, hjl]
        have : (baseCycle q D).length - 1 + 1 = (baseCycle q D).length := by rw [hlen]; omega
        rw [this, Nat.mod_self]
      rw [SubdivisionCounting.getElem_eq_of_index_eq (baseCycle q D) hnxt h2
        (show 0 < (baseCycle q D).length by rw [hlen]; omega)]
      rw [baseCycle_getElem_right q D j (by omega) hj,
        baseCycle_getElem_left q D 0 (by omega) (by rw [hlen]; omega)]
      rw [hlen] at hjl
      have e2 : D[D.length - 2 - (j - q.length)]'(by omega) = D[1]'(by omega) :=
        SubdivisionCounting.getElem_eq_of_index_eq D (by omega) (by omega) (by omega)
      rw [e2, hq0, ← hD0]
      have := hD.1.2.2 0 (by omega)
      exact this.symm

/-! ### Rotating a cycle -/

/-- A cycle may be listed starting at any of its vertices. -/
theorem isCycleList_rotate {cy : List W} (hc : IsCycleList H cy) (r : ℕ) :
    IsCycleList H (cy.rotate r) := by
  obtain ⟨h3, hnd, hadj⟩ := hc
  have hlen : (cy.rotate r).length = cy.length := List.length_rotate cy r
  refine ⟨by omega, List.nodup_rotate.mpr hnd, ?_⟩
  intro i hi h2
  have hL : 0 < cy.length := by omega
  rw [List.getElem_rotate, List.getElem_rotate]
  have hj : (i + r) % cy.length < cy.length := Nat.mod_lt _ hL
  have hh := hadj ((i + r) % cy.length) hj (nxt_lt hj)
  have e : nxt cy ((i + r) % cy.length) = (nxt (cy.rotate r) i + r) % cy.length := by
    rw [nxt, nxt, hlen, Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    omega
  rw [SubdivisionCounting.getElem_eq_of_index_eq cy e (nxt_lt hj)
    (by rw [← e]; exact nxt_lt hj)] at hh
  exact hh

/-- The cycle of the branch `q` and its return track `D`, listed from `q[s]`. -/
def cycleFrom (q D : List W) (s : ℕ) : List W := (baseCycle q D).rotate s

theorem cycleFrom_length (q D : List W) (s : ℕ) :
    (cycleFrom q D s).length = q.length + (D.length - 2) := by
  rw [cycleFrom, List.length_rotate, baseCycle_length]

theorem mem_cycleFrom {q D : List W} {s : ℕ} {x : W} :
    x ∈ cycleFrom q D s ↔ x ∈ q ∨ x ∈ trackInterior D := by
  rw [cycleFrom, List.mem_rotate, mem_baseCycle]

theorem isCycleList_cycleFrom {q D : List W} {v₁ v₂ : W}
    (hq : IsTrackFrom H q v₁ v₂) (hD : IsTrackFrom H D v₁ v₂)
    (hq2 : 2 ≤ q.length) (hD3 : 3 ≤ D.length)
    (hdisj : ∀ x ∈ trackInterior D, x ∉ q) (s : ℕ) :
    IsCycleList H (cycleFrom q D s) :=
  isCycleList_rotate (isCycleList_baseCycle hq hD hq2 hD3 hdisj) s

/-- The first vertices of the rotated cycle are the tail of the branch. -/
theorem cycleFrom_getElem_branch (q D : List W) (s m : ℕ) (hs : s + m < q.length)
    (h : m < (cycleFrom q D s).length) :
    (cycleFrom q D s)[m] = q[s + m]'(by omega) := by
  have hb : (baseCycle q D).length = q.length + (D.length - 2) := baseCycle_length q D
  simp only [cycleFrom]
  rw [List.getElem_rotate]
  have hmod : (m + s) % (baseCycle q D).length = m + s := Nat.mod_eq_of_lt (by omega)
  rw [SubdivisionCounting.getElem_eq_of_index_eq (baseCycle q D) hmod _ (by omega),
    baseCycle_getElem_left q D (m + s) (by omega) (by omega)]
  exact SubdivisionCounting.getElem_eq_of_index_eq q (by omega) _ _

/-- The last vertex of the rotated cycle is the branch vertex just before the cut. -/
theorem cycleFrom_getElem_last (q D : List W) (s : ℕ) (hs : 1 ≤ s) (hsq : s ≤ q.length)
    (hD3 : 3 ≤ D.length)
    (h : (cycleFrom q D s).length - 1 < (cycleFrom q D s).length) :
    (cycleFrom q D s)[(cycleFrom q D s).length - 1] = q[s - 1]'(by omega) := by
  have hb : (baseCycle q D).length = q.length + (D.length - 2) := baseCycle_length q D
  have hlen : (cycleFrom q D s).length = q.length + (D.length - 2) := cycleFrom_length q D s
  simp only [cycleFrom] at h ⊢
  rw [List.getElem_rotate]
  have hmod : (((baseCycle q D).rotate s).length - 1 + s) % (baseCycle q D).length = s - 1 := by
    rw [List.length_rotate, hb]
    have he : q.length + (D.length - 2) - 1 + s = (s - 1) + 1 * (q.length + (D.length - 2)) := by
      omega
    rw [he, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [SubdivisionCounting.getElem_eq_of_index_eq (baseCycle q D) hmod _ (by omega),
    baseCycle_getElem_left q D (s - 1) (by omega) (by omega)]

end Workspace.ProofLemmas.Connectivity58CycleBuild
