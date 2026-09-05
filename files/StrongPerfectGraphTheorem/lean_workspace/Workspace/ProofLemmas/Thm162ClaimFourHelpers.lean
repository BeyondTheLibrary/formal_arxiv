import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.Statements.S15.Thm_15_3

/-!
# Private graph bookkeeping for 16.2, claim (4)

This file contains no numbered assertion.  It packages the repeated application of 15.3
called `nobanister` in the paper: two mutually anticomplete tracks, each containing exactly
one `Y`-complete edge, cannot have their corresponding ends joined by a clean path outside
the tracks.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

namespace Workspace.ProofLemmas.Thm162ClaimFourHelpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem singleton_path (G : SimpleGraph V) (x : V) : IsPathFrom G [x] x x := by
  exact ⟨PathBasics.isPathList_singleton G x, rfl, rfl⟩

/-- Two adjacent vertices of an induced path occupy consecutive positions. -/
private theorem adjacent_pair_positions {G : SimpleGraph V} {Q : List V} {c d : V}
    (hQ : IsPathList G Q) (hc : c ∈ Q) (hd : d ∈ Q) (hcd : G.Adj c d) :
    ∃ (t : ℕ) (ht : t + 1 < Q.length),
      ((Q[t]'(by omega) = c ∧ Q[t + 1]'ht = d) ∨
        (Q[t]'(by omega) = d ∧ Q[t + 1]'ht = c)) := by
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem hc
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hd
  have hij := (PathBasics.path_adj_iff hQ hi hj).mp (by simpa [hie, hje] using hcd)
  rcases hij with hij | hij
  · refine ⟨i, by omega, Or.inl ⟨hie, ?_⟩⟩
    simpa [hij] using hje
  · refine ⟨j, by omega, Or.inr ⟨hje, ?_⟩⟩
    simpa [hij] using hie

/-- The paper's two uses of 15.3 under the name `nobanister`.

`Q` and `R` are disjoint anticomplete induced paths.  Their corresponding ends attach to the
ends of the induced path `S`, no other edge joins `S` to either track, no vertex of `S` is
`Y`-complete, and each track contains exactly the two ends of one `Y`-complete edge.  The
cycle `f₁-Q-fk-R-f₁`, with the possible chord `f₁fk`, is precisely the configuration of
15.3, whose conclusion contradicts the non-completeness of `S`.
-/
theorem no_banister {G : SimpleGraph V} (hG : InF6 G) {Y : Set V}
    (hYanti : AnticonnectedSet G Y)
    {S Q R : List V} {f₁ fk q₁ q₂ r₁ r₂ : V}
    (hS : IsPathFrom G S f₁ fk) (hS2 : 2 ≤ S.length)
    (hQ : IsPathFrom G Q q₁ q₂) (hQ2 : 2 ≤ Q.length)
    (hR : IsPathFrom G R r₁ r₂) (hR2 : 2 ≤ R.length)
    (hSQdisj : ∀ x ∈ S, x ∉ Q) (hSRdisj : ∀ x ∈ S, x ∉ R)
    (hQRdisj : ∀ x ∈ Q, x ∉ R)
    (hSQ : ∀ x ∈ S, ∀ y ∈ Q,
      (G.Adj x y ↔ (x = f₁ ∧ y = q₁) ∨ (x = fk ∧ y = q₂)))
    (hSR : ∀ x ∈ S, ∀ y ∈ R,
      (G.Adj x y ↔ (x = f₁ ∧ y = r₁) ∨ (x = fk ∧ y = r₂)))
    (hQR : ∀ x ∈ Q, ∀ y ∈ R, ¬ G.Adj x y)
    (hSY : ∀ x ∈ S, x ∉ Y) (hQY : ∀ x ∈ Q, x ∉ Y)
    (hRY : ∀ x ∈ R, x ∉ Y)
    (hSnc : ∀ x ∈ S, ¬ VertexComplete G x Y)
    {c d e g : V}
    (hQc : {x : V | x ∈ Q ∧ VertexComplete G x Y} = {c, d})
    (hcd : c ≠ d) (hcdadj : G.Adj c d)
    (hRc : {x : V | x ∈ R ∧ VertexComplete G x Y} = {e, g})
    (heg : e ≠ g) (hegadj : G.Adj e g) : False := by
  classical
  have hf₁S : f₁ ∈ S := (PathBasics.isPathFrom_ends_mem hS).1
  have hfkS : fk ∈ S := (PathBasics.isPathFrom_ends_mem hS).2
  have hq₁Q : q₁ ∈ Q := (PathBasics.isPathFrom_ends_mem hQ).1
  have hq₂Q : q₂ ∈ Q := (PathBasics.isPathFrom_ends_mem hQ).2
  have hr₁R : r₁ ∈ R := (PathBasics.isPathFrom_ends_mem hR).1
  have hr₂R : r₂ ∈ R := (PathBasics.isPathFrom_ends_mem hR).2
  have hfne : f₁ ≠ fk := by
    intro he
    have h0 : S[0]'(by omega) = f₁ :=
      PathBasics.getElem_zero_of_head? hS.2.1 (by omega)
    have hl : S[S.length - 1]'(by omega) = fk :=
      PathBasics.getElem_last_of_getLast? hS.2.2 (by omega)
    have hi := (List.Nodup.getElem_inj_iff hS.1.2.1).mp (h0.trans (he.trans hl.symm))
    omega
  have hf₁Q : f₁ ∉ Q := hSQdisj f₁ hf₁S
  have hfkQ : fk ∉ Q := hSQdisj fk hfkS
  have hf₁R : f₁ ∉ R := hSRdisj f₁ hf₁S
  have hfkR : fk ∉ R := hSRdisj fk hfkS

  -- `A` and `B` are the two sides of the cycle used in 15.3.
  let A : List V := [f₁] ++ Q
  let B : List V := [fk] ++ R.reverse
  have hA : IsPathFrom G A f₁ q₂ := by
    dsimp only [A]
    refine PathGlue.glue_path (singleton_path G f₁) hQ ?_ ?_
    · intro x hx hxQ
      rw [List.mem_singleton] at hx
      exact hf₁Q (hx ▸ hxQ)
    · intro x hx y hy
      rw [List.mem_singleton] at hx
      subst x
      rw [hSQ f₁ hf₁S y hy]
      constructor
      · rintro (⟨-, rfl⟩ | ⟨he, -⟩)
        · exact ⟨rfl, rfl⟩
        · exact absurd he hfne
      · rintro ⟨-, rfl⟩
        exact Or.inl ⟨rfl, rfl⟩
  have hB : IsPathFrom G B fk r₁ := by
    dsimp only [B]
    refine PathGlue.glue_path (singleton_path G fk)
      (PathBasics.isPathFrom_reverse hR) ?_ ?_
    · intro x hx hxR
      rw [List.mem_singleton] at hx
      exact hfkR (hx ▸ List.mem_reverse.mp hxR)
    · intro x hx y hy
      rw [List.mem_singleton] at hx
      subst x
      rw [List.mem_reverse] at hy
      rw [hSR fk hfkS y hy]
      constructor
      · rintro (⟨he, -⟩ | ⟨-, rfl⟩)
        · exact absurd he hfne.symm
        · exact ⟨rfl, rfl⟩
      · rintro ⟨-, rfl⟩
        exact Or.inr ⟨rfl, rfl⟩
  have hAlen : A.length = Q.length + 1 := by simp [A]
  have hBlen : B.length = R.length + 1 := by simp [B]
  have hA2 : 3 ≤ A.length := by omega
  have hB2 : 3 ≤ B.length := by omega

  have hABdisj : ∀ x ∈ A, x ∉ B := by
    intro x hxA hxB
    rcases List.mem_append.mp hxA with hx | hxQ
    · have hxf : x = f₁ := List.mem_singleton.mp hx
      subst x
      rcases List.mem_append.mp hxB with hx | hxR
      · exact hfne (List.mem_singleton.mp hx)
      · exact hf₁R (List.mem_reverse.mp hxR)
    · rcases List.mem_append.mp hxB with hx | hxR
      · exact hfkQ (List.mem_singleton.mp hx ▸ hxQ)
      · exact hQRdisj x hxQ (List.mem_reverse.mp hxR)
  have hAB : ∀ x ∈ A, ∀ y ∈ B,
      G.Adj x y →
        (x = q₂ ∧ y = fk) ∨ (x = f₁ ∧ y = r₁) ∨ (x = f₁ ∧ y = fk) := by
    intro x hxA y hyB hxy
    rcases List.mem_append.mp hxA with hx | hxQ
    · have hxf : x = f₁ := List.mem_singleton.mp hx
      subst x
      rcases List.mem_append.mp hyB with hy | hyR
      · exact Or.inr (Or.inr ⟨rfl, List.mem_singleton.mp hy⟩)
      · rw [List.mem_reverse] at hyR
        rcases (hSR f₁ hf₁S y hyR).mp hxy with ⟨-, hyr⟩ | ⟨he, -⟩
        · exact Or.inr (Or.inl ⟨rfl, hyr⟩)
        · exact absurd he hfne
    · rcases List.mem_append.mp hyB with hy | hyR
      · have hyf : y = fk := List.mem_singleton.mp hy
        subst y
        rcases (hSQ fk hfkS x hxQ).mp hxy.symm with ⟨he, -⟩ | ⟨-, hxq⟩
        · exact absurd he hfne.symm
        · exact Or.inl ⟨hxq, rfl⟩
      · exact absurd hxy (hQR x hxQ y (List.mem_reverse.mp hyR))

  let D : List V := A ++ B
  have hDlen : D.length = Q.length + R.length + 2 := by
    simp only [D, List.length_append, hAlen, hBlen]
    omega
  have hD6 : 6 ≤ D.length := by omega
  have hDnd : D.Nodup := by
    dsimp only [D]
    rw [List.nodup_append]
    exact ⟨hA.1.2.1, hB.1.2.1,
      fun a ha b hb he => hABdisj a ha (he ▸ hb)⟩

  have hDcycle : ∀ (i j : ℕ) (hi : i < D.length) (hj : j < D.length),
      (j = (i + 1) % D.length ∨ i = (j + 1) % D.length) → G.Adj D[i] D[j] := by
    intro i j hi hj hij
    have hiL : i < A.length + B.length := by simpa [D] using hi
    have hjL : j < A.length + B.length := by simpa [D] using hj
    rcases lt_or_ge i A.length with hiA | hiA <;>
      rcases lt_or_ge j A.length with hjA | hjA
    · rw [show D[i] = A[i] by simp only [D]; exact List.getElem_append_left hiA,
          show D[j] = A[j] by simp only [D]; exact List.getElem_append_left hjA,
          PathBasics.path_adj_iff hA.1 hiA hjA]
      simp only [D, List.length_append] at hij
      rw [PathGlue.succ_mod_eq hiL, PathGlue.succ_mod_eq hjL] at hij
      split_ifs at hij <;> omega
    · have hjB : j - A.length < B.length := by omega
      have hcases : (i = A.length - 1 ∧ j = A.length) ∨
          (i = 0 ∧ j = A.length + B.length - 1) := by
        simp only [D, List.length_append] at hij
        rw [PathGlue.succ_mod_eq hiL, PathGlue.succ_mod_eq hjL] at hij
        split_ifs at hij <;> omega
      rcases hcases with ⟨hiLast, hjFirst⟩ | ⟨hiFirst, hjLast⟩
      · have hAi : A[i]'hiA = q₂ := by
          have := PathBasics.getElem_last_of_getLast? hA.2.2 (by omega)
          simpa [hiLast] using this
        have hBj : B[j - A.length]'hjB = fk := by
          have := PathBasics.getElem_zero_of_head? hB.2.1 (by omega)
          simpa [hjFirst] using this
        rw [show D[i] = A[i] by simp only [D]; exact List.getElem_append_left hiA,
          show D[j] = B[j - A.length] by simp only [D]; exact List.getElem_append_right hjA,
          hAi, hBj]
        exact (hSQ fk hfkS q₂ hq₂Q).mpr (Or.inr ⟨rfl, rfl⟩) |>.symm
      · have hAi : A[i]'hiA = f₁ := by
          have := PathBasics.getElem_zero_of_head? hA.2.1 (by omega)
          simpa [hiFirst] using this
        have hBj : B[j - A.length]'hjB = r₁ := by
          have := PathBasics.getElem_last_of_getLast? hB.2.2 (by omega)
          have he : j - A.length = B.length - 1 := by omega
          simpa [he] using this
        rw [show D[i] = A[i] by simp only [D]; exact List.getElem_append_left hiA,
          show D[j] = B[j - A.length] by simp only [D]; exact List.getElem_append_right hjA,
          hAi, hBj]
        exact (hSR f₁ hf₁S r₁ hr₁R).mpr (Or.inl ⟨rfl, rfl⟩)
    · have hiB : i - A.length < B.length := by omega
      have hcases : (j = A.length - 1 ∧ i = A.length) ∨
          (j = 0 ∧ i = A.length + B.length - 1) := by
        simp only [D, List.length_append] at hij
        rw [PathGlue.succ_mod_eq hiL, PathGlue.succ_mod_eq hjL] at hij
        split_ifs at hij <;> omega
      rcases hcases with ⟨hjLast, hiFirst⟩ | ⟨hjFirst, hiLast⟩
      · have hAj : A[j]'hjA = q₂ := by
          have := PathBasics.getElem_last_of_getLast? hA.2.2 (by omega)
          simpa [hjLast] using this
        have hBi : B[i - A.length]'hiB = fk := by
          have := PathBasics.getElem_zero_of_head? hB.2.1 (by omega)
          simpa [hiFirst] using this
        rw [show D[i] = B[i - A.length] by simp only [D]; exact List.getElem_append_right hiA,
          show D[j] = A[j] by simp only [D]; exact List.getElem_append_left hjA,
          hBi, hAj]
        exact (hSQ fk hfkS q₂ hq₂Q).mpr (Or.inr ⟨rfl, rfl⟩)
      · have hAj : A[j]'hjA = f₁ := by
          have := PathBasics.getElem_zero_of_head? hA.2.1 (by omega)
          simpa [hjFirst] using this
        have hBi : B[i - A.length]'hiB = r₁ := by
          have := PathBasics.getElem_last_of_getLast? hB.2.2 (by omega)
          have he : i - A.length = B.length - 1 := by omega
          simpa [he] using this
        rw [show D[i] = B[i - A.length] by simp only [D]; exact List.getElem_append_right hiA,
          show D[j] = A[j] by simp only [D]; exact List.getElem_append_left hjA,
          hBi, hAj]
        exact (hSR f₁ hf₁S r₁ hr₁R).mpr (Or.inl ⟨rfl, rfl⟩) |>.symm
    · have hiB : i - A.length < B.length := by omega
      have hjB : j - A.length < B.length := by omega
      rw [show D[i] = B[i - A.length] by simp only [D]; exact List.getElem_append_right hiA,
          show D[j] = B[j - A.length] by simp only [D]; exact List.getElem_append_right hjA,
          PathBasics.path_adj_iff hB.1 hiB hjB]
      simp only [D, List.length_append] at hij
      rw [PathGlue.succ_mod_eq hiL, PathGlue.succ_mod_eq hjL] at hij
      split_ifs at hij <;> omega
  have hDinduced : ∀ (i j : ℕ) (hi : i < D.length) (hj : j < D.length),
      G.Adj D[i] D[j] →
        (j = (i + 1) % D.length ∨ i = (j + 1) % D.length) ∨
          ((i = 0 ∧ j = A.length) ∨ (j = 0 ∧ i = A.length)) := by
    intro i j hi hj hadj
    have hiL : i < A.length + B.length := by simpa [D] using hi
    have hjL : j < A.length + B.length := by simpa [D] using hj
    rcases lt_or_ge i A.length with hiA | hiA <;>
      rcases lt_or_ge j A.length with hjA | hjA
    · left
      rw [show D[i] = A[i] by simp only [D]; exact List.getElem_append_left hiA,
          show D[j] = A[j] by simp only [D]; exact List.getElem_append_left hjA,
          PathBasics.path_adj_iff hA.1 hiA hjA] at hadj
      simp only [D, List.length_append]
      rw [PathGlue.succ_mod_eq hiL, PathGlue.succ_mod_eq hjL]
      split_ifs <;> omega
    · have hjB : j - A.length < B.length := by omega
      have hAi : D[i]'hi = A[i]'hiA := by
        simp only [D]; exact List.getElem_append_left hiA
      have hBj : D[j]'hj = B[j - A.length]'hjB := by
        simp only [D]; exact List.getElem_append_right hjA
      have hcases := hAB (A[i]'hiA) (List.getElem_mem hiA)
        (B[j - A.length]'hjB) (List.getElem_mem hjB) (by simpa [hAi, hBj] using hadj)
      rcases hcases with ⟨hqi, hfj⟩ | ⟨hfi, hrj⟩ | ⟨hfi, hfj⟩
      · left
        left
        have hiLast : i = A.length - 1 := by
          have hl : A[A.length - 1]'(by omega) = q₂ :=
            PathBasics.getElem_last_of_getLast? hA.2.2 (by omega)
          exact (List.Nodup.getElem_inj_iff hA.1.2.1).mp (hqi.trans hl.symm)
        have hjFirst : j - A.length = 0 := by
          have h0 : B[0]'(by omega) = fk :=
            PathBasics.getElem_zero_of_head? hB.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hB.1.2.1).mp (hfj.trans h0.symm)
        simp only [D, List.length_append]
        rw [PathGlue.succ_mod_eq hiL]
        split_ifs <;> omega
      · left
        right
        have hiFirst : i = 0 := by
          have h0 : A[0]'(by omega) = f₁ :=
            PathBasics.getElem_zero_of_head? hA.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hA.1.2.1).mp (hfi.trans h0.symm)
        have hjLast : j - A.length = B.length - 1 := by
          have hl : B[B.length - 1]'(by omega) = r₁ :=
            PathBasics.getElem_last_of_getLast? hB.2.2 (by omega)
          exact (List.Nodup.getElem_inj_iff hB.1.2.1).mp (hrj.trans hl.symm)
        simp only [D, List.length_append]
        rw [PathGlue.succ_mod_eq hjL]
        split_ifs <;> omega
      · right
        left
        have hiFirst : i = 0 := by
          have h0 : A[0]'(by omega) = f₁ :=
            PathBasics.getElem_zero_of_head? hA.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hA.1.2.1).mp (hfi.trans h0.symm)
        have hjFirst : j - A.length = 0 := by
          have h0 : B[0]'(by omega) = fk :=
            PathBasics.getElem_zero_of_head? hB.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hB.1.2.1).mp (hfj.trans h0.symm)
        omega
    · have hiB : i - A.length < B.length := by omega
      have hBi : D[i]'hi = B[i - A.length]'hiB := by
        simp only [D]; exact List.getElem_append_right hiA
      have hAj : D[j]'hj = A[j]'hjA := by
        simp only [D]; exact List.getElem_append_left hjA
      have hcases := hAB (A[j]'hjA) (List.getElem_mem hjA)
        (B[i - A.length]'hiB) (List.getElem_mem hiB) (by simpa [hBi, hAj] using hadj.symm)
      rcases hcases with ⟨hqj, hfi⟩ | ⟨hfj, hri⟩ | ⟨hfj, hfi⟩
      · left
        right
        have hjLast : j = A.length - 1 := by
          have hl : A[A.length - 1]'(by omega) = q₂ :=
            PathBasics.getElem_last_of_getLast? hA.2.2 (by omega)
          exact (List.Nodup.getElem_inj_iff hA.1.2.1).mp (hqj.trans hl.symm)
        have hiFirst : i - A.length = 0 := by
          have h0 : B[0]'(by omega) = fk :=
            PathBasics.getElem_zero_of_head? hB.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hB.1.2.1).mp (hfi.trans h0.symm)
        simp only [D, List.length_append]
        rw [PathGlue.succ_mod_eq hjL]
        split_ifs <;> omega
      · left
        left
        have hjFirst : j = 0 := by
          have h0 : A[0]'(by omega) = f₁ :=
            PathBasics.getElem_zero_of_head? hA.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hA.1.2.1).mp (hfj.trans h0.symm)
        have hiLast : i - A.length = B.length - 1 := by
          have hl : B[B.length - 1]'(by omega) = r₁ :=
            PathBasics.getElem_last_of_getLast? hB.2.2 (by omega)
          exact (List.Nodup.getElem_inj_iff hB.1.2.1).mp (hri.trans hl.symm)
        simp only [D, List.length_append]
        rw [PathGlue.succ_mod_eq hiL]
        split_ifs <;> omega
      · right
        right
        have hjFirst : j = 0 := by
          have h0 : A[0]'(by omega) = f₁ :=
            PathBasics.getElem_zero_of_head? hA.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hA.1.2.1).mp (hfj.trans h0.symm)
        have hiFirst : i - A.length = 0 := by
          have h0 : B[0]'(by omega) = fk :=
            PathBasics.getElem_zero_of_head? hB.2.1 (by omega)
          exact (List.Nodup.getElem_inj_iff hB.1.2.1).mp (hfi.trans h0.symm)
        omega
    · have hiB : i - A.length < B.length := by omega
      have hjB : j - A.length < B.length := by omega
      left
      rw [show D[i] = B[i - A.length] by simp only [D]; exact List.getElem_append_right hiA,
          show D[j] = B[j - A.length] by simp only [D]; exact List.getElem_append_right hjA,
          PathBasics.path_adj_iff hB.1 hiB hjB] at hadj
      simp only [D, List.length_append]
      rw [PathGlue.succ_mod_eq hiL, PathGlue.succ_mod_eq hjL]
      split_ifs <;> omega

  -- Locate the unique complete edge of each track.
  have hcQ : c ∈ Q ∧ VertexComplete G c Y := by
    have hm : c ∈ {x : V | x ∈ Q ∧ VertexComplete G x Y} := by rw [hQc]; simp
    exact hm
  have hdQ : d ∈ Q ∧ VertexComplete G d Y := by
    have hm : d ∈ {x : V | x ∈ Q ∧ VertexComplete G x Y} := by rw [hQc]; simp
    exact hm
  have heR : e ∈ R ∧ VertexComplete G e Y := by
    have hm : e ∈ {x : V | x ∈ R ∧ VertexComplete G x Y} := by rw [hRc]; simp
    exact hm
  have hgR : g ∈ R ∧ VertexComplete G g Y := by
    have hm : g ∈ {x : V | x ∈ R ∧ VertexComplete G x Y} := by rw [hRc]; simp
    exact hm
  obtain ⟨t, ht, hQt⟩ := adjacent_pair_positions hQ.1 hcQ.1 hdQ.1 hcdadj
  obtain ⟨v, hv, hRv⟩ := adjacent_pair_positions hR.1 heR.1 hgR.1 hegadj
  have hQexact : {x : V | x ∈ Q ∧ VertexComplete G x Y}
      = {Q[t]'(by omega), Q[t + 1]'ht} := by
    rw [hQc]
    rcases hQt with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
  have hRexact : {x : V | x ∈ R ∧ VertexComplete G x Y}
      = {R[v]'(by omega), R[v + 1]'hv} := by
    rw [hRc]
    rcases hRv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
  have hQcomplete : ∀ x ∈ Q, VertexComplete G x Y ↔
      x = Q[t]'(by omega) ∨ x = Q[t + 1]'ht := by
    intro x hx
    have hm := Set.ext_iff.mp hQexact x
    simpa [hx] using hm
  have hRcomplete : ∀ x ∈ R, VertexComplete G x Y ↔
      x = R[v]'(by omega) ∨ x = R[v + 1]'hv := by
    intro x hx
    have hm := Set.ext_iff.mp hRexact x
    simpa [hx] using hm
  have hDcomplete : ∀ x ∈ D, VertexComplete G x Y ↔
      x = Q[t]'(by omega) ∨ x = Q[t + 1]'ht ∨
        x = R[v]'(by omega) ∨ x = R[v + 1]'hv := by
    intro x hxD
    rcases List.mem_append.mp hxD with hxA | hxB
    · rcases List.mem_append.mp hxA with hx | hxQ
      · have hxf : x = f₁ := List.mem_singleton.mp hx
        subst x
        constructor
        · exact fun hc => absurd hc (hSnc f₁ hf₁S)
        · rintro (he | he | he | he)
          · exact absurd (he ▸ List.getElem_mem (by omega)) hf₁Q
          · exact absurd (he ▸ List.getElem_mem ht) hf₁Q
          · exact absurd (he ▸ List.getElem_mem (by omega)) hf₁R
          · exact absurd (he ▸ List.getElem_mem hv) hf₁R
      · rw [hQcomplete x hxQ]
        constructor
        · intro h; rcases h with h | h <;> tauto
        · intro h
          rcases h with h | h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            apply hQRdisj x hxQ
            simpa [h] using (List.getElem_mem (l := R) (i := v) (by omega))
          · exfalso
            apply hQRdisj x hxQ
            simpa [h] using (List.getElem_mem (l := R) (i := v + 1) hv)
    · rcases List.mem_append.mp hxB with hx | hxR
      · have hxf : x = fk := List.mem_singleton.mp hx
        subst x
        constructor
        · exact fun hc => absurd hc (hSnc fk hfkS)
        · rintro (he | he | he | he)
          · exact absurd (he ▸ List.getElem_mem (by omega)) hfkQ
          · exact absurd (he ▸ List.getElem_mem ht) hfkQ
          · exact absurd (he ▸ List.getElem_mem (by omega)) hfkR
          · exact absurd (he ▸ List.getElem_mem hv) hfkR
      · have hxR' : x ∈ R := List.mem_reverse.mp hxR
        rw [hRcomplete x hxR']
        constructor
        · intro h; rcases h with h | h <;> tauto
        · intro h
          rcases h with h | h | h | h
          · exfalso
            apply hQRdisj (Q[t]'(by omega)) (List.getElem_mem (by omega))
            simpa [h] using hxR'
          · exfalso
            apply hQRdisj (Q[t + 1]'ht) (List.getElem_mem ht)
            simpa [h] using hxR'
          · exact Or.inl h
          · exact Or.inr h

  -- Old positions in `D = f₁,Q,fk,Rᵣ`.
  have hD0 : D[0]'(by omega) = f₁ := by
    have h0 : A[0]'(by omega) = f₁ :=
      PathBasics.getElem_zero_of_head? hA.2.1 (by omega)
    simpa only [D, List.getElem_append_left (show 0 < A.length by omega)] using h0
  have hDA : D[A.length]'(by omega) = fk := by
    simp only [D, List.getElem_append_right (le_refl A.length), Nat.sub_self]
    exact PathBasics.getElem_zero_of_head? hB.2.1 (by omega)
  have hDQ : ∀ (u : ℕ) (hu : u < Q.length), D[1 + u]'(by omega) = Q[u]'hu := by
    intro u hu
    rw [show D[1 + u] = A[1 + u] by
      simp only [D]; exact List.getElem_append_left (by omega)]
    have heA := HoleArithmetic.getElem_congr_idx A (by omega) (by omega)
      (show 1 + u = u + 1 by omega)
    have heQ : A[u + 1]'(by omega) = Q[u]'hu := by
      simpa only [A, List.singleton_append] using List.getElem_cons_succ f₁ Q u (by simp; omega)
    exact heA.trans heQ
  have hDR : ∀ (u : ℕ) (hu : u < R.length),
      D[D.length - 1 - u]'(by omega) = R[u]'hu := by
    intro u hu
    have hidx : D.length - 1 - u - A.length = 1 + (R.length - 1 - u) := by
      rw [hDlen, hAlen]
      omega
    rw [show D[D.length - 1 - u] = B[D.length - 1 - u - A.length] by
      simp only [D]; exact List.getElem_append_right (by rw [hDlen, hAlen]; omega)]
    have heB := HoleArithmetic.getElem_congr_idx B (by omega) (by omega) hidx
    have hcomm : 1 + (R.length - 1 - u) = (R.length - 1 - u) + 1 := by omega
    have heB' := HoleArithmetic.getElem_congr_idx B (by omega) (by omega) hcomm
    have hecons : B[(R.length - 1 - u) + 1]'(by omega) =
        R.reverse[R.length - 1 - u]'(by simp; omega) := by
      simpa only [B, List.singleton_append] using
        List.getElem_cons_succ fk R.reverse (R.length - 1 - u) (by simp; omega)
    have herev : R.reverse[R.length - 1 - u]'(by simp; omega) =
        R[R.length - 1 - (R.length - 1 - u)]'(by omega) := List.getElem_reverse (by simp; omega)
    have heidx : R[R.length - 1 - (R.length - 1 - u)]'(by omega) = R[u]'hu :=
      HoleArithmetic.getElem_congr_idx R (by omega) hu (by omega)
    exact heB.trans (heB'.trans (hecons.trans (herev.trans heidx)))

  -- Rotate at the second vertex of the complete edge of `R`.  In the rotated cycle the two
  -- complete pairs occur at the four positions required literally by 15.3.
  let base : ℕ := D.length - 1 - v
  let hh : ℕ := v + 2
  let ii : ℕ := v + t + 3
  let jj : ℕ := v + Q.length + 3
  let E : List V := D.rotate base
  have hbase : base < D.length := by dsimp only [base]; omega
  have hbase0 : 0 < base := by dsimp only [base]; rw [hDlen]; omega
  have hElen : E.length = D.length := by simp [E]
  have hEnd : E.Nodup := by simpa [E] using (List.nodup_rotate.mpr hDnd : (D.rotate base).Nodup)
  have hhh : 1 < hh := by dsimp only [hh]; omega
  have hhii : hh < ii := by dsimp only [hh, ii]; omega
  have hiij : ii + 1 < jj := by dsimp only [ii, jj]; omega
  have hjj : jj < D.length := by dsimp only [jj]; rw [hDlen]; omega
  have hEget : ∀ (z : ℕ) (hz : z < E.length),
      E[z]'hz = D[(z + base) % D.length]'(Nat.mod_lt _ (by omega)) := by
    intro z hz
    simpa only [E] using List.getElem_rotate D base z hz
  have hEold : ∀ (z old : ℕ) (hz : z < E.length) (hold : old < D.length),
      (z + base) % D.length = old → E[z]'hz = D[old]'hold := by
    intro z old hz hold he
    exact (hEget z hz).trans (HoleArithmetic.getElem_congr_idx D (by omega) hold he)

  have hEprev : E[E.length - 1]'(by omega) = R[v + 1]'hv := by
    have hm : (E.length - 1 + base) % D.length = D.length - 2 - v := by
      rw [hElen]
      dsimp only [base]
      rw [show D.length - 1 + (D.length - 1 - v) =
          (D.length - 2 - v) + D.length by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have heidx : D[D.length - 2 - v]'(by omega) =
        D[D.length - 1 - (v + 1)]'(by omega) :=
      HoleArithmetic.getElem_congr_idx D (by omega) (by omega) (by omega)
    exact (hEold _ _ (by omega) (by omega) hm).trans (heidx.trans (hDR (v + 1) hv))
  have hEzero : E[0]'(by omega) = R[v]'(by omega) := by
    have hm : (0 + base) % D.length = D.length - 1 - v := by
      rw [Nat.zero_add]
      exact Nat.mod_eq_of_lt hbase
    exact (hEold _ _ (by omega) (by omega) hm).trans (hDR v (by omega))
  have hEf₁ : E[hh - 1]'(by omega) = f₁ := by
    have hm : (hh - 1 + base) % D.length = 0 := by
      dsimp only [hh, base]
      rw [show v + 2 - 1 + (D.length - 1 - v) = D.length by omega, Nat.mod_self]
    exact (hEold _ 0 (by omega) (by omega) hm).trans hD0
  have hEq0 : E[ii - 1]'(by omega) = Q[t]'(by omega) := by
    have hm : (ii - 1 + base) % D.length = 1 + t := by
      dsimp only [ii, base]
      rw [show v + t + 3 - 1 + (D.length - 1 - v) = (1 + t) + D.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by rw [hDlen]; omega)]
    exact (hEold _ _ (by omega) (by rw [hDlen]; omega) hm).trans (hDQ t (by omega))
  have hEq1 : E[ii]'(by omega) = Q[t + 1]'ht := by
    have hm : (ii + base) % D.length = 1 + (t + 1) := by
      dsimp only [ii, base]
      rw [show v + t + 3 + (D.length - 1 - v) = (1 + (t + 1)) + D.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by rw [hDlen]; omega)]
    exact (hEold _ _ (by omega) (by rw [hDlen]; omega) hm).trans (hDQ (t + 1) ht)
  have hEfk : E[jj - 1]'(by omega) = fk := by
    have hm : (jj - 1 + base) % D.length = A.length := by
      dsimp only [jj, base]
      rw [hAlen]
      rw [show v + Q.length + 3 - 1 + (D.length - 1 - v) =
          (Q.length + 1) + D.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by rw [hDlen]; omega)]
    exact (hEold _ _ (by omega) (by omega) hm).trans hDA

  have rotate_succ : ∀ {a b : ℕ}, a < D.length → b < D.length →
      b = (a + 1) % D.length →
      (b + base) % D.length = (((a + base) % D.length) + 1) % D.length := by
    intro a b ha hb hab
    calc
      (b + base) % D.length = (((a + 1) % D.length) + base) % D.length := by rw [hab]
      _ = (a + 1 + base) % D.length := Nat.mod_add_mod _ _ _
      _ = (a + base + 1) % D.length := by congr 1 <;> omega
      _ = (((a + base) % D.length) + 1) % D.length := (Nat.mod_add_mod _ _ _).symm
  have unrotate_succ : ∀ {a b : ℕ}, a < D.length → b < D.length →
      (b + base) % D.length = (((a + base) % D.length) + 1) % D.length →
      b = (a + 1) % D.length := by
    intro a b ha hb hab
    have hm : base + b ≡ base + (a + 1) [MOD D.length] := by
      rw [Nat.ModEq]
      calc
        (base + b) % D.length = (b + base) % D.length := by rw [Nat.add_comm]
        _ = (((a + base) % D.length) + 1) % D.length := hab
        _ = (a + base + 1) % D.length := Nat.mod_add_mod _ _ _
        _ = (base + (a + 1)) % D.length := by congr 1 <;> omega
    have hc := Nat.ModEq.add_left_cancel' base hm
    rw [Nat.ModEq, Nat.mod_eq_of_lt hb] at hc
    exact hc

  have hEcycle : ∀ (a b : ℕ) (ha : a < E.length) (hb : b < E.length),
      (b = (a + 1) % E.length ∨ a = (b + 1) % E.length) → G.Adj E[a] E[b] := by
    intro a b ha hb hab
    rw [hEget a ha, hEget b hb]
    apply hDcycle
    rw [hElen] at ha hb hab
    rcases hab with hab | hab
    · exact Or.inl (rotate_succ ha hb hab)
    · exact Or.inr (rotate_succ hb ha hab)
  have hEinduced : ∀ (a b : ℕ) (ha : a < E.length) (hb : b < E.length),
      G.Adj E[a] E[b] →
        (b = (a + 1) % E.length ∨ a = (b + 1) % E.length) ∨
          ((a = hh - 1 ∧ b = jj - 1) ∨ (a = jj - 1 ∧ b = hh - 1)) := by
    intro a b ha hb hab
    have haD : a < D.length := by omega
    have hbD : b < D.length := by omega
    have hold := hDinduced ((a + base) % D.length) ((b + base) % D.length)
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (by
        simpa only [hEget a ha, hEget b hb] using hab)
    rcases hold with hold | ⟨ha0, hbA⟩ | ⟨hb0, haA⟩
    · left
      rw [hElen]
      rcases hold with hold | hold
      · exact Or.inl (unrotate_succ haD hbD hold)
      · exact Or.inr (unrotate_succ hbD haD hold)
    · right
      left
      have haf : E[a]'ha = f₁ := by
        exact (hEget a ha).trans
          ((HoleArithmetic.getElem_congr_idx D (by omega) (by omega) ha0).trans hD0)
      have hbf : E[b]'hb = fk := by
        exact (hEget b hb).trans
          ((HoleArithmetic.getElem_congr_idx D (by omega) (by omega) hbA).trans hDA)
      have hai : a = hh - 1 :=
        (List.Nodup.getElem_inj_iff hEnd).mp (haf.trans hEf₁.symm)
      have hbj : b = jj - 1 :=
        (List.Nodup.getElem_inj_iff hEnd).mp (hbf.trans hEfk.symm)
      exact ⟨hai, hbj⟩
    · right
      right
      have hbf : E[b]'hb = f₁ := by
        exact (hEget b hb).trans
          ((HoleArithmetic.getElem_congr_idx D (by omega) (by omega) hb0).trans hD0)
      have haf : E[a]'ha = fk := by
        exact (hEget a ha).trans
          ((HoleArithmetic.getElem_congr_idx D (by omega) (by omega) haA).trans hDA)
      have haj : a = jj - 1 :=
        (List.Nodup.getElem_inj_iff hEnd).mp (haf.trans hEfk.symm)
      have hbi : b = hh - 1 :=
        (List.Nodup.getElem_inj_iff hEnd).mp (hbf.trans hEf₁.symm)
      exact ⟨haj, hbi⟩

  have hDY : ∀ x ∈ D, x ∉ Y := by
    intro x hxD
    rcases List.mem_append.mp hxD with hxA | hxB
    · rcases List.mem_append.mp hxA with hx | hxQ
      · exact hSY x (List.mem_singleton.mp hx ▸ hf₁S)
      · exact hQY x hxQ
    · rcases List.mem_append.mp hxB with hx | hxR
      · exact hSY x (List.mem_singleton.mp hx ▸ hfkS)
      · exact hRY x (List.mem_reverse.mp hxR)
  have hEY : ∀ y ∈ Y, y ∉ E := by
    intro y hy hyE
    exact hDY y (by simpa only [E, List.mem_rotate] using hyE) hy
  have hElast : E[D.length - 1]'(by omega) = R[v + 1]'hv := by
    exact (HoleArithmetic.getElem_congr_idx E (by omega) (by omega) (by omega)).trans hEprev
  have hEYcomplete : ∀ w ∈ E, VertexComplete G w Y ↔
      (w = E[D.length - 1]'(by omega) ∨ w = E[0]'(by omega) ∨
        w = E[ii - 1]'(by omega) ∨ w = E[ii]'(by omega)) := by
    intro w hw
    have hwD : w ∈ D := by simpa only [E, List.mem_rotate] using hw
    rw [hDcomplete w hwD, hElast, hEzero, hEq0, hEq1]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  have hSint : ∀ x ∈ SPGT.interior S, x ∈ S ∧ x ≠ f₁ ∧ x ≠ fk := by
    intro x hx
    have hm := (PathBasics.mem_interior_iff_of_pathFrom hS).mp hx
    exact ⟨hm.1, hm.2.1, hm.2.2⟩
  have hSE : ∀ x ∈ SPGT.interior S, ∀ w ∈ E,
      w ≠ E[hh - 1]'(by omega) → w ≠ E[jj - 1]'(by omega) → ¬ G.Adj x w := by
    intro x hx w hwE hwf hwk hxw
    obtain ⟨hxS, hxf, hxk⟩ := hSint x hx
    have hwD : w ∈ D := by simpa only [E, List.mem_rotate] using hwE
    rcases List.mem_append.mp hwD with hwA | hwB
    · rcases List.mem_append.mp hwA with hw | hwQ
      · apply hwf
        rw [hEf₁]
        exact List.mem_singleton.mp hw
      · rcases (hSQ x hxS w hwQ).mp hxw with ⟨he, -⟩ | ⟨he, -⟩
        · exact hxf he
        · exact hxk he
    · rcases List.mem_append.mp hwB with hw | hwR
      · apply hwk
        rw [hEfk]
        exact List.mem_singleton.mp hw
      · rcases (hSR x hxS w (List.mem_reverse.mp hwR)).mp hxw with ⟨he, -⟩ | ⟨he, -⟩
        · exact hxf he
        · exact hxk he

  have hSF : IsPathFrom G S (E[hh - 1]'(by omega)) (E[jj - 1]'(by omega)) := by
    simpa only [hEf₁, hEfk] using hS
  have hhit : ∃ w ∈ S, VertexComplete G w Y := by
    exact _root_.Workspace.Statements.S15.SPGT.thm_15_3 G hG E D.length hh ii jj
      hElen hD6 hhh hhii hiij hjj hEnd hEcycle hEinduced Y hEY hYanti hEYcomplete S
      hSF hSY hSE
  obtain ⟨x, hxS, hxc⟩ := hhit
  exact hSnc x hxS hxc

end Workspace.ProofLemmas.Thm162ClaimFourHelpers
