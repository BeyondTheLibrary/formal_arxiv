import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S02.Thm_2_1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm46PathPairCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-  The path-pair case of the proof of **4.6**: if `(A₁, B₂)` is a path pair for an
    anticomponent `B₂` of `B` other than the anticomponent `B₁` containing the kernel `W`,
    while `A₁` is balanced with respect to `W` and contains no `W`-complete vertex, a
    contradiction follows.  -/
theorem path_pair_case {G : SimpleGraph V} (hG : Berge G) {A B W A₁ B₁ B₂ : Set V}
    (hAB : IsSkewPartition G A B) (hWanti : AnticonnectedSet G W) (hWB₁ : W ⊆ B₁)
    (hB₁ : IsAnticomponent G B B₁) (hB₂ : IsAnticomponent G B B₂) (hne : B₂ ≠ B₁)
    (hA₁ : IsComponent G A A₁)
    (hnoWcomp : ∀ v ∈ A₁, ¬ VertexComplete G v W)
    (hbal1 : SPGT.Balanced G A₁ W)
    (hpair : IsPathPair G A B A₁ B₂) :
    False := by
  classical
  obtain ⟨-, -, -, P, u, v, hu, hv, huv, hP, hPint, hPodd⟩ := hpair
  have hB₂B₁ : Disjoint B₂ B₁ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hB₂ hB₁ hne
  have huB₁ : u ∉ B₁ := fun hu' => hB₂B₁.le_bot ⟨hu, hu'⟩
  have hvB₁ : v ∉ B₁ := fun hv' => hB₂B₁.le_bot ⟨hv, hv'⟩
  have hucomp : VertexComplete G u W := by
    have h := Workspace.ProofLemmas.LooseSkewPartition.vertexComplete_of_notMem_anticomponent
      hB₁ (hB₂.1 hu) huB₁
    exact fun w hw => h w (hWB₁ hw)
  have hvcomp : VertexComplete G v W := by
    have h := Workspace.ProofLemmas.LooseSkewPartition.vertexComplete_of_notMem_anticomponent
      hB₁ (hB₂.1 hv) hvB₁
    exact fun w hw => h w (hWB₁ hw)
  have hAW : ∀ a ∈ A, a ∉ W := by
    intro a ha haw
    exact Set.disjoint_left.mp hAB.2.1 ha (hB₁.1 (hWB₁ haw))
  have hPW : ∀ z ∈ P, z ∉ W := by
    intro z hz hzW
    by_cases hzint : z ∈ SPGT.interior P
    · exact hAW z (hA₁.1 (hPint z hzint)) hzW
    · have hends := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP).not.mp hzint
      push Not at hends
      by_cases hzu : z = u
      · exact huB₁ (hzu ▸ hWB₁ hzW)
      · exact hvB₁ ((hends hz hzu) ▸ hWB₁ hzW)
  rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG W hWanti P u v hP hPW hPodd
      hucomp hvcomp with hedge | hleap | hanti
  · obtain ⟨x, hx, y, hy, hxy, hxcomp, hycomp⟩ := hedge
    have only_ends : ∀ z ∈ P, VertexComplete G z W → z = u ∨ z = v := by
      intro z hz hzcomp
      by_contra hn
      push Not at hn
      exact hnoWcomp z (hPint z
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP).mpr
          ⟨hz, hn.1, hn.2⟩)) hzcomp
    rcases only_ends x hx hxcomp with rfl | rfl <;>
      rcases only_ends y hy hycomp with rfl | rfl
    · exact G.irrefl hxy
    · exact huv hxy
    · exact huv hxy.symm
    · exact G.irrefl hxy
  · obtain ⟨h5, a, haW, b, hbW, hleap⟩ := hleap
    obtain ⟨hPlist, -, hab, hnab, hAd, hBd⟩ := hleap
    have hlenEq : P.length = pathLength P + 1 :=
      Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hPlist
    have hIP : IsPathFrom G (SPGT.interior P)
        (P[1]'(by omega)) (P[P.length - 2]'(by omega)) :=
      Workspace.ProofLemmas.PathGlue.isPathFrom_interior hPlist (by omega)
    have hsu : G.Adj a (P[1]'(by omega)) :=
      (hAd 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    have htv : G.Adj b (P[P.length - 2]'(by omega)) :=
      (hBd (P.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
    have haP : a ∉ SPGT.interior P :=
      fun ha => hPW a (Workspace.ProofLemmas.PathBasics.interior_subset ha) haW
    have hbP : b ∉ SPGT.interior P :=
      fun hb => hPW b (Workspace.ProofLemmas.PathBasics.interior_subset hb) hbW
    have hsother : ∀ x ∈ SPGT.interior P, x ≠ (P[1]'(by omega)) → ¬ G.Adj a x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
        Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hPlist hx
      have hc := (hAd k hk).mp hadj
      have hkne : k ≠ 1 := by intro he; exact hxne (by subst he; rfl)
      omega
    have htother : ∀ x ∈ SPGT.interior P, x ≠ (P[P.length - 2]'(by omega)) →
        ¬ G.Adj b x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
        Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hPlist hx
      have hc := (hBd k hk).mp hadj
      have hkne : k ≠ P.length - 2 := by intro he; exact hxne (by subst he; rfl)
      omega
    have hnew : IsPathFrom G (a :: (SPGT.interior P ++ [b])) a b :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hIP hsu htv hnab hab
        haP hbP hsother htother
    have hnewlen : pathLength (a :: (SPGT.interior P ++ [b])) = pathLength P := by
      rw [Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton,
        Workspace.ProofLemmas.PathBasics.interior_length]
      simp only [pathLength]
      omega
    have hnewint : SPGT.interior (a :: (SPGT.interior P ++ [b])) = SPGT.interior P := by
      simp [SPGT.interior]
    exact hbal1.1 a b _ haW hbW hnab hnew
      (fun x hx => hPint x (hnewint ▸ hx)) (by rw [hnewlen]; exact hPodd)
  · obtain ⟨h3, c, d, hInt, q, hq, hqodd, hqint⟩ := hanti
    have hc : c ∈ A₁ := hPint c (by rw [hInt]; simp [SPGT.interior])
    have hd : d ∈ A₁ := hPint d (by rw [hInt]; simp [SPGT.interior])
    have hlen : P.length = 4 := by
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at h3
      have := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
      omega
    have hIpath : IsPathList G [c, d] := by
      have h := Workspace.ProofLemmas.PathGlue.isPathFrom_interior hP.1 (by omega)
      rw [hInt] at h
      exact h.1
    have hcd : G.Adj c d := by
      have h := (Workspace.ProofLemmas.PathBasics.path_adj_iff hIpath
        (i := 0) (j := 1) (by simp) (by simp)).mpr (Or.inl rfl)
      simpa using h
    exact hbal1.2 c d q hc hd hcd hq hqint hqodd

end Workspace.ProofLemmas.Thm46PathPairCase
