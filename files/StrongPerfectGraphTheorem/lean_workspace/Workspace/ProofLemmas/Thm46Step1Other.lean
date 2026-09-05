import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm44Reorder
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S04.Thm_4_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm46Step1Other

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-  Statement (1) of the proof of **4.6**, second half: every other component `A'` of `A`
    is balanced with respect to the kernel `W` as well.  -/
theorem balanced_other {G : SimpleGraph V} (hG : Berge G) {A B W A₁ A' : Set V}
    (hAB : IsSkewPartition G A B) (hWB : W ⊆ B) (hWanti : AnticonnectedSet G W)
    (hnl : ¬ IsLooseSkewPartition G A B)
    (hA₁ : IsComponent G A A₁) (hA' : IsComponent G A A')
    (hbal1 : SPGT.Balanced G A₁ W)
    (hpath : ∀ u ∈ W, ∀ v ∈ W, ¬ G.Adj u v →
      (∃ x ∈ A₁, G.Adj u x) → (∃ x ∈ A₁, G.Adj v x) →
      ∃ p : List V, IsPathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ A) ∧
        Even (pathLength p))
    (hcon : ¬ AdmitsBalancedSkewPartition G) :
    SPGT.Balanced G A' W := by
  classical
  by_cases heq : A' = A₁
  · simpa [heq] using hbal1
  have hdisj : Disjoint A' A₁ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.disjoint_of_isComponent G hA' hA₁ heq
  have hanti : Anticomplete G A' A₁ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.anticomplete_of_isComponent G hA' hA₁ heq
  have hnbr : ∀ w ∈ W, ∃ a ∈ A₁, G.Adj w a := by
    intro w hw
    by_contra hn
    push Not at hn
    exact hnl ⟨hAB, Or.inl ⟨w, hWB hw, A₁, hA₁, hn⟩⟩
  have first_clause : ∀ (u v : V) (p : List V), u ∈ W → v ∈ W → ¬ G.Adj u v →
      IsPathFrom G p u v → (∀ x ∈ SPGT.interior p, x ∈ A') →
      ¬ Odd (pathLength p) := by
    intro u v p hu hv huv hp hpint hpodd
    obtain ⟨p', hp', hp'int, hp'even⟩ := hpath u hu v hv huv (hnbr u hu) (hnbr v hv)
    exact hcon (Workspace.Statements.S04.SPGT.thm_4_3 G hG A B hAB
      (Or.inl ⟨u, v, p, p', hWB hu, hWB hv, hp,
        (fun x hx => hA'.1 (hpint x hx)), hpodd, hp', hp'int, hp'even⟩)).2
  refine ⟨first_clause, ?_⟩
  intro u v q hu hv huv hq hqint hqodd
  have huA₁ : u ∉ A₁ := fun h => hdisj.le_bot ⟨hu, h⟩
  have hvA₁ : v ∉ A₁ := fun h => hdisj.le_bot ⟨hv, h⟩
  have hne1 : pathLength q ≠ 1 := by
    intro h1
    exact ((SimpleGraph.compl_adj G u v).mp
      (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hq h1)).2 huv
  have hne3 : pathLength q ≠ 3 := by
    intro h3
    obtain ⟨x, y, hxyc, hx, hy, hnew⟩ :=
      Workspace.ProofLemmas.Thm44Reorder.antipath_of_path_three (G := Gᶜ) hq h3
    have hxy : ¬ G.Adj x y := (SimpleGraph.compl_adj G x y).mp hxyc |>.2
    have hnew' : IsPathFrom G [x, v, u, y] x y :=
      Workspace.ProofLemmas.PathBasics.isAntipathFrom_compl.mp hnew
    exact first_clause x y [x, v, u, y] (hqint x hx) (hqint y hy) hxy hnew'
      (by
        intro z hz
        simp [SPGT.interior] at hz
        rcases hz with rfl | rfl
        · exact hv
        · exact hu)
      ⟨1, rfl⟩
  have h5 : 5 ≤ pathLength q := by
    obtain ⟨k, hk⟩ := hqodd
    omega
  have hqA₁ : ∀ z ∈ q, z ∉ A₁ := by
    intro z hz hzA₁
    by_cases hzint : z ∈ SPGT.interior q
    · exact Set.disjoint_left.mp hAB.2.1 (hA₁.1 hzA₁) (hWB (hqint z hzint))
    · have hends := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).not.mp hzint
      push Not at hends
      by_cases hzu : z = u
      · exact huA₁ (hzu ▸ hzA₁)
      · exact hvA₁ ((hends hz hzu) ▸ hzA₁)
  have hucomp : VertexComplete Gᶜ u A₁ := by
    intro a ha
    rw [SimpleGraph.compl_adj]
    exact ⟨fun e => huA₁ (e ▸ ha), hanti u hu a ha⟩
  have hvcomp : VertexComplete Gᶜ v A₁ := by
    intro a ha
    rw [SimpleGraph.compl_adj]
    exact ⟨fun e => hvA₁ (e ▸ ha), hanti v hv a ha⟩
  have hnotcomp : ∀ z ∈ SPGT.interior q, ¬ VertexComplete Gᶜ z A₁ := by
    intro z hz hzcomp
    obtain ⟨a, ha, hza⟩ := hnbr z (hqint z hz)
    exact ((SimpleGraph.compl_adj G z a).mp (hzcomp a ha)).2 hza
  have hA₁anti : AnticonnectedSet Gᶜ A₁ := by
    simpa only [AnticonnectedSet, compl_compl] using hA₁.2.1
  have hnuv : ¬ Gᶜ.Adj u v := fun h => ((SimpleGraph.compl_adj G u v).mp h).2 huv
  rcases Workspace.Statements.S02.SPGT.thm_2_1 Gᶜ
      (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) A₁ hA₁anti q u v hq
      hqA₁ hqodd hucomp hvcomp with hedge | hleap | hshort
  · obtain ⟨x, hx, y, hy, hxy, hxcomp, hycomp⟩ := hedge
    have only_ends : ∀ z ∈ q, VertexComplete Gᶜ z A₁ → z = u ∨ z = v := by
      intro z hz hzcomp
      by_contra hn
      push Not at hn
      exact hnotcomp z
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).mpr
          ⟨hz, hn.1, hn.2⟩) hzcomp
    rcases only_ends x hx hxcomp with rfl | rfl <;>
      rcases only_ends y hy hycomp with rfl | rfl
    · exact Gᶜ.irrefl hxy
    · exact hnuv hxy
    · exact hnuv hxy.symm
    · exact Gᶜ.irrefl hxy
  · obtain ⟨-, a, ha, b, hb, hleap⟩ := hleap
    obtain ⟨hqlist, -, hab, hnab, hAd, hBd⟩ := hleap
    have hlenEq : q.length = pathLength q + 1 :=
      Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hqlist
    have hIP : IsPathFrom Gᶜ (SPGT.interior q)
        (q[1]'(by omega)) (q[q.length - 2]'(by omega)) :=
      Workspace.ProofLemmas.PathGlue.isPathFrom_interior hqlist (by omega)
    have hsu : Gᶜ.Adj a (q[1]'(by omega)) :=
      (hAd 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    have htv : Gᶜ.Adj b (q[q.length - 2]'(by omega)) :=
      (hBd (q.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
    have haQ : a ∉ SPGT.interior q :=
      fun ha' => hqA₁ a (Workspace.ProofLemmas.PathBasics.interior_subset ha') ha
    have hbQ : b ∉ SPGT.interior q :=
      fun hb' => hqA₁ b (Workspace.ProofLemmas.PathBasics.interior_subset hb') hb
    have hsother : ∀ x ∈ SPGT.interior q, x ≠ (q[1]'(by omega)) →
        ¬ Gᶜ.Adj a x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
        Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hqlist hx
      have hc := (hAd k hk).mp hadj
      have hkne : k ≠ 1 := by intro he; exact hxne (by subst he; rfl)
      omega
    have htother : ∀ x ∈ SPGT.interior q, x ≠ (q[q.length - 2]'(by omega)) →
        ¬ Gᶜ.Adj b x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
        Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hqlist hx
      have hc := (hBd k hk).mp hadj
      have hkne : k ≠ q.length - 2 := by intro he; exact hxne (by subst he; rfl)
      omega
    have hnew : IsAntipathFrom G (a :: (SPGT.interior q ++ [b])) a b :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hIP hsu htv hnab hab
        haQ hbQ hsother htother
    have hnewlen : pathLength (a :: (SPGT.interior q ++ [b])) = pathLength q := by
      rw [Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton,
        Workspace.ProofLemmas.PathBasics.interior_length]
      simp only [pathLength]
      omega
    have hnewint : SPGT.interior (a :: (SPGT.interior q ++ [b])) = SPGT.interior q := by
      simp [SPGT.interior]
    have habG : G.Adj a b := by
      by_contra hn
      exact hnab ((SimpleGraph.compl_adj G a b).mpr ⟨hab, hn⟩)
    exact hbal1.2 a b _ ha hb habG hnew
      (fun x hx => hqint x (hnewint ▸ hx)) (by rw [hnewlen]; exact hqodd)
  · exact absurd hshort.1 (by omega)

end Workspace.ProofLemmas.Thm46Step1Other
