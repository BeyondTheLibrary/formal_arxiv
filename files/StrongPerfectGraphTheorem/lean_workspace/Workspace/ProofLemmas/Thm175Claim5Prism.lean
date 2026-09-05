import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.Types.Classes

/-! The long prism at the end of the proof of 17.5 (5). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim5Prism

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "But then the three paths `p₁-x₁`, `x₂-z`, `p₂-⋯-p_d-y₁`
form a long prism, a contradiction." -/
theorem contradiction (G : SimpleGraph V) (hG : InF5 G)
    (P : List V) (p₁ pₙ x₁ x₂ y z : V) (hP : IsPathFrom G P p₁ pₙ)
    (h1 : 1 < P.length) (hx₁P : x₁ ∉ P) (hx₂P : x₂ ∉ P)
    (hyP : y ∉ P) (hzP : z ∉ P)
    (hnodup : [x₁, x₂, y, z].Nodup)
    (hx₁x₂ : ¬ G.Adj x₁ x₂) (hx₂y : ¬ G.Adj x₂ y)
    (hx₁y : G.Adj x₁ y) (hzx₁ : G.Adj z x₁)
    (hzx₂ : G.Adj z x₂) (hzy : G.Adj z y)
    (hx₁only : ∀ v ∈ P, G.Adj x₁ v ↔ v = p₁)
    (hx₂only : ∀ v ∈ P, G.Adj x₂ v ↔ v = p₁ ∨ v = P[1]'h1)
    (hzanti : VertexAnticomplete G z {v | v ∈ P})
    (d : ℕ) (hd : d < P.length) (hd2 : 2 ≤ d) (hdy : G.Adj y (P[d]'hd))
    (hybefore : ∀ i (hi : i < P.length), i < d → ¬ G.Adj y (P[i]'hi)) : False := by
  let p₂ := P[1]'h1
  let T := (P.drop 1).take (d - 1 + 1)
  let R := T ++ [y]
  have hp₁P := PathBasics.head_mem hP.2.1
  have hp₂P : p₂ ∈ P := List.getElem_mem h1
  have hp0 := PathBasics.getElem_zero_of_head? hP.2.1 (show 0 < P.length by omega)
  have hp₁p₂ : G.Adj p₁ p₂ := by
    have ha := PathBasics.path_adj_succ hP.1 (i := 0) h1
    simpa only [hp0] using ha
  have ht := PathBasics.isPathFrom_slice hP.1 (show 1 < d by omega) hd
  have hTsub : ∀ v ∈ T, v ∈ P := fun v hv => List.drop_subset _ _ (List.take_subset _ _ hv)
  have hp₁notT : p₁ ∉ T := by
    intro hm
    obtain ⟨i, hi, h1i, -, he⟩ := (PathBasics.mem_slice_iff P (by omega) hd).mp hm
    have := hP.1.2.1.getElem_inj_iff.mp (he.trans hp0.symm)
    omega
  have hR : IsPathFrom G R p₂ y := by
    apply PathAttach.isPathFrom_concat ht hdy
    · exact fun hy => hyP (hTsub y hy)
    · intro v hv hne ha
      obtain ⟨i, hi, -, hid, rfl⟩ := (PathBasics.mem_slice_iff P (by omega) hd).mp hv
      have hine : i ≠ d := by intro he; subst i; exact hne rfl
      exact hybefore i hi (by omega) ha
  have p₁ne (v : V) (hv : v ∉ P) : p₁ ≠ v := fun he => hv (he ▸ hp₁P)
  have p₂ne (v : V) (hv : v ∉ P) : p₂ ≠ v := fun he => hv (he ▸ hp₂P)
  have hx₂x₁ : x₂ ≠ x₁ := by
    have hn := (List.nodup_cons.mp hnodup).1
    intro he
    exact hn (by simp [he])
  have hx₂yNe : x₂ ≠ y := by
    have hn := (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
    intro he
    exact hn (by simp [he])
  have hz₂ : x₂ ≠ z := hzx₂.ne.symm
  have hxyNe : x₁ ≠ y := hx₁y.ne
  have hy₁ : ¬ G.Adj p₁ y := by
    intro ha
    exact hybefore 0 (by omega) (by omega) (by simpa only [hp0] using ha.symm)
  have hp₁R : ∀ v ∈ R, G.Adj p₁ v ↔ v = p₂ := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨i, hi, -, -, rfl⟩ := (PathBasics.mem_slice_iff P (by omega) hd).mp hv
      constructor
      · intro ha
        rw [← hp0] at ha
        have hh := (PathBasics.path_adj_iff hP.1 (by omega) hi).mp ha
        have hi1 : i = 1 := by omega
        subst i
        rfl
      · intro he
        rw [he]
        exact hp₁p₂
    · have he : v = y := by simpa using hv
      subst v
      exact iff_of_false hy₁ (p₂ne y hyP).symm
  have hx₁R : ∀ v ∈ R, G.Adj x₁ v ↔ v = y := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact iff_of_false
        (fun ha => hp₁notT ((hx₁only v (hTsub v hv)).mp ha ▸ hv))
        (fun he => hyP (he ▸ hTsub v hv))
    · have he : v = y := by simpa using hv
      subst v
      exact iff_of_true hx₁y rfl
  have hx₂R : ∀ v ∈ R, G.Adj x₂ v ↔ v = p₂ := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · rw [hx₂only v (hTsub v hv)]
      exact or_iff_right (fun he => hp₁notT (he ▸ hv))
    · have he : v = y := by simpa using hv
      subst v
      exact iff_of_false hx₂y (p₂ne y hyP).symm
  have hzR : ∀ v ∈ R, G.Adj z v ↔ v = y := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact iff_of_false (hzanti v (hTsub v hv)) (fun he => hyP (he ▸ hTsub v hv))
    · have he : v = y := by simpa using hv
      subst v
      exact iff_of_true hzy rfl
  have hp₁x₁ : G.Adj p₁ x₁ := ((hx₁only p₁ hp₁P).mpr rfl).symm
  have hp₁x₂ : G.Adj p₁ x₂ := ((hx₂only p₁ hp₁P).mpr (Or.inl rfl)).symm
  have hp₂x₂ : G.Adj p₂ x₂ := ((hx₂only p₂ hp₂P).mpr (Or.inr rfl)).symm
  have hp₁z : ¬ G.Adj p₁ z := fun ha => hzanti p₁ hp₁P ha.symm
  have he12 : ∀ u ∈ [p₁, x₁], ∀ v ∈ [x₂, z],
      G.Adj u v ↔ (u = p₁ ∧ v = x₂) ∨ (u = x₁ ∧ v = z) := by
    intro u hu v hv
    have hu' : u = p₁ ∨ u = x₁ := by simpa using hu
    have hv' : v = x₂ ∨ v = z := by simpa using hv
    rcases hu' with hu' | hu' <;> subst u <;>
      rcases hv' with hv' | hv' <;> subst v <;>
      simp [hp₁x₂, hp₁z, hx₁x₂, hzx₁.symm, p₁ne x₁ hx₁P,
        (p₁ne x₁ hx₁P).symm, hz₂, hz₂.symm]
  have he13 : ∀ u ∈ [p₁, x₁], ∀ v ∈ R,
      G.Adj u v ↔ (u = p₁ ∧ v = p₂) ∨ (u = x₁ ∧ v = y) := by
    intro u hu v hv
    have hu' : u = p₁ ∨ u = x₁ := by simpa using hu
    rcases hu' with hu' | hu' <;> subst u
    · simpa [p₁ne x₁ hx₁P] using hp₁R v hv
    · simpa [(p₁ne x₁ hx₁P).symm] using hx₁R v hv
  have he23 : ∀ u ∈ [x₂, z], ∀ v ∈ R,
      G.Adj u v ↔ (u = x₂ ∧ v = p₂) ∨ (u = z ∧ v = y) := by
    intro u hu v hv
    have hu' : u = x₂ ∨ u = z := by simpa using hu
    rcases hu' with hu' | hu' <;> subst u
    · simpa [hz₂] using hx₂R v hv
    · simpa [hz₂.symm] using hzR v hv
  have hp : FormPrism G ![p₁, x₂, p₂] ![x₁, z, y] [p₁, x₁] [x₂, z] R :=
    PrismBasics.formPrism_of_data hp₁x₂ hp₁p₂ hp₂x₂.symm
      hzx₁.symm hx₁y hzy (p₁ne x₁ hx₁P) (p₁ne z hzP) (p₁ne y hyP)
      hx₂x₁ hz₂ hx₂yNe (p₂ne x₁ hx₁P) (p₂ne z hzP) (p₂ne y hyP)
      ⟨PathBasics.isPathList_pair hp₁x₁, rfl, rfl⟩
      ⟨PathBasics.isPathList_pair hzx₂.symm, rfl, rfl⟩ hR he12 he13 he23
  apply hG.2.1
  refine ⟨_, _, _, _, R, hp, Or.inr (Or.inr ?_)⟩
  have hTlen := PathBasics.length_slice P (show 1 ≤ d by omega) hd
  change 1 < (T ++ [y]).length - 1
  simp only [List.length_append, List.length_singleton]
  change 1 < T.length + 1 - 1
  change ((P.drop 1).take (d - 1 + 1)).length = _ at hTlen
  dsimp [T]
  rw [hTlen]
  omega

end Workspace.ProofLemmas.Thm175Claim5Prism
