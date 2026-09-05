import Workspace.ProofLemmas.Thm192Claim7GapCatch
import Workspace.ProofLemmas.ReflectionAntihole

/-! The reflection exclusion in both cases of claim (7) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim7GapReflection

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio.SPGT Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (claim (7)): "By 15.7, it contains no reflection of the triangle,
since as before that would give an antihole of length 6 with three vertices in `C`."
Here `a,b` lie on `C`, and the unique neighbour `q` of `b` in the catching set
also lies on `C`. -/
theorem no_reflection {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} (hC : IsHoleList G C) (hClen : 4 < holeLength C)
    {a b y q : V} {F : Set V} (haC : a ∈ C) (hbC : b ∈ C) (hqC : q ∈ C)
    (hab : a ≠ b) (haq : a ≠ q) (hbq : b ≠ q)
    (huniq : ∀ v ∈ F, G.Adj b v → v = q) :
    ¬ ∃ a₁ a₂ a₃ b₁ b₂ b₃ : V, ({a,b,y} : Set V) = {a₁,a₂,a₃} ∧
      ({b₁,b₂,b₃} : Set V) ⊆ F ∧ IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃ := by
  rintro ⟨a₁, a₂, a₃, b₁, b₂, b₃, hT, hBF, hR⟩
  have hD := ReflectionAntihole.isAntiholeList_of_reflection hR
  have hmemT : ∀ v ∈ ({a₁,a₂,a₃} : Set V), v ∈ [a₁,b₂,a₃,b₁,a₂,b₃] := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv | hv <;> simp [hv]
  have hmemB : ∀ v ∈ ({b₁,b₂,b₃} : Set V), v ∈ [a₁,b₂,a₃,b₁,a₂,b₃] := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv | hv <;> simp [hv]
  have hbT : b ∈ ({a₁,a₂,a₃} : Set V) := by rw [← hT]; simp
  have hbmate : ∃ v ∈ ({b₁,b₂,b₃} : Set V), G.Adj b v := by
    rcases hbT with hb | hb | hb
    · refine ⟨b₁, by simp, (hR.2.2.2 b (by simp [hb]) b₁ (by simp)).mpr ?_⟩
      exact Or.inl ⟨hb, rfl⟩
    · refine ⟨b₂, by simp, (hR.2.2.2 b (by simp [hb]) b₂ (by simp)).mpr ?_⟩
      exact Or.inr (Or.inl ⟨hb, rfl⟩)
    · refine ⟨b₃, by simp, (hR.2.2.2 b (by simp [hb]) b₃ (by simp)).mpr ?_⟩
      exact Or.inr (Or.inr ⟨hb, rfl⟩)
  obtain ⟨v, hv, hbv⟩ := hbmate
  have hqB : q ∈ ({b₁,b₂,b₃} : Set V) := huniq v (hBF hv) hbv ▸ hv
  have hsub : ({a,b,q} : Set V) ⊆
      {v : V | v ∈ C} ∩ {v : V | v ∈ [a₁,b₂,a₃,b₁,a₂,b₃]} := by
    intro v hv
    rcases hv with hv | hv | hv
    · rw [hv]
      exact ⟨haC, hmemT a (by rw [← hT]; simp)⟩
    · rw [hv]
      exact ⟨hbC, hmemT b (by rw [← hT]; simp)⟩
    · rw [hv]
      exact ⟨hqC, hmemB q hqB⟩
  have h3 : ({a,b,q} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, haq]), Set.ncard_pair hbq]
  have hcard := Workspace.Statements.S15.SPGT.thm_15_7 G hG C _ hC hClen hD (by simp [holeLength])
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- With unique neighbours `u,q` for the first two triangle vertices, and no
reflection, 17.1 forces the third triangle vertex to see `u` or `q`. -/
theorem catches_forces_contact {G : SimpleGraph V} (hG : InF7 G)
    {a b y u q : V} {F : Set V} (hcatch : Catches G F ({a,b,y} : Set V))
    (huniqA : ∀ v ∈ F, G.Adj a v → v = u)
    (huniqB : ∀ v ∈ F, G.Adj b v → v = q) (huq : u ≠ q)
    (hnoR : ¬ ∃ a₁ a₂ a₃ b₁ b₂ b₃ : V, ({a,b,y} : Set V) = {a₁,a₂,a₃} ∧
      ({b₁,b₂,b₃} : Set V) ⊆ F ∧ IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃) :
    G.Adj y u ∨ G.Adj y q := by
  rcases Workspace.Statements.S17.SPGT.thm_17_1 G hG _ hcatch.1 F
    (fun v hv hvT => Set.disjoint_left.mp hcatch.2.2.1 hv hvT) hcatch with hR | ⟨v, hv, htwo⟩
  · exact (hnoR hR).elim
  · by_contra hn
    push Not at hn
    obtain ⟨r, hr, s, hs, hrs⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp htwo
    have hrT : r = a ∨ r = b ∨ r = y := hr.2
    have hsT : s = a ∨ s = b ∨ s = y := hs.2
    have hrv : G.Adj r v := hr.1.symm
    have hsv : G.Adj s v := hs.1.symm
    rcases hrT with hr | hr | hr <;> rcases hsT with hs | hs | hs
    all_goals rw [hr] at hrv
    all_goals rw [hs] at hsv
    all_goals first
      | exact hrs (hr.trans hs.symm)
      | exact huq ((huniqA v hv hrv).symm.trans (huniqB v hv hsv))
      | exact huq ((huniqA v hv hsv).symm.trans (huniqB v hv hrv))
      | exact hn.1 (huniqA v hv hrv ▸ hsv)
      | exact hn.1 (huniqA v hv hsv ▸ hrv)
      | exact hn.2 (huniqB v hv hrv ▸ hsv)
      | exact hn.2 (huniqB v hv hsv ▸ hrv)

/-- PAPER (claim (7)): "Now `{x₂,p₁,…,pₙ}` is connected and catches the
triangle `{z,x₁,y}`. ... So by 17.1 ... `y` is adjacent to `pₙ`."
Before assuming `x₂y` is a nonedge, the conclusion allows that edge as well. -/
theorem right_contact {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y) (hyz : G.Adj y z)
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1)) (hP5 : 5 ≤ P.length)
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hx21 : ¬ G.Adj (x 2) (x 1))
    (hboth : (∃ w ∈ SPGT.interior P, G.Adj (x 2) w) ∧
      (∃ w ∈ SPGT.interior P, G.Adj y w)) :
    G.Adj y (x 2) ∨ G.Adj y (P[P.length - 2]'(by omega)) := by
  let q := P[P.length - 2]'(by omega)
  have hqI : q ∈ SPGT.interior P :=
    PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)
  have hqP := PathBasics.interior_subset hqI
  obtain ⟨hzP, hx2P, hC, _⟩ := Thm192Claim6Basics.path_facts hG.1.1.1.1 hws
    Set.Subset.rfl hP hPI (by omega)
  have hYout := Thm192Claim6Basics.Y_disjoint_path hHyp Set.Subset.rfl hP hPI
  have hzb := hws.2.2.2.2.2.2 1 (by omega)
  have hby := hHyp.2.2.2.1 y hyY
  have hbq : G.Adj (x 1) q := by
    change G.Adj (x 1) (P[P.length - 2]'(by omega))
    rw [← PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)]
    exact (PathBasics.path_adj_iff hP.1 (by omega) (by omega)).mpr (by omega)
  let F : Set V := {v | v ∈ SPGT.interior P} ∪ {x 2}
  have hIconn : ConnectedSet G {v | v ∈ SPGT.interior P} := by
    rw [PathBasics.interior_eq_drop_take]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain
      (((InducedPathExtraction.isChain_of_isPathList hP.1).drop 1).take (P.length - 2))
  have hFconn : ConnectedSet G F := ConnectedSetUnionAttach.connectedSet_union_singleton hIconn hboth.1
  have hT : IsTriangle G ({z, x 1, y} : Set V) := by
    refine ⟨?_, ?_⟩
    · rw [Set.ncard_insert_of_notMem (by simp [hzb.ne, hyz.ne.symm]), Set.ncard_pair hby.ne]
    · intro a ha b hb hab
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      all_goals first | exact (hab rfl).elim | assumption | exact hzb.symm | exact hyz.symm | exact hby.symm
  have hdisj : Disjoint F ({z,x 1,y} : Set V) := by
    apply Set.disjoint_left.mpr
    intro v hv hvT
    rcases hv with hv | hv
    · have hvP := PathBasics.interior_subset hv
      rcases hvT with hvz | hvb | hvy
      · exact hzP (hvz ▸ hvP)
      · exact ((PathBasics.mem_interior_iff_of_pathFrom hP).mp hv).2.2 hvb
      · exact hYout v hvP (hvy ▸ hyY)
    · have hv2 : v = x 2 := hv
      rw [hv2] at hvT
      rcases hvT with hvz | hvb | hvy
      · exact (hws.2.2.1 2 le_rfl).2 hvz
      · have := hws.2.1 2 le_rfl 1 (by omega) hvb
        omega
      · exact (hHyp.1 y hyY).2.2.2 hvy.symm
  have hcatch : Catches G F ({z,x 1,y} : Set V) := by
    refine ⟨hT, hFconn, hdisj, ?_⟩
    intro v hv
    rcases hv with hv | hv | hv
    · rw [hv]
      exact ⟨x 2, Or.inr rfl, hws.2.2.2.2.2.2 2 le_rfl⟩
    · rw [hv]
      exact ⟨q, Or.inl hqI, hbq⟩
    · rw [hv]
      obtain ⟨w, hw, hyw⟩ := hboth.2
      exact ⟨w, Or.inl hw, hyw⟩
  have huniqA : ∀ v ∈ F, G.Adj z v → v = x 2 := by
    intro v hv hzv
    rcases hv with hv | hv
    · exact (wheelSystemA_no_z v (hPI v hv) hzv).elim
    · exact hv
  have huniqB : ∀ v ∈ F, G.Adj (x 1) v → v = q := by
    intro v hv hbv
    rcases hv with hv | hv
    · obtain ⟨k, hk, hk1, hkn, hkv⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hv
      have hlast := PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
      have hadj : G.Adj (P[P.length-1]'(by omega)) (P[k]'hk) := by rwa [hlast, hkv]
      have hkq : k = P.length - 2 := by
        have := (PathBasics.path_adj_iff hP.1 (by omega) hk).mp hadj
        omega
      exact hkv.symm.trans (hP.1.2.1.getElem_inj_iff.mpr hkq)
    · exact (hx21 (hv ▸ hbv.symm)).elim
  apply catches_forces_contact hG hcatch huniqA huniqB
    (fun he => hx2P (he ▸ hqP))
  apply no_reflection hG.1 hC (by simp only [holeLength, List.length_cons]; omega)
    (by simp) (by simp [PathBasics.getLast_mem hP.2.2]) (by simp [hqP])
    hzb.ne (fun he => hzP (he ▸ hqP)) hbq.ne huniqB

end Workspace.ProofLemmas.Thm192Claim7GapReflection
