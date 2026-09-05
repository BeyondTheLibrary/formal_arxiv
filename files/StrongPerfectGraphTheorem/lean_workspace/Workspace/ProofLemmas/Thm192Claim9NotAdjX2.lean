import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.Thm192Claim3
import Workspace.ProofLemmas.Thm192Claim7
import Workspace.ProofLemmas.Thm192Claim8
import Workspace.ProofLemmas.Thm192Claim9MinimalityWitness
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.FiveHoleBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.ReflectionAntihole
import Workspace.Statements.S17.Thm_17_1
import Workspace.Statements.S17.Thm_17_3

/-!
# Claim (9) of the printed proof of 19.2, in the case `¬ G.Adj (x 2) y`

This is the printed proof of claim (9) verbatim, with its standing hypothesis
*"`y` is not adjacent to `x₂`"* — which the printed text derives from the minimality of
its own choice of `A` — carried as the explicit hypothesis `h2y`.  It is the whole of
`Thm192Claim9.claim9` except for the case `G.Adj (x 2) y`, which
`Thm192Claim9YAdjX2` handles; splitting it off into this file (which does not depend on
`Thm192Claim9`) lets `Thm192Claim9YAdjX2` use claim (9) itself for a *different* vertex of
the hub, namely one that is nonadjacent to `x₂`.

The docstring of `Thm192Claim9.claim9` documents the argument; nothing below is new.
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim9NotAdjX2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.ProofLemmas

/-- A five-element list with exactly its four consecutive edges is an induced path. -/
private theorem isPathList_five {G : SimpleGraph V} {a b c d e : V}
    (hnd : [a, b, c, d, e].Nodup)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d e)
    (n1 : ¬ G.Adj a c) (n2 : ¬ G.Adj a d) (n3 : ¬ G.Adj a e)
    (n4 : ¬ G.Adj b d) (n5 : ¬ G.Adj b e) (n6 : ¬ G.Adj c e) :
    IsPathList G [a, b, c, d, e] := by
  have key : ∀ i j : ℕ, i < 5 → j < 5 →
      ∀ (hi : i < [a, b, c, d, e].length) (hj : j < [a, b, c, d, e].length),
        (G.Adj ([a, b, c, d, e][i]'hi) ([a, b, c, d, e][j]'hj) ↔
          (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi5 hj5
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true h1 (by first | omega | simp | tauto)
      | exact iff_of_true h2 (by first | omega | simp | tauto)
      | exact iff_of_true h3 (by first | omega | simp | tauto)
      | exact iff_of_true h4 (by first | omega | simp | tauto)
      | exact iff_of_true h1.symm (by first | omega | simp | tauto)
      | exact iff_of_true h2.symm (by first | omega | simp | tauto)
      | exact iff_of_true h3.symm (by first | omega | simp | tauto)
      | exact iff_of_true h4.symm (by first | omega | simp | tauto)
      | exact iff_of_false n1 (by first | omega | simp | tauto)
      | exact iff_of_false n2 (by first | omega | simp | tauto)
      | exact iff_of_false n3 (by first | omega | simp | tauto)
      | exact iff_of_false n4 (by first | omega | simp | tauto)
      | exact iff_of_false n5 (by first | omega | simp | tauto)
      | exact iff_of_false n6 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n2 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n3 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n4 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n5 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n6 h.symm) (by first | omega | simp | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩

private theorem triple_distinct {a b c : V} (h : ({a, b, c} : Set V).ncard = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have pair_le : ∀ p q : V, ({p, q} : Set V).ncard ≤ 2 := by
    intro p q
    have hh := Set.ncard_insert_le p ({q} : Set V)
    simpa using hh
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have he : ({a, a, c} : Set V) = {a, c} := by ext; simp
    rw [he] at h
    exact (by have := pair_le a c; omega)
  · have he : ({a, b, a} : Set V) = {a, b} := by ext; simp; tauto
    rw [he] at h
    exact (by have := pair_le a b; omega)
  · have he : ({a, b, b} : Set V) = {a, b} := by ext; simp
    rw [he] at h
    exact (by have := pair_le a b; omega)

/-- Every vertex of the first triangle has its matched vertex in a reflection, and it has
no other neighbour in the reflected triangle. -/
private theorem reflection_partner {G : SimpleGraph V} {a₀ a₁ a₂ b₀ b₁ b₂ u : V}
    (h : IsReflectionOfTriangle G a₀ a₁ a₂ b₀ b₁ b₂)
    (hu : u ∈ ({a₀, a₁, a₂} : Set V)) :
    ∃ v ∈ ({b₀, b₁, b₂} : Set V), G.Adj u v ∧
      ∀ w ∈ ({a₀, a₁, a₂} : Set V), w ≠ u → ¬ G.Adj w v := by
  obtain ⟨hb₀₁, hb₀₂, hb₁₂⟩ := triple_distinct h.2.1.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · refine ⟨b₀, by simp, (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₀ (by simp)).mp hadj with hw | hw | hw
    · exact hne hw.1
    · exact hb₀₁ hw.2
    · exact hb₀₂ hw.2
  · refine ⟨b₁, by simp,
      (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₁ (by simp)).mp hadj with hw | hw | hw
    · exact hb₀₁ hw.2.symm
    · exact hne hw.1
    · exact hb₁₂ hw.2
  · refine ⟨b₂, by simp,
      (h.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    intro w hw hne hadj
    rcases (h.2.2.2 w hw b₂ (by simp)).mp hadj with hw | hw | hw
    · exact hb₀₂ hw.2.symm
    · exact hb₁₂ hw.2.symm
    · exact hne hw.1

/-- The application of 17.1 used twice in claim (9).  The vertices `x₂` and `f` are the
partners of `z` and `y`, so the third partner lies in `A \ {f}` and is adjacent to both. -/
private theorem endpoint_reflection (G : SimpleGraph V) (hG : InF7 G)
    (z y x₂ a b f : V) (A : Set V)
    (hzx₂ : G.Adj z x₂) (hzy : G.Adj z y) (hza : G.Adj z a)
    (hya : G.Adj y a) (hyb : G.Adj y b) (hyx₂ : ¬ G.Adj y x₂)
    (hx₂a : ¬ G.Adj x₂ a) (hfa : ¬ G.Adj f a)
    (hfA : f ∈ A) (hyf : G.Adj y f) (hx₂f : G.Adj x₂ f)
    (hyuniq : ∀ g ∈ A, G.Adj y g → g = f)
    (hAconn : ConnectedSet G A) (haA : ∃ g ∈ A, G.Adj a g)
    (hzA : ∀ g ∈ A, ¬ G.Adj z g) (hznotA : z ∉ A)
    (hnoc : ∀ g ∈ A, ¬ (G.Adj g a ∧ G.Adj g b))
    (hzne_y : z ≠ y) (hzne_a : z ≠ a) (hyne_a : y ≠ a)
    (hx₂ne_z : x₂ ≠ z) (hx₂ne_y : x₂ ≠ y) (hx₂ne_a : x₂ ≠ a) :
    ∃ g ∈ A \ {f}, G.Adj a g ∧ G.Adj x₂ g ∧ G.Adj f g ∧
      ¬ G.Adj y g ∧ ¬ G.Adj b g := by
  classical
  let T : Set V := {z, y, a}
  let F : Set V := A ∪ {x₂}
  have htri : IsTriangle G T := by
    refine ⟨Set.ncard_eq_three.mpr ⟨z, y, a, hzne_y, hzne_a, hyne_a, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact hzy
    · exact hza
    · exact hzy.symm
    · exact (huv rfl).elim
    · exact hya
    · exact hza.symm
    · exact hya.symm
    · exact (huv rfl).elim
  have hyA : y ∉ A := by
    intro hyA
    exact hnoc y hyA ⟨hya, hyb⟩
  have ha_notA : a ∉ A := fun ha => hzA a ha hza
  have hFsub : F ⊆ Tᶜ := by
    intro g hgF hgT
    rcases hgF with hgA | hg2
    · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hgT
      rcases hgT with h | h | h
      · exact hznotA (h ▸ hgA)
      · exact hyA (h ▸ hgA)
      · exact ha_notA (h ▸ hgA)
    · have hg : g = x₂ := by simpa using hg2
      subst g
      simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hgT
      rcases hgT with h | h | h
      · exact hx₂ne_z h
      · exact hx₂ne_y h
      · exact hx₂ne_a h
  have hFconn : ConnectedSet G F := by
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hAconn ⟨f, hfA, hx₂f⟩
  have hcatch : Catches G F T := by
    refine ⟨htri, hFconn, Set.disjoint_left.mpr hFsub, ?_⟩
    intro u hu
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact ⟨x₂, Or.inr rfl, hzx₂⟩
    · exact ⟨f, Or.inl hfA, hyf⟩
    · obtain ⟨g, hgA, hag⟩ := haA
      exact ⟨g, Or.inl hgA, hag⟩
  have hnoTwo : ¬ ∃ g ∈ F, 2 ≤ (G.neighborSet g ∩ T).ncard := by
    rintro ⟨g, hgF, hcard⟩
    have hsubsingle : (G.neighborSet g ∩ T).Subsingleton := by
      intro u hu v hv
      rcases hgF with hgA | hg2
      · have hzu : u ≠ z := fun h => hzA g hgA (h ▸ hu.1).symm
        have hzv : v ≠ z := fun h => hzA g hgA (h ▸ hv.1).symm
        have huT : u = z ∨ u = y ∨ u = a := by simpa [T] using hu.2
        have hvT : v = z ∨ v = y ∨ v = a := by simpa [T] using hv.2
        have hu' : u = y ∨ u = a := huT.resolve_left hzu
        have hv' : v = y ∨ v = a := hvT.resolve_left hzv
        rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
        · rfl
        · have hgf : g = f := hyuniq g hgA hu.1.symm
          exact absurd (hgf ▸ hv.1) hfa
        · have hgf : g = f := hyuniq g hgA hv.1.symm
          exact absurd (hgf ▸ hu.1) hfa
        · rfl
      · have hg : g = x₂ := by simpa using hg2
        subst g
        have hu' : u = z := by
          simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu
          rcases hu.2 with rfl | rfl | rfl
          · rfl
          · exact absurd hu.1.symm hyx₂
          · exact absurd hu.1 hx₂a
        have hv' : v = z := by
          simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
          rcases hv.2 with rfl | rfl | rfl
          · rfl
          · exact absurd hv.1.symm hyx₂
          · exact absurd hv.1 hx₂a
        exact hu'.trans hv'.symm
    have hle : (G.neighborSet g ∩ T).ncard ≤ 1 :=
      (Set.ncard_le_one (Set.toFinite _)).mpr hsubsingle
    omega
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T htri F hFsub hcatch with
    href | htwo
  · obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, hTeq, hBsub, hreff⟩ := href
    have hzT : z ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    have hyT : y ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    have haT : a ∈ ({a₀, a₁, a₂} : Set V) := by rw [← hTeq]; simp [T]
    obtain ⟨bz, hbzB, hzbz, hbzonly⟩ := reflection_partner hreff hzT
    obtain ⟨byv, hbyB, hyby, hbyonly⟩ := reflection_partner hreff hyT
    obtain ⟨g, hgB, hag, hgonly⟩ := reflection_partner hreff haT
    have hbzF := hBsub hbzB
    have hbyF := hBsub hbyB
    have hgF := hBsub hgB
    have hbz : bz = x₂ := by
      rcases hbzF with hbzA | hbz2
      · exact absurd hzbz (hzA bz hbzA)
      · simpa using hbz2
    have hby : byv = f := by
      rcases hbyF with hbyA | hby2
      · exact hyuniq byv hbyA hyby
      · have he : byv = x₂ := by simpa using hby2
        exact absurd (he ▸ hyby) hyx₂
    have hzg : ¬ G.Adj z g := hgonly z (by rw [← hTeq]; simp [T]) hzne_a
    have hyg : ¬ G.Adj y g := hgonly y (by rw [← hTeq]; simp [T]) hyne_a
    have hg2 : g ≠ x₂ := by
      intro he
      exact hzg (he ▸ hzx₂)
    have hgA : g ∈ A := by
      rcases hgF with h | h
      · exact h
      · exact absurd (by simpa using h) hg2
    have hgf : g ≠ f := by
      intro he
      exact hyg (he ▸ hyf)
    have hbzg : bz ≠ g := by intro he; exact hg2 (he.symm.trans hbz)
    have hbyg : byv ≠ g := by intro he; exact hgf (he.symm.trans hby)
    have h2g : G.Adj x₂ g := by
      rw [← hbz]
      exact hreff.2.1.2 bz hbzB g hgB hbzg
    have hfg : G.Adj f g := by
      rw [← hby]
      exact hreff.2.1.2 byv hbyB g hgB hbyg
    have hbg : ¬ G.Adj b g := by
      intro hbg
      exact hnoc g hgA ⟨hag.symm, hbg.symm⟩
    exact ⟨g, ⟨hgA, by simpa using hgf⟩, hag, h2g, hfg, hyg, hbg⟩
  · exact (hnoTwo htwo).elim

/-- Claim **(9)** of the printed proof: *"There is no connected `F ⊆ A` containing
neighbours of all of `x₀, x₁, x₂` except `A` itself."* -/
theorem claim9_of_not_x2_adj_y (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (h2y : ¬ G.Adj (x 2) y) :
    ∀ F : Set V, F ⊆ A → ConnectedSet G F →
      (∃ a ∈ F, G.Adj (x 0) a) → (∃ a ∈ F, G.Adj (x 1) a) → (∃ a ∈ F, G.Adj (x 2) a) →
      F = A := by
  classical
  intro F hFA hFconn hF0 hF1 hF2
  by_contra hFne
  have hzx : ∀ i ≤ 2, G.Adj z (x i) := hws.2.2.2.2.2.2
  have hxne : ∀ i ≤ 2, x i ≠ z := fun i hi => (hws.2.2.1 i hi).2
  have hxij : ∀ i ≤ 2, ∀ j ≤ 2, i ≠ j → x i ≠ x j := by
    intro i hi j hj hij he
    exact hij (hws.2.1 i hi j hj he)
  have hzA : ∀ a ∈ A, ¬ G.Adj z a :=
    fun a ha => Thm192Setup.wheelSystemA_no_z a (hA.1 ha)
  have hxiA : ∀ i ≤ 2, x i ∉ A := by
    intro i hi hmem
    exact hzA (x i) hmem (hzx i hi)
  have hznotA : z ∉ A := by
    intro hzmem
    refine Thm192Setup.wheelSystemA_no_complete z (hA.1 hzmem) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hzx 0 (by omega)
    · exact hzx 1 (by omega)
  have hnoc : ∀ a ∈ A, ¬ (G.Adj a (x 0) ∧ G.Adj a (x 1)) := by
    intro a ha hc
    refine Thm192Setup.wheelSystemA_no_complete a (hA.1 ha) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hc.1
    · exact hc.2
  obtain ⟨f, hfAF, hfrest⟩ :=
    Thm192Claim9MinimalityWitness.minimalityWitness G z A₀ x Y y hyY
      (fun h : G.Adj y (x 2) => h2y h.symm) A hA hAmin F hFA hFconn hFne hF0 hF1 hF2
  rcases hfAF with ⟨hfA, hfF⟩
  rcases hfrest with ⟨hfconn, hyrest⟩
  rcases hyrest with ⟨y₀, hy₀Y, hy₀2, hy₀anti⟩
  obtain ⟨a₀, ha₀A, hy₀a₀⟩ := hA.2.2.2.2.2.1 y₀ hy₀Y hy₀2
  have ha₀f : a₀ = f := by
    by_contra hne
    exact hy₀anti a₀ ⟨ha₀A, by simpa using hne⟩ hy₀a₀
  have hy₀f : G.Adj y₀ f := ha₀f ▸ hy₀a₀
  have hy₀uniq : ∀ a ∈ A, G.Adj y₀ a → a = f := by
    intro a haA hadj
    by_contra hne
    exact hy₀anti a ⟨haA, by simpa using hne⟩ hadj
  have hy₀eq : y₀ = y := by
    by_contra hne
    have hy₀Y0 : y₀ ∈ Y \ {y} := ⟨hy₀Y, by simpa using hne⟩
    rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
      hleft | ⟨-, P, hP, hPint, hcard⟩
    · exact hy₀2 (hleft.1 y₀ hy₀Y0).symm
    · obtain ⟨c, hcI, d, hdI, hcd, hcY, hdY⟩ :=
        Thm192Infra.two_complete_in_interior hws hA.1 hP hPint hcard
      have hcf : c = f := hy₀uniq c (hPint c hcI) (hcY y₀ hy₀Y0).symm
      have hdf : d = f := hy₀uniq d (hPint d hdI) (hdY y₀ hy₀Y0).symm
      exact hcd (hcf.trans hdf.symm)
  subst y₀
  have hy2 : ¬ G.Adj y (x 2) := hy₀2
  have hyf : G.Adj y f := hy₀f
  have hyuniq : ∀ a ∈ A, G.Adj y a → a = f := hy₀uniq
  obtain ⟨hx20, hx21⟩ := Thm192Claim8.claim8 G hG z A₀ hframe x hws Y hHyp ih y hyY
    hyz hY0 A hA hAmin hcex (fun h => hy2 h.symm)
  have hxAne : ∀ i ≤ 2, ∀ a ∈ A, x i ≠ a := by
    intro i hi a ha hia
    exact hxiA i hi (hia ▸ ha)
  have hzAne : ∀ a ∈ A, z ≠ a := by
    intro a ha hza
    exact hznotA (hza ▸ ha)
  have hx2f : G.Adj (x 2) f := by
    by_contra hx2f
    let B : Set V := A ∪ {x 2}
    let W : Set V := {x 0, x 1}
    have hBconn : ConnectedSet G B :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hA.2.1
        ⟨hF2.choose, hFA hF2.choose_spec.1, hF2.choose_spec.2⟩
    have hBW : Disjoint B W := by
      rw [Set.disjoint_left]
      intro v hvB hvW
      rcases hvB with hvA | hv2
      · simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hvW
        rcases hvW with rfl | rfl
        · exact hxiA 0 (by omega) hvA
        · exact hxiA 1 (by omega) hvA
      · have hv : v = x 2 := by simpa using hv2
        subst v
        simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hvW
        rcases hvW with h | h
        · exact hxij 2 (by omega) 0 (by omega) (by omega) h
        · exact hxij 2 (by omega) 1 (by omega) (by omega) h
    have hx2B : x 2 ∈ B := Or.inr rfl
    have hfB : f ∈ B := Or.inl hfA
    have hpath : IsPathList G [x 2, z, y, f] := by
      apply PathGlue.isPathList_four
      · exact FiveHoleBasics.nodup_four
          (hxne 2 (by omega)) (hHyp.1 y hyY).2.2.2.symm
          (hxAne 2 (by omega) f hfA) (hHyp.1 y hyY).1.symm
          (hzAne f hfA) hyf.ne
      · exact (hzx 2 (by omega)).symm
      · exact hyz.symm
      · exact hyf
      · exact fun h => hy2 h.symm
      · exact hx2f
      · exact hzA f hfA
    have hzW : VertexComplete G z W := by
      intro v hv
      simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact hzx 0 (by omega)
      · exact hzx 1 (by omega)
    have hyW : VertexComplete G y W := by
      intro v hv
      simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact (hHyp.2.2.1 y hyY).symm
      · exact (hHyp.2.2.2.1 y hyY).symm
    have hx2nW : ¬ VertexComplete G (x 2) W := by
      intro hc
      exact hx20 (hc (x 0) (Or.inl rfl))
    have hfnW : ¬ VertexComplete G f W := by
      intro hc
      exact hnoc f hfA ⟨hc (x 0) (Or.inl rfl), hc (x 1) (Or.inr rfl)⟩
    have hzB : {g ∈ B | G.Adj z g} = ({x 2} : Set V) := by
      refine Thm192Infra.uniqueNeighbourSetForm.mpr ⟨hx2B, hzx 2 (by omega), ?_⟩
      intro g hgB hzg
      rcases hgB with hgA | hg2
      · exact absurd hzg (hzA g hgA)
      · simpa using hg2
    have hyB : {g ∈ B | G.Adj y g} = ({f} : Set V) := by
      refine Thm192Infra.uniqueNeighbourSetForm.mpr ⟨hfB, hyf, ?_⟩
      intro g hgB hyg
      rcases hgB with hgA | hg2
      · exact hyuniq g hgA hyg
      · have hg : g = x 2 := by simpa using hg2
        exact absurd (hg ▸ hyg) hy2
    have hBdiff : B \ {x 2} = A := by
      ext v
      simp only [B, Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | rfl, hne⟩
        · exact h
        · exact (hne rfl).elim
      · intro hvA
        exact ⟨Or.inl hvA, fun h => hxiA 2 (by omega) (h.symm ▸ hvA)⟩
    have hWanti : AnticonnectedSet G W := by
      have hWeq : W = ({x 0} : Set V) ∪ {x 1} := by
        ext v
        simp [W]
        tauto
      rw [hWeq]
      refine ConnectedSetUnionAttach.connectedSet_union_singleton
        (by
          intro p q
          exact Subtype.ext (p.2.trans q.2.symm) ▸ SimpleGraph.Reachable.refl p)
        ⟨x 0, rfl, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨(hxij 1 (by omega) 0 (by omega) (by omega)),
        fun h => Thm192Setup.x0_not_adj_x1 hws h.symm⟩
    obtain ⟨w, hwW, hwanti⟩ :=
      _root_.Workspace.Statements.S17.SPGT.thm_17_3 G hG B W hBW hBconn
        hWanti
        z y (x 2) f
        (by
          intro h; rcases h with h | h
          · rcases h with h | h
            · exact hznotA h
            · exact hxne 2 (by omega) (by simpa using h.symm)
          · simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at h
            rcases h with h | h
            · exact (hxne 0 (by omega)) h.symm
            · exact (hxne 1 (by omega)) h.symm)
        (by
          intro h; rcases h with h | h
          · rcases h with h | h
            · exact hnoc y h ⟨(hHyp.2.2.1 y hyY).symm,
                (hHyp.2.2.2.1 y hyY).symm⟩
            · exact (hHyp.1 y hyY).2.2.2 (by simpa using h)
          · simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at h
            rcases h with h | h
            · exact (hHyp.1 y hyY).2.1 h
            · exact (hHyp.1 y hyY).2.2.1 h)
        hx2B hfB hpath hzW hyW hx2nW hfnW hzB hyB (by
          rw [hBdiff]
          exact hA.2.1)
    rw [hBdiff] at hwanti
    simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hwW
    rcases hwW with rfl | rfl
    · obtain ⟨a, haA, h0a⟩ := hA.2.2.1
      exact hwanti a haA h0a
    · obtain ⟨a, haA, h1a⟩ := hA.2.2.2.1
      exact hwanti a haA h1a
  have hy0 : G.Adj y (x 0) := (hHyp.2.2.1 y hyY).symm
  have hy1 : G.Adj y (x 1) := (hHyp.2.2.2.1 y hyY).symm
  have hfx1 : ¬ G.Adj f (x 1) := by
    intro hfx1
    have hfx0 : ¬ G.Adj f (x 0) := fun h => hnoc f hfA ⟨h, hfx1⟩
    obtain ⟨f₀, hf₀A, hx0f₀, hx2f₀, hff₀, hyf₀, hx1f₀⟩ :=
      endpoint_reflection G hG z y (x 2) (x 0) (x 1) f A
        (hzx 2 (by omega)) hyz.symm (hzx 0 (by omega)) hy0 hy1 hy2 hx20 hfx0 hfA hyf hx2f
        hyuniq hA.2.1 hA.2.2.1 hzA hznotA hnoc
        (hHyp.1 y hyY).1.symm (hxne 0 (by omega)).symm (hHyp.1 y hyY).2.1
        (hxne 2 (by omega)) (hHyp.1 y hyY).2.2.2.symm
        (hxij 2 (by omega) 0 (by omega) (by omega))
    have hnd : ([z, x 1, f, f₀, x 0] : List V).Nodup :=
      FiveHoleBasics.nodup_five (hzx 1 (by omega)).ne (hzAne f hfA)
        (hzAne f₀ hf₀A.1) (hzx 0 (by omega)).ne
        (hxAne 1 (by omega) f hfA) (hxAne 1 (by omega) f₀ hf₀A.1)
        (hxij 1 (by omega) 0 (by omega) (by omega))
        (by simpa using hf₀A.2 : f₀ ≠ f).symm
        (hxAne 0 (by omega) f hfA).symm (hxAne 0 (by omega) f₀ hf₀A.1).symm
    exact FiveHoleBasics.five_hole_absurd hG.1.1.1.1 hnd
      (hzx 1 (by omega)) hfx1.symm hff₀ hx0f₀.symm (hzx 0 (by omega)).symm
      (hzA f hfA) (hzA f₀ hf₀A.1) hx1f₀
      (fun h => Thm192Setup.x0_not_adj_x1 hws h.symm) hfx0
  obtain ⟨f₁, hf₁A, hx1f₁, hx2f₁, hff₁, hyf₁, hx0f₁⟩ :=
    endpoint_reflection G hG z y (x 2) (x 1) (x 0) f A
      (hzx 2 (by omega)) hyz.symm (hzx 1 (by omega)) hy1 hy0 hy2 hx21 hfx1 hfA hyf hx2f
      hyuniq hA.2.1 hA.2.2.2.1 hzA hznotA (by
        intro g hg; simpa [and_comm] using hnoc g hg)
      (hHyp.1 y hyY).1.symm (hxne 1 (by omega)).symm (hHyp.1 y hyY).2.2.1
      (hxne 2 (by omega)) (hHyp.1 y hyY).2.2.2.symm
      (hxij 2 (by omega) 1 (by omega) (by omega))
  have hfx0 : ¬ G.Adj f (x 0) := by
    intro hfx0
    have hnd : ([z, x 0, f, f₁, x 1] : List V).Nodup :=
      FiveHoleBasics.nodup_five (hzx 0 (by omega)).ne (hzAne f hfA)
        (hzAne f₁ hf₁A.1) (hzx 1 (by omega)).ne
        (hxAne 0 (by omega) f hfA) (hxAne 0 (by omega) f₁ hf₁A.1)
        (hxij 0 (by omega) 1 (by omega) (by omega))
        (by simpa using hf₁A.2 : f₁ ≠ f).symm
        (hxAne 1 (by omega) f hfA).symm (hxAne 1 (by omega) f₁ hf₁A.1).symm
    exact FiveHoleBasics.five_hole_absurd hG.1.1.1.1 hnd
      (hzx 0 (by omega)) hfx0.symm hff₁ hx1f₁.symm (hzx 1 (by omega)).symm
      (hzA f hfA) (hzA f₁ hf₁A.1) hx0f₁
      (Thm192Setup.x0_not_adj_x1 hws) hfx1
  obtain ⟨f₀, hf₀A, hx0f₀, hx2f₀, hff₀, hyf₀, hx1f₀⟩ :=
    endpoint_reflection G hG z y (x 2) (x 0) (x 1) f A
      (hzx 2 (by omega)) hyz.symm (hzx 0 (by omega)) hy0 hy1 hy2 hx20 hfx0 hfA hyf hx2f
      hyuniq hA.2.1 hA.2.2.1 hzA hznotA hnoc
      (hHyp.1 y hyY).1.symm (hxne 0 (by omega)).symm (hHyp.1 y hyY).2.1
      (hxne 2 (by omega)) (hHyp.1 y hyY).2.2.2.symm
      (hxij 2 (by omega) 0 (by omega) (by omega))
  have hf₀f₁ : ¬ G.Adj f₀ f₁ := by
    intro hf₀f₁
    have hnd : ([z, x 0, f₀, f₁, x 1] : List V).Nodup :=
      FiveHoleBasics.nodup_five (hzx 0 (by omega)).ne (hzAne f₀ hf₀A.1)
        (hzAne f₁ hf₁A.1) (hzx 1 (by omega)).ne
        (hxAne 0 (by omega) f₀ hf₀A.1) (hxAne 0 (by omega) f₁ hf₁A.1)
        (hxij 0 (by omega) 1 (by omega) (by omega)) hf₀f₁.ne
        (hxAne 1 (by omega) f₀ hf₀A.1).symm
        (hxAne 1 (by omega) f₁ hf₁A.1).symm
    exact FiveHoleBasics.five_hole_absurd hG.1.1.1.1 hnd
      (hzx 0 (by omega)) hx0f₀ hf₀f₁ hx1f₁.symm (hzx 1 (by omega)).symm
      (hzA f₀ hf₀A.1) (hzA f₁ hf₁A.1) hx0f₁
      (Thm192Setup.x0_not_adj_x1 hws) (fun h => hx1f₀ h.symm)
  have hf₀ne₁ : f₀ ≠ f₁ := by
    intro heq
    subst f₁
    exact hnoc f₀ hf₀A.1 ⟨hx0f₀.symm, hx1f₁.symm⟩
  let Q : List V := [x 0, f₀, f, f₁, x 1]
  have hQ : IsPathFrom G Q (x 0) (x 1) := by
    refine ⟨?_, by simp [Q], by simp [Q]⟩
    apply isPathList_five
    · exact FiveHoleBasics.nodup_five
        (hxAne 0 (by omega) f₀ hf₀A.1) (hxAne 0 (by omega) f hfA)
        (hxAne 0 (by omega) f₁ hf₁A.1)
        (hxij 0 (by omega) 1 (by omega) (by omega))
        (by simpa using hf₀A.2 : f₀ ≠ f) hf₀ne₁
        (hxAne 1 (by omega) f₀ hf₀A.1).symm
        (by simpa using hf₁A.2 : f₁ ≠ f).symm
        (hxAne 1 (by omega) f hfA).symm
        (hxAne 1 (by omega) f₁ hf₁A.1).symm
    · exact hx0f₀
    · exact hff₀.symm
    · exact hff₁
    · exact hx1f₁.symm
    · exact fun h => hfx0 h.symm
    · exact hx0f₁
    · exact Thm192Setup.x0_not_adj_x1 hws
    · exact hf₀f₁
    · exact fun h => hx1f₀ h.symm
    · exact hfx1
  let BQ : Set V := {w : V | w ∈ SPGT.interior Q}
  have hQint : BQ ⊆ A := by
    intro w hw
    change w ∈ SPGT.interior Q at hw
    simp [Q, SPGT.interior] at hw
    rcases hw with rfl | rfl | rfl
    · exact hf₀A.1
    · exact hfA
    · exact hf₁A.1
  have hBQeq : BQ = A := by
    apply Thm192Claim3.claim3 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
    · exact hQint
    · exact MinimalConnectedIsPath.connectedSet_interior hQ
    · exact ⟨f₀, by simp [BQ, Q, SPGT.interior], hx0f₀⟩
    · exact ⟨f₁, by simp [BQ, Q, SPGT.interior], hx1f₁⟩
    · exact ⟨f, by simp [BQ, Q, SPGT.interior], hx2f⟩
    · exact ⟨f, by simp [BQ, Q, SPGT.interior], hyf⟩
  have hYA : ∀ w ∈ Y, w ∉ A := by
    intro w hwY hwA
    exact hnoc w hwA ⟨(hHyp.2.2.1 w hwY).symm, (hHyp.2.2.2.1 w hwY).symm⟩
  have hzQ : z ∉ Q := by
    intro hzmem
    simp [Q] at hzmem
    rcases hzmem with h | h | h | h | h
    · exact hxne 0 (by omega) h.symm
    · exact hzAne f₀ hf₀A.1 h
    · exact hzAne f hfA h
    · exact hzAne f₁ hf₁A.1 h
    · exact hxne 1 (by omega) h.symm
  have hzQint : ∀ w ∈ SPGT.interior Q, ¬ G.Adj z w := by
    intro w hw
    exact hzA w (hQint hw)
  have hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: Q) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior Q, ∃ d ∈ SPGT.interior Q, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})) := by
    by_cases hYempty : Y \ {y} = ∅
    · left
      rw [hYempty]
      intro w hw
      exact (Set.notMem_empty w hw).elim
    rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
      hleft | ⟨hzY, P, hP, hPint, hcard⟩
    · exact Or.inl hleft.1
    · right
      have hanti : AnticonnectedSet G (Y \ {y}) := by
        rcases hY0 with h | h
        · exact (hYempty h).elim
        · exact h
      have hQhole : IsHoleList G (z :: Q) :=
        PrismBasics.isHoleList_of_path_add_vertex hQ (by simp [pathLength, Q])
          (hzx 0 (by omega)) (hzx 1 (by omega)) hzQ hzQint
      have hdisj : ∀ v ∈ z :: Q, v ∉ Y \ {y} := by
        intro v hv hvY0
        rcases List.mem_cons.mp hv with hvz | hvQ
        · subst v
          exact (hHyp.1 z hvY0.1).1 rfl
        · simp [Q] at hvQ
          rcases hvQ with hv0 | hvf₀ | hvf | hvf₁ | hv1
          · subst v
            exact (hHyp.1 (x 0) hvY0.1).2.1 rfl
          · subst v
            exact hYA f₀ hvY0.1 hf₀A.1
          · subst v
            exact hYA f hvY0.1 hfA
          · subst v
            exact hYA f₁ hvY0.1 hf₁A.1
          · subst v
            exact (hHyp.1 (x 1) hvY0.1).2.2.1 rfl
      have hedge0 : EdgeComplete G (Y \ {y}) z (x 0) :=
        ⟨hzx 0 (by omega), fun w hw => hzY w hw.1,
          fun w hw => hHyp.2.2.1 w hw.1⟩
      have hedge1 : EdgeComplete G (Y \ {y}) z (x 1) :=
        ⟨hzx 1 (by omega), fun w hw => hzY w hw.1,
          fun w hw => hHyp.2.2.2.1 w hw.1⟩
      have hedgeNonempty :
          {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧
            EdgeComplete G (Y \ {y}) u v}.Nonempty :=
        Set.nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨e, u, huP, v, hvP, -, huv⟩ := hedgeNonempty
      have hmap : ∀ w ∈ P, w ∈ Q := by
        intro w hwP
        by_cases hw0 : w = x 0
        · subst w
          simp [Q]
        by_cases hw1 : w = x 1
        · subst w
          simp [Q]
        have hwI : w ∈ SPGT.interior P :=
          (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hwP, hw0, hw1⟩
        have hwBQ : w ∈ BQ := by
          rw [hBQeq]
          exact hPint w hwI
        exact PathBasics.interior_subset hwBQ
      have huQ := hmap u huP
      have hvQ := hmap v hvP
      have huz : u ≠ z := fun h => hzQ (h ▸ huQ)
      have hvz : v ≠ z := fun h => hzQ (h ▸ hvQ)
      have hwheelEdges : ∃ a b c d : V,
          a ∈ z :: Q ∧ b ∈ z :: Q ∧ c ∈ z :: Q ∧ d ∈ z :: Q ∧
          EdgeComplete G (Y \ {y}) a b ∧ EdgeComplete G (Y \ {y}) c d ∧
          a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
        by_cases hu0 : u = x 0
        · have hv1 : v ≠ x 1 := by
            intro hv1
            subst u
            subst v
            exact Thm192Setup.x0_not_adj_x1 hws huv.1
          have hu1 : u ≠ x 1 := fun h =>
            hxij 0 (by omega) 1 (by omega) (by omega) (hu0.symm.trans h)
          exact ⟨u, v, z, x 1, List.mem_cons_of_mem z huQ,
            List.mem_cons_of_mem z hvQ, by simp, by simp [Q], huv, hedge1,
            huz, hu1, hvz, hv1⟩
        · by_cases hv0 : v = x 0
          · have hu1 : u ≠ x 1 := by
              intro hu1
              subst u
              subst v
              exact Thm192Setup.x0_not_adj_x1 hws huv.1.symm
            have hv1 : v ≠ x 1 := fun h =>
              hxij 0 (by omega) 1 (by omega) (by omega) (hv0.symm.trans h)
            exact ⟨v, u, z, x 1, List.mem_cons_of_mem z hvQ,
              List.mem_cons_of_mem z huQ, by simp, by simp [Q],
              ⟨huv.1.symm, huv.2.2, huv.2.1⟩, hedge1,
              hvz, hv1, huz, hu1⟩
          · exact ⟨u, v, z, x 0, List.mem_cons_of_mem z huQ,
              List.mem_cons_of_mem z hvQ, by simp, by simp [Q], huv, hedge0,
              huz, hu0, hvz, hv0⟩
      refine ⟨⟨⟨hQhole, by simp [holeLength, Q]⟩,
        ⟨Set.nonempty_iff_ne_empty.mpr hYempty, hanti, hdisj⟩, hwheelEdges⟩, ?_⟩
      obtain ⟨c, hcP, d, hdP, hcd, hc, hd⟩ :=
        Thm192Infra.two_complete_in_interior hws hA.1 hP hPint hcard
      have hcQ : c ∈ SPGT.interior Q := by
        change c ∈ BQ
        rw [hBQeq]
        exact hPint c hcP
      have hdQ : d ∈ SPGT.interior Q := by
        change d ∈ BQ
        rw [hBQeq]
        exact hPint d hdP
      exact ⟨c, hcQ, d, hdQ, hcd, hc, hd⟩
  exact Thm192Claim7.claim7 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
    hAmin hcex Q hQ hQint (by simp [Q]) hchoice
      ⟨⟨f, by simp [Q, SPGT.interior], hx2f⟩,
        ⟨f, by simp [Q, SPGT.interior], hyf⟩⟩

end Workspace.ProofLemmas.Thm192Claim9NotAdjX2
