import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Wheels
import Workspace.Types.TriangleCatching
import Workspace.Types.Classes
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.SegmentBasics
import Workspace.Statements.S17.Thm_17_1

/-! A source-exact, axiom-free local form of Theorem 18.1 used by the 18.5 proof. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Scratch181

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem triple_distinct {a b c : V} (h : ({a,b,c} : Set V).ncard = 3) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  have key : ∀ x y : V, ({x,y} : Set V).ncard ≤ 2 := by
    intro x y
    calc
      ({x,y} : Set V).ncard ≤ ({y} : Set V).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by simp
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have he : ({a,a,c} : Set V) = {a,c} := by ext; simp
    rw [he] at h
    exact (by have := key a c; omega)
  · have he : ({a,b,a} : Set V) = {a,b} := by ext; simp; tauto
    rw [he] at h
    exact (by have := key a b; omega)
  · have he : ({a,b,b} : Set V) = {a,b} := by ext; simp
    rw [he] at h
    exact (by have := key a b; omega)

private theorem reflection_swap12 {G : SimpleGraph V} {a b c x y z : V}
    (h : IsReflectionOfTriangle G a b c x y z) :
    IsReflectionOfTriangle G b a c y x z := by
  obtain ⟨hA, hB, hd, hc⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : ({a,b,c} : Set V) = {b,a,c} := by ext; simp; tauto
    rwa [← he]
  · have he : ({x,y,z} : Set V) = {y,x,z} := by ext; simp; tauto
    rwa [← he]
  · have heA : ({a,b,c} : Set V) = {b,a,c} := by ext; simp; tauto
    have heB : ({x,y,z} : Set V) = {y,x,z} := by ext; simp; tauto
    rwa [← heA, ← heB]
  · intro u hu v hv
    have hu' : u ∈ ({a,b,c} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      tauto
    have hv' : v ∈ ({x,y,z} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
      tauto
    rw [hc u hu' v hv']
    tauto

private theorem reflection_swap23 {G : SimpleGraph V} {a b c x y z : V}
    (h : IsReflectionOfTriangle G a b c x y z) :
    IsReflectionOfTriangle G a c b x z y := by
  obtain ⟨hA, hB, hd, hc⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have he : ({a,b,c} : Set V) = {a,c,b} := by ext; simp; tauto
    rwa [← he]
  · have he : ({x,y,z} : Set V) = {x,z,y} := by ext; simp; tauto
    rwa [← he]
  · have heA : ({a,b,c} : Set V) = {a,c,b} := by ext; simp; tauto
    have heB : ({x,y,z} : Set V) = {x,z,y} := by ext; simp; tauto
    rwa [← heA, ← heB]
  · intro u hu v hv
    have hu' : u ∈ ({a,b,c} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      tauto
    have hv' : v ∈ ({x,y,z} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
      tauto
    rw [hc u hu' v hv']
    tauto

private theorem reflection_rotate {G : SimpleGraph V} {a b c x y z : V}
    (h : IsReflectionOfTriangle G a b c x y z) :
    IsReflectionOfTriangle G c a b z x y :=
  reflection_swap12 (reflection_swap23 h)

private theorem reflection_rotate_left {G : SimpleGraph V} {a b c x y z : V}
    (h : IsReflectionOfTriangle G a b c x y z) :
    IsReflectionOfTriangle G b c a y z x :=
  reflection_swap23 (reflection_swap12 h)

private theorem reflection_swap13 {G : SimpleGraph V} {a b c x y z : V}
    (h : IsReflectionOfTriangle G a b c x y z) :
    IsReflectionOfTriangle G c b a z y x :=
  reflection_swap12 (reflection_swap23 (reflection_swap12 h))

private theorem isHoleList_six (G : SimpleGraph V) (a b c d e f : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hef : G.Adj e f) (hfa : G.Adj f a)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e) (hbf : ¬ G.Adj b f)
    (hce : ¬ G.Adj c e) (hcf : ¬ G.Adj c f) (hdf : ¬ G.Adj d f)
    (hnd : [a,b,c,d,e,f].Nodup) : IsHoleList G [a,b,c,d,e,f] := by
  refine ⟨by simp, hnd, ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;>
    simp [hab, hbc, hcd, hde, hef, hfa, hac, had, hae, hbd, hbe, hbf, hce, hcf,
      hdf, hfa.symm, G.irrefl, SimpleGraph.adj_comm]

theorem thm181_local (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p₁ p₂ p₃ p₄ p₅ : V)
    (htrack : IsTrackList G [p₁, p₂, p₃, p₄, p₅])
    (hout : ∀ w ∈ [p₁, p₂, p₃, p₄, p₅], w ∉ X ∪ Y)
    (hind : ¬ G.Adj p₁ p₃ ∧ ¬ G.Adj p₁ p₄ ∧ ¬ G.Adj p₁ p₅ ∧
      ¬ G.Adj p₂ p₄ ∧ ¬ G.Adj p₃ p₅)
    (hX15 : VertexComplete G p₁ X ∧ VertexComplete G p₅ X)
    (hX234 : ¬ VertexComplete G p₂ X ∧ ¬ VertexComplete G p₃ X ∧
      ¬ VertexComplete G p₄ X)
    (hY1 : VertexComplete G p₁ Y) (hY3 : VertexComplete G p₃ Y)
    (hY4 : VertexComplete G p₄ Y) :
    VertexComplete G p₂ Y ∨ VertexComplete G p₅ Y := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hp12, hp23, hp34, hp45⟩ :
      G.Adj p₁ p₂ ∧ G.Adj p₂ p₃ ∧ G.Adj p₃ p₄ ∧ G.Adj p₄ p₅ := by
    have h := htrack.2.2
    exact ⟨by simpa using h 0 (by simp), by simpa using h 1 (by simp),
      by simpa using h 2 (by simp), by simpa using h 3 (by simp)⟩
  have hndP : [p₁,p₂,p₃,p₄,p₅].Nodup := htrack.2.1
  have miss (z : V) (S : Set V) (hn : ¬ VertexComplete G z S) :
      ∃ x ∈ S, ¬ G.Adj z x := by
    by_contra hc
    push_neg at hc
    exact hn hc
  obtain ⟨x2, hx2X, hp2x2⟩ := miss p₂ X hX234.1
  obtain ⟨x3, hx3X, hp3x3⟩ := miss p₃ X hX234.2.1
  obtain ⟨x4, hx4X, hp4x4⟩ := miss p₄ X hX234.2.2
  obtain ⟨y2, hy2Y, hp2y2⟩ := miss p₂ Y hcon.1
  obtain ⟨y5, hy5Y, hp5y5⟩ := miss p₅ Y hcon.2
  let F : Set V := X ∪ Y ∪ {p₂, p₄}
  have hXconn : ConnectedSet Gᶜ X := hXa
  have hXp2 : ConnectedSet Gᶜ (X ∪ {p₂}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hXconn
      ⟨x2, hx2X, ⟨fun he => (hout p₂ (by simp)) (Or.inl (he ▸ hx2X)), hp2x2⟩⟩
  have hXYp2 : ConnectedSet Gᶜ ((X ∪ {p₂}) ∪ Y) :=
    ConnectedSetUnionAttach.connectedSet_union hXp2 hYa
      (Or.inr ⟨p₂, Or.inr rfl, y2, hy2Y,
        ⟨fun he => (hout p₂ (by simp)) (Or.inr (he ▸ hy2Y)), hp2y2⟩⟩)
  have hp24c : Gᶜ.Adj p₂ p₄ := by
    refine ⟨?_, hind.2.2.2.1⟩
    intro he
    have he' : ([p₁,p₂,p₃,p₄,p₅][1]'(by simp)) =
        ([p₁,p₂,p₃,p₄,p₅][3]'(by simp)) := by simpa using he
    have := hndP.getElem_inj_iff.mp he'
    omega
  have hFc : ConnectedSet Gᶜ F := by
    have h := ConnectedSetUnionAttach.connectedSet_union_singleton hXYp2
      ⟨p₂, Or.inl (Or.inr rfl), hp24c.symm⟩
    simpa [F, Set.union_assoc, Set.union_left_comm, Set.union_comm] using h
  let A : Set V := {p₁,p₃,p₅}
  have hAcard : A.ncard = 3 := by
    have h13 : p₁ ≠ p₃ := by
      intro he
      have he' : ([p₁,p₂,p₃,p₄,p₅][0]'(by simp)) =
          ([p₁,p₂,p₃,p₄,p₅][2]'(by simp)) := by simpa using he
      have := hndP.getElem_inj_iff.mp he'; omega
    have h15 : p₁ ≠ p₅ := by
      intro he
      have he' : ([p₁,p₂,p₃,p₄,p₅][0]'(by simp)) =
          ([p₁,p₂,p₃,p₄,p₅][4]'(by simp)) := by simpa using he
      have := hndP.getElem_inj_iff.mp he'; omega
    have h35 : p₃ ≠ p₅ := by
      intro he
      have he' : ([p₁,p₂,p₃,p₄,p₅][2]'(by simp)) =
          ([p₁,p₂,p₃,p₄,p₅][4]'(by simp)) := by simpa using he
      have := hndP.getElem_inj_iff.mp he'; omega
    simp [A, h13, h15, h35]
  have hAtri : IsTriangle Gᶜ A := by
    refine ⟨hAcard, ?_⟩
    intro a ha b hb hab
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals simp_all [SimpleGraph.adj_comm]
  have hFA : F ⊆ Aᶜ := by
    intro z hz hzA
    simp only [F, A, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_compl_iff] at hz hzA
    rcases hz with hX | hY | rfl | rfl <;> rcases hzA with rfl | rfl | rfl
    all_goals simp_all
  have hcatchAdj : ∀ a ∈ A, ∃ f ∈ F, Gᶜ.Adj a f := by
    intro a ha
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with ha | ha | ha
    · have hp14 : p₁ ≠ p₄ := by
        intro he
        have he' : ([p₁,p₂,p₃,p₄,p₅][0]'(by simp)) =
            ([p₁,p₂,p₃,p₄,p₅][3]'(by simp)) := by simpa using he
        have := hndP.getElem_inj_iff.mp he'; omega
      exact ⟨p₄, by simp [F], by simpa [ha] using (⟨hp14, hind.2.1⟩ : Gᶜ.Adj p₁ p₄)⟩
    · have hne : p₃ ≠ x3 := by
        intro he
        exact (hout p₃ (by simp)) (Or.inl (by simpa [he] using hx3X))
      exact ⟨x3, by simp [F, hx3X], by simpa [ha] using (⟨hne, hp3x3⟩ : Gᶜ.Adj p₃ x3)⟩
    · have hne : p₅ ≠ y5 := by
        intro he
        exact (hout p₅ (by simp)) (Or.inr (by simpa [he] using hy5Y))
      exact ⟨y5, by simp [F, hy5Y], by simpa [ha] using (⟨hne, hp5y5⟩ : Gᶜ.Adj p₅ y5)⟩
  have hbound : ∀ f ∈ F, (Gᶜ.neighborSet f ∩ A).ncard ≤ 1 := by
    intro f hf
    rw [Set.ncard_le_one]
    intro a ha b hb
    rcases ha with ⟨hfa, haA⟩
    rcases hb with ⟨hfb, hbA⟩
    simp only [A, Set.mem_insert_iff, Set.mem_singleton_iff] at haA hbA
    simp only [F, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with (hfX | hfY) | rfl | rfl
    · have ea : a = p₃ := by
        rcases haA with rfl | h | rfl
        · exact absurd (hX15.1 f hfX).symm hfa.2
        · exact h
        · exact absurd (hX15.2 f hfX).symm hfa.2
      have eb : b = p₃ := by
        rcases hbA with rfl | h | rfl
        · exact absurd (hX15.1 f hfX).symm hfb.2
        · exact h
        · exact absurd (hX15.2 f hfX).symm hfb.2
      exact ea.trans eb.symm
    · have ea : a = p₅ := by
        rcases haA with rfl | rfl | h
        · exact absurd (hY1 f hfY).symm hfa.2
        · exact absurd (hY3 f hfY).symm hfa.2
        · exact h
      have eb : b = p₅ := by
        rcases hbA with rfl | rfl | h
        · exact absurd (hY1 f hfY).symm hfb.2
        · exact absurd (hY3 f hfY).symm hfb.2
        · exact h
      exact ea.trans eb.symm
    · have ea : a = p₅ := by
        rcases haA with rfl | rfl | h
        · exact absurd hp12.symm hfa.2
        · exact absurd hp23 hfa.2
        · exact h
      have eb : b = p₅ := by
        rcases hbA with rfl | rfl | h
        · exact absurd hp12.symm hfb.2
        · exact absurd hp23 hfb.2
        · exact h
      exact ea.trans eb.symm
    · have ea : a = p₁ := by
        rcases haA with h | rfl | rfl
        · exact h
        · exact absurd hp34.symm hfa.2
        · exact absurd hp45 hfa.2
      have eb : b = p₁ := by
        rcases hbA with h | rfl | rfl
        · exact h
        · exact absurd hp34.symm hfb.2
        · exact absurd hp45 hfb.2
      exact ea.trans eb.symm
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 Gᶜ
      (ClassLemmas.inF7_compl.mpr hG) A hAtri F hFA
      ⟨hAtri, hFc, Set.disjoint_left.mpr (fun x hxF hxA => hFA hxF hxA), hcatchAdj⟩ with
    ⟨a₁,a₂,a₃,b₁,b₂,b₃,hAeq,hbF,href⟩ | ⟨f,hf,h2⟩
  · have ha1 : a₁ = p₁ ∨ a₁ = p₃ ∨ a₁ = p₅ := by
      have : a₁ ∈ A := by rw [hAeq]; simp
      simpa [A] using this
    have ha2 : a₂ = p₁ ∨ a₂ = p₃ ∨ a₂ = p₅ := by
      have : a₂ ∈ A := by rw [hAeq]; simp
      simpa [A] using this
    have ha3 : a₃ = p₁ ∨ a₃ = p₃ ∨ a₃ = p₅ := by
      have : a₃ ∈ A := by rw [hAeq]; simp
      simpa [A] using this
    obtain ⟨ha12,ha13,ha23⟩ := triple_distinct href.1.1
    have hperm :
        (a₁ = p₁ ∧ a₂ = p₃ ∧ a₃ = p₅) ∨
        (a₁ = p₁ ∧ a₂ = p₅ ∧ a₃ = p₃) ∨
        (a₁ = p₃ ∧ a₂ = p₁ ∧ a₃ = p₅) ∨
        (a₁ = p₃ ∧ a₂ = p₅ ∧ a₃ = p₁) ∨
        (a₁ = p₅ ∧ a₂ = p₁ ∧ a₃ = p₃) ∨
        (a₁ = p₅ ∧ a₂ = p₃ ∧ a₃ = p₁) := by
      rcases ha1 with h1 | h1 | h1 <;> rcases ha2 with h2 | h2 | h2 <;>
        rcases ha3 with h3 | h3 | h3
      all_goals aesop
    obtain ⟨c₁,c₃,c₅,hcF,href'⟩ : ∃ c₁ c₃ c₅,
        ({c₁,c₃,c₅} : Set V) ⊆ F ∧
          IsReflectionOfTriangle Gᶜ p₁ p₃ p₅ c₁ c₃ c₅ := by
      rcases hperm with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ |
          ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
      · exact ⟨b₁,b₂,b₃, hbF, href⟩
      · exact ⟨b₁,b₃,b₂, by
          intro z hz; apply hbF
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          rcases hz with hz | hz | hz
          · exact Or.inl hz
          · exact Or.inr (Or.inr hz)
          · exact Or.inr (Or.inl hz),
          reflection_swap23 href⟩
      · exact ⟨b₂,b₁,b₃, by
          intro z hz; apply hbF
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          rcases hz with hz | hz | hz
          · exact Or.inr (Or.inl hz)
          · exact Or.inl hz
          · exact Or.inr (Or.inr hz),
          reflection_swap12 href⟩
      · exact ⟨b₃,b₁,b₂, by
          intro z hz; apply hbF
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          rcases hz with hz | hz | hz
          · exact Or.inr (Or.inr hz)
          · exact Or.inl hz
          · exact Or.inr (Or.inl hz),
          reflection_rotate href⟩
      · exact ⟨b₂,b₃,b₁, by
          intro z hz; apply hbF
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          rcases hz with hz | hz | hz
          · exact Or.inr (Or.inl hz)
          · exact Or.inr (Or.inr hz)
          · exact Or.inl hz,
          reflection_rotate_left href⟩
      · exact ⟨b₃,b₂,b₁, by
          intro z hz; apply hbF
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          rcases hz with hz | hz | hz
          · exact Or.inr (Or.inr hz)
          · exact Or.inr (Or.inl hz)
          · exact Or.inl hz,
          reflection_swap13 href⟩
    have hc1F : c₁ ∈ F := hcF (by simp)
    have hc3F : c₃ ∈ F := hcF (by simp)
    have hc5F : c₅ ∈ F := hcF (by simp)
    have hp1c1c : Gᶜ.Adj p₁ c₁ := by
      apply (href'.2.2.2 p₁ (by simp) c₁ (by simp)).mpr
      simp
    have hp3c3c : Gᶜ.Adj p₃ c₃ := by
      apply (href'.2.2.2 p₃ (by simp) c₃ (by simp)).mpr
      simp
    have hp5c5c : Gᶜ.Adj p₅ c₅ := by
      apply (href'.2.2.2 p₅ (by simp) c₅ (by simp)).mpr
      simp
    have hc1eq : c₁ = p₄ := by
      simp only [F, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hc1F
      rcases hc1F with (hcX | hcY) | hc2 | hc4
      · exact absurd (hX15.1 c₁ hcX) hp1c1c.2
      · exact absurd (hY1 c₁ hcY) hp1c1c.2
      · rw [hc2] at hp1c1c
        exact absurd hp12 hp1c1c.2
      · exact hc4
    have hc3X : c₃ ∈ X := by
      simp only [F, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hc3F
      rcases hc3F with (hcX | hcY) | hc2 | hc4
      · exact hcX
      · exact absurd (hY3 c₃ hcY) hp3c3c.2
      · rw [hc2] at hp3c3c
        exact absurd hp23.symm hp3c3c.2
      · rw [hc4] at hp3c3c
        exact absurd hp34 hp3c3c.2
    have hc5case : c₅ ∈ Y ∨ c₅ = p₂ := by
      simp only [F, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hc5F
      rcases hc5F with (hcX | hcY) | hc2 | hc4
      · exact absurd (hX15.2 c₅ hcX) hp5c5c.2
      · exact Or.inl hcY
      · exact Or.inr hc2
      · rw [hc4] at hp5c5c
        exact absurd hp45.symm hp5c5c.2
    have hc135 := triple_distinct href'.2.1.1
    have hc1c5c : Gᶜ.Adj c₁ c₅ :=
      href'.2.1.2 c₁ (by simp) c₅ (by simp) hc135.2.1
    have hc5eq : c₅ = p₂ := by
      rcases hc5case with hc5Y | hc5
      · rw [hc1eq] at hc1c5c
        exact absurd (hY4 c₅ hc5Y) hc1c5c.2
      · exact hc5
    have hp135 := triple_distinct href'.1.1
    have hp1c3c : ¬ Gᶜ.Adj p₁ c₃ := by
      rw [href'.2.2.2 p₁ (by simp) c₃ (by simp)]
      rintro (⟨-, h31⟩ | ⟨h13, -⟩ | ⟨h15, -⟩)
      · exact hc135.1 h31.symm
      · exact hp135.1 h13
      · exact hp135.2.1 h15
    have hp5c3c : ¬ Gᶜ.Adj p₅ c₃ := by
      rw [href'.2.2.2 p₅ (by simp) c₃ (by simp)]
      rintro (⟨h51, -⟩ | ⟨h53, -⟩ | ⟨-, h35⟩)
      · exact hp135.2.1 h51.symm
      · exact hp135.2.2 h53.symm
      · exact hc135.2.2 h35
    have hp1c3ne : p₁ ≠ c₃ := by
      intro he
      have hpB : p₁ ∈ ({c₁,c₃,c₅} : Set V) := by
        rw [he]
        simp
      exact (Set.disjoint_left.mp href'.2.2.1) (by simp) hpB
    have hp5c3ne : p₅ ≠ c₃ := by
      intro he
      have hpB : p₅ ∈ ({c₁,c₃,c₅} : Set V) := by
        rw [he]
        simp
      exact (Set.disjoint_left.mp href'.2.2.1) (by simp) hpB
    have hp1c3 : G.Adj p₁ c₃ := by
      by_contra hn
      exact hp1c3c ⟨hp1c3ne, hn⟩
    have hp5c3 : G.Adj p₅ c₃ := by
      by_contra hn
      exact hp5c3c ⟨hp5c3ne, hn⟩
    have hc5c3c : Gᶜ.Adj c₅ c₃ :=
      href'.2.1.2 c₅ (by simp) c₃ (by simp) hc135.2.2.symm
    have hc1c3c : Gᶜ.Adj c₁ c₃ :=
      href'.2.1.2 c₁ (by simp) c₃ (by simp) hc135.1
    have hp2p5n : ¬ G.Adj p₂ p₅ := by
      simpa [hc5eq, SimpleGraph.adj_comm] using hp5c5c.2
    have hp2c3n : ¬ G.Adj p₂ c₃ := by
      simpa [hc5eq] using hc5c3c.2
    have hp4c3n : ¬ G.Adj p₄ c₃ := by
      simpa [hc1eq] using hc1c3c.2
    have hc3notP : c₃ ∉ [p₁,p₂,p₃,p₄,p₅] := by
      intro hcP
      exact (hout c₃ hcP) (Or.inl hc3X)
    have hnd6 : [p₁,p₂,p₃,p₄,p₅,c₃].Nodup := by
      have ha : ([p₁,p₂,p₃,p₄,p₅] ++ [c₃]).Nodup := by
        refine List.nodup_append.mpr ⟨hndP, by simp, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst y
        exact hc3notP (hxy ▸ hx)
      simpa using ha
    have hhole : IsHoleList G [p₁,p₂,p₃,p₄,p₅,c₃] :=
      isHoleList_six G p₁ p₂ p₃ p₄ p₅ c₃ hp12 hp23 hp34 hp45 hp5c3
        hp1c3.symm hind.1 hind.2.1 hind.2.2.1 hind.2.2.2.1 hp2p5n hp2c3n
        hind.2.2.2.2 hp3c3c.2 hp4c3n hnd6
    let C : List V := [p₁,p₂,p₃,p₄,p₅,c₃]
    have hholeC : IsHoleList G C := by simpa [C] using hhole
    have hc3Y : VertexComplete G c₃ Y := hcompl c₃ hc3X
    have hCnotY : ∀ z ∈ C, z ∉ Y := by
      intro z hzC hzY
      have hz : z ∈ [p₁,p₂,p₃,p₄,p₅] ∨ z = c₃ := by
        simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hzC
        rcases hzC with hz | hz | hz | hz | hz | hz
        · exact Or.inl (by simp [hz])
        · exact Or.inl (by simp [hz])
        · exact Or.inl (by simp [hz])
        · exact Or.inl (by simp [hz])
        · exact Or.inl (by simp [hz])
        · exact Or.inr hz
      rcases hz with hzP | hz3
      · exact (hout z hzP) (Or.inr hzY)
      · subst z
        exact (Set.disjoint_left.mp hXY) hc3X hzY
    have hp14 : p₁ ≠ p₄ := by
      intro he
      have he' : ([p₁,p₂,p₃,p₄,p₅][0]'(by simp)) =
          ([p₁,p₂,p₃,p₄,p₅][3]'(by simp)) := by simpa using he
      have := hndP.getElem_inj_iff.mp he'
      omega
    have hc3p3 : c₃ ≠ p₃ := by
      intro he
      apply hc3notP
      simp [he]
    have hc3p4 : c₃ ≠ p₄ := by
      intro he
      apply hc3notP
      simp [he]
    have hwheel : IsWheel G C Y := by
      refine ⟨⟨hholeC, by simp [C, holeLength]⟩, ⟨hYne, hYa, hCnotY⟩,
        p₁, c₃, p₃, p₄, ?_, ?_, ?_, ?_,
        ⟨hp1c3, hY1, hc3Y⟩, ⟨hp34, hY3, hY4⟩,
        hp135.1, hp14, hc3p3, hc3p4⟩
      all_goals simp [C]
    have hseg : IsSegment G C Y [p₃,p₄] := by
      have htake : (C.rotate 2).take 2 = [p₃,p₄] := by simp [C]
      rw [← htake]
      apply SegmentBasics.isSegment_of_run hholeC (k := 2) (L := 2)
          (by omega) (by simp [C])
      · intro t ht
        interval_cases t
        · exact ⟨p₃, by simp [C], hY3⟩
        · exact ⟨p₄, by simp [C], hY4⟩
      · rintro ⟨z, hz, hzY⟩
        have he : z = p₅ := by simpa [C] using hz.symm
        exact hcon.2 (he ▸ hzY)
      · rintro ⟨z, hz, hzY⟩
        have he : z = p₂ := by simpa [C] using hz.symm
        exact hcon.1 (he ▸ hzY)
    have hodd : Odd (pathLength [p₃,p₄]) := by
      rw [pathLength]
      exact ⟨0, by simp⟩
    exact (hG.2.1 ⟨C, Y, hwheel, [p₃,p₄], hseg, hodd⟩).elim
  · exact (by have := hbound f hf; omega)

end Scratch181
