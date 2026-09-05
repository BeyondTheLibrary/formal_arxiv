import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.Thm101ClaimOne
import Workspace.Statements.S09.Thm_9_1

/-!
# Enlarging the distinguished strip in the closing paragraph of 9.4
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm94ClosingEnlarge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem end_eq_of_same_path {G : SimpleGraph V} {p : List V} {a b c d : V}
    (h : IsPathFrom G p a b) (h' : IsPathFrom G p c d) : a = c ∧ b = d := by
  constructor
  · exact Option.some.inj (h.2.1.symm.trans h'.2.1)
  · exact Option.some.inj (h.2.2.symm.trans h'.2.2)

private theorem mem_tail_iff_of_nodup {l : List V} (hnd : l.Nodup) {x u : V}
    (hh : l.head? = some u) : x ∈ l.tail ↔ (x ∈ l ∧ x ≠ u) := by
  cases l with
  | nil => simp at hh
  | cons c t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst c
      rw [List.nodup_cons] at hnd
      simp only [List.tail_cons, List.mem_cons]
      constructor
      · intro hx
        exact ⟨Or.inr hx, fun h => hnd.1 (h ▸ hx)⟩
      · rintro ⟨hx | hx, hne⟩
        · exact absurd hx hne
        · exact hx

/-- An old rung remains a rung after a new vertex is added to its first end class. -/
private theorem old_rung_left {G : SimpleGraph V} {A C B : Set V} {f : V} {p : List V}
    (hf : f ∉ stripVertices ((A, C, B) : Set V × Set V × Set V))
    (hp : IsSRung G (A, C, B) p) : IsSRung G (A ∪ {f}, C, B) p := by
  obtain ⟨a, b, hpath, ha, hb, htail, hdrop, hint⟩ := hp
  refine ⟨a, b, hpath, Or.inl ha, hb, ?_, hdrop, hint⟩
  intro z hz hznew
  rcases hznew with hzA | rfl
  · exact htail z hz hzA
  · exact hf (KnotFromTwist.mem_stripVertices_of_isSRung
      ⟨a, b, hpath, ha, hb, htail, hdrop, hint⟩ (List.mem_of_mem_tail hz))

/-- A neighbour of `f` away from the first end of a rung gives a new rung beginning at `f`.
The last neighbour is used so that the resulting suffix is induced after `f` is prepended. -/
private theorem new_rung_left {G : SimpleGraph V} {A C B : Set V} {f a b : V} {p : List V}
    (hf : f ∉ stripVertices ((A, C, B) : Set V × Set V × Set V))
    (hp : IsSRung G (A, C, B) p) (hpab : IsPathFrom G p a b)
    (hnear : ∃ z ∈ ({z : V | z ∈ p} \ {a} : Set V), G.Adj f z) :
    ∃ q : List V, IsSRung G (A ∪ {f}, C, B) q ∧ f ∈ q := by
  obtain ⟨a', b', hpath, haA, hbB, htail, hdrop, hint⟩ := hp
  have hend := end_eq_of_same_path hpath hpab
  rw [hend.1] at haA
  rw [hend.2] at hbB
  obtain ⟨z, ⟨hzP, hza⟩, hfz⟩ := hnear
  obtain ⟨k, hk, hq, hfhead, hsub, hunique, haiff, hmax⟩ :=
    Workspace.ProofLemmas.Thm101ClaimOne.last_attach hpab ⟨z, hzP, hfz⟩
  have hpos : 0 < p.length := PathBasics.path_length_pos hpab.1
  have hnd : p.Nodup := hpab.1.2.1
  obtain ⟨t, ht, htz⟩ := List.getElem_of_mem hzP
  have ht0 : t ≠ 0 := by
    intro htzero
    subst t
    have hzero : p[0]'ht = a := PathBasics.getElem_zero_of_head? hpab.2.1 ht
    exact hza (htz.symm.trans hzero)
  have htk : t ≤ k := by
    apply hmax t ht
    rwa [htz]
  have hkpos : 0 < k := by omega
  have hka : p[k]'hk ≠ a := by
    intro hka
    have hzero : p[0]'hpos = a := PathBasics.getElem_zero_of_head? hpab.2.1 hpos
    have : k = 0 := hnd.getElem_inj_iff.mp (hka.trans hzero.symm)
    omega
  have hfnq : f ∉ p.drop k := by
    intro hmem
    exact hf (KnotFromTwist.mem_stripVertices_of_isSRung
      ⟨a, b, hpab, haA, hbB, htail, hdrop, hint⟩ (hsub f hmem))
  have hnewpath : IsPathFrom G (f :: p.drop k) f b :=
    PathAttach.isPathFrom_cons hq hfhead hfnq
      (fun y hy hyhead hadj => hyhead (hunique y hy hadj))
  refine ⟨f :: p.drop k, ?_, by simp⟩
  refine ⟨f, b, hnewpath, Or.inr rfl, hbB, ?_, ?_, ?_⟩
  · intro y hy hyA
    simp only [List.tail_cons] at hy
    rcases hyA with hyA | rfl
    · have hyna : y ≠ a := fun hya => hka (haiff.mp (hya ▸ hy))
      exact htail y ((mem_tail_iff_of_nodup hnd hpab.2.1).mpr ⟨hsub y hy, hyna⟩) hyA
    · exact hfnq hy
  · intro y hy hyB
    have hnewnd : (f :: p.drop k).Nodup := hnewpath.1.2.1
    have hnewne : f :: p.drop k ≠ [] := List.cons_ne_nil _ _
    have hyall : y ∈ f :: p.drop k := List.mem_of_mem_dropLast hy
    have hnewlast : (f :: p.drop k).getLast hnewne = b := by
      have hh := List.getLast?_eq_some_getLast (l := f :: p.drop k) hnewne
      rw [hnewpath.2.2] at hh
      exact Option.some.inj hh.symm
    have hyb : y ≠ b := by
      have hh := (PathBasics.mem_dropLast_iff hnewnd hnewne).mp hy |>.2
      rwa [hnewlast] at hh
    simp only [List.mem_cons] at hyall
    rcases hyall with hyf | hyq
    · apply hf
      show f ∈ A ∪ B ∪ C
      rw [← hyf]
      exact Or.inl (Or.inr hyB)
    · have hynlast : y ≠ p.getLast (PathBasics.path_ne_nil hpab.1) := by
        have hlast : p.getLast (PathBasics.path_ne_nil hpab.1) = b := by
          have hh := List.getLast?_eq_some_getLast (l := p) (PathBasics.path_ne_nil hpab.1)
          exact Option.some.inj (hh.symm.trans hpab.2.2)
        simpa only [hlast] using hyb
      exact hdrop y ((PathBasics.mem_dropLast_iff hnd (PathBasics.path_ne_nil hpab.1)).mpr
        ⟨hsub y hyq, hynlast⟩) hyB
  · intro y hy
    have hyq : y ∈ (p.drop k).dropLast := hy
    have hqnd : (p.drop k).Nodup := hq.1.2.1
    have hqne : p.drop k ≠ [] := PathBasics.path_ne_nil hq.1
    have hyall : y ∈ p.drop k := List.mem_of_mem_dropLast hyq
    have hynb : y ≠ b := by
      have hlast : (p.drop k).getLast hqne = b := by
        have hh := List.getLast?_eq_some_getLast (l := p.drop k) hqne
        rw [hq.2.2] at hh
        exact Option.some.inj hh.symm
      have := (PathBasics.mem_dropLast_iff hqnd hqne).mp hyq |>.2
      rwa [hlast] at this
    apply hint y
    exact (PathBasics.mem_interior_iff_of_pathFrom hpab).mpr
      ⟨hsub y hyall, fun hya => hka (haiff.mp (hya ▸ hyall)), hynb⟩

/-- Adding `f` to the first end class preserves the strip axioms when `f` has a neighbour away
from that end on one old rung. -/
theorem isStrip_adjoin_left {G : SimpleGraph V} {A C B : Set V} {f a b : V} {p : List V}
    (hS : IsStrip G (A, C, B))
    (hf : f ∉ stripVertices ((A, C, B) : Set V × Set V × Set V))
    (hp : IsSRung G (A, C, B) p) (hpab : IsPathFrom G p a b)
    (hnear : ∃ z ∈ ({z : V | z ∈ p} \ {a} : Set V), G.Adj f z) :
    IsStrip G (A ∪ {f}, C, B) := by
  obtain ⟨hAB, hAC, hBC, hA, hB, hcover⟩ := hS
  obtain ⟨q, hq, hfq⟩ := new_rung_left hf hp hpab hnear
  have hfA : f ∉ A := fun h => hf (by show f ∈ A ∪ B ∪ C; exact Or.inl (Or.inl h))
  have hfB : f ∉ B := fun h => hf (by show f ∈ A ∪ B ∪ C; exact Or.inl (Or.inr h))
  have hfC : f ∉ C := fun h => hf (by show f ∈ A ∪ B ∪ C; exact Or.inr h)
  refine ⟨Set.disjoint_union_left.mpr ⟨hAB, Set.disjoint_singleton_left.mpr hfB⟩,
    Set.disjoint_union_left.mpr ⟨hAC, Set.disjoint_singleton_left.mpr hfC⟩,
    hBC, hA.mono Set.subset_union_left, hB, ?_⟩
  intro z hz
  by_cases hzf : z = f
  · subst z
    exact ⟨q, hq, hfq⟩
  · have hzold : z ∈ A ∪ B ∪ C := by
      rcases hz with ((hzA | rfl) | hzB) | hzC
      · exact Or.inl (Or.inl hzA)
      · exact absurd rfl hzf
      · exact Or.inl (Or.inr hzB)
      · exact Or.inr hzC
    obtain ⟨r, hr, hzr⟩ := hcover z hzold
    exact ⟨r, old_rung_left hf hr, hzr⟩

/-- If `f` copies a vertex of the first end class on `V(T)`, adding `f` preserves parallelity. -/
theorem parallel_adjoin_left {G : SimpleGraph V} {A C B : Set V}
    {T : Set V × Set V × Set V} {f a : V} (ha : a ∈ A)
    (hcopy : ∀ z ∈ stripVertices T, G.Adj f z ↔ G.Adj a z)
    (h : ParallelStripAntistrip G (A, C, B) T) :
    ParallelStripAntistrip G (A ∪ {f}, C, B) T := by
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨⟨hAX, hBY⟩, hXBC, hYAC⟩ := h
  refine ⟨⟨?_, hBY⟩, hXBC, ?_⟩
  · intro v hv z hz
    rcases hv with hv | rfl
    · exact hAX v hv z hz
    · exact (hcopy z (by show z ∈ X ∪ Y ∪ Z; rcases hz with hz | hz <;> tauto)).mpr
        (hAX a ha z hz)
  · intro y hy z hz
    rcases hz with (hzA | rfl) | hzC
    · exact hYAC y hy z (Or.inl hzA)
    · intro hyf
      exact hYAC y hy a (Or.inl ha)
        ((hcopy y (by show y ∈ X ∪ Y ∪ Z; exact Or.inl (Or.inr hy))).mp hyf.symm).symm
    · exact hYAC y hy z (Or.inr hzC)

/-- The co-parallel version of `parallel_adjoin_left`. -/
theorem coParallel_adjoin_left {G : SimpleGraph V} {A C B : Set V}
    {T : Set V × Set V × Set V} {f a : V} (ha : a ∈ A)
    (hcopy : ∀ z ∈ stripVertices T, G.Adj f z ↔ G.Adj a z)
    (h : CoParallel G (A, C, B) T) : CoParallel G (A ∪ {f}, C, B) T := by
  apply parallel_adjoin_left ha _ h
  intro z hz
  exact hcopy z (by simpa using hz)

/-- The mirror of `isStrip_adjoin_left`, adding `f` to the last end class. -/
theorem isStrip_adjoin_right {G : SimpleGraph V} {A C B : Set V} {f a b : V} {p : List V}
    (hS : IsStrip G (A, C, B))
    (hf : f ∉ stripVertices ((A, C, B) : Set V × Set V × Set V))
    (hp : IsSRung G (A, C, B) p) (hpab : IsPathFrom G p a b)
    (hnear : ∃ z ∈ ({z : V | z ∈ p} \ {b} : Set V), G.Adj f z) :
    IsStrip G (A, C, B ∪ {f}) := by
  have hSr : IsStrip G (B, C, A) := by
    simpa only [reverseStrip] using KnotFromTwist.isStrip_reverseStrip hS
  have hfr : f ∉ stripVertices ((B, C, A) : Set V × Set V × Set V) := by
    intro hmem
    apply hf
    change f ∈ A ∪ B ∪ C
    change f ∈ B ∪ A ∪ C at hmem
    rcases hmem with (hB | hA) | hC
    · exact Or.inl (Or.inr hB)
    · exact Or.inl (Or.inl hA)
    · exact Or.inr hC
  have hpr : IsSRung G (B, C, A) p.reverse := by
    simpa only [reverseStrip] using KnotFromTwist.isSRung_reverse hp
  have hpba : IsPathFrom G p.reverse b a := PathBasics.isPathFrom_reverse hpab
  have hnear' : ∃ z ∈ ({z : V | z ∈ p.reverse} \ {b} : Set V), G.Adj f z := by
    obtain ⟨z, ⟨hz, hzb⟩, hfz⟩ := hnear
    exact ⟨z, ⟨List.mem_reverse.mpr hz, hzb⟩, hfz⟩
  have hnew := isStrip_adjoin_left hSr hfr hpr hpba hnear'
  have hrev := KnotFromTwist.isStrip_reverseStrip hnew
  simpa only [reverseStrip] using hrev

/-- If `f` copies a vertex of the last end class on `V(T)`, adding `f` preserves parallelity. -/
theorem parallel_adjoin_right {G : SimpleGraph V} {A C B : Set V}
    {T : Set V × Set V × Set V} {f b : V} (hb : b ∈ B)
    (hcopy : ∀ z ∈ stripVertices T, G.Adj f z ↔ G.Adj b z)
    (h : ParallelStripAntistrip G (A, C, B) T) :
    ParallelStripAntistrip G (A, C, B ∪ {f}) T := by
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨⟨hAX, hBY⟩, hXBC, hYAC⟩ := h
  refine ⟨⟨hAX, ?_⟩, ?_, hYAC⟩
  · intro v hv z hz
    rcases hv with hv | rfl
    · exact hBY v hv z hz
    · apply (hcopy z ?_).mpr (hBY b hb z hz)
      show z ∈ X ∪ Y ∪ Z
      rcases hz with hz | hz
      · exact Or.inl (Or.inr hz)
      · exact Or.inr hz
  · intro x hx z hz
    rcases hz with (hzB | rfl) | hzC
    · exact hXBC x hx z (Or.inl hzB)
    · intro hxf
      exact hXBC x hx b (Or.inl hb)
        ((hcopy x (by show x ∈ X ∪ Y ∪ Z; exact Or.inl (Or.inl hx))).mp hxf.symm).symm
    · exact hXBC x hx z (Or.inr hzC)

/-- The co-parallel version of `parallel_adjoin_right`. -/
theorem coParallel_adjoin_right {G : SimpleGraph V} {A C B : Set V}
    {T : Set V × Set V × Set V} {f b : V} (hb : b ∈ B)
    (hcopy : ∀ z ∈ stripVertices T, G.Adj f z ↔ G.Adj b z)
    (h : CoParallel G (A, C, B) T) : CoParallel G (A, C, B ∪ {f}) T := by
  apply parallel_adjoin_right hb _ h
  intro z hz
  exact hcopy z (by simpa using hz)

private theorem complete_symm {G : SimpleGraph V} {X Y : Set V} (h : Complete G X Y) :
    Complete G Y X := fun y hy x hx => (h x hx y hy).symm

private theorem anticomplete_symm {G : SimpleGraph V} {X Y : Set V} (h : Anticomplete G X Y) :
    Anticomplete G Y X := fun y hy x hx hadj => h x hx y hy hadj.symm

/-- The construction behind `KnotFromTwist.exists_knot_of_twist`, with the four structural
pieces supplied directly instead of through a full striation.  This form is needed while the
odd-rung clause of an enlarged striation is still being proved. -/
private theorem exists_knot_of_twist_data {G : SimpleGraph V}
    {S₁ S₂ T₁ T₂ : Set V × Set V × Set V} {P₁ P₂ Q₁ Q₂ : List V}
    (hS₁ : IsStrip G S₁) (hS₂ : IsStrip G S₂)
    (hT₁ : IsAntistrip G T₁) (hT₂ : IsAntistrip G T₂)
    (dS : Disjoint (stripVertices S₁) (stripVertices S₂))
    (dT : Disjoint (stripVertices T₁) (stripVertices T₂))
    (d11 : Disjoint (stripVertices S₁) (stripVertices T₁))
    (d12 : Disjoint (stripVertices S₁) (stripVertices T₂))
    (d21 : Disjoint (stripVertices S₂) (stripVertices T₁))
    (d22 : Disjoint (stripVertices S₂) (stripVertices T₂))
    (hanti : Anticomplete G (stripVertices S₁) (stripVertices S₂))
    (hcomp : Complete G (stripVertices T₁) (stripVertices T₂))
    (htw : IsTwist G S₁ S₂ T₁ T₂)
    (hP₁ : IsSRung G S₁ P₁) (hP₂ : IsSRung G S₂ P₂)
    (hQ₁ : IsSRung Gᶜ T₁ Q₁) (hQ₂ : IsSRung Gᶜ T₂ Q₂)
    (lP₁ : 1 ≤ pathLength P₁) (lP₂ : 1 ≤ pathLength P₂)
    (lQ₁ : 1 ≤ pathLength Q₁) (lQ₂ : 1 ≤ pathLength Q₂) :
    ∃ P₂' Q₁' Q₂' : List V,
      (P₂' = P₂ ∨ P₂' = P₂.reverse) ∧
      (Q₁' = Q₁ ∨ Q₁' = Q₁.reverse) ∧
      (Q₂' = Q₂ ∨ Q₂' = Q₂.reverse) ∧ IsKnot G P₁ P₂' Q₁' Q₂' := by
  have app : ∀ (S₂' T₁' T₂' : Set V × Set V × Set V) (P₂' Q₁' Q₂' : List V),
      IsStrip G S₂' → IsAntistrip G T₁' → IsAntistrip G T₂' →
      stripVertices S₂' = stripVertices S₂ →
      stripVertices T₁' = stripVertices T₁ →
      stripVertices T₂' = stripVertices T₂ →
      IsSRung G S₂' P₂' → IsSRung Gᶜ T₁' Q₁' → IsSRung Gᶜ T₂' Q₂' →
      1 ≤ pathLength P₂' → 1 ≤ pathLength Q₁' → 1 ≤ pathLength Q₂' →
      ParallelStripAntistrip G S₁ T₁' → ParallelStripAntistrip G S₁ T₂' →
      ParallelStripAntistrip G S₂' T₁' → CoParallel G S₂' T₂' →
      IsKnot G P₁ P₂' Q₁' Q₂' := by
    intro S₂' T₁' T₂' P₂' Q₁' Q₂' hs2 ht1 ht2 e1 e2 e3 r1 r2 r3 l1 l2 l3
      p11 p12 p21 p22
    refine KnotFromTwist.isKnot_of_parallel_config hS₁ hs2 ht1 ht2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      p11 p12 p21 p22 hP₁ r1 r2 r3 lP₁ l1 l2 l3
    · rw [e1]; exact dS
    · rw [e2, e3]; exact dT
    · rw [e2]; exact d11
    · rw [e3]; exact d12
    · rw [e1, e2]; exact d21
    · rw [e1, e3]; exact d22
    · rw [e1]; exact hanti
    · rw [e2, e3]; exact hcomp
  have rs2 : IsStrip G (reverseStrip S₂) := KnotFromTwist.isStrip_reverseStrip hS₂
  have rt1 : IsAntistrip G (reverseStrip T₁) := KnotFromTwist.isAntistrip_reverseStrip hT₁
  have rt2 : IsAntistrip G (reverseStrip T₂) := KnotFromTwist.isAntistrip_reverseStrip hT₂
  have rrP₂ : IsSRung G (reverseStrip S₂) P₂.reverse := KnotFromTwist.isSRung_reverse hP₂
  have rrQ₁ : IsSRung Gᶜ (reverseStrip T₁) Q₁.reverse := KnotFromTwist.isSRung_reverse hQ₁
  have rrQ₂ : IsSRung Gᶜ (reverseStrip T₂) Q₂.reverse := KnotFromTwist.isSRung_reverse hQ₂
  have rlP₂ : 1 ≤ pathLength P₂.reverse := by rwa [PathBasics.pathLength_reverse]
  have rlQ₁ : 1 ≤ pathLength Q₁.reverse := by rwa [PathBasics.pathLength_reverse]
  have rlQ₂ : 1 ≤ pathLength Q₂.reverse := by rwa [PathBasics.pathLength_reverse]
  rcases htw with ⟨hag, hdis⟩ | ⟨hag, hdis⟩
  · rcases hag with ⟨b11, b21⟩ | ⟨b11, b21⟩ <;> rcases hdis with ⟨b12, b22⟩ | ⟨b12, b22⟩
    · exact ⟨P₂, Q₁, Q₂, Or.inl rfl, Or.inl rfl, Or.inl rfl,
        app S₂ T₁ T₂ P₂ Q₁ Q₂ hS₂ hT₁ hT₂ rfl rfl rfl hP₂ hQ₁ hQ₂ lP₂ lQ₁ lQ₂
          b11 b12 b21 b22⟩
    · exact ⟨P₂, Q₁, Q₂.reverse, Or.inl rfl, Or.inl rfl, Or.inr rfl,
        app S₂ T₁ (reverseStrip T₂) P₂ Q₁ Q₂.reverse hS₂ hT₁ rt2 rfl rfl
          (KnotFromTwist.stripVertices_reverseStrip _) hP₂ hQ₁ rrQ₂ lP₂ lQ₁ rlQ₂
          b11 ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b12) b21
          ((KnotFromTwist.coParallel_reverseStrip_right _ _).mpr b22)⟩
    · exact ⟨P₂, Q₁.reverse, Q₂, Or.inl rfl, Or.inr rfl, Or.inl rfl,
        app S₂ (reverseStrip T₁) T₂ P₂ Q₁.reverse Q₂ hS₂ rt1 hT₂ rfl
          (KnotFromTwist.stripVertices_reverseStrip _) rfl hP₂ rrQ₁ hQ₂ lP₂ rlQ₁ lQ₂
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b11) b12
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b21) b22⟩
    · exact ⟨P₂, Q₁.reverse, Q₂.reverse, Or.inl rfl, Or.inr rfl, Or.inr rfl,
        app S₂ (reverseStrip T₁) (reverseStrip T₂) P₂ Q₁.reverse Q₂.reverse hS₂ rt1 rt2 rfl
          (KnotFromTwist.stripVertices_reverseStrip _) (KnotFromTwist.stripVertices_reverseStrip _)
          hP₂ rrQ₁ rrQ₂ lP₂ rlQ₁ rlQ₂
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b11)
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b12)
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b21)
          ((KnotFromTwist.coParallel_reverseStrip_right _ _).mpr b22)⟩
  · rcases hag with ⟨b12, b22⟩ | ⟨b12, b22⟩ <;> rcases hdis with ⟨b11, b21⟩ | ⟨b11, b21⟩
    · exact ⟨P₂.reverse, Q₁, Q₂, Or.inr rfl, Or.inl rfl, Or.inl rfl,
        app (reverseStrip S₂) T₁ T₂ P₂.reverse Q₁ Q₂ rs2 hT₁ hT₂
          (KnotFromTwist.stripVertices_reverseStrip _) rfl rfl rrP₂ hQ₁ hQ₂ rlP₂ lQ₁ lQ₂
          b11 b12 ((KnotFromTwist.parallel_reverseStrip_left _ _).mpr b21)
          ((KnotFromTwist.coParallel_reverseStrip_left _ _).mpr b22)⟩
    · exact ⟨P₂.reverse, Q₁.reverse, Q₂, Or.inr rfl, Or.inr rfl, Or.inl rfl,
        app (reverseStrip S₂) (reverseStrip T₁) T₂ P₂.reverse Q₁.reverse Q₂ rs2 rt1 hT₂
          (KnotFromTwist.stripVertices_reverseStrip _) (KnotFromTwist.stripVertices_reverseStrip _) rfl
          rrP₂ rrQ₁ hQ₂ rlP₂ rlQ₁ lQ₂
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b11) b12
          ((KnotFromTwist.parallel_reverseStrip_left _ _).mpr
            ((KnotFromTwist.coParallel_reverseStrip_right _ _).mpr b21))
          ((KnotFromTwist.coParallel_reverseStrip_left _ _).mpr b22)⟩
    · exact ⟨P₂.reverse, Q₁, Q₂.reverse, Or.inr rfl, Or.inl rfl, Or.inr rfl,
        app (reverseStrip S₂) T₁ (reverseStrip T₂) P₂.reverse Q₁ Q₂.reverse rs2 hT₁ rt2
          (KnotFromTwist.stripVertices_reverseStrip _) rfl (KnotFromTwist.stripVertices_reverseStrip _)
          rrP₂ hQ₁ rrQ₂ rlP₂ lQ₁ rlQ₂ b11
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b12)
          ((KnotFromTwist.parallel_reverseStrip_left _ _).mpr b21)
          ((KnotFromTwist.coParallel_reverseStrip_left _ _).mpr
            ((KnotFromTwist.coParallel_reverseStrip_right _ _).mpr b22))⟩
    · exact ⟨P₂.reverse, Q₁.reverse, Q₂.reverse, Or.inr rfl, Or.inr rfl, Or.inr rfl,
        app (reverseStrip S₂) (reverseStrip T₁) (reverseStrip T₂)
          P₂.reverse Q₁.reverse Q₂.reverse rs2 rt1 rt2
          (KnotFromTwist.stripVertices_reverseStrip _) (KnotFromTwist.stripVertices_reverseStrip _)
          (KnotFromTwist.stripVertices_reverseStrip _) rrP₂ rrQ₁ rrQ₂ rlP₂ rlQ₁ rlQ₂
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b11)
          ((KnotFromTwist.parallel_reverseStrip_right _ _).mpr b12)
          ((KnotFromTwist.parallel_reverseStrip_left _ _).mpr
            ((KnotFromTwist.coParallel_reverseStrip_right _ _).mpr b21))
          ((KnotFromTwist.coParallel_reverseStrip_left _ _).mpr
            ((KnotFromTwist.coParallel_reverseStrip_right _ _).mpr b22))⟩

private theorem one_le_pathLength_of_rung {G : SimpleGraph V}
    {R : Set V × Set V × Set V} {p : List V} (hR : IsStrip G R) (hp : IsSRung G R p) :
    1 ≤ pathLength p := by
  obtain ⟨A, C, B⟩ := R
  obtain ⟨hAB, -, -, -, -, -⟩ := hR
  obtain ⟨a, b, hpath, ha, hb, -⟩ := hp
  by_contra hnot
  have hlen : p.length = 1 := by
    have hpos := PathBasics.path_length_pos hpath.1
    simp only [pathLength] at hnot
    omega
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hlen
  subst p
  have hza : z = a := Option.some.inj (by simpa using hpath.2.1)
  have hzb : z = b := Option.some.inj (by simpa using hpath.2.2)
  exact Set.disjoint_left.mp hAB ha (hza.symm.trans hzb ▸ hb)

/-- The parity clause survives replacing one strip by a larger strip with the same relations to
all antistrips.  A new rung is placed in a twist with one old rung and two old antirungs; 9.1
then says that it is odd. -/
theorem odd_rungs_of_replacement {G : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    (hG : Berge G) (hL : IsStriation G S T) {f : V} (hfL : f ∉ striationVertices S T)
    (i : Fin m) (R : Set V × Set V × Set V) (hR : IsStrip G R)
    (hverts : stripVertices R = stripVertices (S i) ∪ {f})
    (hfanti : ∀ k : Fin m, i ≠ k → VertexAnticomplete G f (stripVertices (S k)))
    (hpar : ∀ j : Fin n, ParallelStripAntistrip G (S i) (T j) →
      ParallelStripAntistrip G R (T j))
    (hco : ∀ j : Fin n, CoParallel G (S i) (T j) → CoParallel G R (T j)) :
    ∀ p : List V, IsSRung G R p → Odd (pathLength p) := by
  intro p hp
  have hm2 : 2 ≤ m := hL.2.2.2.2.2.2.2.1
  obtain ⟨i', hii'⟩ : ∃ i' : Fin m, i ≠ i' := by
    by_cases hi : (i : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have : (i : ℕ) = 1 := congrArg Fin.val h
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      exact hi (congrArg Fin.val h)
  obtain ⟨j, j', hjj', htw⟩ : ∃ j j' : Fin n, j ≠ j' ∧
      IsTwist G (S i) (S i') (T j) (T j') := by
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hlt
    · exact absurd heq hii'
    · obtain ⟨j, j', hjj', ht⟩ := hL.2.2.2.2.2.2.2.2.2.2.2.2.1 i' i hgt
      refine ⟨j, j', hjj', ?_⟩
      simp only [IsTwist, AgreeOn] at ht ⊢
      tauto
  have htwR : IsTwist G R (S i') (T j) (T j') := by
    have hpj := hpar j
    have hpj' := hpar j'
    have hcj := hco j
    have hcj' := hco j'
    simp only [IsTwist, AgreeOn] at htw ⊢
    tauto
  obtain ⟨p₂, hp₂⟩ : ∃ p₂ : List V, IsSRung G (S i') p₂ := by
    obtain ⟨a, ha⟩ := (hL.1 i').2.2.2.1
    obtain ⟨p₂, hp₂, -⟩ :=
      (hL.1 i').2.2.2.2.2 a (Set.mem_union_left _ (Set.mem_union_left _ ha))
    exact ⟨p₂, hp₂⟩
  obtain ⟨q₁, hq₁⟩ : ∃ q₁ : List V, IsSRung Gᶜ (T j) q₁ := by
    obtain ⟨x, hx⟩ := (hL.2.1 j).2.2.2.1
    obtain ⟨q₁, hq₁, -⟩ :=
      (hL.2.1 j).2.2.2.2.2 x (Set.mem_union_left _ (Set.mem_union_left _ hx))
    exact ⟨q₁, hq₁⟩
  obtain ⟨q₂, hq₂⟩ : ∃ q₂ : List V, IsSRung Gᶜ (T j') q₂ := by
    obtain ⟨x, hx⟩ := (hL.2.1 j').2.2.2.1
    obtain ⟨q₂, hq₂, -⟩ :=
      (hL.2.1 j').2.2.2.2.2 x (Set.mem_union_left _ (Set.mem_union_left _ hx))
    exact ⟨q₂, hq₂⟩
  have oldDisjS : Disjoint (stripVertices (S i)) (stripVertices (S i')) :=
    hL.2.2.1 i i' hii'
  have dS : Disjoint (stripVertices R) (stripVertices (S i')) := by
    rw [hverts]
    refine Set.disjoint_union_left.mpr ⟨oldDisjS, Set.disjoint_singleton_left.mpr ?_⟩
    intro hfmem
    exact hfL (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i', hfmem⟩))
  have dT : Disjoint (stripVertices (T j)) (stripVertices (T j')) :=
    hL.2.2.2.1 j j' hjj'
  have disjRT : ∀ k : Fin n, Disjoint (stripVertices R) (stripVertices (T k)) := by
    intro k
    rw [hverts]
    refine Set.disjoint_union_left.mpr ⟨hL.2.2.2.2.1 i k, Set.disjoint_singleton_left.mpr ?_⟩
    intro hfmem
    exact hfL (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨k, hfmem⟩))
  have hantiOld : Anticomplete G (stripVertices (S i)) (stripVertices (S i')) := by
    rcases lt_trichotomy i i' with hlt | heq | hgt
    · exact hL.2.2.2.2.2.2.2.2.2.1 i i' hlt
    · exact absurd heq hii'
    · exact anticomplete_symm (hL.2.2.2.2.2.2.2.2.2.1 i' i hgt)
  have hantiR : Anticomplete G (stripVertices R) (stripVertices (S i')) := by
    rw [hverts]
    intro z hz w hw
    rcases hz with hz | rfl
    · exact hantiOld z hz w hw
    · exact hfanti i' hii' w hw
  have hcompT : Complete G (stripVertices (T j)) (stripVertices (T j')) := by
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · exact hL.2.2.2.2.2.2.2.2.2.2.1 j j' hlt
    · exact absurd heq hjj'
    · exact complete_symm (hL.2.2.2.2.2.2.2.2.2.2.1 j' j hgt)
  have oddPos : ∀ {k : ℕ}, Odd k → 1 ≤ k := by rintro k ⟨t, rfl⟩; omega
  obtain ⟨p₂', q₁', q₂', -, -, -, hknot⟩ := exists_knot_of_twist_data hR (hL.1 i')
    (hL.2.1 j) (hL.2.1 j') dS dT (disjRT j) (disjRT j')
    (hL.2.2.2.2.1 i' j) (hL.2.2.2.2.1 i' j') hantiR hcompT htwR hp hp₂ hq₁ hq₂
    (one_le_pathLength_of_rung hR hp)
    (oddPos (hL.2.2.2.2.2.1 i' p₂ hp₂))
    (oddPos (hL.2.2.2.2.2.2.1 j q₁ hq₁))
    (oddPos (hL.2.2.2.2.2.2.1 j' q₂ hq₂))
  exact (Workspace.Statements.S09.SPGT.thm_9_1 G hG p p₂' q₁' q₂' hknot).1.1

end Workspace.ProofLemmas.Thm94ClosingEnlarge
