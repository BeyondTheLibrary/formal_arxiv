import Mathlib
import Workspace.ProofLemmas.Thm142PathSetup
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.Thm101K4Appearance
import Workspace.Statements.S10.Thm_10_4

/-!
# 14.2: the non-full left attachment set

This file isolates the final branch on printed pages 89--90.  The path `f` is the globally
minimal path supplied by `Thm142PathSetup`; the paper's set `A'` is represented literally in
the proof below.  The argument uses 10.4 only through its exact project theorem.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm142NonFullCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore
open Workspace.ProofLemmas.Thm142ABComplete

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two attachments at diagonally opposite ends of two rungs are not local. -/
private theorem diagonal_attachments_not_local {G : SimpleGraph V}
    {a b : Fin 3 → V} {R : Fin 3 → List V} {X : Set V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (ha : a 0 ∈ X) (hb : b 1 ∈ X) :
    ¬ LocalForPrism a b (R 0) (R 1) (R 2) X := by
  obtain ⟨-, -, hab, hR0, hR1, hR2, -, -, -⟩ := id hprism
  have haR0 : a 0 ∈ R 0 := List.mem_of_mem_head? hR0.2.1
  have hbR1 : b 1 ∈ R 1 := List.mem_of_mem_getLast? hR1.2.2
  rintro (h0 | h1 | h2 | htop | hbot)
  · exact (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hprism
      (i := 0) (j := 1) (by decide) (b 1) (h0 hb)) hbR1
  · exact (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hprism
      (i := 0) (j := 1) (by decide) (a 0) haR0) (h1 ha)
  · exact (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hprism
      (i := 0) (j := 2) (by decide) (a 0) haR0) (h2 ha)
  · have hm := htop hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact hab 0 1 h.symm
    · exact hab 1 1 h.symm
    · exact hab 2 1 h.symm
  · have hm := hbot ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with h | h | h
    · exact hab 0 0 h
    · exact hab 0 1 h
    · exact hab 0 2 h

/-- The precise 10.4 call used below.  A short first rung makes its conditional major-vertex
hypothesis vacuous. -/
private theorem legal_jump_of_odd_first_rung (G : SimpleGraph V) (hG : InF5 G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hodd : ¬ Even (pathLength (R 0)))
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hR2 : ∀ v ∈ attachments G F K, v ∉ R 2) :
    F.Nontrivial ∧ attachments G F K = ({a 0, b 0, a 1, b 1} : Set V) := by
  apply _root_.Workspace.Statements.S10.SPGT.thm_10_4 G hG.1.1
    (noK4_of_inF3 hG.1) a b R K F hprism hK hFK hFconn
  · intro heven
    exact (hodd heven.2.1).elim
  · exact hFloc
  · exact hR2

/-- If a path has an even, nonempty block of internal vertices, closing it through one clean
extra vertex produces the odd hole repeatedly used in the printed argument. -/
private theorem even_internal_path_cannot_close {G : SimpleGraph V} {f : List V}
    {u v w : V} (hG : Berge G) (hlen : 2 ≤ f.length) (heven : Even f.length)
    (hp : IsPathFrom G (u :: (f ++ [v])) u v)
    (hwu : G.Adj w u) (hwv : G.Adj w v) (hw : w ∉ u :: (f ++ [v]))
    (hwint : ∀ x ∈ interior (u :: (f ++ [v])), ¬ G.Adj w x) : False := by
  have hhole : IsHoleList G (w :: u :: (f ++ [v])) :=
    PrismBasics.isHoleList_of_path_add_vertex hp (by
      simp [pathLength]
      omega) hwu hwv hw hwint
  have hev := hG.1 _ hhole
  have hev' : Even (f.length + 3) := by
    simpa [holeLength, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hev
  exact (Nat.not_even_iff_odd.mpr (heven.add_odd (by norm_num))) hev'

/-- The `A' ≠ A` branch in the last paragraph of the proof of 14.2. -/
theorem left_nonfull_case_false (G : SimpleGraph V) (hG : InF5 G)
    (A B C D F : Set V) (hcube : MaximalCube G A B C D)
    {f : List V} {a₀ b₀ : V} (hcfg : ABPathConfig G A B C D F f a₀ b₀)
    (hCD : Anticomplete G (C ∪ D) {z : V | z ∈ f})
    (hAnonfull : ∃ x ∈ A,
      ¬ (G.Adj x (f[0]'(by have := hcfg.len; omega)) ∧
        ∃ y ∈ B, ¬ G.Adj x y ∧
          G.Adj y (f[f.length - 1]'(by have := hcfg.len; omega)))) : False := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube.1
  have hfpos : 0 < f.length := by have := hcfg.len; omega
  have hlast : f.length - 1 < f.length := by omega
  have hfnd : f.Nodup := PathBasics.path_nodup hcfg.path
  let f₁ : V := f[0]'hfpos
  let fk : V := f[f.length - 1]'hlast
  let A' : Set V :=
    {x : V | x ∈ A ∧ G.Adj x f₁ ∧ ∃ y ∈ B, ¬ G.Adj x y ∧ G.Adj y fk}
  have ha₀A' : a₀ ∈ A' := by
    refine ⟨hcfg.memA, (hcfg.adjA 0 hfpos).2 rfl, b₀, hcfg.memB, hcfg.nonadj, ?_⟩
    exact (hcfg.adjB (f.length - 1) hlast).2 rfl
  obtain ⟨aout, haoutA, haout⟩ := hAnonfull
  have haoutA' : aout ∉ A' := by
    intro h
    exact haout ⟨h.2.1, h.2.2⟩
  obtain ⟨a₁, b₁, b₂, a₂, hsq, ha₁A', ha₂notA'⟩ :=
    exists_square_cross_left sAB A' ⟨a₀, hcfg.memA, ha₀A'⟩
      ⟨aout, haoutA, haoutA'⟩
  have ha₁A : a₁ ∈ A := hsq.2.1
  have ha₂A : a₂ ∈ A := hsq.2.2.1
  have hb₁B : b₁ ∈ B := hsq.2.2.2.1
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ :=
    CubeMajorCoreContradiction.square_adj hsq
  obtain ⟨-, ha₁f₁, b, hbB, ha₁b, hbfk⟩ := ha₁A'
  obtain ⟨d, hdD⟩ := nD
  obtain ⟨c, hcC, hcd⟩ := exists_adj_of_mem_right dCD sCD hdD

  have hq : IsPathFrom G (a₁ :: (f ++ [b])) a₁ b := by
    exact full_path_of_end_attachments dAB hcfg ha₁A hbB ha₁b ha₁f₁ hbfk
  have hfeven : Even f.length := by
    apply even_length_of_end_attachments hG.1.1 hcube.1 hcfg ha₁A hbB ha₁b ha₁f₁ hbfk
    · intro c' hc' x hx
      exact hCD c' (Or.inl hc') x hx
    · intro d' hd' x hx
      exact hCD d' (Or.inr hd') x hx
  have hbne_b₁ : b ≠ b₁ := by
    intro h
    exact ha₁b (h ▸ e01)

  let aa : Fin 3 → V := ![a₁, a₂, c]
  let bb : Fin 3 → V := ![b₁, b₂, d]
  let R : Fin 3 → List V := ![[a₁, b₁], [a₂, b₂], [c, d]]
  let K : Set V := {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2}

  have ha₁c : G.Adj a₁ c := cAC a₁ ha₁A c hcC
  have ha₂c : G.Adj a₂ c := cAC a₂ ha₂A c hcC
  have hb₁d : G.Adj b₁ d := cBD b₁ hb₁B d hdD
  have hb₂d : G.Adj b₂ d := cBD b₂ hb₂B d hdD
  have ha₁d : ¬ G.Adj a₁ d := aAD a₁ ha₁A d hdD
  have ha₂d : ¬ G.Adj a₂ d := aAD a₂ ha₂A d hdD
  have hb₁c : ¬ G.Adj b₁ c := aBC b₁ hb₁B c hcC
  have hb₂c : ¬ G.Adj b₂ c := aBC b₂ hb₂B c hcC

  have hcross01 : ∀ u ∈ [a₁, b₁], ∀ v ∈ [a₂, b₂],
      (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => e30.symm⟩
    · exact ⟨fun h => (n02 h).elim, by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [(ne23 h).elim, (ne01 h).elim]⟩
    · exact ⟨fun h => (n13 h).elim, by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [(ne01 h.symm).elim, (ne23 h.symm).elim]⟩
    · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => e12⟩
  have hcross02 : ∀ u ∈ [a₁, b₁], ∀ v ∈ [c, d],
      (G.Adj u v ↔ (u = a₁ ∧ v = c) ∨ (u = b₁ ∧ v = d)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => ha₁c⟩
    · exact ⟨fun h => (ha₁d h).elim,
        by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [(Set.disjoint_left.mp dCD hcC (h ▸ hdD)).elim,
          (Set.disjoint_left.mp dAB ha₁A (h ▸ hb₁B)).elim]⟩
    · exact ⟨fun h => (hb₁c h).elim,
        by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [(Set.disjoint_left.mp dAB (h ▸ ha₁A) hb₁B).elim,
          (Set.disjoint_left.mp dCD hcC (h ▸ hdD)).elim]⟩
    · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => hb₁d⟩
  have hcross12 : ∀ u ∈ [a₂, b₂], ∀ v ∈ [c, d],
      (G.Adj u v ↔ (u = a₂ ∧ v = c) ∨ (u = b₂ ∧ v = d)) := by
    intro u hu v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => ha₂c⟩
    · exact ⟨fun h => (ha₂d h).elim,
        by rintro (⟨-, h⟩ | ⟨h, -⟩); exacts [(Set.disjoint_left.mp dCD hcC (h ▸ hdD)).elim,
          (Set.disjoint_left.mp dAB ha₂A (h ▸ hb₂B)).elim]⟩
    · exact ⟨fun h => (hb₂c h).elim,
        by rintro (⟨h, -⟩ | ⟨-, h⟩); exacts [(Set.disjoint_left.mp dAB (h ▸ ha₂A) hb₂B).elim,
          (Set.disjoint_left.mp dCD hcC (h ▸ hdD)).elim]⟩
    · exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => hb₂d⟩

  have hprism : FormPrism G aa bb (R 0) (R 1) (R 2) := by
    dsimp [aa, bb, R]
    refine formPrism_of_data e30.symm ha₁c ha₂c e12 hb₁d hb₂d
      ne01 ne02 (fun h => Set.disjoint_left.mp dAD ha₁A (h ▸ hdD))
      ne13.symm ne23.symm (fun h => Set.disjoint_left.mp dAD ha₂A (h ▸ hdD))
      (fun h => Set.disjoint_left.mp dBC (h ▸ hb₁B) hcC)
      (fun h => Set.disjoint_left.mp dBC (h ▸ hb₂B) hcC)
      (fun h => Set.disjoint_left.mp dCD hcC (h ▸ hdD))
      ⟨PathBasics.isPathList_pair e01, rfl, rfl⟩
      ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩
      ⟨PathBasics.isPathList_pair hcd, rfl, rfl⟩ hcross01 hcross02 hcross12

  have hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2} := rfl
  have hoddR0 : ¬ Even (pathLength (R 0)) := by
    simp [R, pathLength]
  let Ff : Set V := {x : V | x ∈ f}
  have hFfconn : ConnectedSet G Ff :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hcfg.path
  have hfK : ∀ x ∈ f, x ∈ Kᶜ := by
    intro x hx hxK
    have hout := hcfg.outside x hx
    rcases hxK with (hx0 | hx1) | hx2
    · have hx0' : x = a₁ ∨ x = b₁ := by simpa [R] using hx0
      rcases hx0' with h | h
      · exact hout (h ▸ Or.inl (Or.inl (Or.inl ha₁A)))
      · exact hout (h ▸ Or.inl (Or.inl (Or.inr hb₁B)))
    · have hx1' : x = a₂ ∨ x = b₂ := by simpa [R] using hx1
      rcases hx1' with h | h
      · exact hout (h ▸ Or.inl (Or.inl (Or.inl ha₂A)))
      · exact hout (h ▸ Or.inl (Or.inl (Or.inr hb₂B)))
    · have hx2' : x = c ∨ x = d := by simpa [R] using hx2
      rcases hx2' with h | h
      · exact hout (h ▸ Or.inl (Or.inr hcC))
      · exact hout (h ▸ Or.inr hdD)
  have hFfK : Ff ⊆ Kᶜ := fun _ hx => hfK _ hx

  have ha₁only : ∀ (i : ℕ) (hi : i < f.length), G.Adj a₁ (f[i]'hi) → i = 0 := by
    intro i hi hai
    rcases attachment_indices_span hcfg ha₁A hbB ha₁b hi hlast hai hbfk with h | h
    · exact h.1
    · omega

  -- PAPER 5594--5599.  If `f_k-b₂`, 10.4 supplies the other two attachments.
  have hnotfkb₂ : ¬ G.Adj fk b₂ := by
    intro hfkb₂
    have ha₁att : a₁ ∈ attachments G Ff K := by
      exact ⟨by simp [K, R], f₁, List.getElem_mem hfpos, ha₁f₁⟩
    have hb₂att : b₂ ∈ attachments G Ff K := by
      exact ⟨by simp [K, R], fk, List.getElem_mem hlast, hfkb₂.symm⟩
    have hnonlocal :
        ¬ LocalForPrism aa bb (R 0) (R 1) (R 2) (attachments G Ff K) := by
      apply diagonal_attachments_not_local hprism
      · simpa [aa] using ha₁att
      · simpa [bb] using hb₂att
    have hnoR2 : ∀ v ∈ attachments G Ff K, v ∉ R 2 := by
      rintro v ⟨-, x, hx, hvx⟩ hvR
      have hvR' : v = c ∨ v = d := by simpa [R] using hvR
      rcases hvR' with h | h
      · subst v
        exact hCD c (Or.inl hcC) x hx hvx
      · subst v
        exact hCD d (Or.inr hdD) x hx hvx
    have hjump := legal_jump_of_odd_first_rung G hG aa bb R K Ff hprism hK hFfK
      hFfconn hoddR0 hnonlocal hnoR2
    have ha₂att : a₂ ∈ attachments G Ff K := by
      rw [hjump.2]
      simp [aa, bb]
    have hb₁att : b₁ ∈ attachments G Ff K := by
      rw [hjump.2]
      simp [aa, bb]
    obtain ⟨-, xa, hxa, ha₂xa⟩ := ha₂att
    obtain ⟨ia, hia, hxaEq⟩ := List.mem_iff_getElem.mp hxa
    subst xa
    obtain ⟨-, xb, hxb, hb₁xb⟩ := hb₁att
    obtain ⟨ib, hib, hxbEq⟩ := List.mem_iff_getElem.mp hxb
    subst xb
    have ha₂b₁ : ¬ G.Adj a₂ b₁ := fun h => n13 h.symm
    rcases attachment_indices_span hcfg ha₂A hb₁B ha₂b₁ hia hib ha₂xa hb₁xb with hor | hor
    · have ha₂f₁ : G.Adj a₂ f₁ := by
        dsimp [f₁]
        simpa only [(getElem_eq_iff hfnd hia hfpos).mpr hor.1] using ha₂xa
      have hb₁fk : G.Adj b₁ fk := by
        dsimp [fk]
        simpa only [(getElem_eq_iff hfnd hib hlast).mpr hor.2] using hb₁xb
      exact ha₂notA' ⟨ha₂A, ha₂f₁, b₁, hb₁B, ha₂b₁, hb₁fk⟩
    · have hb₁f₁ : G.Adj b₁ f₁ := by
        dsimp [f₁]
        simpa only [(getElem_eq_iff hfnd hib hfpos).mpr hor.1] using hb₁xb
      have ha₂fk : G.Adj a₂ fk := by
        dsimp [fk]
        simpa only [(getElem_eq_iff hfnd hia hlast).mpr hor.2] using ha₂xa
      have hb₁only : ∀ (i : ℕ) (hi : i < f.length),
          G.Adj b₁ (f[i]'hi) → i = 0 := by
        intro i hi hbi
        rcases attachment_indices_span hcfg ha₂A hb₁B ha₂b₁ hlast hi ha₂fk hbi with h | h
        · omega
        · exact h.1
      have ha₂only : ∀ (i : ℕ) (hi : i < f.length),
          G.Adj a₂ (f[i]'hi) → i = f.length - 1 := by
        intro i hi hai
        rcases attachment_indices_span hcfg ha₂A hb₁B ha₂b₁ hi hfpos hai hb₁f₁ with h | h
        · omega
        · exact h.2
      have hb₂only : ∀ (i : ℕ) (hi : i < f.length),
          G.Adj b₂ (f[i]'hi) → i = f.length - 1 := by
        intro i hi hbi
        rcases attachment_indices_span hcfg ha₁A hb₂B n02 hfpos hi ha₁f₁ hbi with h | h
        · exact h.2
        · omega
      have hno : ∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
          (x = f₁ ∧ (k = a₁ ∨ k = b₁)) ∨ (x = fk ∧ (k = a₂ ∨ k = b₂)) := by
        intro x hx k hk hxk
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        rcases hk with (hk0 | hk1) | hk2
        · have hk0' : k = a₁ ∨ k = b₁ := by simpa [R] using hk0
          rcases hk0' with hk | hk
          · subst k
            left
            refine ⟨?_, Or.inl rfl⟩
            dsimp [f₁]
            exact (getElem_eq_iff hfnd hi hfpos).mpr (ha₁only i hi hxk.symm)
          · subst k
            left
            refine ⟨?_, Or.inr rfl⟩
            dsimp [f₁]
            exact (getElem_eq_iff hfnd hi hfpos).mpr (hb₁only i hi hxk.symm)
        · have hk1' : k = a₂ ∨ k = b₂ := by simpa [R] using hk1
          rcases hk1' with hk | hk
          · subst k
            right
            refine ⟨?_, Or.inl rfl⟩
            dsimp [fk]
            exact (getElem_eq_iff hfnd hi hlast).mpr (ha₂only i hi hxk.symm)
          · subst k
            right
            refine ⟨?_, Or.inr rfl⟩
            dsimp [fk]
            exact (getElem_eq_iff hfnd hi hlast).mpr (hb₂only i hi hxk.symm)
        · have hk2' : k = c ∨ k = d := by simpa [R] using hk2
          rcases hk2' with hk | hk
          · subst k
            exact (hCD c (Or.inl hcC) _ (List.getElem_mem hi) hxk.symm).elim
          · subst k
            exact (hCD d (Or.inr hdD) _ (List.getElem_mem hi) hxk.symm).elim
      have happ :=
        Workspace.ProofLemmas.Thm101K4Appearance.appears_K4_of_case_one
          G hG.1.1 aa bb R K f f₁ fk a₁ b₁ a₂ b₂ hprism hK
          (isPathFrom_self hcfg.path hfpos) hfK
          (by simp [R]) (by simp [R]) e01 ha₁f₁.symm hb₁f₁.symm
          (by simp [R]) (by simp [R]) e23.symm ha₂fk.symm hfkb₂ hno
      rcases happ with ⟨n, H, K', hsub, ⟨φ⟩⟩
      exact (hG.1.2 n H hsub).1 ⟨K', ⟨φ.symm⟩⟩

  -- The remaining lines use the connected set `F' = V(f) ∪ {b}`.
  have hbne_b₂ : b ≠ b₂ := by
    intro h
    subst b
    exact hnotfkb₂ hbfk.symm
  let F' : Set V := Ff ∪ {b}
  have hF'conn : ConnectedSet G F' := by
    apply ConnectedSetUnionAttach.connectedSet_union_singleton hFfconn
    exact ⟨fk, List.getElem_mem hlast, hbfk⟩
  have hbK : b ∈ Kᶜ := by
    intro hbK
    rcases hbK with (hb0 | hb1) | hb2
    · have hb0' : b = a₁ ∨ b = b₁ := by simpa [R] using hb0
      rcases hb0' with h | h
      · exact Set.disjoint_left.mp dAB ha₁A (h ▸ hbB)
      · exact hbne_b₁ h
    · have hb1' : b = a₂ ∨ b = b₂ := by simpa [R] using hb1
      rcases hb1' with h | h
      · exact Set.disjoint_left.mp dAB ha₂A (h ▸ hbB)
      · exact hbne_b₂ h
    · have hb2' : b = c ∨ b = d := by simpa [R] using hb2
      rcases hb2' with h | h
      · exact Set.disjoint_left.mp dBC hbB (h ▸ hcC)
      · exact Set.disjoint_left.mp dBD hbB (h ▸ hdD)
  have hF'K : F' ⊆ Kᶜ := by
    intro x hx
    rcases hx with hx | hx
    · exact hfK x hx
    · rw [Set.mem_singleton_iff] at hx
      exact hx ▸ hbK
  have hcnoF' : ∀ x ∈ F', ¬ G.Adj c x := by
    intro x hx
    rcases hx with hx | hx
    · exact hCD c (Or.inl hcC) x hx
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact fun h => aBC b hbB c hcC h.symm
  have ha₁attF' : a₁ ∈ attachments G F' K := by
    exact ⟨by simp [K, R], f₁, Or.inl (List.getElem_mem hfpos), ha₁f₁⟩
  have hdattF' : d ∈ attachments G F' K := by
    exact ⟨by simp [K, R], b, Or.inr rfl, (cBD b hbB d hdD).symm⟩

  -- PAPER 5602--5604: 10.4 forces an attachment on the second short rung.
  have ha₂_or_b₂ : a₂ ∈ attachments G F' K ∨ b₂ ∈ attachments G F' K := by
    by_contra hnone
    push_neg at hnone
    let σ : Equiv.Perm (Fin 3) := Equiv.swap (1 : Fin 3) 2
    have hs0 : σ 0 = 0 := by decide
    have hs1 : σ 1 = 2 := by decide
    have hs2 : σ 2 = 1 := by decide
    have hp' := PrismSymmetry.formPrism_perm hprism σ
    change FormPrism G (fun i => aa (σ i)) (fun i => bb (σ i))
      (R (σ 0)) (R (σ 1)) (R (σ 2)) at hp'
    have hK' : K = {z : V | z ∈ R (σ 0)} ∪ {z : V | z ∈ R (σ 1)} ∪
        {z : V | z ∈ R (σ 2)} := by
      simpa [hs0, hs1, hs2, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hK
    have hodd' : ¬ Even (pathLength (R (σ 0))) := by simpa [hs0] using hoddR0
    have hnonlocal' : ¬ LocalForPrism (fun i => aa (σ i)) (fun i => bb (σ i))
        (R (σ 0)) (R (σ 1)) (R (σ 2)) (attachments G F' K) := by
      exact diagonal_attachments_not_local
        (G := G) (a := fun i => aa (σ i)) (b := fun i => bb (σ i))
        (R := fun i => R (σ i)) (X := attachments G F' K) hp'
        (by simpa [hs0, aa] using ha₁attF')
        (by simpa [hs1, bb] using hdattF')
    have hnoR2' : ∀ v ∈ attachments G F' K, v ∉ R (σ 2) := by
      intro v hv hvR
      have hvR' : v = a₂ ∨ v = b₂ := by simpa [hs2, R] using hvR
      rcases hvR' with h | h
      · exact hnone.1 (h ▸ hv)
      · exact hnone.2 (h ▸ hv)
    have hjump := legal_jump_of_odd_first_rung G hG
      (fun i => aa (σ i)) (fun i => bb (σ i)) (fun i => R (σ i)) K F'
      hp' hK' hF'K hF'conn hodd' hnonlocal' hnoR2'
    have hcatt : c ∈ attachments G F' K := by
      rw [hjump.2]
      simp [hs1, aa, bb]
    obtain ⟨-, x, hx, hcx⟩ := hcatt
    exact hcnoF' x hx hcx

  -- First rule out the alternative that only `b₂` attaches; it gives the long prism on line
  -- 5607.  Minimality also shows here that `b₂` has no neighbour on `f`.
  have hb₂noF : ∀ x ∈ f, ¬ G.Adj b₂ x := by
    intro x hx hb₂x
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rcases attachment_indices_span hcfg ha₁A hb₂B n02 hfpos hi ha₁f₁ hb₂x with h | h
    · have heq : f[i] = fk := by
        dsimp [fk]
        exact (getElem_eq_iff hfnd hi hlast).mpr h.2
      exact hnotfkb₂ (heq ▸ hb₂x.symm)
    · have := hcfg.len
      omega

  have ha₂attF' : a₂ ∈ attachments G F' K := by
    rcases ha₂_or_b₂ with h | hb₂att
    · exact h
    · by_contra ha₂att
      have ha₂noF' : ∀ x ∈ F', ¬ G.Adj a₂ x := by
        intro x hx ha₂x
        exact ha₂att ⟨by simp [K, R], x, hx, ha₂x⟩
      obtain ⟨-, x, hx, hb₂x⟩ := hb₂att
      have hb₂b : G.Adj b₂ b := by
        rcases hx with hx | hx
        · exact (hb₂noF x hx hb₂x).elim
        · rw [Set.mem_singleton_iff] at hx
          exact hx ▸ hb₂x
      let q : List V := a₁ :: (f ++ [b])
      have hq' : IsPathFrom G q a₁ b := by simpa [q] using hq
      have hqmem : ∀ x ∈ q, x = a₁ ∨ x ∈ f ∨ x = b := by
        intro x hx
        simpa [q] using hx
      have ha₁ne_b : a₁ ≠ b := fun h => Set.disjoint_left.mp dAB ha₁A (h ▸ hbB)
      have ha₂ne_b : a₂ ≠ b := fun h => Set.disjoint_left.mp dAB ha₂A (h ▸ hbB)
      have hcne_b : c ≠ b := fun h => Set.disjoint_left.mp dBC hbB (h.symm ▸ hcC)
      have hcne_d : c ≠ d := fun h => Set.disjoint_left.mp dCD hcC (h ▸ hdD)
      have hqcross2 : ∀ u ∈ q, ∀ v ∈ [a₂, b₂],
          (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b ∧ v = b₂)) := by
        intro u hu v hv
        have hv' : v = a₂ ∨ v = b₂ := by simpa using hv
        rcases hqmem u hu with hua | huf | hub
        · subst u
          rcases hv' with hva | hvb
          · subst v
            exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => e30.symm⟩
          · subst v
            exact ⟨fun h => (n02 h).elim, by
              rintro (⟨-, h⟩ | ⟨h, -⟩)
              · exact (ne23 h).elim
              · exact (ha₁ne_b h).elim⟩
        · rcases hv' with hva | hvb
          · subst v
            exact ⟨fun h => (ha₂noF' u (Or.inl huf) h.symm).elim, by
              rintro (⟨h, -⟩ | ⟨h, -⟩)
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inl ha₁A)))).elim
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inr hbB)))).elim⟩
          · subst v
            exact ⟨fun h => (hb₂noF u huf h.symm).elim, by
              rintro (⟨h, -⟩ | ⟨h, -⟩)
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inl ha₁A)))).elim
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inr hbB)))).elim⟩
        · subst u
          rcases hv' with hva | hvb
          · subst v
            exact ⟨fun h => (ha₂noF' b (Or.inr rfl) h.symm).elim, by
              rintro (⟨h, -⟩ | ⟨-, h⟩)
              · exact (ha₁ne_b h.symm).elim
              · exact (ne23 h.symm).elim⟩
          · subst v
            exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => hb₂b.symm⟩
      have hqcross3 : ∀ u ∈ q, ∀ v ∈ [c, d],
          (G.Adj u v ↔ (u = a₁ ∧ v = c) ∨ (u = b ∧ v = d)) := by
        intro u hu v hv
        have hv' : v = c ∨ v = d := by simpa using hv
        rcases hqmem u hu with hua | huf | hub
        · subst u
          rcases hv' with hvc | hvd
          · subst v
            exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => ha₁c⟩
          · subst v
            exact ⟨fun h => (ha₁d h).elim, by
              rintro (⟨-, h⟩ | ⟨h, -⟩)
              · exact (hcne_d h.symm).elim
              · exact (ha₁ne_b h).elim⟩
        · rcases hv' with hvc | hvd
          · subst v
            exact ⟨fun h => (hCD c (Or.inl hcC) u huf h.symm).elim, by
              rintro (⟨h, -⟩ | ⟨h, -⟩)
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inl ha₁A)))).elim
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inr hbB)))).elim⟩
          · subst v
            exact ⟨fun h => (hCD d (Or.inr hdD) u huf h.symm).elim, by
              rintro (⟨h, -⟩ | ⟨h, -⟩)
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inl ha₁A)))).elim
              · exact (hcfg.outside u huf (h ▸ Or.inl (Or.inl (Or.inr hbB)))).elim⟩
        · subst u
          rcases hv' with hvc | hvd
          · subst v
            exact ⟨fun h => (aBC b hbB c hcC h).elim, by
              rintro (⟨h, -⟩ | ⟨-, h⟩)
              · exact (ha₁ne_b h.symm).elim
              · exact (hcne_d h).elim⟩
          · subst v
            exact ⟨fun _ => Or.inr ⟨rfl, rfl⟩, fun _ => cBD b hbB d hdD⟩
      have hlongPrism : FormPrism G ![a₁, a₂, c] ![b, b₂, d]
          q [a₂, b₂] [c, d] := by
        refine formPrism_of_data e30.symm ha₁c ha₂c hb₂b.symm (cBD b hbB d hdD) hb₂d
          ?_ ne02 (fun h => Set.disjoint_left.mp dAD ha₁A (h ▸ hdD))
          (fun h => Set.disjoint_left.mp dAB ha₂A (h ▸ hbB)) ne23.symm
          (fun h => Set.disjoint_left.mp dAD ha₂A (h ▸ hdD))
          (fun h => Set.disjoint_left.mp dBC (h ▸ hbB) hcC)
          (fun h => Set.disjoint_left.mp dBC (h ▸ hb₂B) hcC)
          (fun h => Set.disjoint_left.mp dCD hcC (h ▸ hdD)) hq'
          ⟨PathBasics.isPathList_pair e23.symm, rfl, rfl⟩
          ⟨PathBasics.isPathList_pair hcd, rfl, rfl⟩ hqcross2 hqcross3 hcross12
        exact ha₁ne_b
      apply hG.2.1
      exact ⟨_, _, q, [a₂, b₂], [c, d], hlongPrism, Or.inl (by
        simp [q, pathLength]
        have := hcfg.len
        omega)⟩

  -- It attaches through `f`, not merely through `b`: otherwise the displayed cycle on line
  -- 5608 is an odd hole.
  have ha₂F : ∃ x ∈ f, G.Adj a₂ x := by
    obtain ⟨-, x, hx, ha₂x⟩ := ha₂attF'
    rcases hx with hx | hx
    · exact ⟨x, hx, ha₂x⟩
    · rw [Set.mem_singleton_iff] at hx
      subst x
      by_contra hnone
      have ha₂noF : ∀ x ∈ f, ¬ G.Adj a₂ x := by
        intro x hx hax
        exact hnone ⟨x, hx, hax⟩
      have ha₂notq : a₂ ∉ a₁ :: (f ++ [b]) := by
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact ne03 h.symm
        · rcases List.mem_append.mp h with h | h
          · exact hcfg.outside a₂ h (Or.inl (Or.inl (Or.inl ha₂A)))
          · have hab : a₂ = b := by simpa using h
            exact ha₂x.ne hab
      have ha₂int : ∀ x ∈ interior (a₁ :: (f ++ [b])), ¬ G.Adj a₂ x := by
        intro x hx
        have hi := (PathBasics.mem_interior_iff_of_pathFrom hq).mp hx
        rcases List.mem_cons.mp hi.1 with h | h
        · exact (hi.2.1 h).elim
        · rcases List.mem_append.mp h with h | h
          · exact ha₂noF x h
          · have hxb : x = b := by simpa using h
            exact (hi.2.2 hxb).elim
      exact even_internal_path_cannot_close hG.1.1 hcfg.len hfeven hq e30 ha₂x
        ha₂notq ha₂int

  -- Minimality now converts `a₂`'s attachment to the first endpoint.  Since `a₂ ∉ A'`, it
  -- must be adjacent to the selected `b`.
  have ha₂b : G.Adj a₂ b := by
    by_contra ha₂b
    obtain ⟨x, hx, ha₂x⟩ := ha₂F
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rcases attachment_indices_span hcfg ha₂A hbB ha₂b hi hlast ha₂x hbfk with h | h
    · have ha₂f₁ : G.Adj a₂ f₁ := by
        dsimp [f₁]
        simpa only [(getElem_eq_iff hfnd hi hfpos).mpr h.1] using ha₂x
      exact ha₂notA' ⟨ha₂A, ha₂f₁, b, hbB, ha₂b, hbfk⟩
    · have := hcfg.len
      omega

  -- PAPER 5610--5612.  A `b₁`--`f` edge has one of the two endpoint orientations.  The
  -- paper's orientation puts `a₂` in `A'`; the other orientation closes an odd hole through
  -- `b₂` (the parity content hidden in the cited 10.1 symmetry).
  have hb₁noF : ∀ x ∈ f, ¬ G.Adj b₁ x := by
    intro x hx hb₁x
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨y, hy, ha₂y⟩ := ha₂F
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
    have ha₂b₁ : ¬ G.Adj a₂ b₁ := fun h => n13 h.symm
    rcases attachment_indices_span hcfg ha₂A hb₁B ha₂b₁ hi hj ha₂y hb₁x with h | h
    · have ha₂f₁ : G.Adj a₂ f₁ := by
        dsimp [f₁]
        simpa only [(getElem_eq_iff hfnd hi hfpos).mpr h.1] using ha₂y
      have hb₁fk : G.Adj b₁ fk := by
        dsimp [fk]
        simpa only [(getElem_eq_iff hfnd hj hlast).mpr h.2] using hb₁x
      exact ha₂notA' ⟨ha₂A, ha₂f₁, b₁, hb₁B, ha₂b₁, hb₁fk⟩
    · have hb₁f₁ : G.Adj b₁ f₁ := by
        dsimp [f₁]
        simpa only [(getElem_eq_iff hfnd hj hfpos).mpr h.1] using hb₁x
      have ha₂fk : G.Adj a₂ fk := by
        dsimp [fk]
        simpa only [(getElem_eq_iff hfnd hi hlast).mpr h.2] using ha₂y
      have hb₁idx : ∀ (t : ℕ) (ht : t < f.length),
          G.Adj b₁ (f[t]'ht) → t = 0 := by
        intro t ht hbt
        rcases attachment_indices_span hcfg ha₂A hb₁B ha₂b₁ hlast ht ha₂fk hbt with z | z
        · have := hcfg.len
          omega
        · exact z.1
      have ha₂idx : ∀ (t : ℕ) (ht : t < f.length),
          G.Adj a₂ (f[t]'ht) → t = f.length - 1 := by
        intro t ht hat
        rcases attachment_indices_span hcfg ha₂A hb₁B ha₂b₁ ht hfpos hat hb₁f₁ with z | z
        · have := hcfg.len
          omega
        · exact z.2
      have hb₁notf : b₁ ∉ f := by
        intro hm
        exact hcfg.outside b₁ hm (Or.inl (Or.inl (Or.inr hb₁B)))
      have ha₂notf : a₂ ∉ f := by
        intro hm
        exact hcfg.outside a₂ hm (Or.inl (Or.inl (Or.inl ha₂A)))
      have hb₁other : ∀ z ∈ f, z ≠ f₁ → ¬ G.Adj b₁ z := by
        intro z hz hz1 hbz
        obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hz
        apply hz1
        dsimp [f₁]
        exact (getElem_eq_iff hfnd ht hfpos).mpr (hb₁idx t ht hbz)
      have ha₂other : ∀ z ∈ f, z ≠ fk → ¬ G.Adj a₂ z := by
        intro z hz hzk haz
        obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hz
        apply hzk
        dsimp [fk]
        exact (getElem_eq_iff hfnd ht hlast).mpr (ha₂idx t ht haz)
      have hp : IsPathFrom G (b₁ :: (f ++ [a₂])) b₁ a₂ := by
        exact PathAttach.isPathFrom_cons_concat (isPathFrom_self hcfg.path hfpos)
          hb₁f₁ ha₂fk n13 ne13 hb₁notf ha₂notf hb₁other ha₂other
      have hb₂notp : b₂ ∉ b₁ :: (f ++ [a₂]) := by
        intro hm
        rcases List.mem_cons.mp hm with h | h
        · exact ne12 h.symm
        · rcases List.mem_append.mp h with h | h
          · exact hcfg.outside b₂ h (Or.inl (Or.inl (Or.inr hb₂B)))
          · have hba : b₂ = a₂ := by simpa using h
            exact ne23 hba
      have hb₂int : ∀ z ∈ interior (b₁ :: (f ++ [a₂])), ¬ G.Adj b₂ z := by
        intro z hz
        have hi' := (PathBasics.mem_interior_iff_of_pathFrom hp).mp hz
        rcases List.mem_cons.mp hi'.1 with h | h
        · exact (hi'.2.1 h).elim
        · rcases List.mem_append.mp h with h | h
          · exact hb₂noF z h
          · have hza : z = a₂ := by simpa using h
            exact (hi'.2.2 hza).elim
      exact even_internal_path_cannot_close hG.1.1 hcfg.len hfeven hp e12.symm e23
        hb₂notp hb₂int

  -- PAPER 5613--5614: otherwise `b₁-a₁-f-...-b-b₁` is the same forbidden odd hole.
  have hb₁b : ¬ G.Adj b₁ b := by
    intro hb₁b
    have hb₁notq : b₁ ∉ a₁ :: (f ++ [b]) := by
      intro hm
      rcases List.mem_cons.mp hm with h | h
      · exact ne01 h.symm
      · rcases List.mem_append.mp h with h | h
        · exact hcfg.outside b₁ h (Or.inl (Or.inl (Or.inr hb₁B)))
        · have hbb : b₁ = b := by simpa using h
          exact hb₁b.ne hbb
    have hb₁int : ∀ z ∈ interior (a₁ :: (f ++ [b])), ¬ G.Adj b₁ z := by
      intro z hz
      have hi := (PathBasics.mem_interior_iff_of_pathFrom hq).mp hz
      rcases List.mem_cons.mp hi.1 with h | h
      · exact (hi.2.1 h).elim
      · rcases List.mem_append.mp h with h | h
        · exact hb₁noF z h
        · have hzb : z = b := by simpa using h
          exact (hi.2.2 hzb).elim
    exact even_internal_path_cannot_close hG.1.1 hcfg.len hfeven hq e01.symm hb₁b
      hb₁notq hb₁int

  -- It remains to apply 10.4 to the singleton `{b}` with the first square edge as the
  -- attachment-free rung.
  let Fb : Set V := {b}
  have hFbconn : ConnectedSet G Fb := by
    intro x y
    have hxy : x = y := Subtype.ext (x.2.trans y.2.symm)
    exact hxy ▸ SimpleGraph.Reachable.refl x
  have hFbK : Fb ⊆ Kᶜ := by
    intro x hx
    have hxb : x = b := by simpa [Fb] using hx
    exact hxb ▸ hbK
  have ha₂attFb : a₂ ∈ attachments G Fb K := by
    exact ⟨by simp [K, R], b, by simp [Fb], ha₂b⟩
  have hdattFb : d ∈ attachments G Fb K := by
    exact ⟨by simp [K, R], b, by simp [Fb], (cBD b hbB d hdD).symm⟩
  let σ : Equiv.Perm (Fin 3) :=
    { toFun := ![(1 : Fin 3), (2 : Fin 3), (0 : Fin 3)]
      invFun := ![(2 : Fin 3), (0 : Fin 3), (1 : Fin 3)]
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by intro i; fin_cases i <;> rfl }
  have hs0 : σ 0 = 1 := rfl
  have hs1 : σ 1 = 2 := rfl
  have hs2 : σ 2 = 0 := rfl
  have hp' := PrismSymmetry.formPrism_perm hprism σ
  change FormPrism G (fun i => aa (σ i)) (fun i => bb (σ i))
    (R (σ 0)) (R (σ 1)) (R (σ 2)) at hp'
  have hK' : K = {z : V | z ∈ R (σ 0)} ∪ {z : V | z ∈ R (σ 1)} ∪
      {z : V | z ∈ R (σ 2)} := by
    simpa [hs0, hs1, hs2, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hK
  have hodd' : ¬ Even (pathLength (R (σ 0))) := by
    simp [hs0, R, pathLength]
  have hnonlocal' : ¬ LocalForPrism (fun i => aa (σ i)) (fun i => bb (σ i))
      (R (σ 0)) (R (σ 1)) (R (σ 2)) (attachments G Fb K) := by
    exact diagonal_attachments_not_local
      (G := G) (a := fun i => aa (σ i)) (b := fun i => bb (σ i))
      (R := fun i => R (σ i)) (X := attachments G Fb K) hp'
      (by simpa [hs0, aa] using ha₂attFb)
      (by simpa [hs1, bb] using hdattFb)
  have hnoR2' : ∀ v ∈ attachments G Fb K, v ∉ R (σ 2) := by
    rintro v ⟨-, x, hx, hvx⟩ hvR
    have hxb : x = b := by simpa [Fb] using hx
    subst x
    have hvR' : v = a₁ ∨ v = b₁ := by simpa [hs2, R] using hvR
    rcases hvR' with h | h
    · subst v
      exact ha₁b hvx
    · subst v
      exact hb₁b hvx
  have hjump := legal_jump_of_odd_first_rung G hG
    (fun i => aa (σ i)) (fun i => bb (σ i)) (fun i => R (σ i)) K Fb
    hp' hK' hFbK hFbconn hodd' hnonlocal' hnoR2'
  rcases hjump.1 with ⟨x, hx, y, hy, hxy⟩
  have hxb : x = b := by simpa [Fb] using hx
  have hyb : y = b := by simpa [Fb] using hy
  exact hxy (hxb.trans hyb.symm)

end Workspace.ProofLemmas.Thm142NonFullCase
