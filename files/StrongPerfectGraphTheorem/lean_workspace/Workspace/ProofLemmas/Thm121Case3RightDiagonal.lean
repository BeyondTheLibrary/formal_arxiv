import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_4
import Workspace.Statements.S10.Thm_10_4
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.Thm121C3PathCons

/-!
# The core of case (3) of the proof of 12.1

PAPER (printed p. 69, case (3), from the point at which `v` is known to have a neighbour in
`B ∪ C` but none in `R₀*`):

*"… let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step such that `v` has a neighbour in `R₁ \ a₁`, and
in addition such that `v` is not adjacent to `b₂` if possible.  By 10.4, `v` has a neighbour in
`R₂`.  If `a₂` is its only neighbour in `R₂`, then the strip `S' = (A ∪ {v}, C, B)` is
step-connected, since `v`-`R`-`b₁`, `a₂`-`R₂`-`b₂` is an `S'`-step where `R` is the path from
`v` to `b₁` with interior in `R₁ \ a₁`; and since `v` is adjacent to `a₀` and has no other
neighbours in `R₀`, this is contrary to the maximality of the staircase.  So `v` has a neighbour
in `R₂ \ a₂`; and hence `v` can be linked onto the triangle `{b₀, b₁, b₂}` via
`v`-`a₀`-`R₀`-`b₀`, and for `i = 1, 2`, the path from `v` to `bᵢ` with interior in `Rᵢ \ aᵢ`.  By
2.4 it follows that `v` is adjacent to both `b₁, b₂`; and hence from our choice of the step
`R₁, R₂`, and since the strip is step-connected, it follows that `v` is right-diagonal."*

Map of the printed argument onto this file.

* `formPrism_mid` — the prism the paper applies 10.4 to.  It is the one formed by the step
  `R₁, R₂` together with the banister `R₀` (`PrismFromBanisterAndStep`), but with `R₀` in the
  **middle** slot, so that the paper's `R₃` (on which 10.4 forbids attachments) is `R₂`.  This
  ordering is forced: `v` *is* adjacent to `a₀ ∈ V(R₀)`, so `R₀` cannot be the third rung here.
* `nbr_in_R2` — *"By 10.4, `v` has a neighbour in `R₂`."*  Applied with `F = {v}`; the
  attachment set contains `v`'s neighbour on `R₁ \ a₁` and `a₀`, which kills all five
  alternatives of `LocalForPrism`, and 10.4's `|F| ≥ 2` contradicts `F = {v}`.
* `enlarged_contradiction` — *"If `a₂` is its only neighbour in `R₂`, then the strip
  `S' = (A ∪ {v}, C, B)` is step-connected … contrary to the maximality of the staircase."*
  The new rung is `v`-`R`-`b₁` with `R` the stretch of `R₁` from the neighbour of `v` closest to
  `b₁`; the new step is `v`-`R`-`b₁`, `a₂`-`R₂`-`b₂`; every old rung and old step of `S` is one
  of `S'`; and the banister `a₀`-`R₀`-`b₀` survives because `v` is adjacent to `a₀`, nonadjacent
  to `b₀`, and has no neighbour in `R₀*`.
* `adj_b1_b2` — *"`v` can be linked onto the triangle `{b₀, b₁, b₂}` … By 2.4 it follows that
  `v` is adjacent to both `b₁, b₂`."*  The three linking paths are `R₀`, and for `i = 1, 2` the
  stretch of `Rᵢ` from the neighbour of `v` closest to `bᵢ`.
* `body` — the closing sentence.  The derivation above needs only that the step admits a
  neighbour of `v` off its `A`-end, so it applies to *every* such step; the paper's *"such that
  `v` is not adjacent to `b₂` if possible"* is therefore discharged by observing that no such
  step can have `¬ G.Adj v b₂`.  *"Since the strip is step-connected"* is then the partition
  `(B ∩ N(v), B \ N(v))` of `B`: a step across it would be a step of the forbidden kind.

The results cited are 10.4, 2.4, and the maximality of the staircase.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm121Case3RightDiagonal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

/-! ### List / step bookkeeping -/

private theorem getElem_eq_of_eq {V : Type*} {l : List V} {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

private theorem mem_drop_iff' {V : Type*} (p : List V) (k : ℕ) (x : V) :
    x ∈ p.drop k ↔ ∃ (i : ℕ) (hi : i < p.length), k ≤ i ∧ p[i]'hi = x := by
  constructor
  · intro hx
    obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hx
    have ht' : t < p.length - k := by simpa using ht
    refine ⟨k + t, by omega, by omega, ?_⟩
    rw [← htx]
    exact List.getElem_drop.symm
  · rintro ⟨i, hi, hki, rfl⟩
    refine List.mem_iff_getElem.mpr ⟨i - k, by simp only [List.length_drop]; omega, ?_⟩
    rw [List.getElem_drop]
    exact getElem_eq_of_eq _ _ (by omega)

private theorem exists_max_adj {V : Type*} (G : SimpleGraph V) (v : V) (l : List V)
    (k0 : ℕ) (hk0 : k0 < l.length) (hk0adj : G.Adj v (l[k0]'hk0)) :
    ∃ (i : ℕ) (hilt : i < l.length), k0 ≤ i ∧ G.Adj v (l[i]'hilt) ∧
      ∀ (m : ℕ) (hm : m < l.length), i < m → ¬ G.Adj v (l[m]'hm) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.range l.length).filter
      (fun k => ∃ h : k < l.length, G.Adj v (l[k]'h)) := ⟨_, rfl⟩
  have hmemT : ∀ k : ℕ,
      k ∈ T ↔ (k < l.length ∧ ∃ h : k < l.length, G.Adj v (l[k]'h)) := by
    intro k
    rw [hT, Finset.mem_filter, Finset.mem_range]
  have hne : T.Nonempty := ⟨k0, (hmemT k0).mpr ⟨hk0, hk0, hk0adj⟩⟩
  obtain ⟨hlt, _, hadj⟩ := (hmemT _).mp (Finset.max'_mem T hne)
  refine ⟨T.max' hne, hlt, Finset.le_max' T k0 ((hmemT k0).mpr ⟨hk0, hk0, hk0adj⟩), hadj, ?_⟩
  intro m hm hgt hadjm
  have hle : m ≤ T.max' hne := Finset.le_max' T m ((hmemT m).mpr ⟨hm, hm, hadjm⟩)
  omega

private theorem rung_mem_strip {V : Type*} {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {R : List V} (hrung : IsRungOfStrip G A C B a R b) :
    ∀ u ∈ R, u ∈ A ∪ B ∪ C := by
  intro u hu
  by_cases h1 : u = a
  · exact Or.inl (Or.inl (h1 ▸ hrung.2.1))
  · by_cases h2 : u = b
    · exact Or.inl (Or.inr (h2 ▸ hrung.2.2.1))
    · exact Or.inr (hrung.2.2.2.2.2 u
        ((PathBasics.mem_interior_iff_of_pathFrom hrung.1).mpr ⟨hu, h1, h2⟩))

private theorem step_symm {V : Type*} {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V} (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  obtain ⟨h1, h2, hdis, hedge⟩ := h
  refine ⟨h2, h1, ?_, ?_⟩
  · intro x hx hx'
    exact hdis x hx' hx
  · intro u hu w hw
    have := hedge w hw u hu
    rw [SimpleGraph.adj_comm]
    tauto

/-! ### The prism `R₁, R₀, R₂` — the banister as the **middle** rung

10.4 is applied in case (3) with the banister as `R₂` and the second rung of the step as `R₃`,
because `v` *is* adjacent to `a₀ ∈ V(R₀)` and 10.4 forbids attachments on `V(R₃)` only. -/
private theorem formPrism_mid {V : Type*} {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (hban : IsBanister G A C B a₀ R₀ b₀) (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    FormPrism G ![a₁, a₀, a₂] ![b₁, b₀, b₂] R₁ R₀ R₂ := by
  have hform : FormPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ :=
    PrismFromBanisterAndStep.formPrism_of_banister_and_step hban hstep
  obtain ⟨htA, htB, hab, hp1, hp2, hp3, e12, e13, e23⟩ := hform
  have ha12 : G.Adj a₁ a₂ := by simpa using htA 0 1 (by decide)
  have ha10 : G.Adj a₁ a₀ := by simpa using htA 0 2 (by decide)
  have ha20 : G.Adj a₂ a₀ := by simpa using htA 1 2 (by decide)
  have hb12 : G.Adj b₁ b₂ := by simpa using htB 0 1 (by decide)
  have hb10 : G.Adj b₁ b₀ := by simpa using htB 0 2 (by decide)
  have hb20 : G.Adj b₂ b₀ := by simpa using htB 1 2 (by decide)
  have d11 : a₁ ≠ b₁ := by simpa using hab 0 0
  have d12 : a₁ ≠ b₂ := by simpa using hab 0 1
  have d10 : a₁ ≠ b₀ := by simpa using hab 0 2
  have d21 : a₂ ≠ b₁ := by simpa using hab 1 0
  have d22 : a₂ ≠ b₂ := by simpa using hab 1 1
  have d20 : a₂ ≠ b₀ := by simpa using hab 1 2
  have d01 : a₀ ≠ b₁ := by simpa using hab 2 0
  have d02 : a₀ ≠ b₂ := by simpa using hab 2 1
  have d00 : a₀ ≠ b₀ := by simpa using hab 2 2
  have hq1 : IsPathFrom G R₁ a₁ b₁ := by simpa using hp1
  have hq2 : IsPathFrom G R₂ a₂ b₂ := by simpa using hp2
  have hq3 : IsPathFrom G R₀ a₀ b₀ := by simpa using hp3
  have f12 : ∀ u ∈ R₁, ∀ y ∈ R₂, (G.Adj u y ↔ (u = a₁ ∧ y = a₂) ∨ (u = b₁ ∧ y = b₂)) := by
    simpa using e12
  have f10 : ∀ u ∈ R₁, ∀ y ∈ R₀, (G.Adj u y ↔ (u = a₁ ∧ y = a₀) ∨ (u = b₁ ∧ y = b₀)) := by
    simpa using e13
  have f20 : ∀ u ∈ R₂, ∀ y ∈ R₀, (G.Adj u y ↔ (u = a₂ ∧ y = a₀) ∨ (u = b₂ ∧ y = b₀)) := by
    simpa using e23
  have f02 : ∀ u ∈ R₀, ∀ y ∈ R₂, (G.Adj u y ↔ (u = a₀ ∧ y = a₂) ∨ (u = b₀ ∧ y = b₂)) := by
    intro u hu y hy
    rw [SimpleGraph.adj_comm, f20 y hy u hu]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨h2, h1⟩]
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      exacts [Or.inl ⟨h2, h1⟩, Or.inr ⟨h2, h1⟩]
  exact PrismBasics.formPrism_of_data ha10 ha12 (ha20.symm) hb10 hb12 (hb20.symm)
    d11 d10 d12 d01 d00 d02 d21 d20 d22 hq1 hq3 hq2 f10 f12 f02

/-! ### "By 10.4, `v` has a neighbour in `R₂`" -/
theorem nbr_in_R2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsEvenPrism G a b Q₁ Q₂ Q₃)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : G.Adj v a₀)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V) (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (w : V) (hwR₁ : w ∈ R₁) (hwa₁ : w ≠ a₁) (hvw : G.Adj v w) :
    ∃ y ∈ R₂, G.Adj v y := by
  classical
  by_contra hcon
  push_neg at hcon
  have hvABC : v ∉ A ∪ B ∪ C := fun h => hv (Set.mem_union_right _ h)
  have hvR0 : v ∉ R₀ := fun h => hv (Set.mem_union_left _ h)
  obtain ⟨hr1, hr2, hdis, hedge⟩ := id hstep
  have ha₀mem : a₀ ∈ R₀ := PathBasics.head_mem hban.1.2.1
  have hform : FormPrism G ![a₁, a₀, a₂] ![b₁, b₀, b₂] R₁ R₀ R₂ := formPrism_mid hban hstep
  obtain ⟨aa, haa⟩ : ∃ aa : Fin 3 → V, aa = ![a₁, a₀, a₂] := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb : Fin 3 → V, bb = ![b₁, b₀, b₂] := ⟨_, rfl⟩
  obtain ⟨RR, hRR⟩ : ∃ RR : Fin 3 → List V, RR = ![R₁, R₀, R₂] := ⟨_, rfl⟩
  have hRR0 : RR 0 = R₁ := by simp [hRR]
  have hRR1 : RR 1 = R₀ := by simp [hRR]
  have hRR2 : RR 2 = R₂ := by simp [hRR]
  have haa0 : aa 0 = a₁ := by simp [haa]
  have haa1 : aa 1 = a₀ := by simp [haa]
  have haa2 : aa 2 = a₂ := by simp [haa]
  have hbb0 : bb 0 = b₁ := by simp [hbb]
  have hbb1 : bb 1 = b₀ := by simp [hbb]
  have hbb2 : bb 2 = b₂ := by simp [hbb]
  have hformR : FormPrism G aa bb (RR 0) (RR 1) (RR 2) := by
    rw [hRR0, hRR1, hRR2, haa, hbb]; exact hform
  obtain ⟨K, hK⟩ : ∃ K : Set V,
      K = {y : V | y ∈ RR 0} ∪ {y : V | y ∈ RR 1} ∪ {y : V | y ∈ RR 2} := ⟨_, rfl⟩
  have hmemK : ∀ y : V, y ∈ K ↔ (y ∈ R₁ ∨ y ∈ R₀ ∨ y ∈ R₂) := by
    intro y
    rw [hK, hRR0, hRR1, hRR2]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hvK : v ∉ K := by
    rw [hmemK]
    rintro (h | h | h)
    · exact hvABC (rung_mem_strip hr1 v h)
    · exact hvR0 h
    · exact hvABC (rung_mem_strip hr2 v h)
  have hFK : ({v} : Set V) ⊆ Kᶜ := by
    intro y hy; rw [(hy : y = v)]; exact hvK
  have hFconn : SPGT.ConnectedSet G ({v} : Set V) := by
    intro p q
    have hpq : p = q := Subtype.ext (p.2.trans q.2.symm)
    rw [hpq]
  have hFmaj : IsEvenPrism G aa bb (RR 0) (RR 1) (RR 2) →
      ∀ z ∈ ({v} : Set V), ¬ MajorForPrism G aa bb z :=
    fun hev => absurd ⟨aa, bb, RR 0, RR 1, RR 2, hev⟩ hprism
  have hatt : ∀ y : V, (y ∈ R₁ ∨ y ∈ R₀ ∨ y ∈ R₂) → G.Adj v y →
      y ∈ attachments G ({v} : Set V) K :=
    fun y hyK hyadj => ⟨(hmemK y).mpr hyK, v, rfl, hyadj.symm⟩
  have hwatt : w ∈ attachments G ({v} : Set V) K := hatt w (Or.inl hwR₁) hvw
  have ha₀att : a₀ ∈ attachments G ({v} : Set V) K := hatt a₀ (Or.inr (Or.inl ha₀mem)) ha
  have hwS : w ∈ A ∪ B ∪ C := rung_mem_strip hr1 w hwR₁
  have ha₀S : a₀ ∉ A ∪ B ∪ C := hban.2.2.1.1
  have hFloc : ¬ LocalForPrism aa bb (RR 0) (RR 1) (RR 2)
      (attachments G ({v} : Set V) K) := by
    rw [hRR0, hRR1, hRR2]
    rintro (h | h | h | h | h)
    · exact ha₀S (rung_mem_strip hr1 a₀ (h ha₀att))
    · exact hban.2.1 w (h hwatt) hwS
    · exact hdis w hwR₁ (h hwatt)
    · rw [haa0, haa1, haa2] at h
      have : w = a₁ ∨ w = a₀ ∨ w = a₂ := by simpa using h hwatt
      rcases this with rfl | rfl | rfl
      · exact hwa₁ rfl
      · exact ha₀S hwS
      · exact hdis w hwR₁ (PathBasics.isPathFrom_ends_mem hr2.1).1
    · rw [hbb0, hbb1, hbb2] at h
      have : a₀ = b₁ ∨ a₀ = b₀ ∨ a₀ = b₂ := by simpa using h ha₀att
      rcases this with hh | hh | hh
      · exact ha₀S (hh ▸ rung_mem_strip hr1 b₁ (PathBasics.isPathFrom_ends_mem hr1.1).2)
      · exact hban.2.2.2.1.2.2 a₁ (Or.inl hr1.2.1) (hh ▸ hban.2.2.1.2.1 a₁ hr1.2.1)
      · exact ha₀S (hh ▸ rung_mem_strip hr2 b₂ (PathBasics.isPathFrom_ends_mem hr2.1).2)
  have hR₃ : ∀ y ∈ attachments G ({v} : Set V) K, y ∉ RR 2 := by
    intro y hy hyR
    rw [hRR2] at hyR
    obtain ⟨-, f, hf, hadjf⟩ := hy
    rw [(hf : f = v)] at hadjf
    exact hcon y hyR hadjf.symm
  have h104 := _root_.Workspace.Statements.S10.SPGT.thm_10_4 G hG
    (by rintro ⟨n, H, K', happ, -⟩; exact hK4 ⟨n, H, K', happ⟩)
    aa bb RR K ({v} : Set V) hformR hK hFK hFconn hFmaj hFloc hR₃
  exact Set.not_nontrivial_singleton h104.1

/-! ### The three "no other edges" clauses of the banister-and-step prism, unpacked -/
private theorem banister_step_edges {V : Type*} {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (hban : IsBanister G A C B a₀ R₀ b₀) (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    (∀ u ∈ R₁, ∀ y ∈ R₀, (G.Adj u y ↔ (u = a₁ ∧ y = a₀) ∨ (u = b₁ ∧ y = b₀))) ∧
      (∀ u ∈ R₂, ∀ y ∈ R₀, (G.Adj u y ↔ (u = a₂ ∧ y = a₀) ∨ (u = b₂ ∧ y = b₀))) := by
  obtain ⟨-, -, -, -, -, -, -, e13, e23⟩ :=
    PrismFromBanisterAndStep.formPrism_of_banister_and_step hban hstep
  constructor
  · simpa using e13
  · simpa using e23

/-! ### "`v` can be linked onto the triangle `{b₀, b₁, b₂}` … by 2.4 `v` is adjacent to both
`b₁, b₂`" -/
private theorem adj_b1_b2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : G.Adj v a₀) (hb : ¬ G.Adj v b₀)
    (hint : ∀ x ∈ SPGT.interior R₀, ¬ G.Adj v x)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V) (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hn1 : ∃ y ∈ R₁, y ≠ a₁ ∧ G.Adj v y)
    (hn2 : ∃ y ∈ R₂, y ≠ a₂ ∧ G.Adj v y) :
    G.Adj v b₁ ∧ G.Adj v b₂ := by
  classical
  obtain ⟨hr1, hr2, hdis, hedge⟩ := id hstep
  obtain ⟨e10, e20⟩ := banister_step_edges hban hstep
  have hvABC : v ∉ A ∪ B ∪ C := fun h => hv (Set.mem_union_right _ h)
  have hvR0 : v ∉ R₀ := fun h => hv (Set.mem_union_left _ h)
  have hR0S : ∀ y ∈ R₀, y ∉ A ∪ B ∪ C := hban.2.1
  -- the neighbours of `v` on `R₁` and `R₂` closest to `b₁`, `b₂`
  have hlen1 : 0 < R₁.length := PathBasics.path_length_pos hr1.1.1
  have hlen2 : 0 < R₂.length := PathBasics.path_length_pos hr2.1.1
  have ha1z : R₁[0]'hlen1 = a₁ := PathBasics.getElem_zero_of_head? hr1.1.2.1 hlen1
  have ha2z : R₂[0]'hlen2 = a₂ := PathBasics.getElem_zero_of_head? hr2.1.2.1 hlen2
  obtain ⟨y1, hy1R, hy1a, hvy1⟩ := hn1
  obtain ⟨k1, hk1, hk1y⟩ := List.mem_iff_getElem.mp hy1R
  have hk1pos : 1 ≤ k1 := by
    rcases Nat.eq_zero_or_pos k1 with rfl | h
    · exact absurd (hk1y.symm.trans ha1z) hy1a
    · exact h
  obtain ⟨m1, hm1lt, hm1ge, hm1adj, hm1max⟩ :=
    exists_max_adj G v R₁ k1 hk1 (by rw [hk1y]; exact hvy1)
  obtain ⟨y2, hy2R, hy2a, hvy2⟩ := hn2
  obtain ⟨k2, hk2, hk2y⟩ := List.mem_iff_getElem.mp hy2R
  have hk2pos : 1 ≤ k2 := by
    rcases Nat.eq_zero_or_pos k2 with rfl | h
    · exact absurd (hk2y.symm.trans ha2z) hy2a
    · exact h
  obtain ⟨m2, hm2lt, hm2ge, hm2adj, hm2max⟩ :=
    exists_max_adj G v R₂ k2 hk2 (by rw [hk2y]; exact hvy2)
  have hm1pos : 1 ≤ m1 := by omega
  have hm2pos : 1 ≤ m2 := by omega
  -- the two stretches
  have hsub1 : ∀ y ∈ R₁.drop m1, y ∈ R₁ := fun y hy => List.mem_of_mem_drop hy
  have hsub2 : ∀ y ∈ R₂.drop m2, y ∈ R₂ := fun y hy => List.mem_of_mem_drop hy
  have hne1 : ∀ y ∈ R₁.drop m1, y ≠ a₁ := by
    intro y hy
    obtain ⟨t, ht, hmt, hty⟩ := (mem_drop_iff' R₁ m1 y).mp hy
    rw [← hty, ← ha1z]
    exact PathBasics.path_ne_of_ne_index hr1.1.1 ht hlen1 (by omega)
  have hne2 : ∀ y ∈ R₂.drop m2, y ≠ a₂ := by
    intro y hy
    obtain ⟨t, ht, hmt, hty⟩ := (mem_drop_iff' R₂ m2 y).mp hy
    rw [← hty, ← ha2z]
    exact PathBasics.path_ne_of_ne_index hr2.1.1 ht hlen2 (by omega)
  have hp2 : IsPathFrom G (R₁.drop m1) (R₁[m1]'hm1lt) b₁ := by
    refine ⟨PathBasics.isPathList_drop hr1.1.1 hm1lt, ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem hm1lt]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hr1.1.2.2
  have hp3 : IsPathFrom G (R₂.drop m2) (R₂[m2]'hm2lt) b₂ := by
    refine ⟨PathBasics.isPathList_drop hr2.1.1 hm2lt, ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem hm2lt]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hr2.1.2.2
  -- the link data
  have hlink : VertexCanBeLinkedOntoTriangle G v b₀ b₁ b₂ := by
    refine ⟨R₀, R₁.drop m1, R₂.drop m2, ⟨hban.1.1, hp2.1, hp3.1⟩, ⟨?_, ?_, ?_⟩,
      ⟨Or.inr hban.1.2.2, Or.inr hp2.2.2, Or.inr hp3.2.2⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · intro y hy hy'
      exact hR0S y hy (rung_mem_strip hr1 y (hsub1 y hy'))
    · intro y hy hy'
      exact hR0S y hy (rung_mem_strip hr2 y (hsub2 y hy'))
    · intro y hy hy'
      exact hdis y (hsub1 y hy) (hsub2 y hy')
    · intro x hx y hy
      rw [SimpleGraph.adj_comm, e10 y (hsub1 y hy) x hx]
      constructor
      · rintro (⟨h1, -⟩ | ⟨h1, h2⟩)
        · exact absurd h1 (hne1 y hy)
        · exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact Or.inr ⟨h2, h1⟩
    · intro x hx y hy
      rw [SimpleGraph.adj_comm, e20 y (hsub2 y hy) x hx]
      constructor
      · rintro (⟨h1, -⟩ | ⟨h1, h2⟩)
        · exact absurd h1 (hne2 y hy)
        · exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact Or.inr ⟨h2, h1⟩
    · intro x hx y hy
      rw [hedge x (hsub1 x hx) y (hsub2 y hy)]
      constructor
      · rintro (⟨h1, -⟩ | h)
        · exact absurd h1 (hne1 x hx)
        · exact h
      · intro h
        exact Or.inr h
    · exact ⟨a₀, PathBasics.head_mem hban.1.2.1, ha⟩
    · exact ⟨R₁[m1]'hm1lt, (mem_drop_iff' R₁ m1 _).mpr ⟨m1, hm1lt, le_rfl, rfl⟩, hm1adj⟩
    · exact ⟨R₂[m2]'hm2lt, (mem_drop_iff' R₂ m2 _).mpr ⟨m2, hm2lt, le_rfl, rfl⟩, hm2adj⟩
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG v b₀ b₁ b₂ hlink with
    ⟨h1, -⟩ | ⟨h1, -⟩ | h
  · exact absurd h1 hb
  · exact absurd h1 hb
  · exact h

/-! ### "the strip `S' = (A ∪ {v}, C, B)` is step-connected … contrary to the maximality of the
staircase" -/
private theorem enlarged_contradiction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : G.Adj v a₀) (hb : ¬ G.Adj v b₀)
    (hint : ∀ x ∈ SPGT.interior R₀, ¬ G.Adj v x)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V) (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hn1 : ∃ y ∈ R₁, y ≠ a₁ ∧ G.Adj v y)
    (hva₂ : G.Adj v a₂) (honly : ∀ y ∈ R₂, G.Adj v y → y = a₂) :
    False := by
  classical
  have hS : StepConnected G A C B := hK.1.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.1.2.1
  obtain ⟨hr1, hr2, hdis, hedge⟩ := id hstep
  have hvABC : v ∉ A ∪ B ∪ C := fun h => hv (Set.mem_union_right _ h)
  have hvR0 : v ∉ R₀ := fun h => hv (Set.mem_union_left _ h)
  have hva : v ∉ A := fun h => hvABC (Or.inl (Or.inl h))
  have hvb : v ∉ B := fun h => hvABC (Or.inl (Or.inr h))
  have hvc : v ∉ C := fun h => hvABC (Or.inr h)
  have hvR1 : v ∉ R₁ := fun h => hvABC (rung_mem_strip hr1 v h)
  have hvR2 : v ∉ R₂ := fun h => hvABC (rung_mem_strip hr2 v h)
  have ha₂v : a₂ ≠ v := fun h => hva (h ▸ hr2.2.1)
  have hb₁v : b₁ ≠ v := fun h => hvb (h ▸ hr1.2.2.1)
  -- upgrading rungs and steps of `S` to rungs and steps of `S'`
  have rung_up : ∀ {a b : V} {p : List V}, IsRungOfStrip G A C B a p b →
      IsRungOfStrip G (A ∪ {v}) C B a p b := by
    intro a b p hp
    refine ⟨hp.1, Or.inl hp.2.1, hp.2.2.1, ?_, hp.2.2.2.2.1, hp.2.2.2.2.2⟩
    intro w hw hwA
    rcases hwA with h | h
    · exact hp.2.2.2.1 w hw h
    · exact absurd (rung_mem_strip hp w hw) (by rw [(h : w = v)]; exact hvABC)
  have step_up : ∀ {c₁ d₁ c₂ d₂ : V} {P₁ P₂ : List V}, IsStep G A C B c₁ P₁ d₁ c₂ P₂ d₂ →
      IsStep G (A ∪ {v}) C B c₁ P₁ d₁ c₂ P₂ d₂ :=
    fun h => ⟨rung_up h.1, rung_up h.2.1, h.2.2.1, h.2.2.2⟩
  -- the new rung `v`-`R`-`b₁`
  have hlen1 : 0 < R₁.length := PathBasics.path_length_pos hr1.1.1
  have ha1z : R₁[0]'hlen1 = a₁ := PathBasics.getElem_zero_of_head? hr1.1.2.1 hlen1
  obtain ⟨y1, hy1R, hy1a, hvy1⟩ := hn1
  obtain ⟨k1, hk1, hk1y⟩ := List.mem_iff_getElem.mp hy1R
  have hk1pos : 1 ≤ k1 := by
    rcases Nat.eq_zero_or_pos k1 with rfl | h
    · exact absurd (hk1y.symm.trans ha1z) hy1a
    · exact h
  obtain ⟨m1, hm1lt, hm1ge, hm1adj, hm1max⟩ :=
    exists_max_adj G v R₁ k1 hk1 (by rw [hk1y]; exact hvy1)
  have hm1pos : 1 ≤ m1 := by omega
  have hsub1 : ∀ y ∈ R₁.drop m1, y ∈ R₁ := fun y hy => List.mem_of_mem_drop hy
  have hne1 : ∀ y ∈ R₁.drop m1, y ≠ a₁ := by
    intro y hy
    obtain ⟨t, ht, hmt, hty⟩ := (mem_drop_iff' R₁ m1 y).mp hy
    rw [← hty, ← ha1z]
    exact PathBasics.path_ne_of_ne_index hr1.1.1 ht hlen1 (by omega)
  have hstretch : IsPathFrom G (R₁.drop m1) (R₁[m1]'hm1lt) b₁ := by
    refine ⟨PathBasics.isPathList_drop hr1.1.1 hm1lt, ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem hm1lt]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hr1.1.2.2
  have hadjstretch : ∀ y ∈ R₁.drop m1, (G.Adj v y ↔ y = R₁[m1]'hm1lt) := by
    intro y hy
    obtain ⟨t, ht, hmt, hty⟩ := (mem_drop_iff' R₁ m1 y).mp hy
    constructor
    · intro hadj
      have hteq : t = m1 := by
        by_contra hne
        exact hm1max t ht (by omega) (by rw [hty]; exact hadj)
      rw [← hty, getElem_eq_of_eq ht hm1lt hteq]
    · intro hyy
      rw [hyy]; exact hm1adj
  have hR : IsPathFrom G (v :: R₁.drop m1) v b₁ :=
    Workspace.ProofLemmas.Thm121C3PathCons.isPathFrom_cons hstretch
      (fun hh => hvR1 (hsub1 v hh)) hadjstretch
  have hnewrung : IsRungOfStrip G (A ∪ {v}) C B v (v :: R₁.drop m1) b₁ := by
    refine ⟨hR, Or.inr rfl, hr1.2.2.1, ?_, ?_, ?_⟩
    · intro w hw hwA
      rcases List.mem_cons.mp hw with h | h
      · exact h
      · rcases hwA with hh | hh
        · exact absurd (hr1.2.2.2.1 w (hsub1 w h) hh) (hne1 w h)
        · exact absurd (hsub1 w h) (by rw [(hh : w = v)]; exact hvR1)
    · intro w hw hwB
      rcases List.mem_cons.mp hw with h | h
      · exact absurd hwB (by rw [h]; exact hvb)
      · exact hr1.2.2.2.2.1 w (hsub1 w h) hwB
    · intro w hw
      obtain ⟨hwmem, hwv, hwb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hw
      have hwS : w ∈ R₁.drop m1 := by
        rcases List.mem_cons.mp hwmem with h | h
        · exact absurd h hwv
        · exact h
      exact hr1.2.2.2.2.2 w
        ((PathBasics.mem_interior_iff_of_pathFrom hr1.1).mpr
          ⟨hsub1 w hwS, hne1 w hwS, hwb⟩)
  -- the new step `v`-`R`-`b₁`, `a₂`-`R₂`-`b₂`
  have hnewstep : IsStep G (A ∪ {v}) C B v (v :: R₁.drop m1) b₁ a₂ R₂ b₂ := by
    refine ⟨hnewrung, rung_up hr2, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · rw [h]; exact hvR2
      · exact hdis x (hsub1 x h)
    · intro u hu y hy
      rcases List.mem_cons.mp hu with h | h
      · subst h
        constructor
        · intro hadj
          exact Or.inl ⟨rfl, honly y hy hadj⟩
        · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
          · rw [h2]; exact hva₂
          · exact absurd h1.symm hb₁v
      · rw [hedge u (hsub1 u h) y hy]
        constructor
        · rintro (⟨h1, -⟩ | h2)
          · exact absurd h1 (hne1 u h)
          · exact Or.inr h2
        · rintro (⟨h1, -⟩ | h2)
          · exact absurd (hsub1 u h) (by rw [h1]; exact hvR1)
          · exact Or.inr h2
  -- `S'` is a step-connected strip
  have hSnew : StepConnected G (A ∪ {v}) C B := by
    refine ⟨⟨?_, ?_, hS.1.2.2⟩, ⟨⟨v, Or.inr rfl⟩, hS.2.1.2⟩, ?_, ?_, ?_⟩
    · rw [Set.disjoint_union_left]
      exact ⟨hS.1.1, Set.disjoint_singleton_left.mpr hvb⟩
    · rw [Set.disjoint_union_left]
      exact ⟨hS.1.2.1, Set.disjoint_singleton_left.mpr hvc⟩
    · intro w hw
      rcases hw with (hwA | hwv) | hwC
      · rcases hwA with hwA | hwv
        · obtain ⟨a, p, b, hp, hwp⟩ := hS.2.2.1 w (Or.inl (Or.inl hwA))
          exact ⟨a, p, b, rung_up hp, hwp⟩
        · exact ⟨v, v :: R₁.drop m1, b₁, hnewrung, by rw [(hwv : w = v)]; exact List.mem_cons_self⟩
      · obtain ⟨a, p, b, hp, hwp⟩ := hS.2.2.1 w (Or.inl (Or.inr hwv))
        exact ⟨a, p, b, rung_up hp, hwp⟩
      · obtain ⟨a, p, b, hp, hwp⟩ := hS.2.2.1 w (Or.inr hwC)
        exact ⟨a, p, b, rung_up hp, hwp⟩
    · intro w hw
      rcases hw with (hwA | hwv) | hwC
      · rcases hwA with hwA | hwv
        · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hst, hm⟩ := hS.2.2.2.1 w (Or.inl (Or.inl hwA))
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hst, hm⟩
        · exact ⟨v, v :: R₁.drop m1, b₁, a₂, R₂, b₂, hnewstep,
            Or.inl (by rw [(hwv : w = v)]; exact List.mem_cons_self)⟩
      · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hst, hm⟩ := hS.2.2.2.1 w (Or.inl (Or.inr hwv))
        exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hst, hm⟩
      · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hst, hm⟩ := hS.2.2.2.1 w (Or.inr hwC)
        exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hst, hm⟩
    · intro X Y hXY hdXY hXne hYne
      rcases hXY with hXY | hXY
      · -- a partition of `A ∪ {v}`
        by_cases hvX : v ∈ X
        · by_cases hX' : (X \ {v}).Nonempty
          · have hXA : (X \ {v}) ∪ Y = A := by
              apply Set.Subset.antisymm
              · rintro z (⟨hzX, hzv⟩ | hzY)
                · have : z ∈ A ∪ {v} := hXY ▸ Or.inl hzX
                  rcases this with h | h
                  · exact h
                  · exact absurd h hzv
                · have : z ∈ A ∪ {v} := hXY ▸ Or.inr hzY
                  rcases this with h | h
                  · exact h
                  · exact absurd hzY (by rw [(h : z = v)]; exact Set.disjoint_left.mp hdXY hvX)
              · intro z hz
                have hz' : z ∈ X ∪ Y := hXY ▸ Or.inl hz
                rcases hz' with h | h
                · exact Or.inl ⟨h, fun hzv => hva (hzv ▸ hz)⟩
                · exact Or.inr h
            obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hst, h1, h2⟩ :=
              hS.2.2.2.2 (X \ {v}) Y (Or.inl hXA)
                (Set.disjoint_of_subset_left Set.diff_subset hdXY) hX' hYne
            exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hst, h1.imp (fun h => h.1) (fun h => h.1), h2⟩
          · rw [Set.not_nonempty_iff_eq_empty] at hX'
            have ha₂Y : a₂ ∈ Y := by
              have hz : a₂ ∈ X ∪ Y := hXY ▸ Or.inl hr2.2.1
              rcases hz with h | h
              · exact absurd (show a₂ ∈ X \ {v} from ⟨h, ha₂v⟩)
                  (Set.eq_empty_iff_forall_notMem.mp hX' a₂)
              · exact h
            exact ⟨v, v :: R₁.drop m1, b₁, a₂, R₂, b₂, hnewstep, Or.inl hvX, Or.inl ha₂Y⟩
        · have hvY : v ∈ Y := by
            have hz : v ∈ X ∪ Y := hXY ▸ Or.inr rfl
            rcases hz with h | h
            · exact absurd h hvX
            · exact h
          by_cases hY' : (Y \ {v}).Nonempty
          · have hYA : X ∪ (Y \ {v}) = A := by
              apply Set.Subset.antisymm
              · rintro z (hzX | ⟨hzY, hzv⟩)
                · have : z ∈ A ∪ {v} := hXY ▸ Or.inl hzX
                  rcases this with h | h
                  · exact h
                  · exact absurd hzX (by rw [(h : z = v)]; exact Set.disjoint_right.mp hdXY hvY)
                · have : z ∈ A ∪ {v} := hXY ▸ Or.inr hzY
                  rcases this with h | h
                  · exact h
                  · exact absurd h hzv
              · intro z hz
                have hz' : z ∈ X ∪ Y := hXY ▸ Or.inl hz
                rcases hz' with h | h
                · exact Or.inl h
                · exact Or.inr ⟨h, fun hzv => hva (hzv ▸ hz)⟩
            obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hst, h1, h2⟩ :=
              hS.2.2.2.2 X (Y \ {v}) (Or.inl hYA)
                (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hY'
            exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hst, h1, h2.imp (fun h => h.1) (fun h => h.1)⟩
          · rw [Set.not_nonempty_iff_eq_empty] at hY'
            have ha₂X : a₂ ∈ X := by
              have hz : a₂ ∈ X ∪ Y := hXY ▸ Or.inl hr2.2.1
              rcases hz with h | h
              · exact h
              · exact absurd (show a₂ ∈ Y \ {v} from ⟨h, ha₂v⟩)
                  (Set.eq_empty_iff_forall_notMem.mp hY' a₂)
            exact ⟨a₂, R₂, b₂, v, v :: R₁.drop m1, b₁, step_symm hnewstep, Or.inl ha₂X,
              Or.inl hvY⟩
      · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hst, h1, h2⟩ :=
          hS.2.2.2.2 X Y (Or.inr hXY) hdXY hXne hYne
        exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hst, h1, h2⟩
  -- `a₀`-`R₀`-`b₀` is still a banister for `S'`
  have hbannew : IsBanister G (A ∪ {v}) C B a₀ R₀ b₀ := by
    refine ⟨hban.1, ?_, ?_, ?_, ?_⟩
    · intro y hy hcon
      rcases hcon with (h | h) | h
      · rcases h with h | h
        · exact hban.2.1 y hy (Or.inl (Or.inl h))
        · exact hvR0 (by rw [← (h : y = v)]; exact hy)
      · exact hban.2.1 y hy (Or.inl (Or.inr h))
      · exact hban.2.1 y hy (Or.inr h)
    · refine ⟨?_, ?_, hban.2.2.1.2.2⟩
      · rintro (((h | h) | h) | h)
        · exact hban.2.2.1.1 (Or.inl (Or.inl h))
        · exact hvR0 (by rw [← (h : a₀ = v)]; exact PathBasics.head_mem hban.1.2.1)
        · exact hban.2.2.1.1 (Or.inl (Or.inr h))
        · exact hban.2.2.1.1 (Or.inr h)
      · rintro y (hy | hy)
        · exact hban.2.2.1.2.1 y hy
        · rw [(hy : y = v)]; exact ha.symm
    · refine ⟨?_, hban.2.2.2.1.2.1, ?_⟩
      · rintro (((h | h) | h) | h)
        · exact hban.2.2.2.1.1 (Or.inl (Or.inl h))
        · exact hvR0 (by rw [← (h : b₀ = v)]; exact PathBasics.getLast_mem hban.1.2.2)
        · exact hban.2.2.2.1.1 (Or.inl (Or.inr h))
        · exact hban.2.2.2.1.1 (Or.inr h)
      · rintro y ((hy | hy) | hy)
        · exact hban.2.2.2.1.2.2 y (Or.inl hy)
        · rw [(hy : y = v)]
          exact fun hc => hb hc.symm
        · exact hban.2.2.2.1.2.2 y (Or.inr hy)
    · intro y hy z hz
      rcases hz with (hzA | hzv) | hzC
      · rcases hzA with hzA | hzv
        · exact hban.2.2.2.2 y hy z (Or.inl (Or.inl hzA))
        · rw [(hzv : z = v)]
          exact fun hc => hint y hy hc.symm
      · exact hban.2.2.2.2 y hy z (Or.inl (Or.inr hzv))
      · exact hban.2.2.2.2 y hy z (Or.inr hzC)
  -- and that contradicts maximality
  refine hK.2 ⟨A ∪ {v}, C, B, a₀, R₀, b₀, ⟨hSnew, hbannew, hK.1.2.2⟩,
    Set.subset_union_left, Set.Subset.rfl, Set.Subset.rfl, ?_⟩
  constructor
  · intro z hz
    rcases hz with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · intro hsub
    exact hvABC (hsub (Or.inl (Or.inl (Or.inr rfl))))

/-! ### Assembly -/
private theorem body {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsEvenPrism G a b Q₁ Q₂ Q₃)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : G.Adj v a₀) (hb : ¬ G.Adj v b₀)
    (hint : ∀ x ∈ SPGT.interior R₀, ¬ G.Adj v x)
    (hBC : ∃ x ∈ B ∪ C, G.Adj v x) :
    RightDiagonal G A C B a₀ R₀ b₀ v := by
  classical
  have hS : StepConnected G A C B := hK.1.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.1.2.1
  have hAB : ∀ x ∈ A, ∀ y ∈ B ∪ C, x ≠ y := by
    rintro x hx y (hy | hy) rfl
    · exact Set.disjoint_left.mp hS.1.1 hx hy
    · exact Set.disjoint_left.mp hS.1.2.1 hx hy
  -- **Every** step through which `v` has a neighbour off the `A`-end gives `v` two `B`-neighbours.
  have good_adj : ∀ (c₁ d₁ c₂ d₂ : V) (P₁ P₂ : List V), IsStep G A C B c₁ P₁ d₁ c₂ P₂ d₂ →
      (∃ y ∈ P₁, y ≠ c₁ ∧ G.Adj v y) → G.Adj v d₁ ∧ G.Adj v d₂ := by
    intro c₁ d₁ c₂ d₂ P₁ P₂ hst hn1
    obtain ⟨w, hwP₁, hwc₁, hvw⟩ := id hn1
    -- PAPER: *"By 10.4, `v` has a neighbour in `R₂`."*
    obtain ⟨y, hyP₂, hvy⟩ := nbr_in_R2 G hG hK4 hprism A C B a₀ b₀ R₀ hban v hv ha
      c₁ d₁ c₂ d₂ P₁ P₂ hst w hwP₁ hwc₁ hvw
    by_cases hn2 : ∃ z ∈ P₂, z ≠ c₂ ∧ G.Adj v z
    · -- PAPER: *"So `v` has a neighbour in `R₂ \ a₂`; … By 2.4 it follows that `v` is adjacent
      -- to both `b₁, b₂`."*
      exact adj_b1_b2 G hG A C B a₀ b₀ R₀ hban v hv ha hb hint c₁ d₁ c₂ d₂ P₁ P₂ hst hn1 hn2
    · -- PAPER: *"If `a₂` is its only neighbour in `R₂`, then the strip `S' = (A ∪ {v}, C, B)` is
      -- step-connected … contrary to the maximality of the staircase."*
      push_neg at hn2
      have honly : ∀ z ∈ P₂, G.Adj v z → z = c₂ := by
        intro z hz hadj
        by_contra hne
        exact hn2 z hz hne hadj
      have hvc₂ : G.Adj v c₂ := by
        have := honly y hyP₂ hvy
        rw [← this]; exact hvy
      exact absurd (enlarged_contradiction G A C B a₀ b₀ R₀ hK v hv ha hb hint
        c₁ d₁ c₂ d₂ P₁ P₂ hst hn1 hvc₂ honly) not_false
  -- PAPER: *"let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step such that `v` has a neighbour in
  -- `R₁ \ a₁`"* — through the neighbour of `v` in `B ∪ C`.
  obtain ⟨w, hwBC, hvw⟩ := hBC
  have hwS : w ∈ A ∪ B ∪ C := by
    rcases hwBC with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hst0, hm0⟩ := hS.2.2.2.1 w hwS
  have hgood : ∃ (e₁ f₁ e₂ f₂ : V) (Q₁ Q₂ : List V), IsStep G A C B e₁ Q₁ f₁ e₂ Q₂ f₂ ∧
      ∃ y ∈ Q₁, y ≠ e₁ ∧ G.Adj v y := by
    rcases hm0 with h | h
    · exact ⟨c₁, d₁, c₂, d₂, P₁, P₂, hst0, w, h, fun hc => hAB c₁ hst0.1.2.1 w hwBC hc.symm, hvw⟩
    · exact ⟨c₂, d₂, c₁, d₁, P₂, P₁, step_symm hst0, w, h,
        fun hc => hAB c₂ hst0.2.1.2.1 w hwBC hc.symm, hvw⟩
  obtain ⟨e₁, f₁, e₂, f₂, Q₁, Q₂, hstg, hng⟩ := hgood
  obtain ⟨hadjf₁, hadjf₂⟩ := good_adj e₁ f₁ e₂ f₂ Q₁ Q₂ hstg hng
  -- PAPER: *"and hence from our choice of the step `R₁, R₂`, and since the strip is
  -- step-connected, it follows that `v` is right-diagonal."*
  refine ⟨hv, ?_⟩
  rintro x (hxB | hxa)
  · by_contra hnadj
    obtain ⟨X, hX⟩ : ∃ X : Set V, X = {z : V | z ∈ B ∧ G.Adj v z} := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : Set V, Y = {z : V | z ∈ B ∧ ¬ G.Adj v z} := ⟨_, rfl⟩
    have hXY : X ∪ Y = B := by
      apply Set.Subset.antisymm
      · rintro z (hz | hz)
        · exact (hX ▸ hz : z ∈ B ∧ _).1
        · exact (hY ▸ hz : z ∈ B ∧ _).1
      · intro z hz
        by_cases hzz : G.Adj v z
        · exact Or.inl (by rw [hX]; exact ⟨hz, hzz⟩)
        · exact Or.inr (by rw [hY]; exact ⟨hz, hzz⟩)
    have hdXY : Disjoint X Y := by
      rw [Set.disjoint_left]
      intro z hzX hzY
      rw [hX] at hzX
      rw [hY] at hzY
      exact hzY.2 hzX.2
    have hXne : X.Nonempty := ⟨f₁, by rw [hX]; exact ⟨hstg.1.2.2.1, hadjf₁⟩⟩
    have hYne : Y.Nonempty := ⟨x, by rw [hY]; exact ⟨hxB, hnadj⟩⟩
    obtain ⟨g₁, S₁, h₁, g₂, S₂, h₂, hst2, hx1, hx2⟩ :=
      hS.2.2.2.2 X Y (Or.inr hXY) hdXY hXne hYne
    have hh₁X : h₁ ∈ X := by
      rcases hx1 with h | h
      · exact absurd ((hXY ▸ Or.inl h : g₁ ∈ B)) (fun hc =>
          Set.disjoint_left.mp hS.1.1 hst2.1.2.1 hc)
      · exact h
    have hh₂Y : h₂ ∈ Y := by
      rcases hx2 with h | h
      · exact absurd ((hXY ▸ Or.inr h : g₂ ∈ B)) (fun hc =>
          Set.disjoint_left.mp hS.1.1 hst2.2.1.2.1 hc)
      · exact h
    rw [hX] at hh₁X
    rw [hY] at hh₂Y
    have hadj1 : G.Adj v h₁ := hh₁X.2
    have hnadj2 : ¬ G.Adj v h₂ := hh₂Y.2
    have hgood2 : ∃ y ∈ S₁, y ≠ g₁ ∧ G.Adj v y :=
      ⟨h₁, (PathBasics.isPathFrom_ends_mem hst2.1.1).2,
        fun hc => hAB g₁ hst2.1.2.1 h₁ (Or.inl hst2.1.2.2.1) hc.symm, hadj1⟩
    exact hnadj2 (good_adj g₁ h₁ g₂ h₂ S₁ S₂ hst2 hgood2).2
  · rw [(hxa : x = a₀)]; exact ha

/-- **The conclusion of the main stretch of case (3): `v` is right-diagonal.** -/
theorem thm121Case3RightDiagonal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : G.Adj v a₀) (hb : ¬ G.Adj v b₀)
    (hint : ∀ x ∈ SPGT.interior R₀, ¬ G.Adj v x)
    (hBC : ∃ x ∈ B ∪ C, G.Adj v x) :
    RightDiagonal G A C B a₀ R₀ b₀ v :=
  body G hG hK4 hprism A C B a₀ b₀ R₀ hK v hv ha hb hint hBC

end Workspace.ProofLemmas.Thm121Case3RightDiagonal
